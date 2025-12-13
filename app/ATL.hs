{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module ATL where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

-- Types
data Type 
  = TReal                    -- R
  | TPair Type Type          -- T₀ × T₁
  | TTensor String Type      -- [n]T
  deriving (Show, Eq)

-- Affine index expressions
data AffineExpr
  = AVar String              -- i (index variable)
  | ASize String             -- n (size variable)
  | AConst Integer           -- k
  | AAdd AffineExpr AffineExpr  -- a₀ + a₁
  | AScale Integer AffineExpr   -- k · a
  deriving (Show, Eq)

-- Predicates
data Predicate
  = PLT AffineExpr AffineExpr     -- a₀ < a₁
  | PLE AffineExpr AffineExpr     -- a₀ ≤ a₁
  | PEq AffineExpr AffineExpr     -- a₀ = a₁
  | PRel String [AffineExpr]      -- R(a₀, ...)
  | PAnd Predicate Predicate      -- p₀ ∧ p₁
  | POr Predicate Predicate       -- p₀ ∨ p₁
  | PExists String Integer Predicate  -- ∃ⁿᵢ₌₀ p
  deriving (Show, Eq)


-- Expressions
data Expr
  = EVar String                   -- x
  | EConst Double                 -- c
  | EAdd Expr Expr                -- e₀ + e₁
  | EMul Expr Expr                -- e₀ · e₁
  | EFunc String [Expr]           -- f(e₀, ...)
  | EPair Expr Expr               -- (e₀, e₁)
  | EProj0 Expr                   -- π₀ e
  | EProj1 Expr                   -- π₁ e
  | EGen String Integer Expr      -- ⊗ⁿᵢ₌₀ e
  | ESum String Integer Expr      -- ∑ⁿᵢ₌₀ e
  | EAccess Expr AffineExpr       -- e[a]
  | EIverson Predicate Expr       -- [[p]] · e
  | ELet String Expr Expr         -- let x = e₀ in e₁
  deriving (Show, Eq)

-- Values
data Value
  = VScalar Double
  | VPair Value Value
  | VArray [Value]
  deriving (Show, Eq)

-- Zero value for a type
zeroValue :: Type -> Value
zeroValue TReal = VScalar 0.0
zeroValue (TPair t0 t1) = VPair (zeroValue t0) (zeroValue t1)
zeroValue (TTensor _ t) = VArray [] -- Will be filled with zeros based on size

-- Environment for expression evaluation
type Env = Map String Value

-- Environment for index/size evaluation
type IdxEnv = Map String Integer

-- Evaluate affine expressions (Fig 5, rules 4.13-4.17)
evalAffine :: IdxEnv -> AffineExpr -> Integer
evalAffine env = \case
  AVar i -> Map.findWithDefault 0 i env          -- 4.13
  ASize n -> Map.findWithDefault 0 n env         -- 4.14
  AConst k -> k                                   -- 4.15
  AAdd a0 a1 -> evalAffine env a0 + evalAffine env a1  -- 4.16
  AScale k a -> k * evalAffine env a             -- 4.17

-- Evaluate predicates (Fig 5, rules 4.18-4.21)
evalPred :: IdxEnv -> Predicate -> Bool
evalPred env = \case
  PLT a0 a1 -> evalAffine env a0 < evalAffine env a1   -- 4.18
  PLE a0 a1 -> evalAffine env a0 <= evalAffine env a1  -- 4.18
  PEq a0 a1 -> evalAffine env a0 == evalAffine env a1  -- 4.18
  PRel name args -> 
    -- For now, we'll treat relational predicates as external
    -- In a real implementation, these would be looked up
    False  -- 4.20
  PAnd p0 p1 -> evalPred env p0 && evalPred env p1     -- 4.19
  POr p0 p1 -> evalPred env p0 || evalPred env p1      -- 4.19
  PExists i n p ->                                      -- 4.21
    any (\k -> evalPred (Map.insert i k env) p) [0..n-1]

-- Get type of expression (simplified - would need full type checker)
typeOf :: Expr -> Type
typeOf (EConst _) = TReal
typeOf (EVar _) = TReal  -- Simplified
typeOf (EAdd _ _) = TReal
typeOf (EMul _ _) = TReal
typeOf (EFunc _ _) = TReal
typeOf (EPair e0 e1) = TPair (typeOf e0) (typeOf e1)
typeOf (EProj0 (EPair e0 _)) = typeOf e0
typeOf (EProj1 (EPair _ e1)) = typeOf e1
typeOf (EGen _ n e) = TTensor (show n) (typeOf e)
typeOf (ESum _ _ _) = TReal
typeOf (EAccess e _) = 
  case typeOf e of
    TTensor _ t -> t
    _ -> TReal
typeOf (EIverson _ e) = typeOf e
typeOf (ELet _ _ e1) = typeOf e1
typeOf _ = TReal

-- Evaluate expressions (Fig 4)
eval :: Env -> IdxEnv -> Expr -> Value
eval env ienv = \case
  -- Variable lookup (4.1)
  EVar x -> Map.findWithDefault (VScalar 0) x env
  
  -- Constant (4.2)
  EConst c -> VScalar c
  
  -- Addition (4.3)
  EAdd e0 e1 -> 
    case (eval env ienv e0, eval env ienv e1) of
      (VScalar v0, VScalar v1) -> VScalar (v0 + v1)
      _ -> error "Type error in addition"
  
  -- Multiplication (4.4)
  EMul e0 e1 ->
    case (eval env ienv e0, eval env ienv e1) of
      (VScalar v0, VScalar v1) -> VScalar (v0 * v1)
      _ -> error "Type error in multiplication"
  
  -- Function application (4.5)
  EFunc f args ->
    let vals = map (eval env ienv) args
        scalars = [v | VScalar v <- vals]
    in VScalar (applyFunc f scalars)
  
  -- Pair construction (4.6)
  EPair e0 e1 -> VPair (eval env ienv e0) (eval env ienv e1)
  
  -- Projection (4.10)
  EProj0 e ->
    case eval env ienv e of
      VPair v0 _ -> v0
      _ -> error "Type error in projection"
  
  EProj1 e ->
    case eval env ienv e of
      VPair _ v1 -> v1
      _ -> error "Type error in projection"
  
  -- Tensor generation (4.7)
  EGen i n e ->
    VArray [eval env (Map.insert i k ienv) e | k <- [0..n-1]]
  
  -- Tensor summation (4.8)
  ESum i n e ->
    let values = [eval env (Map.insert i k ienv) e | k <- [0..n-1]]
    in foldl addValues (VScalar 0) values
  
  -- Array access (4.11)
  EAccess e a ->
    case eval env ienv e of
      VArray vs ->
        let k = fromInteger (evalAffine ienv a)
        in if k >= 0 && k < length vs
           then vs !! k
           else error "Index out of bounds"
      _ -> error "Type error in access"
  
  -- Iverson bracket (4.12)
  EIverson p e ->
    if evalPred ienv p
    then eval env ienv e
    else zeroValue (typeOf e)
  
  -- Let binding (4.9)
  ELet x e0 e1 ->
    let v0 = eval env ienv e0
        env' = Map.insert x v0 env
    in eval env' ienv e1

-- Helper: add values
addValues :: Value -> Value -> Value
addValues (VScalar v0) (VScalar v1) = VScalar (v0 + v1)
addValues (VPair a0 b0) (VPair a1 b1) = VPair (addValues a0 a1) (addValues b0 b1)
addValues (VArray vs0) (VArray vs1) = VArray (zipWith addValues vs0 vs1)
addValues _ _ = error "Type error in addition"

-- Helper: apply black-box functions
applyFunc :: String -> [Double] -> Double
applyFunc "sin" [x] = sin x
applyFunc "cos" [x] = cos x
applyFunc "exp" [x] = exp x
applyFunc "log" [x] = log x
applyFunc "sqrt" [x] = sqrt x
applyFunc name _ = error $ "Unknown function: " ++ name

-- Example usage
example1 :: Expr
example1 = 
  -- let x = [1, 2, 3] in ∑³ᵢ₌₀ x[i]
  ELet "x" (EGen "i" 3 (EAdd (EConst 1) (EVar "i")))
    (ESum "i" 3 (EAccess (EVar "x") (AVar "i")))

example2 :: Expr
example2 =
  -- ⊗⁵ᵢ₌₀ [[i < 3]] · i
  EGen "i" 5 (EIverson (PLT (AVar "i") (AConst 3)) (EConst 1))

runExample :: Expr -> Value
runExample e = eval Map.empty Map.empty e
