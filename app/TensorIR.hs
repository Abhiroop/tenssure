{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- A compact Toy Tensor IR + loop-nest AST in Haskell and simple passes:
--  - lowering of a MatMul tensor op to explicit loop nests
--  - tiling (strip-mining)
--  - interchange (swap adjacent loops)
--  - fusion (merge sibling loops with same loop var & bound)
--  - tensorize (recognise inner multiply-add reduction and replace with an intrinsic)

module TensorIREx where

import Data.List
import Data.Maybe
import qualified Data.Map.Strict as M

-- Basic arithmetic expressions used in stores
data Expr
  = EVar String
  | EIdx String [Expr]        -- array access like A[i,k]
  | EConst Int
  | EAdd Expr Expr
  | EMul Expr Expr
  deriving (Eq, Show)

-- Simple statements / loop AST
data Stmt
  = For String Int Stmt           -- for var in 0 .. n-1 do body
  | Seq [Stmt]
  | Store String [Expr] Expr      -- name[index-exprs] = expr (represents a write)
  | Let String Expr Stmt          -- local let-binding (not heavily used)
  | Intrinsic String [String]     -- call an intrinsic (e.g. GEMM) with operand names
  | Skip
  deriving (Eq, Show)

-- Pretty printing of the loop AST
indent :: Int -> String
indent n = replicate (2*n) ' '

ppExpr :: Expr -> String
ppExpr = \case
  EVar v -> v
  EIdx a idxs -> a ++ "[" ++ intercalate "," (map ppExpr idxs) ++ "]"
  EConst i -> show i
  EAdd a b -> "(" ++ ppExpr a ++ " + " ++ ppExpr b ++ ")"
  EMul a b -> "(" ++ ppExpr a ++ " * " ++ ppExpr b ++ ")"

ppStmt :: Int -> Stmt -> String
ppStmt d = \case
  Skip -> ""
  Seq ss -> intercalate "\n" (map (ppStmt d) ss)
  For v n body -> indent d ++ "for " ++ v ++ " in 0.." ++ show (n-1) ++ " do\n" ++ ppStmt (d+1) body
  Store name idxs rhs -> indent d ++ ppExpr (EIdx name idxs) ++ " = " ++ ppExpr rhs
  Let v e body -> indent d ++ "let " ++ v ++ " = " ++ ppExpr e ++ " in\n" ++ ppStmt (d+1) body
  Intrinsic tag args -> indent d ++ tag ++ "(" ++ intercalate ", " args ++ ")"

render :: Stmt -> String
render = ppStmt 0

-- Example high-level Tensor op: MatMul
-- We'll present a tiny front-end AST for a tensor expression

data TensorOp
  = MatMul { out :: String, a :: String, b :: String, m :: Int, n :: Int, kdim :: Int }
  | PointwiseAdd String String String Int Int   -- C = A + B (shapes m x n)
  deriving (Eq, Show)

-- Lower MatMul to loops: C[i,j] += A[i,k]*B[k,j]
lower :: TensorOp -> Stmt
lower (MatMul out a b m n k) =
  -- for i in 0..m-1
  --   for j in 0..n-1
  --     C[i,j] = 0
  --     for k in 0..k-1
  --       C[i,j] = C[i,j] + A[i,k]*B[k,j]
  Seq
    [ For "i" m $ Seq
        [ For "j" n $ Seq
            [ Store out [EVar "i", EVar "j"] (EConst 0)
            , For "k" k $ Store out [EVar "i", EVar "j"]
                (EAdd (EIdx out [EVar "i", EVar "j"]) (EMul (EIdx a [EVar "i", EVar "k"]) (EIdx b [EVar "k", EVar "j"])))
            ]
        ]
    ]
lower (PointwiseAdd out a b m n) =
  Seq [ For "i" m $ For "j" n $ Store out [EVar "i", EVar "j"] (EAdd (EIdx a [EVar "i", EVar "j"]) (EIdx b [EVar "i", EVar "j"])) ]

-- Utility: substitute an index expression (e.g. replace EVar "i" occurrences) -- used by tiling
substExpr :: (String -> Maybe Expr) -> Expr -> Expr
substExpr s = \case
  EVar v -> fromMaybe (EVar v) (s v)
  EIdx a idxs -> EIdx a (map (substExpr s) idxs)
  EConst i -> EConst i
  EAdd x y -> EAdd (substExpr s x) (substExpr s y)
  EMul x y -> EMul (substExpr s x) (substExpr s y)

-- TILING: strip-mine a For loop with variable `v` and tile size `t`.
-- For v in 0..N-1 do body
-- -> For v_outer in 0..(ceil(N/t))-1 do
--      For v_inner in 0..t-1 do
--         let v = v_outer * t + v_inner
--         body[v]

tileFor :: String -> Int -> Stmt -> Stmt
tileFor v t = \case
  For var n body | var == v && t > 1 ->
    let outerN = (n + t - 1) `div` t
        inner = "" ++ var ++ "_inner"
        outer = var ++ "_outer"
        -- replace occurrences of var with (outer* t + inner)
        repl name = if name == var
                      then Just (EAdd (EMul (EVar outer) (EConst t)) (EVar inner))
                      else Nothing
        body' = substInStmt repl body
    in For outer outerN $ For inner t body'
  -- otherwise recurse
  For var n body -> For var n (tileFor v t body)
  Seq ss -> Seq (map (tileFor v t) ss)
  Let x e body -> Let x e (tileFor v t body)
  s -> s

-- substitute EVar occurrences in Stmt used by tiling
substInStmt :: (String -> Maybe Expr) -> Stmt -> Stmt
substInStmt s = \case
  For v n body -> For v n (substInStmt s body)
  Seq ss -> Seq (map (substInStmt s) ss)
  Store name idxs rhs -> Store name (map (substExpr s) idxs) (substExpr s rhs)
  Let x e body -> Let x (substExpr s e) (substInStmt s body)
  Intrinsic tag args -> Intrinsic tag args
  Skip -> Skip

-- INTERCHANGE: swap two adjacent loops with variables v1 and v2 when present
-- (for v1 .. for v2 .. body) -> (for v2 .. for v1 .. body)
interchange :: String -> String -> Stmt -> Stmt
interchange v1 v2 = \case
  For v1' n1 (For v2' n2 body) | v1' == v1 && v2' == v2 -> For v2 n2 (For v1 n1 body)
  For v n body -> For v n (interchange v1 v2 body)
  Seq ss -> Seq (map (interchange v1 v2) ss)
  Let x e body -> Let x e (interchange v1 v2 body)
  s -> s

-- FUSION: given two consecutive loops with same loop var and bound, merge bodies
-- Seq [For v n b1, For v n b2] -> For v n (Seq [b1, b2])
-- We do this at top-level sequences; recursive fusion will be achieved by repeated application.

fuseOnce :: Stmt -> Stmt
fuseOnce = \case
  Seq (For v n b1 : For v' n' b2 : rest) | v == v' && n == n' -> Seq (For v n (Seq [b1,b2]) : rest)
  Seq ss -> Seq (map fuseOnce ss)
  For v n body -> For v n (fuseOnce body)
  Let x e body -> Let x e (fuseOnce body)
  s -> s

fuseFully :: Stmt -> Stmt
fuseFully s = let s' = fuseOnce s in if s' == s then s else fuseFully s'

-- TENSORIZE: recognise inner-k reduction pattern for matmul and replace with Intrinsic("GEMM", [C,A,B,i,j,m,n,k])
-- Pattern to match:
-- For i .. For j .. (Store C[i,j] = 0 ; For k .. Store C[i,j] = C[i,j] + A[i,k]*B[k,j])
-- We will search for that exact shape and replace the inner k-loop by an Intrinsic node.

-- helper to find a nested pattern

matchMatMulPattern :: Stmt -> Maybe (String, String, String, Int, Int, Int)
matchMatMulPattern = \case
  Seq [ For i m (Seq [ For j n (Seq [ Store c idx0 (EConst 0)
                                    , For k kBound (Store c' idx1
                                        (EAdd (EIdx c2 idx2)
                                              (EMul (EIdx a idxA) (EIdx b idxB))))
                                    ])
                      ])
      ]
    | idx0 == [EVar i, EVar j]
    , idx1 == [EVar i, EVar j]
    , c == c' && c == c2
    , idx2 == [EVar i, EVar j]
    , idxA == [EVar i, EVar k]
    , idxB == [EVar k, EVar j]
    -> Just (c, a, b, m, n, kBound)
  _ -> Nothing



-- tensorize: replace the inner reduction with an Intrinsic when pattern matches
tensorize :: Stmt -> Stmt
tensorize s = case matchMatMulPattern s of
  Just (c,a,b,m,n,k) ->
    -- produce: for i for j Intrinsic "GEMM" [C,A,B,i,j]
    Seq [ For "i" m $ For "j" n $ Intrinsic "GEMM" [c,a,b, "i", "j", show m, show n, show k] ]
  Nothing -> case s of
    For v n body -> For v n (tensorize body)
    Seq ss -> Seq (map tensorize ss)
    Let x e body -> Let x e (tensorize body)
    other -> other

-- Utilities to apply a transformation across named loops: e.g. tile many vars
applyTiles :: M.Map String Int -> Stmt -> Stmt
applyTiles tiles s = foldr (.) id (map (\(v,t) -> tileFor v t) (M.toList tiles)) s

-- Example pipeline: lower -> tile -> interchange -> fusion -> tensorize
pipeline :: TensorOp -> M.Map String Int -> [(String,String)] -> Stmt
pipeline op tileMap inters =
  let base = lower op
      tiled = applyTiles tileMap base
      interchanged = foldl (\acc (x,y) -> interchange x y acc) tiled inters
      fused = fuseFully interchanged
      tens = tensorize fused
  in tens

-- Small examples and a main to print them
exampleMatMul :: TensorOp
exampleMatMul = MatMul { out = "C", a = "A", b = "B", m = 64, n = 64, kdim = 128 }

-- Example run that tiles i->32, j->32, k->8 and interchanges k_outer with i_inner (a common choice)
example1 :: Stmt
example1 = pipeline exampleMatMul (M.fromList [("i",32),("j",32),("k",8)]) [("k_outer","i_inner")]

-- Another example: just lowering
exampleLowered :: Stmt
exampleLowered = lower exampleMatMul

-- Main for quick GHCi testing
main :: IO ()
main = do
  putStrLn "--- LOWERED (naive) ---"
  putStrLn $ render exampleLowered
  putStrLn "\n--- TRANSFORMED (tiled, interchanged, fused, tensorized) ---"
  putStrLn $ render example1

-- End of toy-tensorir.hs
