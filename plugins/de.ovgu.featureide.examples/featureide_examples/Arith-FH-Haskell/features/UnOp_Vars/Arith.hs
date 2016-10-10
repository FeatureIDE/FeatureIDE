module Arith where
{
  eval env (Unary op exp) = mapResult (tvUnOp op) (eval env exp)
}
