module Arith where
{
  eval env (Binary op exp1 exp2)
    = zipResult (tvBinOp op) (eval env exp1) (eval env exp2)
}
