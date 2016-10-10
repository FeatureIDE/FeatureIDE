module Arith where
{
  data Exp a = ITE (Exp a) (Exp a) (Exp a)		-- ITE
             deriving Show
}
