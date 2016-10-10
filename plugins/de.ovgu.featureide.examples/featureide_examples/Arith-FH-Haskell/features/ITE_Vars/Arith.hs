module Arith where
{

  -- ITE 
  eval env (ITE exp1 exp2 exp3) = case eval env exp1 of
          { Result (TVDouble x)
              | x >= 0 -> eval env exp2
              | otherwise -> eval env exp3;
            Result _ -> Fail TypeError;
            Fail err -> Fail err}
}
