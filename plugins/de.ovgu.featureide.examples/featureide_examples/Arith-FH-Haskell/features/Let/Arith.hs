module Arith where
{
  eval :: Env TypedVal -> Exp TypedVal -> Result TypedVal EvalError;
    eval env (Let defs exp)
    = case liftResult (map (eval env) exps) of
          { Result vals -> eval newEnv exp
              where { newEnv = addToEnvN env (zip names vals)};
            Fail e -> Fail e}
    where { (names, exps) = unzip defs}
  
}
