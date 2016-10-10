module Arith where
{
  data Exp a = Lam String (Exp a)				-- Lambda
             | App (Exp a) (Exp a)				-- Lambda
             deriving Show;
  
  -- TODO MRO: DivByZero bei BinOps ODER UnOps
  data EvalError = ApplicationError				-- Lambda
                 deriving Show;
  
  data TypedVal = TVFun (TypedVal -> Result TypedVal EvalError);					-- Strict and Static Lambdas
  
  
  instance Show TypedVal where
          { show (TVFun _) = "<<function>>"		-- Lambdas
          };
          
  eval :: Env TypedVal -> Exp TypedVal -> Result TypedVal EvalError;

  -- strict-static
  eval env (Lam x exp)
    = Result $ TVFun (\ val -> eval (addToEnv env x val) exp);

  eval env (App exp1 exp2)
    = case (eval env exp1, eval env exp2) of
          { (Result (TVFun f), Result arg) -> f arg;
            (Result (TVFun _), Fail err) -> Fail err;
            (Result _, _) -> Fail ApplicationError;
            (Fail err, _) -> Fail err}
}
