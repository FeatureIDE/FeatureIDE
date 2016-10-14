module CLI where
{ 
  iteExpr :: Parser (Exp TypedVal);
  iteExpr
    = do { reserved "ite";
           cond <- appArg;
           t <- appArg;
           e <- appArg;
           return (ITE cond t e)}
        <?> "conditional expression"
}
