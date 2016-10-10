module CLI where
{
  boolConst :: Parser (Exp TypedVal);
  boolConst
    = do { reserved "true";
           return (Const (TVBool True))}
      <|>
      do { reserved "false";
           return (Const (TVBool False))}
      <?> "bool constant"
}
