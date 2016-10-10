module CLI where
{   
  table
  -- TODO MRO: && und ||
    = [[op "*" Mul AssocLeft, op "/" Div AssocLeft],
       [op "+" Add AssocLeft, op "-" Sub AssocLeft],
       [op "&&" And AssocLeft], [op "||" Or AssocLeft]]
    where { op s f assoc
              = Infix
                  (do { reservedOp s;
                        return (Binary f)}
                     <?> "operator")
                  assoc}
}
