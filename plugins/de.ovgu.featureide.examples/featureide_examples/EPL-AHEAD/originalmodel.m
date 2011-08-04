Root : Ops+ Structs Flattened :: top ;

Ops : Kore [Print] [Eval] :: Str ;

Structs : Core Num [Neg] [Plus] :: Op ;

Flattened : CK [CE] [CP] BK [BE] [BP] [NK] [NE] [NP] [PK] [PE] [PP] :: All ;

%%

Neg implies NK ;
Plus implies PK ;
Eval implies CE and BE ;
Print implies CP and BP ;
Neg and Eval implies NE ;
Plus and Eval implies PE ;
Neg and Print implies NP ;
Plus and Print implies PP ;

##

Ops { eqn }
Structs { eqn }
Flattened { hidden  eqn }

