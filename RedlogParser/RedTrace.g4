grammar RedTrace;

prog : PREAMBULA expr POSTAMBULA EOF;

expr : '(' and expr+ ')'
     | '(' or expr+ ')'
     | '(' ncgong body nil ')'
     | '(' equal body nil ')'
     | '(' gr body nil ')'
     | '(' ls body nil ')'
     | '(' neq body nil ')'
     | '(' leq body nil ')'
     | '(' geq body nil ')'
     | '(' ball id expr expr ')'
     ;

//body : '('( factor | '('mul(')'?) |  num)+(')'?);
body : '('(factor | num | '('mul')')+')';

mul : factor
    | power ( factor | num |  '(' mul ')' )+
    ;

ncgong : '(' NCONG (factor | num | '('mul')')+ ')';

factor : '('power'.'number')';
power : '('id'.'number')';
num : '.'number;

number : NUM;
id : ID;
and : AND;
or : OR;
equal : EQUAL;
gr : GR;
ls : LS;
neq : NEQ;
leq : LEQ;
geq : GEQ;
ball : BALL;
nil : NIL;

AND : 'and';
OR : 'or';
EQUAL : 'equal';
GR : 'greaterp';
LS : 'lessp';
LEQ : 'leq';
NEQ : 'neq';
GEQ : 'geq';
NCONG : 'ncong';
BALL : 'ball';
NIL : 'nil';

PREAMBULA : '(!*fof (pasf)';
POSTAMBULA : 't)';
ID : '!_'?[a-z]+('_'?)NUM;
NUM : '0' | '-'?[1-9][0-9]*;
WS : [ \t\n]+ -> skip;















