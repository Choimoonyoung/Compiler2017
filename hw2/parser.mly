%{

%}

%token <int> NUM
%token <string> ID
%token INT PLUS MINUS STAR SLASH EQUAL EQUALEQUAL LE LT GE GT NOT AND OR IF ELSE WHILE DO READ PRINT SEMICOLON
%token LBRACE RBRACE LBLOCK RBLOCK LPAREN RPAREN EOF 

%nonassoc THEN
%nonassoc ELSE
%left EQUAL
%left OR
%left AND
%left EQUALEQUAL
%left LE LT GT GE
%left PLUS MINUS
%left STAR SLASH
%left NOT
%nonassoc UMINUS



%start program
%type <S.program> program
%%

program:
    block EOF { $1 }
    ;

block:
    LBRACE decls stmts RBRACE { ($2,$3) }
    ;

decls:
   |  { [] }
   |  decls decl { $1@[$2] }
    ;

decl:
	| typ ID SEMICOLON { ($1,$2) }
	;

typ:
	|INT { S.TINT }
	|INT LBLOCK NUM RBLOCK { S.TARR($3) }
	;

stmts:
   |  { [] }
   | stmts stmt { $1@[$2] }
    ;

stmt:
	| lv EQUAL e SEMICOLON { S.ASSIGN($1,$3)}
	| lv PLUS PLUS SEMICOLON {S.ASSIGN($1,S.ADD(S.LV($1),S.NUM(1)))}
	| IF LPAREN e RPAREN stmt ELSE stmt {S.IF($3,$5,$7)}
	| IF LPAREN e RPAREN stmt %prec THEN {S.IF($3,$5,S.BLOCK([],[]))}
	| WHILE LPAREN e RPAREN stmt {S.WHILE($3,$5)}
	| DO stmt WHILE LPAREN e RPAREN SEMICOLON {S.DOWHILE($2,$5)}
	| READ LPAREN ID RPAREN SEMICOLON {S.READ($3)}
	| PRINT LPAREN e RPAREN SEMICOLON {S.PRINT($3)}
	| block {S.BLOCK($1)}
	;

lv: 
	|ID {S.ID($1)}
	|ID LBLOCK e RBLOCK {S.ARR($1,$3)}
	;

e:
	| NUM {S.NUM($1)}
	| lv {S.LV($1)}
	| e PLUS e {S.ADD($1,$3)}
	| e MINUS e {S.SUB($1,$3)}
	| e STAR e {S.MUL($1,$3)}
	| e SLASH e {S.DIV($1,$3)}
	| MINUS e %prec UMINUS {S.MINUS($2)}  
	| e EQUALEQUAL e {S.EQ($1,$3)}    
	| e LT e {S.LT($1,$3)}   
	| e LE e {S.LE($1,$3)}  
	| e GE e {S.GE($1,$3)} 
	| e GT e {S.GT($1,$3)}   
	| NOT e {S.NOT($2)}
	| e OR e {S.OR($1,$3)}
	| e AND e {S.AND($1,$3)}
	| LPAREN e RPAREN {$2}