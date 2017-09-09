{
 open Parser
 exception Eof
 exception LexicalError
 let comment_depth = ref 0
} 

let blank = [' ' '\n' '\t' '\r']+
let id = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']*
let number = ['0'-'9']+

rule start = parse 
	| blank { start lexbuf }
    | "/*" { comment_depth :=1; comment lexbuf; start lexbuf }
    | eof   { EOF}
    | "int" { INT }
    | '+' {PLUS}
    | '-' {MINUS}
    | '*' {STAR}
    | '/' {SLASH}
    | '=' {EQUAL}
    | "==" {EQUALEQUAL}
    | "<=" {LE}
    | '<' {LT}
    | ">=" {GE}
    | '>' {GT}
    | '!' {NOT}
    | "&&" {AND}
    | "||" {OR}
    | "if" {IF}
    | "else" {ELSE}
    | "while" {WHILE}
    | "do" {DO}
    | "read" {READ}
    | ';' {SEMICOLON}
    | "print" {PRINT}
    | '{' {LBRACE}
    | '}' {RBRACE}
    | '(' {LPAREN}
    | ')' {RPAREN}
    | '[' {LBLOCK}
    | ']' {RBLOCK}
    | number {NUM (int_of_string (Lexing.lexeme lexbuf))}
    | id {ID (Lexing.lexeme lexbuf)}
    | _ { raise LexicalError }


and comment = parse
     "/*" {comment_depth := !comment_depth+1; comment lexbuf}
   | "*/" {comment_depth := !comment_depth-1;
           if !comment_depth > 0 then comment lexbuf }
   | eof {raise Eof}
   | _   {comment lexbuf}