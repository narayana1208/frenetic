{
  open Lexing
  open Template_Parser

  let parse_byte str = Int64.of_string ("0x" ^ str)
  let parse_decbyte str = Int64.of_string str
}

let blank = [ ' ' '\t'  ]

let id      = ['a'-'z' 'A'-'z' '_']['a'-'z' 'A'-'z' '0'-'9' '_']*
let decimal = ['0'-'9']+
let float_  = ['0'-'9']+ '.' ['0'-'9']+
let hex     = "0x" ['0'-'9' 'a'-'f' 'A'-'F']+
let byte    = ['0'-'9' 'a'-'f' 'A'-'F']?  ['0'-'9' 'a'-'f' 'A'-'F']
let decbyte = (['0'-'9'] ['0'-'9'] ['0'-'9']) | (['0'-'9'] ['0'-'9']) | ['0'-'9']
let string_body = ([^'"'] | "\\\"")*

rule token = parse
  | "(*"    { block_comment lexbuf }
  | blank+  { token lexbuf }
  | '\n' { new_line lexbuf; token lexbuf }
  | eof { EOF }
  | "," { COMMA }
  | "in" { IN }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | ":" { COLON }
  | "pol" { TPOL }
  | "pred" { TPRED }

  | "true" { TRUE }
  | "false" { FALSE }
  | "<none>" { NONE }
  | "=" { EQUALS }
  | "switch" { SWITCH }
  | "port" { PORT }
  | "ethSrc" { SRCMAC }
  | "ethDst" { DSTMAC }
  | "ethTyp" { FRAMETYPE }
  | "vlanId" { VLAN }
  (* | "vlanPcp" { VLANPCP } *)
  | "ipSrc" { SRCIP }
  | "ipDst" { DSTIP }
  | "ipProto" { PROTOCOLTYPE }
  | "tcpSrcPort" { TCPSRCPORT }
  | "tcpDstPort" { TCPDSTPORT }
  | "arp" { ARP }
  | "ip" { IP }
  | "icmp" { ICMP }
  | "tcp" { TCP }
  | "udp" { UDP }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "let" { LET }
  | ";" { SEMI }
  | "+" { PLUS }
  | "fun"  { FUN }
  | "||"   { PIPEPIPE }
  | "&&"   { AMPAMP }
  | "!"    { BANG }
  | ":="   { COLONEQ }
  | "->"   { RARROW }
  | "macAddr" { TMACVAL }
  | "ipAddr" { TIPVAL }
  | "drop"     { DROP }
  | "pass"     { PASS }
  | "@"        { AT }
  | "=>"       { DBLARROW }

  | (byte as n6) ":" (byte as n5) ":" (byte as n4) ":" (byte as n3) ":" 
    (byte as n2) ":" (byte as n1) 
    { let open Int64 in
      MACADDR
        (logor (shift_left (parse_byte n6) 40)
           (logor (shift_left (parse_byte n5) 32)
              (logor (shift_left (parse_byte n4) 24)
                 (logor (shift_left (parse_byte n3) 16)
                    (logor (shift_left (parse_byte n2) 8)
                       (parse_byte n1)))))) }

  (* | float_ as f { FLOAT (float_of_string f) } *)

  | (decbyte as b4) "." (decbyte as b3) "." (decbyte as b2) "." (decbyte as b1)
    { let open Int64 in
      IPADDR 
        (logor (shift_left (parse_decbyte b4) 24)
           (logor (shift_left (parse_decbyte b3) 16)
              (logor (shift_left (parse_decbyte b2) 8)
                 (parse_decbyte b1)))) }

  | decimal as n { INT64 (Int64.of_string n) } 
  | hex as n { INT64 (Int64.of_string n) }
  (* | '"' (string_body as s) '"' { STRING s } *)
  | id as x { IDENT x }

and block_comment = parse
  | "*)" {  token lexbuf }
  | "*" { block_comment lexbuf }
  | [ '\n' ] { new_line lexbuf; block_comment lexbuf }
  | ([^ '\n' '*'])+  { block_comment lexbuf }
