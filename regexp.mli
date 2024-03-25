type regexp_t =
  | Empty_String
  | Char of char
  | Union of regexp_t * regexp_t
  | Concat of regexp_t * regexp_t
  | Star of regexp_t


val regexp_to_nfa : regexp_t -> (int, char) Nfa.nfa_t

val string_to_regexp : string -> regexp_t

val string_to_nfa : string -> (int, char) Nfa.nfa_t

exception IllegalExpression of string
