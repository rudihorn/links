(** The context used by the lexer *)
type lexer_context

(** Create a new lexing context *)
val fresh_context : unit -> lexer_context

(** An unexpected character was encountered in the lexing buffer. *)
exception LexicalError of (string * Lexing.position)

(** The entry point to the lexer. *)
val lexer : lexer_context
         -> newline_hook:(unit -> unit) 
         -> (Lexing.lexbuf -> Parser_links.token)