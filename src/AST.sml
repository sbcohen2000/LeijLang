(*
 * Written by Samuel Burns Cohen
 * 
 * AST.sml
 *
 *)

structure AST = struct

type 'a env = (string * 'a) list

datatype ty = TYVAR of string
	    | TYCON of string
	    | CONAPP of ty * ty
	    | MU of string * ty
	    | TYEMPTYROW
	    | TYROW of (string * ty) * ty
			    
datatype decl = VAL of string * exp
	      | UNION of string * string list * (string * ty) list
     and exp = CONST of value
	     | VAR of string             
	     | ABS of lam                      (* abstraction            *)
	     | APP of exp * exp                (* application            *)
	     | LET of (string * exp) * exp
	     | IF of exp * exp * exp
	     | DOT of exp * string             (* record access          *)
	     | INJ of string * exp             (* variant injection      *)
	     | DEC of string * exp * exp * exp (* variant decomposition  *)
	     | EXN of string                   (* exception              *)
	     | RECORD_LITERAL of (string * exp) list
	     | PRIMAPP of string * exp list
	     | SUGAR of sugar
     and value = UNIT
	       | BOOL of bool
	       | NUM of int
	       | CLOSURE of lam * value ref env
	       | RECORD of (string * value) list
	       | VARIANT of string * value
     and sugar = MATCH of exp * (string * string * exp) list
	       | LIST of exp list
	       | BLOCK of decl list
withtype lam = string * exp

end
