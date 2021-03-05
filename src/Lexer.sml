(*
 * Written by Samuel Burns Cohen
 * 
 * Lexer.sml
 *
 *)

structure Tokens =
struct
type location = int * int
datatype payload = STRING of string
		 | INT of int
		 | EMPTY
datatype token = TOKEN of kind * location * payload
     and kind = NAME        (* constants *)
	      | NUMBER
	      | QUOTE
	      | TRUE
	      | FALSE
	      | UNIT
	      | DOT         (* punctuation *)
	      | SEMICOLON
	      | COMMA
	      | PIPE
	      | UNDERSCORE
	      | OPENROUND
	      | CLOSEROUND
	      | OPENSQUARE
	      | CLOSESQUARE
	      | OPENCURLY
	      | CLOSECURLY
	      | EQ          (* operators *)
	      | ARROW
	      | TYARROW
	      | PLUS
	      | MINUS
	      | STAR
	      | SLASH
	      | PERCENT
	      | LESS
	      | MORE
	      | LESSEQUAL
	      | MOREEQUAL
	      | AND
	      | OR
	      | OF          (* keywords *)
	      | UNION
	      | RAISE
	      | MATCH
	      | WITH
	      | END
	      | IF
	      | THEN
	      | ELSE
	      | VAL
	      | FUN
	      | MODULE
	      | FN
	      | EOF         (* sentinels *)
	      | ERROR

fun mkEOF () = TOKEN (EOF, (~1, ~1), EMPTY)

fun eqToken (a : token, b : token) =
    let val TOKEN (kindA, _, _) = a
	val TOKEN (kindB, _, _) = b
    in kindA = kindB
    end

fun kindOf (a : token) =
    let val TOKEN (kind, _, _) = a
    in kind
    end

fun locationOf (a : token) =
    let val TOKEN (_, location, _) = a
    in location
    end
	
fun isEOF (TOKEN (EOF, _, _)) = true
  | isEOF _ = false

fun stringOf (TOKEN (_, _, STRING s)) = SOME s
  | stringOf _ = NONE

fun intOf (TOKEN (_, _, INT i)) = SOME i
  | intOf _ = NONE
		  
end

signature LEXER =
sig
    type lexer
    exception LexError
    val newLexer : string -> lexer
    val nextToken : lexer -> (Tokens.token * lexer)
    val kindString : Tokens.kind -> string
    val tokenString : Tokens.token -> string
end

structure Lexer :> LEXER =
struct
open Tokens
(* source string, current token string, token location *)
type lexer = char list * string * location
exception LexError
			     
exception endOfString
fun consume ([], tokenString, _) = raise endOfString
  | consume (c::src, tokenString, (row, col)) =
    (src, tokenString ^ Char.toString c,
     (if c = #"\n" then row + 1 else row,
      if c = #"\n" then 0 else col + 1))
	
fun peek ([], _, _) = raise endOfString
  | peek (c::src, _, _) = c
			   
fun newLexer str = (String.explode str, "", (1, 0))

fun locationOf (_, _, l) = l
			       
fun consumeWhile pred lexer =
    let fun f lexer =
	    let val c = peek lexer
	    in if pred c
	       then f (consume lexer)
	       else lexer
	    end
    in f lexer
    end
	
fun isAllowedNameChar c = Char.isAlpha c
			  orelse Char.isDigit c
			  orelse c = #"_"
			  orelse c = #"-"
			  orelse c = #"'"
			  orelse c = #"?"

fun isAllowedQuoteChar c = Char.isAscii c
			   andalso not (c = #";")
			   andalso not (c = #"(")
			   andalso not (c = #")")
			   andalso not (c = #",")
			   andalso not (Char.isSpace c)

fun keyword lexer =
    let val newLexer = consumeWhile Char.isAlpha lexer
	val (_, keywordText, _) = newLexer
	val (_, _, location) = lexer
	fun mkToken v = TOKEN (v, location, EMPTY)
	val keywords = [("true",   mkToken   TRUE),
			("false",  mkToken  FALSE),
			("of",     mkToken     OF),
			("union",  mkToken  UNION),
			("raise",  mkToken  RAISE),
			("match",  mkToken  MATCH),
			("with",   mkToken   WITH),
			("end",    mkToken    END),
			("if",     mkToken     IF),
			("then",   mkToken   THEN),
			("else",   mkToken   ELSE),
			("val",    mkToken    VAL),
			("fun",    mkToken    FUN),
			("module", mkToken MODULE),
			("fn",     mkToken     FN)]
			   
	fun eliminate (testText, []) = NONE
	  | eliminate (testText, ((text, node)::ks)) =
	    if testText = text then SOME node
	    else eliminate (testText, ks)
			   
	val possibleToken = eliminate (keywordText, keywords)
    in case possibleToken of token as (SOME _) => (newLexer, token)
			   | NONE => (lexer, NONE)
    end

						      
fun name lexer =
    let val newLexer = consumeWhile isAllowedNameChar lexer
	val (_, nameStr, _) = newLexer
    in (newLexer, SOME (TOKEN (NAME, locationOf lexer, STRING nameStr)))
    end

fun quote lexer =
    let val newLexer = consumeWhile isAllowedQuoteChar lexer
	val (_, quoteStr, _) = newLexer
    in (newLexer, SOME (TOKEN (QUOTE, locationOf lexer, STRING quoteStr)))
    end

fun number lexer =
    let val newLexer = consumeWhile Char.isDigit lexer
	val (_, numStr, _) = newLexer
	val possibleNum = Int.fromString numStr
    in case possibleNum of SOME n => (newLexer,
				      SOME (TOKEN (NUMBER, locationOf lexer, INT n)))
			 | NONE => (lexer, NONE)
    end

local fun lookahead lexer =
	  let val lexer = consume lexer
	  in peek lexer
	  end
	      
in fun consumeComment lexer =
       let val commentDepth = ref 0
	   fun f lexer =
	       let val this = peek lexer
		   val next = lookahead lexer
		   val lexer = if this = #"/" andalso next = #"*"
			       then lexer before commentDepth := (!commentDepth) + 1
			       else if this = #"*" andalso next = #"/"
			       then consume (consume lexer) before commentDepth := (!commentDepth) - 1
			       else lexer
	       in if !commentDepth = 0 then lexer else f (consume lexer)
	       end
       in f lexer
       end

   fun consumeWhitespace lexer =
       let fun f lexer =
	       let val this = peek lexer
		   val next = lookahead lexer
		   val lexer = if this = #"/" andalso next = #"*"
			       then consumeComment lexer
			       else lexer
		   val c = peek lexer
		   val lexer = if Char.isSpace c
			       then f (consume lexer)
			       else lexer
	       in lexer
	       end
       in f lexer
       end
end	    

fun resetTokenStr lexer =
    let val (str, _, location) = lexer
    in (str, "", location)
    end
	
fun nextToken lexer =
    let val lexer = consumeWhitespace lexer
	val lexer = resetTokenStr lexer
	val char = peek lexer
	val p as (lexer, possibleToken) = (consume lexer, NONE)
					  handle endOfString =>
						 (lexer, SOME (mkEOF ()))
								    
	fun attemptLex ((lexer, possibleToken), pred, action) =
	    case possibleToken of NONE => if pred char
					  then action lexer
					  else (lexer, NONE)
				| t as SOME _ => (lexer, t)

	val p as(lexer, possibleToken) =
	    attemptLex (p, (fn c => c = #"'"), quote)
		       
	val p as (lexer, possibleToken) =
	    attemptLex (p, Char.isDigit, number)
		       
	val p as (lexer, possibleToken) =
	    attemptLex (p, Char.isAlpha,
			(fn lexer =>
			    case keyword lexer
			     of k as (_, SOME t) => k
			      | (lexer, NONE) => name lexer))

	val (lexer, possibleToken) =
	    case possibleToken
	     of NONE =>
		let fun mkToken v = SOME (TOKEN (v, (locationOf lexer), EMPTY))
		in (case char
		     of #"." => (lexer, mkToken         DOT)
		      | #";" => (lexer, mkToken   SEMICOLON)
		      | #"," => (lexer, mkToken       COMMA)
		      | #"|" => if peek lexer = #"|" then
				    (consume lexer, mkToken OR)
				else (lexer, mkToken PIPE)
		      | #"_" => (lexer, mkToken  UNDERSCORE)
		      | #"(" => if peek lexer = #")" then
				    (consume lexer, mkToken UNIT)
				else (lexer, mkToken OPENROUND)
		      | #")" => (lexer, mkToken  CLOSEROUND)
		      | #"[" => (lexer, mkToken  OPENSQUARE)
		      | #"]" => (lexer, mkToken CLOSESQUARE)
		      | #"{" => (lexer, mkToken   OPENCURLY)
		      | #"}" => (lexer, mkToken  CLOSECURLY)
		      | #"=" => if peek lexer = #">" then
				    (consume lexer, mkToken ARROW)
				else (lexer, mkToken EQ)
		      | #"-" => if peek lexer = #">" then
				    (consume lexer, mkToken TYARROW)
				else (lexer, mkToken MINUS)
		      | #"+" => (lexer, mkToken        PLUS)
		      | #"*" => (lexer, mkToken        STAR)
		      | #"/" => (lexer, mkToken       SLASH)
		      | #"%" => (lexer, mkToken     PERCENT)
		      | #"<" => if peek lexer = #"=" then
				    (consume lexer, mkToken LESSEQUAL)
				else (lexer, mkToken LESS)
		      | #">" => if peek lexer = #"=" then
				    (consume lexer, mkToken MOREEQUAL)
				else (lexer, mkToken MORE)
		      | #"&" => if peek lexer = #"&" then
				    (consume lexer, mkToken AND)
				else (lexer, NONE)
		      | _ => (lexer, NONE))
		end
	      | t as SOME _ => (lexer, t)

    in case possibleToken of SOME t => (t, lexer)
			   | NONE => (TOKEN (ERROR, locationOf lexer,
					     STRING 
						 ("illegal char: \"" ^
						  Char.toString char ^
						  "\"")), lexer)
    end
    handle endOfString => (mkEOF (), lexer)

fun kindString NAME        = "name"
  | kindString NUMBER      = "number"
  | kindString QUOTE       = "quote"
  | kindString TRUE        = "`true'"
  | kindString FALSE       = "`false'"
  | kindString UNIT        = "`()'"
  | kindString DOT         = "`.'"
  | kindString SEMICOLON   = "`;'"
  | kindString COMMA       = "`,'"
  | kindString PIPE        = "`|'"
  | kindString UNDERSCORE  = "`_'"
  | kindString OPENROUND   = "`('"
  | kindString CLOSEROUND  = "`)'"
  | kindString OPENSQUARE  = "`['"
  | kindString CLOSESQUARE = "`]'"
  | kindString OPENCURLY   = "`{'"
  | kindString CLOSECURLY  = "`}'"
  | kindString EQ          = "`='"
  | kindString ARROW       = "`=>'"
  | kindString TYARROW     = "`->'"
  | kindString PLUS        = "`+'"
  | kindString MINUS       = "`-'"
  | kindString STAR        = "`*'"
  | kindString SLASH       = "`/'"
  | kindString PERCENT     = "`%'"
  | kindString LESS        = "`<'"
  | kindString MORE        = "`>'"
  | kindString LESSEQUAL   = "`<='"
  | kindString MOREEQUAL   = "`>='"
  | kindString AND         = "`&&'"
  | kindString OR          = "`||'"
  | kindString OF          = "`of'"
  | kindString UNION       = "`union'"
  | kindString RAISE       = "`raise'"
  | kindString MATCH       = "`match'"
  | kindString WITH        = "`with'"
  | kindString END         = "`end'"
  | kindString IF          = "`if'"
  | kindString THEN        = "`then'"
  | kindString ELSE        = "`else'"
  | kindString VAL         = "`val'"
  | kindString FUN         = "`fun'"
  | kindString MODULE      = "`module'"
  | kindString FN          = "`fn'"
  | kindString EOF         = "EOF"
  | kindString ERROR       = "ERROR:"
			      
fun tokenString t =
    let val TOKEN (kind, _, payload) = t
	val payloadString = case payload of STRING s => " \"" ^ s ^ "\""
					  | INT i => " (" ^ Int.toString i ^ ")"
					  | EMPTY => ""
    in kindString kind ^ payloadString
    end

end
