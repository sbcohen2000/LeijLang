(*
 * Written by Samuel Burns Cohen
 *
 * Parser.sml
 *
 *)

signature PARSER =
sig
    type parser
    exception SyntaxError of string
    val newParser : Lexer.lexer -> parser
    val parse : parser -> AST.decl list
end

structure Parser :> PARSER =
struct
open AST

(* next token, the lexer *)
type parser = Tokens.token * Lexer.lexer
exception SyntaxError of string
			     
fun newParser l = Lexer.nextToken l

fun peek (theToken, lexer) = theToken

val _ = op peek : parser -> Tokens.token
				  
fun consume (theToken, lexer) targetKind =
    let val (nextToken, newLexer) = Lexer.nextToken lexer
    in if (Tokens.kindOf theToken) = targetKind
       then (true, (nextToken, newLexer))
       else (false, (theToken, lexer))
    end

val _ = op consume : parser -> Tokens.kind -> (bool * parser)

fun consumeIf cond p targetKind =
    if cond then consume p targetKind else (false, p)

fun locationString token =
    let val (line, col) = Tokens.locationOf token
    in (Int.toString line ^ ":" ^ Int.toString col)
    end
					       
fun expect (parser as (theToken, _)) targetKind =
    let val (didConsume, parser) = consume parser targetKind
    in if didConsume then parser
       else raise SyntaxError ("expected " ^ Lexer.kindString targetKind ^
			       " but got " ^ Lexer.tokenString theToken ^
			       " at " ^ locationString theToken ^ "\n")
    end

val _ = op expect : parser -> Tokens.kind -> parser

fun extractString parser = case Tokens.stringOf (peek parser) of SOME s => s
							       | NONE => "MISSING PAYLOAD"

fun extractNumber parser = case Tokens.intOf (peek parser) of SOME i => i
							    | NONE => 0


fun notAnyOf [] = true
  | notAnyOf (b::bs) = not b andalso notAnyOf bs
					      
fun tyvarList p =
    let val quoteContents = extractString p
	val (gotQuote, p) = consume p Tokens.QUOTE
    in if gotQuote then let val (l, p) = tyvarList p
			in (quoteContents::l, p)
			end
       else ([], p)
    end

fun arg p =
    let val argContents = extractString p
	val (gotName, p) = consume p Tokens.NAME
    in if gotName
       then (argContents, p)
       else ("_", expect p Tokens.UNDERSCORE)
    end

fun argList p =
    let val (argContents, p) = arg p
    in if Tokens.kindOf (peek p) = Tokens.NAME
	  orelse Tokens.kindOf (peek p) = Tokens.UNDERSCORE
       then let val (l, p) = argList p
	    in (argContents::l, p)
	    end
       else ([argContents], p)
    end

val _ = op tyvarList : parser -> (string list * parser)

fun tyExp p =
    let fun groupTyExp p =
	    let val (t, p) = tyExp p
		val p = expect p Tokens.CLOSEROUND
	    in (SOME t, p)
	    end

	fun funTyExp (SOME ta, p) =
	    let val (tb, p) = tyExp p
	    in (SOME (CONAPP (ta, tb)), p)
	    end
	  | funTyExp (NONE, p) = (NONE, p)

	fun recordTyExp p =
	    let val (t, p) = recordTy p
		val p = expect p Tokens.CLOSECURLY
	    in (SOME (CONAPP (TYCON "record", t)), p)
	    end

	val (gotParen, p) = consume p Tokens.OPENROUND
	val (t, p) = if gotParen then groupTyExp p else (NONE, p)
	val (gotUnit, p) = consumeIf (notAnyOf [gotParen]) p Tokens.UNIT
	val (t, p) = if gotUnit then (SOME (TYCON "unit"), p) else (t, p)
	val (gotCurly, p) = consumeIf (notAnyOf [gotParen, gotUnit]) p Tokens.OPENCURLY
	val (t, p) = if gotCurly
		     then recordTyExp p else (NONE, p)
	val tyconOrAlphaString = extractString p
	val (gotName, p) = consumeIf (notAnyOf [gotParen, gotUnit, gotCurly]) p Tokens.NAME
	val (t, p) = if gotName 
		     then (SOME (TYCON tyconOrAlphaString), p)
		     else (t, p)
	val (gotQuote, p) = consumeIf (notAnyOf [gotName, gotCurly, gotUnit, gotParen]) p Tokens.QUOTE
	val (t, p) = if gotQuote
		     then (SOME (TYVAR tyconOrAlphaString), p)
		     else (t, p)
	val (gotArrow, p) = consume p Tokens.TYARROW
	val (t, p) = if gotArrow
		     then funTyExp (t, p)
		     else (t, p)
	val (t, p) = case t of SOME t => (t, p)
			     | NONE => raise SyntaxError ("Unexpected " ^
							  Lexer.tokenString (peek p) ^
							  " in type expression")
    in (t, p)
    end

and recordTy p =
    let fun recordPair p =
	    let val field = extractString p
		val p = expect p Tokens.NAME
		val p = expect p Tokens.EQ
		val (ty, p) = tyExp p
	    in ((field, ty), p)
	    end
		
	val (elem, p) = recordPair p
	val (gotComma, p) = consume p Tokens.COMMA
    in if gotComma then let val (rest, p) = recordTy p
		       in (TYROW (elem, rest), p)
		       end
       else (TYROW (elem, TYEMPTYROW), p)
    end

fun unionBody p =
    let fun variantPair p =
	    let val variant = extractString p
		val p = expect p Tokens.NAME
		val (gotOf, p) = consume p Tokens.OF
		val (ty, p) = if gotOf then tyExp p else (TYCON "unit", p)
	    in ((variant, ty), p)
	    end
		
	val (elem, p) = variantPair p
	val (gotPipe, p) = consume p Tokens.PIPE
    in if gotPipe then let val (rest, p) = unionBody p
		       in (elem::rest, p)
		       end
       else ([elem], p)
    end

val _ = op unionBody : parser -> ((string * AST.ty) list * parser)
						 
(* 
 * Returns true if a block is directly ahead,
 * false if a record is directly ahead.
 *  
 * blocks and record literals look the same 
 * with potentially more than 1 token of lookahead.
 * This function cheats a little by searching for the end
 * of the { ... }. If the { ... } is terminated with a semicolon,
 * its a block, else its a record literal. 
 *)

exception UnmatchedCurly
fun lookaheadToBlockType p =
    let val p = expect p Tokens.OPENCURLY
	val curlyDepth = ref 1
	fun search (lastToken, lexer) = 
	    let val p' = Lexer.nextToken lexer
	    in case Tokens.kindOf (peek p')
		of Tokens.CLOSECURLY =>
		   let val _ = curlyDepth := !(curlyDepth) - 1
		   in if !curlyDepth < 0 then raise UnmatchedCurly
		      else if !curlyDepth = 0 then Tokens.kindOf lastToken = Tokens.SEMICOLON
		      else search p'
		   end
		 | Tokens.EOF => raise UnmatchedCurly
		 | _ => search p'
	    end
    in search p
    end

fun pattern p =
    let val variantName = extractString p
	val p = expect p Tokens.NAME
	val alphaName = extractString p
	val p = expect p Tokens.NAME
    in ((variantName, alphaName), p)
    end

local fun oneOf _ [] = false
	| oneOf k (kind::kinds) = kind = k orelse oneOf k kinds
							
in fun isConstStarter token =
       let open Tokens
	   val oneOf = oneOf (Tokens.kindOf token)
       in oneOf [NUMBER, TRUE, FALSE, UNIT, OPENSQUARE, OPENCURLY]
       end

   fun isExprStarter token =
       let open Tokens
	   val oneOf = oneOf (Tokens.kindOf token)
       in isConstStarter token orelse
	  oneOf [OPENROUND, NAME, FN, IF, MATCH,
		 OPENCURLY, RAISE]
       end

   fun isInfixStarter token =
       let open Tokens
	   val oneOf = oneOf (Tokens.kindOf token)
       in oneOf [DOT, EQ, PLUS, MINUS, STAR, SLASH, PERCENT,
		 LESS, MORE, LESSEQUAL, MOREEQUAL, AND, OR]
       end
end

fun expr p =
    let fun app p =
	    let val gotStarter = isExprStarter (peek p)
	    in if gotStarter then let val (nextE, p) = term p
				      val (rest, p) = app p
				  in (nextE::rest, p)
				  end
	       else ([], p)
	    end

	val (e, es, p) = case app p of ([], _) => raise SyntaxError ("Empty expr " ^
								     Lexer.tokenString (peek p) ^
								     " at " ^ 
								     locationString (peek p) ^
								     "\n")
				     | (e::es, p) => (e, es, p)
	val (e, p) = (List.foldl (fn (f, rest) => APP (rest, f)) e es, p)
    in (e, p)
    end
	
and term p =
    let fun groupExpr p =
	    let val (e, p) = expr p
		val p = expect p Tokens.CLOSEROUND
	    in (SOME e, p)
	    end

	fun fnExpr p =
	    let val argText = extractString p
		val p = expect p Tokens.NAME
		val p = expect p Tokens.ARROW
		val (e, p) = expr p
	    in (SOME (ABS (argText, e)), p)
	    end

	fun ifExpr p =
	    let val (condE, p) = expr p
		val p = expect p Tokens.THEN
		val (thenE, p) = expr p
		val p = expect p Tokens.ELSE
		val (elseE, p) = expr p
	    in (SOME (IF (condE, thenE, elseE)), p)
	    end

	fun matchExpr p =
	    let val (matchE, p) = expr p
		val p = expect p Tokens.WITH
		val (ms, p) = matches p
	    in (SOME (SUGAR (MATCH (matchE, ms))), p)
	    end

	fun raiseExpr p =
	    let val raiseText = extractString p
		val p = expect p Tokens.NAME
	    in (SOME (EXN raiseText), p)
	    end

	val (gotParen, p) = consume p Tokens.OPENROUND
	val (e, p) = if gotParen 
		     then groupExpr p else (NONE, p)
	val gotCurly = Tokens.kindOf (peek p) = Tokens.OPENCURLY
	val (e, p) = if gotCurly andalso notAnyOf [gotParen] (* block *)
		     then if lookaheadToBlockType p then
			      let val p = expect p Tokens.OPENCURLY
				  val (blockContents, p) = blockExpr p
			      in (SOME (SUGAR (BLOCK blockContents)), p)
			      end
			  else (e, p) else (e, p)
	val gotConst = isConstStarter (peek p)
	val (e, p) = if gotConst andalso notAnyOf [gotParen]
		     then let val (e, p) = constExpr p in (SOME e, p) end else (e, p)
	val possibleNameText = extractString p
	val (gotName, p) = consumeIf (notAnyOf [gotParen, gotCurly,
						gotConst]) p Tokens.NAME
	val (e, p) = if gotName 
		     then (SOME (VAR possibleNameText), p) else (e, p)
	val (gotFn, p) = consumeIf (notAnyOf [gotParen, gotCurly,
					      gotConst, gotName]) p Tokens.FN
	val (e, p) = if gotFn
		     then fnExpr p else (e, p)
	val (gotIf, p) = consumeIf (notAnyOf [gotParen, gotCurly, gotConst,
					      gotName, gotFn])
				   p Tokens.IF
	val (e, p) = if gotIf
		     then ifExpr p else (e, p)
	val (gotMatch, p) = consumeIf (notAnyOf [gotParen, gotCurly, gotConst,
						 gotName, gotFn, gotIf])
				      p Tokens.MATCH
	val (e, p) = if gotMatch
		     then matchExpr p else (e, p)
	val (gotRaise, p) = consumeIf (notAnyOf [gotParen, gotCurly, gotConst,
						 gotName, gotFn, gotIf, gotMatch])
				      p Tokens.RAISE
	val (e, p) = if gotRaise
		     then raiseExpr p else (e, p)
	val (e, p) = case e of SOME e => (e, p)
			     | NONE => raise SyntaxError ("Unexpected " ^
							  Lexer.tokenString (peek p) ^
							  " in expression")
	val gotInfix = isInfixStarter (peek p)
	val (e, p) = if gotInfix then infixExpr (e, p) else (e, p)
    in (e, p)
    end

and blockExpr p =
    let fun valBinding p =
	    let val name = extractString p
		val p = expect p Tokens.NAME
		val p = expect p Tokens.EQ
		val (e, p) = expr p
		val p = expect p Tokens.SEMICOLON
	    in (VAL (name, e), p)
	    end

	fun rawExpr p =
	    let val (e, p) = expr p
		val p = expect p Tokens.SEMICOLON
	    in (VAL ("_", e), p)
	    end

	val (gotVal, p) = consume p Tokens.VAL
	val (binding, p) = if gotVal then valBinding p else rawExpr p
	val (gotClose, p) = consume p Tokens.CLOSECURLY
    in if gotClose then ([binding], p)
       else let val (rest, p) = blockExpr p
	    in (binding::rest, p)
	    end
    end

and matches p =
    let fun patternPair p =
	    let val (pat, p) = pattern p
		val p = expect p Tokens.ARROW
		val (e, p) = expr p
		val (var, alpha) = pat
	    in ((var, alpha, e), p)
	    end
		
	val (match, p) = patternPair p
	val (gotPipe, p) = consume p Tokens.PIPE
    in if gotPipe then let val (rest, p) = matches p
		       in (match::rest, p)
		       end
       else ([match], p)
    end

and constExpr p =
    let val possibleNum = extractNumber p
	val (gotNum, p) = consume p Tokens.NUMBER
	val (e, p) = if gotNum
		     then (SOME (CONST (NUM possibleNum)), p)
		     else (NONE, p)
	val (gotTrue, p) = consumeIf (notAnyOf [gotNum]) p Tokens.TRUE
	val (e, p) = if gotTrue then (SOME (CONST (BOOL true)), p) else (e, p)
	val (gotFalse, p) = consumeIf (notAnyOf [gotNum, gotTrue]) p Tokens.FALSE
	val (e, p) = if gotFalse then (SOME (CONST (BOOL false)), p) else (e, p)
	val (gotUnit, p) = consumeIf (notAnyOf [gotNum, gotTrue, gotFalse]) p Tokens.UNIT
	val (e, p) = if gotUnit then (SOME (CONST UNIT), p) else (e, p)
	val (gotSquare, p) = consumeIf (notAnyOf [gotNum, gotTrue, gotFalse]) p Tokens.OPENSQUARE
	val (e, p) = if gotSquare 
		     then let val isEmpty = Tokens.kindOf (peek p) = Tokens.CLOSESQUARE
			      val (es, p) = if isEmpty then ([], p) else listExpr p
			      val p = expect p Tokens.CLOSESQUARE
			  in (SOME (SUGAR (LIST es)), p)
			  end
		     else (e, p)
	val (gotCurly, p) = consumeIf (notAnyOf [gotNum, gotTrue, gotFalse, gotSquare]) p Tokens.OPENCURLY
	val (e, p) = if gotCurly
		     then let val (records, p) = recordExpr p
			      val p = expect p Tokens.CLOSECURLY
			  in (SOME (RECORD_LITERAL records), p)
			  end
		     else (e, p)
	val (e, p) = case e of SOME e => (e, p)
			     | NONE => raise SyntaxError ("Unexpected " ^
							  Lexer.tokenString (peek p) ^
							  " in const")
    in (e, p)
    end

and listExpr p =
    let val (e, p) = expr p
	val (gotComma, p) = consume p Tokens.COMMA
    in if gotComma then let val (rest, p) = listExpr p
			in (e::rest, p)
			end
       else ([e], p)
    end

and recordExpr p =
    let fun recordPair p =
	    let val field = extractString p
		val p = expect p Tokens.NAME
		val p = expect p Tokens.EQ
		val (e, p) = expr p
	    in ((field, e), p)
	    end
		
	val (elem, p) = recordPair p
	val (gotComma, p) = consume p Tokens.COMMA
    in if gotComma then let val (rest, p) = recordExpr p
		       in (elem::rest, p)
		       end
       else ([elem], p)
    end

and infixExpr (e, p) =
    let fun dotExpr (e, p) =
	    let val p = expect p Tokens.DOT
		val fieldText = extractString p
		val p = expect p Tokens.NAME
	    in (DOT (e, fieldText), p)
	    end

	fun binOp (name, kind, arg1, p) =
	    let val p = expect p kind
		val (arg2, p) = expr p
	    in (PRIMAPP (name, [arg1, arg2]), p)
	    end
		
	val kind = Tokens.kindOf (peek p)
    in case kind of Tokens.DOT       => dotExpr (e, p)
		  | Tokens.EQ        => binOp ("=",  Tokens.EQ, e, p)
		  | Tokens.PLUS      => binOp ("+",  Tokens.PLUS, e, p)
		  | Tokens.MINUS     => binOp ("-",  Tokens.MINUS, e, p)
		  | Tokens.STAR      => binOp ("*",  Tokens.STAR, e, p)
		  | Tokens.SLASH     => binOp ("/",  Tokens.SLASH, e, p)
		  | Tokens.PERCENT   => binOp ("%",  Tokens.PERCENT, e, p)
		  | Tokens.LESS      => binOp ("<",  Tokens.LESS, e, p)
		  | Tokens.MORE      => binOp (">",  Tokens.MORE, e, p)
		  | Tokens.LESSEQUAL => binOp ("<=", Tokens.LESSEQUAL, e, p)
		  | Tokens.MOREEQUAL => binOp (">=", Tokens.MOREEQUAL, e, p)
		  | Tokens.AND       => binOp ("&&", Tokens.AND, e, p)
		  | Tokens.OR        => binOp ("||", Tokens.OR, e, p)
		  | _ => (e, p)
    end
	
fun decl p =
    let fun declFun p =
	    let val name = extractString p
		val p = expect p Tokens.NAME
		val (args, p) = argList p
		val p = expect p Tokens.EQ
		val (e, p) = expr p
		val e' = List.foldr ABS e args
	    in (SOME (VAL (name, e')), p)
	    end

	fun declVal p =
	    let val name = extractString p
		val p = expect p Tokens.NAME
		val p = expect p Tokens.EQ
		val (e, p) = expr p
	    in (SOME (VAL (name, e)), p)
	    end

	fun declUni p =
	    let val (tyvars, p) = tyvarList p
		val name = extractString p
		val p = expect p Tokens.NAME
		val p = expect p Tokens.EQ
		val (body, p) = unionBody p
	    in (SOME (UNION (name, tyvars, body)), p)
	    end

	val (gotFun, p) = consume p Tokens.FUN
	val (d, p) = if gotFun then declFun p else (NONE, p)
	val (gotVal, p) = consumeIf (notAnyOf [gotFun]) p Tokens.VAL
	val (d, p) = if gotVal then declVal p else (d, p)
	val (gotUni, p) = consumeIf (notAnyOf [gotVal, gotFun]) p Tokens.UNION
	val (d, p) = if gotUni then declUni p else (d, p)
	val (d, p) = case d of SOME d => (d, p)
			     | NONE => raise SyntaxError ("Declarations must start with " ^
							  "fun, val, or union")
    in (d, p)
    end

fun program p = 
    let val (d, p) = decl p
	val p = expect p Tokens.SEMICOLON
	val (gotEof, p) = consume p Tokens.EOF
    in if gotEof then ([d], p)
       else let val (rest, p) = program p
	    in (d::rest, p)
	    end
    end
	
fun parse p = 
    let val (ds, p) = program p
    in ds
    end
	
end
