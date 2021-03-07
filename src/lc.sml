(*
 * Written by Samuel Burns Cohen
 * 
 * Based on Leijen 2005, 
 * Extensible records with scoped labels
 *
 * and
 *
 * Norman Ramsay, Tufts University, 2020
 * Programming Langauges: Build, Prove, and Compare
 *
 * lc.sml
 *
 *)

open AST

exception TypeError of string
exception ShouldNotHappen of string
exception Unimplemented of string
exception RuntimeError of string
		       
fun injectBetween s [] = ""
  | injectBetween s (fst::[]) = fst
  | injectBetween s (fst::rest) = fst ^ s ^ injectBetween s rest

fun printTree exp =
    let fun p (e, indent) =
	    let fun recordLabel records =
		    let val (_, es) = ListPair.unzip records
		    in ("record", es)
		    end
		fun rawLabel vars =
		    let val (_, es) = ListPair.unzip vars
		    in ("raw", es)
		    end
		val (label, children) =
		    case e of (CONST v)             => ("const", [])
			    | (VAR v)               => ("var (" ^ v ^ ")", [])
			    | (ABS (p, e))          => ("\\." ^ p, [e])
			    | (APP (e1, e2))        => ("app", [e1, e2])
			    | (LET ((_, e1), e2))   => ("let", [e1, e2])
			    | (IF (e1, e2, e3))     => ("if",  [e1, e2, e3])
			    | (DOT (e, f))          => ("dot (" ^ f ^ ")", [e])
			    | (INJ (_, e))          => ("inj", [e])
			    | (DEC (_, e1, e2, e3)) => ("dec", [e1, e2, e3])
			    | (EXN (s))             => ("exn", [])
			    | (RECORD_LITERAL (rs)) => recordLabel rs
			    | (RAW (_, vars, _))    => rawLabel vars
			    | (SUGAR _)             => ("sugar", [])
		fun childString [] = ""
		  | childString (e::[]) = indent ^ "└── " ^
					  p (e, indent ^ "    ")
		  | childString (e::es) = indent ^ "├── " ^
					  p (e, indent ^ "│   ") ^
					  childString es
	    in label ^ "\n" ^ childString children
	    end
    in print (p (exp, "") ^ "\n")
    end

(*                            ------ TYPES ------                             *)
								 
datatype typeScheme = FORALL of string list * ty

datatype con = TRIVIAL
	     | ~  of ty * ty
             | /\ of con * con

infix 4 ~
infix 3 /\

(*                         ------ PROJECTIONS ------                          *)

fun projectBool (BOOL false) = false
  | projectBool _            = true

fun projectNum (NUM n) = n
  | projectNum _ = raise ShouldNotHappen "NUM projection failed"

fun projectChar (CHAR c) = c
  | projectChar _ = raise ShouldNotHappen "CHAR projection failed"

exception MalformedList
fun projectList (VARIANT ("CONS", RECORD ([("cdr", rest), ("car", car)]))) =
    car::(projectList rest)
  | projectList (VARIANT ("CONS", RECORD ([("car", car), ("cdr", rest)]))) =
    car::(projectList rest)
  | projectList (VARIANT ("NIL", _)) = []
  | projectList _ = raise MalformedList

fun embedList ([]) = VARIANT ("NIL", UNIT)
  | embedList (v::vs) = VARIANT ("CONS",
				 RECORD ([("cdr", embedList vs), ("car", v)]))

(*                         ------ ENVIRONMENTS ------                         *)
type 'a env = (string * 'a) list

fun bind e (name, value) = (name, value)::e
					      
fun isBound [] name = false
  | isBound ((x, _)::xs) name = x = name orelse isBound xs name
							
exception NotFound
fun find [] name = raise NotFound
  | find ((x, v)::xs) name = if x = name then v else find xs name

fun names e = List.map (fn (n, v) => n) e

fun values e = List.map (fn (n, v) => v) e
    
val emptyEnv = []

(*                      ------ TYPE CONSTRUCTORS ------                       *)
						   
val booltype = TYCON "bool"
val inttype  = TYCON "int"
val chartype = TYCON "char"
val unittype = TYCON "unit"
val exntype = TYCON "exn"
fun funtype (param, result) = CONAPP (TYCON "function", CONAPP (param, result))
fun rowtype (record as (label, t), ext) = TYROW (record, ext)
val emptyrow = TYEMPTYROW

fun listtype ty = MU ("'a", CONAPP (TYCON "variant",
				    rowtype (("CONS",
					      CONAPP (TYCON "record",
						      rowtype (("car", ty),
							       rowtype (("cdr", TYVAR "'a"), TYEMPTYROW)))),
					     rowtype (("NIL", unittype), TYEMPTYROW))))
		   
fun arityTwoPrim (argATau, argBTau, retTau, f) =
    ABS ("a", ABS ("b", RAW (retTau, [(argATau, VAR "a"), (argBTau, VAR "b")], f)))
	
val badArity = ShouldNotHappen "primitive applied to wrong number of arguments"

fun primEq args = case args of [a, b] => BOOL ((projectNum a) = (projectNum b))
			     | _ => raise badArity
fun primAdd args = case args of [a, b] => NUM ((projectNum a) + (projectNum b))
			      | _ => raise badArity
fun primSub args = case args of [a, b] => NUM ((projectNum a) - (projectNum b))
			      | _ => raise badArity
fun primMul args = case args of [a, b] => NUM ((projectNum a) * (projectNum b))
			      | _ => raise badArity
fun primDiv args = case args of [a, b] => NUM ((projectNum a) div (projectNum b))
			      | _ => raise badArity
fun primMod args = case args of [a, b] => NUM ((projectNum a) mod (projectNum b))
			      | _ => raise badArity
fun primLess args = case args of [a, b] => BOOL ((projectNum a) < (projectNum b))
			       | _ => raise badArity
fun primMore args = case args of [a, b] => BOOL ((projectNum a) > (projectNum b))
			       | _ => raise badArity
fun primLessEq args = case args of [a, b] => BOOL ((projectNum a) <= (projectNum b))
				 | _ => raise badArity
fun primMoreEq args = case args of [a, b] => BOOL ((projectNum a) >= (projectNum b))
				 | _ => raise badArity
fun primAnd args = case args of [a, b] => BOOL ((projectBool a) andalso (projectBool b))
			      | _ => raise badArity
fun primOr args = case args of [a, b] => BOOL ((projectBool a) orelse (projectBool b))
			     | _ => raise badArity

fun puts args = case args of [a] => let val list = projectList a
					val list = List.map projectChar list
					val str = String.implode list
					val _ = print str
				    in UNIT
				    end
			   | _ => raise badArity

fun gets args = case args of [a] => let val line = case TextIO.inputLine TextIO.stdIn
						    of SOME s => s
						     | NONE => ""
					val list = String.explode line
					val list = List.map CHAR list
				    in embedList list
				    end
			   | _ => raise badArity
					  
val primitives =
    [("=", arityTwoPrim (inttype, inttype, booltype, primEq)),
     ("+", arityTwoPrim (inttype, inttype, inttype, primAdd)),
     ("-", arityTwoPrim (inttype, inttype, inttype, primSub)),
     ("*", arityTwoPrim (inttype, inttype, inttype, primMul)),
     ("/", arityTwoPrim (inttype, inttype, inttype, primDiv)),
     ("%", arityTwoPrim (inttype, inttype, inttype, primMod)),
     ("<", arityTwoPrim (inttype, inttype, booltype, primLess)),
     (">", arityTwoPrim (inttype, inttype, booltype, primMore)),
     ("<=", arityTwoPrim (inttype, inttype, booltype, primLessEq)),
     (">=", arityTwoPrim (inttype, inttype, booltype, primMoreEq)),
     ("&&", arityTwoPrim (booltype, booltype, booltype, primAnd)),
     ("||", arityTwoPrim (booltype, booltype, booltype, primOr)),
     ("puts", ABS ("str", RAW (unittype,
			       [(listtype chartype, VAR "str")],
			       puts))),
     ("gets", ABS ("a", RAW (listtype chartype,
			     [(unittype, VAR "a")],
			     gets)))]
     
	
(*                             ------ SETS ------                             *)
type 'a set = 'a list
fun member x = List.exists (fn y => y = x)
			   
fun insert (v, st) = if member v st then st else v::st
							
fun union (st1, st2) = List.foldl insert st2 st1
			   
fun inter (st1, st2) = List.filter (fn v => member v st2) st1
				 
fun diff (st1, st2) = List.filter (fn v => not (member v st2)) st1

val emptySet = []

(*                            ------ DESUGAR ------                           *)

local
    val n = ref 1
in fun freshtyvar _ = TYVAR ("'t" ^ Int.toString (!n) before n := !n + 1)
end
    
fun expand (MATCH (e, cases)) =
    let val n = ref 1
	(* since the source program can't have variables starting with numbers, 
	 * it's safe to say that a variable created by freshLocal will never
	 * shadow a variable in the source program *)
	fun freshLocal _ = Int.toString (!n) before n := !n + 1
								  
	fun convertToDEC (_, []) = EXN "Pattern matching failed"
	  | convertToDEC (preAlpha, (pattern, alpha, body)::cases) =
	    let val postAlpha = freshLocal ()
	    in DEC (pattern, preAlpha,
		    ABS (alpha, body),
		    ABS (postAlpha, convertToDEC (VAR postAlpha, cases)))
	    end
		
	val desugaredE = desugar e
	val desugaredCases = List.map (fn (pat, alpha, body) => (pat, alpha, desugar body)) cases
    in convertToDEC (desugaredE, desugaredCases)
    end
  | expand (LIST es) =
    let val desugaredEs = List.map desugar es
	val createConsCell =
	 fn (e, rest) => APP (VAR "CONS", RECORD_LITERAL [("car", e), ("cdr", rest)])
    in List.foldr createConsCell (APP (VAR "NIL", CONST UNIT)) desugaredEs
    end
  | expand (BLOCK ds) =
    let fun valToBinding (VAL ("_", e)) = ("_", e)
	  | valToBinding (VAL (nm,  e)) = (nm,  e)
	  | valToBinding _ = raise ShouldNotHappen "Non-val declarations are not allowed in BLOCK"
	fun desugarBinding (nm, e) = (nm, desugar e)
	val bindings = List.map (desugarBinding o valToBinding) (List.rev ds)
	(* note that list of bindings is reversed, so the first
         * element is actually the last *)
	val (body, bindings) = case bindings of (("_", bdg)::rest) => (bdg, rest)
					      | (_::rest) => (CONST UNIT, [])
					      | [] => (CONST UNIT, [])
    in List.foldl LET body bindings
    end
		   
and desugar (e as CONST _)        = e
  | desugar (e as VAR _)          = e
  | desugar (ABS (v, b))          = ABS (v, desugar b)
  | desugar (APP (e1, e2))        = APP (desugar e1, desugar e2)
  | desugar (LET ((n, e1), e2))   = LET ((n, desugar e1), desugar e2)
  | desugar (IF (e1, e2, e3))     = IF (desugar e1, desugar e2, desugar e3)
  | desugar (DOT (e, f))          = DOT (desugar e, f)
  | desugar (INJ (f, e))          = INJ (f, desugar e)
  | desugar (DEC (v, e1, e2, e3)) = DEC (v, desugar e1, desugar e2, desugar e3)
  | desugar (e as EXN _)          = e
  | desugar (RECORD_LITERAL records) =
    let val (fields, es) = ListPair.unzip records
	val desugaredEs = List.map desugar es
	val desugaredRecords = ListPair.zipEq (fields, desugaredEs)
    in RECORD_LITERAL desugaredRecords
    end
  | desugar (RAW (ty, vars, f)) =
    let val (taus, es) = ListPair.unzip vars
	val desugaredEs = List.map desugar es
	val desugaredVars = ListPair.zipEq (taus, desugaredEs)
    in RAW (ty, desugaredVars, f)
    end
  | desugar (SUGAR s) = expand s
			       
(*                          ------ HM HELPERS ------                          *)

fun findVariant Delta field =
    let fun hasLabel (TYROW ((l, _), rest), label) =
	    l = label orelse hasLabel (rest, label)
	  | hasLabel _ = false
	fun hasVariant (MU (_, CONAPP (TYCON "variant", row as TYROW _))) =
	    hasLabel (row, field)
	  | hasVariant (CONAPP (TYCON "variant", row as TYROW _)) =
	    hasLabel (row, field)
	  | hasVariant _ = false
    in List.find (fn ((_, FORALL (_, ty))) => hasVariant ty) Delta
    end

(*
 * freetyvarsInType
 *
 * The freetyvars function returns a set containing the
 * name of every variable in the type expression.
 *)
fun freetyvarsInType (tau : ty) : string set =
    let fun f (TYVAR v,              ftvs) = insert (v, ftvs)
	  | f (TYCON _,              ftvs) = ftvs
	  | f (CONAPP (ta, tb),      ftvs) = union (f (ta, ftvs), f (tb, ftvs))
	  | f (MU (v, t),            ftvs) = diff (f(t, ftvs), insert (v, emptySet))
	  | f (TYROW ((_, t),  ext), ftvs) = union (f (t, ftvs), f (ext, ftvs))
	  | f (TYEMPTYROW,           ftvs) = ftvs
    in f (tau, emptySet)
    end

fun freetyvarsInConstraint (ty1 ~ ty2) =
    union (freetyvarsInType ty1, freetyvarsInType ty2)
  | freetyvarsInConstraint (tyc1 /\ tyc2) =
    union (freetyvarsInConstraint tyc1, freetyvarsInConstraint tyc2)
  | freetyvarsInConstraint (TRIVIAL) = emptySet

fun freetyvarsInGamma (Gamma : typeScheme env) : string set =
    List.foldl (fn (FORALL (vars, t), s) =>
		   union (s, diff (freetyvarsInType t, vars)))
	       emptySet (values Gamma)
	       
fun bindtyscheme (name   : string,
		  scheme : typeScheme,
		  Gamma  : typeScheme env) : typeScheme env  =
    bind Gamma (name, scheme)

local
    val n = ref 1
in fun freshtyvar _ = TYVAR ("'t" ^ Int.toString (!n) before n := !n + 1)
end

fun labelsInType (tau : ty) : string set =
    let fun f (TYROW ((l, _), ext), ls) = f (ext, insert (l, ls))
	  | f (CONAPP (ta, tb),     ls) = union (f (ta, ls), f (tb, ls))
	  | f (_,                   ls) = ls
    in f (tau, emptySet)
    end

(*
 * Note:
 * Theta is a function (a substitution) that maps type
 * variables to types. As such, it is represented as a
 * type env. The purpose of the solve function is to generate
 * such a mapping that solves the input constraint.
 *)

(*
 * varsubst
 *
 * The varsubst function accepts a mapping, theta, and 
 * returns a function that given a name returns the value
 * of the name in theta or a new type variable with that name.
 *)
    
fun varsubst theta =
    (fn a => find theta a handle NotFound => TYVAR a)
	
(*
 * tysubst
 *
 * The tysubst function accepts a mapping, theta, and produces
 * a function that maps a type to another type.
 *)
	
fun tysubst theta =
    let fun subst (TYVAR a) = varsubst theta a
	  | subst (TYCON c) = TYCON c
	  | subst (CONAPP (ta, tb)) = CONAPP (subst ta, subst tb)
	  | subst (MU (v, t)) = MU (v, subst t)
	  | subst (TYROW ((l, t), ext)) = TYROW ((l, subst t), subst ext)
	  | subst (TYEMPTYROW) = TYEMPTYROW
    in subst
    end

(*
 * consubst
 *
 * The consubst function applies theta to a type constraint.
 *)
	
fun consubst theta = 
    let fun subst (tau1 ~ tau2) = (tysubst theta tau1) ~ (tysubst theta tau2)
	  | subst (c1 /\ c2) = subst c1 /\ subst c2
	  | subst (TRIVIAL) = TRIVIAL
    in subst
    end

(*
 * mapsTo
 *
 * The mapsTo function creates a type environment which represents
 * a function that may solve a constraint. The first argument is 
 * a name, and the second argument is a type.
 *)
fun mapsTo (alpha, TYVAR alpha') = if alpha = alpha' then emptyEnv
				   else bind emptyEnv (alpha, TYVAR alpha')
  | mapsTo (alpha, tau) = bind emptyEnv (alpha, tau)

(*
 * domTheta
 *
 * domTheta finds the domain of a mapping, theta
 *)

fun domTheta theta = List.foldl (fn (name, s) => insert (name, s))
				emptySet (names theta)
				
(* 
 * compose
 * 					
 * The compose function accepts two mappings, theta1 and theta2,
 * and returns a new mapping which is the composition of theta1
 * with theta2.
 *)

fun compose (theta2, theta1) =
    let val domain  = union (domTheta theta2, domTheta theta1)
	val replace = tysubst theta2 o varsubst theta1
    in map (fn a => (a, replace a)) domain
    end

(* 
 * canonicalize
 *
 * The canonicalize function accepts a typeScheme
 * and returns a typeScheme where the type variables
 * have been renamed to be more readable for error messages.
 *
 *)
	
fun canonicalize (FORALL (bound, ty)) =
    let fun canonicalTyvarName n =
            if n < 26 then "'" ^ str (chr (ord #"a" + n))
            else "v" ^ Int.toString (n - 25)
	val free = diff (union (freetyvarsInType ty, labelsInType ty), bound)
	fun unusedIndex n =
            if member (canonicalTyvarName n) free then unusedIndex (n + 1) else n
	fun newBoundVars (index, []) = []
          | newBoundVars (index, oldvar :: oldvars) =
            let val n = unusedIndex index
            in canonicalTyvarName n :: newBoundVars (n+1, oldvars)
            end
	val newBound = newBoundVars (0, bound)
	val theta = List.foldl (fn (pair, env) => bind env pair)
			       emptyEnv (ListPair.zipEq (bound, map TYVAR newBound))
	val newTau = tysubst theta ty
    in  FORALL (newBound, newTau)
    end

(* 
 * generalize
 *
 * The generalize function converts the monomorphic type
 * tau into a polymorphic type. 
 *)
						
fun generalize (tau : ty, tyvars : string set) : typeScheme =
    canonicalize (FORALL (diff (freetyvarsInType tau, tyvars), tau))

(*
 * instantiate
 *
 * The instantiate function converts an abstract typeScheme into
 * a proper type. It does this by creating a type where each 
 * variable in the input typeScheme has been substituted for a 
 * value in the actuals list.
 *)
fun instantiate (FORALL (formals, tau), actuals) : ty =
    tysubst (List.foldl (fn (pair, e) => bind e pair)
			emptyEnv (ListPair.zipEq (formals, actuals))) tau
	    
(*
 * freshInstance
 *
 * The freshInstance function instantiates a typeScheme converting
 * it to a proper type by creating a new type variable for every tyvar
 * in the typeScheme.
 *)

fun freshInstance (FORALL (bound, tau)) : ty =
    instantiate (FORALL (bound, tau), List.map freshtyvar bound)
		
(*                         ------ HM INFERENCE ------                         *)

fun unroll (MU (t, tau)) =
    let val theta = mapsTo (t, MU (t, tau))
    in tysubst theta tau
    end
  | unroll (CONAPP (ta, tb)) = CONAPP (unroll ta, unroll tb)
  | unroll (TYROW ((s, ta), tb)) = TYROW ((s, unroll ta), unroll tb)
  | unroll tau = tau (* all types with no children *)

(* as written, this function can't deal with cases
 * where there are multiple distinct mu types which
 * are children of the root tau. This function is only
 * used for type simplification for printing, however,
 * so it's okay *)

(* NOTE: this function shouldn't be used right now -- it doesnt terminate for some inputs *)
fun roll tau =
    let fun optionalOr (SOME v, _)  = SOME v
	  | optionalOr (_, SOME v)  = SOME v
	  | optionalOr (NONE, NONE) = NONE
	fun rollHelper (MU (t, tau)) = (TYVAR t, SOME t)
	  | rollHelper (CONAPP (ta, tb)) =
	    let val (ta', muVarA) = rollHelper ta
		val (tb', muVarB) = rollHelper tb
	    in (CONAPP (ta', tb'), optionalOr (muVarA, muVarB))
	    end
	  | rollHelper (TYROW ((s, ta), tb)) =
	    let val (ta', muVarA) = rollHelper ta
		val (tb', muVarB) = rollHelper tb
	    in (TYROW ((s, ta'), tb'), optionalOr (muVarA, muVarB))
	    end
	  | rollHelper tau = (tau, NONE) (* all types with no children *)
	val (rolledTau, potentialVar) = rollHelper tau
    in case potentialVar of SOME t => MU (t, rolledTau)
			  | NONE => tau
    end

datatype brokenConstraint = UNEQUAL of ty * ty
			  | MISSING of string
					   
exception UnsatisfiableConstraint of brokenConstraint
fun solve c =
    let fun solveRow (TYROW ((l, _), _), TYEMPTYROW) =
	    raise UnsatisfiableConstraint (MISSING ("row doesn't contain " ^ l))
	  | solveRow (TYEMPTYROW, TYROW ((l, _), _)) =
	    raise UnsatisfiableConstraint (MISSING ("row doesn't contain " ^ l))
	  | solveRow (TYROW ((label', tau'), r), TYROW ((label, tau), r')) =
	    if label' = label
	    then (TYROW ((label', tau'), r), emptyEnv)
	    else let val (rest, theta) = solveRow (r, TYROW ((label, tau), r'))
		     val tau = case rest of TYROW (f, ext) =>
					    TYROW (f, TYROW ((label', tau'), ext))
					  | _ => raise ShouldNotHappen "solveRow returned non-row"
		 in (tau, theta)
		 end
	  | solveRow (TYROW ((label, tau), _), TYVAR alpha) =
	    let val gamma = freshtyvar ()
		val beta = freshtyvar ()
		val tau = TYROW ((label, gamma), beta)
	    in (tau, mapsTo (alpha, tau))
	    end
	  | solveRow (TYVAR alpha, r as TYROW _) = solveRow (r, TYVAR alpha)
	  | solveRow (ta, tb) =
	    raise ShouldNotHappen "solveRow got unexpected inputs"

	fun solveEq (TYCON "exn", t) = emptyEnv (* make exception types always typecheck *)
	  | solveEq (t, TYCON "exn") = emptyEnv (* there's probably a better way to do this -- maybe introduce a new 
						 * type constructor ??? *)
	  | solveEq (TYVAR a, TYVAR b) = mapsTo (a, TYVAR b)
	  | solveEq (TYVAR nm, t) =
	    let val _ = if member nm (freetyvarsInType t)
			then raise UnsatisfiableConstraint (UNEQUAL (TYVAR nm, t))
			else ()
	    in mapsTo (nm, t)
	    end
	  | solveEq (t, TYVAR nm) = solveEq (TYVAR nm, t)
	  | solveEq (TYCON nm1, TYCON nm2) =
	    if nm1 = nm2 then
		emptyEnv
	    else raise UnsatisfiableConstraint (UNEQUAL (TYCON nm1, TYCON nm2))
	  | solveEq (CONAPP (ta, tb), CONAPP (tc, td)) =
	    solve (ta ~ tc /\ tb ~ td)
	  | solveEq (TYEMPTYROW, TYEMPTYROW) = emptyEnv
	  | solveEq (TYROW ((l, t), r), s as TYROW _) =
	    let val (row2, theta1) = solveRow (s, TYROW ((l, t), r))
		val (t', s') = case row2 of TYROW ((_, r2t), r2s) => (r2t, r2s)
					  | _ => raise ShouldNotHappen "got non-row from solveRow"
		fun tailOf (TYROW (_, e)) = tailOf e
		  | tailOf (TYVAR a) = SOME a
		  | tailOf _ = NONE

		val _ = case tailOf r
			 of SOME a =>
			    if member a (domTheta theta1)
			    then raise UnsatisfiableConstraint (UNEQUAL (TYROW ((l, t), r), s))
			    else ()
			  | NONE => ()
					
	    in (compose (solve (t ~ t' /\ r ~ s'), theta1))
	    end
	  | solveEq (MU (t, tau), MU (t', tau')) = solve ((TYVAR t) ~ (TYVAR  t') /\ tau ~ tau')
	  | solveEq (rectype as MU _, t) = solve (unroll rectype ~ t)
	  | solveEq (t, rectype as MU _) = solve (t ~ unroll rectype)
	  | solveEq (ta, tb) = raise UnsatisfiableConstraint (UNEQUAL (ta, tb))
						       
	fun solveCon (c1, c2) =
	    let val theta1 = solve c1
		val appliedTheta1 = consubst theta1 c2
	    in compose (solve appliedTheta1, theta1)
	    end
	fun sv (t1 ~ t2)  = solveEq (t1, t2)
	  | sv (c1 /\ c2) = solveCon (c1, c2)
	  | sv TRIVIAL    = emptyEnv
    in sv c
    end

local fun flattenRow (TYROW (record, TYVAR a)) = [record, ("...", TYVAR a)]
	| flattenRow (TYROW (record, ext)) = record::flattenRow ext
	| flattenRow (TYEMPTYROW) = []
	| flattenRow _ = raise ShouldNotHappen("flattenRow got non row")

in fun typeString (tau, Delta) =
       let fun ts (TYVAR s) = s
	     | ts (TYCON "unit") = "()"
	     | ts (TYCON s) = s
	     | ts (f as CONAPP (TYCON "function", _)) = funString (f, Delta)
	     | ts (r as CONAPP (TYCON "record", _)) = recordString (r, Delta)
	     | ts (v as CONAPP (TYCON "variant", _)) = variantString (v, Delta)
	     | ts (CONAPP (ta, tb)) =
	       ts ta ^ " -> " ^ ts tb
	     | ts (tau as MU (var, t)) =
	       "mu." ^ var ^ " [" ^ ts t ^ "]"
	     | ts (TYROW ((label, t), ext)) =
	       "(" ^ label ^ " :: " ^ ts t ^ " | " ^ ts ext ^ ")"
	     | ts (TYEMPTYROW) = "[]"
       in case collapseDefinedType (tau, Delta) of SOME str => str
						 | NONE => ts tau
       end

   and funString (CONAPP (TYCON "function", CONAPP (param, result)), Delta) =
       typeString (param, Delta) ^ " -> " ^ typeString (result, Delta)
     | funString _ = raise ShouldNotHappen "funString applied to non function"

   and recordString (CONAPP (TYCON "record", row), Delta) =
       let val records = List.map (fn (label, t) => label ^ " : " ^
						    typeString (t, Delta))
				  (flattenRow row)
       in "{" ^ injectBetween ", " records ^ "}"
       end
     | recordString _ = raise ShouldNotHappen "recordString got non record"

   and variantString (CONAPP (TYCON "variant", row), Delta) =
       let val records = List.map (fn (label, t) => label ^ " : " ^
						    typeString (t, Delta))
				  (flattenRow row)
       in "<" ^ injectBetween " | " records ^ ">"
       end
     | variantString _ = raise ShouldNotHappen "variantString got non record"
			      
   and collapseDefinedType (TYVAR _, _) = NONE
     | collapseDefinedType (TYCON _, _) = NONE
     | collapseDefinedType (tau, Delta) =
       let val defnMatches = fn (nm, FORALL (_, defnTau)) =>
				let val con = defnTau ~ tau
				in SOME (solve con)
				   handle UnsatisfiableConstraint _ => NONE
				end

	   fun findMatch (def::ds) =
	       let val possibleTheta = defnMatches def
	       in case possibleTheta of SOME theta => SOME (def, theta)
				      | NONE => findMatch ds
	       end
	     | findMatch [] = NONE

       in case findMatch Delta of SOME ((nm, FORALL (alphas, tau)), theta) =>
				  let val instantiatedAlphas = List.map (fn a => varsubst theta a) alphas
				      val alphaStrings = List.map (fn tau => typeString (tau, Delta)) instantiatedAlphas
				  in SOME (injectBetween " " (alphaStrings @ [nm]))
				  end
				| NONE => NONE
       end

   fun typeSchemeString (FORALL ([], t), Delta) =
       typeString (t, Delta)
     | typeSchemeString (FORALL (vars, t), Delta) =
       "∀" ^ injectBetween "" vars ^ "." ^ typeString (t, Delta)
						      
end

fun registerTypeError (UNEQUAL (t1, t2), Delta) =
    let val t1Arrowt2 = funtype (t1, t2)
	val FORALL (_, canonical) =
            canonicalize (FORALL (freetyvarsInType t1Arrowt2, t1Arrowt2))
    in case canonical
        of CONAPP (TYCON "function", CONAPP(t1', t2')) =>
           raise TypeError ("cannot make " ^ typeString (t1', Delta) ^
                            " equal to " ^ typeString (t2', Delta))
         | _ => raise ShouldNotHappen "funtype returned non-funtype"
    end
  | registerTypeError (MISSING str, _) =
    raise TypeError str
	
fun typeof (e, Gamma : typeScheme env, Delta : typeScheme env) : ty * con =
    let fun typesof ([],    Gamma) = ([], TRIVIAL)
	  | typesof (e::es, Gamma) =
	    let val (tau,  c)  = typeof  (e,  Gamma, Delta)
		val (taus, c') = typesof (es, Gamma)
	    in (tau::taus, c /\ c')
	    end

	fun constant (BOOL _) = (booltype, TRIVIAL)
	  | constant (NUM  _) = (inttype,  TRIVIAL)
	  | constant (CHAR _) = (chartype, TRIVIAL)
	  | constant (UNIT)   = (unittype, TRIVIAL)
	  | constant _ = raise ShouldNotHappen "typecheck non instantiatable constant"

	fun declOfVariant field =
	    case findVariant Delta field
	     of SOME (_, scheme) => freshInstance scheme
	      | NONE => raise TypeError ("variant with field " ^ field ^
					 " used before its declaration")

	fun ty (CONST v) = constant v
	  | ty (VAR name) = ((freshInstance (find Gamma name), TRIVIAL)
			     handle NotFound => raise TypeError
						      ("name \"" ^ name ^
						       "\" is unknown"))
	  | ty (ABS (param, body)) =
	    let val alpha = freshtyvar ()
		val Gamma' = bindtyscheme (param, FORALL ([], alpha), Gamma)
		val (bodyTau, Con) = typeof (body, Gamma', Delta)
	    in (funtype (alpha, bodyTau), Con)
	    end
	  | ty (APP (e1, e2)) =
	    let val (fTau, fCon) = ty e1
		val (paramTau, pCon) = ty e2
		val retTau = freshtyvar ()
	    in (retTau, fCon /\ pCon /\ fTau ~ funtype (paramTau, retTau))
	    end
	  | ty (LET (binding, body)) =
	    let val (name, e) = binding
		val (eTau, Con) = ty e
		val theta = solve Con
			    handle UnsatisfiableConstraint error => registerTypeError (error, Delta)
		val alphas = inter (freetyvarsInGamma Gamma, domTheta theta)
		val Con' = List.foldl (fn (a, constraint) =>
					  constraint /\ (TYVAR a ~ (varsubst theta a)))
				      TRIVIAL alphas
		val scheme = generalize (tysubst theta eTau, union (freetyvarsInGamma Gamma,
								    freetyvarsInConstraint Con'))
		val Gamma' = bindtyscheme (name, scheme, Gamma)
		val (tau, Cb) = typeof (body, Gamma', Delta)
	    in (tau, Con' /\ Cb)
	    end
	  | ty (IF  (cond, trueE, falseE)) =
	    let val (condT, condC) = ty cond
		val (trueT, trueC) = ty trueE
		val (falseT, falseC) = ty falseE
	    in (trueT,
		condC /\ trueC /\ falseC /\ condT ~ booltype /\ trueT ~ falseT)
	    end
	  | ty (DOT (e, field)) =
	    (* simulates call to forall [r, f] { field : f | r } -> f *)
	    let val restTau = freshtyvar ()
		val fieldTau = freshtyvar ()
		val paramTau = CONAPP (TYCON "record",
				       rowtype ((field, fieldTau), restTau))
		val (recordTau, con) = ty e
	    in (fieldTau, con /\ paramTau ~ recordTau)
	    end
	  | ty (INJ (field, e)) =
	    (* simulates call to forall [a, r] a -> < field : a | r > *)
	    let val restTau = freshtyvar ()
		val fieldTau = freshtyvar ()
		val resultTau = CONAPP (TYCON "variant",
					rowtype ((field, fieldTau), restTau))
		val declTau = declOfVariant field
		val (valueTau, Con) = ty e
	    in (resultTau, Con /\ fieldTau ~ valueTau /\ resultTau ~ declTau)
	    end
	  | ty (DEC (field, variant, match, noMatch)) =
	    (* simulates call to forall [a, B, r] < field : a | r >
             *                       -> ( a -> B ) 
             *                       -> ( <field : a | r> -> B ) -> B
             *)
	    let val restTau = freshtyvar ()
		val betaTau = freshtyvar ()
		val fieldTau = freshtyvar ()
		val declTau = declOfVariant field
		val rowTau = rowtype ((field, fieldTau), restTau)
		val fstArg = CONAPP (TYCON "variant", rowTau)
		val sndArg = funtype (fieldTau, betaTau)
		val thrArg = funtype (CONAPP (TYCON "variant", rowTau),
				      betaTau)
		val (vTau, vCon) = ty variant
		val (mTau, mCon) = ty match
		val (nmTau, nmCon) = ty noMatch
	    in (betaTau, vCon /\ mCon /\ nmCon
			 /\ fstArg ~ vTau
			 /\ fstArg ~ declTau
			 /\ sndArg ~ mTau
			 /\ thrArg ~ nmTau)
	    end
	  | ty (EXN _) = (exntype, TRIVIAL)
	  | ty (RECORD_LITERAL records) =
	    let fun makeType [] = TYEMPTYROW
		  | makeType ((label, t)::rs) =
		    rowtype ((label, t), makeType rs)
		val (ls, es) = ListPair.unzip records
		val (taus, Con) = typesof (es, Gamma)
	    in (CONAPP (TYCON "record", makeType (ListPair.zipEq (ls, taus))),
		Con)
	    end
	  | ty (RAW (retTau, vars, _)) =
	    let val (targetTaus, es) = ListPair.unzip vars
		val (actualTaus, Con) = typesof (es, Gamma)
		val conPairs = ListPair.zipEq (targetTaus, actualTaus)
		val C = List.foldl (fn ((t, t'), C) => t ~ t' /\ C) TRIVIAL conPairs
	    in (retTau, Con /\ C)
	    end
	  | ty (SUGAR _) =
	    raise ShouldNotHappen "Sugar nodes should never be typed"
    in ty e
    end
	
fun typedef (name, e, Gamma : typeScheme env, Delta : typeScheme env) =
    let fun ty (e as ABS (formal, body)) =
	    let val alpha = freshtyvar ()
		val Gamma' = bindtyscheme (name, FORALL ([], alpha), Gamma)
		val (tau, Con) = typeof (e, Gamma', Delta)
		val theta = solve (Con /\ alpha ~ tau)
				  handle UnsatisfiableConstraint error => registerTypeError (error, Delta)
		val sigma = generalize (tysubst theta alpha, freetyvarsInGamma Gamma)
	    in bindtyscheme (name, sigma, Gamma)
	    end
	  | ty e = 
	    let val (tau, Con) = typeof (e, Gamma, Delta)
		val theta = solve Con
			    handle UnsatisfiableConstraint error=> registerTypeError (error, Delta)
		val sigma = generalize (tysubst theta tau, freetyvarsInGamma Gamma)
	    in bindtyscheme (name, sigma, Gamma)
	    end
    in ty e
    end
	
(*                          ------ EVALUATION ------                          *)

fun valueString (UNIT) = "unit"
  | valueString (BOOL b) = if b then "true" else "false"
  | valueString (NUM n) = Int.toString n
  | valueString (CHAR c) = "'" ^ Char.toString c ^ "'"
  | valueString (CLOSURE _) = "fn"
  | valueString (RECORD _) = "record"
  | valueString (v as VARIANT _) =
    case asList v of SOME str => str
		   | NONE => "union"

and asList (l as VARIANT ("CONS", listElems)) =
    let val listElems = SOME (projectList l)
			handle MalformedList => NONE
    in case listElems of SOME l => SOME ("[" ^ injectBetween ", " (List.map valueString l) ^ "]")
		       | NONE => NONE
    end
  | asList (VARIANT ("NIL", _)) = SOME "[]"
  | asList _ = NONE
				  
fun eval (e, Rho : value ref env) =
    let fun bindList (x::vars, v::vals, Rho) = bindList (vars, vals, bind Rho (x, v))
	  | bindList ([], [], Rho) = Rho
	  | bindList _ = raise ShouldNotHappen "bindList unequal length"
			       
	fun ev (CONST v) = v
	  | ev (VAR n) = !(find Rho n)
	  | ev (ABS (var, body)) = CLOSURE ((var, body), Rho)
	  | ev (APP (e1, e2)) =
	    (case ev e1 of CLOSURE ((var, body), capturedRho) =>
			   let val formalVal = ref (ev e2)
			   in eval (body, bind capturedRho (var, formalVal))
			   end
			 | _ => raise ShouldNotHappen "applied non-closure")
	  | ev (LET (binding, body)) =
	    let val (name, e) = binding
	    in eval (body, bind Rho (name, (ref o ev) e))
	    end
	  | ev (IF (cond, trueE, falseE)) =
	    ev (if projectBool (ev cond) then trueE else falseE)
	  | ev (DOT (e, field)) =
	    let val records = case ev e
			       of RECORD records => records
				| _ => raise ShouldNotHappen
					     "dot applied to non-record"
		val value = case List.find (fn (nm, v) => nm = field) records
			     of SOME (_, v) => v
			      | NONE => raise ShouldNotHappen
					      ("struct doesn't have " ^
					       field ^ " field")
	    in value
	    end
	  | ev (INJ (field, e)) = VARIANT (field, ev e)
	  | ev (DEC (field, variant, match, noMatch)) =
	    let val (itsField, v) =
		    case ev variant of VARIANT pair => pair
				     | v => raise ShouldNotHappen
						  ("dec got non-variant" ^
						   " (" ^ valueString v ^ ")")
						  
		fun applyCase (CLOSURE ((var, body), capturedRho)) v =
		    let val formalVal = ref v
		    in eval (body, bind capturedRho (var, formalVal))
		    end
		  | applyCase _ _ = raise ShouldNotHappen
					"dec match applied to non-closure"
					
	    in if field = itsField
	       then applyCase (ev match) v
	       else applyCase (ev noMatch) (VARIANT (itsField, v))
	    end
	  | ev (EXN s) = raise RuntimeError s
	  | ev (RECORD_LITERAL records) =
	    let val value = List.map (fn (name, e) => (name, ev e)) records
	    in RECORD value
	    end
	  | ev (RAW (_, vars, f)) =
	    let val (_, es) = ListPair.unzip vars
	    in f (List.map ev es)
	    end
	  | ev (SUGAR _) =
	    raise ShouldNotHappen "Sugar nodes should never be evaluated"
    in ev e
    end
	
fun evaldef (name, e, Rho : value ref env) =
    let val this = ref UNIT
	val Rho' = bind Rho (name, this)
	val v = eval (e, Rho')
	val _ = this := v
    in Rho'
    end

(*                             ------ REPL ------                             *)

fun recover (TypeError msg) = "Type Error: " ^ msg
  | recover (ShouldNotHappen msg) = "Shouldn't Happen: " ^ msg
  | recover (Unimplemented msg) = "Unimplemented: " ^ msg
  | recover (RuntimeError msg) = "Runtime Error: " ^ msg
  | recover _ = "Unknown Error!"

fun isWhitespace c = c = #" " orelse c = #"\n" orelse c = #"\t"

fun eof () = "" before print "\n" before OS.Process.exit OS.Process.success

fun fetchInput flags =
    let val recordDepth = ref 0
	fun getLine prev =
	    let val _ = if #prompt flags
			then print (if (!recordDepth = 0 andalso prev = "") then "- " else "= ")
			else ()
		val line = String.explode (case TextIO.inputLine TextIO.stdIn of SOME s => s
									       | NONE => eof())
		val lineDepth = List.foldl (fn (c, i) => if c = #"{" then i + 1
							 else if c = #"}" then i - 1
							 else i) (!recordDepth) line
		val _ = recordDepth := lineDepth
		fun semiTerminated [] = false
		  | semiTerminated (c::cs) = (c = #";" andalso List.all isWhitespace cs)
					     orelse semiTerminated cs
		val lineStr = prev ^ (String.implode line)
	    in if (!recordDepth) <= 0 andalso semiTerminated line then lineStr
	       else getLine (lineStr)
	    end
    in getLine ""
    end

fun replaceTycon (name, ty, replacement) =
    let fun subst (t as TYVAR _) = t
	  | subst (t as TYCON s) = if s = name then replacement else t
	  | subst (CONAPP (ta, tb)) = CONAPP (subst ta, subst tb)
	  | subst (t as MU _) = t
	  | subst (t as TYEMPTYROW) = t
	  | subst (TYROW ((f, ta), tb)) = TYROW ((f, subst ta), subst tb)
    in subst ty
    end

fun isRectype (name, TYCON s) = name = s
  | isRectype (name, CONAPP (ta, tb)) = isRectype (name, ta) orelse isRectype (name, tb)
  | isRectype (name, TYROW ((_, ta), tb)) = isRectype (name, ta) orelse isRectype (name, tb)
  | isRectype _ = false

fun introduceDefs (namedEs, Gamma, Rho, Delta) =
    let val Gamma' = List.foldl (fn ((name, e), Gamma) => typedef (name, e, Gamma, Delta))
				Gamma namedEs
	val Rho' = List.foldl (fn ((name, e), Rho) => evaldef (name, e, Rho))
			      Rho namedEs
    in (Gamma', Rho')
    end
	
(* 
 * introduceConstructors
 * 
 * Creates constructors for the variants mentioned
 * in names.
 *)
fun introduceConstructors (names, Gamma, Rho, Delta) =
    let fun makeConstructor name =
	    ABS ("expr", INJ (name, VAR "expr"))
	val namedEs = List.map (fn nm => (nm, makeConstructor nm)) names
    in introduceDefs (namedEs, Gamma, Rho, Delta)
    end

fun introducePrimitives (Gamma, Rho, Delta) =
    introduceDefs (primitives, Gamma, Rho, Delta)

fun processDef (VAL (name, rawExpr), flags, Gamma, Rho, Delta) =
    let val expr = desugar rawExpr
	val _ = if #showAST flags then printTree expr else ()
	val Gamma' = typedef (name, expr, Gamma, Delta)
	val itsType = find Gamma' name
	val Rho' = evaldef (name, expr, Rho)
	val itsValue = !(find Rho' name)
    in (name ^ " = " ^ valueString itsValue ^
	" : " ^
	typeSchemeString (itsType, Delta), Gamma', Rho', Delta)
    end
  | processDef (UNION (name, tyvars, options), flags, Gamma, Rho, Delta) =
    let val row = List.foldl rowtype TYEMPTYROW options
	val rawTau = CONAPP (TYCON "variant", row)
	val _ = if not (freetyvarsInType rawTau = tyvars)
		then raise TypeError "tyvar mismatch in variant"
		else ()
	val tau = if isRectype (name, rawTau) then
		      let val recVar = case freshtyvar () of TYVAR a => a
							   | _ => raise ShouldNotHappen
									"freshtyvar gave non-tyvar"
			  val recTau = MU (recVar, replaceTycon (name, rawTau, TYVAR recVar))
		      in recTau
		      end
		  else rawTau
	val sigma = FORALL (freetyvarsInType tau, tau)
	val Delta' = bindtyscheme (name, sigma, Delta)
	val (names, _) = ListPair.unzip options
	val (Gamma', Rho') = introduceConstructors (names, Gamma, Rho, Delta')
    in (name ^ " : " ^ typeSchemeString (sigma, Delta), Gamma', Rho', Delta')
    end
	
fun readFileIntoString filename =
    let val infile = TextIO.openIn filename
	fun reader (c : char option, data : char list) =
	    case c of SOME c => reader (TextIO.input1 infile, c::data)
		    | NONE => data before TextIO.closeIn infile
    in implode (List.rev (reader (TextIO.input1 infile, [])))
    end

fun parse str =
    let val lexer = Lexer.newLexer str
	val parser = Parser.newParser lexer
    in Parser.parse parser
    end

fun loadInitialBasis () =
    let val flags = { prompt = false, showAST = false }
	val (Gamma, Rho) = introducePrimitives (emptyEnv, emptyEnv, emptyEnv)
	val basisText = readFileIntoString "basis.lj"
	val decls = SOME (parse basisText)
		    handle Parser.SyntaxError msg => NONE before print msg
	val (_, Gamma', Rho', Delta)
	    = (case decls of SOME ds =>
			     List.foldl (fn (dec, (str, Gamma, Rho, Delta)) =>
					    processDef (dec, flags, Gamma, Rho, Delta))
					("", Gamma, Rho, emptyEnv) ds
			   | NONE => ("", Gamma, Rho, emptyEnv))
	      handle e => (recover e, Gamma, Rho, emptyEnv)
    in (Gamma', Rho', Delta)
    end
	
fun REPL flags =
    let fun loop (Gamma, Rho, Delta) =
	    let val decls = SOME (parse (fetchInput flags))
			    handle Parser.SyntaxError msg => NONE before print msg
		val (response, Gamma', Rho', Delta')
		    = (case decls of SOME ds =>
				     List.foldl (fn (dec, (str, Gamma, Rho, Delta)) =>
						    processDef (dec, flags, Gamma, Rho, Delta))
						("", Gamma, Rho, Delta) ds
				   | NONE => ("", Gamma, Rho, Delta))
		      handle e => (recover e, Gamma, Rho, Delta)
		val _ = print (response ^ "\n")
	    in loop (Gamma', Rho', Delta')
	    end
    in loop (loadInitialBasis ())
    end

val _ = let val args = CommandLine.arguments()
	    val prompt = not (List.exists (fn s => s = "-q") args)
	    val showAST = List.exists (fn s => s = "--AST") args
	    val _ = REPL ({ prompt = prompt, showAST = showAST })
	in ()
	end
