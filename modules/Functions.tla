------------------------------ MODULE Functions -----------------------------
(***************************************************************************)
(* `^{\large\bf \vspace{12pt}                                              *)
(*  Notions about functions including injection, surjection, and bijection.*)
(*  Originally contributed by Tom Rodeheffer, MSR.                         *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)

EXTENDS Folds

(***************************************************************************)
(* Restriction of a function to a set (should be a subset of the domain).  *)
(***************************************************************************)
Restrict(f,S) == [ x \in S |-> f[x] ]

(***************************************************************************)
(* Restriction of a function to the subset of its domain satisfying a      *)
(* test predicate.                                                         *)
(*                                                                         *)
(* Example:                                                                *)
(*   (LET f == (0 :> "a" @@ 1 :> "b" @@ 2 :> "c")                          *)
(*    IN  RestrictDomain(f, LAMBDA x : x \in {0,2}))                       *)
(*   = (0 :> "a" @@ 2 :> "c")                                              *)
(***************************************************************************)
RestrictDomain(f, Test(_)) == Restrict(f, {x \in DOMAIN f : Test(x)})

(***************************************************************************)
(* Restriction of a function to the subset of its domain for which the     *)
(* function values satisfy a test predicate.                               *)
(*                                                                         *)
(* Example:                                                                *)
(*   (LET f == ("a" :> 0 @@ "b" :> 1 @@ "c" :> 2)                          *)
(*    IN  RestrictValues(f, LAMBDA y : y \in {0,2}))                       *)
(*   = ("a" :> 0 @@ "b" :> 2)                                              *)
(*                                                                         *)
(* This is similar to the operator SelectSeq from the standard Sequences   *)
(* module and related to standard "filter" functions in functional         *)
(* programming. However, SelectSeq produces sequences, whereas             *)
(* RestrictValues will in general not. For example,                        *)
(*                                                                         *)
(*   RestrictValues([0,1,2], LAMBDA y : y \in {0,2})                       *)
(*   = (1 :> 0 @@ 3 :> 2)                                                  *)
(***************************************************************************)
RestrictValues(f, Test(_)) ==
  LET S == {x \in DOMAIN f : Test(f[x])}
  IN  Restrict(f, S)

(***************************************************************************)
(* Check if a function narrow is a restriction of a function wide, i.e.    *)
(* Is the domain of narrow a subset of that of wide, and does the          *)
(* projection of wide on the domain of narrow have the same image as       *)
(* narrow does.                                                            *)
(*                                                                         *)
(* Examples:                                                               *)
(*   IsRestriction([one |-> 1], [one |-> 1, two |-> 2])                    *)
(*   IsRestriction([one |-> 1], [one |-> 1])                               *)
(*  ~IsRestriction([one |-> 1, two |-> 2], [one |-> 1, two |-> 3])         *)
(*  ~IsRestriction([one |-> 1], [2 |-> two])                               *)
(*  ~IsRestriction([one |-> 1, two |-> 2], [two |-> 2])                    *)
(***************************************************************************)
IsRestriction(narrow, wide) ==
    /\ DOMAIN narrow \subseteq DOMAIN wide 
    /\ \A x \in DOMAIN narrow \intersect DOMAIN wide: narrow[x] = wide[x]

(***************************************************************************)
(* Range of a function.                                                    *)
(* Note: The image of a set under function f can be defined as             *)
(*       Range(Restrict(f,S)).                                             *)
(***************************************************************************)
Range(f) == { f[x] : x \in DOMAIN f }

(***************************************************************************)
(* Assuming DOMAIN f \subseteq DOMAIN g, apply the binary operation T to   *)
(* the corresponding elements of the two functions f and g.                *)
(*                                                                         *)
(* Example:                                                                *)
(*   LET f == ("a" :> 0 @@ "b" :> 1 @@ "c" :> 2)                           *)
(*       g == ("a" :> 1 @@ "b" :> 1 @@ "c" :> 3)                           *)
(*   IN Pointwise(f,g,+) = ("a" :> 1 @@ "b" :> 2 @@ "c" :> 5 )             *)
(***************************************************************************)
Pointwise(f, g, T(_,_)) == [ e \in DOMAIN f |-> T(f[e], g[e]) ]

(***************************************************************************)
(* The inverse of a function.                                              *)
(* Example:                                                                *)
(*    LET f == ("a" :> 0 @@ "b" :> 1 @@ "c" :> 2)                          *)
(*    IN Inverse(f, DOMAIN f, Range(f)) =                                  *)
(*                                 (0 :> "a" @@ 1 :> "b" @@ 2 :> "c")      *)
(* Example:                                                                *)
(*    LET f == ("a" :> 0 @@ "b" :> 1 @@ "c" :> 2)                          *)
(*    IN Inverse(f, DOMAIN f, {1,3}) =                                     *)
(*                                 1 :> "b" @@ 3 :> "a")                   *)
(***************************************************************************)
Inverse(f,S,T) == [t \in T |-> CHOOSE s \in S : t \in Range(f) => f[s] = t]

(***************************************************************************)
(* The inverse of a function.                                              *)
(***************************************************************************)
AntiFunction(f) == Inverse(f, DOMAIN f, Range(f))

(***************************************************************************)
(* A function is injective iff it maps each element in its domain to a     *)
(* distinct element.                                                       *)
(*                                                                         *)
(* This definition is overridden by TLC in the Java class Functions.java   *)
(* The operator is overridden by the Java method with the same name.       *)
(***************************************************************************)
IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b

(***************************************************************************)
(* Set of injections between two sets.                                     *)
(***************************************************************************)
Injection(S,T) == { M \in [S -> T] : IsInjective(M) }


(***************************************************************************)
(* A map is a surjection iff for each element in the range there is some   *)
(* element in the domain that maps to it.                                  *)
(***************************************************************************)
Surjection(S,T) == { M \in [S -> T] : \A t \in T : \E s \in S : M[s] = t }


(***************************************************************************)
(* A map is a bijection iff it is both an injection and a surjection.      *)
(***************************************************************************)
Bijection(S,T) == Injection(S,T) \cap Surjection(S,T)


(***************************************************************************)
(* An injection, surjection, or bijection exists if the corresponding set  *)
(* is nonempty.                                                            *)
(***************************************************************************)
ExistsInjection(S,T)  == Injection(S,T) # {}
ExistsSurjection(S,T) == Surjection(S,T) # {}
ExistsBijection(S,T)  == Bijection(S,T) # {}

--------------------------------------------------------------------------------

(***************************************************************************)
(* Applies the binary operator op on the elements f[i] for i \in indices,  *)
(* a subset of DOMAIN fun, in an unspecified order, starting from value    *)
(* base. The result is                                                     *)
(*    op(f[i],op(f[j], ..., op(f[k],base) ...))                            *)
(* where i,j,k range over the sets indices.                                *)
(*                                                                         *)
(* op should be associative and commutative, because we can not assume a   *)
(* particular ordering of i, j, and k                                      *)
(*                                                                         *)
(* Example:                                                                *)
(*  FoldFunctionOnSet(LAMBDA x,y: {x} \cup y, {}, <<1,2>>, {}) = {}        *)
(***************************************************************************)
FoldFunctionOnSet(op(_,_), base, fun, indices) ==
  MapThenFoldSet(op, base, LAMBDA i : fun[i], LAMBDA s: CHOOSE x \in s : TRUE, indices)

(***************************************************************************)
(* Special case of the above where indices = DOMAIN fun. In other words,   *)
(* the values f[i] for all i \in DOMAIN fun, are combined using the binary *)
(* operator op, in an unspecified order.                                   *)
(*                                                                         *)
(* Example:                                                                *)
(*  FoldFunction(LAMBDA x,y: {x} \cup y, {}, <<1,2,1>>) = {1,2}            *)
(***************************************************************************)
FoldFunction(op(_,_), base, fun) ==
  FoldFunctionOnSet(op, base, fun, DOMAIN fun)

=============================================================================
\* Created Thu Apr 11 10:30:48 PDT 2013 by tomr
