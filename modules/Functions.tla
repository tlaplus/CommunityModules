------------------------------ MODULE Functions -----------------------------
(***************************************************************************)
(* `^{\large\bf \vspace{12pt}                                              *)
(*  Notions about functions including injection, surjection, and bijection.*)
(*  Originally contributed by Tom Rodeheffer, MSR.                         *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)

LOCAL INSTANCE Folds

(***************************************************************************)
(* Restriction of a function to a set (should be a subset of the domain).  *)
(***************************************************************************)
\* @supportedBy("TLC,Apalache")
Restrict(f,S) == [ x \in S |-> f[x] ]

(***************************************************************************)
(* Range of a function.                                                    *)
(* Note: The image of a set under function f can be defined as             *)
(*       Range(Restrict(f,S)).                                             *)
(***************************************************************************)
\* @supportedBy("TLC,Apalache")
Range(f) == { f[x] : x \in DOMAIN f }


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
\* @supportedBy("TLC,Apalache")
Inverse(f,S,T) == [t \in T |-> CHOOSE s \in S : t \in Range(f) => f[s] = t]

(***************************************************************************)
(* The inverse of a function.                                              *)
(***************************************************************************)
\* @supportedBy("TLC,Apalache")
AntiFunction(f) == Inverse(f, DOMAIN f, Range(f))

(***************************************************************************)
(* A function is injective iff it maps each element in its domain to a     *)
(* distinct element.                                                       *)
(*                                                                         *)
(* This definition is overridden by TLC in the Java class SequencesExt.    *)
(* The operator is overridden by the Java method with the same name.       *)
(***************************************************************************)
\* @supportedBy("TLC,Apalache")
IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b

(***************************************************************************)
(* Set of injections between two sets.                                     *)
(***************************************************************************)
\* @supportedBy("TLC,Apalache")
Injection(S,T) == { M \in [S -> T] : IsInjective(M) }


(***************************************************************************)
(* A map is a surjection iff for each element in the range there is some   *)
(* element in the domain that maps to it.                                  *)
(***************************************************************************)
\* @supportedBy("TLC,Apalache")
Surjection(S,T) == { M \in [S -> T] : \A t \in T : \E s \in S : M[s] = t }


(***************************************************************************)
(* A map is a bijection iff it is both an injection and a surjection.      *)
(***************************************************************************)
\* @supportedBy("TLC,Apalache")
Bijection(S,T) == Injection(S,T) \cap Surjection(S,T)


(***************************************************************************)
(* An injection, surjection, or bijection exists if the corresponding set  *)
(* is nonempty.                                                            *)
(***************************************************************************)
\* @supportedBy("TLC,Apalache")
ExistsInjection(S,T)  == Injection(S,T) # {}
\* @supportedBy("TLC,Apalache")
ExistsSurjection(S,T) == Surjection(S,T) # {}
\* @supportedBy("TLC,Apalache")
ExistsBijection(S,T)  == Bijection(S,T) # {}

--------------------------------------------------------------------------------

\* @supportedBy("TLC,Apalache")
FoldFunction(op(_,_), base, fun) ==
  (***************************************************************************)
  (* Applies the binary function op on all elements of seq in arbitrary      *)
  (* order starting with op(f[k], base). The resulting function is:          *)
  (*    op(f[i],op(f[j], ..., op(f[k],base) ...))                            *)
  (*                                                                         *)
  (* op must be associative and commutative, because we can not assume a     *)
  (* particular ordering of i, j, and k                                      *)
  (*                                                                         *)
  (* Example:                                                                *)
  (*  FoldFunction(LAMBDA x,y: {x} \cup y, {}, <<1,2,1>>) = {1,2}            *)
  (***************************************************************************)
  MapThenFoldSet(op, base, LAMBDA i : fun[i], LAMBDA s: CHOOSE x \in s : TRUE, DOMAIN fun)


\* @supportedBy("TLC,Apalache")
FoldFunctionOnSet(op(_,_), base, fun, indices) ==
  (***************************************************************************)
  (* Applies the binary function op on the given indices of seq in arbitrary *)
  (* order starting with op(f[k], base). The resulting function is:          *)
  (*    op(f[i],op(f[j], ..., op(f[k],base) ...))                            *)
  (*                                                                         *)
  (* op must be associative and commutative, because we can not assume a     *)
  (* particular ordering of i, j, and k                                      *)
  (*                                                                         *)
  (* indices must be a subset of DOMAIN(fun)                                 *)
  (*                                                                         *)
  (* Example:                                                                *)
  (*  FoldFunctionOnSet(LAMBDA x,y: {x} \cup y, {}, <<1,2>>, {}) = {}        *)
  (***************************************************************************)
  MapThenFoldSet(op, base, LAMBDA i : fun[i], LAMBDA s: CHOOSE x \in s : TRUE, indices)

=============================================================================
\* Modification History
\* Last modified Mon Apr 05 03:25:53 CEST 2021 by marty
\* Last modified Sun Dec 27 09:38:06 CET 2020 by merz
\* Last modified Wed Jun 05 12:14:19 CEST 2013 by bhargav
\* Last modified Fri May 03 12:55:35 PDT 2013 by tomr
\* Created Thu Apr 11 10:30:48 PDT 2013 by tomr
