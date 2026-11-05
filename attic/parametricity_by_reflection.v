From elpi.apps Require Import derive.std.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

(* The type of Church-encoded natural numbers: *)
Definition church_nat := forall (T : Type), (T -> T) -> T -> T.

derive church_nat.
(*
church_nat_R =
fun f g : forall T : Type, (T -> T) -> T -> T =>
forall (T1 T2 : Type) (T_R : T1 -> T2 -> Type) (_1 : T1 -> T1) (_2 : T2 -> T2),
(forall (_3 : T1) (_4 : T2), T_R _3 _4 -> T_R (_1 _3) (_2 _4)) ->
forall (_3 : T1) (_4 : T2), T_R _3 _4 -> T_R (f T1 _1 _3) (g T2 _2 _4)
     : church_nat -> church_nat -> Type
*)

(* The conversion from `nat` to `church_nat`, i.e., `iter` in `ssrnat`: *)
Fixpoint eval_nat (n : nat) : church_nat := fun T succ zero =>
  if n is n'.+1 then succ (eval_nat n' T succ zero) else zero.

derive eval_nat.

Lemma nat_R_refl (n : nat) : nat_R n n.
Proof. by elim: n; constructor. Defined.

(* Church encoding of `100`: *)
Definition church_nat_100 : church_nat := Eval cbv in eval_nat 100.
(*
church_nat_100 =
fun (T : Type) (f : T -> T) (x : T) =>
f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f ...))))))))))))))))))))))
     : church_nat
*)

derive church_nat_100.

(* The parametricity of `iter` allows us to prove the parametricity of        *)
(* *concrete* Church-encoded natural numbers by reflection.                   *)
Lemma church_nat_100_R' : church_nat_R church_nat_100 church_nat_100.
Proof. exact: (eval_nat_R _ _ (nat_R_refl 100)). Qed.

Print church_nat_100_R. (* quadratic? *)
Print church_nat_100_R'. (* linear *)

(*
The general recipe for proving parametricity by reflection:
1. See the given polymorphic datatype `church_t` as Church encoding, and define
   an equivalent `Inductive` datatype `t`.
2. Define the `eval_t` function that converts `t` to `church_t`, and derive its
   parametricity `eval_t_R`.
3. Reify the given concrete term of type `church_t` to a term of type `t`.
   Supplying this reified term to `eval_t_R` gives us the parametricity of the
   given term.

Question: can we plug this idea into the parametricity translation? More
specifically:
- Can we extend this idea to the terms that are not fully concrete?
- How do we want to specify or detect the part of parametricity proofs that
  should be done by reflection?
*)
