From mathcomp Require Import ssreflect ssrbool eqtype ssrfun all_algebra.

Import Num.Def Num.Theory.

Lemma bool_prop_equiv (T : eqType) (x y : T) : (x = y) <-> (x == y).
  split.
  -move=>H.
  by apply/eqP.
  -move=>H.
  by apply/eqP.
Qed.

Lemma bool_prop_equiv2 (T : eqType) (x y : T) : (x <> y) <-> (x != y).
  split.
  -move=>H.
  by apply/eqP.
  -move=>H.
  by apply/eqP.
Qed.

Lemma neq_sym (T : eqType) (x y : T) : x != y -> y != x.
Proof.
  move => H.
  by rewrite eq_sym in H.
Qed.


From Ltac2 Require Import Ltac2 Message.

Ltac2 proof_disjunction_using (lemma: constr) :=
  print(of_string "We are here");
  print(of_constr lemma);
  ltac1:(lemma |- case: lemma; try intro; try assumption) (Ltac1.of_constr lemma);
  try (apply or_introl; apply is_true_true);
  try (apply or_introl; assumption);
  try (apply or_intror; apply is_true_true);
  try (apply or_intror; assumption).

Ltac2 proof_disjunction () :=

  try (ltac1:(rewrite [_ = _]bool_prop_equiv));
  try (ltac1:(rewrite [_ <> _]bool_prop_equiv2));

  first [
    proof_disjunction_using constr:(@eqVneq)     |
    proof_disjunction_using constr:(@real_leP)   |
    proof_disjunction_using constr:(@real_ge0P)  |
    proof_disjunction_using constr:(@real_le0P)  |
    proof_disjunction_using constr:(@real_ltgtP) 
  ].

#[export] Hint Extern 1 (_ \/ _) => ltac2:(proof_disjunction ()) : wp_decidability_classical.
#[export] Hint Extern 1 (_ \/ _ \/ _) => ltac2:(proof_disjunction ()) : wp_decidability_classical.
#[export] Hint Resolve eq_sym : wp_core.
#[export] Hint Resolve neq_sym : wp_core.

(* Goal forall T : eqType, forall x y : T, x = y \/ x != y.
Proof.
  intros.
  auto with wp_decidability_classical.
Qed.

Goal forall T : eqType, forall x y : T, x != y \/ x = y.
Proof.
  intros.
  auto with wp_decidability_classical.
Qed.

Goal forall T : eqType, forall x y : T, x == y \/ x != y.
Proof.
  intros.
  auto with wp_decidability_classical.
Qed.

Goal forall T : eqType, forall x y : T, x = y \/ x <> y.
Proof.
  intros.
  auto with wp_decidability_classical.
Qed.

Goal forall T : eqType, forall x y : T, x <> y \/ x = y.
Proof.
  intros.
  auto with wp_decidability_classical.
Qed.

Section R_tests.
Open Scope ring_scope.

Parameter R : numDomainType.
Parameters x y : R.

Goal x \is Num.real -> y \is Num.real -> x <= y \/ x > y.
Proof.
  intros.
  auto with wp_decidability_classical.
Qed.

End R_tests. *)