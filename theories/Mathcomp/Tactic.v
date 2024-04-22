From mathcomp Require Import ssreflect ssrbool eqtype all_algebra.
(* FIXME: The import above 'all_algebra' is kinda big and slow, try to fix this! *)
Import Num.Def Num.Theory.

Lemma props__bools (T : eqType) (x y : T) : (x = y \/ x <> y) <-> (is_true (x == y) \/ is_true (x != y)).
Proof.
  split.

  move=>H.
  destruct H as [H1 | H2].
  move/eqP in H1.
  by left.
  move/eqP in H2.
  by right.

  move=>H.
  destruct H as [H1 | H2].
  move/eqP in H1.
  by left.
  move/eqP in H2.
  by right.
Qed.

Lemma props__bools2 (T : eqType) (x y : T) : (x <> y \/ x = y) <-> (is_true (x != y) \/ is_true (x == y)).
Proof.
  split.

  move=>H.
  destruct H as [H1 | H2].
  move/eqP in H1.
  by left.
  move/eqP in H2.
  by right.

  move=>H.
  destruct H as [H1 | H2].
  move/eqP in H1.
  by left.
  move/eqP in H2.
  by right.
Qed.

Lemma neq_sym (T : eqType) (x y : T) : x != y -> y != x.
Proof. 
  intro H.
  rewrite eq_sym in H.
  exact H.
Qed.

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

From Ltac2 Require Import Ltac2.

(* FIXME: This should get a different more fitting name *)
Ltac2 proof_disjunction_using (lemma:constr) :=
  destruct $lemma; auto.

Ltac2 Notation "proof_disjunction_using" lemma(constr) := proof_disjunction_using lemma.

Ltac2 disjunction () :=
  Message.print(Message.of_string "disjunction");
  match! goal with
  (* --- eqVneq ---*)

  (* bool prop *)
  | [|- is_true(?x == ?y) \/ (?x <> ?y) ] => proof_disjunction_using (eqVneq $x $y) 
  | [|- is_true(?x != ?y) \/ (?x = ?y) ] => proof_disjunction_using (eqVneq $x $y)
  | [|- is_true(?y == ?x) \/ (?x <> ?y) ] => proof_disjunction_using (eqVneq $x $y) 
  | [|- is_true(?y != ?x) \/ (?x = ?y) ] => proof_disjunction_using (eqVneq $x $y)
  (* prop bool *)
  | [|- (?x = ?y) \/ is_true(?x != ?y) ] => proof_disjunction_using (eqVneq $x $y)
  | [|- (?x <> ?y) \/ is_true(?x == ?y) ] => proof_disjunction_using (eqVneq $x $y)
  | [|- (?y = ?x) \/ is_true(?x != ?y) ] => proof_disjunction_using (eqVneq $x $y)
  | [|- (?y <> ?x) \/ is_true(?x == ?y) ] => proof_disjunction_using (eqVneq $x $y)
  (* bool bool *)
  | [|- is_true(?x == ?y) \/ is_true(?x != ?y) ] => proof_disjunction_using (eqVneq $x $y)
  | [|- is_true(?x != ?y) \/ is_true(?x == ?y) ] => proof_disjunction_using (eqVneq $x $y)
  | [|- is_true(?y == ?x) \/ is_true(?x != ?y) ] => proof_disjunction_using (eqVneq $x $y)
  | [|- is_true(?y != ?x) \/ is_true(?x == ?y) ] => proof_disjunction_using (eqVneq $x $y)
  (* prop prop *)
  | [|- (?x = ?y) \/ (?x <> ?y) ] => rewrite props__bools; proof_disjunction_using (eqVneq $x $y)
  | [|- (?x <> ?y) \/ (?x = ?y) ] => rewrite props__bools2; proof_disjunction_using (eqVneq $x $y)
  | [|- (?y = ?x) \/ (?x <> ?y) ] => rewrite props__bools; proof_disjunction_using (eqVneq $x $y)
  | [|- (?y <> ?x) \/ (?x = ?y) ] => rewrite props__bools2; proof_disjunction_using (eqVneq $x $y)

  (* --- /eqVneq --- *)
  (* --- real_leP --- *)
  | [
    h1: is_true (@in_mem (Num.NumDomain.sort ?r) ?x (@mem (Num.NumDomain.sort ?r) (predPredType (Num.NumDomain.sort ?r)) (@has_quality O (Num.NumDomain.sort ?r) (@Rreal ?r)))),
    h2: is_true (@in_mem (Num.NumDomain.sort ?r) ?y (@mem (Num.NumDomain.sort ?r) (predPredType (Num.NumDomain.sort ?r)) (@has_quality O (Num.NumDomain.sort ?r) (@Rreal ?r)))) |- _ ] => 
    let h1 := Control.hyp h1 in
    let h2 := Control.hyp h2 in
    proof_disjunction_using (real_leP $h1 $h2)

  (* --- /real_leP --- *)

  end.

Ltac2 disjunction3 () :=
  match! goal with
  | [
    h1: is_true (@in_mem (Num.NumDomain.sort ?r) ?x (@mem (Num.NumDomain.sort ?r) (predPredType (Num.NumDomain.sort ?r)) (@has_quality O (Num.NumDomain.sort ?r) (@Rreal ?r)))),
    h2: is_true (@in_mem (Num.NumDomain.sort ?r) ?y (@mem (Num.NumDomain.sort ?r) (predPredType (Num.NumDomain.sort ?r)) (@has_quality O (Num.NumDomain.sort ?r) (@Rreal ?r)))) |- _ ] => 
    let h1 := Control.hyp h1 in
    let h2 := Control.hyp h2 in
    proof_disjunction_using (real_ltgtP $h1 $h2)
  end.

(* Add to the hint database *)
#[export] Hint Extern 1 (_ \/ _) => ltac2:(disjunction ()) : wp_decidability_classical.
#[export] Hint Extern 1 (_ \/ _ \/ _) => ltac2:(disjunction3 ()) : wp_decidability_classical.
#[export] Hint Resolve eq_sym : wp_core.
#[export] Hint Resolve neq_sym : wp_core.
#[export] Hint Resolve bool_prop_equiv : wp_core.
#[export] Hint Resolve bool_prop_equiv2 : wp_core.

(* Set Printing All. *)

(* Section tests.
Parameter T : eqType.
Parameter x y : T.
Goal (x != y) \/ (x = y).
Proof.
auto with wp_core wp_decidability_classical.
Qed.

Goal (x = y) \/ (x != y).
Proof.
auto with wp_core wp_decidability_classical.
Qed.

Goal (x == y) \/ (x != y).
Proof.
auto with wp_core wp_decidability_classical.
(* exclusion(). *)
Qed.

Goal (x != y) \/ (x == y).
Proof.
auto with wp_core wp_decidability_classical.
Qed.

Goal (y == x) \/ (x != y).
Proof.
auto with wp_core wp_decidability_classical.
Qed.

(* Prop prop seems to be more involved *)
Goal (x = y) \/ (x <> y).
Proof.
(* destruct (eqVneq x y); auto. *)

(* exclusion(). *)
auto with wp_core wp_decidability_classical.
Qed.

Goal (x <> y) \/ (x = y).
Proof.
auto with wp_core wp_decidability_classical.
Qed.

(* This does not work *)
Goal (y = x) \/ (~(x = y)).
Proof.
match! goal with
  | [|- ?a \/ ?b ] => Message.print(Message.of_constr a); Message.print(Message.of_constr (Constr.type a)); Message.print(Message.of_constr b); Message.print(Message.of_constr (Constr.type b))
end.
exclusion().

End tests. *)
(* 
Section tests_r.
Parameter R : numDomainType.
Parameter x y : R.
Open Scope ring_scope.

Goal x \is Num.real -> y \is Num.real -> (`| x - y | = y - x) \/ (`| x - y | = x - y).
Proof.
intros.
Locate "\is".
(* Set Printing All. *)
auto with wp_core wp_decidability_classical.
Qed.

Goal x \is Num.real -> y \is Num.real -> (x == y) \/ (x < y) \/ (x > y).
Proof.
intros.
auto with wp_core wp_decidability_classical.
Qed.

End tests_r. *)