From mathcomp Require Import ssreflect ssrbool eqtype.

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
Ltac2 exclude_using (exclusion_lemma:constr) :=
  destruct $exclusion_lemma; auto.

Ltac2 Notation "exclude_using" exclusion_lemma(constr) := exclude_using exclusion_lemma.

Ltac2 exclusion () :=
  Message.print(Message.of_string "Using Exclusion");
  match! goal with
  (* bool prop *)
  | [|- is_true(?x == ?y) \/ (?x <> ?y) ] => exclude_using (eqVneq $x $y) 
  | [|- is_true(?x != ?y) \/ (?x = ?y) ] => exclude_using (eqVneq $x $y)
  | [|- is_true(?y == ?x) \/ (?x <> ?y) ] => exclude_using (eqVneq $x $y) 
  | [|- is_true(?y != ?x) \/ (?x = ?y) ] => exclude_using (eqVneq $x $y)
  (* prop bool *)
  | [|- (?x = ?y) \/ is_true(?x != ?y) ] => exclude_using (eqVneq $x $y)
  | [|- (?x <> ?y) \/ is_true(?x == ?y) ] => exclude_using (eqVneq $x $y)
  | [|- (?y = ?x) \/ is_true(?x != ?y) ] => exclude_using (eqVneq $x $y)
  | [|- (?y <> ?x) \/ is_true(?x == ?y) ] => exclude_using (eqVneq $x $y)
  (* bool bool *)
  | [|- is_true(?x == ?y) \/ is_true(?x != ?y) ] => exclude_using (eqVneq $x $y)
  | [|- is_true(?x != ?y) \/ is_true(?x == ?y) ] => exclude_using (eqVneq $x $y)
  | [|- is_true(?y == ?x) \/ is_true(?x != ?y) ] => exclude_using (eqVneq $x $y)
  | [|- is_true(?y != ?x) \/ is_true(?x == ?y) ] => exclude_using (eqVneq $x $y)
  (* prop prop *)
  | [|- (?x = ?y) \/ (?x <> ?y) ] => rewrite props__bools; exclude_using (eqVneq $x $y)
  | [|- (?x <> ?y) \/ (?x = ?y) ] => rewrite props__bools2; exclude_using (eqVneq $x $y)
  | [|- (?y = ?x) \/ (?x <> ?y) ] => rewrite props__bools; exclude_using (eqVneq $x $y)
  | [|- (?y <> ?x) \/ (?x = ?y) ] => rewrite props__bools2; exclude_using (eqVneq $x $y)
  end.

(* Add to the hint database *)
#[export] Hint Extern 1 (_ \/ _) => ltac2:(exclusion ()) : wp_decidability_classical.
#[export] Hint Resolve eq_sym : wp_core.
#[export] Hint Resolve neq_sym : wp_core.
#[export] Hint Resolve bool_prop_equiv : wp_core.
#[export] Hint Resolve bool_prop_equiv2 : wp_core.

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