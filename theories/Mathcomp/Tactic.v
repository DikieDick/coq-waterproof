From mathcomp Require Import ssreflect ssrbool eqtype all_algebra.
(* FIXME: The import above 'all_algebra' is kinda big and slow, try to fix this! *)
Import Num.Def Num.Theory.

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
  Message.print(Message.of_string "proof_disjunction_using");
  Message.print(Message.of_constr lemma);
  destruct $lemma; auto.

Ltac2 Notation "proof_disjunction_using" lemma(constr) := proof_disjunction_using lemma.

(* TODO: I don't think using this tactic works in the case that the goal 
  includes the or statement as a subgoal, which is the case in the Either ... or ... usage *)
Ltac2 fail_if_open_goal () :=
  Control.enter (fun _ => fail).

Ltac2 rewrite_props_bools () :=
  ltac1:(rewrite [_ = _]bool_prop_equiv);
  ltac1:(rewrite [_ <> _]bool_prop_equiv2).

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
  | [|- (?x = ?y) \/ (?x <> ?y) ] => rewrite_props_bools (); proof_disjunction_using (eqVneq $x $y)
  | [|- (?x <> ?y) \/ (?x = ?y) ] => rewrite_props_bools (); proof_disjunction_using (eqVneq $x $y)
  | [|- (?y = ?x) \/ (?x <> ?y) ] => rewrite_props_bools (); proof_disjunction_using (eqVneq $x $y)
  | [|- (?y <> ?x) \/ (?x = ?y) ] => rewrite_props_bools (); proof_disjunction_using (eqVneq $x $y)

  (* --- /eqVneq --- *)
  (* --- real_leP --- *)
  | [
    h1: is_true (@in_mem (Num.NumDomain.sort ?r) ?x (@mem (Num.NumDomain.sort ?r) (predPredType (Num.NumDomain.sort ?r)) (@has_quality O (Num.NumDomain.sort ?r) (@Rreal ?r)))),
    h2: is_true (@in_mem (Num.NumDomain.sort ?r) ?y (@mem (Num.NumDomain.sort ?r) (predPredType (Num.NumDomain.sort ?r)) (@has_quality O (Num.NumDomain.sort ?r) (@Rreal ?r))))
    |- _ ] => 
    let h1 := Control.hyp h1 in
    let h2 := Control.hyp h2 in
    proof_disjunction_using (real_leP $h1 $h2)

  (* --- /real_leP --- *)

  (* --- real_ge0P --- *)
  | [
    h1: is_true (@in_mem (Num.NumDomain.sort ?r) ?x (@mem (Num.NumDomain.sort ?r) (predPredType (Num.NumDomain.sort ?r)) (@has_quality O (Num.NumDomain.sort ?r) (@Rreal ?r))))
    |- _ ] => let h1 := Control.hyp h1 in
    first [
      proof_disjunction_using (real_ge0P $h1); fail_if_open_goal ()
      | proof_disjunction_using (real_le0P $h1); fail_if_open_goal ()
    ]
  (* --- /real_ge0P --- *)

  end.

Ltac2 disjunction3 () :=
  match! goal with
  | [
    h1: is_true (@in_mem (Num.NumDomain.sort ?r) ?x (@mem (Num.NumDomain.sort ?r) (predPredType (Num.NumDomain.sort ?r)) (@has_quality O (Num.NumDomain.sort ?r) (@Rreal ?r)))),
    h2: is_true (@in_mem (Num.NumDomain.sort ?r) ?y (@mem (Num.NumDomain.sort ?r) (predPredType (Num.NumDomain.sort ?r)) (@has_quality O (Num.NumDomain.sort ?r) (@Rreal ?r))))
    |- _ ] => 
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

Goal (y = x) \/ (x <> y).
Proof.
auto with wp_core wp_decidability_classical.
Qed.

Goal (y <> x) \/ (x = y).
Proof.
auto with wp_core wp_decidability_classical.
Qed.

End tests. *)

(* Section tests_r.
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

Goal x \is Num.real -> y \is Num.real -> (x == y) \/ (x != y).
Proof.
intros.
auto with wp_core wp_decidability_classical.
Qed.

Goal x \is Num.real -> (x < 0) \/ (x >= 0).
Proof.
intros.
auto with wp_core wp_decidability_classical.
Qed.

Goal x \is Num.real -> (x <= 0) \/ (x > 0).
Proof.
intros.
auto with wp_core wp_decidability_classical.
Qed.


End tests_r. *)