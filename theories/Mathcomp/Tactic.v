From Ltac2 Require Import Ltac2.

From mathcomp Require Import ssrbool eqtype.

Ltac2 exclude_using (exclusion_lemma:constr) :=
  destruct $exclusion_lemma; auto.

Ltac2 Notation "exclude_using" exclusion_lemma(constr) := exclude_using exclusion_lemma.

Ltac2 exclusion () :=
  match! goal with
  (* | [ h : _ |- ?x \/ ?y ] => Message.print(Message.concat (Message.of_constr x) (Message.of_constr y)) *)
  | [ h : _ |- (?x = ?y) \/ is_true(?x != ?y) ] => exclude_using (eqVneq $x $y)
  (* | [ h : _ |- _ ] => let h := Control.hyp h in Message.print (Message.of_constr h); apply $h *)
  end.

Lemma neq_sym (T : eqType) (x y : T) : x != y -> y != x.
Proof. 
intro H.
rewrite eq_sym in H.
exact H.
Qed.

#[export] Hint Extern 1 => ltac2:(exclusion ()) : wp_decidability_classical.
#[export] Hint Resolve eq_sym : wp_core.
#[export] Hint Resolve neq_sym : wp_core.