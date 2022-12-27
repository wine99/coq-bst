Require Import Arith.
Require Import Setoids.Setoid.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H : P) : reflect P true
  | ReflectF (H : not P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite Nat.eqb_eq. reflexivity.
Qed.

Lemma ltbP : forall n m, reflect (n < m) (n <? m).
Proof.
  intros n m. apply iff_reflect. rewrite Nat.ltb_lt. reflexivity.
Qed.

Lemma lebP : forall n m, reflect (n <= m) (n <=? m).
Proof.
  intros n m. apply iff_reflect. rewrite Nat.leb_le. reflexivity.
Qed.
