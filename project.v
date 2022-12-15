Set Warnings "-deprecated-hint-without-locality,-implicit-core-hint-db".
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Lia.
From BST Require Import helpers.

Inductive tree :=
  | leaf : tree
  | node : nat -> tree -> tree -> tree.

Example Sorted := node 10 (node 5 (node 2 leaf leaf) (node 7 leaf leaf)) (node 16 (node 12 leaf leaf) (node 17 leaf leaf)).
Example Unsorted := node 1 (node 2 (node 3 leaf leaf) (node 4 leaf leaf)) (node 5 leaf leaf).

Inductive all : (nat -> Prop) -> tree -> Prop :=
  | all_leaf : forall p,
      all p leaf
  | all_node : forall p n t1 t2,
      all p t1 ->
      all p t2 ->
      p n ->
      all p (node n t1 t2).

Hint Constructors all.

Inductive sorted : tree -> Prop :=
  | sorted_leaf : sorted leaf
  | sorted_node : forall n t1 t2,
      sorted t1 ->
      sorted t2 ->
      all (fun x => x < n) t1 ->
      all (fun x => n < x) t2 ->
      sorted (node n t1 t2).

Hint Constructors sorted.

Example SortedSorted : sorted Sorted.
Proof.
  unfold Sorted; repeat (try reflexivity; constructor).
Qed.

Example UnsortedUnsorted : sorted Unsorted -> False.
Proof.
  unfold Unsorted; intro; (solve_by_inverts 4).
Qed.

Fixpoint elem_of (x : nat) (t : tree) : bool := match t with
  | node n t1 t2 =>
      if x =? n then true else
      if x <? n then elem_of x t1 else
      elem_of x t2
  | leaf => false
end.

Inductive elem_ofP : nat -> tree -> Prop :=
  | elem_ofP_root : forall x lhs rhs, elem_ofP x (node x lhs rhs)
  | elem_ofP_left : forall x x' lhs rhs,
      elem_ofP x lhs ->
      x < x' ->
      elem_ofP x (node x' lhs rhs)
  | elem_ofP_right : forall x x' lhs rhs,
      elem_ofP x rhs ->
      x > x' ->
      elem_ofP x (node x' lhs rhs).

Lemma elem_of_prop : forall x t, elem_of x t = true <-> elem_ofP x t.
Proof.
Admitted.

Example SortedDoesntContain4 : elem_of 4 Sorted = false.
Proof. reflexivity. Qed.

Example SortedDoesntContain27 : elem_of 27 Sorted = false.
Proof. reflexivity. Qed.

Example SortedContains17 : elem_of 17 Sorted = true.
Proof. reflexivity. Qed.

Example SortedContains10 : elem_of 10 Sorted = true.
Proof. reflexivity. Qed.

Fixpoint insert (x : nat) (t : tree) : tree := match t with
  | leaf => node x leaf leaf
  | node n t1 t2 =>
      if x =? n then t else
      if x <? n then node n (insert x t1) t2 else
      node n t1 (insert x t2)
end.

Example InsertIntoEmpty : insert 5 leaf = node 5 leaf leaf.
Proof. reflexivity. Qed.

Example InsertIntoExisting : insert 7 (insert 5 leaf) = node 5 leaf (node 7 leaf leaf).
Proof. reflexivity. Qed.

Lemma insert_all : forall p t x,
  all p t ->
  p x ->
  all p (insert x t).
Proof with auto.
  intros. induction H.
  - constructor...
  - unfold insert. destruct (eqbP x n)...
    destruct (ltbP x n)...
Qed.

Lemma insert_sorted : forall t x,
  sorted t -> sorted (insert x t).
Proof with auto using insert_all.
  intros. induction H.
  - constructor...
  - unfold insert.
    destruct (eqbP x n)...
    destruct (ltbP x n)...
    assert (Hlt: n < x) by lia...
Qed.

Lemma insert_diff_root : forall t x y,
  sorted t ->
  y <> x ->
  elem_of y (insert x t) = elem_of y t.
Proof.
  intros.
  induction H.
  - simpl. apply Nat.eqb_neq in H0. rewrite H0.
    destruct (ltbP y x); reflexivity.
  - simpl. destruct (eqbP x n).
    + subst. apply Nat.eqb_neq in H0. rewrite H0.
      destruct (y <? n) eqn:Hyn;
      solve [simpl; rewrite H0; rewrite Hyn; reflexivity].
    + destruct (x <? n);
      solve [simpl; destruct (eqbP y n); try reflexivity;
        destruct (y <? n); auto].
Qed.

Lemma insert_correct : forall t x y,
  sorted t ->
  elem_of y (insert x t) = orb (elem_of y t) (y =? x).
Proof with auto.
  intros. induction H.
  - simpl. destruct (eqbP y x)... destruct (ltbP y x)...
  - unfold insert. destruct (eqbP x n).
    + (* inserted [x] = root [n] *)
      simpl. destruct (eqbP y n); subst...
      * (* searching [y] <> root [n] *)
        destruct (ltbP y n);
        try rewrite <- IHsorted1; try rewrite <- IHsorted2;
        rewrite insert_diff_root...
    + destruct (ltbP x n); fold insert.
      * (* inserted [x] < root [n] *)
        simpl. destruct (eqbP y n); subst...
        destruct (ltbP y n).
        -- (* searching [y] < root [n] *)
           apply IHsorted1.
        -- (* searching [y] > root [n] *)
           assert (Hneq: x <> y) by lia.
           rewrite <- IHsorted2.
           rewrite insert_diff_root...
      * (* inserted [x] > root [n] *)
        simpl. destruct (eqbP y n); subst...
        destruct (ltbP y n).
        -- (* searching [y] < root [n] *)
           assert (Hneq: x <> y) by lia.
           rewrite <- IHsorted1.
           rewrite insert_diff_root...
        -- (* searching [y] > root [n] *)
           apply IHsorted2.
Qed.

Fixpoint bst_to_list (bst : tree) : list nat :=
  match bst with
    | leaf => nil
    | node x lhs rhs => (bst_to_list lhs) ++ x :: nil ++ (bst_to_list rhs)
  end.

From Coq Require Import Lists.List.

Definition list_to_bst (l : list nat) : tree := fold_left (fun acc e => insert e acc) l leaf.

Lemma toBSTStillContains : forall (e : nat) (l : list nat),
  (In e l) <-> elem_ofP e (list_to_bst l).
Proof.
Admitted.

Lemma toListStillContains : forall (e : nat) (t : tree),
  (elem_ofP e t) <-> In e (bst_to_list t).
Proof.
Admitted.

Lemma conversionThroughListPreservesElements : forall (e : nat) (t : tree),
  sorted t -> (elem_ofP e t <-> elem_ofP e (list_to_bst (bst_to_list t))).
Proof.
  split.
  - intros. inversion H0.
    + assert (H_contains_root: elem_ofP x (node x lhs rhs)) by constructor.
      apply toListStillContains in H_contains_root. apply toBSTStillContains in H_contains_root.
      subst. assumption.
    + assert (H_contains_left: elem_ofP e (node x' lhs rhs)). {
        constructor; assumption.
      }
      apply toListStillContains in H_contains_left. apply toBSTStillContains in H_contains_left.
      assumption.
    + assert (H_contains_right: elem_ofP e (node x' lhs rhs)). {
        constructor; assumption.
      }
      apply toListStillContains in H_contains_right. apply toBSTStillContains in H_contains_right.
      assumption.
  - intros. apply toListStillContains. apply toBSTStillContains. assumption.
Qed.
