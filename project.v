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
  | all_node : forall p n lhs rhs,
      all p lhs ->
      all p rhs ->
      p n ->
      all p (node n lhs rhs).

Hint Constructors all.

Inductive sorted : tree -> Prop :=
  | sorted_leaf : sorted leaf
  | sorted_node : forall n lhs rhs,
      sorted lhs ->
      sorted rhs ->
      all (fun x => x < n) lhs ->
      all (fun x => n < x) rhs ->
      sorted (node n lhs rhs).

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
  | node n lhs rhs =>
      if x =? n then true else
      if x <? n then elem_of x lhs else
      elem_of x rhs
  | leaf => false
end.

Inductive elem_ofP : nat -> tree -> Prop :=
  | elem_ofP_root : forall x lhs rhs,
      elem_ofP x (node x lhs rhs)
  | elem_ofP_left : forall x n lhs rhs,
      elem_ofP x lhs ->
      x < n ->
      elem_ofP x (node n lhs rhs)
  | elem_ofP_right : forall x n lhs rhs,
      elem_ofP x rhs ->
      n < x ->
      elem_ofP x (node n lhs rhs).

Hint Constructors elem_ofP.

Lemma elem_of_prop : forall x t, elem_ofP x t <-> elem_of x t = true.
Proof with auto.
  intros. split; intros.
  - induction H; simpl; subst.
    + rewrite Nat.eqb_refl. reflexivity.
    + simpl. destruct (eqbP x n)...
      destruct (ltbP x n)...
    + destruct (eqbP x n)...
      destruct (x <? n) eqn:Hlt...
      apply Nat.ltb_lt in Hlt; lia.
  - induction t; simpl in *; try discriminate.
    destruct (eqbP x n); subst...
    destruct (ltbP x n); subst...
    assert (n < x) by lia...
Qed.

Lemma elem_of_reflect : forall x t, reflect (elem_ofP x t) (elem_of x t).
Proof.
  intros. apply iff_reflect. apply elem_of_prop.
Qed.

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
  | node n lhs rhs =>
      if x =? n then t
      else if x <? n then node n (insert x lhs) rhs
      else node n lhs (insert x rhs)
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

Lemma insert_correctP : forall t x y,
  sorted t ->
  elem_ofP y (insert x t) <-> (elem_ofP y t) \/ (y = x).
Proof with auto.
  intros; split; intros.
  - rewrite elem_of_prop in H0.
    rewrite insert_correct in H0...
    destruct (elem_of y t) eqn: Helem.
    rewrite <- elem_of_prop in Helem...
    destruct (y =? x) eqn:Heq.
    rewrite Nat.eqb_eq in Heq... discriminate.
  - rewrite elem_of_prop.
    rewrite insert_correct...
    destruct H0...
    rewrite elem_of_prop in H0; intuition.
    rewrite <- Nat.eqb_eq in H0; intuition.
Qed.

From Coq Require Import Lists.List.

Fixpoint bst_to_list (bst : tree) : list nat :=
  match bst with
    | leaf => nil
    | node x lhs rhs => (bst_to_list lhs) ++ x :: nil ++ (bst_to_list rhs)
  end.

Fixpoint list_to_bst (l : list nat) : tree :=
  match l with
  | nil => leaf
  | x :: xs => insert x (list_to_bst xs)
  end.

Lemma to_bst_sorted : forall (l : list nat),
  sorted (list_to_bst l).
Proof.
  induction l.
  - simpl; constructor.
  - simpl. now apply insert_sorted.
Qed.

Lemma to_bst_still_contains : forall (e : nat) (l : list nat),
  (In e l) <-> elem_ofP e (list_to_bst l).
Proof.
  split; intros.
  - induction l.
    + inversion H.
    + simpl in H. destruct H.
      * subst. simpl.
        rewrite insert_correctP. right. reflexivity.
        apply to_bst_sorted.
      * simpl.
        rewrite insert_correctP. left. now apply IHl.
        apply to_bst_sorted.
  - induction l.
    + inversion H.
    + simpl in H. destruct (eqbP e a).
      * subst. simpl. left. reflexivity.
      * simpl. right.
        rewrite insert_correctP in H; try apply to_bst_sorted.
        destruct H; try contradiction.
        now apply IHl in H.
Qed.

Lemma to_list_preserve_all : forall e t p,
  all p t ->
  In e (bst_to_list t) ->
  p e.
Proof.
  intros. induction H; subst.
  - inversion H0.
  - simpl in H0. apply List.in_app_or in H0. destruct H0.
    now apply IHall1 in H0.
    destruct H0; subst; try assumption.
    now apply IHall2 in H0.
Qed.

Lemma to_list_still_contains : forall (e : nat) (t : tree),
  sorted t ->
  (elem_ofP e t) <-> In e (bst_to_list t).
Proof with auto.
  intros e t Hsorted. split; intros.
  - induction H; simpl.
    + apply in_or_app. right. simpl; left; reflexivity.
    + inversion Hsorted; subst. apply IHelem_ofP in H4.
      apply in_or_app. now left.
    + inversion Hsorted; subst. apply IHelem_ofP in H5.
      apply in_or_app. right. now simpl; right.
  - induction t.
    + inversion H.
    + inversion Hsorted; subst.
      simpl in H. apply in_app_or in H. destruct H.
      apply (to_list_preserve_all _ _ _ H5) in H as Hlt...
      destruct H; subst...
      apply (to_list_preserve_all _ _ _ H6) in H as Hlt...
Qed.

Lemma through_list_perserves_elements : forall (e : nat) (t : tree),
  sorted t -> (elem_ofP e t <-> elem_ofP e (list_to_bst (bst_to_list t))).
Proof.
  intros e t Hsorted. split; intros.
  - inversion H; subst;
    solve [
      inversion Hsorted; subst;
      apply to_list_still_contains in H; auto;
      apply to_bst_still_contains in H; auto
    ].
  - apply to_list_still_contains; auto.
    apply to_bst_still_contains; auto.
Qed.

Fixpoint max (t : tree) : nat :=
  match t with
  | node n lhs rhs =>
      match rhs with
      | leaf => n
      | _ => max rhs
      end
  | leaf => 0
  end.

Fixpoint delete x t :=
  match t with
  | leaf => leaf
  | node n lhs rhs =>
      if x =? n then
        match lhs, rhs with
        | leaf, leaf => leaf
        | leaf, _ => rhs
        | _, leaf => lhs
        | _, _ => node (max lhs) (delete (max lhs) lhs) rhs
        end
      else if x <? n then
        node n (delete x lhs) rhs
      else
        node n lhs (delete x rhs)
  end.

Example deletes_nothing : delete 0 (node 10 leaf leaf) = node 10 leaf leaf.
Proof. reflexivity. Qed.

Example deletes_something : delete 10 (node 10 leaf leaf) = leaf.
Proof. reflexivity. Qed.

Example rotates_correctly : delete 10 Sorted = node 7 (node 5 (node 2 leaf leaf) leaf) (node 16 (node 12 leaf leaf) (node 17 leaf leaf)).
Proof. reflexivity. Qed.

Lemma simpl_max : forall n n' lhs lhs' rhs',
  max (node n lhs (node n' lhs' rhs')) = max (node n' lhs' rhs').
Proof.
  intros. reflexivity.
Qed.

Lemma max_preserves_all : forall p n lhs rhs,
  all p (node n lhs rhs) ->
  p (max (node n lhs rhs)).
Proof.
  intros.
  generalize dependent n.
  generalize dependent lhs.
  induction rhs; intros.
  - simpl. now inversion H.
  - rewrite simpl_max.
    inversion H; subst.
    now apply IHrhs2 in H5.
Qed.

(* Have not used this lemma *)
Lemma max_is_in_tree : forall t n lhs rhs,
  t = node n lhs rhs ->
  sorted t ->
  elem_ofP (max t) t.
Proof.
  intros; subst.
  generalize dependent n.
  generalize dependent lhs.
  induction rhs; intros lhs root Hsorted.
  - constructor.
  - inversion Hsorted; subst.
    rewrite simpl_max.
    apply elem_ofP_right.
    now apply IHrhs2.
    now apply max_preserves_all in H5.
Qed.

Lemma delete_all : forall p t x,
  all p t ->
  all p (delete x t).
Proof.
  intros. generalize dependent x.
  induction H; subst; intros; auto.
  simpl. destruct (eqbP x n).
  - destruct lhs; destruct rhs; try assumption.
    constructor.
    + apply IHall1.
    + assumption.
    + now apply max_preserves_all in H.
  - destruct (ltbP x n); auto.
Qed.

Lemma no_deletion_if_all_less : forall n n' lhs rhs,
  sorted (node n' lhs rhs) ->
  all (fun x : nat => n < x) (node n' lhs rhs) ->
  delete n (node n' lhs rhs) = node n' lhs rhs.
Proof.
  intros. induction H. {
    reflexivity.
  }
  simpl. destruct (eqbP n n0).
  - subst. inversion H0. lia.
  - inversion H0. subst. rewrite <- Nat.ltb_lt in H11. rewrite H11.
    apply IHsorted1 in H9. now rewrite H9.
Qed.

Lemma no_deletion_if_all_greater : forall n n' lhs rhs,
  sorted (node n' lhs rhs) ->
  all (fun x : nat => x < n) (node n' lhs rhs) ->
  delete n (node n' lhs rhs) = node n' lhs rhs.
Proof.
  intros. induction H. {
    reflexivity.
  }
  simpl. destruct (eqbP n n0).
  - subst. inversion H0. lia.
  - inversion H0; subst. destruct (ltbP n n0); try lia.
    apply IHsorted2 in H10. now rewrite H10.
Qed.

Lemma delete_correct : forall t x,
  sorted t ->
  elem_ofP x (delete x t) -> False.
Proof.
  intros t x HSorted HBad.
  induction HSorted; subst; intros.
  { inversion HBad. }
  simpl in HBad. destruct (eqbP x n).
  - subst. destruct lhs eqn:d1; destruct rhs eqn:d2.
    + inversion HBad.
    + apply IHHSorted2. rewrite no_deletion_if_all_less; assumption.
    + apply IHHSorted1. rewrite no_deletion_if_all_greater; assumption.
    + rewrite <- d1 in *. rewrite <- d2 in *. inversion HBad;
      try (
        assert (Hmax: max lhs < n);
        try (subst lhs; apply max_preserves_all; assumption);
        lia
      ).
      assert (Hrhs: delete n rhs = rhs).
      { subst rhs; apply no_deletion_if_all_less; assumption. }
      rewrite <- Hrhs in H4.
      now apply IHHSorted2.
  - destruct (ltbP x n);
    (inversion HBad; subst; auto; lia).
Qed.

Lemma all_less_trans : forall t n n',
  sorted t ->
  n < n' ->
  all (fun x => x < n) t ->
  all (fun x => x < n') t.
Proof.
  intros. remember (fun x => x < n) as p.
  induction H1; auto. inversion H; subst.
  constructor.
  apply IHall1; auto.
  apply IHall2; auto.
  lia.
Qed.

Lemma all_greater_trans : forall t n n',
  sorted t ->
  n' < n ->
  all (fun x => n < x) t ->
  all (fun x => n' < x) t.
Proof.
  intros. remember (fun x => n < x) as p.
  induction H1; auto. inversion H; subst.
  constructor.
  apply IHall1; auto.
  apply IHall2; auto.
  lia.
Qed.

Lemma simpl_delete : forall m n lhs n' rhs1 rhs2,
  n < m ->
  sorted (node n lhs (node n' rhs1 rhs2)) ->
  delete m (node n lhs (node n' rhs1 rhs2)) =
  node n lhs (delete m (node n' rhs1 rhs2)).
Proof.
  intros; simpl.
  destruct (eqbP m n); try lia.
  destruct (ltbP m n); try lia.
  reflexivity.
Qed.

Lemma delete_max : forall t n lhs rhs,
  t = node n lhs rhs ->
  sorted t ->
  all (fun x => x < max t) (delete (max t) t).
Proof with auto.
  intros; subst.
  inversion H0; subst.
  remember (max (node n lhs rhs)) as m.
  generalize dependent n.
  generalize dependent lhs.
  induction rhs; intros.
  - subst. simpl. rewrite Nat.eqb_refl.
    destruct lhs...
  - rewrite simpl_max in Heqm.
    assert (Hmgt: n0 < m).
    { subst; apply max_preserves_all... }
    rewrite simpl_delete...
    constructor...
    apply all_less_trans with (n := n0)...
    inversion H4; apply IHrhs2...
Qed.

Lemma delete_sorted : forall t x,
  sorted t ->
  sorted (delete x t).
Proof.
  intros. generalize dependent x.
  induction H; subst; intros; auto.
  simpl. destruct (eqbP x n).
  - subst. destruct lhs; destruct rhs; try assumption.
    constructor; auto.
    + eapply delete_max; eauto.
    + assert (Hmax: max (node n0 lhs1 lhs2) < n).
      { apply max_preserves_all; assumption. }
      apply all_greater_trans with (n := n); assumption.
  - destruct (ltbP x n);
    constructor; auto; now apply delete_all.
Qed.
