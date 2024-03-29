Set Warnings "-deprecated-hint-without-locality,-implicit-core-hint-db".
Require Import PeanoNat.
Require Import Setoids.Setoid.
Require Import Lia.
Require Import List. Import ListNotations.
From BST Require Import helpers.

Inductive tree :=
  | leaf
  | node (n : nat) (lhs rhs : tree).

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
  y <> x ->
  elem_of y (insert x t) = elem_of y t.
Proof.
  intros.
  induction t.
  - simpl. apply Nat.eqb_neq in H. rewrite H.
    destruct (ltbP y x); reflexivity.
  - simpl. destruct (eqbP x n); try reflexivity.
    destruct (ltbP x n);
    solve [simpl; destruct (eqbP y n); try reflexivity;
      destruct (ltbP y n); auto].
Qed.

Lemma insert_correct : forall t x y,
  elem_of y (insert x t) = orb (elem_of y t) (y =? x).
Proof with auto.
  intros. induction t.
  - simpl. destruct (eqbP y x)... destruct (ltbP y x)...
  - unfold insert. destruct (eqbP x n).
    + (* inserted [x] = root [n] *)
      simpl. destruct (eqbP y n); subst...
      (* searching [y] <> root [n] *)
      destruct (ltbP y n);
      try rewrite <- IHt1; try rewrite <- IHt2;
      rewrite insert_diff_root...
    + destruct (ltbP x n); fold insert.
      * (* inserted [x] < root [n] *)
        simpl. destruct (eqbP y n); subst...
        destruct (ltbP y n).
        -- (* searching [y] < root [n] *)
           apply IHt1.
        -- (* searching [y] > root [n] *)
           assert (Hneq: x <> y) by lia.
           rewrite <- IHt2.
           rewrite insert_diff_root...
      * (* inserted [x] > root [n] *)
        simpl. destruct (eqbP y n); subst...
        destruct (ltbP y n).
        -- (* searching [y] < root [n] *)
           assert (Hneq: x <> y) by lia.
           rewrite <- IHt1.
           rewrite insert_diff_root...
        -- (* searching [y] > root [n] *)
           apply IHt2.
Qed.

Lemma insert_correctP : forall t x y,
  elem_ofP y (insert x t) <-> (elem_ofP y t) \/ (y = x).
Proof with auto.
  intros; split; intros.
  - rewrite elem_of_prop in H.
    rewrite insert_correct in H...
    destruct (elem_of y t) eqn: Helem.
    rewrite <- elem_of_prop in Helem...
    destruct (y =? x) eqn:Heq.
    rewrite Nat.eqb_eq in Heq... discriminate.
  - rewrite elem_of_prop.
    rewrite insert_correct...
    destruct H...
    rewrite elem_of_prop in H; intuition.
    rewrite <- Nat.eqb_eq in H; intuition.
Qed.

From Coq Require Import Lists.List.

Fixpoint bst_to_list (bst : tree) : list nat :=
  match bst with
    | leaf => []
    | node x lhs rhs => (bst_to_list lhs) ++ [x] ++ (bst_to_list rhs)
  end.

Fixpoint list_to_bst (l : list nat) : tree :=
  match l with
  | [] => leaf
  | x :: xs => insert x (list_to_bst xs)
  end.

Lemma to_bst_still_contains : forall (e : nat) (l : list nat),
  (In e l) <-> elem_ofP e (list_to_bst l).
Proof.
  split; intros.
  - induction l.
    + inversion H.
    + simpl in H. destruct H.
      * subst. simpl.
        rewrite insert_correctP. right. reflexivity.
      * simpl.
        rewrite insert_correctP. left. now apply IHl.
  - induction l.
    + inversion H.
    + simpl in H. destruct (eqbP e a).
      * subst. simpl. left. reflexivity.
      * simpl. right.
        rewrite insert_correctP in H.
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
  - induction H; simpl; apply in_or_app.
    + right. simpl; left; reflexivity.
    + inversion Hsorted; subst. apply IHelem_ofP in H4.
      now left.
    + inversion Hsorted; subst. apply IHelem_ofP in H5.
      right. now simpl; right.
  - induction t.
    + inversion H.
    + inversion Hsorted; subst.
      simpl in H. apply in_app_or in H. destruct H.
      * apply (to_list_preserve_all _ _ _ H5) in H as Hlt...
      * destruct H; subst...
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
      apply to_bst_still_contains in H; auto ].
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
  intros. induction H. reflexivity.
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
  intros. induction H. reflexivity.
  simpl. destruct (eqbP n n0).
  - subst. inversion H0. lia.
  - inversion H0; subst. destruct (ltbP n n0); try lia.
    apply IHsorted2 in H10. now rewrite H10.
Qed.

Lemma delete_correct : forall t x,
  sorted t ->
  elem_ofP x t ->
  elem_ofP x (delete x t) -> False.
Proof.
  intros t x HSorted Hin HBad.
  induction HSorted; subst; intros.
  { inversion HBad. }
  inversion Hin; subst.
  - unfold delete in HBad. rewrite Nat.eqb_refl in HBad. fold delete in HBad.
    destruct lhs eqn:d1; destruct rhs eqn:d2.
    + inversion HBad.
    + apply IHHSorted2; auto. rewrite no_deletion_if_all_less; auto.
    + apply IHHSorted1; auto. rewrite no_deletion_if_all_greater; auto.
    + rewrite <- d1 in *. rewrite <- d2 in *. inversion HBad;
      try (
        assert (Hmax: max lhs < n);
        try (subst lhs; apply max_preserves_all; assumption);
        lia ).
      assert (Hrhs: delete n rhs = rhs).
      { subst rhs; apply no_deletion_if_all_less; assumption. }
      rewrite Hrhs in IHHSorted2.
      apply IHHSorted2; auto.
  - subst. unfold delete in HBad. destruct (eqbP x n); try lia.
    destruct (ltbP x n); try lia. fold delete in HBad.
    inversion HBad; try lia; auto.
  - subst. unfold delete in HBad. destruct (eqbP x n); try lia.
    destruct (ltbP x n); try lia. fold delete in HBad.
    inversion HBad; try lia; auto.
Qed.

Lemma all_less_trans : forall t n n',
  n < n' ->
  all (fun x => x < n) t ->
  all (fun x => x < n') t.
Proof.
  intros. remember (fun x => x < n) as p.
  induction t; auto. inversion H0; subst.
  constructor; auto; lia.
Qed.

Lemma all_greater_trans : forall t n n',
  n' < n ->
  all (fun x => n < x) t ->
  all (fun x => n' < x) t.
Proof.
  intros. remember (fun x => n < x) as p.
  induction t; auto. inversion H0; subst.
  constructor; auto; lia.
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

(* ----------------------- AVL ----------------------- *)

Module AVL.

Fixpoint height (t : tree) : nat :=
  match t with
  | leaf => 0
  | node _ lhs rhs => S (Nat.max (height lhs) (height rhs))
  end.

Inductive balanced : tree -> Prop :=
  | balanced_leaf : balanced leaf
  | balanced_eq : forall n lhs rhs,
      balanced lhs ->
      balanced rhs ->
      height lhs = height rhs ->
      balanced (node n lhs rhs)
  | balanced_l1 : forall n lhs rhs,
      balanced lhs ->
      balanced rhs ->
      height lhs = S (height rhs) ->
      balanced (node n lhs rhs)
  | balanced_r1 : forall n lhs rhs,
      balanced lhs ->
      balanced rhs ->
      height rhs = S (height lhs) ->
      balanced (node n lhs rhs).

Hint Constructors balanced.

Lemma height_single : forall n,
  height (node n leaf leaf) = 1.
Proof. reflexivity. Qed.

Example test_balanced_p1 : balanced Sorted.
Proof. unfold Sorted; auto. Qed.

Example test_balanced_p2 : balanced Unsorted.
Proof. unfold Unsorted; auto. Qed.

Example test_balanced_n1 : balanced (node 10 Unsorted (node 11 leaf leaf)) -> False.
Proof.
  unfold Unsorted; intro.
  solve_by_inverts 2.
Qed.

Example test_balanced_n2 : balanced (node 10 (node 11 leaf leaf) Unsorted) -> False.
Proof.
  unfold Unsorted; intro.
  solve_by_inverts 2.
Qed.

Definition avl t := sorted t /\ balanced t.

Definition balance n lhs rhs :=
  let hl := height lhs in
  let hr := height rhs in
  if S hr <? hl then
    match lhs with
    | leaf => leaf (* impossible *)
    | node n' lhs1 lhs2 =>
        if height lhs2 <=? height lhs1 then
          node n' lhs1 (node n lhs2 rhs)
        else
          match lhs2 with
          | leaf => leaf (* impossible *)
          | node n'' lhs2_1 lhs2_2 =>
              node n'' (node n' lhs1 lhs2_1) (node n lhs2_2 rhs)
          end
    end
  else if S hl <? hr then
    match rhs with
    | leaf => leaf (* impossible *)
    | node n' rhs1 rhs2 =>
        if height rhs1 <=? height rhs2 then
          node n' (node n lhs rhs1) rhs2
        else
          match rhs1 with
          | leaf => leaf (* impossible *)
          | node n'' rhs1_1 rhs1_2 =>
              node n'' (node n lhs rhs1_1) (node n' rhs1_2 rhs2)
          end
    end
  else node n lhs rhs.

Fixpoint insert x t :=
  match t with
  | leaf => node x leaf leaf
  | node n lhs rhs =>
      if x =? n then t
      else if x <? n then balance n (insert x lhs) rhs
      else balance n lhs (insert x rhs)
  end.

Ltac invert_and_construct :=
  repeat
    match goal with
    | |- sorted _ _ (node _ _ _) => try assumption; constructor
    | |- sorted (if ?x =? ?y then _ else _) => destruct (eqbP x y)
    | |- sorted (if ?x <? ?y then _ else _) => destruct (ltbP x y)
    | |- sorted (if ?x then _ else _) => destruct x
    | |- all _ (node _ _ _) => try assumption; constructor
    | |- all _ (if ?x then _ else _) => destruct x
    | |- all _ (match ?t with leaf => _ | node _ _ _ => _ end) => destruct t
    | H: sorted (node _ _ _) |- _ => inversion H; clear H; subst
    | H: all _ (node _ _ _) |- _ => inversion H; clear H; subst
    end;
    try lia; auto.

Ltac construct_with_all_tran :=
  repeat constructor; try lia; eauto using all_greater_trans, all_less_trans.

Lemma balance_sorted : forall n lhs rhs,
  sorted (node n lhs rhs) ->
  sorted (balance n lhs rhs).
Proof.
  intros.
  inversion H; clear H; subst.
  destruct lhs; destruct rhs; unfold balance; cbn; auto.
  - destruct rhs1; destruct rhs2; cbn; invert_and_construct.
    construct_with_all_tran.
  - destruct lhs1; destruct lhs2; cbn; invert_and_construct;
    construct_with_all_tran.
  - destruct lhs1; destruct lhs2; destruct rhs1; destruct rhs2; invert_and_construct;
    construct_with_all_tran.
Qed.

Lemma balance_all : forall p n lhs rhs,
  all p (node n lhs rhs) ->
  all p (balance n lhs rhs).
Proof.
  intros.
  inversion H; clear H; subst.
  destruct lhs; destruct rhs; unfold balance; cbn; invert_and_construct.
Qed.

Lemma insert_all : forall p x t,
  all p t ->
  p x ->
  all p (insert x t).
Proof.
  intros. generalize dependent x.
  induction t; intros; simpl; auto.
  invert_and_construct; auto using balance_all.
Qed.

Ltac use_helper_lemmas :=
  match goal with
  | |- sorted (balance _ _ _) => apply balance_sorted
  | |- all _ (balance _ _ _) => apply balance_all
  | |- all _ (insert _ _) => apply insert_all
  end;
  try constructor; auto.

Lemma insert_sorted : forall x t,
  sorted t ->
  sorted (insert x t).
Proof.
  intros. induction H; simpl; auto.
  invert_and_construct; repeat use_helper_lemmas; lia.
Qed.

Lemma SS_lt_S : forall x,
  S (S x) <? S x = false.
Proof.
  induction x; auto.
Qed.

Lemma SS_lt_SS: forall x,
  S (S x) <? S (S x) = false.
Proof.
  induction x; auto.
Qed.

Lemma SSS_lt_S : forall x,
  S (S (S x)) <? S x = false.
Proof.
  induction x; auto.
Qed.

Lemma already_balanced : forall n lhs rhs,
  balanced (node n lhs rhs) ->
  balanced (balance n lhs rhs).
Proof.
  intros.
  destruct lhs; destruct rhs; auto.
  - inversion H; try solve_by_invert.
    destruct rhs1; destruct rhs2; try solve_by_invert; auto.
  - inversion H; try solve_by_invert.
    destruct lhs1; destruct lhs2; try solve_by_invert; auto.
  - inversion H; try solve_by_invert;
    unfold balance; rewrite H5; simpl;
    try rewrite SS_lt_S;
    try rewrite SSS_lt_S;
    try rewrite SS_lt_SS; auto.
Qed.

Lemma insert_exists : forall x t,
  exists n lhs rhs, insert x t = node n lhs rhs.
Proof.
  intros. induction t; simpl.
  - exists x, leaf, leaf; reflexivity.
  - rename t1 into lhs. rename t2 into rhs.
    destruct (eqbP x n).
    + exists n, lhs, rhs; reflexivity.
    + destruct (ltbP x n).
      * destruct IHt1 as [n0 [lhs1 [lhs2 IHt1]]].
        rewrite IHt1.
        unfold balance.
        destruct (ltbP (S (height rhs)) (height (node n0 lhs1 lhs2))).
        -- destruct (lebP (height lhs2) (height lhs1)).
           ++ exists n0, lhs1, (node n lhs2 rhs); reflexivity.
           ++ assert (height lhs2 > height lhs1) by lia.
              destruct lhs2; try solve_by_invert.
              exists n1, (node n0 lhs1 lhs2_1), (node n lhs2_2 rhs); reflexivity.
        -- destruct (ltbP (S (height (node n0 lhs1 lhs2))) (height rhs)).
           ++ destruct rhs; try solve_by_invert.
              destruct (lebP (height rhs1) (height rhs2)).
              exists n1, (node n (node n0 lhs1 lhs2) rhs1), rhs2; reflexivity.
              assert (height rhs1 > height rhs2) by lia.
              destruct rhs1; try solve_by_invert.
              exists n2, (node n (node n0 lhs1 lhs2) rhs1_1), (node n1 rhs1_2 rhs2); reflexivity.
           ++ exists n, (node n0 lhs1 lhs2), rhs; reflexivity.
      * destruct IHt2 as [n0 [rhs1 [rhs2 IHt2]]].
        rewrite IHt2.
        unfold balance.
        destruct (ltbP (S (height (node n0 rhs1 rhs2))) (height lhs)).
        -- destruct lhs; try solve_by_invert.
           destruct (lebP (height lhs2) (height lhs1)).
           ++ exists n1, lhs1, (node n lhs2 (node n0 rhs1 rhs2)); reflexivity.
           ++ assert (height lhs2 > height lhs1) by lia.
              destruct lhs2; try solve_by_invert.
              exists n2, (node n1 lhs1 lhs2_1), (node n lhs2_2 (node n0 rhs1 rhs2)); reflexivity.
        -- destruct (ltbP (S (height lhs)) (height (node n0 rhs1 rhs2))).
           ++ destruct (lebP (height rhs1) (height rhs2)).
              exists n0, (node n lhs rhs1), rhs2; reflexivity.
              assert (height rhs1 > height rhs2) by lia.
              destruct rhs1; try solve_by_invert.
              exists n1, (node n lhs rhs1_1), (node n0 rhs1_2 rhs2); reflexivity.
           ++ exists n, lhs, (node n0 rhs1 rhs2); reflexivity.
Qed.

Lemma insert_height : forall x t,
  balanced t ->
  height (insert x t) = height t \/
  height (insert x t) = S (height t).
Proof with try lia.
  intros. induction H; auto; unfold insert.
  - destruct (eqbP x n); fold insert; auto.
    destruct (ltbP x n).
    + destruct (insert_exists x lhs) as [n0 [lhs1 [lhs2 Hex]]].
      rewrite Hex in *.
      unfold balance.
      destruct (ltbP (S (height rhs)) (height (node n0 lhs1 lhs2)))...
      destruct (ltbP (S (height (node n0 lhs1 lhs2))) (height rhs))...
      destruct IHbalanced1;
      unfold height in *...
    + destruct (insert_exists x rhs) as [n0 [rhs1 [rhs2 Hex]]].
      rewrite Hex in *.
      unfold balance.
      destruct (ltbP (S (height (node n0 rhs1 rhs2))) (height lhs))...
      destruct (ltbP (S (height lhs)) (height (node n0 rhs1 rhs2)))...
      destruct IHbalanced2;
      unfold height in *...
  - destruct (eqbP x n); fold insert; auto.
    destruct (ltbP x n).
    + destruct (insert_exists x lhs) as [n0 [lhs1 [lhs2 Hex]]].
      rewrite Hex in *.
      unfold balance.
      destruct (ltbP (S (height rhs)) (height (node n0 lhs1 lhs2))).
      * destruct IHbalanced1...
        destruct (lebP (height lhs2) (height lhs1)).
        -- unfold height in *...
        -- assert (height lhs2 > height lhs1)...
           destruct lhs2; try solve_by_invert.
           left; unfold height in *...
      * destruct (ltbP (S (height (node n0 lhs1 lhs2))) (height rhs))...
        destruct IHbalanced1...
        left; unfold height in *...
    + destruct (insert_exists x rhs) as [n0 [rhs1 [rhs2 Hex]]].
      rewrite Hex in *.
      unfold balance.
      destruct (ltbP (S (height (node n0 rhs1 rhs2))) (height lhs))...
      destruct (ltbP (S (height lhs)) (height (node n0 rhs1 rhs2)))...
      left; unfold height in *...
  - destruct (eqbP x n); fold insert; auto.
    destruct (ltbP x n).
    + destruct (insert_exists x lhs) as [n0 [lhs1 [lhs2 Hex]]].
      rewrite Hex in *.
      unfold balance.
      destruct (ltbP (S (height rhs)) (height (node n0 lhs1 lhs2)))...
      destruct (ltbP (S (height (node n0 lhs1 lhs2))) (height rhs))...
      left; unfold height in *...
    + destruct (insert_exists x rhs) as [n0 [rhs1 [rhs2 Hex]]].
      rewrite Hex in *.
      unfold balance.
      destruct (ltbP (S (height (node n0 rhs1 rhs2))) (height lhs))...
      destruct (ltbP (S (height lhs)) (height (node n0 rhs1 rhs2))).
      * destruct (lebP (height rhs1) (height rhs2)).
        -- unfold height in *...
        -- assert (height rhs1 > height rhs2)...
           destruct rhs1; try solve_by_invert.
           left; unfold height in *...
      * destruct IHbalanced2...
        left; unfold height in *...
Qed.

Lemma insert_balanced : forall x t,
  balanced t ->
  balanced (insert x t).
Proof with try lia.
  intros. induction H.
  - simpl insert. auto.
  - unfold insert.
    destruct (x =? n) eqn:Heq; auto.
    fold insert. destruct (x <? n) eqn:Hlt.
    + apply already_balanced.
      destruct (insert_height x lhs H) as [Hh | Hh];
      [ apply balanced_eq | apply balanced_l1 ];
      try rewrite Hh; auto.
    + apply already_balanced.
      destruct (insert_height x rhs H0) as [Hh | Hh];
      [ apply balanced_eq | apply balanced_r1 ];
      try rewrite Hh; auto.
  - unfold insert.
    destruct (x =? n) eqn:Heq; auto.
    fold insert. destruct (x <? n) eqn:Hlt.
    + destruct (insert_height x lhs H) as [Hh | Hh].
      * apply already_balanced. apply balanced_l1; try rewrite Hh; auto.
      * destruct (insert_exists x lhs) as [n0' [lhs1' [lhs2' Ht]]].
        rewrite Ht in *. rewrite H1 in *.
        unfold balance.
        assert (Hlt' : S (height rhs) < height (node n0' lhs1' lhs2'))...
        rewrite <- Nat.ltb_lt in Hlt'.
        rewrite Hlt'.
        inversion IHbalanced1; subst.
        -- destruct (lebP (height lhs2') (height lhs1'))...
           inversion Hh.
           assert (Hh1: height lhs1' = S (height rhs))...
           assert (Hh2: height lhs2' = S (height rhs))...
           apply balanced_r1; auto; simpl...
        -- destruct (lebP (height lhs2') (height lhs1'))...
           inversion Hh.
           assert (Hh1: height lhs1' = S (height rhs))...
           assert (Hh2: height lhs2' = height rhs)...
           apply balanced_eq; auto; simpl...
        -- destruct (lebP (height lhs2') (height lhs1'))...
           destruct lhs2'; inversion H7. inversion Hh.
           inversion H6; subst.
           ++ assert (Hh1: height lhs2'1 = height lhs1')...
              apply balanced_eq; auto.
              apply balanced_eq; auto...
              simpl...
           ++ assert (Hh1: height lhs2'1 = height lhs1')...
              assert (Hh2: height rhs = S (height lhs2'2))...
              apply balanced_eq; auto; simpl...
           ++ assert (Hh1: S (height lhs2'1) = height lhs1')...
              assert (Hh2: height rhs = height lhs2'2)...
              apply balanced_eq; auto; simpl...
    + destruct (insert_height x rhs H0) as [Hh | Hh];
      apply already_balanced;
      [ apply balanced_l1 | apply balanced_eq ]; try rewrite Hh; auto.
  - unfold insert.
    destruct (x =? n) eqn:Heq; auto.
    fold insert. destruct (x <? n) eqn:Hlt.
    + destruct (insert_height x lhs H) as [Hh | Hh];
      apply already_balanced;
      [ apply balanced_r1 | apply balanced_eq ]; try rewrite Hh; auto.
    + destruct (insert_height x rhs H0) as [Hh | Hh].
      * apply already_balanced. apply balanced_r1; try rewrite Hh; auto.
      * destruct (insert_exists x rhs) as [n0' [rhs1' [rhs2' Ht]]].
        rewrite Ht in *. rewrite H1 in *.
        unfold balance.
        destruct (ltbP (S (height (node n0' rhs1' rhs2'))) (height lhs))...
        destruct (ltbP (S (height lhs)) (height (node n0' rhs1' rhs2')))...
        inversion IHbalanced2; subst.
        -- destruct (lebP (height rhs1') (height rhs2'))...
           inversion Hh.
           assert (Hh1: height rhs1' = S (height lhs))...
           assert (Hh2: height rhs2' = S (height lhs))...
           apply balanced_l1; auto; simpl...
        -- destruct (lebP (height rhs1') (height rhs2'))...
           inversion Hh.
           destruct rhs1'; inversion H9.
           inversion H7; subst.
           ++ assert (Hh1: height rhs1'1 = height lhs)...
              apply balanced_eq; auto.
              apply balanced_eq; auto...
              simpl...
           ++ assert (Hh1: height rhs1'1 = height lhs)...
              assert (Hh2: height rhs2' = S (height rhs1'2))...
              apply balanced_eq; auto; simpl...
           ++ assert (Hh1: S (height rhs1'1) = height lhs)...
              assert (Hh2: height rhs2' = height rhs1'2)...
              apply balanced_eq; auto; simpl...
        -- destruct (lebP (height rhs1') (height rhs2'))...
           inversion Hh.
           assert (Hh1: height rhs2' = S (height lhs))...
           assert (Hh2: height lhs = height rhs1')...
           apply balanced_eq; auto; simpl...
Qed.

Lemma insert_AVL: forall x t,
  avl t -> avl (insert x t).
Proof.
  unfold avl in *; split; destruct H;
  try apply insert_sorted;
  try apply insert_balanced; auto.
Qed.

End AVL.
