From Coq Require Import Init.Nat.

Inductive Tree {T : Type} :=
  | node (t : T) (l r : Tree)
  | null : Tree.

Example Sorted := node 10 (node 5 (node 2 null null) (node 7 null null)) (node 16 (node 12 null null) (node 17 null null)).
Example Unsorted := node 1 (node 2 (node 3 null null) (node 4 null null)) (node 5 null null).

Inductive sorted : @Tree nat -> Prop :=
  | leaf_sorted : sorted null
  | node_empty (t : nat) : sorted (node t null null)
  | node_left (t l : nat) (ll lr : Tree) :
      (l <? t) = true ->
      sorted (node l ll lr) ->
      sorted (node t (node l ll lr) null)
  | node_right (t r : nat) (rl rr : Tree) :
      (t <? r) = true ->
      sorted (node r rl rr) ->
      sorted (node t null (node r rl rr))
  | node_full (t l r : nat) (ll lr rl rr : Tree) :
      (l <? t) = true ->
      (t <? r) = true ->
      sorted (node l ll lr) ->
      sorted (node r rl rr) ->
      sorted (node t (node l ll lr) (node r rl rr)).

Example SortedSorted : sorted Sorted.
Proof.
  unfold Sorted; repeat (try reflexivity; constructor).
Qed.

Example UnsortedUnsorted : sorted Unsorted -> False.
Proof.
  unfold Unsorted. intro. inversion H. inversion H4.
Qed.

Fixpoint elem_of (x : nat) (t : @Tree nat) : bool := match t with
  | node t l r => if x =? t then true else
    if x <? t then elem_of x l else elem_of x r
  | null => false
end.

Example SortedDoesntContain4 : elem_of 4 Sorted = false.
Proof. reflexivity. Qed.

Example SortedDoesntContain27 : elem_of 27 Sorted = false.
Proof. reflexivity. Qed.

Example SortedContains17 : elem_of 17 Sorted = true.
Proof. reflexivity. Qed.

Example SortedContains10 : elem_of 10 Sorted = true.
Proof. reflexivity. Qed.

Fixpoint insert (x : nat) (t : Tree) : Tree := match t with
  | node t l r => if x =? t then node t l r else
    if x <? t then node t (insert x l) r else node t l (insert x r)
  | null => node x null null
end.

Example InsertIntoEmpty : insert 5 null = node 5 null null.
Proof. reflexivity. Qed.

Example InsertIntoExisting : insert 7 (insert 5 null) = node 5 null (node 7 null null).
Proof. reflexivity. Qed.

Lemma insert_always_produce_node : forall t x,
  exists t' l r, insert x t = node t' l r.
Proof.
  induction t.
  - intros x. unfold insert. destruct (x =? t1). {
      exists t1. exists t2. exists t3. reflexivity.
    }
    destruct (x <? t1). {
      destruct (IHt1 x). exists t1. destruct H. destruct H.
      exists (node x0 x1 x2). exists t3. rewrite <- H. reflexivity.
    }
    exists t1. exists t2. destruct (IHt2 x). destruct H. destruct H.
    exists (node x0 x1 x2). rewrite <- H. reflexivity.
  - intros x. exists x. exists null. exists null. reflexivity.
Qed.

Lemma insert_diff_root_stays :
  forall (x x': nat) (t1 t2 : Tree),
  x' <> x ->
  exists (t1' t2' : Tree), insert x' (node x t1 t2) = node x t1' t2'.
Proof.
  intros.
Admitted.

Lemma subst_node : forall (x' : nat) (t : Tree),
  insert x' t = node x' null null \/
  (exists (x : nat) (t1 t2 t1': Tree), t = node x t1 t2 -> x' <? x = true -> insert x' t = node x t1' t2) \/
  (exists (x : nat) (t1 t2 : Tree), t = node x t1 t2 -> x = x' -> insert x' t = t) \/
  (exists (x : nat) (t1 t2 t2' : Tree), t = node x t1 t2 -> x <? x' = true -> insert x' t = node x t1 t2').
Proof.
Admitted.

Lemma insert_sorted : forall t x,
  sorted t -> sorted (insert x t).
Proof.
  induction t.
  - intros. cbn. destruct (x =? t1) eqn:Heq. {
    apply H.
  }
  destruct t1.
    + destruct t2. {
        inversion H. inversion H2. inversion H4.
      }
      destruct t3. 2: {
        constructor.
        - destruct x.
          + discriminate Heq.
          + reflexivity.
        - constructor.
      }
      inversion H. apply (IHt2 x) in H5. subst.

        apply (IHt2 x) in H5.
      assert (Hsome_node: exists (n : nat) (t1' t2': Tree),
              insert x (node t t3_1 t3_2) = node n t1' t2'). {
        apply insert_always_produce_node.
      }
      destruct Hsome_node as [x' [t1' [t2']]].
      rewrite H6 in *. constructor. subst.