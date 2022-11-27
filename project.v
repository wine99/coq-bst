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
      (l <=? t) = true ->
      sorted (node l ll lr) ->
      sorted (node t (node l ll lr) null)
  | node_right (t r : nat) (rl rr : Tree) :
      (t <=? r) = true ->
      sorted (node r rl rr) ->
      sorted (node t null (node r rl rr))
  | node_full (t l r : nat) (ll lr rl rr : Tree) :
      (l <=? t) = true ->
      (t <=? r) = true ->
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