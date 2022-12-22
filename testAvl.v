Set Warnings "-deprecated-hint-without-locality,-implicit-core-hint-db".

(** I wanted to use QuickChick to test AVL operations preserve
    all kinds of proerties. But after I write down all the proofs
    of decidability of these properties, I realised I can not
    test these propositions since we can not prove whether they hold
    or not automatically even though they are decidable. So if we want to
    test these properties, we have to define the function versions of
    all these proerties and prove they are equal to the prosition
    versions. Therefore, the following code is not really useful. *)

From BST Require Import project.
Require Import List. Import ListNotations.
From QuickChick Require Import QuickChick. Import QcNotation.
Require Import ssreflect ssrbool.
Require Import String.

Hint Constructors project.all.
Hint Constructors sorted.

Local Open Scope string_scope.
#[local] Instance showTree : Show tree :=
  {| show := let fix aux t :=
       match t with
         | leaf => "leaf"
         | node x lhs rhs =>
             "node (" ++ show x ++ ") ("
                      ++ aux lhs ++ ") ("
                      ++ aux rhs ++ ")"
       end
     in aux
  |}.
Local Close Scope string_scope.

Fixpoint genTreeSized (sz : nat) (g : G nat) : G tree :=
  match sz with
    | O => ret leaf
    | S sz' =>
        freq [ (1, ret leaf) ;
               (sz, liftM3 node g (genTreeSized sz' g)
                                  (genTreeSized sz' g))
             ]
  end.

Fixpoint shrinkTreeAux (s : nat -> list nat) (t : tree) : list tree :=
  match t with
    | leaf => []
    | node x l r => [l] ++ [r] ++
                    map (fun x' => node x' l r) (s x) ++
                    map (fun l' => node x l' r) (shrinkTreeAux s l) ++
                    map (fun r' => node x l r') (shrinkTreeAux s r)
  end.

#[local] Instance dec_all_less : forall n t, Dec (project.all (fun x => x < n) t).
Proof.
  constructor. induction t.
  - unfold decidable. left; auto.
  - assert (Hlt: decidable (n0 < n)) by apply Compare_dec.lt_dec.
    destruct Hlt; destruct IHt1; destruct IHt2; unfold decidable;
    (* One thing don't like about coq: can't do something with some specific clauses I want *)
    try solve [left; auto];
    solve [right; intro H; inversion H; contradiction].
Defined.

#[local] Instance dec_all_greater : forall n t, Dec (project.all (fun x => n < x) t).
Proof.
  constructor. induction t.
  - unfold decidable. left; auto.
  - assert (Hlt: decidable (n < n0)) by apply Compare_dec.lt_dec.
    destruct Hlt; destruct IHt1; destruct IHt2; unfold decidable;
    try solve [left; auto];
    solve [right; intro H; inversion H; contradiction].
Defined.

#[local] Instance dec_sorted : forall t, Dec (sorted t).
Proof.
  constructor. induction t.
  - unfold decidable. left; auto.
  - assert (Hall1: decidable (project.all (fun x => x < n) t1)) by apply dec_all_less.
    assert (Hall2: decidable (project.all (fun x => n < x) t2)) by apply dec_all_greater.
    destruct IHt1; destruct IHt2; destruct Hall1; destruct Hall2; unfold decidable;
    try solve [left; auto];
    solve [right; intro H; inversion H; contradiction].
Defined.

#[local] Instance dec_balancedF : forall t, Dec (AVL.balanced t = true).
Proof. intros. dec_eq. Defined.

#[local] Instance dec_balanced : forall t, Dec (AVL.balancedP t).
Proof.
  intros.
  assert (H: decidable (AVL.balanced t = true)) by apply dec_balancedF.
  destruct H as [H | H]; rewrite <- (AVL.balanced_prop t) in H;
  constructor; unfold decidable; auto.
Qed.

#[local] Instance dec_avl : forall t, Dec (AVL.avl t).
Proof. constructor. unfold AVL.avl. Fail apply Decidable.dec_and. Admitted.
