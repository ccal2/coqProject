Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.

Inductive tree : Type :=
  | Nil
  | Node (v : nat) (l r : tree).

Fixpoint insert (t : tree) (v: nat): tree :=
  match t with
  | Nil => Node v Nil Nil
  | Node v' l r => if v <? v'
                   then Node v' (insert l v) r
                   else if v' <? v
                        then Node v' l (insert r v)
                        else t
  end.

Fixpoint search (t:tree) (v:nat) : bool :=
   match t with
   | Nil => false
   | Node v' l r => if v <? v'
                   then search l v
                   else if v' <? v
                        then search r v
                        else true
  end.

Fixpoint ForallT (t : tree) (P : nat -> Prop) : Prop :=
  match t with
  | Nil => True
  | Node v' l r => P v' /\ ForallT l P /\ ForallT r P
  end.

Inductive BST : tree -> Prop :=
  | BST_Empty: BST Nil
  | BST_Node (v : nat) (l r : tree):
    BST l ->
    BST r ->
    ForallT l (fun x => x < v) ->
    ForallT r (fun x => x > v) ->
    BST (Node v l r).

Theorem insertBST : forall (v : nat) (t : tree),
  BST t -> BST (insert t v).
Proof.
Admitted.

Fixpoint InT (t : tree) (v : nat) : Prop :=
  match t with
  | Nil => False
  | Node v' l r => v = v' \/ InT l v \/ InT r v
  end.

Theorem searchBST: forall (v : nat) (t : tree),
  BST t -> search t v = true <-> InT t v.
Proof.
Admitted.

(* -------------- AVL -------------- *)
Fixpoint height (t : tree) : nat :=
  match t with
  | Nil => 0
  | Node v l r => S (max (height l) (height r))
  end.

Inductive AVL :tree -> Prop :=
  | AVL_Empty: AVL Nil
  | AVL_Node_Eq (v : nat) (l r : tree): 
    AVL l ->
    AVL r ->
    height r = height l ->
    AVL (Node v l r)
  | AVL_Node_R (v : nat) (l r : tree): 
    AVL l ->
    AVL r ->
    height r = S (height l) ->
    AVL (Node v l r)
  | AVL_Node_L (v : nat) (l r : tree): 
    AVL l ->
    AVL r ->
    height l = S (height r) ->
    AVL (Node v l r).

Definition left_rotate (t: tree) : tree :=
  match t with
  | Node v1 l1 (Node v2 l2 r2) => Node v2 (Node v1 l1 l2) r2
  | _ => t
  end.

Theorem left_rotate_BST: forall (v: nat) (t : tree),
  BST t -> BST (left_rotate t).
Proof.
  intros v t. induction t as [| v' l' IHl' r' IHr'].
  - simpl. intros H. apply H.
  - intros H. destruct l' as [| v2' l2' r2'];
    destruct r' as [| v1' l1' r1']; simpl.
    + apply H.
    + apply BST_Node.
      * admit.
Admitted.

Definition right_rotate (t: tree) : tree :=
  match t with
  | Node v1 (Node v2 l2 r2) r1 => Node v2 l2 (Node v1 r2 r1)
  | _ => t
  end.

Theorem right_rotate_BST: forall (v: nat) (t : tree),
  BST t -> BST (right_rotate t).
Proof.
Admitted.

Inductive Diff : Type :=
  | Neutral
  | GoodLeft
  | GoodRight
  | BadLeft
  | BadRight
  | Impossible.

Definition diff (t : tree) : Diff :=
  match t with
  | Nil => Neutral
  | Node _ l r => let hl := height l in
                  let hr := height r in
                    if hl =? hr
                    then Neutral
                    else if hl =? (S hr)
                    then GoodLeft
                    else if (S hl) =? hr
                    then GoodRight
                    else if hl =? (S (S hr))
                    then BadLeft
                    else if (S (S hl)) =? hr
                    then BadRight
                    else Impossible
  end.


Definition eqb_diff (d1 d2 : Diff) : bool :=
  match d1, d2 with
  | Neutral, Neutral       => true
  | GoodLeft, GoodLeft     => true
  | GoodRight, GoodRight   => true
  | BadLeft, BadLeft       => true
  | BadRight, BadRight     => true
  | Impossible, Impossible => true
  | _, _                   => false
  end.

Lemma diff_Neutral : forall v l r,
  diff (Node v l r) = Neutral <-> height l = height r.
Proof.
  intros. split.
  - intros H. unfold diff in H.
    destruct (height l =? height r) eqn: E.
    apply Nat.eqb_eq; apply E.
    destruct (height l =? S (height r)). discriminate.
    destruct (S (height l) =? height r).  discriminate.
    destruct (height l =? S (S (height r))). discriminate.
    destruct (S (S (height l)) =? height r); discriminate.
  - intros H. apply Nat.eqb_eq in H. unfold diff. rewrite H. auto.
Qed.

Lemma diff_GoodLeft : forall v l r,
  diff (Node v l r) = GoodLeft <-> height l = S (height r).
Proof.
  intros. split.
  - intros H. unfold diff in H.
    destruct (height l =? height r). discriminate.
    destruct (height l =? S (height r)) eqn: E. 
    apply Nat.eqb_eq; apply E.
    destruct (S (height l) =? height r). discriminate.
    destruct (height l =? S (S (height r))). discriminate.
    destruct (S (S (height l)) =? height r); discriminate.
  - intros H. unfold diff.
    destruct (height l =? height r) eqn: E.
    apply Nat.eqb_eq in E. rewrite H in E. apply Nat.neq_succ_diag_l in E.
    inversion E.
    apply Nat.eqb_eq in H. rewrite H. auto.
Qed.

Lemma neq_succ_2_diag_l: forall n : nat,
  S (S n) <> n.
Proof.
  intros n H. induction n as [| n' IHn'].
  - discriminate.
  - apply Nat.succ_inj in H. apply IHn' in H. inversion H.
Qed.

Lemma diff_GoodRight : forall v l r,
  diff (Node v l r) = GoodRight <-> S (height l) = height r.
Proof.
  intros. split.
  - intros H. unfold diff in H.
    destruct (height l =? height r). discriminate.
    destruct (height l =? S (height r)). discriminate.
    destruct (S (height l) =? height r) eqn: E.
    apply Nat.eqb_eq; apply E.
    destruct (height l =? S (S (height r))). discriminate.
    destruct (S (S (height l)) =? height r); discriminate.
  - intros H. unfold diff.
    destruct (height l =? height r) eqn: E1.
    apply Nat.eqb_eq in E1. rewrite E1 in H.
    apply Nat.neq_succ_diag_l in H. inversion H.
    destruct (height l =? S (height r)) eqn: E2.
    apply Nat.eqb_eq in E2. rewrite E2 in H.
    apply neq_succ_2_diag_l in H. inversion H.
    apply Nat.eqb_eq in H. rewrite H. reflexivity.
Qed.

Lemma neq_succ_3_diag_l: forall n : nat,
  n <> S (S (S n)).
Proof.
  intros n H. induction n as [| n' IHn'].
  - discriminate.
  - apply Nat.succ_inj in H. apply IHn' in H. inversion H.
Qed.

Lemma diff_BadLeft : forall v l r,
  diff (Node v l r) = BadLeft <-> height l = S (S (height r)).
Proof.
  intros. split.
  - intros H. unfold diff in H.
    destruct (height l =? height r). discriminate.
    destruct (height l =? S (height r)). discriminate.
    destruct (S (height l) =? height r). discriminate.
    destruct (height l =? S (S (height r))) eqn: E.
    apply Nat.eqb_eq; apply E.
    destruct (S (S (height l)) =? height r); discriminate.
  - intros H. unfold diff.
    destruct (height l =? height r) eqn: E1.
    apply Nat.eqb_eq in E1. rewrite E1 in H.
    symmetry in H. apply neq_succ_2_diag_l in H. inversion H.
    destruct (height l =? S (height r)) eqn: E2.
    apply Nat.eqb_eq in E2. rewrite E2 in H.
    apply Nat.succ_inj in H. symmetry in H.
    apply Nat.neq_succ_diag_l in H. inversion H.
    destruct (S (height l) =? height r) eqn: E3.
    apply Nat.eqb_eq in E3. rewrite <- E3 in H.
    apply neq_succ_3_diag_l in H. inversion H.
    apply Nat.eqb_eq in H. rewrite H. reflexivity.
Qed.

Lemma neq_succ_4_diag_l: forall n : nat,
  S (S (S (S n))) <> n.
Proof.
  intros n H. induction n as [| n' IHn'].
  - discriminate.
  - apply Nat.succ_inj in H. apply IHn' in H. inversion H.
Qed.

Lemma diff_BadRight : forall v l r,
  diff (Node v l r) = BadRight <-> S (S (height l)) = height r.
Proof.
  intros. split.
  - intros H. unfold diff in H.
    destruct (height l =? height r). discriminate.
    destruct (height l =? S (height r)). discriminate.
    destruct (S (height l) =? height r). discriminate.
    destruct (height l =? S (S (height r))). discriminate.
    destruct (S (S (height l)) =? height r)  eqn: E.
    apply Nat.eqb_eq; apply E. inversion H.
  - intros H. unfold diff.
    destruct (height l =? height r) eqn: E1.
    apply Nat.eqb_eq in E1. rewrite E1 in H.
    apply neq_succ_2_diag_l in H. inversion H.
    destruct (height l =? S (height r)) eqn: E2.
    apply Nat.eqb_eq in E2. rewrite E2 in H.
    symmetry in H. apply neq_succ_3_diag_l in H. inversion H.
    destruct (S (height l) =? height r) eqn: E3.
    apply Nat.eqb_eq in E3. rewrite <- E3 in H.
    apply Nat.succ_inj in H. apply Nat.neq_succ_diag_l in H. inversion H.
    destruct (height l =? S (S (height r))) eqn: E4.
    apply Nat.eqb_eq in E4. rewrite E4 in H.
    apply neq_succ_4_diag_l in H. inversion H.
    apply Nat.eqb_eq in H. rewrite H. reflexivity.
Qed.
