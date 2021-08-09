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

Lemma ForallT_insert : forall (t : tree) (P : nat -> Prop) (v : nat),
  P v -> ForallT t P -> ForallT (insert t v) P.
Proof.
 intros t P v H1 H2. induction t as [| v' l IHr r IHl]; simpl.
 - repeat split. apply H1.
 - destruct (v <? v').
  + simpl. simpl in H2. destruct H2 as [H2 [H3 H4]]. repeat split.
    * apply H2.
    * apply IHr. apply H3.
    * apply H4.
  + destruct (v' <? v).
    * simpl. simpl in H2.
      destruct H2 as [H2 [H3 H4]]. repeat split; auto.
    * auto.
Qed.

Theorem insertBST : forall (v : nat) (t : tree),
  BST t -> BST (insert t v).
Proof.
  intros v t H. induction H as [| v' l r H1 IHl H2 IHr H3 H4].
  - simpl. constructor; try constructor.
  - simpl. destruct (v<? v') eqn: E1.
    + constructor; auto. apply ForallT_insert.
      * apply Nat.ltb_lt. apply E1.
      * auto.
    + destruct (v'<? v) eqn: E2.
      * constructor; auto. apply ForallT_insert.
        -- unfold gt. apply Nat.ltb_lt. apply E2.
        -- auto.
      * constructor; auto.
Qed.

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

Lemma ForallT_lt_trans : forall (n m : nat) (t : tree),
  n < m -> ForallT t (fun x : nat => x < n) -> ForallT t (fun x : nat => x < m).
Proof.
  intros n m t H1 H2. induction t as [| v l IHl r IHr];
  simpl; auto.
  repeat split.
  - simpl in H2. destruct H2 as [H2 H3].
    apply Nat.lt_trans with (m := n); auto.
  - apply IHl. simpl in H2. destruct H2 as [H2 [H3 H4]].
    auto.
  - apply IHr. simpl in H2. destruct H2 as [H2 [H3 H4]].
    auto.
Qed.

Theorem left_rotate_BST: forall (v: nat) (t : tree),
  BST t -> BST (left_rotate t).
Proof.
  intros v t H. inversion H; unfold left_rotate.
  - constructor.
  - destruct r as [| v' l' r'].
    + rewrite H4. apply H.
    + constructor.
      * inversion H1. constructor; auto.
        simpl in H3. destruct H3 as [H3 [H12 H13]].
        auto.
      * inversion H1; auto.
      * simpl in H3. destruct H3 as [H3 [H12 H13]].
        simpl. repeat split.
        -- auto.
        -- apply ForallT_lt_trans with (n := v0); auto.
        -- inversion H1. auto.
      * inversion H1. auto.
Qed.

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
  | Zero
  | One
  | MinusOne
  | Two
  | MinusTwo
  | Impossible.

Definition diff (t : tree) : Diff :=
  match t with
  | Nil => Zero
  | Node _ l r => let hl := height l in
                  let hr := height r in
                    if hl =? hr
                    then Zero
                    else if hl =? (S hr)
                    then One
                    else if (S hl) =? hr
                    then MinusOne
                    else if hl =? (S (S hr))
                    then Two
                    else if (S (S hl)) =? hr
                    then MinusTwo
                    else Impossible
  end.

Lemma diff_Zero : forall v l r,
  diff (Node v l r) = Zero <-> height l = height r.
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

Lemma diff_One : forall v l r,
  diff (Node v l r) = One <-> height l = S (height r).
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

Lemma diff_MinusOne : forall v l r,
  diff (Node v l r) = MinusOne <-> S (height l) = height r.
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

Lemma diff_Two : forall v l r,
  diff (Node v l r) = Two <-> height l = S (S (height r)).
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

Lemma diff_MinusTwo : forall v l r,
  diff (Node v l r) = MinusTwo <-> S (S (height l)) = height r.
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

(* ---------- insert AVL ----------*)
Definition rebalance_right (t : tree) : tree :=
  match t with
  | Nil => Nil
  | Node v l r => match diff l with
                  | MinusOne => right_rotate (Node v (left_rotate l) r)
                  | _ => right_rotate (Node v l r)
                  end
  end.

Definition rebalance_left (t : tree) : tree :=
  match t with
  | Nil => Nil
  | Node v l r => match diff r with
                  | One => left_rotate (Node v l (right_rotate r))
                  | _ => left_rotate (Node v l r)
                  end
  end.

Definition rebalance (t : tree) : tree :=
  match diff t with
  | Two => rebalance_right t
  | MinusTwo => rebalance_left t
  | _ => t
  end.

Fixpoint insertAVL (t : tree) (v: nat): tree :=
  match t with
  | Nil => Node v Nil Nil
  | Node v' l r => if v <? v'
                   then rebalance (Node v' (insertAVL l v) r)
                   else if v' <? v
                        then rebalance (Node v' l (insertAVL r v))
                        else t
  end.

Lemma max_Sn_n: forall (n: nat),
  max (S n) n = S n.
Proof.
  intros n. apply max_l. auto.
Qed.

Theorem insertAVL_AVL: forall (t : tree) (v : nat),
  AVL t -> AVL (insertAVL t v).
Proof.
  intros t v H. induction H.
    * simpl.  apply AVL_Node_Eq; try apply AVL_Empty.
      + simpl. reflexivity.
    * simpl. destruct (v <? v0).
      + unfold rebalance. destruct (diff (Node v0 (insertAVL l v) r)) eqn:EQ.
        -- apply diff_Zero in EQ. apply AVL_Node_Eq; auto.
        -- apply diff_One in EQ. apply AVL_Node_L; auto.
        -- apply diff_MinusOne in EQ. apply AVL_Node_R; auto.
        -- apply diff_Two in EQ. unfold rebalance_right. inversion IHAVL1.
           ++ rewrite <- H3 in EQ. discriminate.
           ++ Admitted.
           (*
           destruct (diff (insertAVL l v)) eqn:EQ2.
           ++ simpl. destruct (insertAVL l v).
              ** discriminate.
              ** simpl in EQ. apply diff_Zero in EQ2. rewrite EQ2 in EQ.
                 rewrite Nat.max_id in EQ. injection EQ as EQ. apply AVL_Node_R.
                 --- inversion IHAVL1; auto.
                 --- apply AVL_Node_L; auto. inversion IHAVL1; auto.
                 --- simpl. rewrite EQ. f_equal. rewrite EQ2. rewrite EQ.
                     apply max_Sn_n.
           ++ simpl. destruct (insertAVL l v).
              ** discriminate.
              ** simpl in EQ. apply diff_One in EQ2. rewrite EQ2 in EQ.
                 rewrite max_Sn_n in EQ. injection EQ as EQ. apply AVL_Node_L.
                 --- inversion IHAVL1; auto. *)

Theorem insertAVL_BST: forall (t : tree) (v : nat),
  BST t -> BST (insertAVL t v).
Proof.
Admitted.

Lemma insert_not_Nil : forall (t : tree) (v : nat),
  insert t v <> Nil.
Proof.
  intros t v. induction t as [| v' l IHl r IHr]; simpl;
  (try destruct (v <? v'));
  (try destruct (v' <? v));
  intros H; discriminate H.
(* resolução original (passo a passo):
  intros t v. induction t as [| v' l IHl r IHr]; simpl.
  - intros H. discriminate H.
  - destruct (v <? v').
    + intros H. discriminate H.
    + destruct (v' <? v).
      * intros H. discriminate H.
      * intros H. discriminate H.
*)
Qed.
