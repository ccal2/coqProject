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

Lemma insert_not_Nil : forall (t : tree) (v : nat),
  insert t v <> Nil.
Proof.
  intros t v. induction t as [| v' l IHl r IHr]; simpl;
  (try destruct (v <? v'));
  (try destruct (v' <? v));
  intros H; discriminate H.
Qed.

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

Lemma ForallT_InT: forall (t : tree) (v : nat) (P : nat -> Prop),
  ForallT t P -> InT t v -> P v.
Proof.
  intros t v P H H'. induction t as [| v' l IHl r IHr].
  - inversion H'.
  - simpl in H'. simpl in H. destruct H' as [H' | [H' | H']].
    + destruct H as [H _]. rewrite H'. apply H.
    + destruct H as [_ [H _]]. apply IHl; auto.
    + destruct H as [_ [_ H]]. apply IHr; auto.
Qed.

Theorem searchBST: forall (v : nat) (t : tree),
  BST t -> search t v = true <-> InT t v.
Proof.
  intros v t H. split; induction H as [| v1 l1 r1 H1 H3 H2 H4 IHl1 IHr1].
  - intros H. discriminate.
  - simpl. destruct (v <? v1) eqn: E1.
    + intros H. right. left. auto.
    + destruct (v1 <? v) eqn: E2.
      * intros H. right. right. auto.
      * intros H. left. clear H.
        apply Nat.ltb_ge in E1. apply Nat.ltb_ge in E2.
        apply Nat.le_antisymm; auto.
  - simpl. auto.
  - simpl. intros [H | [H | H]].
    + rewrite H. rewrite Nat.ltb_irrefl. reflexivity.
    + apply ForallT_InT with (v := v) in IHl1; auto.
      apply Nat.ltb_lt in IHl1. rewrite IHl1. apply H3. apply H.
    + apply ForallT_InT with (v := v) in IHr1; auto.
      unfold gt in IHr1. apply Nat.ltb_lt in IHr1. rewrite IHr1.
      apply Nat.ltb_lt in IHr1. apply Nat.lt_le_incl in IHr1.
      apply Nat.ltb_ge in IHr1. rewrite IHr1. apply H4. apply H.
Qed.

(* -------------- AVL -------------- *)
Fixpoint height (t : tree) : nat :=
  match t with
  | Nil => 0
  | Node v l r => S (max (height l) (height r))
  end.

(* BT = Balanced Tree *)
Inductive BT : tree -> Prop :=
  | BT_Empty: BT Nil
  | BT_Node_Eq (v : nat) (l r : tree): 
    BT l ->
    BT r ->
    height r = height l ->
    BT (Node v l r)
  | BT_Node_R (v : nat) (l r : tree): 
    BT l ->
    BT r ->
    height r = S (height l) ->
    BT (Node v l r)
  | BT_Node_L (v : nat) (l r : tree): 
    BT l ->
    BT r ->
    height l = S (height r) ->
    BT (Node v l r).

Definition AVL (t : tree) : Prop :=
  BST t /\ BT t.

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

Theorem left_rotate_BST: forall (t : tree),
  BST t -> BST (left_rotate t).
Proof.
  intros t H. inversion H; unfold left_rotate.
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
        -- apply ForallT_lt_trans with (n := v); auto.
        -- inversion H1. auto.
      * inversion H1. auto.
Qed.

Theorem ForallT_left_rotate: forall (P : nat -> Prop) (t : tree),
  ForallT t P ->
  ForallT (left_rotate t) P.
Proof.
  intros P t H. induction t as [| v1 l1 IHl1 r1 IHr1]; auto.
  unfold left_rotate. destruct r1 as [| l2 r2]; auto.
  simpl. simpl in H. destruct H as [H1 [H2 [H3 [H4 H5]]]].
  repeat split; auto.
Qed.

Definition right_rotate (t: tree) : tree :=
  match t with
  | Node v1 (Node v2 l2 r2) r1 => Node v2 l2 (Node v1 r2 r1)
  | _ => t
  end.

Lemma ForallT_gt_trans : forall (n m : nat) (t : tree),
  n > m -> ForallT t (fun x : nat => x > n) -> ForallT t (fun x : nat => x > m).
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

Theorem right_rotate_BST: forall (t : tree),
  BST t -> BST (right_rotate t).
Proof.
  intros t H. inversion H; unfold right_rotate.
  - constructor.
  - destruct l as [| v' l' r'].
    + rewrite H4. auto.
    + constructor.
      * inversion H0. auto.
      * constructor; auto.
        -- inversion H0. auto.
        -- simpl in H2. destruct H2 as [H2 [H5 H6]]. auto.
      * inversion H0. auto.
      * simpl. repeat split. 
        -- simpl in H2. destruct H2 as [H2 [H5 H6]]. auto.
        -- inversion H0. auto.
        -- simpl in H2. destruct H2 as [H2 [H5 H6]].
           apply ForallT_gt_trans with (n := v); auto.
Qed.

Theorem ForallT_right_rotate: forall (P : nat -> Prop) (t : tree),
  ForallT t P ->
  ForallT (right_rotate t) P.
Proof.
  intros P t H. induction t as [| v1 l1 IHl1 r1 IHr1]; auto.
  unfold right_rotate. destruct l1 as [| l2 r2]; auto.
  simpl. simpl in H. destruct H as [H1 [[H2 [H3 H4]] H5]].
  repeat split; auto.
Qed.

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

Theorem rebalance_right_BST: forall (t : tree),
  BST t -> BST (rebalance_right t).
Proof.
  intros t H. unfold rebalance_right. inversion H.
  - constructor.
  - destruct (diff l); apply right_rotate_BST; subst; auto.
    constructor; auto.
    + apply left_rotate_BST; auto.
    + destruct l as [| v1 l1 r1]; auto.
      simpl. destruct r1 as [| v2 l2 r2]; auto.
      inversion H. simpl in H9.
      destruct H9 as [H11 [H12 [H13 [H14]]]].
      simpl in H2. destruct H2 as [H15 [H16]].
      simpl. repeat split; assumption.
Qed.

Theorem ForallT_rebalance_right: forall (P : nat -> Prop) (t : tree),
  ForallT t P ->
  ForallT (rebalance_right t) P.
Proof.
  intros P t H. induction t as [| v1 l1 IHl1 r1 IHr1]; auto.
  unfold rebalance_right. destruct (diff l1);
  apply ForallT_right_rotate; auto.
  simpl. simpl in H. destruct H as [H1 [H2 H3]].
  repeat split; auto.
  apply ForallT_left_rotate. auto.
Qed.

Definition rebalance_left (t : tree) : tree :=
  match t with
  | Nil => Nil
  | Node v l r => match diff r with
                  | One => left_rotate (Node v l (right_rotate r))
                  | _ => left_rotate (Node v l r)
                  end
  end.

Theorem rebalance_left_BST: forall (t : tree),
  BST t -> BST (rebalance_left t).
Proof.
  intros t H. unfold rebalance_left. inversion H.
  - constructor.
  - destruct (diff r); apply left_rotate_BST; subst; auto.
    constructor; auto.
    + apply right_rotate_BST; auto.
    + unfold right_rotate. destruct r as [| v1 l1 r1];
      auto. destruct l1 as [| v2 l2 r2]; auto.
      simpl in H3. destruct H3 as [H5 [[H7 [H8]]]].
      simpl. repeat split; assumption.
Qed.

Theorem ForallT_rebalance_left: forall (P : nat -> Prop) (t : tree),
  ForallT t P ->
  ForallT (rebalance_left t) P.
Proof.
  intros P t H. induction t as [| v1 l1 IHl1 r1 IHr1]; auto.
  unfold rebalance_left. destruct (diff r1);
  apply ForallT_left_rotate; auto.
  simpl. simpl in H. destruct H as [H1 [H2 H3]].
  repeat split; auto.
  apply ForallT_right_rotate. auto.
Qed.

Definition rebalance (t : tree) : tree :=
  match diff t with
  | Two => rebalance_right t
  | MinusTwo => rebalance_left t
  | _ => t
  end.

Theorem rebalance_BST: forall (t : tree),
  BST t -> BST (rebalance t).
Proof.
  intros t H. unfold rebalance. inversion H.
  - constructor.
  - destruct (diff (Node v l r)); subst; auto.
    + apply rebalance_right_BST; auto.
    + apply rebalance_left_BST; auto.
Qed.

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

Lemma max_n_Sn: forall (n: nat),
  max n (S n) = S n.
Proof.
  intros n. rewrite Nat.max_comm. apply max_Sn_n.
Qed.

Lemma max_SSn_n: forall (n: nat),
  max (S (S n)) n = S ( S n).
Proof.
  intros n. induction n as [| n' IHn']; auto.
  simpl. destruct n'; auto.
Qed.

Lemma insertAVL_height: forall (t : tree) (v: nat),
  BT t ->
  height (insertAVL t v) = S (height t) \/ height (insertAVL t v) = height t.
Proof.
  intros. induction H as 
    [|
     v' l r BTl IHl BTr IHr EQlr |
     v' l r BTl IHl BTr IHr EQlr |
     v' l r BTl IHl BTr IHr EQlr ].
  - simpl. left. reflexivity.
  - simpl. destruct (v <? v').
    + unfold rebalance. destruct (diff (Node v' (insertAVL l v) r)) eqn:EQ;
      try (simpl; destruct IHl as [IHl | IHl]; [
        rewrite IHl; destruct (S (height l) <=? height r) eqn: EQ2; [
           apply Nat.leb_le in EQ2; right; f_equal; rewrite max_r; auto;
              symmetry; apply max_r; rewrite Nat.le_succ_l in EQ2;
              apply Nat.lt_le_incl in EQ2; apply EQ2 |
           rewrite Nat.leb_gt in EQ2; left; f_equal; rewrite max_l; [
              f_equal; unfold lt in EQ2; apply le_S_n in EQ2;
                 symmetry; apply max_l; apply EQ2 |
             apply Nat.lt_le_incl; apply EQ2 ]]|
        right; f_equal; rewrite IHl; reflexivity ]).
     * unfold rebalance_right. destruct (diff (insertAVL l v)) eqn:EQ2;
       try (unfold right_rotate; destruct (insertAVL l v); [
            simpl; apply diff_Two in EQ; simpl in EQ; discriminate |
            simpl; apply diff_Two in EQ; simpl in EQ; injection EQ as EQ;
              destruct IHl; [
              simpl in H; injection H as H; rewrite <- H; rewrite EQ;
                 rewrite max_Sn_n;
                 pose proof (Nat.max_spec (height t2) (height t1)) as H1;
                 destruct H1 as [ [H1 H2] | [H1 H2]]; [
                  rewrite Nat.max_comm in H2; rewrite H2 in EQ; rewrite EQ;
                     simpl; rewrite Nat.max_assoc; right; f_equal; f_equal;
                     apply max_r; rewrite max_l; auto; rewrite EQ in H1; unfold lt in H1;
                     apply le_S_n; auto |
                  rewrite Nat.max_comm in H2; rewrite H2 in EQ; rewrite EQ;
                     rewrite max_Sn_n; left; f_equal; apply max_r; rewrite EQ in H1; auto ] |
              simpl in H; rewrite EQ in H; rewrite EQlr in H; apply neq_succ_2_diag_l in H;
                 inversion H ]]).
        unfold right_rotate. destruct (insertAVL l v) eqn:EQ3.
        -- simpl. rewrite EQlr. right. f_equal. rewrite Nat.max_id. reflexivity.
        -- unfold left_rotate. destruct t2 eqn:EQ4.
           ++ simpl. apply diff_MinusOne in EQ2. discriminate.
           ++ simpl. apply diff_MinusOne in EQ2. simpl in EQ2. injection EQ2 as EQ2.
              apply diff_Two in EQ. simpl in EQ. injection EQ as EQ. rewrite EQ2 in EQ.
              rewrite Nat.max_comm in EQ. rewrite max_Sn_n in EQ. injection EQ as EQ.
              assert (H: max (height t1) (height t3) = max (height t3) (height t4)).
              { rewrite Nat.max_comm. rewrite EQ2. rewrite Nat.max_assoc.
                rewrite Nat.max_id. reflexivity. }
              rewrite H. clear H.
              assert (H: max (height t4) (height r) = max (height t3) (height t4)).
              { rewrite Nat.max_comm. rewrite <- EQ. rewrite <- Nat.max_assoc.
                rewrite Nat.max_id. reflexivity. }
              rewrite H. rewrite Nat.max_id. rewrite EQ. rewrite EQlr.
              left. rewrite Nat.max_id. reflexivity.
      * apply diff_MinusTwo in EQ. destruct IHl.
        -- rewrite <- EQlr in H. rewrite H in EQ. symmetry in EQ.
           apply neq_succ_3_diag_l in EQ. inversion EQ.
        -- rewrite <- EQlr in H. rewrite H in EQ.
           apply neq_succ_2_diag_l in EQ. inversion EQ.
    +  destruct (v' <? v).
       * unfold rebalance. destruct (diff (Node v' l (insertAVL r v))) eqn:EQ;
         try ( simpl; destruct IHr as [IHr | IHr]; [
            rewrite IHr; rewrite EQlr; left; rewrite Nat.max_id; rewrite Nat.max_comm;
            rewrite max_Sn_n; reflexivity |
            rewrite IHr; rewrite EQlr; right; reflexivity ]).
         -- apply diff_Two in EQ.  destruct IHr. 
            ++ rewrite EQlr in H. rewrite H in EQ.
               apply neq_succ_3_diag_l in EQ. inversion EQ.
            ++ rewrite EQlr in H. rewrite H in EQ. symmetry in EQ.
               apply neq_succ_2_diag_l in EQ. inversion EQ. 
         -- apply diff_MinusTwo in EQ. destruct IHr.
            ++ rewrite EQlr in H. rewrite H in EQ. apply Nat.neq_succ_diag_l in EQ.
               inversion EQ.
            ++ rewrite EQlr in H. rewrite H in EQ. apply neq_succ_2_diag_l in EQ.
               inversion EQ.
       * simpl. right. reflexivity.
  - simpl. destruct (v <? v').
    + unfold rebalance. destruct (diff (Node v' (insertAVL l v) r)) eqn:EQ;
      try (simpl; destruct IHl as [IHl | IHl]; [
        rewrite IHl; destruct (S (height l) <=? height r) eqn: EQ2; [
           apply Nat.leb_le in EQ2; right; f_equal; rewrite max_r; auto;
              symmetry; apply max_r; rewrite Nat.le_succ_l in EQ2;
              apply Nat.lt_le_incl in EQ2; apply EQ2 |
           rewrite Nat.leb_gt in EQ2; left; f_equal; rewrite max_l; [
              f_equal; unfold lt in EQ2; apply le_S_n in EQ2;
                 symmetry; apply max_l; apply EQ2 |
             apply Nat.lt_le_incl; apply EQ2 ]]|
        right; f_equal; rewrite IHl; reflexivity ]).
     * unfold rebalance_right. destruct (diff (insertAVL l v)) eqn:EQ2;
        try (unfold right_rotate; destruct (insertAVL l v); [
            simpl; apply diff_Two in EQ; simpl in EQ; discriminate |
            simpl; apply diff_Two in EQ; simpl in EQ; injection EQ as EQ;
              destruct IHl; [
              simpl in H; injection H as H; rewrite <- H; rewrite EQ;
                 rewrite max_Sn_n;
                 pose proof (Nat.max_spec (height t2) (height t1)) as H1;
                 destruct H1 as [ [H1 H2] | [H1 H2]]; [
                  rewrite Nat.max_comm in H2; rewrite H2 in EQ; rewrite EQ;
                     simpl; rewrite Nat.max_assoc; right; f_equal; f_equal;
                     apply max_r; rewrite max_l; auto; rewrite EQ in H1; unfold lt in H1;
                     apply le_S_n; auto |
                  rewrite Nat.max_comm in H2; rewrite H2 in EQ; rewrite EQ;
                     rewrite max_Sn_n; left; f_equal; apply max_r; rewrite EQ in H1; auto ] |
            simpl in H; rewrite EQ in H; rewrite EQlr in H; symmetry in H; apply neq_succ_3_diag_l in H;
                 inversion H]]).
        unfold right_rotate. destruct (insertAVL l v) eqn:EQ3.
        -- simpl. rewrite EQlr. right. f_equal. rewrite Nat.max_comm. rewrite max_Sn_n.
           reflexivity.
        -- unfold left_rotate. destruct t2 eqn:EQ4.
           ++ simpl. apply diff_MinusOne in EQ2. discriminate.
           ++ simpl. apply diff_MinusOne in EQ2. simpl in EQ2. injection EQ2 as EQ2.
              apply diff_Two in EQ. simpl in EQ. injection EQ as EQ. rewrite EQ2 in EQ.
              rewrite Nat.max_comm in EQ. rewrite max_Sn_n in EQ. injection EQ as EQ.
              assert (H: max (height t1) (height t3) = max (height t3) (height t4)).
              { rewrite Nat.max_comm. rewrite EQ2. rewrite Nat.max_assoc.
                rewrite Nat.max_id. reflexivity. }
              rewrite H. clear H.
              assert (H: max (height t4) (height r) = max (height t3) (height t4)).
              { rewrite Nat.max_comm. rewrite <- EQ. rewrite <- Nat.max_assoc.
                rewrite Nat.max_id. reflexivity. }
              rewrite H. rewrite Nat.max_id. rewrite EQ. rewrite EQlr.
              left. rewrite Nat.max_comm. rewrite max_Sn_n. reflexivity.
      * apply diff_MinusTwo in EQ. destruct IHl.
        -- rewrite <- EQlr in H. rewrite H in EQ.
           apply neq_succ_2_diag_l in EQ. inversion EQ.
        -- rewrite EQlr in EQ. rewrite H in EQ.
           apply Nat.neq_succ_diag_l in EQ. inversion EQ.
    +  destruct (v' <? v).
       * unfold rebalance. destruct (diff (Node v' l (insertAVL r v))) eqn:EQ;
         try (simpl; destruct IHr as [IHr | IHr]; [
             rewrite IHr; rewrite EQlr; left; rewrite Nat.max_comm;
             rewrite max_SSn_n; rewrite Nat.max_comm;
            rewrite max_Sn_n; reflexivity |
            rewrite IHr; rewrite EQlr; right; reflexivity ]).
         -- apply diff_Two in EQ.  destruct IHr. 
            ++ rewrite EQlr in H. rewrite H in EQ. symmetry in EQ.
               apply neq_succ_4_diag_l in EQ. inversion EQ.
            ++ rewrite EQlr in H. rewrite H in EQ.
               apply neq_succ_3_diag_l in EQ. inversion EQ. 
         -- apply diff_MinusTwo in EQ. destruct IHr.
            ++ unfold rebalance_left. Arguments max: simpl never.
               destruct ( diff (insertAVL r v)) eqn:EQ2;
               try (unfold left_rotate; destruct (insertAVL r v); [ discriminate |
                    simpl in EQ; injection EQ as EQ;
                      simpl in H; injection H as H; simpl;
                      pose proof (Nat.max_spec (height t1) (height t2)) as H1;
                 destruct H1 as [ [H1 H2] | [H1 H2]]; [
                   rewrite H2 in EQ; rewrite <- EQ;
                     rewrite <- EQ in H1; unfold lt in H1; apply le_S_n in H1; right;
                     rewrite EQlr; rewrite max_n_Sn; f_equal; apply max_r; rewrite max_l; auto |
                   rewrite H2 in EQ; rewrite <- EQ;
                     rewrite max_n_Sn; left; f_equal; f_equal; rewrite EQlr; rewrite max_n_Sn;
                     apply max_l; rewrite <- EQ in H1; auto ]]).
                unfold left_rotate. destruct (insertAVL r v) eqn: EQ3.
                ** inversion EQ2.
                ** apply diff_One in EQ2. unfold right_rotate. destruct t1.
                   --- discriminate.
                   --- simpl in EQ2. simpl in EQ. rewrite EQ2 in EQ. rewrite max_Sn_n in EQ.
                       injection EQ as EQ. simpl in H. injection H as H. rewrite EQ2 in H.
                       rewrite max_Sn_n in H. injection EQ2 as EQ2.
                       Arguments max : simpl nomatch. simpl.
                       assert (H': max (height l) (height t1_1) = height l).
                       { rewrite  EQ. rewrite <- Nat.max_comm in EQ2.  rewrite <- EQ2.
                         rewrite <- Nat.max_assoc. rewrite Nat.max_id. reflexivity. }
                       rewrite H'. clear H'.
                       assert (H': max (height t1_2) (height t2) = height l).
                       { rewrite Nat.max_comm. rewrite <- EQ2. rewrite <- Nat.max_assoc.
                         rewrite Nat.max_id. rewrite <- EQ in EQ2. apply EQ2. }
                       rewrite H'. rewrite EQlr. right. rewrite Nat.max_id. rewrite max_n_Sn.
                       reflexivity.
            ++ rewrite EQlr in H. rewrite H in EQ.
               apply Nat.neq_succ_diag_l in EQ. inversion EQ.
       * simpl. right. reflexivity.
  - simpl. destruct (v <? v').
    + unfold rebalance. destruct (diff (Node v' (insertAVL l v) r)) eqn:EQ;
      try (simpl; destruct IHl as [IHl | IHl]; [
        rewrite IHl; destruct (S (height l) <=? height r) eqn: EQ2; [
           apply Nat.leb_le in EQ2; right; f_equal; rewrite max_r; auto;
              symmetry; apply max_r; rewrite Nat.le_succ_l in EQ2;
              apply Nat.lt_le_incl in EQ2; apply EQ2 |
           rewrite Nat.leb_gt in EQ2; left; f_equal; rewrite max_l; [
              f_equal; unfold lt in EQ2; apply le_S_n in EQ2;
                 symmetry; apply max_l; apply EQ2 |
             apply Nat.lt_le_incl; apply EQ2 ]]|
        right; f_equal; rewrite IHl; reflexivity ]).
     * unfold rebalance_right. destruct (diff (insertAVL l v)) eqn:EQ2;
        try (unfold right_rotate; destruct (insertAVL l v); [
            simpl; apply diff_Two in EQ; simpl in EQ; discriminate |
            simpl; apply diff_Two in EQ; simpl in EQ; injection EQ as EQ;
              destruct IHl; [
              simpl in H; injection H as H; rewrite <- H; rewrite EQ;
                 rewrite max_Sn_n;
                 pose proof (Nat.max_spec (height t2) (height t1)) as H1;
                 destruct H1 as [ [H1 H2] | [H1 H2]]; [
                  rewrite Nat.max_comm in H2; rewrite H2 in EQ; rewrite EQ;
                     simpl; rewrite Nat.max_assoc; right; f_equal; f_equal;
                     apply max_r; rewrite max_l; auto; rewrite EQ in H1; unfold lt in H1;
                     apply le_S_n; auto |
                  rewrite Nat.max_comm in H2; rewrite H2 in EQ; rewrite EQ;
                     rewrite max_Sn_n; left; f_equal; apply max_r; rewrite EQ in H1; auto ] |
            simpl in H; rewrite EQ in H; rewrite EQlr in H; apply Nat.neq_succ_diag_l in H;
                 inversion H]]).
        unfold right_rotate. destruct (insertAVL l v) eqn:EQ3.
        -- simpl. rewrite EQlr. inversion EQ2.
        -- unfold left_rotate. destruct t2 eqn:EQ4.
           ++ simpl. apply diff_MinusOne in EQ2. discriminate.
           ++ simpl. apply diff_MinusOne in EQ2. simpl in EQ2. injection EQ2 as EQ2.
              apply diff_Two in EQ. simpl in EQ. injection EQ as EQ. rewrite EQ2 in EQ.
              rewrite Nat.max_comm in EQ. rewrite max_Sn_n in EQ. injection EQ as EQ.
              assert (H: max (height t1) (height t3) = max (height t3) (height t4)).
              { rewrite Nat.max_comm. rewrite EQ2. rewrite Nat.max_assoc.
                rewrite Nat.max_id. reflexivity. }
              rewrite H. clear H.
              assert (H: max (height t4) (height r) = max (height t3) (height t4)).
              { rewrite Nat.max_comm. rewrite <- EQ. rewrite <- Nat.max_assoc.
                rewrite Nat.max_id. reflexivity. }
              rewrite H. rewrite Nat.max_id. rewrite EQ. rewrite EQlr.
              right. rewrite max_Sn_n. reflexivity.
      * apply diff_MinusTwo in EQ. destruct IHl.
        -- rewrite EQlr in H. rewrite H in EQ.
           apply neq_succ_4_diag_l in EQ. inversion EQ.
        -- rewrite EQlr in H. rewrite H in EQ. symmetry in EQ.
           apply neq_succ_3_diag_l in EQ. inversion EQ.
    +  destruct (v' <? v).
       * unfold rebalance. destruct (diff (Node v' l (insertAVL r v))) eqn:EQ;
         try (simpl; destruct IHr as [IHr | IHr]; [
             rewrite IHr; rewrite EQlr; right; rewrite Nat.max_id;
            rewrite max_Sn_n; reflexivity |
             rewrite IHr; rewrite EQlr; right; reflexivity]).
         -- apply diff_Two in EQ.  destruct IHr. 
            ++ rewrite <- EQlr in H. rewrite H in EQ. symmetry in EQ.
               apply neq_succ_2_diag_l in EQ. inversion EQ.
            ++ rewrite EQlr in EQ. rewrite H in EQ. symmetry in EQ.
               apply Nat.neq_succ_diag_l in EQ. inversion EQ. 
         -- apply diff_MinusTwo in EQ. destruct IHr.
            ++ rewrite <- EQlr in H. rewrite H in EQ. apply neq_succ_2_diag_l in EQ.
               inversion EQ.
            ++ rewrite EQlr in EQ. rewrite H in EQ. symmetry in EQ.
               apply neq_succ_3_diag_l in EQ. inversion EQ.
       * simpl. right. reflexivity.
Qed.

Lemma rebalance_right_BT: forall (l r : tree) (v : nat),
  BT l -> BT r -> height l = S (S (height r)) ->
  BT (rebalance_right (Node v l r)).
Proof.
  intros. unfold rebalance_right. destruct l; try discriminate.
  inversion H.
  - symmetry in H7. apply diff_Zero with (v:= v0) in H7. rewrite H7.
    unfold right_rotate. apply diff_Zero in H7. simpl in H1. injection H1 as H1.
    rewrite H7 in H1. rewrite Nat.max_id in H1. apply BT_Node_R.
    + auto.
    + apply BT_Node_L; auto.
    + simpl. rewrite H1. rewrite max_Sn_n. f_equal.
      rewrite H7. rewrite H1. reflexivity.
  - symmetry in H7. apply diff_MinusOne with (v:= v0) in H7. rewrite H7.
    unfold right_rotate. unfold left_rotate. destruct l2.
    + apply diff_MinusOne in H7. discriminate.
    + apply diff_MinusOne in H7. simpl in H7. simpl in H1.
      rewrite <- H7 in H1. rewrite max_n_Sn in H1. injection H1 as H1.
      injection H7 as H7. inversion H6.
      * rewrite H13 in H7. rewrite Nat.max_id in H7. apply BT_Node_Eq.
        -- apply BT_Node_Eq; auto.
        -- apply BT_Node_Eq; auto. rewrite <- H13 in H7. rewrite H7 in H1.
           symmetry in H1. apply H1.
        -- simpl. rewrite <- H1. rewrite H7. rewrite Nat.max_id. rewrite <- H13.
           rewrite Nat.max_id. auto.
      * rewrite H13 in H7. rewrite max_n_Sn in H7. apply BT_Node_Eq.
        -- apply BT_Node_L; auto.
        -- apply BT_Node_Eq; auto. rewrite <- H13 in H7. rewrite H7 in H1.
           symmetry in H1. apply H1.
        -- simpl. rewrite <- H1. rewrite H7. rewrite H13. rewrite Nat.max_id.
           rewrite max_Sn_n. auto.
      * rewrite H13 in H7. rewrite max_Sn_n in H7. apply BT_Node_Eq.
        -- apply BT_Node_Eq; auto. rewrite H7. apply H13.
        -- apply BT_Node_R; auto. rewrite <- H7. symmetry. apply H1.
        -- simpl. rewrite <- H1. rewrite H7. rewrite H13. rewrite Nat.max_id.
           rewrite max_n_Sn. reflexivity.
  - apply diff_One with (v:= v0) in H7. rewrite H7.
    apply diff_One in H7. simpl in H1. injection H1 as H1. unfold right_rotate.
    rewrite H7 in H1. rewrite max_Sn_n in H1. injection H1 as H1. apply BT_Node_Eq.
    + auto.
    + apply BT_Node_Eq; auto.
    + simpl. rewrite H1. rewrite Nat.max_id.
      rewrite H7. rewrite H1. reflexivity.
Qed.

Lemma rebalance_left_BT: forall (l r : tree) (v : nat),
  BT l -> BT r -> S (S (height l)) = height r ->
  BT (rebalance_left (Node v l r)).
Proof.
  intros. unfold rebalance_left. destruct r; try discriminate.
  inversion H0.
  - symmetry in H7. apply diff_Zero with (v:= v0) in H7. rewrite H7.
    unfold left_rotate. apply diff_Zero in H7. simpl in H1. rewrite H7 in H1.
    rewrite Nat.max_id in H1. injection H1 as H1. apply BT_Node_L.
    + rewrite <- H1 in H7. apply BT_Node_R; auto.
    + auto.
    + simpl. f_equal. rewrite H7. rewrite <- H1. rewrite max_n_Sn. reflexivity.
  - symmetry in H7. apply diff_MinusOne with (v:= v0) in H7. rewrite H7.
    unfold left_rotate. apply diff_MinusOne in H7. simpl in H1.
    rewrite <- H7 in H1. rewrite max_n_Sn in H1. injection H1 as H1.
    apply BT_Node_Eq.
    + apply BT_Node_Eq; auto.
    + auto.
    + simpl. rewrite H1. rewrite Nat.max_id. symmetry. apply H7.
  - apply diff_One with (v:= v0) in H7. rewrite H7.
    unfold left_rotate. unfold right_rotate. destruct r1.
    + apply diff_One in H7. discriminate.
    + apply diff_One in H7.  simpl in H1. simpl in H7. injection H7 as H7.
      rewrite H7 in H1. rewrite max_Sn_n in H1. injection H1 as H1. inversion H5.
      * rewrite H13 in H7.
        rewrite Nat.max_id in H7. apply BT_Node_Eq.
        -- rewrite <- H7 in H1. apply BT_Node_Eq; auto.
        -- rewrite <- H13 in H7. apply BT_Node_Eq; auto.
        -- simpl. rewrite H1. rewrite <- H7. rewrite H13. reflexivity.
      * rewrite H13 in H7.
        rewrite max_n_Sn in H7. apply BT_Node_Eq.
        -- rewrite <- H7 in H1. apply BT_Node_L; auto.
        -- rewrite H7 in H13. apply BT_Node_Eq; auto.
        -- simpl. rewrite H1. rewrite <- H7. rewrite H13.
           rewrite Nat.max_id. rewrite max_Sn_n. reflexivity.
      * rewrite H13 in H7. rewrite max_Sn_n in H7. apply BT_Node_Eq.
        -- rewrite <- H13 in H7. rewrite  <- H7 in H1. apply BT_Node_Eq; auto.
        -- apply BT_Node_R; auto.
        -- simpl. rewrite H1. rewrite <- H7. rewrite H13. rewrite Nat.max_id.
           f_equal. apply max_n_Sn.
Qed.

Theorem insertAVL_BT: forall (t : tree) (v : nat),
  BT t -> BT (insertAVL t v).
Proof.
  intros t v H. induction H.
  - simpl.  apply BT_Node_Eq; try apply BT_Empty. reflexivity.
  - simpl. destruct (v <? v0).
    + unfold rebalance. destruct (diff (Node v0 (insertAVL l v) r)) eqn:EQ.
        -- apply diff_Zero in EQ. apply BT_Node_Eq; auto.
        -- apply diff_One in EQ. apply BT_Node_L; auto.
        -- apply diff_MinusOne in EQ. apply BT_Node_R; auto.
        --  apply diff_Two in EQ. apply rebalance_right_BT; auto.
        -- apply diff_MinusTwo in EQ. apply rebalance_left_BT; auto.
        -- apply (insertAVL_height l v) in H. destruct H.
           ++ rewrite <- H1 in H. apply diff_One with (v := v0) in H.
              rewrite H in EQ. discriminate.
           ++ rewrite <- H1 in H. apply diff_Zero with (v := v0) in H.
              rewrite H in EQ. discriminate.
    + destruct (v0 <? v).
      * unfold rebalance. destruct (diff (Node v0 l (insertAVL r v))) eqn:EQ.
        -- apply diff_Zero in EQ. apply BT_Node_Eq; auto.
        -- apply diff_One in EQ. apply BT_Node_L; auto.
        -- apply diff_MinusOne in EQ. apply BT_Node_R; auto.
        -- apply diff_Two in EQ. apply rebalance_right_BT; auto.
        -- apply diff_MinusTwo in EQ. apply rebalance_left_BT; auto.
        -- apply (insertAVL_height r v) in H0. destruct H0.
           ++ rewrite H1 in H0. symmetry in H0. apply diff_MinusOne with (v := v0) in H0.
              rewrite H0 in EQ. discriminate.
           ++ rewrite H1 in H0. symmetry in H0. apply diff_Zero with (v := v0) in H0.
              rewrite H0 in EQ. discriminate.
     * apply BT_Node_Eq; auto.
  - simpl. destruct (v <? v0).
    + unfold rebalance. destruct (diff (Node v0 (insertAVL l v) r)) eqn:EQ.
        -- apply diff_Zero in EQ. apply BT_Node_Eq; auto.
        -- apply diff_One in EQ. apply BT_Node_L; auto.
        -- apply diff_MinusOne in EQ. apply BT_Node_R; auto.
        --  apply diff_Two in EQ. apply rebalance_right_BT; auto.
        -- apply diff_MinusTwo in EQ. apply rebalance_left_BT; auto.
        -- apply (insertAVL_height l v) in H. destruct H.
           ++ rewrite <- H1 in H. apply diff_Zero with (v := v0) in H.
              rewrite H in EQ. discriminate.
           ++ rewrite <- H in H1. symmetry in H1. apply diff_MinusOne with (v := v0) in H1.
              rewrite H1 in EQ. discriminate.
    + destruct (v0 <? v).
      * unfold rebalance. destruct (diff (Node v0 l (insertAVL r v))) eqn:EQ.
        -- apply diff_Zero in EQ. apply BT_Node_Eq; auto.
        -- apply diff_One in EQ. apply BT_Node_L; auto.
        -- apply diff_MinusOne in EQ. apply BT_Node_R; auto.
        -- apply diff_Two in EQ. apply rebalance_right_BT; auto.
        -- apply diff_MinusTwo in EQ. apply rebalance_left_BT; auto.
        -- apply (insertAVL_height r v) in H0. destruct H0.
           ++ rewrite H1 in H0. symmetry in H0. apply diff_MinusTwo with (v := v0) in H0.
              rewrite H0 in EQ. discriminate.
           ++ rewrite H1 in H0. symmetry in H0. apply diff_MinusOne with (v := v0) in H0.
              rewrite H0 in EQ. discriminate.
     * apply BT_Node_R; auto.
  - simpl. destruct (v <? v0).
    + unfold rebalance. destruct (diff (Node v0 (insertAVL l v) r)) eqn:EQ.
        -- apply diff_Zero in EQ. apply BT_Node_Eq; auto.
        -- apply diff_One in EQ. apply BT_Node_L; auto.
        -- apply diff_MinusOne in EQ. apply BT_Node_R; auto.
        --  apply diff_Two in EQ. apply rebalance_right_BT; auto.
        -- apply diff_MinusTwo in EQ. apply rebalance_left_BT; auto.
        -- apply (insertAVL_height l v) in H. destruct H.
           ++ rewrite H1 in H. apply diff_Two with (v := v0) in H.
              rewrite H in EQ. discriminate.
           ++ rewrite H1 in H. apply diff_One with (v := v0) in H.
              rewrite H in EQ. discriminate.
    + destruct (v0 <? v).
      * unfold rebalance. destruct (diff (Node v0 l (insertAVL r v))) eqn:EQ.
        -- apply diff_Zero in EQ. apply BT_Node_Eq; auto.
        -- apply diff_One in EQ. apply BT_Node_L; auto.
        -- apply diff_MinusOne in EQ. apply BT_Node_R; auto.
        -- apply diff_Two in EQ. apply rebalance_right_BT; auto.
        -- apply diff_MinusTwo in EQ. apply rebalance_left_BT; auto.
        -- apply (insertAVL_height r v) in H0. destruct H0.
           ++ rewrite <- H1 in H0. symmetry in H0. apply diff_Zero with (v := v0) in H0.
              rewrite H0 in EQ. discriminate.
           ++ rewrite <- H0 in H1. apply diff_One with (v := v0) in H1.
              rewrite H1 in EQ. discriminate.
     * apply BT_Node_L; auto.
Qed.

Ltac match_contradiction exp :=
  try destruct exp; try contradiction; try (repeat (intros H; discriminate H)).

Lemma insertAVL_not_Nil: forall (t : tree) (v : nat),
  insertAVL t v <> Nil.
Proof.
  intros t v. induction t as [| v' l IHl r IHr]; simpl.
  - intros H. discriminate H.
  - destruct (v <? v').
    + unfold rebalance. match_contradiction (diff (Node v' (insertAVL l v) r)).
      * unfold rebalance_right. destruct (diff (insertAVL l v));
        unfold right_rotate; try match_contradiction (insertAVL l v);
        try match_contradiction (left_rotate (Node v0 t1 t2)).
      * unfold rebalance_left. destruct (diff r);
        unfold left_rotate; try match_contradiction r;
        try match_contradiction (right_rotate (Node v0 r1 r2)).
    + destruct (v' <? v); try (intros H; discriminate H).
      unfold rebalance. destruct (diff (Node v' (insertAVL l v) r));
      try match_contradiction (diff (Node v' l (insertAVL r v)));
      unfold rebalance_right; try match_contradiction (diff l);
      unfold right_rotate; try match_contradiction l;
      try match_contradiction (left_rotate (Node v0 l1 l2));
      unfold rebalance_left; try match_contradiction (diff (insertAVL r v));
      unfold left_rotate; try match_contradiction (insertAVL r v);
      try match_contradiction (right_rotate (Node v0 t1 t2));
      try match_contradiction (right_rotate (Node v1 t1 t2));
      try match_contradiction (right_rotate (Node v2 t3 t4)).
Qed.

Theorem ForallT_rebalance: forall (P : nat -> Prop) (t : tree),
  ForallT t P ->
  ForallT (rebalance t) P.
Proof.
  intros P t H1. induction t as [| v1 l1 IHl1 r1 IHr1]; auto.
  unfold rebalance. destruct (diff (Node v1 l1 r1)); auto.
  - apply ForallT_rebalance_right. auto.
  - apply ForallT_rebalance_left. auto.
Qed.

Theorem ForallT_insertAVL: forall (P : nat -> Prop) (t : tree) (v: nat),
  P v ->
  ForallT t P ->
  ForallT (insertAVL t v) P.
Proof.
  intros P t v H1 H2. induction t as [| v1 l1 IHl1 r1 IHr1]; simpl.
  - repeat split; auto.
  - simpl in H2. destruct H2 as [H2 [H3 H4]].
    destruct (v <? v1).
    + apply ForallT_rebalance. simpl.
      repeat split; auto.
    + destruct (v1 <? v).
      * apply ForallT_rebalance. simpl.
        repeat split; auto.
      * simpl. repeat split; auto.
Qed.

Lemma ltb_symm: forall (n m : nat),
  (n < m) -> (m > n).
Proof.
  intros n m H. induction n as [| n'];
  destruct m as [| m']; auto.
Qed.

Theorem insertAVL_BST: forall (t : tree) (v : nat),
  BST t -> BST (insertAVL t v).
Proof.
  intros t v H. induction H as [| v1 l1 r1 H1 IHl1 H2 IHr1 H3 H4]; simpl.
  - repeat constructor.
  - destruct (v <? v1) eqn: Ev1.
    + apply rebalance_BST. constructor; auto.
      apply ForallT_insertAVL; auto.
      apply Nat.ltb_lt in Ev1. auto.
    + destruct (v1 <? v) eqn: Ev2.
      * apply rebalance_BST. constructor; auto.
        apply ForallT_insertAVL; auto.
        apply Nat.ltb_lt in Ev2. apply ltb_symm in Ev2. auto.
      * constructor; auto.
Qed.

Theorem insertAVL_AVL:  forall (t : tree) (v : nat),
  AVL t -> AVL (insertAVL t v).
Proof.
  unfold AVL. intros. destruct H. split.
  - apply insertAVL_BST. apply H.
  - apply insertAVL_BT. apply H0.
Qed.
