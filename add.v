Require Import def.

Lemma add_0_r : forall x : nat, x + O = x.
Proof.
 induction x as [| x IHx].
 - reflexivity.
 - simpl.
   rewrite IHx.
   reflexivity.
Qed.

Lemma add_0_l : forall x : nat, O + x = x.
Proof.
 intros x.
 reflexivity.
Qed.

Lemma add_succ_l : forall x y : nat, S x + y = S (x + y).
Proof.
 intros x y.
 reflexivity.
Qed.

Lemma add_succ_r : forall x y : nat, x + S y = S (x + y).
Proof.
 intros x.
 induction x as [| x IHx].
 - intros y.
   reflexivity.
 - intros y.
   simpl.
   rewrite IHx.
   reflexivity.
Qed.

Lemma add_comm : forall x y : nat, x + y = y + x.
Proof.
 intros x.
 induction x as [| x IHx].
 - intros y.
   simpl.
   rewrite add_0_r.
   reflexivity.
 - intros y.
   simpl.
   rewrite IHx.
   rewrite add_succ_r.
   reflexivity.
Qed.

Lemma add_assoc : forall x y z : nat, x + (y + z) = (x + y) + z.
Proof.
 intros x.
 induction x as [| x IHx].
 - intros y z.
   reflexivity.
 - intros y z.
   simpl.
   rewrite IHx.
   reflexivity.
Qed.

Lemma add_succ_succ : forall x y : nat, S x + S y = S (S (x + y)).
Proof.
 intros x y.
 rewrite add_succ_l.
 rewrite add_succ_r.
 reflexivity.
Qed.

Lemma add_cancel_l : forall x y z : nat, x + y = x + z -> y = z.
Proof.
 intros x.
 induction x as [| x IHx].
 - intros y z H.
   simpl in H.
   exact H.
 - intros y z H.
   simpl in H.
   injection H as Hxz.
   apply IHx.
   exact Hxz.
Qed.

Lemma add_cancel_r : forall x y z : nat, x + z = y + z -> x = y.
Proof.
 intros x y z H.
 rewrite <- (add_comm z x) in H.
 rewrite <- (add_comm z y) in H.
 apply (add_cancel_l z x y).
 exact H.
Qed.

Lemma add_eq_O : forall x y : nat, x + y = O -> x = O /\ y = O.
Proof.
 intros x.
 induction x as [| x IHx].
 - intros y H.
   simpl in H.
   split.
   + reflexivity.
   + exact H.
 - intros y H.
   simpl in H.
   discriminate H.
Qed.

Lemma add_eq_self_r : forall x y : nat, x + y = x -> y = O.
Proof.
 intros x.
 induction x as [| x IHx].
 - intros y H.
   simpl in H.
   exact H.
 - intros y H.
   simpl in H.
   injection H as Hxy.
   apply IHx.
   exact Hxy.
Qed.

Lemma add_eq_self_l : forall x y : nat, x + y = y -> x = O.
Proof.
 intros x y H.
 rewrite add_comm in H.
 apply add_eq_self_r in H.
 exact H.
Qed.

Lemma add_left_comm : forall x y z : nat, x + (y + z) = y + (x + z).
Proof.
 intros x y z.
 rewrite add_assoc.
 rewrite (add_comm x y).
 rewrite <- add_assoc.
 reflexivity.
Qed.

Lemma add_right_comm : forall x y z : nat, (x + y) + z = (x + z) + y.
Proof.
 intros x y z.
 rewrite <- add_assoc.
 rewrite (add_comm y z).
 rewrite add_assoc.
 reflexivity.
Qed.

Lemma add_succ_cancel_l : forall x y z : nat, S x + z = S y + z -> x = y.
Proof.
 intros x y z H.
 simpl in H.
 injection H as Hxy.
 apply (add_cancel_r x y z).
 exact Hxy.
Qed.

Lemma add_succ_cancel_r : forall x y z : nat, x + S y = x + S z -> y = z.
Proof.
 intros x y z H.
 rewrite (add_succ_r x y) in H.
 rewrite (add_succ_r x z) in H.
 injection H as Hyz.
 apply (add_cancel_l x y z).
 exact Hyz.
Qed.

Lemma add_eq_self_iff_r : forall x y : nat, x + y = x <-> y = O.
Proof.
 intros x y.
 split.
 - apply add_eq_self_r.
 - intros H.
   rewrite H.
   apply add_0_r.
Qed.

Lemma add_eq_self_iff_l : forall x y : nat, x + y = y <-> x = O.
Proof.
 intros x y.
 split.
 - apply add_eq_self_l.
 - intros H.
   rewrite H.
   apply add_0_l.
Qed.

Lemma add_eq_O_iff : forall x y : nat, x + y = O <-> x = O /\ y = O.
Proof.
 intros x y.
 split.
 - apply add_eq_O.
 - intros [Hx Hy].
   rewrite Hx.
   rewrite Hy.
   reflexivity.
Qed.

Lemma add_cancel_l_iff : forall x y z : nat, x + y = x + z <-> y = z.
Proof.
 intros x y z.
 split.
 - apply add_cancel_l.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_cancel_r_iff : forall x y z : nat, x + z = y + z <-> x = y.
Proof.
 intros x y z.
 split.
 - apply add_cancel_r.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_succ_cancel_l_iff : forall x y z : nat,
  S x + z = S y + z <-> x = y.
Proof.
 intros x y z.
 split.
 - apply add_succ_cancel_l.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_succ_cancel_r_iff : forall x y z : nat,
  x + S y = x + S z <-> y = z.
Proof.
 intros x y z.
 split.
 - apply add_succ_cancel_r.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_succ_l_eq_succ_iff : forall x y z : nat,
  S x + y = S z <-> x + y = z.
Proof.
 intros x y z.
 rewrite add_succ_l.
 split.
 - intros H.
   injection H as H.
   exact H.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_succ_r_eq_succ_iff : forall x y z : nat,
  x + S y = S z <-> x + y = z.
Proof.
 intros x y z.
 rewrite add_succ_r.
 split.
 - intros H.
   injection H as H.
   exact H.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_succ_succ_l : forall x y : nat,
  S (S x) + y = S (S (x + y)).
Proof.
 intros x y.
 rewrite add_succ_l.
 rewrite add_succ_l.
 reflexivity.
Qed.

Lemma add_succ_succ_r : forall x y : nat,
  x + S (S y) = S (S (x + y)).
Proof.
 intros x y.
 rewrite add_succ_r.
 rewrite add_succ_r.
 reflexivity.
Qed.

Lemma add_comm_iff : forall x y z : nat, x + y = z <-> y + x = z.
Proof.
 intros x y z.
 split.
 - intros H.
   rewrite (add_comm y x).
   exact H.
 - intros H.
   rewrite (add_comm x y).
   exact H.
Qed.

Lemma add_eq_one_iff : forall x y : nat,
  x + y = S O <-> (x = O /\ y = S O) \/ (x = S O /\ y = O).
Proof.
 intros x y.
 split.
 - intros H.
   destruct x as [| x].
   + left.
     split.
     * reflexivity.
     * simpl in H.
       exact H.
   + right.
     simpl in H.
     injection H as H.
     apply add_eq_O in H.
     destruct H as [Hx Hy].
     split.
     * rewrite Hx.
       reflexivity.
     * exact Hy.
 - intros [[Hx Hy] | [Hx Hy]].
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
Qed.

Lemma add_neq_O_iff : forall x y : nat,
  x + y <> O <-> x <> O \/ y <> O.
Proof.
 intros x y.
 split.
 - intros H.
   destruct x as [| x].
   + right.
     intros Hy.
     apply H.
     rewrite Hy.
     reflexivity.
   + left.
     intros Hx.
     discriminate Hx.
 - intros [Hx | Hy] Hsum.
   + apply add_eq_O in Hsum.
     destruct Hsum as [Hzero _].
     apply Hx.
     exact Hzero.
   + apply add_eq_O in Hsum.
     destruct Hsum as [_ Hzero].
     apply Hy.
     exact Hzero.
Qed.

Lemma add_comm_cancel_l : forall x y z : nat, x + y = z + x -> y = z.
Proof.
 intros x y z H.
 rewrite (add_comm z x) in H.
 apply (add_cancel_l x y z).
 exact H.
Qed.

Lemma add_comm_cancel_r : forall x y z : nat, x + y = y + z -> x = z.
Proof.
 intros x y z H.
 rewrite (add_comm x y) in H.
 apply (add_cancel_l y x z).
 exact H.
Qed.

Lemma add_assoc_iff : forall x y z w : nat,
  x + (y + z) = w <-> (x + y) + z = w.
Proof.
 intros x y z w.
 split.
 - intros H.
   rewrite add_assoc in H.
   exact H.
 - intros H.
   rewrite <- add_assoc in H.
   exact H.
Qed.

Lemma add_left_comm_iff : forall x y z w : nat,
  x + (y + z) = w <-> y + (x + z) = w.
Proof.
 intros x y z w.
 split.
 - intros H.
   rewrite add_left_comm in H.
   exact H.
 - intros H.
   rewrite <- add_left_comm in H.
   exact H.
Qed.

Lemma add_right_comm_iff : forall x y z w : nat,
  (x + y) + z = w <-> (x + z) + y = w.
Proof.
 intros x y z w.
 split.
 - intros H.
   rewrite add_right_comm in H.
   exact H.
 - intros H.
   rewrite <- add_right_comm in H.
   exact H.
Qed.

Lemma add_succ_comm : forall x y : nat, S x + y = x + S y.
Proof.
 intros x y.
 rewrite add_succ_l.
 rewrite add_succ_r.
 reflexivity.
Qed.

Lemma add_two_succ_l : forall x y z : nat,
  (S x + S y) + z = S (S ((x + y) + z)).
Proof.
 intros x y z.
 rewrite add_succ_succ.
 rewrite add_succ_l.
 rewrite add_succ_l.
 reflexivity.
Qed.

Lemma add_two_succ_r : forall x y z : nat,
  (x + S y) + S z = S (S ((x + y) + z)).
Proof.
 intros x y z.
 rewrite add_succ_r.
 rewrite add_succ_r.
 reflexivity.
Qed.

Lemma add_succ_group_l : forall x y z : nat,
  S x + (y + z) = S (x + (y + z)).
Proof.
 intros x y z.
 apply add_succ_l.
Qed.

Lemma add_succ_group_r : forall x y z : nat,
  x + (y + S z) = S (x + (y + z)).
Proof.
 intros x y z.
 rewrite add_succ_r.
 rewrite add_succ_r.
 reflexivity.
Qed.

Lemma add_succ_middle_l : forall x y z : nat,
  (S x + y) + z = S ((x + y) + z).
Proof.
 intros x y z.
 rewrite add_succ_l.
 reflexivity.
Qed.

Lemma add_succ_middle_r : forall x y z : nat,
  (x + S y) + z = S ((x + y) + z).
Proof.
 intros x y z.
 rewrite add_succ_r.
 rewrite add_succ_l.
 reflexivity.
Qed.

Lemma add_succ_group_assoc : forall x y z : nat,
  x + (y + S z) = S ((x + y) + z).
Proof.
 intros x y z.
 rewrite add_succ_r.
 rewrite add_succ_r.
 rewrite add_assoc.
 reflexivity.
Qed.

Lemma add_self_eq_O : forall x : nat, x + x = O -> x = O.
Proof.
 intros x H.
 apply add_eq_O in H.
 destruct H as [Hx _].
 exact Hx.
Qed.

Lemma add_self_neq_O_iff : forall x : nat, x + x <> O <-> x <> O.
Proof.
 intros x.
 split.
 - intros H Hx.
   apply H.
   rewrite Hx.
   reflexivity.
 - intros H Hsum.
   apply add_eq_O in Hsum.
   destruct Hsum as [Hx _].
   apply H.
   exact Hx.
Qed.

Lemma add_self_eq_one_false : forall x : nat, x + x = S O -> False.
Proof.
 intros x H.
 destruct x as [| x].
 - simpl in H.
   discriminate H.
 - simpl in H.
   injection H as H.
   apply add_eq_O in H.
   destruct H as [_ Hy].
   discriminate Hy.
Qed.

Lemma add_self_eq_two_iff : forall x : nat,
  x + x = S (S O) <-> x = S O.
Proof.
 intros x.
 split.
 - intros H.
   destruct x as [| x].
   + simpl in H.
     discriminate H.
   + simpl in H.
     injection H as H.
     apply add_eq_one_iff in H.
     destruct H as [[Hx _] | [_ Hy]].
     * rewrite Hx.
       reflexivity.
     * discriminate Hy.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_eq_two_iff : forall x y : nat,
  x + y = S (S O) <->
  (x = O /\ y = S (S O)) \/
  (x = S O /\ y = S O) \/
  (x = S (S O) /\ y = O).
Proof.
 intros x y.
 split.
 - intros H.
   destruct x as [| x].
   + left.
     split.
     * reflexivity.
     * simpl in H.
       exact H.
   + simpl in H.
     injection H as H.
     apply add_eq_one_iff in H.
     destruct H as [[Hx Hy] | [Hx Hy]].
     * right.
       left.
       split.
       -- rewrite Hx.
          reflexivity.
       -- exact Hy.
     * right.
       right.
       split.
       -- rewrite Hx.
          reflexivity.
       -- exact Hy.
 - intros [[Hx Hy] | [[Hx Hy] | [Hx Hy]]].
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
Qed.

Lemma add_eq_two_l : forall x y : nat,
  x + y = S (S O) -> x = O \/ x = S O \/ x = S (S O).
Proof.
 intros x y H.
 apply add_eq_two_iff in H.
 destruct H as [[Hx _] | [[Hx _] | [Hx _]]].
 - left.
   exact Hx.
 - right.
   left.
   exact Hx.
 - right.
   right.
   exact Hx.
Qed.

Lemma add_eq_two_r : forall x y : nat,
  x + y = S (S O) -> y = O \/ y = S O \/ y = S (S O).
Proof.
 intros x y H.
 apply add_eq_two_iff in H.
 destruct H as [[_ Hy] | [[_ Hy] | [_ Hy]]].
 - right.
   right.
   exact Hy.
 - right.
   left.
   exact Hy.
 - left.
   exact Hy.
Qed.

Lemma add_cancel_nested_l : forall x y z w : nat,
  x + (y + z) = x + (y + w) -> z = w.
Proof.
 intros x y z w H.
 apply add_cancel_l in H.
 apply add_cancel_l in H.
 exact H.
Qed.

Lemma add_cancel_nested_m : forall x y z w : nat,
  x + (y + z) = x + (w + z) -> y = w.
Proof.
 intros x y z w H.
 apply add_cancel_l in H.
 apply add_cancel_r in H.
 exact H.
Qed.

Lemma add_cancel_nested_r : forall x y z w : nat,
  (x + y) + z = (x + w) + z -> y = w.
Proof.
 intros x y z w H.
 apply add_cancel_r in H.
 apply add_cancel_l in H.
 exact H.
Qed.

Lemma add_cancel_nested_outer : forall x y z w : nat,
  (x + y) + z = (w + y) + z -> x = w.
Proof.
 intros x y z w H.
 apply add_cancel_r in H.
 apply add_cancel_r in H.
 exact H.
Qed.

Lemma add_cancel_four_first : forall x y z w v : nat,
  x + (y + (z + w)) = x + (v + (z + w)) -> y = v.
Proof.
 intros x y z w v H.
 apply add_cancel_l in H.
 apply add_cancel_r in H.
 exact H.
Qed.

Lemma add_cancel_four_second : forall x y z w v : nat,
  x + (y + (z + w)) = x + (y + (v + w)) -> z = v.
Proof.
 intros x y z w v H.
 apply add_cancel_l in H.
 apply add_cancel_l in H.
 apply add_cancel_r in H.
 exact H.
Qed.

Lemma add_cancel_four_third : forall x y z w v : nat,
  x + (y + (z + w)) = x + (y + (z + v)) -> w = v.
Proof.
 intros x y z w v H.
 apply add_cancel_l in H.
 apply add_cancel_l in H.
 apply add_cancel_l in H.
 exact H.
Qed.

Lemma add_cancel_four_outer : forall x y z w : nat,
  x + (y + z) = w + (y + z) -> x = w.
Proof.
 intros x y z w H.
 apply add_cancel_r in H.
 exact H.
Qed.

Lemma add_eq_three_iff : forall x y : nat,
  x + y = S (S (S O)) <->
  (x = O /\ y = S (S (S O))) \/
  (x = S O /\ y = S (S O)) \/
  (x = S (S O) /\ y = S O) \/
  (x = S (S (S O)) /\ y = O).
Proof.
 intros x y.
 split.
 - intros H.
   destruct x as [| x].
   + left.
     split.
     * reflexivity.
     * simpl in H.
       exact H.
   + simpl in H.
     injection H as H.
     apply add_eq_two_iff in H.
     destruct H as [[Hx Hy] | [[Hx Hy] | [Hx Hy]]].
     * right.
       left.
       split.
       -- rewrite Hx.
          reflexivity.
       -- exact Hy.
     * right.
       right.
       left.
       split.
       -- rewrite Hx.
          reflexivity.
       -- exact Hy.
     * right.
       right.
       right.
       split.
       -- rewrite Hx.
          reflexivity.
       -- exact Hy.
 - intros [[Hx Hy] | [[Hx Hy] | [[Hx Hy] | [Hx Hy]]]].
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
Qed.

Lemma add_eq_three_l : forall x y : nat,
  x + y = S (S (S O)) ->
  x = O \/ x = S O \/ x = S (S O) \/ x = S (S (S O)).
Proof.
 intros x y H.
 apply add_eq_three_iff in H.
 destruct H as [[Hx _] | [[Hx _] | [[Hx _] | [Hx _]]]].
 - left.
   exact Hx.
 - right.
   left.
   exact Hx.
 - right.
   right.
   left.
   exact Hx.
 - right.
   right.
   right.
   exact Hx.
Qed.

Lemma add_eq_three_r : forall x y : nat,
  x + y = S (S (S O)) ->
  y = O \/ y = S O \/ y = S (S O) \/ y = S (S (S O)).
Proof.
 intros x y H.
 apply add_eq_three_iff in H.
 destruct H as [[_ Hy] | [[_ Hy] | [[_ Hy] | [_ Hy]]]].
 - right.
   right.
   right.
   exact Hy.
 - right.
   right.
   left.
   exact Hy.
 - right.
   left.
   exact Hy.
 - left.
   exact Hy.
Qed.

Lemma add_eq_four_iff : forall x y : nat,
  x + y = S (S (S (S O))) <->
  (x = O /\ y = S (S (S (S O)))) \/
  (x = S O /\ y = S (S (S O))) \/
  (x = S (S O) /\ y = S (S O)) \/
  (x = S (S (S O)) /\ y = S O) \/
  (x = S (S (S (S O))) /\ y = O).
Proof.
 intros x y.
 split.
 - intros H.
   destruct x as [| x].
   + left.
     split.
     * reflexivity.
     * simpl in H.
       exact H.
   + simpl in H.
     injection H as H.
     apply add_eq_three_iff in H.
     destruct H as [[Hx Hy] | [[Hx Hy] | [[Hx Hy] | [Hx Hy]]]].
     * right.
       left.
       split.
       -- rewrite Hx.
          reflexivity.
       -- exact Hy.
     * right.
       right.
       left.
       split.
       -- rewrite Hx.
          reflexivity.
       -- exact Hy.
     * right.
       right.
       right.
       left.
       split.
       -- rewrite Hx.
          reflexivity.
       -- exact Hy.
     * right.
       right.
       right.
       right.
       split.
       -- rewrite Hx.
          reflexivity.
       -- exact Hy.
 - intros [[Hx Hy] | [[Hx Hy] | [[Hx Hy] | [[Hx Hy] | [Hx Hy]]]]].
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
Qed.

Lemma add_eq_four_l : forall x y : nat,
  x + y = S (S (S (S O))) ->
  x = O \/ x = S O \/ x = S (S O) \/
  x = S (S (S O)) \/ x = S (S (S (S O))).
Proof.
 intros x y H.
 apply add_eq_four_iff in H.
 destruct H as [[Hx _] | [[Hx _] | [[Hx _] | [[Hx _] | [Hx _]]]]].
 - left.
   exact Hx.
 - right.
   left.
   exact Hx.
 - right.
   right.
   left.
   exact Hx.
 - right.
   right.
   right.
   left.
   exact Hx.
 - right.
   right.
   right.
   right.
   exact Hx.
Qed.

Lemma add_eq_four_r : forall x y : nat,
  x + y = S (S (S (S O))) ->
  y = O \/ y = S O \/ y = S (S O) \/
  y = S (S (S O)) \/ y = S (S (S (S O))).
Proof.
 intros x y H.
 apply add_eq_four_iff in H.
 destruct H as [[_ Hy] | [[_ Hy] | [[_ Hy] | [[_ Hy] | [_ Hy]]]]].
 - right.
   right.
   right.
   right.
   exact Hy.
 - right.
   right.
   right.
   left.
   exact Hy.
 - right.
   right.
   left.
   exact Hy.
 - right.
   left.
   exact Hy.
 - left.
   exact Hy.
Qed.

Lemma add_self_eq_three_false : forall x : nat,
  x + x = S (S (S O)) -> False.
Proof.
 intros x H.
 pose proof (add_eq_three_l x x H) as Hcases.
 destruct Hcases as [Hx | [Hx | [Hx | Hx]]].
 - rewrite Hx in H.
   simpl in H.
   discriminate H.
 - rewrite Hx in H.
   simpl in H.
   discriminate H.
 - rewrite Hx in H.
   simpl in H.
   discriminate H.
 - rewrite Hx in H.
   simpl in H.
   discriminate H.
Qed.

Lemma add_self_eq_four_iff : forall x : nat,
  x + x = S (S (S (S O))) <-> x = S (S O).
Proof.
 intros x.
 split.
 - intros H.
   pose proof (add_eq_four_l x x H) as Hcases.
   destruct Hcases as [Hx | [Hx | [Hx | [Hx | Hx]]]].
   + rewrite Hx in H.
     simpl in H.
     discriminate H.
   + rewrite Hx in H.
     simpl in H.
     discriminate H.
   + exact Hx.
   + rewrite Hx in H.
     simpl in H.
     discriminate H.
   + rewrite Hx in H.
     simpl in H.
     discriminate H.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_triple_eq_three_iff : forall x : nat,
  x + (x + x) = S (S (S O)) <-> x = S O.
Proof.
 intros x.
 split.
 - intros H.
   pose proof (add_eq_three_l x (x + x) H) as Hcases.
   destruct Hcases as [Hx | [Hx | [Hx | Hx]]].
   + rewrite Hx in H.
     simpl in H.
     discriminate H.
   + exact Hx.
   + rewrite Hx in H.
     simpl in H.
     discriminate H.
   + rewrite Hx in H.
     simpl in H.
     discriminate H.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_triple_eq_O_iff : forall x : nat,
  x + (x + x) = O <-> x = O.
Proof.
 intros x.
 split.
 - intros H.
   apply add_eq_O in H.
   destruct H as [Hx _].
   exact Hx.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_succ_three_l : forall x y : nat,
  S (S (S x)) + y = S (S (S (x + y))).
Proof.
 intros x y.
 rewrite add_succ_l.
 rewrite add_succ_l.
 rewrite add_succ_l.
 reflexivity.
Qed.

Lemma add_succ_three_r : forall x y : nat,
  x + S (S (S y)) = S (S (S (x + y))).
Proof.
 intros x y.
 rewrite add_succ_r.
 rewrite add_succ_r.
 rewrite add_succ_r.
 reflexivity.
Qed.

Lemma add_three_succ : forall x y z : nat,
  (S x + S y) + S z = S (S (S ((x + y) + z))).
Proof.
 intros x y z.
 rewrite add_succ_succ.
 rewrite add_succ_l.
 rewrite add_succ_l.
 rewrite add_succ_r.
 reflexivity.
Qed.

Lemma add_assoc_four : forall x y z w : nat,
  x + (y + (z + w)) = ((x + y) + z) + w.
Proof.
 intros x y z w.
 rewrite add_assoc.
 rewrite add_assoc.
 reflexivity.
Qed.

Lemma add_left_comm_four : forall x y z w : nat,
  x + (y + (z + w)) = x + (z + (y + w)).
Proof.
 intros x y z w.
 rewrite (add_left_comm y z w).
 reflexivity.
Qed.

Lemma add_cancel_nested_l_iff : forall x y z w : nat,
  x + (y + z) = x + (y + w) <-> z = w.
Proof.
 intros x y z w.
 split.
 - apply add_cancel_nested_l.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_cancel_nested_m_iff : forall x y z w : nat,
  x + (y + z) = x + (w + z) <-> y = w.
Proof.
 intros x y z w.
 split.
 - apply add_cancel_nested_m.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_cancel_nested_r_iff : forall x y z w : nat,
  (x + y) + z = (x + w) + z <-> y = w.
Proof.
 intros x y z w.
 split.
 - apply add_cancel_nested_r.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_cancel_nested_outer_iff : forall x y z w : nat,
  (x + y) + z = (w + y) + z <-> x = w.
Proof.
 intros x y z w.
 split.
 - apply add_cancel_nested_outer.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_cancel_four_first_iff : forall x y z w v : nat,
  x + (y + (z + w)) = x + (v + (z + w)) <-> y = v.
Proof.
 intros x y z w v.
 split.
 - apply add_cancel_four_first.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_cancel_four_second_iff : forall x y z w v : nat,
  x + (y + (z + w)) = x + (y + (v + w)) <-> z = v.
Proof.
 intros x y z w v.
 split.
 - apply add_cancel_four_second.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_cancel_four_third_iff : forall x y z w v : nat,
  x + (y + (z + w)) = x + (y + (z + v)) <-> w = v.
Proof.
 intros x y z w v.
 split.
 - apply add_cancel_four_third.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_cancel_four_outer_iff : forall x y z w : nat,
  x + (y + z) = w + (y + z) <-> x = w.
Proof.
 intros x y z w.
 split.
 - apply add_cancel_four_outer.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_succ_cancel_nested_l_iff : forall x y z w : nat,
  S x + (y + z) = S x + (y + w) <-> z = w.
Proof.
 intros x y z w.
 split.
 - apply add_cancel_nested_l.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_succ_cancel_nested_r_iff : forall x y z w : nat,
  x + (S y + z) = x + (S w + z) <-> y = w.
Proof.
 intros x y z w.
 split.
 - intros H.
   apply add_cancel_l in H.
   apply add_succ_cancel_l in H.
   exact H.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_eq_five_iff : forall x y : nat,
  x + y = S (S (S (S (S O)))) <->
  (x = O /\ y = S (S (S (S (S O))))) \/
  (x = S O /\ y = S (S (S (S O)))) \/
  (x = S (S O) /\ y = S (S (S O))) \/
  (x = S (S (S O)) /\ y = S (S O)) \/
  (x = S (S (S (S O))) /\ y = S O) \/
  (x = S (S (S (S (S O)))) /\ y = O).
Proof.
 intros x y.
 split.
 - intros H.
   destruct x as [| x].
   + left.
     split.
     * reflexivity.
     * simpl in H.
       exact H.
   + simpl in H.
     injection H as H.
     apply add_eq_four_iff in H.
     destruct H as [[Hx Hy] | [[Hx Hy] | [[Hx Hy] | [[Hx Hy] | [Hx Hy]]]]].
     * right.
       left.
       split.
       -- rewrite Hx.
          reflexivity.
       -- exact Hy.
     * right.
       right.
       left.
       split.
       -- rewrite Hx.
          reflexivity.
       -- exact Hy.
     * right.
       right.
       right.
       left.
       split.
       -- rewrite Hx.
          reflexivity.
       -- exact Hy.
     * right.
       right.
       right.
       right.
       left.
       split.
       -- rewrite Hx.
          reflexivity.
       -- exact Hy.
     * right.
       right.
       right.
       right.
       right.
       split.
       -- rewrite Hx.
          reflexivity.
       -- exact Hy.
 - intros [[Hx Hy] | [[Hx Hy] | [[Hx Hy] | [[Hx Hy] | [[Hx Hy] | [Hx Hy]]]]]].
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
   + rewrite Hx.
     rewrite Hy.
     reflexivity.
Qed.

Lemma add_eq_five_l : forall x y : nat,
  x + y = S (S (S (S (S O)))) ->
  x = O \/ x = S O \/ x = S (S O) \/ x = S (S (S O)) \/
  x = S (S (S (S O))) \/ x = S (S (S (S (S O)))).
Proof.
 intros x y H.
 apply add_eq_five_iff in H.
 destruct H as [[Hx _] | [[Hx _] | [[Hx _] | [[Hx _] | [[Hx _] | [Hx _]]]]]].
 - left.
   exact Hx.
 - right.
   left.
   exact Hx.
 - right.
   right.
   left.
   exact Hx.
 - right.
   right.
   right.
   left.
   exact Hx.
 - right.
   right.
   right.
   right.
   left.
   exact Hx.
 - right.
   right.
   right.
   right.
   right.
   exact Hx.
Qed.

Lemma add_eq_five_r : forall x y : nat,
  x + y = S (S (S (S (S O)))) ->
  y = O \/ y = S O \/ y = S (S O) \/ y = S (S (S O)) \/
  y = S (S (S (S O))) \/ y = S (S (S (S (S O)))).
Proof.
 intros x y H.
 apply add_eq_five_iff in H.
 destruct H as [[_ Hy] | [[_ Hy] | [[_ Hy] | [[_ Hy] | [[_ Hy] | [_ Hy]]]]]].
 - right.
   right.
   right.
   right.
   right.
   exact Hy.
 - right.
   right.
   right.
   right.
   left.
   exact Hy.
 - right.
   right.
   right.
   left.
   exact Hy.
 - right.
   right.
   left.
   exact Hy.
 - right.
   left.
   exact Hy.
 - left.
   exact Hy.
Qed.

Lemma add_self_eq_five_false : forall x : nat,
  x + x = S (S (S (S (S O)))) -> False.
Proof.
 intros x H.
 pose proof (add_eq_five_l x x H) as Hcases.
 destruct Hcases as [Hx | [Hx | [Hx | [Hx | [Hx | Hx]]]]].
 - rewrite Hx in H.
   simpl in H.
   discriminate H.
 - rewrite Hx in H.
   simpl in H.
   discriminate H.
 - rewrite Hx in H.
   simpl in H.
   discriminate H.
 - rewrite Hx in H.
   simpl in H.
   discriminate H.
 - rewrite Hx in H.
   simpl in H.
   discriminate H.
 - rewrite Hx in H.
   simpl in H.
   discriminate H.
Qed.

Lemma add_self_eq_six_iff : forall x : nat,
  x + x = S (S (S (S (S (S O))))) <-> x = S (S (S O)).
Proof.
 intros x.
 split.
 - intros H.
   destruct x as [| x].
   + simpl in H.
     discriminate H.
   + rewrite add_succ_succ in H.
     injection H as H.
     apply add_self_eq_four_iff in H.
     rewrite H.
     reflexivity.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma add_6_l : forall x : nat,
  S (S (S (S (S (S O))))) + x = S (S (S (S (S (S x))))).
Proof.
 intros x.
 repeat rewrite add_succ_l.
 reflexivity.
Qed.

Lemma add_6_r : forall x : nat,
  x + S (S (S (S (S (S O))))) = S (S (S (S (S (S x))))).
Proof.
 intros x.
 repeat rewrite add_succ_r.
 rewrite add_0_r.
 reflexivity.
Qed.

Lemma add_7_l : forall x : nat,
  S (S (S (S (S (S (S O)))))) + x = S (S (S (S (S (S (S x)))))).
Proof.
 intros x.
 repeat rewrite add_succ_l.
 reflexivity.
Qed.

Lemma add_7_r : forall x : nat,
  x + S (S (S (S (S (S (S O)))))) = S (S (S (S (S (S (S x)))))).
Proof.
 intros x.
 repeat rewrite add_succ_r.
 rewrite add_0_r.
 reflexivity.
Qed.

Lemma add_8_l : forall x : nat,
  S (S (S (S (S (S (S (S O))))))) + x = S (S (S (S (S (S (S (S x))))))).
Proof.
 intros x.
 repeat rewrite add_succ_l.
 reflexivity.
Qed.

Lemma add_8_r : forall x : nat,
  x + S (S (S (S (S (S (S (S O))))))) = S (S (S (S (S (S (S (S x))))))).
Proof.
 intros x.
 repeat rewrite add_succ_r.
 rewrite add_0_r.
 reflexivity.
Qed.

Lemma add_9_l : forall x : nat,
  S (S (S (S (S (S (S (S (S O)))))))) + x =
  S (S (S (S (S (S (S (S (S x)))))))).
Proof.
 intros x.
 repeat rewrite add_succ_l.
 reflexivity.
Qed.

Lemma add_9_r : forall x : nat,
  x + S (S (S (S (S (S (S (S (S O)))))))) =
  S (S (S (S (S (S (S (S (S x)))))))).
Proof.
 intros x.
 repeat rewrite add_succ_r.
 rewrite add_0_r.
 reflexivity.
Qed.

Lemma add_10_l : forall x : nat,
  S (S (S (S (S (S (S (S (S (S O))))))))) + x =
  S (S (S (S (S (S (S (S (S (S x))))))))).
Proof.
 intros x.
 repeat rewrite add_succ_l.
 reflexivity.
Qed.

Lemma add_10_r : forall x : nat,
  x + S (S (S (S (S (S (S (S (S (S O))))))))) =
  S (S (S (S (S (S (S (S (S (S x))))))))).
Proof.
 intros x.
 repeat rewrite add_succ_r.
 rewrite add_0_r.
 reflexivity.
Qed.

Lemma add_11_l : forall x : nat,
  S (S (S (S (S (S (S (S (S (S (S O)))))))))) + x =
  S (S (S (S (S (S (S (S (S (S (S x)))))))))).
Proof.
 intros x.
 repeat rewrite add_succ_l.
 reflexivity.
Qed.

Lemma add_11_r : forall x : nat,
  x + S (S (S (S (S (S (S (S (S (S (S O)))))))))) =
  S (S (S (S (S (S (S (S (S (S (S x)))))))))).
Proof.
 intros x.
 repeat rewrite add_succ_r.
 rewrite add_0_r.
 reflexivity.
Qed.

Lemma add_12_l : forall x : nat,
  S (S (S (S (S (S (S (S (S (S (S (S O))))))))))) + x =
  S (S (S (S (S (S (S (S (S (S (S (S x))))))))))).
Proof.
 intros x.
 repeat rewrite add_succ_l.
 reflexivity.
Qed.

Lemma add_12_r : forall x : nat,
  x + S (S (S (S (S (S (S (S (S (S (S (S O))))))))))) =
  S (S (S (S (S (S (S (S (S (S (S (S x))))))))))).
Proof.
 intros x.
 repeat rewrite add_succ_r.
 rewrite add_0_r.
 reflexivity.
Qed.

Lemma add_13_l : forall x : nat,
  S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))) + x =
  S (S (S (S (S (S (S (S (S (S (S (S (S x)))))))))))).
Proof.
 intros x.
 repeat rewrite add_succ_l.
 reflexivity.
Qed.

Lemma add_13_r : forall x : nat,
  x + S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))) =
  S (S (S (S (S (S (S (S (S (S (S (S (S x)))))))))))).
Proof.
 intros x.
 repeat rewrite add_succ_r.
 rewrite add_0_r.
 reflexivity.
Qed.

Lemma add_14_l : forall x : nat,
  S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))) + x =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S x))))))))))))).
Proof.
 intros x.
 repeat rewrite add_succ_l.
 reflexivity.
Qed.

Lemma add_14_r : forall x : nat,
  x + S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))) =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S x))))))))))))).
Proof.
 intros x.
 repeat rewrite add_succ_r.
 rewrite add_0_r.
 reflexivity.
Qed.

Lemma add_15_l : forall x : nat,
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))) + x =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x)))))))))))))).
Proof.
 intros x.
 repeat rewrite add_succ_l.
 reflexivity.
Qed.

Lemma add_15_r : forall x : nat,
  x + S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))) =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x)))))))))))))).
Proof.
 intros x.
 repeat rewrite add_succ_r.
 rewrite add_0_r.
 reflexivity.
Qed.

Lemma add_succ_assoc : forall x y z : nat,
  S x + (y + z) = (S x + y) + z.
Proof.
 intros x y z.
 rewrite add_assoc.
 reflexivity.
Qed.

Lemma add_left_cancel_succ : forall x y z : nat,
  S x + y = S x + z -> y = z.
Proof.
 intros x y z H.
 apply (add_cancel_l (S x) y z).
 exact H.
Qed.

Lemma add_eq_O_three_iff : forall x y z : nat,
  (x + y) + z = O <-> x = O /\ y = O /\ z = O.
Proof.
 intros x y z.
 split.
 - intros H.
   apply add_eq_O_iff in H.
   destruct H as [Hxy Hz].
   apply add_eq_O_iff in Hxy.
   destruct Hxy as [Hx Hy].
   repeat split; assumption.
 - intros [Hx [Hy Hz]].
   rewrite Hx, Hy, Hz.
   reflexivity.
Qed.

Lemma add_eq_O_four_iff : forall x y z w : nat,
  ((x + y) + z) + w = O <-> x = O /\ y = O /\ z = O /\ w = O.
Proof.
 intros x y z w.
 split.
 - intros H.
   apply add_eq_O_iff in H.
   destruct H as [Hxyz Hw].
   apply add_eq_O_three_iff in Hxyz.
   destruct Hxyz as [Hx [Hy Hz]].
   repeat split; assumption.
 - intros [Hx [Hy [Hz Hw]]].
   rewrite Hx, Hy, Hz, Hw.
   reflexivity.
Qed.

Lemma add_eq_O_five_iff : forall x y z w v : nat,
  (((x + y) + z) + w) + v = O <->
  x = O /\ y = O /\ z = O /\ w = O /\ v = O.
Proof.
 intros x y z w v.
 split.
 - intros H.
   apply add_eq_O_iff in H.
   destruct H as [Hxyzw Hv].
   apply add_eq_O_four_iff in Hxyzw.
   destruct Hxyzw as [Hx [Hy [Hz Hw]]].
   repeat split; assumption.
 - intros [Hx [Hy [Hz [Hw Hv]]]].
   rewrite Hx, Hy, Hz, Hw, Hv.
   reflexivity.
Qed.

Lemma add_eq_O_six_iff : forall x y z w v u : nat,
  ((((x + y) + z) + w) + v) + u = O <->
  x = O /\ y = O /\ z = O /\ w = O /\ v = O /\ u = O.
Proof.
 intros x y z w v u.
 split.
 - intros H.
   apply add_eq_O_iff in H.
   destruct H as [Hxyzwv Hu].
   apply add_eq_O_five_iff in Hxyzwv.
   destruct Hxyzwv as [Hx [Hy [Hz [Hw Hv]]]].
   repeat split; assumption.
 - intros [Hx [Hy [Hz [Hw [Hv Hu]]]]].
   rewrite Hx, Hy, Hz, Hw, Hv, Hu.
   reflexivity.
Qed.

Lemma add_eq_O_seven_iff : forall x y z w v u t : nat,
  (((((x + y) + z) + w) + v) + u) + t = O <->
  x = O /\ y = O /\ z = O /\ w = O /\ v = O /\ u = O /\ t = O.
Proof.
 intros x y z w v u t.
 split.
 - intros H.
   apply add_eq_O_iff in H.
   destruct H as [Hxyzwvu Ht].
   apply add_eq_O_six_iff in Hxyzwvu.
   destruct Hxyzwvu as [Hx [Hy [Hz [Hw [Hv Hu]]]]].
   repeat split; assumption.
 - intros [Hx [Hy [Hz [Hw [Hv [Hu Ht]]]]]].
   rewrite Hx, Hy, Hz, Hw, Hv, Hu, Ht.
   reflexivity.
Qed.

Lemma add_eq_O_three_l : forall x y z : nat,
  (x + y) + z = O -> x = O.
Proof.
 intros x y z H.
 apply add_eq_O_three_iff in H.
 tauto.
Qed.

Lemma add_eq_O_three_m : forall x y z : nat,
  (x + y) + z = O -> y = O.
Proof.
 intros x y z H.
 apply add_eq_O_three_iff in H.
 tauto.
Qed.

Lemma add_eq_O_three_r : forall x y z : nat,
  (x + y) + z = O -> z = O.
Proof.
 intros x y z H.
 apply add_eq_O_three_iff in H.
 tauto.
Qed.

Lemma add_eq_O_four_first : forall x y z w : nat,
  ((x + y) + z) + w = O -> x = O.
Proof.
 intros x y z w H.
 apply add_eq_O_four_iff in H.
 tauto.
Qed.

Lemma add_eq_O_four_second : forall x y z w : nat,
  ((x + y) + z) + w = O -> y = O.
Proof.
 intros x y z w H.
 apply add_eq_O_four_iff in H.
 tauto.
Qed.

Lemma add_eq_O_four_third : forall x y z w : nat,
  ((x + y) + z) + w = O -> z = O.
Proof.
 intros x y z w H.
 apply add_eq_O_four_iff in H.
 tauto.
Qed.

Lemma add_eq_O_four_fourth : forall x y z w : nat,
  ((x + y) + z) + w = O -> w = O.
Proof.
 intros x y z w H.
 apply add_eq_O_four_iff in H.
 tauto.
Qed.

Lemma add_eq_O_five_first : forall x y z w v : nat,
  (((x + y) + z) + w) + v = O -> x = O.
Proof.
 intros x y z w v H.
 apply add_eq_O_five_iff in H.
 tauto.
Qed.

Lemma add_eq_O_five_second : forall x y z w v : nat,
  (((x + y) + z) + w) + v = O -> y = O.
Proof.
 intros x y z w v H.
 apply add_eq_O_five_iff in H.
 tauto.
Qed.

Lemma add_eq_O_five_third : forall x y z w v : nat,
  (((x + y) + z) + w) + v = O -> z = O.
Proof.
 intros x y z w v H.
 apply add_eq_O_five_iff in H.
 tauto.
Qed.

Lemma add_eq_O_five_fourth : forall x y z w v : nat,
  (((x + y) + z) + w) + v = O -> w = O.
Proof.
 intros x y z w v H.
 apply add_eq_O_five_iff in H.
 tauto.
Qed.

Lemma add_eq_O_five_fifth : forall x y z w v : nat,
  (((x + y) + z) + w) + v = O -> v = O.
Proof.
 intros x y z w v H.
 apply add_eq_O_five_iff in H.
 tauto.
Qed.

Lemma add_eq_O_six_first : forall x y z w v u : nat,
  ((((x + y) + z) + w) + v) + u = O -> x = O.
Proof.
 intros x y z w v u H.
 apply add_eq_O_six_iff in H.
 tauto.
Qed.

Lemma add_eq_O_six_second : forall x y z w v u : nat,
  ((((x + y) + z) + w) + v) + u = O -> y = O.
Proof.
 intros x y z w v u H.
 apply add_eq_O_six_iff in H.
 tauto.
Qed.

Lemma add_eq_O_six_third : forall x y z w v u : nat,
  ((((x + y) + z) + w) + v) + u = O -> z = O.
Proof.
 intros x y z w v u H.
 apply add_eq_O_six_iff in H.
 tauto.
Qed.
