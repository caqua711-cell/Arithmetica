Require Import def.
Require Import add.

Lemma mult_0_l : forall x : nat, O * x = O.
Proof.
 intros x.
 reflexivity.
Qed.

Lemma mult_0_r : forall x : nat, x * O = O.
Proof.
 intros x.
 induction x as [| x IHx].
 - reflexivity.
 - simpl.
   rewrite IHx.
   reflexivity.
Qed.

Lemma mult_succ_l : forall x y : nat, S x * y = y + x * y.
Proof.
 intros x y.
 reflexivity.
Qed.

Lemma mult_succ_r : forall x y : nat, x * S y = x + x * y.
Proof.
 intros x.
 induction x as [| x IHx].
 - intros y.
   reflexivity.
 - intros y.
   simpl.
   rewrite IHx.
   rewrite add_left_comm.
   reflexivity.
Qed.

Lemma mult_1_l : forall x : nat, S O * x = x.
Proof.
 intros x.
 simpl.
 rewrite add_0_r.
 reflexivity.
Qed.

Lemma mult_1_r : forall x : nat, x * S O = x.
Proof.
 intros x.
 induction x as [| x IHx].
 - reflexivity.
 - simpl.
   rewrite IHx.
   reflexivity.
Qed.

Lemma mult_comm : forall x y : nat, x * y = y * x.
Proof.
 intros x.
 induction x as [| x IHx].
 - intros y.
   simpl.
   rewrite mult_0_r.
   reflexivity.
 - intros y.
   simpl.
   rewrite mult_succ_r.
   rewrite IHx.
   reflexivity.
Qed.

Lemma mult_add_distr_r : forall x y z : nat,
  (x + y) * z = x * z + y * z.
Proof.
 intros x.
 induction x as [| x IHx].
 - intros y z.
   simpl.
   reflexivity.
 - intros y z.
   rewrite add_succ_l.
   simpl.
   rewrite IHx.
   rewrite add_assoc.
   reflexivity.
Qed.

Lemma mult_add_distr_l : forall x y z : nat,
  x * (y + z) = x * y + x * z.
Proof.
 intros x y z.
 rewrite (mult_comm x (add y z)).
 rewrite mult_add_distr_r.
 rewrite (mult_comm y x).
 rewrite (mult_comm z x).
 reflexivity.
Qed.

Lemma mult_assoc : forall x y z : nat,
  (x * y) * z = x * (y * z).
Proof.
 intros x.
 induction x as [| x IHx].
 - intros y z.
   reflexivity.
 - intros y z.
   simpl.
   rewrite mult_add_distr_r.
   rewrite IHx.
   reflexivity.
Qed.

Lemma mult_left_comm : forall x y z : nat,
  (x * y) * z = (x * z) * y.
Proof.
 intros x y z.
 rewrite mult_assoc.
 rewrite (mult_comm y z).
 rewrite <- mult_assoc.
 reflexivity.
Qed.

Lemma mult_right_comm : forall x y z : nat,
  x * (y * z) = y * (x * z).
Proof.
 intros x y z.
 rewrite <- mult_assoc.
 rewrite (mult_comm x y).
 rewrite mult_assoc.
 reflexivity.
Qed.

Lemma mult_succ_succ : forall x y : nat,
  S x * S y = S y + (x + x * y).
Proof.
 intros x y.
 rewrite mult_succ_l.
 rewrite mult_succ_r.
 reflexivity.
Qed.

Lemma mult_eq_O : forall x y : nat, x * y = O -> x = O \/ y = O.
Proof.
 intros x y H.
 destruct x as [| x].
 - left.
   reflexivity.
 - right.
   simpl in H.
   apply add_eq_O in H.
   destruct H as [Hy _].
   exact Hy.
Qed.

Lemma mult_neq_O : forall x y : nat,
  x <> O -> y <> O -> x * y <> O.
Proof.
 intros x y Hx Hy Hmult.
 apply mult_eq_O in Hmult.
 destruct Hmult as [Hzero | Hzero].
 - apply Hx.
   exact Hzero.
 - apply Hy.
   exact Hzero.
Qed.

Lemma mult_succ_l_add : forall x y : nat,
  S x * y = x * y + y.
Proof.
 intros x y.
 rewrite mult_succ_l.
 rewrite add_comm.
 reflexivity.
Qed.

Lemma mult_succ_r_add : forall x y : nat,
  x * S y = x * y + x.
Proof.
 intros x y.
 rewrite mult_succ_r.
 rewrite add_comm.
 reflexivity.
Qed.

Lemma mult_add_distr_l_rev : forall x y z : nat,
  x * y + x * z = x * (y + z).
Proof.
 intros x y z.
 symmetry.
 apply mult_add_distr_l.
Qed.

Lemma mult_add_distr_r_rev : forall x y z : nat,
  x * z + y * z = (x + y) * z.
Proof.
 intros x y z.
 symmetry.
 apply mult_add_distr_r.
Qed.

Lemma mult_add_add : forall x y z w : nat,
  (x + y) * (z + w) = (x * z + x * w) + (y * z + y * w).
Proof.
 intros x y z w.
 rewrite mult_add_distr_r.
 rewrite mult_add_distr_l.
 rewrite mult_add_distr_l.
 reflexivity.
Qed.

Lemma mult_add_distr_l_three : forall x y z w : nat,
  x * ((y + z) + w) = (x * y + x * z) + x * w.
Proof.
 intros x y z w.
 rewrite mult_add_distr_l.
 rewrite mult_add_distr_l.
 reflexivity.
Qed.

Lemma mult_add_distr_r_three : forall x y z w : nat,
  ((x + y) + z) * w = (x * w + y * w) + z * w.
Proof.
 intros x y z w.
 rewrite mult_add_distr_r.
 rewrite mult_add_distr_r.
 reflexivity.
Qed.

Lemma mult_add_add_alt : forall x y z w : nat,
  (x + y) * (z + w) = (x * z + y * z) + (x * w + y * w).
Proof.
 intros x y z w.
 rewrite mult_add_distr_r.
 rewrite mult_add_distr_l.
 rewrite mult_add_distr_l.
 rewrite add_assoc.
 rewrite (add_right_comm (x * z) (x * w) (y * z)).
 rewrite <- add_assoc.
 reflexivity.
Qed.

Lemma mult_add_cancel_l : forall x y z w : nat,
  z + x * y = z + x * w -> x * y = x * w.
Proof.
 intros x y z w H.
 apply (add_cancel_l z (x * y) (x * w)).
 exact H.
Qed.

Lemma mult_add_cancel_r : forall x y z w : nat,
  x * y + z = x * w + z -> x * y = x * w.
Proof.
 intros x y z w H.
 apply (add_cancel_r (x * y) (x * w) z).
 exact H.
Qed.

Lemma mult_succ_succ_add : forall x y : nat,
  S x * S y = S (x + (y + x * y)).
Proof.
 intros x y.
 rewrite mult_succ_succ.
 rewrite add_succ_l.
 rewrite add_left_comm.
 reflexivity.
Qed.

Lemma mult_eq_O_iff : forall x y : nat, x * y = O <-> x = O \/ y = O.
Proof.
 intros x y.
 split.
 - apply mult_eq_O.
 - intros [Hx | Hy].
   + rewrite Hx.
     apply mult_0_l.
   + rewrite Hy.
     apply mult_0_r.
Qed.

Lemma mult_neq_O_iff : forall x y : nat,
  x * y <> O <-> x <> O /\ y <> O.
Proof.
 intros x y.
 split.
 - intros H.
   split.
   + intros Hx.
     apply H.
     rewrite Hx.
     apply mult_0_l.
   + intros Hy.
     apply H.
     rewrite Hy.
     apply mult_0_r.
 - intros [Hx Hy].
   apply mult_neq_O; assumption.
Qed.

Lemma mult_1_cancel_l : forall x y : nat, S O * x = S O * y -> x = y.
Proof.
 intros x y H.
 rewrite mult_1_l in H.
 rewrite mult_1_l in H.
 exact H.
Qed.

Lemma mult_1_cancel_r : forall x y : nat, x * S O = y * S O -> x = y.
Proof.
 intros x y H.
 rewrite mult_1_r in H.
 rewrite mult_1_r in H.
 exact H.
Qed.

Lemma mult_comm_iff : forall x y z : nat, x * y = z <-> y * x = z.
Proof.
 intros x y z.
 split.
 - intros H.
   rewrite (mult_comm y x).
   exact H.
 - intros H.
   rewrite (mult_comm x y).
   exact H.
Qed.

Lemma mult_assoc_iff : forall x y z w : nat,
  (x * y) * z = w <-> x * (y * z) = w.
Proof.
 intros x y z w.
 split.
 - intros H.
   rewrite mult_assoc in H.
   exact H.
 - intros H.
   rewrite <- mult_assoc in H.
   exact H.
Qed.

Lemma mult_left_comm_iff : forall x y z w : nat,
  (x * y) * z = w <-> (x * z) * y = w.
Proof.
 intros x y z w.
 split.
 - intros H.
   rewrite mult_left_comm in H.
   exact H.
 - intros H.
   rewrite <- mult_left_comm in H.
   exact H.
Qed.

Lemma mult_right_comm_iff : forall x y z w : nat,
  x * (y * z) = w <-> y * (x * z) = w.
Proof.
 intros x y z w.
 split.
 - intros H.
   rewrite mult_right_comm in H.
   exact H.
 - intros H.
   rewrite <- mult_right_comm in H.
   exact H.
Qed.

Lemma mult_eq_one_iff : forall x y : nat,
  x * y = S O <-> x = S O /\ y = S O.
Proof.
 intros x y.
 split.
 - intros H.
   destruct x as [| x].
   + simpl in H.
     discriminate H.
   + simpl in H.
     apply add_eq_one_iff in H.
     destruct H as [[Hy Hxy] | [Hy Hxy]].
     * rewrite Hy in Hxy.
       rewrite mult_0_r in Hxy.
       discriminate Hxy.
     * rewrite Hy in Hxy.
       rewrite mult_1_r in Hxy.
       split.
       -- rewrite Hxy.
          reflexivity.
       -- exact Hy.
 - intros [Hx Hy].
   rewrite Hx.
   rewrite Hy.
   reflexivity.
Qed.

Lemma mult_eq_one_l : forall x y : nat, x * y = S O -> x = S O.
Proof.
 intros x y H.
 apply mult_eq_one_iff in H.
 destruct H as [Hx _].
 exact Hx.
Qed.

Lemma mult_eq_one_r : forall x y : nat, x * y = S O -> y = S O.
Proof.
 intros x y H.
 apply mult_eq_one_iff in H.
 destruct H as [_ Hy].
 exact Hy.
Qed.

Lemma mult_eq_O_l_iff : forall x y : nat,
  y <> O -> (x * y = O <-> x = O).
Proof.
 intros x y Hy.
 split.
 - intros H.
   apply mult_eq_O in H.
   destruct H as [Hx | Hyzero].
   + exact Hx.
   + contradiction.
 - intros H.
   rewrite H.
   apply mult_0_l.
Qed.

Lemma mult_eq_O_r_iff : forall x y : nat,
  x <> O -> (x * y = O <-> y = O).
Proof.
 intros x y Hx.
 split.
 - intros H.
   apply mult_eq_O in H.
   destruct H as [Hxzero | Hy].
   + contradiction.
   + exact Hy.
 - intros H.
   rewrite H.
   apply mult_0_r.
Qed.

Lemma mult_succ_succ_add_assoc : forall x y : nat,
  S x * S y = S ((x + y) + x * y).
Proof.
 intros x y.
 rewrite mult_succ_succ_add.
 f_equal.
 apply add_assoc.
Qed.

Lemma mult_add_cancel_l_iff : forall x y z w : nat,
  x + y * z = x + w <-> y * z = w.
Proof.
 intros x y z w.
 split.
 - apply add_cancel_l.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma mult_add_cancel_r_iff : forall x y z w : nat,
  y * z + x = w + x <-> y * z = w.
Proof.
 intros x y z w.
 split.
 - apply add_cancel_r.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma mult_add_zero_iff : forall x y z : nat,
  x * y + z = O <-> x * y = O /\ z = O.
Proof.
 intros x y z.
 split.
 - apply add_eq_O.
 - intros [Hxy Hz].
   rewrite Hxy.
   rewrite Hz.
   reflexivity.
Qed.

Lemma mult_add_eq_self_l : forall x y z : nat,
  x + y * z = x -> y * z = O.
Proof.
 intros x y z H.
 apply add_eq_self_r in H.
 exact H.
Qed.

Lemma mult_add_eq_self_r : forall x y z : nat,
  y * z + x = x -> y * z = O.
Proof.
 intros x y z H.
 apply add_eq_self_l in H.
 exact H.
Qed.

Lemma mult_add_succ_r : forall x y z : nat,
  (x + y) * S z = (x + y) * z + (x + y).
Proof.
 intros x y z.
 rewrite mult_succ_r.
 rewrite add_comm.
 reflexivity.
Qed.

Lemma mult_succ_add_l : forall x y z : nat,
  S (x + y) * z = (x + y) * z + z.
Proof.
 intros x y z.
 apply mult_succ_l_add.
Qed.

Lemma mult_add_succ_l : forall x y z : nat,
  (S x + y) * z = (x * z + y * z) + z.
Proof.
 intros x y z.
 rewrite add_succ_l.
 rewrite mult_succ_l_add.
 rewrite mult_add_distr_r.
 reflexivity.
Qed.

Lemma mult_succ_add_r : forall x y z : nat,
  (x + S y) * z = x * z + (y * z + z).
Proof.
 intros x y z.
 rewrite add_succ_r.
 rewrite mult_succ_l_add.
 rewrite mult_add_distr_r.
 rewrite <- add_assoc.
 reflexivity.
Qed.

Lemma mult_add_distr_l_nested : forall x y z w : nat,
  x * (y + (z + w)) = x * y + (x * z + x * w).
Proof.
 intros x y z w.
 rewrite mult_add_distr_l.
 rewrite mult_add_distr_l.
 reflexivity.
Qed.

Lemma mult_add_distr_r_nested : forall x y z w : nat,
  (x + (y + z)) * w = x * w + (y * w + z * w).
Proof.
 intros x y z w.
 rewrite mult_add_distr_r.
 rewrite mult_add_distr_r.
 reflexivity.
Qed.

Lemma mult_add_distr_l_four : forall x y z w v : nat,
  x * ((y + z) + (w + v)) =
  (x * y + x * z) + (x * w + x * v).
Proof.
 intros x y z w v.
 rewrite mult_add_distr_l.
 rewrite mult_add_distr_l.
 rewrite mult_add_distr_l.
 reflexivity.
Qed.

Lemma mult_add_distr_r_four : forall x y z w v : nat,
  ((x + y) + (z + w)) * v =
  (x * v + y * v) + (z * v + w * v).
Proof.
 intros x y z w v.
 rewrite mult_add_distr_r.
 rewrite mult_add_distr_r.
 rewrite mult_add_distr_r.
 reflexivity.
Qed.

Lemma mult_add_add_left_assoc : forall x y z w v : nat,
  (x + y) * (z + (w + v)) =
  (x * z + (x * w + x * v)) + (y * z + (y * w + y * v)).
Proof.
 intros x y z w v.
 rewrite mult_add_distr_r.
 rewrite (mult_add_distr_l x z (w + v)).
 rewrite (mult_add_distr_l x w v).
 rewrite (mult_add_distr_l y z (w + v)).
 rewrite (mult_add_distr_l y w v).
 reflexivity.
Qed.

Lemma mult_add_add_right_assoc : forall x y z w v : nat,
  (x + (y + z)) * (w + v) =
  (x * w + x * v) + ((y * w + y * v) + (z * w + z * v)).
Proof.
 intros x y z w v.
 rewrite mult_add_distr_r.
 rewrite mult_add_distr_r.
 rewrite mult_add_distr_l.
 rewrite mult_add_distr_l.
 rewrite mult_add_distr_l.
 reflexivity.
Qed.

Lemma mult_2_l : forall x : nat, S (S O) * x = x + x.
Proof.
 intros x.
 rewrite mult_succ_l.
 rewrite mult_1_l.
 reflexivity.
Qed.

Lemma mult_2_r : forall x : nat, x * S (S O) = x + x.
Proof.
 intros x.
 rewrite mult_succ_r.
 rewrite mult_1_r.
 reflexivity.
Qed.

Lemma mult_3_l : forall x : nat, S (S (S O)) * x = x + (x + x).
Proof.
 intros x.
 rewrite mult_succ_l.
 rewrite mult_2_l.
 reflexivity.
Qed.

Lemma mult_3_r : forall x : nat, x * S (S (S O)) = x + (x + x).
Proof.
 intros x.
 rewrite mult_succ_r.
 rewrite mult_2_r.
 reflexivity.
Qed.

Lemma mult_self_eq_O_iff : forall x : nat, x * x = O <-> x = O.
Proof.
 intros x.
 split.
 - intros H.
   apply mult_eq_O_iff in H.
   destruct H as [H | H].
   + exact H.
   + exact H.
 - intros H.
   rewrite H.
   apply mult_0_l.
Qed.

Lemma mult_self_neq_O_iff : forall x : nat, x * x <> O <-> x <> O.
Proof.
 intros x.
 split.
 - intros H Hx.
   apply H.
   rewrite Hx.
   reflexivity.
 - intros H Hsquare.
   apply (mult_self_eq_O_iff x) in Hsquare.
   apply H.
   exact Hsquare.
Qed.

Lemma mult_eq_self_l_iff : forall x y : nat,
  x * y = x <-> x = O \/ y = S O.
Proof.
 intros x y.
 split.
 - intros H.
   destruct x as [| x].
   + left.
     reflexivity.
   + destruct y as [| y].
     * rewrite mult_0_r in H.
       discriminate H.
     * right.
       rewrite mult_succ_r in H.
       apply add_eq_self_r in H.
       apply mult_eq_O in H.
       destruct H as [Hx | Hy].
       -- discriminate Hx.
       -- rewrite Hy.
          reflexivity.
 - intros [Hx | Hy].
   + rewrite Hx.
     reflexivity.
   + rewrite Hy.
     apply mult_1_r.
Qed.

Lemma mult_eq_self_r_iff : forall x y : nat,
  x * y = y <-> y = O \/ x = S O.
Proof.
 intros x y.
 rewrite (mult_comm x y).
 apply mult_eq_self_l_iff.
Qed.

Lemma mult_self_eq_one_iff : forall x : nat,
  x * x = S O <-> x = S O.
Proof.
 intros x.
 split.
 - intros H.
   apply mult_eq_one_iff in H.
   destruct H as [H _].
   exact H.
 - intros H.
   rewrite H.
   reflexivity.
Qed.

Lemma mult_self_neq_one_iff : forall x : nat,
  x * x <> S O <-> x <> S O.
Proof.
 intros x.
 split.
 - intros H Hx.
   apply H.
   rewrite Hx.
   reflexivity.
 - intros H Hsquare.
   apply (mult_self_eq_one_iff x) in Hsquare.
   apply H.
   exact Hsquare.
Qed.

Lemma mult_4_l : forall x : nat,
  S (S (S (S O))) * x = x + (x + (x + x)).
Proof.
 intros x.
 rewrite mult_succ_l.
 rewrite mult_3_l.
 reflexivity.
Qed.

Lemma mult_4_r : forall x : nat,
  x * S (S (S (S O))) = x + (x + (x + x)).
Proof.
 intros x.
 rewrite mult_succ_r.
 rewrite mult_3_r.
 reflexivity.
Qed.

Lemma mult_5_l : forall x : nat,
  S (S (S (S (S O)))) * x = x + (x + (x + (x + x))).
Proof.
 intros x.
 rewrite mult_succ_l.
 rewrite mult_4_l.
 reflexivity.
Qed.

Lemma mult_5_r : forall x : nat,
  x * S (S (S (S (S O)))) = x + (x + (x + (x + x))).
Proof.
 intros x.
 rewrite mult_succ_r.
 rewrite mult_4_r.
 reflexivity.
Qed.

Lemma mult_add_l_assoc : forall x y z w : nat,
  x * (y + z + w) = x * y + (x * z + x * w).
Proof.
 intros x y z w.
 rewrite mult_add_distr_l.
 rewrite mult_add_distr_l.
 rewrite add_assoc.
 reflexivity.
Qed.

Lemma mult_add_l_assoc_rev : forall x y z w : nat,
  x * y + (x * z + x * w) = x * (y + z + w).
Proof.
 intros x y z w.
 symmetry.
 apply mult_add_l_assoc.
Qed.

Lemma mult_add_r_assoc : forall x y z w : nat,
  (x + y + z) * w = x * w + (y * w + z * w).
Proof.
 intros x y z w.
 rewrite mult_add_distr_r.
 rewrite mult_add_distr_r.
 rewrite add_assoc.
 reflexivity.
Qed.

Lemma mult_add_r_assoc_rev : forall x y z w : nat,
  x * w + (y * w + z * w) = (x + y + z) * w.
Proof.
 intros x y z w.
 symmetry.
 apply mult_add_r_assoc.
Qed.

Lemma mult_succ_l_alt : forall x y : nat, S x * y = x * y + y.
Proof.
 intros x y.
 apply mult_succ_l_add.
Qed.

Lemma mult_succ_r_alt : forall x y : nat, x * S y = x * y + x.
Proof.
 intros x y.
 apply mult_succ_r_add.
Qed.

Lemma mult_three_l_flat : forall x : nat,
  S (S (S O)) * x = x + x + x.
Proof.
 intros x.
 rewrite mult_3_l.
 rewrite add_assoc.
 reflexivity.
Qed.

Lemma mult_three_r_flat : forall x : nat,
  x * S (S (S O)) = x + x + x.
Proof.
 intros x.
 rewrite mult_3_r.
 rewrite add_assoc.
 reflexivity.
Qed.

Lemma mult_self_plus_one_l : forall x : nat,
  x * (x + S O) = x + x * x.
Proof.
 intros x.
 rewrite mult_add_distr_l.
 rewrite mult_1_r.
 rewrite add_comm.
 reflexivity.
Qed.

Lemma mult_one_plus_self_l : forall x : nat,
  (S O + x) * x = x + x * x.
Proof.
 intros x.
 rewrite (add_comm (S O) x).
 rewrite mult_add_distr_r.
 rewrite mult_1_l.
 rewrite add_comm.
 reflexivity.
Qed.

Lemma mult_6_l : forall x : nat,
  S (S (S (S (S (S O))))) * x = x + (x + (x + (x + (x + x)))).
Proof.
 intros x.
 rewrite mult_succ_l.
 rewrite mult_5_l.
 reflexivity.
Qed.

Lemma mult_6_r : forall x : nat,
  x * S (S (S (S (S (S O))))) = x + (x + (x + (x + (x + x)))).
Proof.
 intros x.
 rewrite mult_succ_r.
 rewrite mult_5_r.
 reflexivity.
Qed.

Lemma mult_7_l : forall x : nat,
  S (S (S (S (S (S (S O)))))) * x = x + (x + (x + (x + (x + (x + x))))).
Proof.
 intros x.
 rewrite mult_succ_l.
 rewrite mult_6_l.
 reflexivity.
Qed.

Lemma mult_7_r : forall x : nat,
  x * S (S (S (S (S (S (S O)))))) = x + (x + (x + (x + (x + (x + x))))).
Proof.
 intros x.
 rewrite mult_succ_r.
 rewrite mult_6_r.
 reflexivity.
Qed.

Lemma mult_8_l : forall x : nat,
  S (S (S (S (S (S (S (S O))))))) * x = x + (x + (x + (x + (x + (x + (x + x)))))).
Proof.
 intros x.
 rewrite mult_succ_l.
 rewrite mult_7_l.
 reflexivity.
Qed.

Lemma mult_8_r : forall x : nat,
  x * S (S (S (S (S (S (S (S O))))))) = x + (x + (x + (x + (x + (x + (x + x)))))).
Proof.
 intros x.
 rewrite mult_succ_r.
 rewrite mult_7_r.
 reflexivity.
Qed.

Lemma mult_9_l : forall x : nat,
  S (S (S (S (S (S (S (S (S O)))))))) * x =
  x + (x + (x + (x + (x + (x + (x + (x + x))))))).
Proof.
 intros x.
 rewrite mult_succ_l.
 rewrite mult_8_l.
 reflexivity.
Qed.

Lemma mult_9_r : forall x : nat,
  x * S (S (S (S (S (S (S (S (S O)))))))) =
  x + (x + (x + (x + (x + (x + (x + (x + x))))))).
Proof.
 intros x.
 rewrite mult_succ_r.
 rewrite mult_8_r.
 reflexivity.
Qed.

Lemma mult_10_l : forall x : nat,
  S (S (S (S (S (S (S (S (S (S O))))))))) * x =
  x + (x + (x + (x + (x + (x + (x + (x + (x + x)))))))).
Proof.
 intros x.
 rewrite mult_succ_l.
 rewrite mult_9_l.
 reflexivity.
Qed.

Lemma mult_10_r : forall x : nat,
  x * S (S (S (S (S (S (S (S (S (S O))))))))) =
  x + (x + (x + (x + (x + (x + (x + (x + (x + x)))))))).
Proof.
 intros x.
 rewrite mult_succ_r.
 rewrite mult_9_r.
 reflexivity.
Qed.

Lemma mult_11_l : forall x : nat,
  S (S (S (S (S (S (S (S (S (S (S O)))))))))) * x =
  x + (x + (x + (x + (x + (x + (x + (x + (x + (x + x))))))))).
Proof.
 intros x.
 rewrite mult_succ_l.
 rewrite mult_10_l.
 reflexivity.
Qed.

Lemma mult_11_r : forall x : nat,
  x * S (S (S (S (S (S (S (S (S (S (S O)))))))))) =
  x + (x + (x + (x + (x + (x + (x + (x + (x + (x + x))))))))).
Proof.
 intros x.
 rewrite mult_succ_r.
 rewrite mult_10_r.
 reflexivity.
Qed.

Lemma mult_12_l : forall x : nat,
  S (S (S (S (S (S (S (S (S (S (S (S O))))))))))) * x =
  x + (x + (x + (x + (x + (x + (x + (x + (x + (x + (x + x)))))))))).
Proof.
 intros x.
 rewrite mult_succ_l.
 rewrite mult_11_l.
 reflexivity.
Qed.

Lemma mult_12_r : forall x : nat,
  x * S (S (S (S (S (S (S (S (S (S (S (S O))))))))))) =
  x + (x + (x + (x + (x + (x + (x + (x + (x + (x + (x + x)))))))))).
Proof.
 intros x.
 rewrite mult_succ_r.
 rewrite mult_11_r.
 reflexivity.
Qed.

Lemma mult_13_l : forall x : nat,
  S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))) * x =
  x + (x + (x + (x + (x + (x + (x + (x + (x + (x + (x + (x + x))))))))))).
Proof.
 intros x.
 rewrite mult_succ_l.
 rewrite mult_12_l.
 reflexivity.
Qed.

Lemma mult_13_r : forall x : nat,
  x * S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))) =
  x + (x + (x + (x + (x + (x + (x + (x + (x + (x + (x + (x + x))))))))))).
Proof.
 intros x.
 rewrite mult_succ_r.
 rewrite mult_12_r.
 reflexivity.
Qed.