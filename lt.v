Require Import def.
Require Import le.
Require Import add.
Require Import mult.

Lemma lt_add_one : forall x : nat, x < x + S O.
Proof.
 intros x.
 unfold lt.
 rewrite add_succ_r.
 rewrite add_0_r.
 apply le_refl_rule.
Qed.

Lemma lt_succ_r : forall x y : nat, x < y -> x < S y.
Proof.
 intros x y H.
 unfold lt in *.
 apply le_step_rule.
 exact H.
Qed.

Lemma lt_irrefl : forall x : nat, ~ (x < x).
Proof.
 intros x H.
 unfold lt in H.
 apply (le_succ_not_le x).
 exact H.
Qed.

Lemma lt_succ : forall x : nat, x < S x.
Proof.
 intros x.
 unfold lt.
 apply le_refl.
Qed.

Lemma lt_le : forall x y : nat, x < y -> x <= y.
Proof.
 intros x y H.
 unfold lt in H.
 eapply le_trans.
 - apply le_step.
   apply le_refl.
 - exact H.
Qed.

Lemma le_lt_succ : forall x y : nat, x <= y -> x < S y.
Proof.
 intros x y H.
 unfold lt.
 apply le_succ_mono.
 exact H.
Qed.

Lemma lt_trans : forall x y z : nat, x < y -> y < z -> x < z.
Proof.
 intros x y z Hxy Hyz.
 unfold lt in *.
 eapply le_trans.
 - eapply le_trans.
   + exact Hxy.
   + apply le_step.
     apply le_refl.
 - exact Hyz.
Qed.

Lemma le_lt_or_eq : forall x y : nat, x <= y -> x < y \/ x = y.
Proof.
 intros x y H.
 induction H as [x | x y Hxy IH].
 - right.
   reflexivity.
 - destruct IH as [Hlt | Heq].
   + left.
     unfold lt in *.
     apply le_step.
     exact Hlt.
   + subst y.
     left.
     unfold lt.
     apply le_refl.
Qed.

Lemma lt_succ_cases : forall x y : nat, x < S y -> x < y \/ x = y.
Proof.
 intros x y H.
 unfold lt in H.
 apply le_succ_inv in H.
 apply le_lt_or_eq.
 exact H.
Qed.

Lemma lt_asymm : forall x y : nat, x < y -> y < x -> False.
Proof.
 intros x y Hxy Hyx.
 apply (lt_irrefl x).
 eapply lt_trans.
 - exact Hxy.
 - exact Hyx.
Qed.

Lemma lt_le_trans : forall x y z : nat, x < y -> y <= z -> x < z.
Proof.
 intros x y z Hxy Hyz.
 unfold lt in *.
 eapply le_trans.
 - exact Hxy.
 - exact Hyz.
Qed.

Lemma le_lt_trans : forall x y z : nat, x <= y -> y < z -> x < z.
Proof.
 intros x y z Hxy Hyz.
 unfold lt in *.
 eapply le_trans.
 - apply le_succ_mono.
   exact Hxy.
 - exact Hyz.
Qed.

Lemma ge_lt_trans : forall x y z : nat, x >= y -> x < z -> y < z.
Proof.
 intros x y z Hge Hlt.
 unfold ge, lt in *.
 eapply le_trans.
 - apply le_succ_mono.
   exact Hge.
 - exact Hlt.
Qed.

Lemma gt_le_trans : forall x y z : nat, x > y -> x <= z -> y < z.
Proof.
 intros x y z Hgt Hle.
 unfold gt, lt in *.
 eapply le_trans.
 - exact Hgt.
 - exact Hle.
Qed.

Lemma gt_lt_upper_bound_trans : forall x y z : nat, x > y -> x < z -> y < z.
Proof.
 intros x y z Hgt Hlt.
 unfold gt, lt in *.
 apply le_succ_lower in Hlt.
 eapply le_trans.
 - exact Hgt.
 - exact Hlt.
Qed.

Lemma le_lt_trans_rev : forall x y z : nat, x < y -> z <= x -> z < y.
Proof.
 intros x y z Hxy Hzx.
 unfold lt in *.
 eapply le_trans.
 - apply le_succ_mono.
   exact Hzx.
 - exact Hxy.
Qed.

Lemma lt_zero_false : forall x : nat, ~ (x < O).
Proof.
 intros x H.
 unfold lt in H.
 apply le_zero_inv in H.
 discriminate H.
Qed.

Lemma lt_succ_iff : forall x y : nat, x < S y <-> x <= y.
Proof.
 intros x y.
 unfold lt.
 split.
 - apply le_succ_inv.
 - apply le_succ_mono.
Qed.

Lemma lt_succ_succ_iff : forall x y : nat,
  S x < S y <-> x < y.
Proof.
 intros x y.
 unfold lt.
 split.
 - apply le_succ_inv.
 - apply le_succ_mono.
Qed.

Lemma lt_neq : forall x y : nat, x < y -> x <> y.
Proof.
 intros x y H Heq.
 subst y.
 apply (lt_irrefl x).
 exact H.
Qed.

Lemma lt_iff_le_and_neq : forall x y : nat,
  x < y <-> x <= y /\ x <> y.
Proof.
 intros x y.
 split.
 - intros H.
   split.
   + apply lt_le.
     exact H.
   + apply lt_neq.
     exact H.
 - intros [Hle Hneq].
   destruct (le_lt_or_eq x y Hle) as [Hlt | Heq].
   + exact Hlt.
   + exfalso.
     apply Hneq.
     exact Heq.
Qed.

Lemma lt_not_le : forall x y : nat, x < y -> ~ (y <= x).
Proof.
 intros x y Hlt Hle.
 unfold lt in Hlt.
 apply (le_succ_not_le x).
 eapply le_trans.
 - exact Hlt.
 - exact Hle.
Qed.

Lemma lt_succ_left : forall x y : nat, S x < y -> x < y.
Proof.
 intros x y H.
 unfold lt in *.
 apply le_succ_lower in H.
 exact H.
Qed.

Lemma lt_succ_right : forall x y : nat, x < y -> x < S y.
Proof.
 intros x y H.
 unfold lt in *.
 apply le_step.
 exact H.
Qed.

Lemma lt_one_iff : forall x : nat, x < S O <-> x = O.
Proof.
 intros x.
 split.
 - intros H.
   unfold lt in H.
   apply le_succ_inv in H.
   apply le_zero_inv in H.
   exact H.
 - intros H.
   rewrite H.
   unfold lt.
   apply le_refl.
Qed.

Lemma lt_two_iff : forall x : nat, x < S (S O) <-> x = O \/ x = S O.
Proof.
 intros x.
 split.
 - intros H.
   unfold lt in H.
   pose proof (@le_succ_inv x (S O) H) as Hle.
   apply (@le_succ_cases x O) in Hle.
   destruct Hle as [Hlower | Hsucc].
   + left.
     apply le_zero_inv.
     exact Hlower.
   + right.
     exact Hsucc.
 - intros [H | H].
   + rewrite H.
     unfold lt.
     apply le_step.
     apply le_refl.
   + rewrite H.
     unfold lt.
     apply le_refl.
Qed.

Lemma lt_three_iff : forall x : nat,
  x < S (S (S O)) <-> x = O \/ x = S O \/ x = S (S O).
Proof.
 intros x.
 split.
 - intros H.
   unfold lt in H.
   pose proof (@le_succ_inv x (S (S O)) H) as Hle.
   apply (@le_succ_cases x (S O)) in Hle.
   destruct Hle as [Hlower | Hmiddle].
   + apply le_succ_cases in Hlower.
     destruct Hlower as [Hzero | Hone].
     * left.
       apply le_zero_inv.
       exact Hzero.
     * right.
       left.
       exact Hone.
   + right.
     right.
     exact Hmiddle.
 - intros [H | [H | H]].
   + rewrite H.
     unfold lt.
     apply le_step.
     apply le_step.
     apply le_refl.
   + rewrite H.
     unfold lt.
     apply le_step.
     apply le_refl.
   + rewrite H.
     unfold lt.
     apply le_refl.
Qed.

Lemma lt_add_mono_l : forall x y z : nat, x < y -> z + x < z + y.
Proof.
 intros x y z H.
 unfold lt in *.
 rewrite <- add_succ_r.
 apply le_add_mono_l.
 exact H.
Qed.

Lemma lt_add_mono_r : forall x y z : nat, x < y -> x + z < y + z.
Proof.
 intros x y z H.
 rewrite (add_comm x z).
 rewrite (add_comm y z).
 apply lt_add_mono_l.
 exact H.
Qed.

Lemma lt_add_mono : forall x y z w : nat,
  x < y -> z < w -> x + z < y + w.
Proof.
 intros x y z w Hxy Hzw.
 unfold lt in *.
 rewrite <- add_succ_l.
 apply le_add_mono.
 - exact Hxy.
 - apply lt_le.
   exact Hzw.
Qed.

Lemma lt_add_lt_le : forall x y z w : nat,
  x < y -> z <= w -> x + z < y + w.
Proof.
 intros x y z w Hxy Hzw.
 unfold lt in *.
 rewrite <- add_succ_l.
 apply le_add_mono.
 - exact Hxy.
 - exact Hzw.
Qed.

Lemma lt_add_le_lt : forall x y z w : nat,
  x <= y -> z < w -> x + z < y + w.
Proof.
 intros x y z w Hxy Hzw.
 unfold lt in *.
 rewrite <- add_succ_r.
 apply le_add_mono.
 - exact Hxy.
 - exact Hzw.
Qed.

Lemma lt_add_extend : forall x y z : nat, x < y -> x < y + z.
Proof.
 intros x y z H.
 eapply lt_le_trans.
 - exact H.
 - apply le_add_l.
Qed.

Lemma lt_add_self_iff : forall x y : nat, x < x + y <-> y <> O.
Proof.
 intros x y.
 split.
 - intros H Hy.
   subst y.
   rewrite add_0_r in H.
   apply (lt_irrefl x).
   exact H.
 - intros Hy.
   destruct y as [| y].
   + contradiction.
   + unfold lt.
     rewrite add_succ_r.
     apply le_succ_mono.
     apply le_add_l.
Qed.

Lemma lt_self_add_iff : forall x y : nat, y < x + y <-> x <> O.
Proof.
 intros x y.
 rewrite (add_comm x y).
 apply lt_add_self_iff.
Qed.

Lemma lt_add_cancel_l : forall x y z : nat,
  x + y < x + z -> y < z.
Proof.
 intros x y z H.
 unfold lt in *.
 rewrite <- add_succ_r in H.
 apply (le_add_cancel_l x (S y) z).
 exact H.
Qed.

Lemma lt_add_cancel_r : forall x y z : nat,
  x + z < y + z -> x < y.
Proof.
 intros x y z H.
 rewrite (add_comm x z) in H.
 rewrite (add_comm y z) in H.
 apply (lt_add_cancel_l z x y).
 exact H.
Qed.

Lemma lt_mult_one_l_iff : forall x y : nat,
  S O * x < S O * y <-> x < y.
Proof.
 intros x y.
 rewrite mult_1_l.
 rewrite mult_1_l.
 split; intros H; exact H.
Qed.

Lemma lt_mult_one_r_iff : forall x y : nat,
  x * S O < y * S O <-> x < y.
Proof.
 intros x y.
 rewrite mult_1_r.
 rewrite mult_1_r.
 split; intros H; exact H.
Qed.

Lemma lt_mult_mono_l : forall x y z : nat,
  x < y -> z <> O -> z * x < z * y.
Proof.
 intros x y z Hxy Hz.
 destruct z as [| z].
 - contradiction.
 - rewrite mult_succ_l.
   rewrite mult_succ_l.
   apply lt_add_lt_le.
   + exact Hxy.
   + apply le_mult_mono_r.
     apply lt_le.
     exact Hxy.
Qed.

Lemma lt_mult_mono_r : forall x y z : nat,
  x < y -> z <> O -> x * z < y * z.
Proof.
 intros x y z Hxy Hz.
 rewrite (mult_comm x z).
 rewrite (mult_comm y z).
 apply lt_mult_mono_l.
 - exact Hxy.
 - exact Hz.
Qed.

Lemma lt_succ_mono_three : forall x y : nat,
  x < y -> S (S (S x)) < S (S (S y)).
Proof.
 intros x y H.
 unfold lt in *.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma lt_succ_mono_four : forall x y : nat,
  x < y -> S (S (S (S x))) < S (S (S (S y))).
Proof.
 intros x y H.
 unfold lt in *.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma lt_succ_mono_five : forall x y : nat,
  x < y -> S (S (S (S (S x)))) < S (S (S (S (S y)))).
Proof.
 intros x y H.
 unfold lt in *.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma lt_succ_mono_six : forall x y : nat,
  x < y -> S (S (S (S (S (S x))))) < S (S (S (S (S (S y))))).
Proof.
 intros x y H.
 unfold lt in *.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma lt_succ_mono_seven : forall x y : nat,
  x < y -> S (S (S (S (S (S (S x)))))) < S (S (S (S (S (S (S y)))))).
Proof.
 intros x y H.
 unfold lt in *.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma lt_succ_mono_three_iff : forall x y : nat,
  S (S (S x)) < S (S (S y)) <-> x < y.
Proof.
 intros x y.
 unfold lt.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma lt_succ_mono_four_iff : forall x y : nat,
  S (S (S (S x))) < S (S (S (S y))) <-> x < y.
Proof.
 intros x y.
 unfold lt.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma lt_succ_mono_five_iff : forall x y : nat,
  S (S (S (S (S x)))) < S (S (S (S (S y)))) <-> x < y.
Proof.
 intros x y.
 unfold lt.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma lt_succ_mono_six_iff : forall x y : nat,
  S (S (S (S (S (S x))))) < S (S (S (S (S (S y))))) <-> x < y.
Proof.
 intros x y.
 unfold lt.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma lt_succ_mono_seven_iff : forall x y : nat,
  S (S (S (S (S (S (S x)))))) < S (S (S (S (S (S (S y)))))) <-> x < y.
Proof.
 intros x y.
 unfold lt.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma lt_succ_mono_eight : forall x y : nat,
  x < y -> S (S (S (S (S (S (S (S x))))))) < S (S (S (S (S (S (S (S y))))))).
Proof.
 intros x y H.
 unfold lt in *.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma lt_succ_mono_nine : forall x y : nat,
  x < y -> S (S (S (S (S (S (S (S (S x)))))))) < S (S (S (S (S (S (S (S (S y)))))))).
Proof.
 intros x y H.
 unfold lt in *.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma lt_succ_mono_ten : forall x y : nat,
  x < y -> S (S (S (S (S (S (S (S (S (S x))))))))) < S (S (S (S (S (S (S (S (S (S y))))))))).
Proof.
 intros x y H.
 unfold lt in *.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma lt_succ_mono_eleven : forall x y : nat,
  x < y -> S (S (S (S (S (S (S (S (S (S (S x)))))))))) < S (S (S (S (S (S (S (S (S (S (S y)))))))))).
Proof.
 intros x y H.
 unfold lt in *.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma lt_succ_mono_twelve : forall x y : nat,
  x < y -> S (S (S (S (S (S (S (S (S (S (S (S x))))))))))) < S (S (S (S (S (S (S (S (S (S (S (S y))))))))))).
Proof.
 intros x y H.
 unfold lt in *.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma lt_succ_mono_eight_iff : forall x y : nat,
  S (S (S (S (S (S (S (S x))))))) < S (S (S (S (S (S (S (S y))))))) <-> x < y.
Proof.
 intros x y.
 unfold lt.
 split; intros H.
 - repeat apply le_succ_inv in H.
   exact H.
 - repeat apply le_succ_mono.
   exact H.
Qed.

Lemma lt_succ_mono_nine_iff : forall x y : nat,
  S (S (S (S (S (S (S (S (S x)))))))) < S (S (S (S (S (S (S (S (S y)))))))) <-> x < y.
Proof.
 intros x y.
 unfold lt.
 split; intros H.
 - repeat apply le_succ_inv in H.
   exact H.
 - repeat apply le_succ_mono.
   exact H.
Qed.

Lemma lt_succ_mono_ten_iff : forall x y : nat,
  S (S (S (S (S (S (S (S (S (S x))))))))) < S (S (S (S (S (S (S (S (S (S y))))))))) <-> x < y.
Proof.
 intros x y.
 unfold lt.
 split; intros H.
 - repeat apply le_succ_inv in H.
   exact H.
 - repeat apply le_succ_mono.
   exact H.
Qed.

Lemma lt_succ_mono_eleven_iff : forall x y : nat,
  S (S (S (S (S (S (S (S (S (S (S x)))))))))) < S (S (S (S (S (S (S (S (S (S (S y)))))))))) <-> x < y.
Proof.
 intros x y.
 unfold lt.
 split; intros H.
 - repeat apply le_succ_inv in H.
   exact H.
 - repeat apply le_succ_mono.
   exact H.
Qed.

Lemma lt_succ_mono_twelve_iff : forall x y : nat,
  S (S (S (S (S (S (S (S (S (S (S (S x))))))))))) < S (S (S (S (S (S (S (S (S (S (S (S y))))))))))) <-> x < y.
Proof.
 intros x y.
 unfold lt.
 split; intros H.
 - repeat apply le_succ_inv in H.
   exact H.
 - repeat apply le_succ_mono.
   exact H.
Qed.

Lemma lt_add_one_right_iff : forall x y : nat,
  x + S O < y + S O <-> x < y.
Proof.
 intros x y.
 repeat rewrite add_succ_r.
 repeat rewrite add_0_r.
 repeat apply lt_succ_succ_iff.
Qed.

Lemma lt_add_two_right_iff : forall x y : nat,
  x + S (S O) < y + S (S O) <-> x < y.
Proof.
 intros x y.
 repeat rewrite add_succ_r.
 repeat rewrite add_0_r.
 unfold lt.
 split; intros H.
 - repeat apply le_succ_inv in H.
   exact H.
 - repeat apply le_succ_mono.
   exact H.
Qed.

Lemma lt_add_three_right_iff : forall x y : nat,
  x + S (S (S O)) < y + S (S (S O)) <-> x < y.
Proof.
 intros x y.
 repeat rewrite add_succ_r.
 repeat rewrite add_0_r.
 apply lt_succ_mono_three_iff.
Qed.

Lemma lt_add_four_right_iff : forall x y : nat,
  x + S (S (S (S O))) < y + S (S (S (S O))) <-> x < y.
Proof.
 intros x y.
 repeat rewrite add_succ_r.
 repeat rewrite add_0_r.
 apply lt_succ_mono_four_iff.
Qed.

Lemma lt_add_five_right_iff : forall x y : nat,
  x + S (S (S (S (S O)))) < y + S (S (S (S (S O)))) <-> x < y.
Proof.
 intros x y.
 repeat rewrite add_succ_r.
 repeat rewrite add_0_r.
 apply lt_succ_mono_five_iff.
Qed.

Lemma lt_add_one_left_iff : forall x y : nat,
  S O + x < S O + y <-> x < y.
Proof.
 intros x y.
 rewrite (add_comm (S O) x).
 rewrite (add_comm (S O) y).
 apply lt_add_one_right_iff.
Qed.

Lemma lt_add_two_left_iff : forall x y : nat,
  S (S O) + x < S (S O) + y <-> x < y.
Proof.
 intros x y.
 rewrite (add_comm (S (S O)) x).
 rewrite (add_comm (S (S O)) y).
 apply lt_add_two_right_iff.
Qed.

Lemma lt_add_three_left_iff : forall x y : nat,
  S (S (S O)) + x < S (S (S O)) + y <-> x < y.
Proof.
 intros x y.
 rewrite (add_comm (S (S (S O))) x).
 rewrite (add_comm (S (S (S O))) y).
 apply lt_add_three_right_iff.
Qed.

Lemma lt_add_four_left_iff : forall x y : nat,
  S (S (S (S O))) + x < S (S (S (S O))) + y <-> x < y.
Proof.
 intros x y.
 rewrite (add_comm (S (S (S (S O)))) x).
 rewrite (add_comm (S (S (S (S O)))) y).
 apply lt_add_four_right_iff.
Qed.

Lemma lt_add_five_left_iff : forall x y : nat,
  S (S (S (S (S O)))) + x < S (S (S (S (S O)))) + y <-> x < y.
Proof.
 intros x y.
 rewrite (add_comm (S (S (S (S (S O))))) x).
 rewrite (add_comm (S (S (S (S (S O))))) y).
 apply lt_add_five_right_iff.
Qed.

Lemma lt_mult_mono_l_iff : forall x y z : nat,
  z <> O -> (z * x < z * y <-> x < y).
Proof.
 intros x y z Hz.
 split.
 - intros H.
   destruct (le_total x y) as [Hle | Hle].
   + apply le_lt_or_eq in Hle.
     destruct Hle as [Hxy | Heq].
     * exact Hxy.
     * subst y.
       exfalso.
       apply (lt_irrefl (z * x)).
       exact H.
   + exfalso.
     apply (lt_not_le (z * x) (z * y) H).
     apply le_mult_mono_r.
     exact Hle.
 - intros Hxy.
   exact (@lt_mult_mono_l x y z Hxy Hz).
Qed.

Lemma lt_mult_mono_r_iff : forall x y z : nat,
  z <> O -> (x * z < y * z <-> x < y).
Proof.
 intros x y z Hz.
 rewrite (mult_comm x z).
 rewrite (mult_comm y z).
 apply lt_mult_mono_l_iff.
 exact Hz.
Qed.

Lemma lt_mult_increase_right_iff : forall x y z : nat,
  x * y < x * (y + z) <-> x <> O /\ z <> O.
Proof.
 intros x y z.
 split.
 - intros H.
   rewrite mult_add_distr_l in H.
   apply (proj1 (lt_add_self_iff (x * y) (x * z))) in H.
   apply (proj1 (mult_neq_O_iff x z)) in H.
   exact H.
 - intros [Hx Hz].
   assert (Hlt : x * y < x * y + x * z).
   { apply (proj2 (lt_add_self_iff (x * y) (x * z))).
     apply (proj2 (mult_neq_O_iff x z)).
     split; assumption. }
   rewrite mult_add_distr_l.
   exact Hlt.
Qed.

Lemma lt_mult_increase_left_iff : forall x y z : nat,
  x * y < (x + z) * y <-> z <> O /\ y <> O.
Proof.
 intros x y z.
 split.
 - intros H.
   rewrite mult_add_distr_r in H.
   apply (proj1 (lt_add_self_iff (x * y) (z * y))) in H.
   apply (proj1 (mult_neq_O_iff z y)) in H.
   tauto.
 - intros [Hx Hz].
   assert (Hlt : x * y < x * y + z * y).
   { apply (proj2 (lt_add_self_iff (x * y) (z * y))).
     apply (proj2 (mult_neq_O_iff z y)).
     tauto. }
   rewrite mult_add_distr_r.
   exact Hlt.
Qed.

Lemma lt_mult_add_product_r_iff : forall x y z w : nat,
  x * y < x * y + z * w <-> z <> O /\ w <> O.
Proof.
 intros x y z w.
 split.
 - intros H.
   apply (proj1 (lt_add_self_iff (x * y) (z * w))) in H.
   apply (proj1 (mult_neq_O_iff z w)) in H.
   exact H.
 - intros [Hz Hw].
   apply (proj2 (lt_add_self_iff (x * y) (z * w))).
   apply (proj2 (mult_neq_O_iff z w)).
   split; assumption.
Qed.

Lemma lt_mult_add_product_l_iff : forall x y z w : nat,
  x * y < z * w + x * y <-> z <> O /\ w <> O.
Proof.
 intros x y z w.
 rewrite (add_comm (z * w) (x * y)).
 apply lt_mult_add_product_r_iff.
Qed.

Lemma lt_mult_add_const_r_iff : forall x y z : nat,
  x * y < x * y + z <-> z <> O.
Proof.
 intros x y z.
 split.
 - apply (proj1 (lt_add_self_iff (x * y) z)).
 - apply (proj2 (lt_add_self_iff (x * y) z)).
Qed.

Lemma lt_mult_add_const_l_iff : forall x y z : nat,
  x * y < z + x * y <-> z <> O.
Proof.
 intros x y z.
 rewrite (add_comm z (x * y)).
 apply lt_mult_add_const_r_iff.
Qed.

Lemma lt_mult_mono_both_l : forall x y z w : nat,
  x < y -> z < w -> x * z < y * w.
Proof.
 intros x y z w Hxy Hzw.
 assert (Hy : y <> O).
 { intros Hy.
   subst y.
   apply (lt_zero_false x).
   exact Hxy. }
 eapply le_lt_trans.
 - apply le_mult_mono_l.
   apply lt_le.
   exact Hxy.
 - apply lt_mult_mono_l.
   + exact Hzw.
   + exact Hy.
Qed.

Lemma lt_mult_mono_both_r : forall x y z w : nat,
  x < y -> z < w -> z * x < w * y.
Proof.
 intros x y z w Hxy Hzw.
 rewrite (mult_comm z x).
 rewrite (mult_comm w y).
 apply lt_mult_mono_both_l; assumption.
Qed.

Lemma lt_mult_mono_left_factor : forall x y z w : nat,
  x < y -> z <= w -> z <> O -> x * z < y * w.
Proof.
 intros x y z w Hxy Hzw Hz.
 eapply lt_le_trans.
 - exact (@lt_mult_mono_r x y z Hxy Hz).
 - apply le_mult_mono_r.
   exact Hzw.
Qed.

Lemma lt_mult_mono_right_factor : forall x y z w : nat,
  x <= y -> z < w -> y <> O -> x * z < y * w.
Proof.
 intros x y z w Hxy Hzw Hy.
 eapply le_lt_trans.
 - apply le_mult_mono_l.
   exact Hxy.
 - exact (@lt_mult_mono_l z w y Hzw Hy).
Qed.

Lemma lt_mult_add_first_factor : forall x y z : nat,
  z <> O -> y <> O -> x * y < (x + z) * y.
Proof.
 intros x y z Hz Hy.
 apply lt_mult_mono_r.
 - apply lt_add_self_iff.
   exact Hz.
 - exact Hy.
Qed.

Lemma lt_mult_add_second_factor : forall x y z : nat,
  x <> O -> z <> O -> x * y < x * (y + z).
Proof.
 intros x y z Hx Hz.
 apply lt_mult_mono_l.
 - apply lt_add_self_iff.
   exact Hz.
 - exact Hx.
Qed.

Lemma lt_mult_add_two_left : forall x y z w : nat,
  z <> O -> y <> O -> x * y < ((x + z) + w) * y.
Proof.
 intros x y z w Hz Hy.
 eapply lt_le_trans with (y := (x + z) * y).
 - exact (@lt_mult_add_first_factor x y z Hz Hy).
 - apply le_mult_mono_l.
   apply le_add_l.
Qed.

Lemma lt_mult_add_two_right : forall x y z w : nat,
  x <> O -> z <> O -> x * y < x * ((y + z) + w).
Proof.
 intros x y z w Hx Hz.
 eapply lt_le_trans with (y := x * (y + z)).
 - exact (@lt_mult_add_second_factor x y z Hx Hz).
 - apply le_mult_mono_r.
   apply le_add_l.
Qed.

Lemma lt_mult_add_both_factors : forall x y z w : nat,
  z <> O -> y <> O -> x * y < (x + z) * (y + w).
Proof.
 intros x y z w Hz Hy.
 eapply lt_le_trans with (y := (x + z) * y).
 - exact (@lt_mult_add_first_factor x y z Hz Hy).
 - apply le_mult_mono_r.
   apply le_add_l.
Qed.

Lemma lt_mult_add_second_both_factors : forall x y z w : nat,
  x <> O -> w <> O -> x * y < (x + z) * (y + w).
Proof.
 intros x y z w Hx Hw.
 eapply le_lt_trans.
 - apply le_mult_mono_l.
   apply le_add_l.
 - apply lt_mult_mono_l.
   + apply lt_add_self_iff.
     exact Hw.
   + intros Heq.
     apply (proj1 (add_eq_O_iff x z)) in Heq.
     destruct Heq as [Heq _].
     apply Hx.
     exact Heq.
Qed.

Lemma lt_mult_add_extend_right : forall x y z w : nat,
  z <> O -> w <> O -> x * y < x * y + z * w.
Proof.
 intros x y z w Hz Hw.
 apply lt_mult_add_product_r_iff.
 split; assumption.
Qed.

Lemma lt_mult_add_extend_left : forall x y z w : nat,
  z <> O -> w <> O -> x * y < z * w + x * y.
Proof.
 intros x y z w Hz Hw.
 apply lt_mult_add_product_l_iff.
 split; assumption.
Qed.

Lemma lt_add_mono_four : forall a b c d e f g h : nat,
  a < b -> c < d -> e < f -> g < h ->
  ((a + c) + e) + g < ((b + d) + f) + h.
Proof.
 intros a b c d e f g h Hab Hcd Hef Hgh.
 apply lt_add_mono.
 - apply lt_add_mono.
   + apply lt_add_mono; assumption.
   + exact Hef.
 - exact Hgh.
Qed.

Lemma lt_add_mono_five : forall a b c d e f g h i j : nat,
  a < b -> c < d -> e < f -> g < h -> i < j ->
  ((((a + c) + e) + g) + i) < ((((b + d) + f) + h) + j).
Proof.
 intros a b c d e f g h i j Hab Hcd Hef Hgh Hij.
 apply lt_add_mono.
 - apply lt_add_mono_four; assumption.
 - exact Hij.
Qed.

Lemma lt_add_nested_surround_l : forall x y z w : nat,
  x < y -> (z + x) + w < (z + y) + w.
Proof.
 intros x y z w H.
 apply lt_add_mono_r.
 apply lt_add_mono_l.
 exact H.
Qed.

Lemma lt_add_nested_surround_r : forall x y z w : nat,
  x < y -> (x + z) + w < (y + z) + w.
Proof.
 intros x y z w H.
 apply lt_add_mono_r.
 apply lt_add_mono_r.
 exact H.
Qed.

Lemma lt_add_extend_twice_r : forall x y z w : nat,
  x < y -> x < (y + z) + w.
Proof.
 intros x y z w H.
 eapply lt_le_trans with (y := y + z).
 - eapply lt_le_trans.
   + exact H.
   + apply le_add_l.
 - apply le_add_l.
Qed.

Lemma lt_add_extend_twice_l : forall x y z w : nat,
  x < y -> x < (z + w) + y.
Proof.
 intros x y z w H.
 eapply lt_le_trans.
 - exact H.
 - apply le_add_r.
Qed.

Lemma lt_add_common_extension : forall x y z w : nat,
  x < y -> x + z < y + (z + w).
Proof.
 intros x y z w H.
 eapply lt_le_trans.
 - apply lt_add_mono_r.
   exact H.
 - apply le_add_mono_l.
   apply le_add_l.
Qed.

Lemma lt_add_common_prefix_extension : forall x y z w : nat,
  x < y -> z + x < (z + y) + w.
Proof.
 intros x y z w H.
 eapply lt_le_trans.
 - apply lt_add_mono_l.
   exact H.
 - apply le_add_l.
Qed.

Lemma lt_add_one_summand_extend : forall x y z w : nat,
  x < y -> z <= w -> x + z < y + (z + w).
Proof.
 intros x y z w Hxy Hzw.
 apply lt_add_lt_le.
 - exact Hxy.
 - apply le_add_l.
Qed.

Lemma lt_add_other_summand_extend : forall x y z w : nat,
  x <= y -> z < w -> x + z < (y + w) + x.
Proof.
 intros x y z w Hxy Hzw.
 eapply lt_le_trans with (y := y + w).
 - apply lt_add_le_lt; assumption.
 - apply le_add_l.
Qed.

Lemma lt_le_add_mult_mono_r : forall x y z w a : nat,
  x < y -> z <= w -> a <> O ->
  (x + z) * a < (y + w) * a.
Proof.
 intros x y z w a Hxy Hzw Ha.
 apply lt_mult_mono_r.
 - apply lt_add_lt_le; assumption.
 - exact Ha.
Qed.

Lemma lt_le_add_mult_mono_l : forall x y z w a : nat,
  x < y -> z <= w -> a <> O ->
  a * (x + z) < a * (y + w).
Proof.
 intros x y z w a Hxy Hzw Ha.
 apply lt_mult_mono_l.
 - apply lt_add_lt_le; assumption.
 - exact Ha.
Qed.

Lemma le_lt_add_mult_mono_r : forall x y z w a : nat,
  x <= y -> z < w -> a <> O ->
  (x + z) * a < (y + w) * a.
Proof.
 intros x y z w a Hxy Hzw Ha.
 apply lt_mult_mono_r.
 - apply lt_add_le_lt; assumption.
 - exact Ha.
Qed.

Lemma le_lt_add_mult_mono_l : forall x y z w a : nat,
  x <= y -> z < w -> a <> O ->
  a * (x + z) < a * (y + w).
Proof.
 intros x y z w a Hxy Hzw Ha.
 apply lt_mult_mono_l.
 - apply lt_add_le_lt; assumption.
 - exact Ha.
Qed.

Lemma lt_le_distributed_mult_add_r : forall x y z w a : nat,
  x < y -> z <= w -> a <> O ->
  x * a + z * a < y * a + w * a.
Proof.
 intros x y z w a Hxy Hzw Ha.
 apply lt_add_lt_le.
 - apply lt_mult_mono_r; assumption.
 - apply le_mult_mono_l.
   exact Hzw.
Qed.

Lemma lt_le_distributed_mult_add_l : forall x y z w a : nat,
  x < y -> z <= w -> a <> O ->
  a * x + a * z < a * y + a * w.
Proof.
 intros x y z w a Hxy Hzw Ha.
 apply lt_add_lt_le.
 - apply lt_mult_mono_l; assumption.
 - apply le_mult_mono_r.
   exact Hzw.
Qed.

Lemma le_lt_distributed_mult_add_r : forall x y z w a : nat,
  x <= y -> z < w -> a <> O ->
  x * a + z * a < y * a + w * a.
Proof.
 intros x y z w a Hxy Hzw Ha.
 apply lt_add_le_lt.
 - apply le_mult_mono_l.
   exact Hxy.
 - apply lt_mult_mono_r; assumption.
Qed.

Lemma le_lt_distributed_mult_add_l : forall x y z w a : nat,
  x <= y -> z < w -> a <> O ->
  a * x + a * z < a * y + a * w.
Proof.
 intros x y z w a Hxy Hzw Ha.
 apply lt_add_le_lt.
 - apply le_mult_mono_r.
   exact Hxy.
 - apply lt_mult_mono_l; assumption.
Qed.

Lemma lt_le_product_cross_left : forall x y z w : nat,
  x < y -> z <= w -> z <> O -> x * z < y * w.
Proof.
 intros x y z w Hxy Hzw Hz.
 apply lt_mult_mono_left_factor; assumption.
Qed.

Lemma le_lt_product_cross_left : forall x y z w : nat,
  x <= y -> z < w -> y <> O -> x * z < y * w.
Proof.
 intros x y z w Hxy Hzw Hy.
 apply lt_mult_mono_right_factor; assumption.
Qed.

Lemma lt_le_product_cross_right : forall x y z w : nat,
  x < y -> z <= w -> z <> O -> z * x < w * y.
Proof.
 intros x y z w Hxy Hzw Hz.
 rewrite (mult_comm z x).
 rewrite (mult_comm w y).
 apply lt_mult_mono_left_factor; assumption.
Qed.

Lemma le_lt_product_cross_right : forall x y z w : nat,
  x <= y -> z < w -> y <> O -> z * x < w * y.
Proof.
 intros x y z w Hxy Hzw Hy.
 rewrite (mult_comm z x).
 rewrite (mult_comm w y).
 apply lt_mult_mono_right_factor; assumption.
Qed.

Lemma lt_le_sum_product_extend_right : forall x y z w a b : nat,
  x < y -> z <= w -> a <> O ->
  (x + z) * a < (y + w) * a + b.
Proof.
 intros x y z w a b Hxy Hzw Ha.
 eapply lt_le_trans.
 - apply lt_le_add_mult_mono_r; assumption.
 - apply le_add_l.
Qed.

Lemma lt_le_sum_product_extend_left : forall x y z w a b : nat,
  x < y -> z <= w -> a <> O ->
  (x + z) * a < b + (y + w) * a.
Proof.
 intros x y z w a b Hxy Hzw Ha.
 eapply lt_le_trans.
 - apply lt_le_add_mult_mono_r; assumption.
 - apply le_add_r.
Qed.

Lemma le_lt_sum_product_extend_right : forall x y z w a b : nat,
  x <= y -> z < w -> a <> O ->
  a * (x + z) < a * (y + w) + b.
Proof.
 intros x y z w a b Hxy Hzw Ha.
 eapply lt_le_trans.
 - apply le_lt_add_mult_mono_l; assumption.
 - apply le_add_l.
Qed.

Lemma le_lt_sum_product_extend_left : forall x y z w a b : nat,
  x <= y -> z < w -> a <> O ->
  a * (x + z) < b + a * (y + w).
Proof.
 intros x y z w a b Hxy Hzw Ha.
 eapply lt_le_trans.
 - apply le_lt_add_mult_mono_l; assumption.
 - apply le_add_r.
Qed.

Lemma lt_le_distributed_product_extend_right : forall x y z w a b : nat,
  x < y -> z <= w -> a <> O ->
  x * a + z * a < y * a + w * a + b.
Proof.
 intros x y z w a b Hxy Hzw Ha.
 eapply lt_le_trans.
 - apply lt_le_distributed_mult_add_r; assumption.
 - apply le_add_l.
Qed.

Lemma lt_le_distributed_product_extend_left : forall x y z w a b : nat,
  x < y -> z <= w -> a <> O ->
  x * a + z * a < b + (y * a + w * a).
Proof.
 intros x y z w a b Hxy Hzw Ha.
 eapply lt_le_trans.
 - apply lt_le_distributed_mult_add_r; assumption.
 - apply le_add_r.
Qed.

Lemma le_lt_distributed_product_extend_right : forall x y z w a b : nat,
  x <= y -> z < w -> a <> O ->
  a * x + a * z < a * y + a * w + b.
Proof.
 intros x y z w a b Hxy Hzw Ha.
 eapply lt_le_trans.
 - apply le_lt_distributed_mult_add_l; assumption.
 - apply le_add_l.
Qed.

Lemma le_lt_distributed_product_extend_left : forall x y z w a b : nat,
  x <= y -> z < w -> a <> O ->
  a * x + a * z < b + (a * y + a * w).
Proof.
 intros x y z w a b Hxy Hzw Ha.
 eapply lt_le_trans.
 - apply le_lt_distributed_mult_add_l; assumption.
 - apply le_add_r.
Qed.