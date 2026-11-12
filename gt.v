Require Import def.
Require Import le.
Require Import lt.
Require Import ge.
Require Import add.
Require Import mult.

Lemma gt_irrefl : forall x : nat, ~ (x > x).
Proof.
 intros x H.
 unfold gt in H.
 apply (lt_irrefl x).
 exact H.
Qed.

Lemma gt_trans : forall x y z : nat, x > y -> y > z -> x > z.
Proof.
 intros x y z Hxy Hyz.
 unfold gt in *.
 eapply lt_trans.
 - exact Hyz.
 - exact Hxy.
Qed.

Lemma gt_trans_le : forall x y z : nat, x > y -> y >= z -> x > z.
Proof.
 intros x y z Hxy Hyz.
 unfold gt, ge in *.
 eapply le_lt_trans.
 - exact Hyz.
 - exact Hxy.
Qed.

Lemma gt_ge : forall x y : nat, x > y -> x >= y.
Proof.
 intros x y H.
 unfold gt in H.
 unfold ge.
 apply lt_le.
 exact H.
Qed.

Lemma ge_gt_trans : forall x y z : nat, x >= y -> y > z -> x > z.
Proof.
 intros x y z Hxy Hyz.
 unfold ge, gt, lt in *.
 eapply le_trans.
 - exact Hyz.
 - exact Hxy.
Qed.

Lemma gt_iff_ge_and_neq : forall x y : nat,
  x > y <-> x >= y /\ x <> y.
Proof.
 intros x y.
 split.
 - intros H.
   split.
   + apply gt_ge.
     exact H.
   + intros Heq.
     subst y.
     apply (gt_irrefl x).
     exact H.
 - intros [Hge Hneq].
   destruct (ge_gt_or_eq x y Hge) as [Hgt | Heq].
   + exact Hgt.
   + exfalso.
     apply Hneq.
     exact Heq.
Qed.

Lemma gt_succ : forall x : nat, S x > x.
Proof.
 intros x.
 unfold gt.
 apply lt_succ.
Qed.

Lemma gt_succ_left : forall x y : nat, S x > y -> x >= y.
Proof.
 intros x y H.
 unfold gt, lt, ge in H.
 apply le_succ_inv in H.
 exact H.
Qed.

Lemma gt_lt_iff : forall x y : nat, x > y <-> y < x.
Proof.
 intros x y.
 split; intros H; exact H.
Qed.

Lemma gt_asymm : forall x y : nat, x > y -> y > x -> False.
Proof.
 intros x y Hxy Hyx.
 unfold gt in *.
 apply (lt_asymm y x).
 - exact Hxy.
 - exact Hyx.
Qed.

Lemma gt_succ_lower : forall x y : nat, S x > S y -> x > y.
Proof.
 intros x y H.
 unfold gt in *.
 unfold lt in *.
 apply le_succ_inv in H.
 exact H.
Qed.

Lemma gt_succ_iff : forall x y : nat, S x > y <-> x >= y.
Proof.
 intros x y.
 unfold gt, lt, ge.
 split.
 - apply le_succ_inv.
 - apply le_succ_mono.
Qed.

Lemma gt_zero_iff : forall x : nat, x > O <-> x <> O.
Proof.
 intros x.
 unfold gt, lt.
 apply ge_one_iff.
Qed.

Lemma gt_neq : forall x y : nat, x > y -> x <> y.
Proof.
 intros x y H Heq.
 subst y.
 apply (gt_irrefl x).
 exact H.
Qed.

Lemma gt_not_le : forall x y : nat, x > y -> ~ (x <= y).
Proof.
 intros x y Hgt Hle.
 unfold gt in Hgt.
 exact (@lt_not_le y x Hgt Hle).
Qed.

Lemma gt_not_ge : forall x y : nat, x > y -> ~ (y >= x).
Proof.
 intros x y Hgt Hge.
 exact (@gt_not_le x y Hgt Hge).
Qed.

Lemma gt_succ_mono : forall x y : nat, x > y -> S x > S y.
Proof.
 intros x y H.
 unfold gt, lt in *.
 apply le_succ_mono.
 exact H.
Qed.

Lemma gt_succ_mono_two_iff : forall x y : nat,
  S (S x) > S (S y) <-> x > y.
Proof.
 intros x y.
 unfold gt, lt.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma gt_succ_mono_three_iff : forall x y : nat,
  S (S (S x)) > S (S (S y)) <-> x > y.
Proof.
 intros x y.
 unfold gt, lt.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma gt_succ_mono_four_iff : forall x y : nat,
  S (S (S (S x))) > S (S (S (S y))) <-> x > y.
Proof.
 intros x y.
 unfold gt, lt.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma gt_succ_mono_five_iff : forall x y : nat,
  S (S (S (S (S x)))) > S (S (S (S (S y)))) <-> x > y.
Proof.
 intros x y.
 unfold gt, lt.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma gt_succ_mono_six_iff : forall x y : nat,
  S (S (S (S (S (S x))))) > S (S (S (S (S (S y))))) <-> x > y.
Proof.
 intros x y.
 unfold gt, lt.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma gt_succ_mono_seven : forall x y : nat,
  x > y -> S (S (S (S (S (S (S x)))))) > S (S (S (S (S (S (S y)))))).
Proof.
 intros x y H.
 unfold gt, lt in *.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma gt_succ_mono_eight : forall x y : nat,
  x > y -> S (S (S (S (S (S (S (S x))))))) > S (S (S (S (S (S (S (S y))))))).
Proof.
 intros x y H.
 unfold gt, lt in *.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma gt_succ_mono_nine : forall x y : nat,
  x > y -> S (S (S (S (S (S (S (S (S x)))))))) > S (S (S (S (S (S (S (S (S y)))))))).
Proof.
 intros x y H.
 unfold gt, lt in *.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma gt_succ_mono_ten : forall x y : nat,
  x > y -> S (S (S (S (S (S (S (S (S (S x))))))))) > S (S (S (S (S (S (S (S (S (S y))))))))).
Proof.
 intros x y H.
 unfold gt, lt in *.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma gt_succ_mono_eleven : forall x y : nat,
  x > y -> S (S (S (S (S (S (S (S (S (S (S x)))))))))) > S (S (S (S (S (S (S (S (S (S (S y)))))))))).
Proof.
 intros x y H.
 unfold gt, lt in *.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma gt_succ_mono_seven_iff : forall x y : nat,
  S (S (S (S (S (S (S x)))))) > S (S (S (S (S (S (S y)))))) <-> x > y.
Proof.
 intros x y.
 unfold gt, lt.
 split; intros H.
 - repeat apply le_succ_inv in H.
   exact H.
 - repeat apply le_succ_mono.
   exact H.
Qed.

Lemma gt_succ_mono_eight_iff : forall x y : nat,
  S (S (S (S (S (S (S (S x))))))) > S (S (S (S (S (S (S (S y))))))) <-> x > y.
Proof.
 intros x y.
 unfold gt, lt.
 split; intros H.
 - repeat apply le_succ_inv in H.
   exact H.
 - repeat apply le_succ_mono.
   exact H.
Qed.

Lemma gt_succ_mono_nine_iff : forall x y : nat,
  S (S (S (S (S (S (S (S (S x)))))))) > S (S (S (S (S (S (S (S (S y)))))))) <-> x > y.
Proof.
 intros x y.
 unfold gt, lt.
 split; intros H.
 - repeat apply le_succ_inv in H.
   exact H.
 - repeat apply le_succ_mono.
   exact H.
Qed.

Lemma gt_succ_mono_ten_iff : forall x y : nat,
  S (S (S (S (S (S (S (S (S (S x))))))))) > S (S (S (S (S (S (S (S (S (S y))))))))) <-> x > y.
Proof.
 intros x y.
 unfold gt, lt.
 split; intros H.
 - repeat apply le_succ_inv in H.
   exact H.
 - repeat apply le_succ_mono.
   exact H.
Qed.

Lemma gt_succ_mono_eleven_iff : forall x y : nat,
  S (S (S (S (S (S (S (S (S (S (S x)))))))))) > S (S (S (S (S (S (S (S (S (S (S y)))))))))) <-> x > y.
Proof.
 intros x y.
 unfold gt, lt.
 split; intros H.
 - repeat apply le_succ_inv in H.
   exact H.
 - repeat apply le_succ_mono.
   exact H.
Qed.

Lemma gt_succ_lower_iff : forall x y : nat,
	S x > S y <-> x > y.
Proof.
 intros x y.
 unfold gt, lt.
 apply le_succ_iff.
Qed.

Lemma gt_succ_right_inv : forall x y : nat, x > S y -> x > y.
Proof.
 intros x y H.
 unfold gt, lt in *.
 apply le_succ_lower in H.
 exact H.
Qed.

Lemma gt_one_iff : forall x : nat,
	x > S O <-> exists y : nat, x = S (S y).
Proof.
 intros x.
 change (x >= S (S O) <-> exists y : nat, x = S (S y)).
 apply ge_two_iff.
Qed.

Lemma gt_two_iff : forall x : nat,
	x > S (S O) <-> exists y : nat, x = S (S (S y)).
Proof.
 intros x.
 change (x >= S (S (S O)) <-> exists y : nat, x = S (S (S y))).
 apply ge_three_iff.
Qed.

Lemma gt_three_iff : forall x : nat,
  x > S (S (S O)) <-> exists y : nat, x = S (S (S (S y))).
Proof.
 intros x.
 apply ge_four_iff.
Qed.

Lemma gt_four_iff : forall x : nat,
  x > S (S (S (S O))) <-> exists y : nat, x = S (S (S (S (S y)))).
Proof.
 intros x.
 apply ge_five_iff.
Qed.

Lemma gt_five_iff : forall x : nat,
  x > S (S (S (S (S O)))) <-> exists y : nat, x = S (S (S (S (S (S y))))).
Proof.
 intros x.
 apply ge_six_iff.
Qed.

Lemma gt_six_iff : forall x : nat,
  x > S (S (S (S (S (S O))))) <-> exists y : nat, x = S (S (S (S (S (S (S y)))))).
Proof.
 intros x.
 apply ge_seven_iff.
Qed.

Lemma gt_seven_iff : forall x : nat,
  x > S (S (S (S (S (S (S O)))))) <-> exists y : nat, x = S (S (S (S (S (S (S (S y))))))).
Proof.
 intros x.
 apply ge_eight_iff.
Qed.

Lemma gt_eight_iff : forall x : nat,
  x > S (S (S (S (S (S (S (S O))))))) <-> exists y : nat, x = S (S (S (S (S (S (S (S (S y)))))))).
Proof.
 intros x.
 split.
 - intros H.
   destruct x as [| x].
   + unfold gt, lt in H.
     apply le_zero_inv in H.
     discriminate H.
   + unfold gt, lt in H.
     apply le_succ_inv in H.
     apply gt_seven_iff in H.
     destruct H as [y Hx].
     exists y.
     rewrite Hx.
     reflexivity.
 - intros [y Hx].
   rewrite Hx.
   unfold gt, lt.
   repeat apply le_succ_mono.
   apply le_zero_l.
Qed.

Lemma gt_nine_iff : forall x : nat,
  x > S (S (S (S (S (S (S (S (S O)))))))) <-> exists y : nat, x = S (S (S (S (S (S (S (S (S (S y))))))))).
Proof.
 intros x.
 split.
 - intros H.
   destruct x as [| x].
   + unfold gt, lt in H.
     apply le_zero_inv in H.
     discriminate H.
   + unfold gt, lt in H.
     apply le_succ_inv in H.
     apply gt_eight_iff in H.
     destruct H as [y Hx].
     exists y.
     rewrite Hx.
     reflexivity.
 - intros [y Hx].
   rewrite Hx.
   unfold gt, lt.
   repeat apply le_succ_mono.
   apply le_zero_l.
Qed.

Lemma gt_ten_iff : forall x : nat,
  x > S (S (S (S (S (S (S (S (S (S O))))))))) <-> exists y : nat, x = S (S (S (S (S (S (S (S (S (S (S y)))))))))).
Proof.
 intros x.
 split.
 - intros H.
   destruct x as [| x].
   + unfold gt, lt in H.
     apply le_zero_inv in H.
     discriminate H.
   + unfold gt, lt in H.
     apply le_succ_inv in H.
     apply gt_nine_iff in H.
     destruct H as [y Hx].
     exists y.
     rewrite Hx.
     reflexivity.
 - intros [y Hx].
   rewrite Hx.
   unfold gt, lt.
   repeat apply le_succ_mono.
   apply le_zero_l.
Qed.

Lemma gt_eleven_iff : forall x : nat,
  x > S (S (S (S (S (S (S (S (S (S (S O)))))))))) <-> exists y : nat, x = S (S (S (S (S (S (S (S (S (S (S (S y))))))))))).
Proof.
 intros x.
 split.
 - intros H.
   destruct x as [| x].
   + unfold gt, lt in H.
     apply le_zero_inv in H.
     discriminate H.
   + unfold gt, lt in H.
     apply le_succ_inv in H.
     apply gt_ten_iff in H.
     destruct H as [y Hx].
     exists y.
     rewrite Hx.
     reflexivity.
 - intros [y Hx].
   rewrite Hx.
   unfold gt, lt.
   repeat apply le_succ_mono.
   apply le_zero_l.
Qed.

Lemma gt_twelve_iff : forall x : nat,
  x > S (S (S (S (S (S (S (S (S (S (S (S O))))))))))) <->
  exists y : nat, x = S (S (S (S (S (S (S (S (S (S (S (S (S y)))))))))))).
Proof.
 intros x.
 split.
 - intros H.
   destruct x as [| x].
   + unfold gt, lt in H.
     apply le_zero_inv in H.
     discriminate H.
   + unfold gt, lt in H.
     apply le_succ_inv in H.
     apply gt_eleven_iff in H.
     destruct H as [y Hx].
     exists y.
     rewrite Hx.
     reflexivity.
 - intros [y Hx].
   rewrite Hx.
   unfold gt, lt.
   repeat apply le_succ_mono.
   apply le_zero_l.
Qed.

Lemma gt_add_mono_l : forall x y z : nat, x > y -> z + x > z + y.
Proof.
 intros x y z H.
 unfold gt in *.
 apply lt_add_mono_l.
 exact H.
Qed.

Lemma gt_add_mono_r : forall x y z : nat, x > y -> x + z > y + z.
Proof.
 intros x y z H.
 unfold gt in *.
 apply lt_add_mono_r.
 exact H.
Qed.

Lemma gt_add_mono : forall x y z w : nat,
	x > y -> z > w -> x + z > y + w.
Proof.
 intros x y z w Hxy Hzw.
 unfold gt in *.
 apply lt_add_mono.
 - exact Hxy.
 - exact Hzw.
Qed.

Lemma gt_add_mono_three : forall x y z u v w : nat,
  x > y -> z > u -> v > w ->
  (x + z) + v > (y + u) + w.
Proof.
 intros x y z u v w Hxy Hzu Hvw.
 eapply gt_add_mono.
 - apply gt_add_mono; assumption.
 - exact Hvw.
Qed.

Lemma gt_add_extend : forall x y z : nat, x > y -> x + z > y.
Proof.
 intros x y z H.
 unfold gt in *.
 eapply lt_le_trans.
 - exact H.
 - apply le_add_l.
Qed.

Lemma gt_add_self_iff : forall x y : nat, x + y > x <-> y <> O.
Proof.
 intros x y.
 unfold gt.
 apply lt_add_self_iff.
Qed.

Lemma gt_self_add_iff : forall x y : nat, x + y > y <-> x <> O.
Proof.
 intros x y.
 unfold gt.
 rewrite (add_comm x y).
 apply lt_add_self_iff.
Qed.

Lemma gt_add_cancel_l : forall x y z : nat,
  x + z > y + z -> x > y.
Proof.
 intros x y z H.
 unfold gt in *.
 apply (lt_add_cancel_r y x z).
 exact H.
Qed.

Lemma gt_add_cancel_r : forall x y z : nat,
  z + x > z + y -> x > y.
Proof.
 intros x y z H.
 unfold gt in *.
 apply (lt_add_cancel_l z y x).
 exact H.
Qed.

Lemma gt_add_cancel_l_iff : forall x y z : nat,
  x + z > y + z <-> x > y.
Proof.
 intros x y z.
 split.
 - apply gt_add_cancel_l.
 - intros H.
   apply gt_add_mono_r.
   exact H.
Qed.

Lemma gt_add_cancel_r_iff : forall x y z : nat,
  z + x > z + y <-> x > y.
Proof.
 intros x y z.
 split.
 - apply gt_add_cancel_r.
 - intros H.
   apply gt_add_mono_l.
   exact H.
Qed.

Lemma gt_mult_one_l_iff : forall x y : nat,
	S O * x > S O * y <-> x > y.
Proof.
 intros x y.
 rewrite mult_1_l.
 rewrite mult_1_l.
 split; intros H; exact H.
Qed.

Lemma gt_mult_one_r_iff : forall x y : nat,
	x * S O > y * S O <-> x > y.
Proof.
 intros x y.
 rewrite mult_1_r.
 rewrite mult_1_r.
 split; intros H; exact H.
Qed.

Lemma gt_mult_mono_l : forall x y z : nat,
	x > y -> z <> O -> z * x > z * y.
Proof.
 intros x y z Hxy Hz.
 destruct z as [| z].
 - contradiction.
 - unfold gt in *.
	 rewrite mult_succ_l.
	 rewrite mult_succ_l.
	 apply lt_add_lt_le.
	 + exact Hxy.
	 + apply le_mult_mono_r.
		 apply lt_le.
		 exact Hxy.
Qed.

Lemma gt_mult_mono_r : forall x y z : nat,
	x > y -> z <> O -> x * z > y * z.
Proof.
 intros x y z Hxy Hz.
 rewrite (mult_comm x z).
 rewrite (mult_comm y z).
 apply gt_mult_mono_l.
 - exact Hxy.
 - exact Hz.
Qed.

Lemma gt_mult_mono_l_iff : forall x y z : nat,
  z <> O -> (z * x > z * y <-> x > y).
Proof.
 intros x y z Hz.
 split.
 - intros H.
   destruct (le_total x y) as [Hle | Hle].
   + exfalso.
     apply (gt_not_le (z * x) (z * y) H).
     apply le_mult_mono_r.
     exact Hle.
   + apply le_lt_or_eq in Hle.
     destruct Hle as [Hxy | Heq].
     * exact Hxy.
     * subst y.
       exfalso.
       apply (gt_irrefl (z * x)).
       exact H.
 - intros Hxy.
   exact (@gt_mult_mono_l x y z Hxy Hz).
Qed.

Lemma gt_mult_mono_r_iff : forall x y z : nat,
  z <> O -> (x * z > y * z <-> x > y).
Proof.
 intros x y z Hz.
 rewrite (mult_comm x z).
 rewrite (mult_comm y z).
 apply gt_mult_mono_l_iff.
 exact Hz.
Qed.

Lemma lt_gt_trans : forall x y z : nat,
  x < y -> z > y -> z > x.
Proof.
 intros x y z Hxy Hzy.
 unfold gt in *.
 eapply lt_trans.
 - exact Hxy.
 - exact Hzy.
Qed.

Lemma gt_lt_trans : forall x y z : nat,
  x > y -> y > z -> z < x.
Proof.
 intros x y z Hxy Hyz.
 unfold gt in *.
 eapply lt_trans.
 - exact Hyz.
 - exact Hxy.
Qed.

Lemma lt_gt_add_mono : forall x y z : nat,
  x < y -> z + y > z + x.
Proof.
 intros x y z Hxy.
 unfold gt.
 apply lt_add_mono_l.
 exact Hxy.
Qed.

Lemma gt_lt_add_mono : forall x y z : nat,
  x > y -> z + x > z + y.
Proof.
 intros x y z Hxy.
 apply gt_add_mono_l.
 exact Hxy.
Qed.

Lemma lt_gt_add_cancel : forall x y z : nat,
  y + z > x + z -> x < y.
Proof.
 intros x y z H.
 apply gt_add_cancel_l in H.
 exact H.
Qed.

Lemma gt_lt_add_cancel : forall x y z : nat,
  z + x > z + y -> y < x.
Proof.
 intros x y z H.
 apply gt_add_cancel_r in H.
 exact H.
Qed.

Lemma lt_gt_mult_mono : forall x y z : nat,
  x < y -> z <> O -> z * y > z * x.
Proof.
 intros x y z Hxy Hz.
 unfold gt.
 apply lt_mult_mono_l; assumption.
Qed.

Lemma gt_lt_mult_mono : forall x y z : nat,
  x > y -> z <> O -> z * x > z * y.
Proof.
 intros x y z Hxy Hz.
 apply gt_mult_mono_l; assumption.
Qed.

Lemma lt_gt_mult_cancel : forall x y z : nat,
  z <> O -> (z * y > z * x <-> x < y).
Proof.
 intros x y z Hz.
 apply (gt_mult_mono_l_iff y x z Hz).
Qed.

Lemma gt_lt_mult_cancel : forall x y z : nat,
  z <> O -> (z * x > z * y <-> y < x).
Proof.
 intros x y z Hz.
 apply (gt_mult_mono_l_iff x y z Hz).
Qed.

Lemma lt_gt_add_mult_mono_l : forall x y z w a : nat,
  x < y -> w > z -> a <> O ->
  (x + z) * a < (y + w) * a.
Proof.
 intros x y z w a Hxy Hwz Ha.
 assert (Hsum : x + z < y + w).
 { apply lt_add_mono.
   - exact Hxy.
   - unfold gt in Hwz.
     exact Hwz. }
 apply lt_mult_mono_r; assumption.
Qed.

Lemma lt_gt_add_mult_mono_r : forall x y z w a : nat,
  x < y -> w > z -> a <> O ->
  a * (x + z) < a * (y + w).
Proof.
 intros x y z w a Hxy Hwz Ha.
 assert (Hsum : x + z < y + w).
 { apply lt_add_mono.
   - exact Hxy.
   - unfold gt in Hwz.
     exact Hwz. }
 apply lt_mult_mono_l; assumption.
Qed.

Lemma gt_lt_add_mult_mono_l : forall x y z w a : nat,
  x < y -> w > z -> a <> O ->
  (y + w) * a > (x + z) * a.
Proof.
 intros x y z w a Hxy Hwz Ha.
 apply lt_gt_add_mult_mono_l; assumption.
Qed.

Lemma gt_lt_add_mult_mono_r : forall x y z w a : nat,
  x < y -> w > z -> a <> O ->
  a * (y + w) > a * (x + z).
Proof.
 intros x y z w a Hxy Hwz Ha.
 apply lt_gt_add_mult_mono_r; assumption.
Qed.

Lemma lt_gt_product_cross_mono : forall x y z w : nat,
  x < y -> w > z -> z <> O -> x * z < y * w.
Proof.
 intros x y z w Hxy Hwz Hz.
 eapply lt_le_trans.
 - exact (@lt_mult_mono_r x y z Hxy Hz).
 - apply le_mult_mono_r.
   apply lt_le.
   unfold gt in Hwz.
   exact Hwz.
Qed.

Lemma gt_lt_product_cross_mono : forall x y z w : nat,
  x < y -> w > z -> z <> O -> y * w > x * z.
Proof.
 intros x y z w Hxy Hwz Hz.
 apply lt_gt_product_cross_mono; assumption.
Qed.

Lemma lt_gt_distributed_mult_add : forall x y z w a : nat,
  x < y -> w > z -> a <> O ->
  x * a + z * a < y * a + w * a.
Proof.
 intros x y z w a Hxy Hwz Ha.
 apply lt_add_mono.
 - apply lt_mult_mono_r; assumption.
 - apply lt_mult_mono_r.
   + unfold gt in Hwz.
     exact Hwz.
   + exact Ha.
Qed.

Lemma gt_lt_distributed_mult_add : forall x y z w a : nat,
  x < y -> w > z -> a <> O ->
  y * a + w * a > x * a + z * a.
Proof.
 intros x y z w a Hxy Hwz Ha.
 apply lt_gt_distributed_mult_add; assumption.
Qed.

Lemma lt_gt_add_mult_cancel_l : forall x y z a : nat,
  a <> O -> ((y + z) * a > (x + z) * a <-> x < y).
Proof.
 intros x y z a Ha.
 split.
 - intros H.
   apply (lt_mult_mono_r_iff (x + z) (y + z) a Ha) in H.
   apply lt_add_cancel_r in H.
   exact H.
 - intros Hxy.
   assert (Hsum : x + z < y + z).
   { apply lt_add_mono_r.
     exact Hxy. }
   unfold gt.
   apply lt_mult_mono_r; assumption.
Qed.

Lemma lt_gt_add_mult_cancel_r : forall x y z a : nat,
  a <> O -> (a * (y + z) > a * (x + z) <-> x < y).
Proof.
 intros x y z a Ha.
 split.
 - intros H.
   apply (gt_mult_mono_l_iff (y + z) (x + z) a Ha) in H.
   apply lt_add_cancel_r in H.
   exact H.
 - intros Hxy.
   assert (Hsum : x + z < y + z).
   { apply lt_add_mono_r.
     exact Hxy. }
   unfold gt.
   apply lt_mult_mono_l; assumption.
Qed.
