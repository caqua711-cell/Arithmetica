Require Import def.
Require Import le.
Require Import lt.
Require Import add.
Require Import mult.

Lemma ge_refl : forall x : nat, x >= x.
Proof.
 intros x.
 apply le_refl.
Qed.

Lemma ge_step : forall x y : nat, x >= y -> S x >= y.
Proof.
 intros x y H.
 apply le_step.
 exact H.
Qed.

Lemma ge_trans : forall x y z : nat, x >= y -> y >= z -> x >= z.
Proof.
 intros x y z Hxy Hyz.
 unfold ge in *.
 eapply le_trans.
 - exact Hyz.
 - exact Hxy.
Qed.

Lemma ge_antisym : forall x y : nat, x >= y -> y >= x -> x = y.
Proof.
 intros x y Hxy Hyx.
 unfold ge in *.
 symmetry.
 eapply le_antisym.
 - exact Hxy.
 - exact Hyx.
Qed.

Lemma ge_zero : forall x : nat, x >= O.
Proof.
 intros x.
 apply le_zero_l.
Qed.

Lemma ge_succ_cases : forall x y : nat, S x >= y -> x >= y \/ y = S x.
Proof.
 intros x y H.
 unfold ge in H.
 apply le_succ_cases in H.
 exact H.
Qed.

Lemma ge_gt_or_eq : forall x y : nat, x >= y -> x > y \/ x = y.
Proof.
 intros x y H.
 unfold ge in H.
 apply le_lt_or_eq in H.
 destruct H as [Hlt | Heq].
 - left.
	 exact Hlt.
 - right.
	 symmetry.
	 exact Heq.
Qed.

Lemma ge_le_iff : forall x y : nat, x >= y <-> y <= x.
Proof.
 intros x y.
 split; intros H; exact H.
Qed.

Lemma ge_le_trans : forall x y z : nat, x >= y -> x <= z -> z >= y.
Proof.
 intros x y z Hxy Hxz.
 unfold ge in *.
 eapply le_trans.
 - exact Hxy.
 - exact Hxz.
Qed.

Lemma ge_succ_right_iff : forall x y : nat, x >= S y <-> x > y.
Proof.
 intros x y.
 unfold ge, gt, lt.
 split; intros H; exact H.
Qed.

Lemma ge_succ_iff : forall x y : nat, S x >= S y <-> x >= y.
Proof.
 intros x y.
 unfold ge.
 apply le_succ_iff.
Qed.

Lemma ge_succ_mono_two_iff : forall x y : nat,
  S (S x) >= S (S y) <-> x >= y.
Proof.
 intros x y.
 unfold ge.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma ge_succ_mono_three_iff : forall x y : nat,
  S (S (S x)) >= S (S (S y)) <-> x >= y.
Proof.
 intros x y.
 unfold ge.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma ge_succ_mono_four_iff : forall x y : nat,
  S (S (S (S x))) >= S (S (S (S y))) <-> x >= y.
Proof.
 intros x y.
 unfold ge.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma ge_succ_mono_five_iff : forall x y : nat,
  S (S (S (S (S x)))) >= S (S (S (S (S y)))) <-> x >= y.
Proof.
 intros x y.
 unfold ge.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma ge_succ_mono_six_iff : forall x y : nat,
  S (S (S (S (S (S x))))) >= S (S (S (S (S (S y))))) <-> x >= y.
Proof.
 intros x y.
 unfold ge.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma ge_succ_cases_iff : forall x y : nat,
	S x >= y <-> x >= y \/ y = S x.
Proof.
 intros x y.
 split.
 - apply ge_succ_cases.
 - intros [Hxy | Hxy].
	 + unfold ge in *.
		 apply le_step.
		 exact Hxy.
	 + rewrite Hxy.
		 apply le_refl.
Qed.

Lemma ge_gt_or_eq_iff : forall x y : nat,
	x >= y <-> x > y \/ x = y.
Proof.
 intros x y.
 split.
 - apply ge_gt_or_eq.
 - intros [Hgt | Heq].
	 + unfold gt in Hgt.
		 unfold ge.
		 apply lt_le.
		 exact Hgt.
	 + rewrite Heq.
		 apply ge_refl.
Qed.

Lemma ge_not_lt_iff : forall x y : nat, x >= y <-> ~ (x < y).
Proof.
 intros x y.
 unfold ge.
 apply le_not_lt_iff.
Qed.

Lemma ge_one_iff : forall x : nat, x >= S O <-> x <> O.
Proof.
 intros x.
 split.
 - intros H Hx.
	 subst x.
	 unfold ge in H.
	 apply le_zero_inv in H.
	 discriminate H.
 - intros H.
	 destruct x as [| x].
	 + contradiction.
	 + unfold ge.
		 apply le_succ_mono.
		 apply le_zero_l.
Qed.

Lemma ge_zero_right_iff : forall x : nat, O >= x <-> x = O.
Proof.
 intros x.
 unfold ge.
 split.
 - apply le_zero_inv.
 - intros H.
	 rewrite H.
	 apply le_refl.
Qed.

Lemma ge_two_iff : forall x : nat,
	x >= S (S O) <-> exists y : nat, x = S (S y).
Proof.
 intros x.
 split.
 - intros H.
	 unfold ge in H.
	 apply (@le_succ_left_iff (S O) x) in H.
	 destruct H as [y [Hx Hy]].
	 apply (@le_succ_left_iff O y) in Hy.
	 destruct Hy as [z [Hy _]].
	 exists z.
	 rewrite Hx.
	 rewrite Hy.
	 reflexivity.
 - intros [y Hx].
	 unfold ge.
	 rewrite Hx.
	 apply le_succ_mono.
	 apply le_succ_mono.
	 apply le_zero_l.
Qed.

Lemma ge_three_iff : forall x : nat,
	x >= S (S (S O)) <-> exists y : nat, x = S (S (S y)).
Proof.
 intros x.
 split.
 - intros H.
	 unfold ge in H.
	 apply (@le_succ_left_iff (S (S O)) x) in H.
	 destruct H as [y [Hx Hy]].
	 apply (@le_succ_left_iff (S O) y) in Hy.
	 destruct Hy as [z [Hy Hz]].
	 apply (@le_succ_left_iff O z) in Hz.
	 destruct Hz as [w [Hz _]].
	 exists w.
	 rewrite Hx.
	 rewrite Hy.
	 rewrite Hz.
	 reflexivity.
 - intros [y Hx].
	 unfold ge.
	 rewrite Hx.
	 apply le_succ_mono.
	 apply le_succ_mono.
	 apply le_succ_mono.
	 apply le_zero_l.
Qed.

Lemma ge_four_iff : forall x : nat,
	x >= S (S (S (S O))) <-> exists y : nat, x = S (S (S (S y))).
Proof.
 intros x.
 split.
 - intros H.
	 unfold ge in H.
	 apply (@le_succ_left_iff (S (S (S O))) x) in H.
	 destruct H as [y [Hx Hy]].
	 apply (@le_succ_left_iff (S (S O)) y) in Hy.
	 destruct Hy as [z [Hy Hz]].
	 apply (@le_succ_left_iff (S O) z) in Hz.
	 destruct Hz as [w [Hz Hw]].
	 apply (@le_succ_left_iff O w) in Hw.
	 destruct Hw as [v [Hw _]].
	 exists v.
	 rewrite Hx.
	 rewrite Hy.
	 rewrite Hz.
	 rewrite Hw.
	 reflexivity.
 - intros [y Hx].
	 unfold ge.
	 rewrite Hx.
	 apply le_succ_mono.
	 apply le_succ_mono.
	 apply le_succ_mono.
	 apply le_succ_mono.
	 apply le_zero_l.
Qed.

Lemma ge_five_iff : forall x : nat,
  x >= S (S (S (S (S O)))) <-> exists y : nat, x = S (S (S (S (S y)))).
Proof.
 intros x.
 split.
 - intros H.
   destruct x as [| x].
   + unfold ge in H.
     apply le_zero_inv in H.
     discriminate H.
   + unfold ge in H.
     apply le_succ_inv in H.
     apply ge_four_iff in H.
     destruct H as [y Hx].
     exists y.
     rewrite Hx.
     reflexivity.
 - intros [y Hx].
   unfold ge.
   rewrite Hx.
   repeat apply le_succ_mono.
   apply le_zero_l.
Qed.

Lemma ge_six_iff : forall x : nat,
  x >= S (S (S (S (S (S O))))) <-> exists y : nat, x = S (S (S (S (S (S y))))).
Proof.
 intros x.
 split.
 - intros H.
   destruct x as [| x].
   + unfold ge in H.
     apply le_zero_inv in H.
     discriminate H.
   + unfold ge in H.
     apply le_succ_inv in H.
     apply ge_five_iff in H.
     destruct H as [y Hx].
     exists y.
     rewrite Hx.
     reflexivity.
 - intros [y Hx].
   unfold ge.
   rewrite Hx.
   repeat apply le_succ_mono.
   apply le_zero_l.
Qed.

Lemma ge_seven_iff : forall x : nat,
  x >= S (S (S (S (S (S (S O)))))) <-> exists y : nat, x = S (S (S (S (S (S (S y)))))).
Proof.
 intros x.
 split.
 - intros H.
   destruct x as [| x].
   + unfold ge in H.
     apply le_zero_inv in H.
     discriminate H.
   + unfold ge in H.
     apply le_succ_inv in H.
     apply ge_six_iff in H.
     destruct H as [y Hx].
     exists y.
     rewrite Hx.
     reflexivity.
 - intros [y Hx].
   unfold ge.
   rewrite Hx.
   repeat apply le_succ_mono.
   apply le_zero_l.
Qed.

Lemma ge_eight_iff : forall x : nat,
  x >= S (S (S (S (S (S (S (S O))))))) <-> exists y : nat, x = S (S (S (S (S (S (S (S y))))))).
Proof.
 intros x.
 split.
 - intros H.
   destruct x as [| x].
   + unfold ge in H.
     apply le_zero_inv in H.
     discriminate H.
   + unfold ge in H.
     apply le_succ_inv in H.
     apply ge_seven_iff in H.
     destruct H as [y Hx].
     exists y.
     rewrite Hx.
     reflexivity.
 - intros [y Hx].
   unfold ge.
   rewrite Hx.
   repeat apply le_succ_mono.
   apply le_zero_l.
Qed.

Lemma ge_nine_iff : forall x : nat,
  x >= S (S (S (S (S (S (S (S (S O)))))))) <->
  exists y : nat, x = S (S (S (S (S (S (S (S (S y)))))))).
Proof.
 intros x.
 split.
 - intros H.
   destruct x as [| x].
   + unfold ge in H.
     apply le_zero_inv in H.
     discriminate H.
   + unfold ge in H.
     apply le_succ_inv in H.
     apply ge_eight_iff in H.
     destruct H as [y Hx].
     exists y.
     rewrite Hx.
     reflexivity.
 - intros [y Hx].
   unfold ge.
   rewrite Hx.
   repeat apply le_succ_mono.
   apply le_zero_l.
Qed.

Lemma ge_succ_gt_or_eq_iff : forall x y : nat,
	x >= S y <-> x > S y \/ x = S y.
Proof.
 intros x y.
 unfold ge.
 split.
 - intros H.
	 apply le_lt_or_eq in H.
	 destruct H as [Hlt | Heq].
	 + left.
		 exact Hlt.
	 + right.
		 symmetry.
		 exact Heq.
 - intros [Hgt | Heq].
	 + unfold gt, lt in Hgt.
		 apply le_succ_lower.
		 exact Hgt.
	 + rewrite Heq.
		 apply le_refl.
Qed.

Lemma ge_add_l : forall x y z : nat, x >= y -> x + z >= y + z.
Proof.
 intros x y z H.
 unfold ge in *.
 apply le_add_mono_r.
 exact H.
Qed.

Lemma ge_add_r : forall x y z : nat, x >= y -> z + x >= z + y.
Proof.
 intros x y z H.
 unfold ge in *.
 apply le_add_mono_l.
 exact H.
Qed.

Lemma ge_add_mono : forall x y z w : nat,
	x >= y -> z >= w -> x + z >= y + w.
Proof.
 intros x y z w Hxy Hzw.
 unfold ge in *.
 apply le_add_mono.
 - exact Hxy.
 - exact Hzw.
Qed.

Lemma ge_add_self_l : forall x y : nat, x + y >= x.
Proof.
 intros x y.
 unfold ge.
 apply le_add_l.
Qed.

Lemma ge_add_self_r : forall x y : nat, x + y >= y.
Proof.
 intros x y.
 unfold ge.
 apply le_add_r.
Qed.

Lemma ge_add_left : forall x y : nat, x + y >= x.
Proof.
 intros x y.
 unfold ge.
 apply le_add_l.
Qed.

Lemma ge_add_right : forall x y : nat, x + y >= y.
Proof.
 intros x y.
 rewrite (add_comm x y).
 unfold ge.
 apply le_add_l.
Qed.

Lemma ge_add_cancel_l : forall x y z : nat,
  x + z >= y + z -> x >= y.
Proof.
 intros x y z H.
 unfold ge in *.
 apply (le_add_cancel_r y x z).
 exact H.
Qed.

Lemma ge_add_cancel_r : forall x y z : nat,
  z + x >= z + y -> x >= y.
Proof.
 intros x y z H.
 unfold ge in *.
 apply (le_add_cancel_l z y x).
 exact H.
Qed.

Lemma ge_mult_l : forall x y z : nat, x >= y -> x * z >= y * z.
Proof.
 intros x y z H.
 unfold ge in *.
 apply le_mult_mono_l.
 exact H.
Qed.

Lemma ge_mult_r : forall x y z : nat, x >= y -> z * x >= z * y.
Proof.
 intros x y z H.
 unfold ge in *.
 apply le_mult_mono_r.
 exact H.
Qed.

Lemma ge_mult_mono : forall x y z w : nat,
	x >= y -> z >= w -> x * z >= y * w.
Proof.
 intros x y z w Hxy Hzw.
 unfold ge in *.
 apply le_mult_mono.
 - exact Hxy.
 - exact Hzw.
Qed.

Lemma ge_mult_left : forall x y : nat, x * y >= O.
Proof.
 intros x y.
 unfold ge.
 apply le_zero_l.
Qed.

Lemma ge_mult_add_l : forall x y z : nat, x * (y + z) >= x * y.
Proof.
 intros x y z.
 unfold ge.
 apply le_mult_add_l.
Qed.

Lemma ge_mult_add_r : forall x y z : nat, (x + z) * y >= x * y.
Proof.
 intros x y z.
 unfold ge.
 apply le_mult_add_r.
Qed.