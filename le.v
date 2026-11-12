Require Import def.
Require Import add.
Require Import mult.

Lemma le_trans_eq : forall x y z : nat, x <= y -> y = z -> x <= z.
Proof.
 intros x y z Hxy Heq.
 rewrite <- Heq.
 exact Hxy.
Qed.

Lemma le_refl : forall x : nat, x <= x.
Proof.
 intros x.
 apply le_refl_rule.
Qed.

Lemma le_step : forall x y : nat, x <= y -> x <= S y.
Proof.
 intros x y H.
 apply le_step_rule.
 exact H.
Qed.

Lemma le_zero_l : forall x : nat, O <= x.
Proof.
 induction x as [| x IHx].
 - apply le_refl.
 - apply le_step.
   exact IHx.
Qed.

Lemma le_trans : forall x y z : nat, x <= y -> y <= z -> x <= z.
Proof.
 intros x y z Hxy Hyz.
 revert x Hxy.
 induction Hyz as [y | y z Hyz IH].
 - intros x Hxy.
   exact Hxy.
 - intros x Hxy.
   apply le_step.
   apply IH.
   exact Hxy.
Qed.

Lemma le_succ_mono : forall x y : nat, x <= y -> S x <= S y.
Proof.
 intros x y H.
 induction H as [x | x y Hxy IH].
 - apply le_refl.
 - apply le_step.
   exact IH.
Qed.

Lemma le_succ_cases : forall x y : nat, x <= S y -> x <= y \/ x = S y.
Proof.
 intros x y H.
 inversion H; subst.
 - right.
   reflexivity.
 - left.
   assumption.
Qed.

Lemma le_succ_inv : forall x y : nat, S x <= S y -> x <= y.
Proof.
 intros x y H.
 inversion H; subst.
 - apply le_refl.
 - eapply le_trans.
   + apply le_step.
     apply le_refl.
   + assumption.
Qed.

Lemma le_zero_inv : forall x : nat, x <= O -> x = O.
Proof.
 intros x H.
 inversion H; reflexivity.
Qed.

Lemma le_succ_not_le : forall x : nat, ~ (S x <= x).
Proof.
 induction x as [| x IHx].
 - intros H.
   inversion H.
 - intros H.
   apply IHx.
   apply le_succ_inv in H.
   exact H.
Qed.

Lemma le_antisym : forall x y : nat, x <= y -> y <= x -> x = y.
Proof.
 intros x.
 induction x as [| x IHx].
 - intros y Hxy Hyx.
   apply le_zero_inv in Hyx.
   symmetry.
   exact Hyx.
 - intros y Hxy Hyx.
   destruct y as [| y].
   + apply le_zero_inv in Hxy.
     discriminate Hxy.
   + f_equal.
     apply IHx.
     * apply le_succ_inv in Hxy.
       exact Hxy.
     * apply le_succ_inv in Hyx.
       exact Hyx.
Qed.

Lemma le_total : forall x y : nat, x <= y \/ y <= x.
Proof.
 intros x.
 induction x as [| x IHx].
 - intros y.
   left.
   apply le_zero_l.
 - intros y.
   destruct y as [| y].
   + right.
     apply le_zero_l.
   + destruct (IHx y) as [Hxy | Hyx].
     * left.
       apply le_succ_mono.
       exact Hxy.
     * right.
       apply le_succ_mono.
       exact Hyx.
Qed.

Lemma le_or_gt_total : forall x y : nat, x <= y \/ x > y.
Proof.
 intros x.
 induction x as [| x IHx]; intros y.
 - left.
   apply le_zero_l.
 - destruct y as [| y].
   + right.
       unfold gt, lt.
       apply le_succ_mono.
       apply le_zero_l.
   + destruct (IHx y) as [Hle | Hgt].
       * left.
         apply le_succ_mono.
         exact Hle.
       * right.
         unfold gt, lt in *.
         apply le_succ_mono.
         exact Hgt.
Qed.

Lemma le_zero_iff : forall x : nat, x <= O <-> x = O.
Proof.
 intros x.
 split.
 - apply le_zero_inv.
 - intros H.
   rewrite H.
   apply le_refl.
Qed.

Lemma le_succ_iff : forall x y : nat, S x <= S y <-> x <= y.
Proof.
 intros x y.
 split.
 - apply le_succ_inv.
 - apply le_succ_mono.
Qed.

Lemma le_succ_right_iff : forall x y : nat,
  x <= S y <-> x <= y \/ x = S y.
Proof.
 intros x y.
 split.
 - apply le_succ_cases.
 - intros [Hxy | Hxy].
   + apply le_step.
     exact Hxy.
   + rewrite Hxy.
     apply le_refl.
Qed.

Lemma le_eq_or_succ_le_iff : forall x y : nat,
  x <= y <-> x = y \/ S x <= y.
Proof.
 intros x y.
 split.
 - intros H.
   induction H as [x | x y Hxy IH].
   + left.
     reflexivity.
   + destruct IH as [Heq | Hsucc].
     * right.
       rewrite Heq.
       apply le_refl.
     * right.
       apply le_step.
       exact Hsucc.
 - intros [Hxy | Hxy].
   + rewrite Hxy.
     apply le_refl.
   + eapply le_trans.
     * apply le_step.
       apply le_refl.
     * exact Hxy.
Qed.

Lemma le_lt_or_eq_iff : forall x y : nat,
  x <= y <-> x < y \/ x = y.
Proof.
 intros x y.
 split.
 - intros Hxy.
   induction Hxy as [x | x y Hxy IH].
   + right.
     reflexivity.
   + destruct IH as [Hlt | Heq].
     * left.
       unfold lt in *.
       apply le_step.
       exact Hlt.
     * subst y.
       left.
       unfold lt.
       apply le_refl.
 - intros [Hlt | Heq].
   + unfold lt in Hlt.
     eapply le_trans.
     * apply le_step.
       apply le_refl.
     * exact Hlt.
   + rewrite Heq.
     apply le_refl.
Qed.

Lemma le_not_lt_iff : forall x y : nat,
  x <= y <-> ~ (y < x).
Proof.
 intros x y.
 split.
 - intros Hxy Hlt.
   unfold lt in Hlt.
   apply (le_succ_not_le y).
   eapply le_trans.
   + exact Hlt.
   + exact Hxy.
 - intros Hnot.
   destruct (le_total x y) as [Hxy | Hyx].
   + exact Hxy.
   + apply le_eq_or_succ_le_iff in Hyx.
     destruct Hyx as [Heq | Hlt].
     * rewrite <- Heq.
       apply le_refl.
     * exfalso.
       apply Hnot.
       exact Hlt.
Qed.

Lemma le_succ_lower : forall x y : nat, S x <= y -> x <= y.
Proof.
 intros x y H.
 eapply le_trans.
 - apply le_step.
   apply le_refl.
 - exact H.
Qed.

Lemma le_lt_succ_iff : forall x y : nat,
  x <= y <-> x < S y.
Proof.
 intros x y.
 split.
 - unfold lt.
   apply le_succ_mono.
 - unfold lt.
   apply le_succ_inv.
Qed.

Lemma le_succ_left_iff : forall x y : nat,
  S x <= y <-> exists z : nat, y = S z /\ x <= z.
Proof.
 intros x y.
 split.
 - intros H.
   destruct y as [| y].
   + apply le_zero_inv in H.
     discriminate H.
   + exists y.
     split.
     * reflexivity.
     * apply le_succ_inv in H.
       exact H.
 - intros [z [Hyz Hxz]].
   rewrite Hyz.
   apply le_succ_mono.
   exact Hxz.
Qed.

Lemma le_lt_iff_succ_le : forall x y : nat, x < y <-> S x <= y.
Proof.
 intros x y.
 unfold lt.
 split; intros H; exact H.
Qed.

Lemma le_add_l : forall x y : nat, x <= x + y.
Proof.
 intros x y.
 induction y as [| y IHy].
 - rewrite add_0_r.
   apply le_refl.
 - rewrite add_succ_r.
   apply le_step.
   exact IHy.
Qed.

Lemma le_add_r : forall x y : nat, y <= x + y.
Proof.
 intros x y.
 rewrite (add_comm x y).
 apply le_add_l.
Qed.

Lemma le_add_mono_l : forall x y z : nat, x <= y -> z + x <= z + y.
Proof.
 intros x y z H.
 induction H as [x | x y Hxy IH].
 - apply le_refl.
 - rewrite add_succ_r.
   apply le_step.
   exact IH.
Qed.

Lemma le_add_mono_r : forall x y z : nat, x <= y -> x + z <= y + z.
Proof.
 intros x y z H.
 rewrite (add_comm x z).
 rewrite (add_comm y z).
 apply le_add_mono_l.
 exact H.
Qed.

Lemma le_add_mono : forall x y z w : nat,
  x <= y -> z <= w -> x + z <= y + w.
Proof.
 intros x y z w Hxy Hzw.
 eapply le_trans with (y := y + z).
 - exact (@le_add_mono_r x y z Hxy).
 - exact (@le_add_mono_l z w y Hzw).
Qed.

Lemma le_add_cancel_l : forall x y z : nat,
  x + y <= x + z -> y <= z.
Proof.
 intros x.
 induction x as [| x IHx].
 - intros y z H.
   simpl in H.
   exact H.
 - intros y z H.
   apply IHx.
   apply le_succ_inv in H.
   exact H.
Qed.

Lemma le_add_cancel_r : forall x y z : nat,
  x + z <= y + z -> x <= y.
Proof.
 intros x y z H.
 rewrite (add_comm x z) in H.
 rewrite (add_comm y z) in H.
 apply (le_add_cancel_l z x y).
 exact H.
Qed.

Lemma le_add_cancel_l_iff : forall x y z : nat,
  x + y <= x + z <-> y <= z.
Proof.
 intros x y z.
 split.
 - apply le_add_cancel_l.
 - intros H.
   apply le_add_mono_l.
   exact H.
Qed.

Lemma le_add_cancel_r_iff : forall x y z : nat,
  x + z <= y + z <-> x <= y.
Proof.
 intros x y z.
 split.
 - apply le_add_cancel_r.
 - intros H.
   apply le_add_mono_r.
   exact H.
Qed.

Lemma le_add_mono_three : forall x y z u v w : nat,
  x <= y -> z <= u -> v <= w ->
  (x + z) + v <= (y + u) + w.
Proof.
 intros x y z u v w Hxy Hzu Hvw.
 apply le_add_mono.
 - apply le_add_mono; assumption.
 - exact Hvw.
Qed.

Lemma le_add_extend_r : forall x y z : nat,
  x <= y -> x <= y + z.
Proof.
 intros x y z H.
 eapply le_trans.
 - exact H.
 - apply le_add_l.
Qed.

Lemma le_add_extend_l : forall x y z : nat,
  x <= y -> x <= z + y.
Proof.
 intros x y z H.
 eapply le_trans.
 - exact H.
 - apply le_add_r.
Qed.

Lemma le_mult_mono_l : forall x y z : nat, x <= y -> x * z <= y * z.
Proof.
 intros x y z H.
 induction H as [x | x y Hxy IH].
 - apply le_refl.
 - simpl.
   eapply le_trans.
   + exact IH.
   + apply le_add_r.
Qed.

Lemma le_mult_mono_r : forall x y z : nat, x <= y -> z * x <= z * y.
Proof.
 intros x y z H.
 rewrite (mult_comm z x).
 rewrite (mult_comm z y).
 apply le_mult_mono_l.
 exact H.
Qed.

Lemma le_mult_mono : forall x y z w : nat,
  x <= y -> z <= w -> x * z <= y * w.
Proof.
 intros x y z w Hxy Hzw.
 eapply le_trans with (y := y * z).
 - exact (@le_mult_mono_l x y z Hxy).
 - exact (@le_mult_mono_r z w y Hzw).
Qed.

Lemma le_mult_add_l : forall x y z : nat, x * y <= x * (y + z).
Proof.
 intros x y z.
 apply le_mult_mono_r.
 apply le_add_l.
Qed.

Lemma le_mult_add_r : forall x y z : nat, x * y <= (x + z) * y.
Proof.
 intros x y z.
 apply le_mult_mono_l.
 apply le_add_l.
Qed.

Lemma le_mult_left_factor : forall x y : nat,
  y <> O -> x <= x * y.
Proof.
 intros x y Hy.
 destruct y as [| y].
 - contradiction.
 - rewrite mult_succ_r.
   apply le_add_l.
Qed.

Lemma le_mult_right_factor : forall x y : nat,
  x <> O -> y <= x * y.
Proof.
 intros x y Hx.
 rewrite (mult_comm x y).
 apply le_mult_left_factor.
 exact Hx.
Qed.

Lemma le_mult_succ_left : forall x y : nat,
  x * y <= S x * y.
Proof.
 intros x y.
 apply le_mult_mono_l.
 apply le_step.
 apply le_refl.
Qed.

Lemma le_mult_succ_right : forall x y : nat,
  x * y <= x * S y.
Proof.
 intros x y.
 apply le_mult_mono_r.
 apply le_step.
 apply le_refl.
Qed.

Lemma le_mult_add_both : forall x y z w : nat,
  x * y <= (x + z) * (y + w).
Proof.
 intros x y z w.
 apply le_mult_mono.
 - apply le_add_l.
 - apply le_add_l.
Qed.

Lemma le_succ_mono_two : forall x y : nat, x <= y -> S (S x) <= S (S y).
Proof.
 intros x y H.
 apply le_succ_mono.
 apply le_succ_mono.
 exact H.
Qed.

Lemma le_succ_mono_three : forall x y : nat, x <= y -> S (S (S x)) <= S (S (S y)).
Proof.
 intros x y H.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma le_succ_mono_four : forall x y : nat, x <= y -> S (S (S (S x))) <= S (S (S (S y))).
Proof.
 intros x y H.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma le_succ_mono_five : forall x y : nat, x <= y -> S (S (S (S (S x)))) <= S (S (S (S (S y)))).
Proof.
 intros x y H.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma le_succ_mono_four_iff : forall x y : nat,
  S (S (S (S x))) <= S (S (S (S y))) <-> x <= y.
Proof.
 intros x y.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - apply le_succ_mono_four.
Qed.

Lemma le_succ_right_two_cases : forall x y : nat,
  x <= S (S y) -> x <= y \/ x = S y \/ x = S (S y).
Proof.
 intros x y H.
 apply le_succ_cases in H.
 destruct H as [H | H].
 - apply le_succ_cases in H.
   destruct H as [H | H].
   + left.
     exact H.
   + right.
     left.
     exact H.
 - right.
   right.
   exact H.
Qed.

Lemma le_trans_three : forall x y z w : nat,
  x <= y -> y <= z -> z <= w -> x <= w.
Proof.
 intros x y z w Hxy Hyz Hzw.
 eapply le_trans.
 - eapply le_trans.
   + exact Hxy.
   + exact Hyz.
 - exact Hzw.
Qed.

Lemma le_trans_four : forall x y z w v : nat,
  x <= y -> y <= z -> z <= w -> w <= v -> x <= v.
Proof.
 intros x y z w v Hxy Hyz Hzw Hwv.
 eapply le_trans.
 - eapply le_trans.
   + eapply le_trans.
     * exact Hxy.
     * exact Hyz.
   + exact Hzw.
 - exact Hwv.
Qed.

Lemma le_antisym_iff : forall x y : nat, x = y <-> x <= y /\ y <= x.
Proof.
 intros x y.
 split.
 - intros H.
   subst y.
   split; apply le_refl.
 - intros [Hxy Hyx].
   apply le_antisym; assumption.
Qed.

Lemma le_refl_iff : forall x : nat, x <= x <-> x = x.
Proof.
 intros x.
 split.
 - intros _.
   reflexivity.
 - intros _.
   apply le_refl.
Qed.

Lemma le_succ_mono_six : forall x y : nat,
  x <= y -> S (S (S (S (S (S x))))) <= S (S (S (S (S (S y))))).
Proof.
 intros x y H.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma le_succ_mono_seven : forall x y : nat,
  x <= y -> S (S (S (S (S (S (S x)))))) <= S (S (S (S (S (S (S y)))))).
Proof.
 intros x y H.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma le_succ_mono_eight : forall x y : nat,
  x <= y -> S (S (S (S (S (S (S (S x))))))) <= S (S (S (S (S (S (S (S y))))))).
Proof.
 intros x y H.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma le_succ_mono_nine : forall x y : nat,
  x <= y -> S (S (S (S (S (S (S (S (S x)))))))) <= S (S (S (S (S (S (S (S (S y)))))))).
Proof.
 intros x y H.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma le_succ_mono_ten : forall x y : nat,
  x <= y -> S (S (S (S (S (S (S (S (S (S x))))))))) <= S (S (S (S (S (S (S (S (S (S y))))))))).
Proof.
 intros x y H.
 repeat apply le_succ_mono.
 exact H.
Qed.

Lemma le_succ_mono_two_iff : forall x y : nat,
  S (S x) <= S (S y) <-> x <= y.
Proof.
 intros x y.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma le_succ_mono_three_iff : forall x y : nat,
  S (S (S x)) <= S (S (S y)) <-> x <= y.
Proof.
 intros x y.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma le_succ_mono_five_iff : forall x y : nat,
  S (S (S (S (S x)))) <= S (S (S (S (S y)))) <-> x <= y.
Proof.
 intros x y.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma le_succ_mono_six_iff : forall x y : nat,
  S (S (S (S (S (S x))))) <= S (S (S (S (S (S y))))) <-> x <= y.
Proof.
 intros x y.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma le_succ_mono_seven_iff : forall x y : nat,
  S (S (S (S (S (S (S x)))))) <= S (S (S (S (S (S (S y)))))) <-> x <= y.
Proof.
 intros x y.
 split.
 - intros H.
   repeat apply le_succ_inv in H.
   exact H.
 - intros H.
   repeat apply le_succ_mono.
   exact H.
Qed.

Lemma le_add_mono_four : forall a b c d e f g h : nat,
  a <= b -> c <= d -> e <= f -> g <= h ->
  ((a + c) + e) + g <= ((b + d) + f) + h.
Proof.
 intros a b c d e f g h Hab Hcd Hef Hgh.
 apply le_add_mono.
 - apply le_add_mono.
   + apply le_add_mono; assumption.
   + exact Hef.
 - exact Hgh.
Qed.

Lemma le_add_mono_five : forall a b c d e f g h i j : nat,
  a <= b -> c <= d -> e <= f -> g <= h -> i <= j ->
  ((((a + c) + e) + g) + i) <= ((((b + d) + f) + h) + j).
Proof.
 intros a b c d e f g h i j Hab Hcd Hef Hgh Hij.
 apply le_add_mono.
 - apply le_add_mono_four; assumption.
 - exact Hij.
Qed.

Lemma le_add_surround_l : forall x y z : nat,
  x <= y -> z + x <= z + y.
Proof.
 intros x y z H.
 apply le_add_mono_l.
 exact H.
Qed.

Lemma le_add_surround_r : forall x y z : nat,
  x <= y -> x + z <= y + z.
Proof.
 intros x y z H.
 apply le_add_mono_r.
 exact H.
Qed.

Lemma le_add_nested_surround_l : forall x y z w : nat,
  x <= y -> (z + x) + w <= (z + y) + w.
Proof.
 intros x y z w H.
 apply le_add_mono_r.
 apply le_add_mono_l.
 exact H.
Qed.

Lemma le_add_nested_surround_r : forall x y z w : nat,
  x <= y -> (x + z) + w <= (y + z) + w.
Proof.
 intros x y z w H.
 apply le_add_mono_r.
 apply le_add_mono_r.
 exact H.
Qed.

Lemma le_add_extend_twice_r : forall x y z w : nat,
  x <= y -> x <= (y + z) + w.
Proof.
 intros x y z w H.
 eapply le_trans with (y := y + z).
 - eapply le_trans.
   + exact H.
   + apply le_add_l.
 - apply le_add_l.
Qed.

Lemma le_add_extend_twice_l : forall x y z w : nat,
  x <= y -> x <= (z + w) + y.
Proof.
 intros x y z w H.
 eapply le_trans.
 - exact H.
 - apply le_add_r.
Qed.

Lemma le_add_common_extension : forall x y z w : nat,
  x <= y -> x + z <= y + (z + w).
Proof.
 intros x y z w H.
 eapply le_trans.
 - apply le_add_mono_r.
   exact H.
 - apply le_add_mono_l.
   apply le_add_l.
Qed.

Lemma le_add_common_prefix_extension : forall x y z w : nat,
  x <= y -> z + x <= (z + y) + w.
Proof.
 intros x y z w H.
 eapply le_trans.
 - apply le_add_mono_l.
   exact H.
 - apply le_add_l.
Qed.

Lemma le_mult_mono_three : forall a b c d e f : nat,
  a <= b -> c <= d -> e <= f ->
  (a * c) * e <= (b * d) * f.
Proof.
 intros a b c d e f Hab Hcd Hef.
 apply le_mult_mono.
 - apply le_mult_mono; assumption.
 - exact Hef.
Qed.

Lemma le_mult_mono_four : forall a b c d e f g h : nat,
  a <= b -> c <= d -> e <= f -> g <= h ->
  ((a * c) * e) * g <= ((b * d) * f) * h.
Proof.
 intros a b c d e f g h Hab Hcd Hef Hgh.
 apply le_mult_mono.
 - apply le_mult_mono_three; assumption.
 - exact Hgh.
Qed.

Lemma le_mult_mono_nested_l : forall a b c : nat,
  a <= b -> c * a <= c * b.
Proof.
 intros a b c Hab.
 apply le_mult_mono_r.
 exact Hab.
Qed.

Lemma le_mult_mono_nested_r : forall a b c : nat,
  a <= b -> a * c <= b * c.
Proof.
 intros a b c Hab.
 apply le_mult_mono_l.
 exact Hab.
Qed.

Lemma le_mult_add_two_right : forall x y z w : nat,
  x * y <= x * ((y + z) + w).
Proof.
 intros x y z w.
 apply le_mult_mono_r.
 eapply le_trans.
 - apply le_add_l.
 - apply le_add_l.
Qed.

Lemma le_mult_add_two_left : forall x y z w : nat,
  x * y <= ((x + z) + w) * y.
Proof.
 intros x y z w.
 apply le_mult_mono_l.
 eapply le_trans.
 - apply le_add_l.
 - apply le_add_l.
Qed.

Lemma le_mult_add_right_factor : forall x y z : nat,
  x * y <= x * (y + z) + z.
Proof.
 intros x y z.
 eapply le_trans.
 - apply le_mult_add_l.
 - apply le_add_l.
Qed.

Lemma le_mult_add_left_factor : forall x y z : nat,
  x * y <= (x + z) * y + z.
Proof.
 intros x y z.
 eapply le_trans.
 - apply le_mult_add_r.
 - apply le_add_l.
Qed.

Lemma le_mult_nested_add_right : forall x y z w : nat,
  x * y <= x * y + x * (z + w).
Proof.
 intros x y z w.
 apply le_add_l.
Qed.

Lemma le_mult_nested_add_left : forall x y z w : nat,
  x * y <= x * y + (z + w) * y.
Proof.
 intros x y z w.
 apply le_add_l.
Qed.