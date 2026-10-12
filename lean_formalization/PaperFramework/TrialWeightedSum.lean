import PaperFramework.TrialWeightedPointwise
import PaperFramework.TrialHarmonicBounds

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem trial_reverse_sum (N : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin N, f (N - i.val)) = ∑ k ∈ Finset.range N, f (k + 1) := by
  calc
    _ = ∑ i : Fin N, f (N - i.rev.val) :=
      (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin N)) (fun i => f (N - i.val))).symm
    _ = ∑ i : Fin N, f (i.val + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      simp only [Fin.val_rev]
      omega
    _ = _ := Fin.sum_univ_eq_sum_range (fun k => f (k + 1)) N

theorem trial_reciprocal_right_sum (N : ℕ) :
    (∑ i : Fin N, 1 / ((N : ℝ) - i.val)) = harmonicSum N := by
  have hh : (∑ i : Fin N, 1 / ((N : ℝ) - i.val)) =
      ∑ i : Fin N, 1 / ((N - i.val : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.le_of_lt i.isLt)]
  rw [hh, trial_reverse_sum N (fun j => 1 / (j : ℝ))]
  simp only [harmonicSum, Nat.cast_add, Nat.cast_one]

theorem trial_endpoint_summand_sum (N : ℕ) (t : ℝ) (ht : 1 ≤ t) :
    (∑ i : Fin N, (8 + shiftedHarmonic t (N - i.val)) /
      (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1))) ≤ 9 := by
  have hh : (∑ i : Fin N, (8 + shiftedHarmonic t (N - i.val)) /
      (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1))) =
      ∑ i : Fin N, (8 + shiftedHarmonic t (N - i.val)) /
        (((N - i.val : ℕ) : ℝ) * (((N - i.val : ℕ) : ℝ) + 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.le_of_lt i.isLt)]
  rw [hh, trial_reverse_sum N (fun j =>
    (8 + shiftedHarmonic t j) / ((j : ℝ) * ((j : ℝ) + 1)))]
  simp only [Nat.cast_add, Nat.cast_one]
  have hid : (∑ k ∈ Finset.range N, (8 + shiftedHarmonic t (k + 1)) /
      (((k : ℝ) + 1) * ((k : ℝ) + 1 + 1))) =
      8 * (∑ k ∈ Finset.range N, 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) +
        ∑ k ∈ Finset.range N, shiftedHarmonic t (k + 1) /
          (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hid, trial_reciprocal_product_sum]
  have hw := shiftedHarmonic_weighted_sum_upper t ht N
  have hn : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
  linarith only [hw, hn]

theorem trial_weighted_sum_bound (N : ℕ) (t : ℝ) (hN : 0 < N) (ht : 1 ≤ t) :
    (N : ℝ) * (∑ i : Fin N, ((i.val : ℝ) + 1) * difference (trialVector N t) i *
        trialVector N t i / ((N : ℝ) - i.val)) ≤
      17 + (4 * (shiftedHarmonic t N) ^ 2 +
        4 * (2 + shiftedHarmonic t N) * harmonicSum N) / (N : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
    trial_weighted_pointwise N t hN ht i)
  have hprod := weighted_difference_product_bound (trialVector N t)
    (fun i => (trialVector_positive N t ht i).le) (trialVector_differences_nonnegative N t ht)
  have hsquares := trialVector_square_sum_upper N t hN ht
  have hend := trial_endpoint_summand_sum N t ht
  have hid : (∑ i : Fin N, 4 * (2 + shiftedHarmonic t N) /
      ((N : ℝ) * ((N : ℝ) - i.val))) =
      4 * (2 + shiftedHarmonic t N) / (N : ℝ) * harmonicSum N := by
    rw [← trial_reciprocal_right_sum N, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
    field_simp [ne_of_gt hn, ne_of_gt (sub_pos.mpr hi)]
    <;> ring
  have hleft : (∑ i : Fin N, (N : ℝ) *
      (((i.val : ℝ) + 1) * difference (trialVector N t) i) * trialVector N t i /
        ((N : ℝ) - i.val)) =
      (N : ℝ) * (∑ i : Fin N, ((i.val : ℝ) + 1) * difference (trialVector N t) i *
        trialVector N t i / ((N : ℝ) - i.val)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hleft, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hid] at hsum
  have hb : (∑ i : Fin N, ((i.val : ℝ) + 1) * difference (trialVector N t) i *
      trialVector N t i) ≤ 4 + 2 * (shiftedHarmonic t N) ^ 2 / (N : ℝ) := hprod.trans hsquares
  have he : 17 + (4 * (shiftedHarmonic t N) ^ 2 +
      4 * (2 + shiftedHarmonic t N) * harmonicSum N) / (N : ℝ) =
      2 * (4 + 2 * (shiftedHarmonic t N) ^ 2 / (N : ℝ)) +
        4 * (2 + shiftedHarmonic t N) / (N : ℝ) * harmonicSum N + 9 := by ring
  rw [he]
  linarith only [hsum, hb, hend]

def trialWeightConstant (t : ℝ) : ℝ :=
  33 + 8 * (1 + 2 * t) ^ 2 + 4 * (3 + 2 * t) ^ 2

theorem trialWeightConstant_positive (t : ℝ) : 0 < trialWeightConstant t := by
  unfold trialWeightConstant
  positivity

theorem trial_weighted_sum_log_bound (N : ℕ) (t : ℝ) (hN : 0 < N) (ht : 1 ≤ t) :
    (N : ℝ) * (∑ i : Fin N, ((i.val : ℝ) + 1) * difference (trialVector N t) i *
        trialVector N t i / ((N : ℝ) - i.val)) ≤
      trialWeightConstant t * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ)) := by
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : 0 < (N : ℝ) := by linarith
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hn
  have hq0 := shiftedHarmonic_nonnegative t ht N
  have hq : shiftedHarmonic t N ≤ Real.log (N : ℝ) + (1 + 2 * t) := by
    have hh := (abs_le.mp (shifted_reciprocal_log_error (1 + 2 * t) (by linarith) N hN)).2
    simpa only [shiftedHarmonic, add_assoc] using (by linarith :
      (∑ k ∈ Finset.range N, 1 / ((k : ℝ) + (1 + 2 * t))) ≤
        Real.log (N : ℝ) + (1 + 2 * t))
  have hH : harmonicSum N ≤ Real.log (N : ℝ) + 1 := by
    have hh := (abs_le.mp (harmonicSum_log_error N (by omega))).2
    linarith
  have hq2 : (shiftedHarmonic t N) ^ 2 ≤
      2 * (Real.log (N : ℝ)) ^ 2 + 2 * (1 + 2 * t) ^ 2 := by
    have hh : (shiftedHarmonic t N) ^ 2 ≤ (Real.log (N : ℝ) + (1 + 2 * t)) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq) (by linarith :
        0 ≤ Real.log (N : ℝ) + (1 + 2 * t) + shiftedHarmonic t N)]
    nlinarith [sq_nonneg (Real.log (N : ℝ) - (1 + 2 * t))]
  have hprod : (2 + shiftedHarmonic t N) * harmonicSum N ≤
      2 * (Real.log (N : ℝ)) ^ 2 + (3 + 2 * t) ^ 2 + 1 := by
    have hh : (2 + shiftedHarmonic t N) * harmonicSum N ≤
        (Real.log (N : ℝ) + (3 + 2 * t)) * (Real.log (N : ℝ) + 1) := by
      calc
        _ ≤ (2 + shiftedHarmonic t N) * (Real.log (N : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hH (by linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith [sq_nonneg (Real.log (N : ℝ) - (3 + 2 * t)),
      sq_nonneg (Real.log (N : ℝ) - 1),
      sq_nonneg ((Real.log (N : ℝ) + (3 + 2 * t)) - (Real.log (N : ℝ) + 1))]
  have hnum : 4 * (shiftedHarmonic t N) ^ 2 +
      4 * (2 + shiftedHarmonic t N) * harmonicSum N ≤
      16 * (Real.log (N : ℝ)) ^ 2 + 8 * (1 + 2 * t) ^ 2 + 4 * (3 + 2 * t) ^ 2 + 4 := by
    linarith only [hq2, hprod]
  have hb := trial_weighted_sum_bound N t hN ht
  have hdiv := div_le_div_of_nonneg_right hnum hn0.le
  have hC : 16 ≤ trialWeightConstant t := by
    unfold trialWeightConstant
    nlinarith [sq_nonneg (1 + 2 * t), sq_nonneg (3 + 2 * t)]
  have hconst : 0 ≤ 8 * (1 + 2 * t) ^ 2 + 4 * (3 + 2 * t) ^ 2 + 4 := by positivity
  have hsmall : (8 * (1 + 2 * t) ^ 2 + 4 * (3 + 2 * t) ^ 2 + 4) / (N : ℝ) ≤
      8 * (1 + 2 * t) ^ 2 + 4 * (3 + 2 * t) ^ 2 + 4 := by
    apply (div_le_iff₀ hn0).mpr
    exact le_mul_of_one_le_right hconst hn
  have hlogs := mul_le_mul_of_nonneg_right hC
    (div_nonneg (sq_nonneg (Real.log (N : ℝ))) hn0.le)
  unfold trialWeightConstant at ⊢ hlogs
  have he : (16 * (Real.log (N : ℝ)) ^ 2 + 8 * (1 + 2 * t) ^ 2 +
      4 * (3 + 2 * t) ^ 2 + 4) / (N : ℝ) =
      16 * ((Real.log (N : ℝ)) ^ 2 / (N : ℝ)) +
        (8 * (1 + 2 * t) ^ 2 + 4 * (3 + 2 * t) ^ 2 + 4) / (N : ℝ) := by ring
  rw [he] at hdiv
  nlinarith only [hb, hdiv, hsmall, hlogs]

end
end CriticalExtrapolation.Paper
