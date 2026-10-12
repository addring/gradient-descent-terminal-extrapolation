import PaperFramework.TrialReferenceTailSum
import PaperFramework.TrialReferenceEnergyPointwise

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem shiftedHarmonic_endpoint_weight_sum (N : ℕ) (t : ℝ) (ht : 1 ≤ t) :
    (∑ i : Fin N, shiftedHarmonic t (N - i.val) /
      (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1))) ≤ 1 := by
  have hh : (∑ i : Fin N, shiftedHarmonic t (N - i.val) /
      (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1))) =
      ∑ i : Fin N, shiftedHarmonic t (N - i.val) /
        (((N - i.val : ℕ) : ℝ) * (((N - i.val : ℕ) : ℝ) + 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.le_of_lt i.isLt)]
  rw [hh, trial_reverse_sum N (fun j => shiftedHarmonic t j / ((j : ℝ) * ((j : ℝ) + 1)))]
  simp only [Nat.cast_add, Nat.cast_one]
  simp_rw [show ∀ k : ℕ, ((k : ℝ) + 1) * ((k : ℝ) + 1 + 1) =
    ((k : ℝ) + 1) * ((k : ℝ) + 2) from fun _ => by ring]
  exact shiftedHarmonic_weighted_sum_upper t ht N

theorem trialLeft_remainder_weighted_sum_upper (N : ℕ) (t : ℝ)
    (hN : 0 < N) (ht : 1 ≤ t) :
    (∑ i : Fin N, (tail (trialLeft N t) i.val -
      ((N : ℝ) - i.val) / ((N : ℝ) + 2 * t)) /
        (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1))) ≤ 1 / (N : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hT : 0 < (N : ℝ) + 2 * t := by linarith
  have hnum : (∑ i : Fin N, ((i.val : ℝ) + 1) / ((i.val : ℝ) + 2 * t)) ≤ N := by
    have hh : (∑ i : Fin N, ((i.val : ℝ) + 1) / ((i.val : ℝ) + 2 * t)) ≤
        ∑ _i : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hu : 0 < (i.val : ℝ) + 2 * t := by have := Nat.cast_nonneg (α := ℝ) i.val; linarith
      exact (div_le_one hu).mpr (by linarith)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using hh
  rw [trialLeft_remainder_weighted_sum N t ht]
  calc
    _ ≤ ((N : ℝ) + 1) / (((N : ℝ) + 2 * t) * ((N : ℝ) + 1)) :=
      div_le_div_of_nonneg_right (by linarith only [hnum]) (by positivity)
    _ = 1 / ((N : ℝ) + 2 * t) := by
      field_simp [ne_of_gt hT, ne_of_gt (show 0 < (N : ℝ) + 1 by positivity)]
      <;> ring
    _ ≤ _ := one_div_le_one_div_of_le hn (by linarith)

theorem trial_reciprocal_model_positive_correction_sum (N : ℕ) (t : ℝ)
    (hN : 0 < N) (ht : 1 ≤ t) :
    (∑ i : Fin N, 2 * t /
      ((N : ℝ) * ((N : ℝ) + 2 * t) * ((N : ℝ) - i.val + 1))) ≤ 2 * t / (N : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hT : 0 < (N : ℝ) + 2 * t := by linarith
  have hsum : (∑ i : Fin N, 1 / ((N : ℝ) - i.val + 1)) ≤ N := by
    have hh : (∑ i : Fin N, 1 / ((N : ℝ) - i.val + 1)) ≤ ∑ _i : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
      exact (div_le_one (by linarith : 0 < (N : ℝ) - i.val + 1)).mpr (by linarith)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using hh
  have hid : (∑ i : Fin N, 2 * t /
      ((N : ℝ) * ((N : ℝ) + 2 * t) * ((N : ℝ) - i.val + 1))) =
      (2 * t / ((N : ℝ) * ((N : ℝ) + 2 * t))) *
        ∑ i : Fin N, 1 / ((N : ℝ) - i.val + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
    field_simp [ne_of_gt hn, ne_of_gt hT, ne_of_gt (show 0 < (N : ℝ) - i.val + 1 by linarith)]
    <;> ring
  rw [hid]
  calc
    _ ≤ (2 * t / ((N : ℝ) * ((N : ℝ) + 2 * t))) * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg (by linarith) (by positivity))
    _ = 2 * t / ((N : ℝ) + 2 * t) := by field_simp [ne_of_gt hn, ne_of_gt hT] <;> ring
    _ ≤ _ := div_le_div_of_nonneg_left (by linarith) hn (by linarith)

end
end CriticalExtrapolation.Paper
