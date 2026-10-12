import PaperFramework.TrialReferenceFiniteBounds

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem trial_reference_profile_error_sum (N : ℕ) (t : ℝ)
    (hN : 0 < N) (ht : 1 ≤ t) :
    (∑ i : Fin N, |tailU 0 1 (trialVector N t) i -
      1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t))|) ≤
        (1 + 4 * t) / (N : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hT : 0 < (N : ℝ) + 2 * t := by linarith
  let d0 : Fin N → ℝ := fun i => 2 * t /
    ((N : ℝ) * ((N : ℝ) + 2 * t) * ((N : ℝ) - i.val + 1))
  let dL : Fin N → ℝ := fun i =>
    (tail (trialLeft N t) i.val - ((N : ℝ) - i.val) / ((N : ℝ) + 2 * t)) /
      (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1))
  let dQ : Fin N → ℝ := fun i => 2 * t * shiftedHarmonic t (N - i.val) /
    ((N : ℝ) * ((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1))
  have hp : ∀ i : Fin N, |tailU 0 1 (trialVector N t) i -
      1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t))| ≤ d0 i + dL i + dQ i := by
    intro i
    have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
    have hj : 0 < (N : ℝ) - i.val := sub_pos.mpr hi
    have h0 : 0 ≤ d0 i := by dsimp [d0]; positivity
    have hL : 0 ≤ dL i := div_nonneg
      (sub_nonneg.mpr (trialLeft_tail_reference_lower N t ht i)) (by positivity)
    have hQ : 0 ≤ dQ i := div_nonneg
      (mul_nonneg (by linarith) (shiftedHarmonic_nonnegative t ht _)) (by positivity)
    rw [trial_baseline_reciprocal_difference N t ht i]
    change |d0 i - dL i - dQ i| ≤ d0 i + dL i + dQ i
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h0 := trial_reciprocal_model_positive_correction_sum N t hN ht
  have hL := trialLeft_remainder_weighted_sum_upper N t hN ht
  have hQ : (∑ i : Fin N, dQ i) ≤ 2 * t / (N : ℝ) := by
    have heq : (∑ i : Fin N, dQ i) = (2 * t / (N : ℝ)) *
        ∑ i : Fin N, shiftedHarmonic t (N - i.val) /
          (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
      dsimp [dQ]
      field_simp [ne_of_gt hn, ne_of_gt (sub_pos.mpr hi),
        ne_of_gt (show 0 < (N : ℝ) - i.val + 1 by linarith)]
      <;> ring
    rw [heq]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (shiftedHarmonic_endpoint_weight_sum N t ht) (show 0 ≤ 2 * t / (N : ℝ) by positivity)
  calc
    _ ≤ ∑ i : Fin N, (d0 i + dL i + dQ i) := Finset.sum_le_sum (fun i _ => hp i)
    _ = (∑ i : Fin N, d0 i) + (∑ i : Fin N, dL i) + ∑ i : Fin N, dQ i := by
      simp only [Finset.sum_add_distrib]
    _ ≤ 2 * t / (N : ℝ) + 1 / (N : ℝ) + 2 * t / (N : ℝ) :=
      add_le_add (add_le_add h0 hL) hQ
    _ = _ := by ring

def reciprocalReferenceEnergy (N : ℕ) (t : ℝ) : ℝ :=
  ∑ i : Fin N, ((N : ℝ) + 1) ^ 2 * referenceWeight (N : ℝ) (i.val : ℝ) *
    (1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t))) ^ 2

theorem trial_reference_energy_model_error (N : ℕ) (t : ℝ)
    (hN : 0 < N) (ht : 1 ≤ t) :
    |homogeneousEnergy 0 1 (trialVector N t) - reciprocalReferenceEnergy N t| ≤
      12 * (2 + 2 * t) * (1 + 4 * t) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [trial_reference_energy_sum N t hN]
  unfold reciprocalReferenceEnergy
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin N, |((N : ℝ) + 1) ^ 2 * referenceWeight (N : ℝ) (i.val : ℝ) *
        (tailU 0 1 (trialVector N t) i) ^ 2 -
      ((N : ℝ) + 1) ^ 2 * referenceWeight (N : ℝ) (i.val : ℝ) *
        (1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t))) ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, 12 * (2 + 2 * t) * (N : ℝ) *
        |tailU 0 1 (trialVector N t) i -
          1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t))| :=
      Finset.sum_le_sum (fun i _ => trial_reference_pointwise_energy_error N t hN ht i)
    _ = 12 * (2 + 2 * t) * (N : ℝ) * ∑ i : Fin N,
        |tailU 0 1 (trialVector N t) i -
          1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t))| := by rw [Finset.mul_sum]
    _ ≤ 12 * (2 + 2 * t) * (N : ℝ) * ((1 + 4 * t) / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (trial_reference_profile_error_sum N t hN ht) (by positivity)
    _ = _ := by field_simp [ne_of_gt hn] <;> ring

end
end CriticalExtrapolation.Paper
