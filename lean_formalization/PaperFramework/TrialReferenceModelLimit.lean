import PaperFramework.TrialReferenceEnergyError
import PaperFramework.TrialReferencePoleLimit
import PaperFramework.TrialReferenceSumLimit

namespace CriticalExtrapolation.Paper
open scoped BigOperators
open Filter Topology
noncomputable section

theorem reciprocalReferenceEnergy_decomposition (N : ℕ) (t : ℝ)
    (hN : 0 < N) (ht : 1 ≤ t) :
    reciprocalReferenceEnergy N t =
      referencePoleA (N : ℝ) (2 * t) *
        ((∑ i : Fin N, 1 / ((i.val : ℝ) + 2 * t)) + harmonicSum N) +
      referencePoleB (N : ℝ) (2 * t) *
        (∑ i : Fin N, (1 / ((i.val : ℝ) + 2 * t)) ^ 2) +
      referencePoleD (N : ℝ) (2 * t) *
        (∑ i : Fin N, (1 / ((N : ℝ) - i.val)) ^ 2) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hterm : ∀ i : Fin N,
      ((N : ℝ) + 1) ^ 2 * referenceWeight (N : ℝ) (i.val : ℝ) *
        (1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t))) ^ 2 =
      referencePoleA (N : ℝ) (2 * t) *
        (1 / ((i.val : ℝ) + 2 * t) + 1 / ((N : ℝ) - i.val)) +
      referencePoleB (N : ℝ) (2 * t) * (1 / ((i.val : ℝ) + 2 * t)) ^ 2 +
      referencePoleD (N : ℝ) (2 * t) * (1 / ((N : ℝ) - i.val)) ^ 2 := by
    intro i
    have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
    have hu : 0 < (i.val : ℝ) + 2 * t := by have := Nat.cast_nonneg (α := ℝ) i.val; linarith
    have hj : 0 < (N : ℝ) - i.val := sub_pos.mpr hi
    have hh := scalar_reference_partial_fraction (N : ℝ) (2 * t) (i.val : ℝ)
      hn (by linarith) (Nat.cast_nonneg _) hi
    convert hh using 1
    all_goals field_simp [ne_of_gt hu, ne_of_gt hj] <;> ring
  unfold reciprocalReferenceEnergy
  simp_rw [hterm, mul_add]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [trial_reciprocal_right_sum]

theorem reciprocalReferenceEnergy_div_log_tendsto (t : ℝ) (ht : 1 ≤ t) :
    Tendsto (fun N : ℕ => reciprocalReferenceEnergy N t / Real.log (N : ℝ))
      atTop (𝓝 4) := by
  have hA := referencePoleA_tendsto (2 * t) (by linarith : 2 ≤ 2 * t)
  have hB := referencePoleB_tendsto (2 * t) (by linarith : 2 ≤ 2 * t)
  have hD := referencePoleD_tendsto (2 * t) (by linarith : 2 ≤ 2 * t)
  have hL := trialLeft_reciprocal_sum_div_log_tendsto t ht
  have hH := harmonicSum_div_log_tendsto
  have hSL := trialLeft_reciprocal_square_div_log_tendsto t ht
  have hSR := trialRight_reciprocal_square_div_log_tendsto
  have hh : Tendsto (fun N : ℕ =>
      referencePoleA (N : ℝ) (2 * t) *
        ((∑ i : Fin N, 1 / ((i.val : ℝ) + 2 * t)) / Real.log (N : ℝ) +
          harmonicSum N / Real.log (N : ℝ)) +
      referencePoleB (N : ℝ) (2 * t) *
        ((∑ i : Fin N, (1 / ((i.val : ℝ) + 2 * t)) ^ 2) / Real.log (N : ℝ)) +
      referencePoleD (N : ℝ) (2 * t) *
        ((∑ i : Fin N, (1 / ((N : ℝ) - i.val)) ^ 2) / Real.log (N : ℝ)))
      atTop (𝓝 4) := by
    convert ((hA.mul (hL.add hH)).add (hB.mul hSL)).add (hD.mul hSR) using 1 <;> norm_num
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [reciprocalReferenceEnergy_decomposition N t hN ht]
  ring

theorem trial_reference_energy_limit_proved (t : ℝ) (ht : 1 ≤ t) :
    Tendsto (fun N : ℕ => homogeneousEnergy 0 1 (trialVector N t) / Real.log (N : ℝ))
      atTop (𝓝 4) := by
  have hz : Tendsto (fun N : ℕ =>
      (homogeneousEnergy 0 1 (trialVector N t) - reciprocalReferenceEnergy N t) /
        Real.log (N : ℝ)) atTop (𝓝 0) := by
    apply bounded_div_log_tendsto_zero _ (12 * (2 + 2 * t) * (1 + 4 * t))
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact trial_reference_energy_model_error N t hN ht
  have hh : Tendsto (fun N : ℕ =>
      (homogeneousEnergy 0 1 (trialVector N t) - reciprocalReferenceEnergy N t) /
        Real.log (N : ℝ) + reciprocalReferenceEnergy N t / Real.log (N : ℝ))
      atTop (𝓝 4) := by
    simpa only [zero_add] using hz.add (reciprocalReferenceEnergy_div_log_tendsto t ht)
  convert hh using 1
  funext N
  ring

end
end CriticalExtrapolation.Paper
