import PaperFramework.TrialProfiles

namespace CriticalExtrapolation.Paper
open scoped BigOperators
open Filter Topology Asymptotics
noncomputable section

theorem shifted_reciprocal_error (s : ℝ) (hs : 2 ≤ s) (N : ℕ) :
    0 ≤ harmonicSum N - (∑ k ∈ Finset.range N, 1 / ((k : ℝ) + s)) ∧
      harmonicSum N - (∑ k ∈ Finset.range N, 1 / ((k : ℝ) + s)) ≤
        (s - 1) * (1 - 1 / ((N : ℝ) + 1)) := by
  induction N with
  | zero => simp [harmonicSum]
  | succ N ih =>
    have hk := Nat.cast_nonneg (α := ℝ) N
    have h1 : 0 < (N : ℝ) + 1 := by linarith
    have h2 : 0 < (N : ℝ) + 2 := by linarith
    have hsN : 0 < (N : ℝ) + s := by linarith
    have hterm0 : 0 ≤ 1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + s) := by
      exact sub_nonneg.mpr (one_div_le_one_div_of_le h1 (by linarith))
    have hterm : 1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + s) ≤
        (s - 1) * (1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + 2)) := by
      have hprod : 0 ≤ (s - 1) * ((N : ℝ) + 1) * (s - 2) :=
        mul_nonneg (mul_nonneg (by linarith) h1.le) (by linarith)
      have hquot : (s - 1) / (((N : ℝ) + 1) * ((N : ℝ) + s)) ≤
          (s - 1) / (((N : ℝ) + 1) * ((N : ℝ) + 2)) :=
        (div_le_div_iff₀ (mul_pos h1 hsN) (mul_pos h1 h2)).mpr (by nlinarith only [hprod])
      convert hquot using 1
      all_goals field_simp [ne_of_gt h1, ne_of_gt h2, ne_of_gt hsN] <;> ring
    have hH : harmonicSum (N + 1) = harmonicSum N + 1 / ((N : ℝ) + 1) := by
      unfold harmonicSum
      rw [Finset.sum_range_succ]
    rw [hH, Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
    constructor <;> nlinarith [ih.1, ih.2, hterm0, hterm]

theorem shifted_reciprocal_log_error (s : ℝ) (hs : 2 ≤ s) (N : ℕ) (hN : 0 < N) :
    |(∑ k ∈ Finset.range N, 1 / ((k : ℝ) + s)) - Real.log (N : ℝ)| ≤ s := by
  have herror := shifted_reciprocal_error s hs N
  have hH := abs_le.mp (harmonicSum_log_error N (by omega))
  have hs1 : 0 ≤ s - 1 := by linarith
  have hmul : 0 ≤ (s - 1) * (1 / ((N : ℝ) + 1)) := mul_nonneg hs1 (by positivity)
  apply abs_le.mpr
  constructor <;> nlinarith [herror.1, herror.2]

theorem trial_normalization_identity (N : ℕ) (t : ℝ) (hN : 0 < N) (ht : 1 ≤ t) :
    trialNormalization N t =
      (∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 2 * t)) +
        ((N : ℝ) + 2 * t + 1) * shiftedHarmonic t N / (N : ℝ) - 1 := by
  let i : Fin N := ⟨0, hN⟩
  have hleft := trialLeft_tail N t i
  have hright := trialRight_tail N t ht i
  simp only [i, Fin.val_zero, Nat.sub_zero, Nat.cast_zero, zero_add, tail_zero] at hleft hright
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp only [div_self hn] at hright
  have hleft' : (∑ i, trialLeft N t i) = ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 2 * t) := by
    simpa only [add_comm] using hleft
  unfold trialNormalization
  rw [trialVector_profiles]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [hleft', hright]
  ring

theorem trial_normalization_log_error (N : ℕ) (t : ℝ) (hN : 0 < N) (ht : 1 ≤ t) :
    |trialNormalization N t - 2 * Real.log (N : ℝ)| ≤ 4 * t + 2 := by
  have hleft := abs_le.mp (shifted_reciprocal_log_error (2 * t) (by linarith) N hN)
  have hright := shifted_reciprocal_log_error (1 + 2 * t) (by linarith) N hN
  have hq : |shiftedHarmonic t N - Real.log (N : ℝ)| ≤ 1 + 2 * t := by
    simpa only [shiftedHarmonic, add_assoc] using hright
  have hqbounds := abs_le.mp hq
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcoef : 0 < 2 * t + 1 := by linarith
  have hq0 := shiftedHarmonic_nonnegative t ht N
  have hqupper := shiftedHarmonic_upper t ht N
  have hcorrection : 0 ≤ (2 * t + 1) * shiftedHarmonic t N / (N : ℝ) ∧
      (2 * t + 1) * shiftedHarmonic t N / (N : ℝ) ≤ 1 := by
    refine ⟨by positivity, (div_le_one hn).mpr ?_⟩
    have hmul := (le_div_iff₀ hcoef).mp hqupper
    nlinarith
  rw [trial_normalization_identity N t hN ht]
  have hid : ((N : ℝ) + 2 * t + 1) * shiftedHarmonic t N / (N : ℝ) =
      shiftedHarmonic t N + (2 * t + 1) * shiftedHarmonic t N / (N : ℝ) := by
    field_simp [ne_of_gt hn]
    <;> ring
  rw [hid]
  apply abs_le.mpr
  constructor <;> linarith [hleft.1, hleft.2, hqbounds.1, hqbounds.2, hcorrection.1, hcorrection.2]

/-- Equation (9.2), proved with an explicit bounded error for the shifted harmonic sums. -/
theorem trial_normalization_asymptotic (t : ℝ) (ht : 1 ≤ t) :
    (fun N : ℕ => trialNormalization N t - 2 * Real.log (N : ℝ)) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (4 * t + 2)
  filter_upwards [eventually_gt_atTop 0] with N hN
  simpa only [Real.norm_eq_abs, norm_one, mul_one] using trial_normalization_log_error N t hN ht

end
end CriticalExtrapolation.Paper
