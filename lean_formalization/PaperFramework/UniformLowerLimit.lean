import PaperFramework.UniformMassBounds
import PaperFramework.UniformErrorBounds

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

theorem finiteLowerBound_uniform_scaled_limit (h : ℝ) (hh : 0 < h) (K : ℝ) :
    UniformOn 0 K (fun N k => Real.log (N : ℝ) * finiteLowerBound N h (scaledC N h k))
      (fun k => 1 - k ^ 2) := by
  let t : ℝ := 1 / h
  let b : ℕ → ℝ := fun N =>
    |Real.log (N : ℝ) / referenceReciprocalSum N - 1| +
      (1 + K ^ 2) * (2 * scaledA N h K / t) +
      Real.log (N : ℝ) * scaledA N h K / (N : ℝ)
  have ht : 0 < t := one_div_pos.mpr hh
  have herr : Tendsto (fun N : ℕ => |Real.log (N : ℝ) / referenceReciprocalSum N - 1|)
      atTop (𝓝 0) := by
    simpa using (log_div_referenceReciprocalSum_tendsto.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
  have hmass : Tendsto (fun N : ℕ => (1 + K ^ 2) * (2 * scaledA N h K / t))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 1 + K ^ 2)).mul
      (((tendsto_const_nhds (x := (2 : ℝ))).mul (scaledA_tendsto_zero h K hh)).div_const t)
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa only [zero_add] using (herr.add hmass).add (log_scaledA_div_nat_tendsto_zero h K hh)
  apply uniformOn_of_uniform_error_bound 0 K _ _ b hb
  filter_upwards [eventually_gt_atTop 1] with N hN
  intro k hk
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos hn
  have ha : 0 ≤ scaledA N h k := div_nonneg hk.1 (by positivity)
  have hmono : scaledA N h k ≤ scaledA N h K := div_le_div_of_nonneg_right hk.2 (by positivity)
  have hdrift : 0 ≤ Real.log (N : ℝ) * scaledA N h k / (N : ℝ) := by positivity
  have he := scaled_mass_main_error_bound (scaledA N h k) t
    (Real.log (N : ℝ) / referenceReciprocalSum N) k K ha ht hk
  rw [finiteLowerBound_scaled_identity N h k hN hh]
  change |(shiftMass (scaledA N h k) t) ^ 2 *
      (Real.log (N : ℝ) / referenceReciprocalSum N - k ^ 2) -
      Real.log (N : ℝ) * scaledA N h k / (N : ℝ) - (1 - k ^ 2)| ≤ b N
  calc
    _ = |((shiftMass (scaledA N h k) t) ^ 2 *
        (Real.log (N : ℝ) / referenceReciprocalSum N - k ^ 2) - (1 - k ^ 2)) +
        -(Real.log (N : ℝ) * scaledA N h k / (N : ℝ))| := by congr 1; ring
    _ ≤ |(shiftMass (scaledA N h k) t) ^ 2 *
        (Real.log (N : ℝ) / referenceReciprocalSum N - k ^ 2) - (1 - k ^ 2)| +
      Real.log (N : ℝ) * scaledA N h k / (N : ℝ) := by
        simpa only [Real.norm_eq_abs, abs_neg, abs_of_nonneg hdrift] using norm_add_le
          ((shiftMass (scaledA N h k) t) ^ 2 *
            (Real.log (N : ℝ) / referenceReciprocalSum N - k ^ 2) - (1 - k ^ 2))
          (-(Real.log (N : ℝ) * scaledA N h k / (N : ℝ)))
    _ ≤ |Real.log (N : ℝ) / referenceReciprocalSum N - 1| +
        (1 + K ^ 2) * (2 * scaledA N h k / t) +
        Real.log (N : ℝ) * scaledA N h k / (N : ℝ) := add_le_add he (le_refl _)
    _ ≤ b N := by
      apply add_le_add
      · exact add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmono (by norm_num)) ht.le)
            (by positivity))
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hl.le)
          (Nat.cast_nonneg _)

end
end CriticalExtrapolation.Paper
