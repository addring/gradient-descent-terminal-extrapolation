import PaperFramework.TrialHarmonicBounds
import PaperFramework.TrialWeightedSum
import PaperFramework.ReferenceRatio

namespace CriticalExtrapolation.Paper
open scoped BigOperators
open Filter Topology
noncomputable section

theorem bounded_div_log_tendsto_zero (f : ℕ → ℝ) (C : ℝ)
    (hb : ∀ᶠ N in atTop, |f N| ≤ C) :
    Tendsto (fun N : ℕ => f N / Real.log (N : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun N : ℕ => |f N / Real.log (N : ℝ)|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _
      (tendsto_const_nhds.div_atTop hlog :
        Tendsto (fun N : ℕ => C / Real.log (N : ℝ)) atTop (𝓝 0))
    filter_upwards [hb, eventually_ge_atTop 2] with N hN hN2
    have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    rw [abs_div, abs_of_pos (Real.log_pos hn)]
    exact div_le_div_of_nonneg_right hN (Real.log_pos hn).le
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hz)

theorem log_quotient_tendsto_of_bounded_error (f : ℕ → ℝ) (a C : ℝ)
    (hb : ∀ᶠ N in atTop, |f N - a * Real.log (N : ℝ)| ≤ C) :
    Tendsto (fun N : ℕ => f N / Real.log (N : ℝ)) atTop (𝓝 a) := by
  have hz := bounded_div_log_tendsto_zero (fun N => f N - a * Real.log (N : ℝ)) C hb
  have hh : Tendsto (fun N : ℕ =>
      (f N - a * Real.log (N : ℝ)) / Real.log (N : ℝ) + a) atTop (𝓝 a) := by
    simpa only [zero_add] using hz.add (tendsto_const_nhds (x := a))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  field_simp [ne_of_gt (Real.log_pos hn)]
  <;> ring

theorem trialLeft_reciprocal_sum_div_log_tendsto (t : ℝ) (ht : 1 ≤ t) :
    Tendsto (fun N : ℕ => (∑ i : Fin N, 1 / ((i.val : ℝ) + 2 * t)) /
      Real.log (N : ℝ)) atTop (𝓝 1) := by
  apply log_quotient_tendsto_of_bounded_error _ 1 (2 * t)
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [one_mul, Fin.sum_univ_eq_sum_range (fun k : ℕ => 1 / ((k : ℝ) + 2 * t)) N]
  exact shifted_reciprocal_log_error (2 * t) (by linarith) N hN

theorem harmonicSum_div_log_tendsto :
    Tendsto (fun N : ℕ => harmonicSum N / Real.log (N : ℝ)) atTop (𝓝 1) := by
  apply log_quotient_tendsto_of_bounded_error _ 1 1
  filter_upwards [eventually_ge_atTop 1] with N hN
  simpa only [one_mul] using harmonicSum_log_error N hN

theorem trialRight_reciprocal_square_sum_upper (N : ℕ) :
    (∑ i : Fin N, (1 / ((N : ℝ) - i.val)) ^ 2) ≤ 2 := by
  have heq : (∑ i : Fin N, (1 / ((N : ℝ) - i.val)) ^ 2) =
      ∑ i : Fin N, (1 / ((N - i.val : ℕ) : ℝ)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.le_of_lt i.isLt)]
  rw [heq, trial_reverse_sum N (fun j : ℕ => (1 / (j : ℝ)) ^ 2)]
  simp only [Nat.cast_add, Nat.cast_one, div_pow, one_pow]
  exact trial_reciprocal_square_sum_upper N

theorem trialLeft_reciprocal_square_div_log_tendsto (t : ℝ) (ht : 1 ≤ t) :
    Tendsto (fun N : ℕ => (∑ i : Fin N, (1 / ((i.val : ℝ) + 2 * t)) ^ 2) /
      Real.log (N : ℝ)) atTop (𝓝 0) := by
  apply bounded_div_log_tendsto_zero _ 2
  apply Eventually.of_forall
  intro N
  rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  exact trialLeft_square_sum_upper N t ht

theorem trialRight_reciprocal_square_div_log_tendsto :
    Tendsto (fun N : ℕ => (∑ i : Fin N, (1 / ((N : ℝ) - i.val)) ^ 2) /
      Real.log (N : ℝ)) atTop (𝓝 0) := by
  apply bounded_div_log_tendsto_zero _ 2
  apply Eventually.of_forall
  intro N
  rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  exact trialRight_reciprocal_square_sum_upper N

end
end CriticalExtrapolation.Paper
