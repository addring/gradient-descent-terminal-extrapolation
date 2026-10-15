import PaperFramework.LargeQuadratic
import PaperFramework.ProblemAndHuber
import Mathlib.Analysis.SpecificLimits.Normed

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

theorem original_quadratic_tail_decay (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 2 * (1 / h)) * (1 - h) ^ N)
      atTop (𝓝 0) := by
  have hr : 0 ≤ 1 - h := by linarith
  have hr1 : 1 - h < 1 := by linarith
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1
  have hnp := tendsto_self_mul_const_pow_of_lt_one hr hr1
  convert hnp.add ((tendsto_const_nhds (x := 2 * (1 / h))).mul hp) using 1
  · ext N
    ring
  · simp

/-- A single quadratic covers the entire unbounded right tail, uniformly in a. -/
theorem original_quadratic_tail_failure (h L D : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 0 < L) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, ∀ a ≥ 2 * (1 / h),
      L * D / S N h (1 + a / (N : ℝ)) <
        worstGradient N h (1 + a / (N : ℝ)) L D := by
  let t : ℝ := 1 / h
  have ht : 0 < t := one_div_pos.mpr hh
  have hsmall : ∀ᶠ N : ℕ in atTop,
      ((N : ℝ) + 2 * t) * (1 - h) ^ N < t :=
    (original_quadratic_tail_decay h hh hh1).eventually (gt_mem_nhds ht)
  filter_upwards [hsmall, eventually_gt_atTop 0] with N hs hN
  intro a ha
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have ha0 : 0 ≤ a := by linarith
  let c : ℝ := 1 + a / (N : ℝ)
  have hc : 1 ≤ c := by
    dsimp [c]
    exact le_add_of_nonneg_right (div_nonneg ha0 hn.le)
  let r : ℝ := (1 - h) ^ N
  have hr1 : r ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  let y : ℝ := 1 - c * (1 - r)
  have hid : (N : ℝ) * (-y) = a * (1 - r) - (N : ℝ) * r := by
    dsimp [y, c]
    field_simp [hn.ne']
    <;> ring
  have hny : t < (N : ℝ) * (-y) := by
    rw [hid]
    have hm := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hr1)
    change ((N : ℝ) + 2 * t) * r < t at hs
    nlinarith only [hm, hs]
  have hy : t / (N : ℝ) < -y := by
    apply (div_lt_iff₀ hn).mpr
    nlinarith only [hny]
  have hB : 1 / S N h c < t / (N : ℝ) := by
    have he : S N h c = h * ((N : ℝ) + a + t) := by
      dsimp [S, c, t]
      field_simp [hn.ne', hh.ne']
      <;> ring
    have hbound : 1 / S N h c = t / ((N : ℝ) + a + t) := by
      rw [he]
      dsimp [t]
      field_simp
    rw [hbound]
    exact div_lt_div_of_pos_left ht hn (by linarith)
  let I₀ := quadraticUnitInstance 1 unitOne
  have hrad : D * ‖unitOne‖ ≤ D := by rw [unitOne_norm, mul_one]
  let I := dilatedInstance I₀ L D D hL hD hrad
  have hbase : ‖gradient I₀.f (output I₀ N h c)‖ = |y| := by
    change ‖gradient halfSquaredNorm (output (quadraticUnitInstance 1 unitOne) N h c)‖ = _
    rw [quadraticUnitInstance_output, halfSquaredNorm_gradient, norm_smul,
      Real.norm_eq_abs, unitOne_norm, mul_one]
  have hgrad : ‖gradient I.f (output I N h c)‖ = L * D * |y| := by
    change ‖gradient (dilatedInstance I₀ L D D hL hD hrad).f
      (output (dilatedInstance I₀ L D D hL hD hrad) N h c)‖ = _
    rw [dilatedInstance_output, dilatedInstance_gradient, norm_smul,
      Real.norm_eq_abs, abs_of_pos (mul_pos hL hD), hbase]
  have hstrict := mul_lt_mul_of_pos_left
    ((hB.trans hy).trans_le (neg_le_abs y)) (mul_pos hL hD)
  have hactual : L * D / S N h c < ‖gradient I.f (output I N h c)‖ := by
    rw [hgrad]
    convert hstrict using 1 <;> ring
  have hsup : ‖gradient I.f (output I N h c)‖ ≤ worstGradient N h c L D :=
    le_csSup (instance_values_nonempty_bounded N h c L D hL hD).2 ⟨1, I, rfl⟩
  exact hactual.trans_le hsup

end
end CriticalExtrapolation.Paper
