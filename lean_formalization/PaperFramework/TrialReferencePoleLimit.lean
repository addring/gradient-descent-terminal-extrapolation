import PaperFramework.TrialReferenceModel
import PaperFramework.ReferenceRatio

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

theorem shifted_nat_reciprocal_tendsto_zero (s : ℝ) (hs : 0 ≤ s) :
    Tendsto (fun N : ℕ => 1 / ((N : ℝ) + s)) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop
    (tendsto_atTop_mono (fun N : ℕ => by linarith : ∀ N : ℕ, (N : ℝ) ≤ (N : ℝ) + s)
      tendsto_natCast_atTop_atTop)

theorem shifted_nat_ratio_tendsto_one (s b : ℝ) (hs : 0 ≤ s) :
    Tendsto (fun N : ℕ => ((N : ℝ) + b) / ((N : ℝ) + s)) atTop (𝓝 1) := by
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).add
    ((tendsto_const_nhds (x := b - s)).mul (shifted_nat_reciprocal_tendsto_zero s hs))
  have hh' : Tendsto (fun N : ℕ => 1 + (b - s) * (1 / ((N : ℝ) + s))) atTop (𝓝 1) := by
    simpa using hh
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  field_simp [ne_of_gt (show 0 < (N : ℝ) + s by linarith)]
  <;> ring

theorem referencePoleA_tendsto (s : ℝ) (hs : 2 ≤ s) :
    Tendsto (fun N : ℕ => referencePoleA (N : ℝ) s) atTop (𝓝 2) := by
  have hr := shifted_nat_ratio_tendsto_one s 1 (by linarith : 0 ≤ s)
  have hn := shifted_nat_ratio_tendsto_one s 0 (by linarith : 0 ≤ s)
  have hz := shifted_nat_reciprocal_tendsto_zero s (by linarith : 0 ≤ s)
  have hh : Tendsto (fun N : ℕ => 2 * (((N : ℝ) + 0) / ((N : ℝ) + s)) *
      (((N : ℝ) + 1) / ((N : ℝ) + s)) +
      2 * (((N : ℝ) + 1) / ((N : ℝ) + s)) ^ 2 * (1 / ((N : ℝ) + s))) atTop (𝓝 2) := by
    convert ((tendsto_const_nhds (x := (2 : ℝ))).mul hn |>.mul hr).add
      (((tendsto_const_nhds (x := (2 : ℝ))).mul (hr.pow 2)).mul hz) using 1 <;> norm_num
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hn0 : 0 < (N : ℝ) := by exact_mod_cast hN
  unfold referencePoleA
  field_simp [ne_of_gt (show 0 < (N : ℝ) + s by linarith)]
  <;> ring

theorem referencePoleB_tendsto (s : ℝ) (hs : 2 ≤ s) :
    Tendsto (fun N : ℕ => referencePoleB (N : ℝ) s) atTop (𝓝 (1 - 2 * s)) := by
  have hr := shifted_nat_ratio_tendsto_one s 1 (by linarith : 0 ≤ s)
  have hh : Tendsto (fun N : ℕ => (((N : ℝ) + 1) / ((N : ℝ) + s)) ^ 2 -
      (2 * s) * (((N : ℝ) + 1) / ((N : ℝ) + s))) atTop (𝓝 (1 - 2 * s)) := by
    convert (hr.pow 2).sub ((tendsto_const_nhds (x := 2 * s)).mul hr) using 1 <;> norm_num
  simpa only [referencePoleB, div_pow, mul_div_assoc] using hh

theorem referencePoleD_tendsto (s : ℝ) (hs : 2 ≤ s) :
    Tendsto (fun N : ℕ => referencePoleD (N : ℝ) s) atTop (𝓝 1) := by
  simpa only [referencePoleD, div_pow, one_pow] using
    (shifted_nat_ratio_tendsto_one s 1 (by linarith : 0 ≤ s)).pow 2

end
end CriticalExtrapolation.Paper
