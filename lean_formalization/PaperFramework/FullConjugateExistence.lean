import PaperFramework.FullConjugateGrowth
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

namespace CriticalExtrapolation.Paper
noncomputable section

theorem fullConjugatePotential_support_lower {N d : ℕ} (data : Sample N d)
    (i : Query N) (u : Space d) :
    ‖u‖ ^ 2 / 2 + (inner ℝ (data.x i - data.g i) (u - data.g i) +
      interpolationIntercept data i) ≤
      fullConjugatePotential data u := by
  classical
  rw [fullConjugatePotential, fullConjugateAffineMaximum]
  exact add_le_add (le_refl _)
    (Finset.le_sup' (fun j : Query N => inner ℝ (data.x j - data.g j) (u - data.g j) +
      interpolationIntercept data j)
      (Finset.mem_univ i))

/-- A single affine support makes the tilted potential coercive in every finite dimension. -/
theorem full_conjugate_minimizer_exists {N d : ℕ} (data : Sample N d) (x : Space d) :
    ∃ u, FullConjugateMinimizer data x u := by
  let r := data.x (starQuery N) - data.g (starQuery N)
  let q := data.g (starQuery N)
  let a : ℝ := ‖r - x‖
  let b : ℝ := inner ℝ r q - interpolationIntercept data (starQuery N)
  let φ : Space d → ℝ := fun u => fullConjugatePotential data u - inner ℝ x u
  let B : ℝ := |φ 0 + b|
  let R : ℝ := 2 * a + 2 * B + 2
  have ha : 0 ≤ a := norm_nonneg _
  have hB : 0 ≤ B := abs_nonneg _
  have hR : 0 < R := by dsimp [R]; linarith
  have hlower : ∀ u : Space d, ‖u‖ ^ 2 / 2 - a * ‖u‖ - b ≤ φ u := by
    intro u
    have hs := fullConjugatePotential_support_lower data (starQuery N) u
    change ‖u‖ ^ 2 / 2 + (inner ℝ r (u - q) + interpolationIntercept data (starQuery N)) ≤
      fullConjugatePotential data u at hs
    have habs := abs_real_inner_le_norm (r - x) u
    have hinner := (abs_le.mp habs).1
    rw [inner_sub_left] at hinner
    rw [inner_sub_right] at hs
    dsimp [a, b, φ]
    linarith
  have houtside : ∀ u : Space d, R < ‖u‖ → φ 0 ≤ φ u := by
    intro u hu
    have hu1 : 1 ≤ ‖u‖ := by dsimp [R] at hu; linarith
    have hfactor : 2 * (B + 1) ≤ ‖u‖ - 2 * a := by dsimp [R] at hu; linarith
    have hm := mul_le_mul_of_nonneg_left hfactor (norm_nonneg u)
    have hn := le_mul_of_one_le_left (show 0 ≤ B + 1 by linarith) hu1
    have hval : φ 0 + b ≤ B := le_abs_self _
    have hl := hlower u
    nlinarith only [hm, hn, hval, hl]
  have hcont : Continuous φ := by
    apply (fullConjugatePotential_continuous data).sub
    fun_prop
  have hzero : (0 : Space d) ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_self] using hR.le
  obtain ⟨u, hu, hmin⟩ := (isCompact_closedBall (0 : Space d) R).exists_isMinOn
    ⟨0, hzero⟩ hcont.continuousOn
  refine ⟨u, ?_⟩
  intro v
  change φ u ≤ φ v
  by_cases hv : v ∈ Metric.closedBall (0 : Space d) R
  · exact hmin hv
  · have hnorm : R < ‖v‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hv
    exact (hmin hzero).trans (houtside v hnorm)

theorem full_conjugate_minimizer_exists_unique_proved {N d : ℕ} (data : Sample N d) (x : Space d) :
    ∃! u, FullConjugateMinimizer data x u := by
  obtain ⟨u, hu⟩ := full_conjugate_minimizer_exists data x
  refine ⟨u, hu, ?_⟩
  intro v hv
  have hfirm := full_conjugate_optimizer_firm_nonexpansive_proved data x x v u hv hu
  simp only [sub_self, inner_zero_left] at hfirm
  have hnorm : ‖v - u‖ = 0 := by nlinarith [norm_nonneg (v - u)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end
end CriticalExtrapolation.Paper

