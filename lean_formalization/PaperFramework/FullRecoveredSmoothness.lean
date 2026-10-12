import PaperFramework.FullConjugateExistence
import Mathlib.Analysis.Asymptotics.Lemmas

namespace CriticalExtrapolation.Paper
open Filter Topology Asymptotics
noncomputable section

theorem full_conjugate_recovered_support {N d : ℕ} (data : Sample N d) (x u : Space d) :
    inner ℝ x u - fullConjugatePotential data u ≤ fullRecoveredFunction data x := by
  obtain ⟨v, hv⟩ := full_conjugate_minimizer_exists data x
  rw [full_conjugate_minimizer_recovered_value data x v hv]
  have h := hv u
  linarith

theorem full_conjugate_optimizer_nonexpansive {N d : ℕ} (data : Sample N d)
    (x z u v : Space d) (hu : FullConjugateMinimizer data x u)
    (hv : FullConjugateMinimizer data z v) : ‖u - v‖ ≤ ‖x - z‖ := by
  have hf := full_conjugate_optimizer_firm_nonexpansive_proved data x z u v hu hv
  have hc := (abs_le.mp (abs_real_inner_le_norm (x - z) (u - v))).2
  by_cases hzero : ‖u - v‖ = 0
  · rw [hzero]
    exact norm_nonneg _
  have hpos : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (fun h => hzero h.symm)
  refine le_of_mul_le_mul_right ?_ hpos
  nlinarith only [hf, hc]

theorem full_recovered_linear_error_bounds {N d : ℕ} (data : Sample N d)
    (x y u : Space d) (hu : FullConjugateMinimizer data x u) :
    0 ≤ fullRecoveredFunction data y - fullRecoveredFunction data x - inner ℝ u (y - x) ∧
      fullRecoveredFunction data y - fullRecoveredFunction data x - inner ℝ u (y - x) ≤ ‖y - x‖ ^ 2 := by
  have hlin : inner ℝ u (y - x) = inner ℝ y u - inner ℝ x u := by
    rw [real_inner_comm, inner_sub_left]
  rw [hlin]
  have hx := full_conjugate_minimizer_recovered_value data x u hu
  constructor
  · have hsupport := full_conjugate_recovered_support data y u
    rw [hx]
    linarith
  · obtain ⟨v, hv⟩ := full_conjugate_minimizer_exists data y
    have hy := full_conjugate_minimizer_recovered_value data y v hv
    have hupper : fullRecoveredFunction data y - fullRecoveredFunction data x -
        (inner ℝ y u - inner ℝ x u) ≤ inner ℝ (y - x) (v - u) := by
      rw [hx, hy, inner_sub_left, inner_sub_right, inner_sub_right]
      have h := hu v
      linarith
    have hlip := full_conjugate_optimizer_nonexpansive data y x v u hv hu
    calc
      _ ≤ inner ℝ (y - x) (v - u) := hupper
      _ ≤ ‖y - x‖ * ‖v - u‖ := (abs_le.mp (abs_real_inner_le_norm _ _)).2
      _ ≤ ‖y - x‖ * ‖y - x‖ := mul_le_mul_of_nonneg_left hlip (norm_nonneg _)
      _ = _ := by ring

theorem full_recovered_hasGradientAt {N d : ℕ} (data : Sample N d) (x u : Space d)
    (hu : FullConjugateMinimizer data x u) : HasGradientAt (fullRecoveredFunction data) u x := by
  apply hasGradientAt_iff_isLittleO_nhds_zero.mpr
  have hbound : ∀ h : Space d,
      ‖fullRecoveredFunction data (x + h) - fullRecoveredFunction data x - inner ℝ u h‖ ≤ ‖‖h‖ ^ 2‖ := by
    intro h
    have hb := full_recovered_linear_error_bounds data x (x + h) u hu
    rw [show x + h - x = h by abel] at hb
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1, abs_of_nonneg (sq_nonneg ‖h‖)] using hb.2
  have hO : (fun h : Space d => fullRecoveredFunction data (x + h) -
      fullRecoveredFunction data x - inner ℝ u h) =O[𝓝 0] (fun h : Space d => ‖h‖ ^ 2) :=
    IsBigO.of_bound' (Eventually.of_forall hbound)
  exact hO.trans_isLittleO (isLittleO_norm_pow_id (by decide : 1 < 2))

theorem fullRecoveredFunction_convex {N d : ℕ} (data : Sample N d) :
    ConvexOn ℝ Set.univ (fullRecoveredFunction data) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  obtain ⟨u, hu⟩ := full_conjugate_minimizer_exists data (a • x + b • y)
  rw [full_conjugate_minimizer_recovered_value data (a • x + b • y) u hu]
  simp only [smul_eq_mul]
  have hid : inner ℝ (a • x + b • y) u - fullConjugatePotential data u =
      a * (inner ℝ x u - fullConjugatePotential data u) +
        b * (inner ℝ y u - fullConjugatePotential data u) := by
    simp only [inner_add_left, real_inner_smul_left]
    linear_combination (congrArg (fun r : ℝ => r * fullConjugatePotential data u) hab)
  rw [hid]
  exact add_le_add (mul_le_mul_of_nonneg_left (full_conjugate_recovered_support data x u) ha)
    (mul_le_mul_of_nonneg_left (full_conjugate_recovered_support data y u) hb)

theorem full_recovered_function_global_smoothness_proved {N d : ℕ} (data : Sample N d) :
    SmoothConvexOne (fullRecoveredFunction data) ∧
      ∀ x u, FullConjugateMinimizer data x u → gradient (fullRecoveredFunction data) x = u := by
  have hgradient : ∀ x u, FullConjugateMinimizer data x u →
      gradient (fullRecoveredFunction data) x = u :=
    fun x u hu => (full_recovered_hasGradientAt data x u hu).gradient
  refine ⟨⟨fullRecoveredFunction_convex data, ?_, ?_⟩, hgradient⟩
  · intro x
    obtain ⟨u, hu⟩ := full_conjugate_minimizer_exists data x
    exact (full_recovered_hasGradientAt data x u hu).differentiableAt
  · intro x z
    obtain ⟨u, hu⟩ := full_conjugate_minimizer_exists data x
    obtain ⟨v, hv⟩ := full_conjugate_minimizer_exists data z
    rw [hgradient x u hu, hgradient z v hv]
    exact full_conjugate_optimizer_nonexpansive data x z u v hu hv

end
end CriticalExtrapolation.Paper

