import PaperFramework.FirstOrderConvex
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace CriticalExtrapolation.Paper
open Set
noncomputable section

/-- Integrating the unit gradient bound along a segment, expressed by scalar monotonicity. -/
theorem unit_smooth_descent {d : ℕ} (f : Space d → ℝ) (hdiff : Differentiable ℝ f)
    (hlip : ∀ x z, ‖gradient f x - gradient f z‖ ≤ ‖x - z‖) (x v : Space d) :
    f (x + v) ≤ f x + inner ℝ (gradient f x) v + ‖v‖ ^ 2 / 2 := by
  let a : ℝ := inner ℝ (gradient f x) v
  let b : ℝ := ‖v‖ ^ 2
  let φ : ℝ → ℝ := fun t => f (x + t • v) - t * a - t ^ 2 * b / 2
  have hderiv : ∀ t : ℝ, HasDerivAt φ
      (inner ℝ (gradient f (x + t • v)) v - a - t * b) t := by
    intro t
    dsimp [φ]
    convert ((affine_line_hasDerivAt f hdiff x v t).sub
      ((hasDerivAt_id t).mul_const a)).sub
      ((((hasDerivAt_id t).pow 2).mul_const b).div_const 2) using 1
      <;> simp only [id_eq] <;> ring
  have hnonpos : ∀ t ∈ interior (Icc (0 : ℝ) 1),
      inner ℝ (gradient f (x + t • v)) v - a - t * b ≤ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have hbound := hlip (x + t • v) x
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hbound
    have hc := (abs_le.mp (abs_real_inner_le_norm
      (gradient f (x + t • v) - gradient f x) v)).2
    rw [inner_sub_left] at hc
    have hm := mul_le_mul_of_nonneg_right hbound (norm_nonneg v)
    dsimp [a, b]
    nlinarith only [hc, hm]
  have hanti : AntitoneOn φ (Icc (0 : ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      ((continuous_iff_continuousAt.mpr (fun t => (hderiv t).continuousAt)).continuousOn)
      (fun t _ => (hderiv t).hasDerivWithinAt) hnonpos
  have h := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [φ, a, b, one_smul, zero_smul, add_zero, one_mul, one_pow,
    zero_mul, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero] at h
  linarith

theorem smooth_convex_interpolation_necessary_proved {d : ℕ} (f : Space d → ℝ)
    (hf : SmoothConvexOne f) (x z : Space d) :
    0 ≤ f x - f z - inner ℝ (gradient f z) (x - z) -
      ‖gradient f x - gradient f z‖ ^ 2 / 2 := by
  let w : Space d := gradient f x - gradient f z
  have hup := unit_smooth_descent f hf.2.1 hf.2.2 x (-w)
  have hlow := convex_gradient_support f hf.1 hf.2.1 z (x - w)
  rw [show x + -w = x - w by abel, inner_neg_right, norm_neg] at hup
  rw [show x - w - z = (x - z) - w by abel, inner_sub_right] at hlow
  have hinner : inner ℝ (gradient f x) w - inner ℝ (gradient f z) w = ‖w‖ ^ 2 := by
    rw [← inner_sub_left]
    exact real_inner_self_eq_norm_sq w
  change 0 ≤ f x - f z - inner ℝ (gradient f z) (x - z) - ‖w‖ ^ 2 / 2
  linarith

end
end CriticalExtrapolation.Paper
