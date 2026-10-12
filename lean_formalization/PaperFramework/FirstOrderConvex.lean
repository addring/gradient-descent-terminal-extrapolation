import PaperFramework.Definitions
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace CriticalExtrapolation.Paper
open InnerProductSpace
noncomputable section

theorem affine_line_hasDerivAt {d : ℕ} (f : Space d → ℝ) (hf : Differentiable ℝ f)
    (x v : Space d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (inner ℝ (gradient f (x + t • v)) v) t := by
  have hpath : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa only [one_smul] using ((hasDerivAt_id t).smul_const v).const_add x
  simpa only [Function.comp_def, toDual_apply_apply] using
    ((hf (x + t • v)).hasGradientAt.hasFDerivAt.comp_hasDerivAt t hpath)

theorem affine_line_convex {d : ℕ} (f : Space d → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (x v : Space d) :
    ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • v)) := by
  simpa only [Set.preimage_univ, Function.comp_def, AffineMap.lineMap_apply_module',
    add_sub_cancel_left, add_comm] using hf.comp_affineMap (AffineMap.lineMap x (x + v))

theorem convex_gradient_support {d : ℕ} (f : Space d → ℝ)
    (hconvex : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f) (x y : Space d) :
    f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
  have h := (affine_line_convex f hconvex x (y - x)).le_slope_of_hasDerivAt
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) zero_lt_one
    (affine_line_hasDerivAt f hdiff x (y - x) 0)
  simp only [zero_smul, add_zero, _root_.slope, sub_zero, one_smul, add_sub_cancel,
    inv_one, vsub_eq_sub] at h
  linarith

end
end CriticalExtrapolation.Paper
