import PaperFramework.Definitions
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add

namespace CriticalExtrapolation.Paper
open InnerProductSpace
noncomputable section

theorem dilation_hasGradientAt {d : ℕ} (f : Space d → ℝ) (a b : ℝ)
    (x g : Space d) (hf : HasGradientAt f g (b • x)) :
    HasGradientAt (fun y => a * f (b • y)) ((a * b) • g) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd := (hf.hasFDerivAt.comp x ((hasFDerivAt_id x).fun_const_smul b)).const_mul a
  have heq : a • ((toDual ℝ (Space d) g).comp (b • ContinuousLinearMap.id ℝ (Space d))) =
      toDual ℝ (Space d) ((a * b) • g) := by
    ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, toDual_apply_apply, real_inner_smul_left,
      inner_smul_right, smul_eq_mul]
    ring
  rw [← heq]
  exact hd

theorem dilation_gradient {d : ℕ} (f : Space d → ℝ) (a b : ℝ)
    (hf : Differentiable ℝ f) (x : Space d) :
    gradient (fun y => a * f (b • y)) x = (a * b) • gradient f (b • x) :=
  (dilation_hasGradientAt f a b x _ (hf (b • x)).hasGradientAt).gradient

theorem dilation_convex {d : ℕ} (f : Space d → ℝ) (a b : ℝ) (ha : 0 ≤ a)
    (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (fun y => a * f (b • y)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  change a * f (b • (s • x + t • y)) ≤ s • (a * f (b • x)) + t • (a * f (b • y))
  have hc := hf.2 (Set.mem_univ (b • x)) (Set.mem_univ (b • y)) hs ht hst
  have harg : b • (s • x + t • y) = s • (b • x) + t • (b • y) := by
    simp only [smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
  rw [harg]
  simp only [smul_eq_mul] at hc ⊢
  nlinarith [mul_le_mul_of_nonneg_left hc ha]

end
end CriticalExtrapolation.Paper
