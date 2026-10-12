import PaperFramework.InstanceDilation
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.Strong
import Mathlib.Tactic.Module

namespace CriticalExtrapolation.Paper
open InnerProductSpace
noncomputable section

def halfSquaredNorm {d : ℕ} (x : Space d) : ℝ := ‖x‖ ^ 2 / 2

theorem halfSquaredNorm_hasGradientAt {d : ℕ} (x : Space d) :
    HasGradientAt halfSquaredNorm x x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hn : HasFDerivAt (fun y : Space d => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hd := hn.fun_const_smul (2 : ℝ)⁻¹
  convert hd using 1
  · funext y
    dsimp [halfSquaredNorm]
    ring
  · ext v
    simp [smul_smul, toDual_apply_apply, innerSL_apply_apply]

theorem halfSquaredNorm_gradient {d : ℕ} (x : Space d) : gradient halfSquaredNorm x = x :=
  (halfSquaredNorm_hasGradientAt x).gradient

theorem halfSquaredNorm_convex (d : ℕ) : ConvexOn ℝ Set.univ (@halfSquaredNorm d) := by
  have hstrong : StrongConvexOn Set.univ 1 (@halfSquaredNorm d) := by
    apply strongConvexOn_iff_convex.mpr
    convert convexOn_const (0 : ℝ) convex_univ using 1
    funext x
    dsimp [halfSquaredNorm]
    ring
  exact hstrong.convexOn (by intro r; positivity)

def quadraticUnitInstance (d : ℕ) (x₀ : Space d) : Instance d 1 ‖x₀‖ where
  f := halfSquaredNorm
  convex := halfSquaredNorm_convex d
  differentiable := fun x => (halfSquaredNorm_hasGradientAt x).differentiableAt
  gradient_lipschitz := by intro x z; simp only [halfSquaredNorm_gradient, one_mul]; exact le_rfl
  initial := x₀
  minimizer := 0
  minimizes := by intro x; simp only [halfSquaredNorm, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div]; positivity
  radius := by simp only [sub_zero]; exact le_rfl

theorem quadraticUnitInstance_iterate (d : ℕ) (x₀ : Space d) (h : ℝ) (n : ℕ) :
    iterate (quadraticUnitInstance d x₀) h n = (1 - h) ^ n • x₀ := by
  induction n with
  | zero => simp [iterate, quadraticUnitInstance]
  | succ n ih =>
    rw [iterate, ih, div_one]
    change (1 - h) ^ n • x₀ - h • gradient halfSquaredNorm ((1 - h) ^ n • x₀) = _
    rw [halfSquaredNorm_gradient, pow_succ]
    module

theorem quadraticUnitInstance_output (d : ℕ) (x₀ : Space d) (N : ℕ) (h c : ℝ) :
    output (quadraticUnitInstance d x₀) N h c =
      (1 - c * (1 - (1 - h) ^ N)) • x₀ := by
  rw [output, quadraticUnitInstance_iterate]
  change x₀ + c • ((1 - h) ^ N • x₀ - x₀) = _
  module

def unitOne : Space 1 := WithLp.toLp 2 (fun _ : Fin 1 => 1)

theorem unitOne_norm : ‖unitOne‖ = 1 := by
  have hsq : ‖unitOne‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp [unitOne, RCLike.inner_apply, Fin.sum_univ_one]
  nlinarith [norm_nonneg unitOne]

end
end CriticalExtrapolation.Paper
