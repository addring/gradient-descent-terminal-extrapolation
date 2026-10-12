import PaperFramework.FlowVectorQuadratic
import PaperFramework.FunctionDilation

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def radiusDrop (d : ℕ) : Space (d + 1) →L[ℝ] Space d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin d =>
      PiLp.proj (p := 2) (𝕜 := ℝ) (fun _ : Fin (d + 1) => ℝ) i.castSucc))

def radiusLift (d : ℕ) : Space d →L[ℝ] Space (d + 1) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j : Fin (d + 1) =>
      if hj : j.val < d then PiLp.proj (p := 2) (𝕜 := ℝ) (fun _ : Fin d => ℝ) ⟨j.val, hj⟩
      else 0))

theorem radiusDrop_apply {d : ℕ} (x : Space (d + 1)) (i : Fin d) :
    radiusDrop d x i = x i.castSucc := rfl

theorem radiusLift_castSucc_apply {d : ℕ} (x : Space d) (i : Fin d) :
    radiusLift d x i.castSucc = x i := by
  simp [radiusLift, i.isLt, PiLp.proj]

theorem radiusLift_last_apply {d : ℕ} (x : Space d) :
    radiusLift d x (Fin.last d) = 0 := by
  simp [radiusLift]

theorem radiusDrop_radiusLift {d : ℕ} (x : Space d) :
    radiusDrop d (radiusLift d x) = x := by
  ext i
  rw [radiusDrop_apply, radiusLift_castSucc_apply]

theorem radiusLift_norm {d : ℕ} (x : Space d) : ‖radiusLift d x‖ = ‖x‖ := by
  have hs : ‖radiusLift d x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [space_norm_sq_coordinates, Fin.sum_univ_castSucc]
    simp only [radiusLift_castSucc_apply, radiusLift_last_apply, zero_pow (by decide : 2 ≠ 0),
      add_zero, ← space_norm_sq_coordinates]
  nlinarith [norm_nonneg (radiusLift d x), norm_nonneg x]

theorem radiusDrop_norm_le {d : ℕ} (x : Space (d + 1)) : ‖radiusDrop d x‖ ≤ ‖x‖ := by
  have hs : ‖radiusDrop d x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [space_norm_sq_coordinates, space_norm_sq_coordinates, Fin.sum_univ_castSucc]
    simp only [radiusDrop_apply]
    exact le_add_of_nonneg_right (sq_nonneg _)
  nlinarith [norm_nonneg (radiusDrop d x), norm_nonneg x]

theorem radiusLift_inner {d : ℕ} (g : Space d) (x : Space (d + 1)) :
    inner ℝ (radiusLift d g) x = inner ℝ g (radiusDrop d x) := by
  rw [PiLp.inner_apply, Fin.sum_univ_castSucc, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, radiusLift_castSucc_apply,
    radiusLift_last_apply, radiusDrop_apply, mul_zero, add_zero]

theorem radius_extension_hasGradientAt {d : ℕ} (f : Space d → ℝ)
    (x : Space (d + 1)) (g : Space d) (hf : HasGradientAt f g (radiusDrop d x)) :
    HasGradientAt (fun y => f (radiusDrop d y)) (radiusLift d g) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd := hf.hasFDerivAt.comp x (radiusDrop d).hasFDerivAt
  have heq : (InnerProductSpace.toDual ℝ (Space d) g).comp (radiusDrop d) =
      InnerProductSpace.toDual ℝ (Space (d + 1)) (radiusLift d g) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
      radiusLift_inner]
  rw [← heq]
  exact hd

theorem radius_extension_gradient {d : ℕ} (f : Space d → ℝ) (hf : Differentiable ℝ f)
    (x : Space (d + 1)) :
    gradient (fun y => f (radiusDrop d y)) x = radiusLift d (gradient f (radiusDrop d x)) :=
  (radius_extension_hasGradientAt f x _ (hf _).hasGradientAt).gradient

end
end CriticalExtrapolation.Paper
