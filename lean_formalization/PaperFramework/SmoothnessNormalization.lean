import PaperFramework.FunctionDilation

namespace CriticalExtrapolation.Paper
noncomputable section

theorem vertical_scaling_hasGradientAt {d : ℕ} (f : Space d → ℝ) (a : ℝ)
    (x g : Space d) (hf : HasGradientAt f g x) :
    HasGradientAt (fun y => a * f y) (a • g) x := by
  simpa only [one_smul, mul_one] using dilation_hasGradientAt f a 1 x g
    (show HasGradientAt f g (1 • x) by simpa only [one_smul] using hf)

theorem vertical_scaling_gradient {d : ℕ} (f : Space d → ℝ) (a : ℝ)
    (hf : Differentiable ℝ f) (x : Space d) :
    gradient (fun y => a * f y) x = a • gradient f x :=
  (vertical_scaling_hasGradientAt f a x _ (hf x).hasGradientAt).gradient

def unitSmoothInstance {d : ℕ} {L D : ℝ} (I : Instance d L D) (hL : 0 < L) :
    Instance d 1 D where
  f := fun x => L⁻¹ * I.f x
  convex := by
    simpa only [one_smul] using
      dilation_convex I.f L⁻¹ 1 (inv_pos.mpr hL).le I.convex
  differentiable := fun x =>
    (vertical_scaling_hasGradientAt I.f L⁻¹ x _ (I.differentiable x).hasGradientAt).differentiableAt
  gradient_lipschitz := by
    intro x z
    rw [vertical_scaling_gradient I.f L⁻¹ I.differentiable,
      vertical_scaling_gradient I.f L⁻¹ I.differentiable,
      ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), one_mul]
    calc
      _ ≤ L⁻¹ * (L * ‖x - z‖) :=
        mul_le_mul_of_nonneg_left (I.gradient_lipschitz x z) (inv_pos.mpr hL).le
      _ = ‖x - z‖ := by rw [← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
  initial := I.initial
  minimizer := I.minimizer
  minimizes := fun x => mul_le_mul_of_nonneg_left (I.minimizes x) (inv_pos.mpr hL).le
  radius := I.radius

theorem unitSmoothInstance_gradient {d : ℕ} {L D : ℝ} (I : Instance d L D)
    (hL : 0 < L) (x : Space d) :
    gradient (unitSmoothInstance I hL).f x = L⁻¹ • gradient I.f x :=
  vertical_scaling_gradient I.f L⁻¹ I.differentiable x

theorem unitSmoothInstance_iterate {d : ℕ} {L D : ℝ} (I : Instance d L D)
    (hL : 0 < L) (h : ℝ) (n : ℕ) :
    iterate (unitSmoothInstance I hL) h n = iterate I h n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate, ih, div_one, unitSmoothInstance_gradient, smul_smul,
      iterate, div_eq_mul_inv]

theorem unitSmoothInstance_output {d : ℕ} {L D : ℝ} (I : Instance d L D)
    (hL : 0 < L) (N : ℕ) (h c : ℝ) :
    output (unitSmoothInstance I hL) N h c = output I N h c := by
  rw [output, unitSmoothInstance_iterate, output]
  rfl

end
end CriticalExtrapolation.Paper
