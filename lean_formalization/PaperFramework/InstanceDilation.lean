import PaperFramework.FunctionDilation

namespace CriticalExtrapolation.Paper
noncomputable section

theorem normalized_dilation_gradient {d : ℕ} (f : Space d → ℝ)
    (hf : Differentiable ℝ f) (L r : ℝ) (hr : 0 < r) (x : Space d) :
    gradient (fun y => L * r ^ 2 * f (r⁻¹ • y)) x =
      (L * r) • gradient f (r⁻¹ • x) := by
  rw [dilation_gradient f (L * r ^ 2) r⁻¹ hf]
  congr 1
  field_simp [hr.ne']

def dilatedInstance {d : ℕ} {R : ℝ} (I : Instance d 1 R)
    (L D r : ℝ) (hL : 0 < L) (hr : 0 < r) (hrad : r * R ≤ D) : Instance d L D where
  f := fun x => L * r ^ 2 * I.f (r⁻¹ • x)
  convex := dilation_convex I.f (L * r ^ 2) r⁻¹ (mul_nonneg hL.le (sq_nonneg r)) I.convex
  differentiable := fun x =>
    (dilation_hasGradientAt I.f (L * r ^ 2) r⁻¹ x _ (I.differentiable _).hasGradientAt).differentiableAt
  gradient_lipschitz := by
    intro x z
    rw [normalized_dilation_gradient I.f I.differentiable L r hr,
      normalized_dilation_gradient I.f I.differentiable L r hr,
      ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hL hr)]
    have hb := I.gradient_lipschitz (r⁻¹ • x) (r⁻¹ • z)
    rw [one_mul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at hb
    calc
      _ ≤ (L * r) * (r⁻¹ * ‖x - z‖) := mul_le_mul_of_nonneg_left hb (mul_pos hL hr).le
      _ = L * ‖x - z‖ := by field_simp [hr.ne']
  initial := r • I.initial
  minimizer := r • I.minimizer
  minimizes := by
    intro x
    simp only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    exact mul_le_mul_of_nonneg_left (I.minimizes (r⁻¹ • x)) (mul_nonneg hL.le (sq_nonneg r))
  radius := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left I.radius hr.le).trans hrad

theorem dilatedInstance_gradient {d : ℕ} {R : ℝ} (I : Instance d 1 R)
    (L D r : ℝ) (hL : 0 < L) (hr : 0 < r) (hrad : r * R ≤ D) (x : Space d) :
    gradient (dilatedInstance I L D r hL hr hrad).f (r • x) =
      (L * r) • gradient I.f x := by
  change gradient (fun y => L * r ^ 2 * I.f (r⁻¹ • y)) (r • x) = _
  rw [normalized_dilation_gradient I.f I.differentiable L r hr]
  simp only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

theorem dilatedInstance_iterate {d : ℕ} {R : ℝ} (I : Instance d 1 R)
    (L D r : ℝ) (hL : 0 < L) (hr : 0 < r) (hrad : r * R ≤ D) (h : ℝ) (n : ℕ) :
    iterate (dilatedInstance I L D r hL hr hrad) h n = r • iterate I h n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate, ih, dilatedInstance_gradient, iterate, div_one, smul_sub, smul_smul, smul_smul]
    have hcoeff : (h / L) * (L * r) = r * h := by field_simp [hL.ne']
    rw [hcoeff]

theorem dilatedInstance_output {d : ℕ} {R : ℝ} (I : Instance d 1 R)
    (L D r : ℝ) (hL : 0 < L) (hr : 0 < r) (hrad : r * R ≤ D) (N : ℕ) (h c : ℝ) :
    output (dilatedInstance I L D r hL hr hrad) N h c = r • output I N h c := by
  rw [output, dilatedInstance_iterate, output]
  change r • I.initial + c • (r • iterate I h N - r • I.initial) = _
  rw [smul_add, ← smul_sub, smul_smul, smul_smul, mul_comm c r]

end
end CriticalExtrapolation.Paper
