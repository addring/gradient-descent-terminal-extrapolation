import PaperFramework.PerturbationRecovery
import PaperFramework.PerturbationTrajectory
import PaperFramework.InstanceDilation

namespace CriticalExtrapolation.Paper
noncomputable section

/-- The finite data are realized by an admissible global function with the actual GD output. -/
theorem negative_direction_realization_proved (N : ℕ) (h c L D : ℝ) (hp : Parameters N h c)
    (hL : 0 < L) (hD : 0 < D) (β : Vec N)
    (hβ : StrictlyFeasible h c β) (hQ : chainObjective h c β < 0) :
    ∃ I : Instance 2 L D, L * D / S N h c < ‖gradient I.f (output I N h c)‖ := by
  obtain ⟨ε, _, hslack, hRpos, hRlt⟩ := negative_direction_finite_data N h c hp β hβ hQ
  obtain ⟨hf, hinterp, hmin⟩ := perturbation_global_function_proved N h c ε β hslack
  let R : ℝ := ‖perturbationInitial h c ε β‖
  let I₀ : Instance 2 1 R := {
    f := recoveredFunction (perturbationSample h c ε β)
    convex := hf.1
    differentiable := hf.2.1
    gradient_lipschitz := by intro x z; simpa only [one_mul] using hf.2.2 x z
    initial := perturbationInitial h c ε β
    minimizer := 0
    minimizes := hmin
    radius := by simp only [sub_zero]; exact le_rfl }
  let r : ℝ := D / R
  have hr : 0 < r := div_pos hD hRpos
  have hrad : r * R ≤ D := by dsimp [r]; rw [div_mul_cancel₀ _ hRpos.ne']
  let I := dilatedInstance I₀ L D r hL hr hrad
  have hout : output I₀ N h c = vec2 1 0 :=
    perturbation_output_formula I₀ h c ε β rfl hinterp
  have hg : gradient I₀.f (vec2 1 0) = vec2 1 0 := by
    have hs := hinterp.2 (outputQuery N)
    simpa [I₀, perturbationSample, outputQuery] using hs
  have hnorm : ‖vec2 1 0‖ = 1 := by
    have hs := vec2_norm_sq 1 0
    nlinarith [norm_nonneg (vec2 1 0)]
  have hgrad : ‖gradient I.f (output I N h c)‖ = L * r := by
    change ‖gradient (dilatedInstance I₀ L D r hL hr hrad).f
      (output (dilatedInstance I₀ L D r hL hr hrad) N h c)‖ = _
    rw [dilatedInstance_output, hout, dilatedInstance_gradient, hg, norm_smul,
      Real.norm_eq_abs, abs_of_pos (mul_pos hL hr), hnorm, mul_one]
  refine ⟨I, ?_⟩
  rw [hgrad]
  have hinv : 1 / S N h c < 1 / R := one_div_lt_one_div_of_lt hRpos hRlt
  have hstrict := mul_lt_mul_of_pos_left hinv (mul_pos hL hD)
  dsimp [r]
  simpa only [div_eq_mul_inv, one_mul, mul_assoc] using hstrict

end
end CriticalExtrapolation.Paper
