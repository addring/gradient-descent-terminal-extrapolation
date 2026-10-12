import CriticalExtrapolation.Problem
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.FunProp

namespace CriticalExtrapolation

theorem Instance.gradient_at_minimizer {d : ℕ} {L D : ℝ} (I : Instance d L D) :
    gradient I.f I.minimizer = 0 := by
  have hlocal : IsLocalMin I.f I.minimizer :=
    Filter.Eventually.of_forall I.minimizes
  simp [gradient, hlocal.fderiv_eq_zero]

theorem Instance.continuous_gradient {d : ℕ} {L D : ℝ}
    (I : Instance d L D) (hL : 0 ≤ L) : Continuous (gradient I.f) := by
  have hLip : LipschitzWith ⟨L, hL⟩ (gradient I.f) := by
    apply LipschitzWith.of_dist_le_mul
    intro x z
    simpa only [dist_eq_norm, NNReal.coe_mk] using I.gradient_lipschitz x z
  exact hLip.continuous

/-- Continuity for one fixed actual function and a fixed finite trajectory length.
It does not exchange a limit with the worst-case supremum. -/
theorem continuous_iterate {d : ℕ} {L D : ℝ}
    (I : Instance d L D) (hL : 0 ≤ L) (N : ℕ) :
    Continuous (fun h : ℝ => iterate I h N) := by
  induction N with
  | zero => exact continuous_const
  | succ N ih =>
    change Continuous (fun h : ℝ => iterate I h N - (h / L) • gradient I.f (iterate I h N))
    exact ih.sub ((continuous_id.div_const L).smul ((I.continuous_gradient hL).comp ih))

theorem continuous_output {d : ℕ} {L D : ℝ}
    (I : Instance d L D) (hL : 0 ≤ L) (N : ℕ) (c : ℝ) :
    Continuous (fun h : ℝ => output I N h c) := by
  unfold output
  exact continuous_const.add (continuous_const.smul ((continuous_iterate I hL N).sub continuous_const))

theorem continuous_output_gradient_norm {d : ℕ} {L D : ℝ}
    (I : Instance d L D) (hL : 0 ≤ L) (N : ℕ) (c : ℝ) :
    Continuous (fun h : ℝ => ‖gradient I.f (output I N h c)‖) :=
  ((I.continuous_gradient hL).comp (continuous_output I hL N c)).norm

/-- Passing an upper bound to a step-size limit for each fixed function.
The supremum over instances is not involved in this limit. -/
theorem output_gradient_bound_at_step_limit {d : ℕ} {L D : ℝ}
    (I : Instance d L D) (hL : 0 ≤ L) (N : ℕ) (c h₀ : ℝ) (steps : ℕ → ℝ)
    (hsteps : Filter.Tendsto steps Filter.atTop (nhds h₀))
    (hden : 1 + (N : ℝ) * h₀ * c ≠ 0)
    (hbound : ∀ m, ‖gradient I.f (output I N (steps m) c)‖ ≤
      L * D / (1 + (N : ℝ) * steps m * c)) :
    ‖gradient I.f (output I N h₀ c)‖ ≤ L * D / (1 + (N : ℝ) * h₀ * c) := by
  have hg := (continuous_output_gradient_norm I hL N c).continuousAt.tendsto.comp hsteps
  have hd : ContinuousAt (fun h : ℝ => 1 + (N : ℝ) * h * c) h₀ := by fun_prop
  have hb : ContinuousAt (fun h : ℝ => L * D / (1 + (N : ℝ) * h * c)) h₀ :=
    continuousAt_const.div hd hden
  exact le_of_tendsto_of_tendsto hg (hb.tendsto.comp hsteps) (Filter.Eventually.of_forall hbound)

end CriticalExtrapolation
