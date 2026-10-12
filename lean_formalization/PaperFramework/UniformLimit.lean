import PaperFramework.TrialAsymptotics
import PaperFramework.ScaledParameters
import PaperFramework.UniformSigns
import PaperFramework.UniformAuxiliaryProof

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

/-- Theorem (10.3), with h fixed and k varying over a fixed compact interval. -/
theorem auxiliary_uniform_scaled_limit (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (K : ℝ) (hK : 0 < K) :
    UniformOn 0 K
      (fun N k => Real.log (N : ℝ) / (h ^ 2 * scaledC N h k) *
        auxiliaryValue N h (scaledC N h k)) (fun k => 1 - k ^ 2) := by
  exact auxiliary_uniform_scaled_limit_proved h hh hh1 K

/-- The same scaled limit for the explicit direction used in counterexamples. -/
theorem trial_objective_uniform_scaled_limit (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (K : ℝ) (hK : 0 < K) :
    UniformOn 0 K
      (fun N k => Real.log (N : ℝ) / (h ^ 2 * scaledC N h k) *
        chainObjective h (scaledC N h k) (trialDirection N (scaledA N h k) (1 / h)))
      (fun k => 1 - k ^ 2) := by
  exact trial_objective_uniform_scaled_limit_proved h hh hh1 K

theorem eventual_positive_initial_interval (h ε : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ N in atTop, ∀ k ∈ Set.Icc (0 : ℝ) (1 - ε),
      0 < auxiliaryValue N h (scaledC N h k) := by
  exact eventual_positive_initial_interval_of_limit h ε hh hh1 hε hε1
    (auxiliary_uniform_scaled_limit h hh hh1 1 zero_lt_one)

theorem eventual_strictly_feasible_negative_trial (h ε : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hε : 0 < ε) :
    ∀ᶠ N in atTop,
      StrictlyFeasible h (scaledC N h (1 + ε)) (trialDirection N (scaledA N h (1 + ε)) (1 / h)) ∧
      chainObjective h (scaledC N h (1 + ε)) (trialDirection N (scaledA N h (1 + ε)) (1 / h)) < 0 := by
  exact eventual_strictly_feasible_negative_trial_of_limit h ε hh hh1 hε
    (trial_objective_uniform_scaled_limit h hh hh1 (2 + ε) (by linarith))

end
end CriticalExtrapolation.Paper
