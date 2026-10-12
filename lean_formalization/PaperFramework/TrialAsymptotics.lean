import PaperFramework.TrialDirection
import PaperFramework.TrialNormalization
import PaperFramework.TrialMajorant
import PaperFramework.TrialUniformLimitProof
import PaperFramework.TrialPerturbationProof
import PaperFramework.TrialReferenceModelLimit

namespace CriticalExtrapolation.Paper
open scoped BigOperators
open Filter Topology Asymptotics
noncomputable section

/-- (9.5), proved by the global reciprocal model comparison documented in FORMALIZATION_NOTES. -/
theorem trial_reference_energy_limit (t : ℝ) (ht : 1 ≤ t) :
    Tendsto (fun N : ℕ => homogeneousEnergy 0 1 (trialVector N t) / Real.log (N : ℝ))
      atTop (𝓝 4) := by
  exact trial_reference_energy_limit_proved t ht

/-- (9.7): constants are uniform for a in [0,A_t], including moving a_N. -/
theorem trial_energy_uniform_perturbation (t : ℝ) (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ N, 0 < N → ∀ a ∈ Set.Icc (0 : ℝ) (trialParameterMax t),
      |homogeneousEnergy a t (trialVector N t) - homogeneousEnergy 0 1 (trialVector N t)| ≤
        C * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ)) := by
  exact trial_energy_uniform_perturbation_proved t ht

/-- (9.1): the leading energy is uniform in bounded a, with fixed t. -/
theorem trial_energy_uniform_limit (t : ℝ) (ht : 1 ≤ t) :
    UniformOn 0 (trialParameterMax t)
      (fun N a => Real.log (N : ℝ) * homogeneousEnergy a t (normalizedTrial N t))
      (fun _ => 1) := by
  exact trial_energy_uniform_limit_from_estimates t ht
    (trial_reference_energy_limit t ht) (trial_energy_uniform_perturbation t ht)

end
end CriticalExtrapolation.Paper
