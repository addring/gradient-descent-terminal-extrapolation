import PaperFramework.UniformScaledAlgebra
import PaperFramework.TrialDirection

namespace CriticalExtrapolation.Paper
noncomputable section

theorem trial_objective_scaled_identity (N : ℕ) (h k : ℝ) (hN : 1 < N)
    (hh : 0 < h) (hh1 : h ≤ 1) (hk : 0 ≤ k) :
    Real.log (N : ℝ) / (h ^ 2 * scaledC N h k) *
      chainObjective h (scaledC N h k) (trialDirection N (scaledA N h k) (1 / h)) =
    (shiftMass (scaledA N h k) (1 / h)) ^ 2 *
      (Real.log (N : ℝ) * homogeneousEnergy (scaledA N h k) (1 / h)
        (normalizedTrial N (1 / h)) - k ^ 2) -
    Real.log (N : ℝ) * scaledA N h k / (N : ℝ) +
    Real.log (N : ℝ) *
      (2 * energyF N (scaledA N h k) (1 / h) * shiftMass (scaledA N h k) (1 / h) *
        shiftB N (scaledA N h k) (1 / h) * (N : ℝ) * (1 / h - 1) /
        (scaledA N h k + 1) * normalizedTrial N (1 / h) ⟨N - 1, by omega⟩) := by
  have ht : 1 ≤ 1 / h := (le_div_iff₀ hh).mpr (by simpa using hh1)
  have hp := scaledC_parameters N h k (by omega) hh hh1 hk
  have hy := affine_shift_energy_identity N h (scaledC N h k) hp
    (normalizedTrial N (1 / h)) (normalizedTrial_normalized N (1 / h) (by omega) ht)
  dsimp only at hy
  rw [scaledA_identity N h k hN hh] at hy
  change chainObjective h (scaledC N h k) (trialDirection N (scaledA N h k) (1 / h)) /
    (h ^ 2 * scaledC N h k) = _ at hy
  calc
    _ = Real.log (N : ℝ) *
        (chainObjective h (scaledC N h k) (trialDirection N (scaledA N h k) (1 / h)) /
          (h ^ 2 * scaledC N h k)) := by ring
    _ = _ := by
      rw [hy]
      calc
        _ = (shiftMass (scaledA N h k) (1 / h)) ^ 2 *
            (Real.log (N : ℝ) * homogeneousEnergy (scaledA N h k) (1 / h)
              (normalizedTrial N (1 / h))) -
          Real.log (N : ℝ) * (scaledA N h k) ^ 2 / (scaledA N h k + 1 / h) ^ 2 -
          Real.log (N : ℝ) * scaledA N h k / (N : ℝ) +
          Real.log (N : ℝ) *
            (2 * energyF N (scaledA N h k) (1 / h) * shiftMass (scaledA N h k) (1 / h) *
              shiftB N (scaledA N h k) (1 / h) * (N : ℝ) * (1 / h - 1) /
              (scaledA N h k + 1) * normalizedTrial N (1 / h) ⟨N - 1, by omega⟩) := by ring
        _ = _ := by rw [scaled_penalty_identity N h k hN hh]; ring

end
end CriticalExtrapolation.Paper
