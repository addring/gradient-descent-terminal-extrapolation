import PaperFramework.ScaledParameters
import PaperFramework.EnergyLowerBound

namespace CriticalExtrapolation.Paper
noncomputable section

theorem scaledA_square_identity (N : ℕ) (h k : ℝ) (hN : 1 < N) (hh : 0 < h) :
    Real.log (N : ℝ) * (scaledA N h k) ^ 2 = (1 / h) ^ 2 * k ^ 2 := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos hn
  unfold scaledA
  rw [div_pow, mul_pow, Real.sq_sqrt hl.le]
  field_simp [ne_of_gt hh, ne_of_gt hl]
  <;> ring

theorem scaled_penalty_identity (N : ℕ) (h k : ℝ) (hN : 1 < N) (hh : 0 < h) :
    Real.log (N : ℝ) * (scaledA N h k) ^ 2 / (scaledA N h k + 1 / h) ^ 2 =
      (shiftMass (scaledA N h k) (1 / h)) ^ 2 * k ^ 2 := by
  rw [scaledA_square_identity N h k hN hh]
  unfold shiftMass
  simp only [div_pow]
  ring

theorem finiteLowerBound_scaled_identity (N : ℕ) (h k : ℝ)
    (hN : 1 < N) (hh : 0 < h) :
    Real.log (N : ℝ) * finiteLowerBound N h (scaledC N h k) =
      (shiftMass (scaledA N h k) (1 / h)) ^ 2 *
        (Real.log (N : ℝ) / referenceReciprocalSum N - k ^ 2) -
      Real.log (N : ℝ) * scaledA N h k / (N : ℝ) := by
  unfold finiteLowerBound
  rw [scaledA_identity N h k hN hh]
  calc
    _ = (shiftMass (scaledA N h k) (1 / h)) ^ 2 *
        (Real.log (N : ℝ) / referenceReciprocalSum N) -
      Real.log (N : ℝ) * (scaledA N h k) ^ 2 / (scaledA N h k + 1 / h) ^ 2 -
      Real.log (N : ℝ) * scaledA N h k / (N : ℝ) := by
      unfold shiftMass
      rw [div_pow]
      ring
    _ = _ := by rw [scaled_penalty_identity N h k hN hh]; ring

end
end CriticalExtrapolation.Paper
