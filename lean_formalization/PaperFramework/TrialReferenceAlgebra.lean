import PaperFramework.Energy
import PaperFramework.TrialMajorant

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem energy_matrix_at_reference (N : ℕ) (hN : 0 < N) (i j : Fin N) :
    E N 0 1 i j = if i = j then referenceWeight (N : ℝ) (i.val : ℝ) else 0 := by
  have hh := tridiagonal_matrix_split N 0 1 hN (by norm_num) (by norm_num) i j
  simpa [energyF] using hh

/-- The exact nonnegative baseline sum used for the two endpoint layers in (9.5). -/
theorem trial_reference_energy_sum (N : ℕ) (t : ℝ) (hN : 0 < N) :
    homogeneousEnergy 0 1 (trialVector N t) =
      ∑ i, ((N : ℝ) + 1) ^ 2 * referenceWeight (N : ℝ) (i.val : ℝ) *
        (tailU 0 1 (trialVector N t) i) ^ 2 := by
  rw [tridiagonal_energy_identity N 0 1 hN (by norm_num) (by norm_num)]
  have hq : quadraticForm (E N 0 1) (tailU 0 1 (trialVector N t)) =
      ∑ i, referenceWeight (N : ℝ) (i.val : ℝ) * (tailU 0 1 (trialVector N t) i) ^ 2 := by
    unfold quadraticForm
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [energy_matrix_at_reference N hN i, ite_mul, zero_mul]
    simp [pow_two, mul_assoc]
  rw [hq]
  simp only [energyF, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end CriticalExtrapolation.Paper
