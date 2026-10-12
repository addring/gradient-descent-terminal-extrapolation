import PaperFramework.TrialMajorant

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def trialEnergyJ {N : ℕ} (a t : ℝ) (p : Vec N) : ℝ :=
  ∑ i, ((i.val : ℝ) + 1) * difference p i *
    (tail p i.val - t * p i) / energyD N a i.val

theorem homogeneousEnergy_eq_trialEnergyJ {N : ℕ} (a t : ℝ) (p : Vec N) :
    homogeneousEnergy a t p = (∑ i, p i) ^ 2 - 2 * energyF N a t * trialEnergyJ a t p := rfl

/-- The exact J perturbation identity in the document, before any asymptotic bound. -/
theorem trialEnergyJ_parameter_difference {N : ℕ} (a t : ℝ) (ha : 0 ≤ a) (p : Vec N) :
    trialEnergyJ a t p - trialEnergyJ 0 1 p =
      -(∑ i, ((i.val : ℝ) + 1) * difference p i *
        (a * (tail p i.val - p i) / (((N : ℝ) - i.val) * ((N : ℝ) + a - i.val)) +
          (t - 1) * p i / ((N : ℝ) + a - i.val))) := by
  unfold trialEnergyJ
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
  have hj : 0 < (N : ℝ) - i.val := sub_pos.mpr hi
  have hja : 0 < (N : ℝ) + a - i.val := by linarith
  unfold energyD
  field_simp [ne_of_gt hj, ne_of_gt hja]
  <;> ring

theorem homogeneousEnergy_parameter_difference {N : ℕ} (a t : ℝ) (p : Vec N) :
    homogeneousEnergy a t p - homogeneousEnergy 0 1 p =
      -2 * (a + t - 1) * trialEnergyJ 0 1 p -
        2 * energyF N a t * (trialEnergyJ a t p - trialEnergyJ 0 1 p) := by
  simp only [homogeneousEnergy_eq_trialEnergyJ, energyF]
  ring

end
end CriticalExtrapolation.Paper
