import PaperFramework.TrialWeightedSum
import PaperFramework.TailEnergyIdentities

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- Exact finite summation by parts, with the terminal tail equal to zero. -/
theorem reciprocal_weighted_tail_identity (N : ℕ) (p : Vec N) :
    (∑ i : Fin N, tail p i.val / (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1))) =
      (∑ i : Fin N, p i / ((N : ℝ) - i.val)) - (∑ i : Fin N, p i) / ((N : ℝ) + 1) := by
  let z : ℕ → ℝ := fun k => tail p k / ((N : ℝ) - k + 1)
  have hp : ∀ i : Fin N, tail p i.val /
      (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1)) =
      p i / ((N : ℝ) - i.val) - (z i.val - z (i.val + 1)) := by
    intro i
    have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
    have hj : 0 < (N : ℝ) - i.val := sub_pos.mpr hi
    have hnext : tail p (i.val + 1) = tail p i.val - p i := by
      have hs := tail_step p i
      linarith only [hs]
    dsimp only [z]
    rw [hnext]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (N : ℝ) - ((i.val : ℝ) + 1) + 1 = (N : ℝ) - i.val by ring]
    field_simp [ne_of_gt hj, ne_of_gt (show 0 < (N : ℝ) - i.val + 1 by linarith)]
    <;> ring
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, sum_fin_natural_differences N z]
  simp [z, tail_terminal, tail_zero]

end
end CriticalExtrapolation.Paper
