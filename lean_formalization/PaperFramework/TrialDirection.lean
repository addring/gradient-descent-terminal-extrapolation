import PaperFramework.EnergyLowerBound
import PaperFramework.TrialBasics
import PaperFramework.TrialProfiles

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- Section 8: the explicit direction satisfies both orderings strictly for the whole a range. -/
theorem trial_strict_feasibility (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (ha : (N : ℝ) * (c - 1) ≤ trialParameterMax (1 / h)) :
    StrictlyFeasible h c (trialDirection N ((N : ℝ) * (c - 1)) (1 / h)) := by
  let a : ℝ := (N : ℝ) * (c - 1)
  let t : ℝ := 1 / h
  have ha0 : 0 ≤ a := mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hp.c_ge_one)
  have ht : 1 ≤ t := (le_div_iff₀ hp.h_pos).mpr (by simpa using hp.h_le_one)
  have ht0 : 0 < t := by linarith
  have hH := trial_normalization_positive N t hp.n_pos ht
  have hsum := normalizedTrial_normalized N t hp.n_pos ht
  change StrictlyFeasible h c (shiftedDirection a t (normalizedTrial N t))
  refine ⟨shifted_direction_normalized N a t hp.n_pos ha0 ht0 _ hsum, ?_, ?_⟩
  · intro i
    rw [shifted_direction_difference]
    have hm : 0 < shiftMass a t := div_pos ht0 (add_pos_of_nonneg_of_pos ha0 ht0)
    have hb : 0 ≤ shiftB N a t := by
      exact div_nonneg ha0 (mul_nonneg (Nat.cast_nonneg _) (by linarith))
    have hboundary : 0 ≤ (if i.val + 1 = N then shiftB N a t else 0) := by
      split_ifs <;> positivity
    exact add_pos_of_pos_of_nonneg
      (mul_pos hm (normalizedTrial_differences_positive N t hp.n_pos ht i)) hboundary
  · intro i j hij
    apply shifted_slopes_strict_of_functional N h c hp _ hsum i j hij
    rw [trialSlopeFunctional_normalized]
    exact div_pos (trialVector_functional_positive N a t ha0 ht ha i j hij) hH

end
end CriticalExtrapolation.Paper
