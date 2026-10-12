import PaperFramework.Definitions
import Mathlib.Algebra.BigOperators.Intervals

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem shiftedHarmonic_nonnegative (t : ℝ) (ht : 1 ≤ t) (j : ℕ) :
    0 ≤ shiftedHarmonic t j := by
  unfold shiftedHarmonic
  apply Finset.sum_nonneg
  intro k _
  have hk := Nat.cast_nonneg (α := ℝ) k
  exact (one_div_pos.mpr (by linarith : 0 < (k : ℝ) + 1 + 2 * t)).le

theorem shiftedHarmonic_step (t : ℝ) (j : ℕ) :
    shiftedHarmonic t (j + 1) = shiftedHarmonic t j + 1 / ((j : ℝ) + 1 + 2 * t) := by
  exact Finset.sum_range_succ _ _

theorem trialVector_positive (N : ℕ) (t : ℝ) (ht : 1 ≤ t) (i : Fin N) : 0 < trialVector N t i := by
  have hi := Nat.cast_nonneg (α := ℝ) i.val
  have hleft : 0 < 1 / ((i.val : ℝ) + 2 * t) := one_div_pos.mpr (by linarith)
  have hright : 0 ≤ shiftedHarmonic t (N - i.val) / (N : ℝ) :=
    div_nonneg (shiftedHarmonic_nonnegative t ht _) (Nat.cast_nonneg _)
  exact add_pos_of_pos_of_nonneg hleft hright

theorem trial_normalization_positive (N : ℕ) (t : ℝ) (hN : 0 < N) (ht : 1 ≤ t) :
    0 < trialNormalization N t := by
  unfold trialNormalization
  apply Finset.sum_pos'
  · intro i _; exact (trialVector_positive N t ht i).le
  · exact ⟨⟨0, hN⟩, Finset.mem_univ _, trialVector_positive N t ht _⟩

theorem normalizedTrial_normalized (N : ℕ) (t : ℝ) (hN : 0 < N) (ht : 1 ≤ t) :
    (∑ i, normalizedTrial N t i) = 1 := by
  simp only [normalizedTrial, ← Finset.sum_div]
  exact div_self (ne_of_gt (trial_normalization_positive N t hN ht))

theorem trialVector_adjacent_strict (N : ℕ) (t : ℝ) (ht : 1 ≤ t)
    (i j : Fin N) (hij : i.val + 1 = j.val) : trialVector N t j < trialVector N t i := by
  have hi := Nat.cast_nonneg (α := ℝ) i.val
  have hden : 0 < (i.val : ℝ) + 2 * t := by linarith
  have hval : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij.symm
  have hleft := one_div_lt_one_div_of_lt hden
    (show (i.val : ℝ) + 2 * t < (j.val : ℝ) + 2 * t by linarith)
  have hnat : N - i.val = N - j.val + 1 := by omega
  have hright : shiftedHarmonic t (N - j.val) ≤ shiftedHarmonic t (N - i.val) := by
    rw [hnat, shiftedHarmonic_step]
    have hk := Nat.cast_nonneg (α := ℝ) (N - j.val)
    exact le_add_of_nonneg_right (by apply div_nonneg zero_le_one; linarith)
  have hdiv := div_le_div_of_nonneg_right hright (Nat.cast_nonneg (α := ℝ) N)
  exact add_lt_add_of_lt_of_le hleft hdiv

theorem normalizedTrial_differences_positive (N : ℕ) (t : ℝ) (hN : 0 < N) (ht : 1 ≤ t) :
    ∀ i, 0 < difference (normalizedTrial N t) i := by
  have hnorm := trial_normalization_positive N t hN ht
  intro i
  by_cases hi : i.val + 1 < N
  · let j : Fin N := ⟨i.val + 1, hi⟩
    have hstrict := trialVector_adjacent_strict N t ht i j rfl
    have heq : difference (normalizedTrial N t) i =
        (trialVector N t i - trialVector N t j) / trialNormalization N t := by
      simp only [difference, zeroExtend, dif_pos hi, normalizedTrial]
      rw [sub_div]
    rw [heq]
    exact div_pos (sub_pos.mpr hstrict) hnorm
  · simp only [difference, zeroExtend, dif_neg hi, sub_zero, normalizedTrial]
    exact div_pos (trialVector_positive N t ht i) hnorm

end
end CriticalExtrapolation.Paper
