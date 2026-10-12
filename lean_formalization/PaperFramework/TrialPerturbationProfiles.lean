import PaperFramework.TrialPerturbationAlgebra
import PaperFramework.TrialDirection

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem shiftedHarmonic_monotone (t : ℝ) (ht : 1 ≤ t) : Monotone (shiftedHarmonic t) := by
  intro m n hmn
  unfold shiftedHarmonic
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
  intro k _ _
  exact div_nonneg zero_le_one (by have := Nat.cast_nonneg (α := ℝ) k; linarith)

theorem trialVector_antitone (N : ℕ) (t : ℝ) (ht : 1 ≤ t) : Antitone (trialVector N t) := by
  intro i j hij
  have hijR : (i.val : ℝ) ≤ j.val := by exact_mod_cast hij
  have hleft : 1 / ((j.val : ℝ) + 2 * t) ≤ 1 / ((i.val : ℝ) + 2 * t) :=
    one_div_le_one_div_of_le (by have := Nat.cast_nonneg (α := ℝ) i.val; linarith) (by linarith)
  exact add_le_add hleft (div_le_div_of_nonneg_right
    (shiftedHarmonic_monotone t ht (Nat.sub_le_sub_left hij N)) (Nat.cast_nonneg N))

theorem trial_tail_bounds (N : ℕ) (t : ℝ) (ht : 1 ≤ t) (i : Fin N) :
    0 ≤ tail (trialVector N t) i.val - trialVector N t i ∧
      tail (trialVector N t) i.val - trialVector N t i ≤
        (((N - i.val : ℕ) : ℝ) - 1) * trialVector N t i := by
  have hnext : 0 ≤ tail (trialVector N t) (i.val + 1) := by
    apply Finset.sum_nonneg
    intro j _
    exact (trialVector_positive N t ht j).le
  have hupper : tail (trialVector N t) i.val ≤
      ((N - i.val : ℕ) : ℝ) * trialVector N t i := by
    unfold tail
    calc
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => i.val ≤ j.val), trialVector N t i := by
        apply Finset.sum_le_sum
        intro j hj
        exact trialVector_antitone N t ht (Finset.mem_filter.mp hj).2
      _ = _ := by
        have hset : Finset.univ.filter (fun j : Fin N => i.val ≤ j.val) = Finset.Ici i := by
          ext j
          simp
        rw [hset]
        simp [Finset.sum_const, Fin.card_Ici]
  have hstep := tail_step (trialVector N t) i
  constructor <;> linarith

theorem trialVector_difference_adjacent (N : ℕ) (t : ℝ) (ht : 1 ≤ t)
    (i j : Fin N) (hij : i.val + 1 = j.val) :
    difference (trialVector N t) i =
      1 / (((i.val : ℝ) + 2 * t) * ((i.val : ℝ) + 2 * t + 1)) +
        1 / ((N : ℝ) * (((N - i.val : ℕ) : ℝ) + 2 * t)) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hu : 0 < (i.val : ℝ) + 2 * t := by have := Nat.cast_nonneg (α := ℝ) i.val; linarith
  have hv : 0 < ((N - i.val : ℕ) : ℝ) + 2 * t := by
    have := Nat.cast_nonneg (α := ℝ) (N - i.val); linarith
  have hjR : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij.symm
  have hnat : N - i.val = N - j.val + 1 := by omega
  have hstep : shiftedHarmonic t (N - i.val) = shiftedHarmonic t (N - j.val) +
      1 / (((N - i.val : ℕ) : ℝ) + 2 * t) := by
    rw [hnat, shiftedHarmonic_step]
    simp only [Nat.cast_add, Nat.cast_one] <;> ring
  rw [difference_adjacent _ i j hij]
  simp only [trialVector, hjR, hstep]
  field_simp [ne_of_gt hn, ne_of_gt hu, ne_of_gt hv, ne_of_gt (show 0 < (i.val : ℝ) + 2 * t + 1 by linarith)]
  <;> ring

theorem trialVector_terminal_upper (N : ℕ) (t : ℝ) (ht : 1 ≤ t)
    (i : Fin N) (hi : i.val + 1 = N) : trialVector N t i ≤ 2 / (N : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hiR : (i.val : ℝ) + 1 = N := by exact_mod_cast hi
  have hleft := one_div_le_one_div_of_le hn (show (N : ℝ) ≤ (i.val : ℝ) + 2 * t by linarith)
  have hright := one_div_le_one_div_of_le zero_lt_one (show (1 : ℝ) ≤ 1 + 2 * t by linarith)
  have hdiff : N - i.val = 1 := by omega
  have hH : shiftedHarmonic t 1 = 1 / (1 + 2 * t) := by simp [shiftedHarmonic]
  unfold trialVector
  rw [hdiff, hH]
  have hr := div_le_div_of_nonneg_right hright hn.le
  calc
    _ ≤ 1 / (N : ℝ) + 1 / (N : ℝ) := add_le_add hleft (by simpa only [div_one] using hr)
    _ = _ := by ring

end
end CriticalExtrapolation.Paper
