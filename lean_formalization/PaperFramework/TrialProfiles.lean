import PaperFramework.TrialFunctional

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def trialLeft (N : ℕ) (t : ℝ) : Vec N := fun i => 1 / ((i.val : ℝ) + 2 * t)
def trialRight (N : ℕ) (t : ℝ) : Vec N := fun i => shiftedHarmonic t (N - i.val) / (N : ℝ)

theorem trialVector_profiles (N : ℕ) (t : ℝ) :
    trialVector N t = trialLeft N t + trialRight N t := rfl

theorem trialLeft_tail (N : ℕ) (t : ℝ) (i : Fin N) :
    tail (trialLeft N t) i.val =
      ∑ k ∈ Finset.range (N - i.val), 1 / ((i.val : ℝ) + 2 * t + (k : ℝ)) := by
  unfold tail trialLeft
  rw [sum_fin_suffix_eq_Ico N i.val (fun k => 1 / ((k : ℝ) + 2 * t)), Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Nat.cast_add]
  congr 1
  ring

theorem trialRight_tail (N : ℕ) (t : ℝ) (ht : 1 ≤ t) (i : Fin N) :
    tail (trialRight N t) i.val =
      (((N - i.val : ℕ) : ℝ) + 2 * t + 1) * shiftedHarmonic t (N - i.val) / (N : ℝ) -
        ((N - i.val : ℕ) : ℝ) / (N : ℝ) := by
  unfold tail trialRight
  rw [← Finset.sum_div, sum_fin_suffix_eq_Ico N i.val (fun k => shiftedHarmonic t (N - k)),
    Finset.sum_Ico_eq_sum_range]
  have hreflect : (∑ k ∈ Finset.range (N - i.val), shiftedHarmonic t (N - (i.val + k))) =
      ∑ k ∈ Finset.range (N - i.val), shiftedHarmonic t (k + 1) := by
    calc
      _ = ∑ k ∈ Finset.range (N - i.val), shiftedHarmonic t ((N - i.val - 1 - k) + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        have := Finset.mem_range.mp hk
        omega
      _ = _ := Finset.sum_range_reflect (fun k => shiftedHarmonic t (k + 1)) (N - i.val)
  rw [hreflect]
  have hsum := Finset.sum_range_succ' (fun k => shiftedHarmonic t k) (N - i.val)
  have hz : shiftedHarmonic t 0 = 0 := by simp [shiftedHarmonic]
  simp only [hz, add_zero] at hsum
  rw [← hsum, shiftedHarmonic_sum t ht]
  ring

theorem trialLeft_functional_positive (N : ℕ) (a t : ℝ) (ha : 0 ≤ a) (ht : 1 ≤ t)
    (i j : Fin N) (hij : i.val + 1 = j.val) :
    0 < trialSlopeFunctional a t (trialLeft N t) i := by
  have hJ : 2 ≤ N - i.val := by omega
  have hu : 2 * t ≤ (i.val : ℝ) + 2 * t := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hpositive := trial_left_slope_positive (N - i.val) hJ a t ((i.val : ℝ) + 2 * t) ha ht hu
  have hd : energyD N a i.val = ((N - i.val : ℕ) : ℝ) + a := by
    rw [Nat.cast_sub (by omega)]
    unfold energyD
    ring
  have hjR : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij.symm
  unfold trialSlopeFunctional
  rw [trialLeft_tail, difference_adjacent _ i j hij, hd]
  simp only [trialLeft, hjR]
  convert hpositive using 1 <;> congr 1 <;> ring

theorem trialRight_functional_positive (N : ℕ) (a t : ℝ) (ha : 0 ≤ a) (ht : 1 ≤ t)
    (hmax : a ≤ trialParameterMax t) (i j : Fin N) (hij : i.val + 1 = j.val) :
    0 < trialSlopeFunctional a t (trialRight N t) i := by
  have hJ : 2 ≤ N - i.val := by omega
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hd : energyD N a i.val = ((N - i.val : ℕ) : ℝ) + a := by
    rw [Nat.cast_sub (by omega)]
    unfold energyD
    ring
  have hstep : shiftedHarmonic t (N - i.val) =
      shiftedHarmonic t (N - j.val) + 1 / (((N - i.val : ℕ) : ℝ) + 2 * t) := by
    have hnat : N - i.val = N - j.val + 1 := by omega
    conv_lhs => rw [hnat, shiftedHarmonic_step]
    rw [hnat, Nat.cast_add, Nat.cast_one]
  have hdiff : difference (trialRight N t) i =
      (1 / (((N - i.val : ℕ) : ℝ) + 2 * t)) / (N : ℝ) := by
    rw [difference_adjacent _ i j hij]
    simp only [trialRight, ← sub_div]
    rw [hstep]
    ring
  have hid : trialSlopeFunctional a t (trialRight N t) i =
      (((N - i.val : ℕ) : ℝ) + (a - t - 1) * shiftedHarmonic t (N - i.val) -
        t * (((N - i.val : ℕ) : ℝ) + a) / (((N - i.val : ℕ) : ℝ) + 2 * t)) / (N : ℝ) := by
    unfold trialSlopeFunctional
    rw [trialRight_tail N t ht i, hdiff, hd]
    simp only [trialRight]
    ring
  rw [hid]
  exact div_pos (trial_right_slope_positive (N - i.val) hJ a t ha ht hmax) hn

theorem trialVector_functional_positive (N : ℕ) (a t : ℝ) (ha : 0 ≤ a) (ht : 1 ≤ t)
    (hmax : a ≤ trialParameterMax t) (i j : Fin N) (hij : i.val + 1 = j.val) :
    0 < trialSlopeFunctional a t (trialVector N t) i := by
  rw [trialVector_profiles, trialSlopeFunctional_add]
  exact add_pos (trialLeft_functional_positive N a t ha ht i j hij)
    (trialRight_functional_positive N a t ha ht hmax i j hij)

end
end CriticalExtrapolation.Paper
