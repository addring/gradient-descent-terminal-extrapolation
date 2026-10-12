import PaperFramework.TrialReferenceModel

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem trialLeft_tail_reference_lower (N : ℕ) (t : ℝ) (ht : 1 ≤ t) (i : Fin N) :
    ((N : ℝ) - i.val) / ((N : ℝ) + 2 * t) ≤ tail (trialLeft N t) i.val := by
  have hn : 0 < (N : ℝ) + 2 * t := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  rw [trialLeft_tail]
  calc
    _ = ∑ k ∈ Finset.range (N - i.val), 1 / ((N : ℝ) + 2 * t) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Nat.cast_sub (Nat.le_of_lt i.isLt)]
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN : i.val + k ≤ N := by
        have := Finset.mem_range.mp hk
        have := i.isLt
        omega
      have hkR : (i.val : ℝ) + (k : ℝ) ≤ N := by exact_mod_cast hkN
      have hu : 0 < (i.val : ℝ) + (k : ℝ) + 2 * t := by
        have := Nat.cast_nonneg (α := ℝ) i.val
        have := Nat.cast_nonneg (α := ℝ) k
        linarith
      rw [show (i.val : ℝ) + 2 * t + (k : ℝ) = (i.val : ℝ) + (k : ℝ) + 2 * t by ring]
      apply one_div_le_one_div_of_le hu
      linarith

theorem trial_baseline_reciprocal_upper (N : ℕ) (t : ℝ) (ht : 1 ≤ t) (i : Fin N) :
    tailU 0 1 (trialVector N t) i ≤
      (1 + 2 * t) / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t)) := by
  have hN : 1 ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt))
  have hn : 0 < (N : ℝ) := by linarith
  have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
  have hu : 0 < (i.val : ℝ) + 2 * t := by have := Nat.cast_nonneg (α := ℝ) i.val; linarith
  have hj : 0 < (N : ℝ) - i.val := sub_pos.mpr hi
  have hT : 0 < (N : ℝ) + 2 * t := by linarith
  have hr : 0 ≤ tail (trialLeft N t) i.val - ((N : ℝ) - i.val) / ((N : ℝ) + 2 * t) :=
    sub_nonneg.mpr (trialLeft_tail_reference_lower N t ht i)
  have hq := shiftedHarmonic_nonnegative t ht (N - i.val)
  have hsmall : 2 * t / ((N : ℝ) * ((N : ℝ) + 2 * t) * ((N : ℝ) - i.val + 1)) ≤
      2 * t / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t)) := by
    apply div_le_div_of_nonneg_left (by linarith) (mul_pos hj hu)
    calc
      _ ≤ ((N : ℝ) - i.val) * ((N : ℝ) + 2 * t) :=
        mul_le_mul_of_nonneg_left (by linarith) hj.le
      _ ≤ ((N : ℝ) - i.val + 1) * ((N : ℝ) + 2 * t) :=
        mul_le_mul_of_nonneg_right (by linarith) hT.le
      _ ≤ (N : ℝ) * (((N : ℝ) - i.val + 1) * ((N : ℝ) + 2 * t)) :=
        le_mul_of_one_le_left (mul_nonneg (by linarith) hT.le) hN
      _ = _ := by ring
  have hminus : 0 ≤ (tail (trialLeft N t) i.val -
      ((N : ℝ) - i.val) / ((N : ℝ) + 2 * t)) /
      (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1)) := by positivity
  have hqterm : 0 ≤ 2 * t * shiftedHarmonic t (N - i.val) /
      ((N : ℝ) * ((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1)) := by
    exact div_nonneg (mul_nonneg (by linarith) hq) (by positivity)
  have he := trial_baseline_reciprocal_difference N t ht i
  have hsum : (1 + 2 * t) / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t)) =
      1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t)) +
        2 * t / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t)) := by ring
  rw [hsum]
  linarith only [he, hsmall, hminus, hqterm]

end
end CriticalExtrapolation.Paper
