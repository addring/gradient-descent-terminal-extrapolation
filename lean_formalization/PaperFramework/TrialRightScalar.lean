import PaperFramework.TrialBasics

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem shiftedHarmonic_sum (t : ℝ) (ht : 1 ≤ t) (j : ℕ) :
    (∑ k ∈ Finset.range (j + 1), shiftedHarmonic t k) =
      ((j : ℝ) + 2 * t + 1) * shiftedHarmonic t j - (j : ℝ) := by
  induction j with
  | zero => simp [shiftedHarmonic]
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [shiftedHarmonic_step, Nat.cast_add, Nat.cast_one]
    have hd : (j : ℝ) + 1 + 2 * t ≠ 0 := by
      have := Nat.cast_nonneg (α := ℝ) j
      linarith
    field_simp [hd]
    <;> ring

theorem shiftedHarmonic_upper (t : ℝ) (ht : 1 ≤ t) (j : ℕ) :
    shiftedHarmonic t j ≤ (j : ℝ) / (2 * t + 1) := by
  have hd : 0 < 2 * t + 1 := by linarith
  calc
    _ ≤ ∑ k ∈ Finset.range j, 1 / (2 * t + 1) := by
      apply Finset.sum_le_sum
      intro k _
      have hk := Nat.cast_nonneg (α := ℝ) k
      apply (div_le_div_iff₀ (by linarith : 0 < (k : ℝ) + 1 + 2 * t) hd).mpr
      simp only [one_mul]
      linarith
    _ = _ := by simp [div_eq_mul_inv]

/-- The harmonic endpoint profile has strictly decreasing slopes in the paper's full a range. -/
theorem trial_right_slope_positive (j : ℕ) (hj : 2 ≤ j) (a t : ℝ)
    (ha : 0 ≤ a) (ht : 1 ≤ t) (hmax : a ≤ 1 / (2 * t + 1)) :
    0 < (j : ℝ) + (a - t - 1) * shiftedHarmonic t j - t * ((j : ℝ) + a) / ((j : ℝ) + 2 * t) := by
  have hJ : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have ht0 : 0 < t := by linarith
  have hC : 0 < 2 * t + 1 := by linarith
  have hD : 0 < (j : ℝ) + 2 * t := by linarith
  have hAone : a ≤ 1 := hmax.trans ((div_le_one hC).mpr (by linarith))
  have hcoef : a - t - 1 ≤ 0 := by linarith
  have hq := mul_le_mul_of_nonpos_left (shiftedHarmonic_upper t ht j) hcoef
  have hpoly : 1 < (j : ℝ) * ((j : ℝ) - 1) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ (j : ℝ) - 2) (by linarith : 0 ≤ (j : ℝ) - 1)]
  have hstrict : 1 / (2 * t + 1) < (j : ℝ) * ((j : ℝ) - 1) / (2 * t + 1) :=
    div_lt_div_of_pos_right hpoly hC
  have hnum : 0 < (j : ℝ) * ((j : ℝ) - 1) / (2 * t + 1) - a := by linarith
  have hpositive := mul_pos (div_pos ht0 hD) hnum
  have haJ : 0 ≤ a * (j : ℝ) / (2 * t + 1) :=
    div_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) hC.le
  have hid : (j : ℝ) + (a - t - 1) * ((j : ℝ) / (2 * t + 1)) -
      t * ((j : ℝ) + a) / ((j : ℝ) + 2 * t) =
      t / ((j : ℝ) + 2 * t) * ((j : ℝ) * ((j : ℝ) - 1) / (2 * t + 1) - a) +
        a * (j : ℝ) / (2 * t + 1) := by
    field_simp [ne_of_gt hC, ne_of_gt hD]
    <;> ring
  linarith

end
end CriticalExtrapolation.Paper
