import CriticalExtrapolation.Weights
import CriticalExtrapolation.FiniteIdentities
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

namespace CriticalExtrapolation

open scoped BigOperators

noncomputable def referenceReciprocalSum (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, 1 / referenceWeight (N : ℝ) (i : ℝ)

noncomputable def harmonicSum (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1)

/-- The reversal used for the right endpoint, with real subtraction fully justified. -/
theorem sum_reverse_endpoint (f : ℝ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, f ((N : ℝ) - (i : ℝ))) =
      ∑ i ∈ Finset.range N, f ((i : ℝ) + 1) := by
  calc
    _ = ∑ i ∈ Finset.range N, f (((N - 1 - i : ℕ) : ℝ) + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiN := Finset.mem_range.mp hi
      have hnat : N - 1 - i + 1 = N - i := by omega
      have hcast : (((N - 1 - i : ℕ) : ℝ) + 1) = (N : ℝ) - (i : ℝ) := by
        calc
          _ = ((N - 1 - i + 1 : ℕ) : ℝ) := by simp
          _ = ((N - i : ℕ) : ℝ) := congrArg (fun k : ℕ => (k : ℝ)) hnat
          _ = _ := Nat.cast_sub (Nat.le_of_lt hiN)
      rw [hcast]
    _ = _ := Finset.sum_range_reflect (fun k => f ((k : ℝ) + 1)) N

theorem sum_inverse_comparisonWeight (N : ℕ) :
    (∑ i ∈ Finset.range N, 1 / comparisonWeight (N : ℝ) (i : ℝ)) = harmonicSum N := by
  have hterms : (∑ i ∈ Finset.range N, 1 / comparisonWeight (N : ℝ) (i : ℝ)) =
      (∑ i ∈ Finset.range N, (1 / ((i : ℝ) + 1) + 1 / ((N : ℝ) - (i : ℝ))) / 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply inverse_comparisonWeight (Nat.cast_nonneg i)
    exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hi)
  rw [hterms, ← Finset.sum_div, Finset.sum_add_distrib,
    sum_reverse_endpoint (fun x : ℝ => 1 / x)]
  unfold harmonicSum
  ring

/-- A telescoping majorant; this proves a uniform series bound without a numerical sum. -/
theorem reciprocal_square_majorant {k : ℝ} (hk : 1 ≤ k) :
    1 / k ^ 2 ≤ 2 * (1 / k - 1 / (k + 1)) := by
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k + 1 := by linarith
  have hdiff : 1 / k - 1 / (k + 1) = 1 / (k * (k + 1)) := by
    field_simp
    ring
  rw [hdiff, ← mul_div_assoc]
  apply (div_le_div_iff₀ (sq_pos_of_pos hk0) (mul_pos hk0 hk1)).mpr
  have hp : 0 ≤ k * (k - 1) := mul_nonneg (le_of_lt hk0) (by linarith)
  nlinarith only [hp]

theorem sum_reciprocal_squares_lt_two (N : ℕ) :
    (∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) ^ 2) < 2 := by
  have hbound : (∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) ^ 2) ≤
      2 * (∑ i ∈ Finset.range N,
        (1 / ((i : ℝ) + 1) - 1 / (((i + 1 : ℕ) : ℝ) + 1))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [Nat.cast_add, Nat.cast_one] using
      reciprocal_square_majorant (show 1 ≤ (i : ℝ) + 1 by
        have : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
        linarith)
  rw [sum_differences (fun i => 1 / ((i : ℝ) + 1)) N] at hbound
  have hp : 0 < 1 / ((N : ℝ) + 1) := by positivity
  simp only [Nat.cast_zero, zero_add, div_one] at hbound
  linarith

/-- A uniform, all-N error bound from the corrected absolute pointwise comparison. -/
theorem referenceReciprocalSum_error (N : ℕ) (hN : 2 ≤ N) :
    |referenceReciprocalSum N - harmonicSum N| < 8 := by
  rw [referenceReciprocalSum, ← sum_inverse_comparisonWeight N, ← Finset.sum_sub_distrib]
  have hpoint : (∑ i ∈ Finset.range N,
      |1 / referenceWeight (N : ℝ) (i : ℝ) -
        1 / comparisonWeight (N : ℝ) (i : ℝ)|) ≤
      ∑ i ∈ Finset.range N,
        2 * (1 / ((i : ℝ) + 1) ^ 2 + 1 / ((N : ℝ) - (i : ℝ)) ^ 2) := by
    apply Finset.sum_le_sum
    intro i hi
    apply reciprocal_referenceWeight_error (by exact_mod_cast hN) (Nat.cast_nonneg i)
    exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hi)
  have hsum : (∑ i ∈ Finset.range N,
      2 * (1 / ((i : ℝ) + 1) ^ 2 + 1 / ((N : ℝ) - (i : ℝ)) ^ 2)) =
      4 * ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib,
      sum_reverse_endpoint (fun x : ℝ => 1 / x ^ 2)]
    ring
  have htriangle := Finset.abs_sum_le_sum_abs
    (fun i : ℕ => 1 / referenceWeight (N : ℝ) (i : ℝ) -
      1 / comparisonWeight (N : ℝ) (i : ℝ)) (Finset.range N)
  rw [hsum] at hpoint
  have hseries := sum_reciprocal_squares_lt_two N
  linarith

end CriticalExtrapolation
