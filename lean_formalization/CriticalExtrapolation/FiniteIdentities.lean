import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace CriticalExtrapolation

open scoped BigOperators

/-- Finite telescoping, used for zero-extended tails and flow divergences. -/
theorem sum_differences (z : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, (z i - z (i + 1))) = z 0 - z N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Exact first-moment summation by parts, including the terminal boundary term. -/
theorem sum_weighted_differences (β : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, ((i : ℝ) + 1) * (β i - β (i + 1))) =
      (∑ i ∈ Finset.range N, β i) - (N : ℝ) * β N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem sum_weighted_differences_zero_boundary (β : ℕ → ℝ) (N : ℕ) (hβ : β N = 0) :
    (∑ i ∈ Finset.range N, ((i : ℝ) + 1) * (β i - β (i + 1))) =
      ∑ i ∈ Finset.range N, β i := by
  rw [sum_weighted_differences, hβ]
  simp

/-- Cancellation of the sum square in (3.4); the tail convention is explicit. -/
theorem sum_mul_tail (u : ℕ → ℝ) (N : ℕ) :
    2 * (∑ i ∈ Finset.range N, u i * (∑ j ∈ Finset.range (N - i), u (i + j))) =
      (∑ i ∈ Finset.range N, u i) ^ 2 + ∑ i ∈ Finset.range N, (u i) ^ 2 := by
  induction N generalizing u with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero, zero_add]
    have htail : (∑ i ∈ Finset.range N,
        u (i + 1) * ∑ j ∈ Finset.range (N + 1 - (i + 1)), u (i + 1 + j)) =
        ∑ i ∈ Finset.range N,
          (fun k => u (k + 1)) i * ∑ j ∈ Finset.range (N - i), (fun k => u (k + 1)) (i + j) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    rw [htail]
    rw [Finset.sum_range_succ' u, Finset.sum_range_succ' (fun i => (u i) ^ 2)]
    have h := ih (fun k => u (k + 1))
    nlinarith only [h]

end CriticalExtrapolation
