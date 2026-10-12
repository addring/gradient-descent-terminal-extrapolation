import PaperFramework.TrialNormalization

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- Finite summation by parts for the reciprocal endpoint weights. -/
theorem trial_finite_abel (f : ℕ → ℝ) (hf : f 0 = 0) (n : ℕ) :
    (∑ k ∈ Finset.range n, f (k + 1) / (((k : ℝ) + 1) * ((k : ℝ) + 2))) =
      (∑ k ∈ Finset.range n, (f (k + 1) - f k) / ((k : ℝ) + 1)) -
        f n / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp [hf]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [h1, h2]
    <;> ring

end
end CriticalExtrapolation.Paper
