import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace CriticalExtrapolation

open scoped BigOperators

/-- The weighted Cauchy--Schwarz inequality behind (7.3), for arbitrary real u. -/
theorem weighted_cauchy_schwarz {ι : Type*} [Fintype ι]
    (e u : ι → ℝ) (he : ∀ i, 0 < e i) :
    (∑ i, u i) ^ 2 ≤ (∑ i, e i * (u i) ^ 2) * (∑ i, 1 / e i) := by
  classical
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
  · intro i _
    exact mul_nonneg (le_of_lt (he i)) (sq_nonneg _)
  · intro i _
    exact div_nonneg (by norm_num) (le_of_lt (he i))
  · intro i _
    field_simp [ne_of_gt (he i)]

/-- Normalization converts the weighted bound into a reciprocal-sum energy bound. -/
theorem normalized_energy_lower_bound {ι : Type*} [Fintype ι]
    (e u : ι → ℝ) (F : ℝ) (he : ∀ i, 0 < e i)
    (hF : F ≠ 0) (hnorm : ∑ i, u i = 1 / F)
    (hR : 0 < ∑ i, 1 / e i) :
    1 / (∑ i, 1 / e i) ≤ F ^ 2 * (∑ i, e i * (u i) ^ 2) := by
  have hCS := weighted_cauchy_schwarz e u he
  rw [hnorm] at hCS
  apply (div_le_iff₀ hR).mpr
  have hmul := mul_le_mul_of_nonneg_left hCS (sq_nonneg F)
  have hunit : F ^ 2 * (1 / F) ^ 2 = 1 := by
    field_simp
  rw [hunit] at hmul
  simpa only [mul_assoc] using hmul

end CriticalExtrapolation
