import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace CriticalExtrapolation

open scoped BigOperators

/-- Equation (6.7), with `zᵢ = βᵢ xᵢ` and a symmetric double sum.
Diagonal terms of the edge sum vanish; each unordered edge occurs twice. -/
theorem weighted_sos_identity {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (β x : ι → ℝ) (Φ : ℝ)
    (hsym : ∀ i j, M i j = M j i)
    (hkernel : ∀ i, ∑ j, M i j * β j = Φ) :
    (∑ i, ∑ j, M i j * (β i * x i) * (β j * x j)) =
      (∑ i, ∑ j, (-M i j) * β i * β j * (x i - x j) ^ 2) / 2 +
        Φ * ∑ i, β i * (x i) ^ 2 := by
  classical
  have hrow : (∑ i, ∑ j, M i j * β i * β j * (x i) ^ 2) =
      Φ * ∑ i, β i * (x i) ^ 2 := by
    calc
      _ = ∑ i, (β i * (x i) ^ 2) * ∑ j, M i j * β j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = Φ * ∑ i, β i * (x i) ^ 2 := by
        simp_rw [hkernel]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hcol : (∑ i, ∑ j, M i j * β i * β j * (x j) ^ 2) =
      Φ * ∑ i, β i * (x i) ^ 2 := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ i, ∑ j, M i j * β i * β j * (x i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hsym j i]
        ring
      _ = _ := hrow
  have hexpand : (∑ i, ∑ j, (-M i j) * β i * β j * (x i - x j) ^ 2) =
      2 * (∑ i, ∑ j, M i j * (β i * x i) * (β j * x j)) -
        (∑ i, ∑ j, M i j * β i * β j * (x i) ^ 2) -
        (∑ i, ∑ j, M i j * β i * β j * (x j) ^ 2) := by
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hrow, hcol] at hexpand
  linarith

/-- The matrix conclusion needed by the certificate, including Φ=0. -/
theorem weighted_sos_nonnegative {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (β x : ι → ℝ) (Φ : ℝ)
    (hsym : ∀ i j, M i j = M j i)
    (hkernel : ∀ i, ∑ j, M i j * β j = Φ)
    (hβ : ∀ i, 0 < β i) (hΦ : 0 ≤ Φ)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) :
    0 ≤ ∑ i, ∑ j, M i j * (β i * x i) * (β j * x j) := by
  classical
  rw [weighted_sos_identity M β x Φ hsym hkernel]
  apply add_nonneg
  · apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases hij : i = j
    · subst j
      simp
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (neg_nonneg.mpr (hoff i j hij)) (le_of_lt (hβ i)))
          (le_of_lt (hβ j))) (sq_nonneg _)
  · apply mul_nonneg hΦ
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (le_of_lt (hβ i)) (sq_nonneg _)

/-- Equation (6.7) for an arbitrary z, in symmetric double-sum form. -/
theorem weighted_sos_identity_quotients {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (β z : ι → ℝ) (Φ : ℝ)
    (hsym : ∀ i j, M i j = M j i)
    (hkernel : ∀ i, ∑ j, M i j * β j = Φ)
    (hβ : ∀ i, 0 < β i) :
    (∑ i, ∑ j, M i j * z i * z j) =
      (∑ i, ∑ j, (-M i j) * β i * β j * (z i / β i - z j / β j) ^ 2) / 2 +
        Φ * ∑ i, (z i) ^ 2 / β i := by
  classical
  have hscale : ∀ i, β i * (z i / β i) = z i := by
    intro i
    exact mul_div_cancel₀ (z i) (ne_of_gt (hβ i))
  have hlast : (∑ i, β i * (z i / β i) ^ 2) = ∑ i, (z i) ^ 2 / β i := by
    apply Finset.sum_congr rfl
    intro i _
    field_simp [ne_of_gt (hβ i)]
  have h := weighted_sos_identity M β (fun i => z i / β i) Φ hsym hkernel
  simp only [hscale, hlast] at h
  exact h

/-- Nonnegativity of the quadratic form for every real vector, not just a weighted one. -/
theorem quadratic_form_nonnegative {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (β : ι → ℝ) (Φ : ℝ)
    (hsym : ∀ i j, M i j = M j i)
    (hkernel : ∀ i, ∑ j, M i j * β j = Φ)
    (hβ : ∀ i, 0 < β i) (hΦ : 0 ≤ Φ)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) :
    ∀ z : ι → ℝ, 0 ≤ ∑ i, ∑ j, M i j * z i * z j := by
  intro z
  have hscale : ∀ i, β i * (z i / β i) = z i := by
    intro i
    exact mul_div_cancel₀ (z i) (ne_of_gt (hβ i))
  simpa only [hscale] using weighted_sos_nonnegative M β (fun i => z i / β i)
    Φ hsym hkernel hβ hΦ hoff

end CriticalExtrapolation
