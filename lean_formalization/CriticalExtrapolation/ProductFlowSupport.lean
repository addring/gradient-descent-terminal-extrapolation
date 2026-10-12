import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

namespace CriticalExtrapolation

open scoped BigOperators

def productFlow (O π : ℕ → ℝ) (i j : ℕ) : ℝ :=
  O i * π j * ∏ k ∈ Finset.Ioo i j, (1 - π k)

/-- A positive edge cannot skip a node at which adjacent slopes differ.
This conclusion does not refer to the arrival slope τ_j. -/
theorem positive_productFlow_adjacent_slopes
    (O π τ : ℕ → ℝ) (i j : ℕ)
    (hF : 0 < productFlow O π i j)
    (hcomp : ∀ k ∈ Finset.Ioo i j, (1 - π k) * (τ (k - 1) - τ k) = 0) :
    ∀ k ∈ Finset.Ioo i j, τ (k - 1) = τ k := by
  have hprod : (∏ k ∈ Finset.Ioo i j, (1 - π k)) ≠ 0 := by
    exact (mul_ne_zero_iff.mp (ne_of_gt hF)).2
  intro k hk
  have hs : 1 - π k ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod) k hk
  have hdiff : τ (k - 1) - τ k = 0 :=
    (mul_eq_zero.mp (hcomp k hk)).resolve_left hs
  exact sub_eq_zero.mp hdiff

/-- The corrected (6.3a): slopes are equal from i through j−1, never through j. -/
theorem positive_productFlow_support
    (O π τ : ℕ → ℝ) (i j : ℕ)
    (hF : 0 < productFlow O π i j)
    (hcomp : ∀ k ∈ Finset.Ioo i j, (1 - π k) * (τ (k - 1) - τ k) = 0) :
    ∀ m, i ≤ m → m < j → τ m = τ i := by
  have hadj := positive_productFlow_adjacent_slopes O π τ i j hF hcomp
  intro m
  induction m with
  | zero =>
    intro hi _
    have : i = 0 := by omega
    rw [this]
  | succ m ih =>
    intro him hmj
    by_cases heq : i = m + 1
    · rw [heq]
    · have hik : i < m + 1 := by omega
      have hk : m + 1 ∈ Finset.Ioo i j := Finset.mem_Ioo.mpr ⟨hik, hmj⟩
      have hs := hadj (m + 1) hk
      simp only [Nat.add_sub_cancel] at hs
      exact hs.symm.trans (ih (by omega) (by omega))

end CriticalExtrapolation
