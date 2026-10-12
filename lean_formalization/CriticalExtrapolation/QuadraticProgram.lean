import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.CompleteField
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace CriticalExtrapolation

open scoped BigOperators

abbrev Direction (N : ℕ) := Fin N → ℝ

/-- Extension is used for differences only, never as an extra slope constraint. -/
def zeroExtend {N : ℕ} (β : Direction N) (i : ℕ) : ℝ :=
  if hi : i < N then β ⟨i, hi⟩ else 0

def difference {N : ℕ} (β : Direction N) (i : Fin N) : ℝ :=
  β i - zeroExtend β (i.val + 1)

def queryK (N : ℕ) (h c : ℝ) (i : Fin N) : ℝ :=
  h * ((N : ℝ) * c - (i.val : ℝ))

def applyT {N : ℕ} (h c : ℝ) (β : Direction N) (i : Fin N) : ℝ :=
  h * c * (∑ j, β j) - h * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), β j) - β i

noncomputable def slope {N : ℕ} (h c : ℝ) (β : Direction N) (i : Fin N) : ℝ :=
  applyT h c β i / queryK N h c i

/-- Exactly (3.1): N differences but only adjacent pairs of the N actual slopes. -/
def Feasible {N : ℕ} (h c : ℝ) (β : Direction N) : Prop :=
  (∑ i, β i) = 1 ∧
    (∀ i, 0 ≤ difference β i) ∧
    (∀ i j : Fin N, i.val + 1 = j.val → slope h c β j ≤ slope h c β i)

def StrictlyFeasible {N : ℕ} (h c : ℝ) (β : Direction N) : Prop :=
  (∑ i, β i) = 1 ∧
    (∀ i, 0 < difference β i) ∧
    (∀ i j : Fin N, i.val + 1 = j.val → slope h c β j < slope h c β i)

/-- The homogeneous chain-flow objective, not restricted to normalized β. -/
noncomputable def chainObjective {N : ℕ} (h c : ℝ) (β : Direction N) : ℝ :=
  h ^ 2 * c ^ 2 * (∑ i, β i) ^ 2 -
    2 * h * c * (1 + (N : ℝ) * h * c) *
      ∑ i, ((i.val : ℝ) + 1) * difference β i * slope h c β i

/-- The infimum is defined before proving attainment. It is not the critical coefficient. -/
noncomputable def auxiliaryValue (N : ℕ) (h c : ℝ) : ℝ :=
  sInf {r | ∃ β : Direction N, Feasible h c β ∧ r = chainObjective h c β}

end CriticalExtrapolation
