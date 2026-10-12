import PaperFramework.QuadraticVariation

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def qpNormalization (N : ℕ) : Vec N →ₗ[ℝ] ℝ := coordinateLinear 1

/-- Exactly N-1 adjacent slope rows and N difference rows. -/
def qpConstraintLinear {N : ℕ} (h c : ℝ) :
    Fin (N - 1) ⊕ Fin N → Vec N →ₗ[ℝ] ℝ
  | Sum.inl k => coordinateLinear (AEntry h c k)
  | Sum.inr k => coordinateLinear (DEntry k)

theorem qpNormalization_apply {N : ℕ} (β : Vec N) : qpNormalization N β = ∑ i, β i := by
  simp [qpNormalization, coordinateLinear]

theorem REntry_apply {N : ℕ} (h c : ℝ) (β : Vec N) (i : Fin N) :
    (∑ j, REntry h c i j * β j) = slope h c β i := by
  unfold REntry slope
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [TEntry_apply]

theorem AEntry_apply {N : ℕ} (h c : ℝ) (β : Vec N) (i : Fin (N - 1)) :
    (∑ j, AEntry h c i j * β j) =
      slope h c β (slopeLeft i) - slope h c β (slopeRight i) := by
  unfold AEntry
  simp_rw [sub_mul, Finset.sum_sub_distrib, REntry_apply]

theorem qpConstraint_slope {N : ℕ} (h c : ℝ) (β : Vec N) (i : Fin (N - 1)) :
    qpConstraintLinear h c (Sum.inl i) β =
      slope h c β (slopeLeft i) - slope h c β (slopeRight i) := AEntry_apply h c β i

theorem qpConstraint_difference {N : ℕ} (h c : ℝ) (β : Vec N) (i : Fin N) :
    qpConstraintLinear h c (Sum.inr i) β = difference β i := DEntry_apply β i

theorem qp_feasible_iff {N : ℕ} (h c : ℝ) (β : Vec N) :
    Feasible h c β ↔ qpNormalization N β = 1 ∧ ∀ i, 0 ≤ qpConstraintLinear h c i β := by
  rw [qpNormalization_apply]
  constructor
  · intro hβ
    refine ⟨hβ.1, ?_⟩
    intro i
    cases i with
    | inl k =>
      rw [qpConstraint_slope]
      exact sub_nonneg.mpr (hβ.2.2 (slopeLeft k) (slopeRight k) rfl)
    | inr k => simpa only [qpConstraint_difference] using hβ.2.1 k
  · rintro ⟨hnorm, hrows⟩
    refine ⟨hnorm, fun i => ?_, ?_⟩
    · simpa only [qpConstraint_difference] using hrows (Sum.inr i)
    ·
      intro i j hij
      let k : Fin (N - 1) := ⟨i.val, by omega⟩
      have hi : slopeLeft k = i := Fin.ext rfl
      have hj : slopeRight k = j := Fin.ext hij
      have h := hrows (Sum.inl k)
      rw [qpConstraint_slope, hi, hj] at h
      exact sub_nonneg.mp h

theorem qpConstraint_positive_of_strict {N : ℕ} (h c : ℝ) (β : Vec N)
    (hβ : StrictlyFeasible h c β) : ∀ i, 0 < qpConstraintLinear h c i β := by
  intro i
  cases i with
  | inl k =>
    rw [qpConstraint_slope]
    exact sub_pos.mpr (hβ.2.2 (slopeLeft k) (slopeRight k) rfl)
  | inr k => simpa only [qpConstraint_difference] using hβ.2.1 k

end
end CriticalExtrapolation.Paper
