import PaperFramework.Definitions

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem quadraticForm_row_sos {N : ℕ} (M : Mat N) (u : Vec N)
    (hsym : ∀ i j, M i j = M j i) :
    quadraticForm M u =
      (∑ i, ∑ j, (-M i j) * (u i - u j) ^ 2) / 2 +
        ∑ i, (∑ j, M i j) * (u i) ^ 2 := by
  have hrow : (∑ i, ∑ j, M i j * (u i) ^ 2) =
      ∑ i, (∑ j, M i j) * (u i) ^ 2 := by simp_rw [Finset.sum_mul]
  have hcol : (∑ i, ∑ j, M i j * (u j) ^ 2) =
      ∑ i, (∑ j, M i j) * (u i) ^ 2 := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ i, ∑ j, M i j * (u i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hsym j i]
      _ = _ := hrow
  have hexpand : (∑ i, ∑ j, (-M i j) * (u i - u j) ^ 2) =
      2 * quadraticForm M u - (∑ i, ∑ j, M i j * (u i) ^ 2) -
        ∑ i, ∑ j, M i j * (u j) ^ 2 := by
    unfold quadraticForm
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hrow, hcol] at hexpand
  linarith

theorem positiveQuadratic_of_positive_row_sums {N : ℕ} (M : Mat N)
    (hsym : ∀ i j, M i j = M j i)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) (hrow : ∀ i, 0 < ∑ j, M i j) :
    PositiveQuadratic M := by
  intro u hu
  have hex : ∃ i, u i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (funext h)
  obtain ⟨i, hi⟩ := hex
  have hdiag : 0 < ∑ j, (∑ k, M j k) * (u j) ^ 2 := by
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (hrow j).le (sq_nonneg _)
    · exact ⟨i, Finset.mem_univ _, mul_pos (hrow i) (sq_pos_of_ne_zero hi)⟩
  have hedge : 0 ≤ ∑ i, ∑ j, (-M i j) * (u i - u j) ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases hij : i = j
    · subst j
      simp
    · exact mul_nonneg (neg_nonneg.mpr (hoff i j hij)) (sq_nonneg _)
  rw [quadraticForm_row_sos M u hsym]
  exact add_pos_of_nonneg_of_pos (div_nonneg hedge (by norm_num)) hdiag

theorem sum_fin_indicator_le (N k : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (∑ j : Fin N, if j.val = k then r else 0) ≤ r := by
  by_cases hk : k < N
  · let i : Fin N := ⟨k, hk⟩
    have hpred : ∀ j : Fin N, (j.val = k) ↔ j = i := by
      intro j
      constructor
      · intro hj
        exact Fin.ext hj
      · intro hj
        exact congrArg Fin.val hj
    simp_rw [hpred]
    simp
  · have hpred : ∀ j : Fin N, j.val ≠ k := by
      intro j hj
      exact hk (hj ▸ j.isLt)
    simpa only [hpred, if_false, Finset.sum_const_zero] using hr

end
end CriticalExtrapolation.Paper
