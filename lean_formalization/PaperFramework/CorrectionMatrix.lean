import PaperFramework.TridiagonalStructure
import PaperFramework.MatrixPositivity

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def correctionRight (N : ℕ) (a t : ℝ) (i : ℕ) : ℝ :=
  ((i : ℝ) + 1) * energyZeta N a t i * (energyZeta N a t i - 2) / energyD N a i

def correctionLeft (N : ℕ) (a t : ℝ) (i : ℕ) : ℝ :=
  (i : ℝ) * (energyZeta N a t i ^ 2 - 1) / (energyD N a i + 1)

theorem energyZeta_ge_two (N : ℕ) (a t : ℝ) (ha : 0 ≤ a) (ht : 1 ≤ t) (i : Fin N) :
    2 ≤ energyZeta N a t i.val := by
  have hi : (i.val : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt i.isLt
  unfold energyZeta energyF
  linarith

theorem correctionRight_nonnegative (N : ℕ) (a t : ℝ)
    (ha : 0 ≤ a) (ht : 1 ≤ t) (i : Fin N) : 0 ≤ correctionRight N a t i.val := by
  have hz := energyZeta_ge_two N a t ha ht i
  have hd := energyD_pos N a ha i
  unfold correctionRight
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)) hd.le

theorem correctionLeft_nonnegative (N : ℕ) (a t : ℝ)
    (ha : 0 ≤ a) (ht : 1 ≤ t) (i : Fin N) : 0 ≤ correctionLeft N a t i.val := by
  have hz := energyZeta_ge_two N a t ha ht i
  have hd := energyD_pos N a ha i
  unfold correctionLeft
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by nlinarith)) (by linarith)

theorem correction_left_eq_previous_right (N : ℕ) (a t : ℝ) (i j : Fin N)
    (hji : j.val + 1 = i.val) : correctionLeft N a t i.val = correctionRight N a t j.val := by
  have hi : (i.val : ℝ) = (j.val : ℝ) + 1 := by exact_mod_cast hji.symm
  have hz : energyZeta N a t j.val = energyZeta N a t i.val + 1 := by
    unfold energyZeta
    rw [hi]
    ring
  have hd : energyD N a j.val = energyD N a i.val + 1 := by
    unfold energyD
    rw [hi]
    ring
  unfold correctionLeft correctionRight
  rw [hz, hd, ← hi]
  congr 1
  ring

theorem correction_matrix_entries (N : ℕ) (a t : ℝ) (i j : Fin N) :
    H N a t i j =
      (if i = j then 2 * ((i.val : ℝ) + 1) * energyZeta N a t i.val ^ 2 / energyD N a i.val else 0) -
      (if j.val + 1 = i.val then correctionLeft N a t i.val else 0) -
      (if i.val + 1 = j.val then correctionRight N a t i.val else 0) := by
  by_cases hij : i = j
  · subst j
    simp [H]
  · by_cases hright : i.val + 1 = j.val
    · have hleft : ¬j.val + 1 = i.val := by omega
      simp [H, hij, hright, hleft, correctionRight]
    · by_cases hleft : j.val + 1 = i.val
      · rw [correction_left_eq_previous_right N a t i j hleft]
        simp [H, hij, hright, hleft, correctionRight]
      · simp [H, hij, hright, hleft]

theorem correction_matrix_symmetric (N : ℕ) (a t : ℝ) : ∀ i j, H N a t i j = H N a t j i := by
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · by_cases hright : i.val + 1 = j.val
    · have hleft : ¬j.val + 1 = i.val := by omega
      simp [H, hij, Ne.symm hij, hright, hleft]
    · by_cases hleft : j.val + 1 = i.val
      · simp [H, hij, Ne.symm hij, hright, hleft]
      · simp [H, hij, Ne.symm hij, hright, hleft]

theorem correction_matrix_off_nonpositive (N : ℕ) (a t : ℝ)
    (ha : 0 ≤ a) (ht : 1 ≤ t) : ∀ i j, i ≠ j → H N a t i j ≤ 0 := by
  intro i j hij
  rw [correction_matrix_entries, if_neg hij]
  have hleft : 0 ≤ (if j.val + 1 = i.val then correctionLeft N a t i.val else 0) :=
    ite_nonneg (correctionLeft_nonnegative N a t ha ht i) le_rfl
  have hright : 0 ≤ (if i.val + 1 = j.val then correctionRight N a t i.val else 0) :=
    ite_nonneg (correctionRight_nonnegative N a t ha ht i) le_rfl
  linarith

theorem correction_matrix_row_positive (N : ℕ) (a t : ℝ)
    (ha : 0 ≤ a) (ht : 1 ≤ t) (i : Fin N) : 0 < ∑ j, H N a t i j := by
  have hL := correctionLeft_nonnegative N a t ha ht i
  have hR := correctionRight_nonnegative N a t ha ht i
  have hleft : (∑ j : Fin N, if j.val + 1 = i.val then correctionLeft N a t i.val else 0) ≤
      correctionLeft N a t i.val := by
    by_cases hi : i.val = 0
    · simpa [hi] using hL
    · have hpred : ∀ j : Fin N, (j.val + 1 = i.val) ↔ j.val = i.val - 1 := by
        intro j
        omega
      simp_rw [hpred]
      exact sum_fin_indicator_le N (i.val - 1) _ hL
  have hright : (∑ j : Fin N, if i.val + 1 = j.val then correctionRight N a t i.val else 0) ≤
      correctionRight N a t i.val := by
    simpa only [eq_comm] using sum_fin_indicator_le N (i.val + 1) _ hR
  have hlower := tridiagonal_row_lower_pos (energyD_pos N a ha i)
    (energyZeta_ge_two N a t ha ht i) (Nat.cast_nonneg (α := ℝ) i.val)
  have hid : 2 * ((i.val : ℝ) + 1) * energyZeta N a t i.val ^ 2 / energyD N a i.val -
      correctionLeft N a t i.val - correctionRight N a t i.val =
      ((i.val : ℝ) + 1) * energyZeta N a t i.val * (energyZeta N a t i.val + 2) / energyD N a i.val -
        (i.val : ℝ) * (energyZeta N a t i.val ^ 2 - 1) / (energyD N a i.val + 1) := by
    unfold correctionLeft correctionRight
    ring
  simp_rw [correction_matrix_entries, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  linarith

/-- Positive row sums handle the actual first/last rows without inventing boundary entries. -/
theorem correction_matrix_positive (N : ℕ) (a t : ℝ)
    (hN : 0 < N) (ha : 0 ≤ a) (ht : 1 ≤ t) : PositiveQuadratic (H N a t) :=
  positiveQuadratic_of_positive_row_sums (H N a t)
    (correction_matrix_symmetric N a t) (correction_matrix_off_nonpositive N a t ha ht)
    (correction_matrix_row_positive N a t ha ht)

theorem energy_quadratic_split (N : ℕ) (a t : ℝ)
    (hN : 0 < N) (ha : 0 ≤ a) (ht : 1 ≤ t) (u : Vec N) :
    quadraticForm (E N a t) u =
      (∑ i, referenceWeight (energyF N a t - 1) (i.val : ℝ) * (u i) ^ 2) +
        (t - 1) / energyF N a t * quadraticForm (H N a t) u := by
  unfold quadraticForm
  simp_rw [tridiagonal_matrix_split N a t hN ha ht, add_mul, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp [ite_mul, pow_two, mul_assoc]
  · simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Equation (3.8), with the corrected reference weight and the full matrix. -/
theorem energy_matrix_domination (N : ℕ) (a t : ℝ)
    (hN : 0 < N) (ha : 0 ≤ a) (ht : 1 ≤ t) (u : Vec N) :
    (∑ i, referenceWeight (N : ℝ) (i.val : ℝ) * (u i) ^ 2) ≤ quadraticForm (E N a t) u := by
  have hH : 0 ≤ quadraticForm (H N a t) u := by
    by_cases hu : u = 0
    · subst u
      simp [quadraticForm]
    · exact (correction_matrix_positive N a t hN ha ht u hu).le
  have hfac : 0 ≤ (t - 1) / energyF N a t :=
    div_nonneg (sub_nonneg.mpr ht) (energyF_pos N a t ha ht).le
  have hNm : (N : ℝ) ≤ energyF N a t - 1 := by
    unfold energyF
    linarith
  have hdiag : (∑ i, referenceWeight (N : ℝ) (i.val : ℝ) * (u i) ^ 2) ≤
      ∑ i, referenceWeight (energyF N a t - 1) (i.val : ℝ) * (u i) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right
      (referenceWeight_mono_parameter (Nat.cast_nonneg N) hNm (Nat.cast_nonneg i.val)) (sq_nonneg _)
  rw [energy_quadratic_split N a t hN ha ht u]
  exact hdiag.trans (le_add_of_nonneg_right (mul_nonneg hfac hH))

end
end CriticalExtrapolation.Paper
