import PaperFramework.TailTransform

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem energyD_pos (N : ℕ) (a : ℝ) (ha : 0 ≤ a) (i : Fin N) :
    0 < energyD N a i.val := by
  have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
  unfold energyD
  linarith

theorem energyF_pos (N : ℕ) (a t : ℝ) (ha : 0 ≤ a) (ht : 1 ≤ t) :
    0 < energyF N a t := by
  unfold energyF
  have hN := Nat.cast_nonneg (α := ℝ) N
  linarith

theorem energyZeta_eq_D_add (N : ℕ) (a t : ℝ) (k : ℕ) :
    energyZeta N a t k = energyD N a k + t := by
  unfold energyZeta energyF energyD
  ring

theorem energyF_eq_D_add (N : ℕ) (a t : ℝ) (k : ℕ) :
    energyF N a t = energyD N a k + t + (k : ℝ) := by
  unfold energyF energyD
  ring

theorem tridiagonal_diagonal_entry_split (N : ℕ) (a t : ℝ)
    (ha : 0 ≤ a) (ht : 1 ≤ t) (i : Fin N) :
    energyDiagonal N a t i.val =
      referenceWeight (energyF N a t - 1) (i.val : ℝ) +
        (t - 1) / energyF N a t *
          (2 * ((i.val : ℝ) + 1) * energyZeta N a t i.val ^ 2 / energyD N a i.val) := by
  have hd := ne_of_gt (energyD_pos N a ha i)
  have hF := ne_of_gt (energyF_pos N a t ha ht)
  have hid := tridiagonal_diagonal_split (energyD N a i.val) t (i.val : ℝ) hd
    (by rw [← energyF_eq_D_add]; exact hF)
  simpa only [energyDiagonal, referenceWeight, sub_add_cancel,
    energyF_eq_D_add N a t i.val, energyZeta_eq_D_add] using hid

theorem tridiagonal_neighbor_entry_split (N : ℕ) (a t : ℝ) (i : ℕ) :
    energyNeighbor N a t i = (t - 1) / energyF N a t *
      (-(((i : ℝ) + 1) * energyZeta N a t i * (energyZeta N a t i - 2) / energyD N a i)) := by
  simpa only [energyNeighbor, energyF_eq_D_add N a t i, energyZeta_eq_D_add] using
    tridiagonal_neighbor_split (energyD N a i) t (i : ℝ)

/-- Equation (3.6), including both matrix boundary rows and all non-neighbor entries. -/
theorem tridiagonal_matrix_split (N : ℕ) (a t : ℝ)
    (hN : 0 < N) (ha : 0 ≤ a) (ht : 1 ≤ t) :
    ∀ i j, E N a t i j =
      (if i = j then referenceWeight (energyF N a t - 1) (i.val : ℝ) else 0) +
        (t - 1) / energyF N a t * H N a t i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa only [E, H, if_pos rfl] using tridiagonal_diagonal_entry_split N a t ha ht i
  · by_cases hright : i.val + 1 = j.val
    · simpa only [E, H, if_neg hij, if_pos hright, zero_add] using
        tridiagonal_neighbor_entry_split N a t i.val
    · by_cases hleft : j.val + 1 = i.val
      · simpa only [E, H, if_neg hij, if_neg hright, if_pos hleft, zero_add] using
          tridiagonal_neighbor_entry_split N a t j.val
      · simp [E, H, hij, hright, hleft]

theorem referenceWeight_mono_parameter {n m i : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m) (hi : 0 ≤ i) :
    referenceWeight n i ≤ referenceWeight m i := by
  have hn1 : 0 < n + 1 := by linarith
  have hm1 : 0 < m + 1 := by linarith
  have hnum : 0 ≤ 2 * i * (i + 1) := mul_nonneg (mul_nonneg (by norm_num) hi) (by linarith)
  unfold referenceWeight
  have hfrac : 2 * i * (i + 1) / (m + 1) ≤ 2 * i * (i + 1) / (n + 1) := by
    apply (div_le_div_iff₀ hm1 hn1).mpr
    exact mul_le_mul_of_nonneg_left (by linarith) hnum
  linarith

end
end CriticalExtrapolation.Paper
