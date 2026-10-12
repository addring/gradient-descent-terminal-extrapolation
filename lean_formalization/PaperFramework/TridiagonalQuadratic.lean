import PaperFramework.Definitions

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem sum_fin_value_selector {N : ℕ} (v : Vec N) (k : ℕ) :
    (∑ j : Fin N, if k = j.val then v j else 0) = zeroExtend v k := by
  by_cases hk : k < N
  · have hpred : ∀ j : Fin N, (k = j.val) ↔ j = ⟨k, hk⟩ := by
      intro j
      constructor
      · intro hj
        exact Fin.ext hj.symm
      · intro hj
        exact (congrArg Fin.val hj).symm
    simp_rw [hpred]
    simp [zeroExtend, hk]
  · have hpred : ∀ j : Fin N, k ≠ j.val := by
      intro j hj
      have hjN := j.isLt
      omega
    simp [hpred, zeroExtend, hk]

theorem energy_matrix_entries_add (N : ℕ) (a t : ℝ) (i j : Fin N) :
    E N a t i j = (if i = j then energyDiagonal N a t i.val else 0) +
      (if i.val + 1 = j.val then energyNeighbor N a t i.val else 0) +
      (if j.val + 1 = i.val then energyNeighbor N a t j.val else 0) := by
  by_cases hij : i = j
  · subst j
    simp [E]
  · by_cases hr : i.val + 1 = j.val
    · have hl : ¬j.val + 1 = i.val := by omega
      simp [E, hij, hr, hl]
    · by_cases hl : j.val + 1 = i.val
      · simp [E, hij, hr, hl]
      · simp [E, hij, hr, hl]

theorem right_neighbor_sum {N : ℕ} (b u : Vec N) (i : Fin N) :
    (∑ j : Fin N, (if i.val + 1 = j.val then b i else 0) * u i * u j) =
      b i * u i * zeroExtend u (i.val + 1) := by
  calc
    _ = ∑ j : Fin N, if i.val + 1 = j.val then b i * u i * u j else 0 := by
      simp_rw [ite_mul, zero_mul]
    _ = zeroExtend (fun j => b i * u i * u j) (i.val + 1) := sum_fin_value_selector _ _
    _ = _ := by
      by_cases hk : i.val + 1 < N <;> simp [zeroExtend, hk]

/-- The virtual last neighbor is zero; no extra matrix entry is introduced. -/
theorem energy_quadratic_neighbors (N : ℕ) (a t : ℝ) (u : Vec N) :
    quadraticForm (E N a t) u =
      (∑ i, energyDiagonal N a t i.val * (u i) ^ 2) +
        2 * ∑ i, energyNeighbor N a t i.val * u i * zeroExtend u (i.val + 1) := by
  have hdiag : (∑ i, ∑ j, (if i = j then energyDiagonal N a t i.val else 0) * u i * u j) =
      ∑ i, energyDiagonal N a t i.val * (u i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp [ite_mul, pow_two, mul_assoc]
  have hleft : (∑ i, ∑ j, (if j.val + 1 = i.val then energyNeighbor N a t j.val else 0) * u i * u j) =
      ∑ i, ∑ j, (if i.val + 1 = j.val then energyNeighbor N a t i.val else 0) * u i * u j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hright : (∑ i, ∑ j, (if i.val + 1 = j.val then energyNeighbor N a t i.val else 0) * u i * u j) =
      ∑ i, energyNeighbor N a t i.val * u i * zeroExtend u (i.val + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    exact right_neighbor_sum (fun j => energyNeighbor N a t j.val) u i
  unfold quadraticForm
  simp_rw [energy_matrix_entries_add, add_mul, Finset.sum_add_distrib]
  rw [hdiag, hleft, hright]
  ring

end
end CriticalExtrapolation.Paper
