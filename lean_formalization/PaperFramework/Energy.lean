import PaperFramework.CorrectionMatrix
import PaperFramework.ObjectiveEnergy
import PaperFramework.EnergyIdentity
import PaperFramework.ChainMatrix

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem homogeneousEnergy_positive (N : ℕ) (a t : ℝ)
    (hN : 0 < N) (ha : 0 ≤ a) (ht : 1 ≤ t) (p : Vec N) (hp : p ≠ 0) :
    0 < homogeneousEnergy a t p := by
  have hid := tridiagonal_energy_identity N a t hN ha ht p
  have hbound := energy_matrix_domination N a t hN ha ht (tailU a t p)
  have hinjective := tail_transform_injective N a t hN ha ht
  have hu : tailU a t p ≠ 0 := by
    intro hz
    apply hp
    apply hinjective
    rw [hz, tailU_zero]
  have hex : ∃ i, tailU a t p i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (funext h)
  obtain ⟨i, hi⟩ := hex
  have hweights : ∀ j : Fin N, 0 < referenceWeight (N : ℝ) (j.val : ℝ) := by
    intro j
    apply referenceWeight_pos
    · exact_mod_cast Nat.succ_le_of_lt hN
    · exact Nat.cast_nonneg _
    · exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hdiag : 0 < ∑ j, referenceWeight (N : ℝ) (j.val : ℝ) * (tailU a t p j) ^ 2 := by
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (hweights j).le (sq_nonneg _)
    · exact ⟨i, Finset.mem_univ _, mul_pos (hweights i) (sq_pos_of_ne_zero hi)⟩
  rw [hid]
  exact mul_pos (sq_pos_of_pos (energyF_pos N a t ha ht)) (hdiag.trans_le hbound)

theorem objective_positive_on_zero_sum (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (v : Vec N) (hsum : (∑ i, v i) = 0) (hv : v ≠ 0) :
    0 < chainObjective h c v := by
  have hid := objective_energy_on_zero_sum N h c hp v hsum
  have ha : 0 ≤ (N : ℝ) * (c - 1) :=
    mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hp.c_ge_one)
  have ht : 1 ≤ 1 / h := (le_div_iff₀ hp.h_pos).mpr (by simpa using hp.h_le_one)
  have he := homogeneousEnergy_positive N ((N : ℝ) * (c - 1)) (1 / h)
    hp.n_pos ha ht v hv
  have hden : 0 < h ^ 2 * c := mul_pos (sq_pos_of_pos hp.h_pos) (by linarith [hp.c_ge_one])
  have hq : 0 < chainObjective h c v / (h ^ 2 * c) := by rw [hid]; exact he
  have hprod := mul_pos hq hden
  rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at hprod

/-- At c=1 the identity and positivity hold without a zero-sum restriction. -/
theorem chain_at_one_positive (N : ℕ) (h : ℝ)
    (hp : Parameters N h 1) : PositiveQuadratic (M₀ N h 1) := by
  have ht : 1 ≤ 1 / h := (le_div_iff₀ hp.h_pos).mpr (by simpa using hp.h_le_one)
  have he := homogeneousEnergy_positive N 0 (1 / h) hp.n_pos (by norm_num) ht
  intro v hv
  have hq : 0 < chainObjective h 1 v / h ^ 2 := by
    rw [objective_energy_at_one N h hp v]
    exact he v hv
  have hprod := mul_pos hq (sq_pos_of_pos hp.h_pos)
  rw [div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hp.h_pos))] at hprod
  rw [← chainObjective_matrix N h 1 hp v]
  exact hprod

end
end CriticalExtrapolation.Paper

