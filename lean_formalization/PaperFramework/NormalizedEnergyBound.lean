import PaperFramework.EnergyIdentity
import PaperFramework.CorrectionMatrix

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem referenceReciprocalSum_positive (N : ℕ) (hN : 0 < N) : 0 < referenceReciprocalSum N := by
  unfold referenceReciprocalSum
  apply Finset.sum_pos'
  · intro i hi
    exact (one_div_pos.mpr (referenceWeight_pos
      (by exact_mod_cast hN) (Nat.cast_nonneg i)
      (by exact_mod_cast Finset.mem_range.mp hi))).le
  · refine ⟨0, Finset.mem_range.mpr hN, ?_⟩
    simp [referenceWeight]

/-- Weighted Cauchy--Schwarz applies on the full normalized real space. -/
theorem full_space_energy_lower_bound (N : ℕ) (a t : ℝ)
    (hN : 0 < N) (ha : 0 ≤ a) (ht : 1 ≤ t)
    (p : Vec N) (hpsum : (∑ i, p i) = 1) :
    1 / referenceReciprocalSum N ≤ homogeneousEnergy a t p := by
  have hid := tridiagonal_energy_identity N a t hN ha ht p
  have hdom := energy_matrix_domination N a t hN ha ht (tailU a t p)
  have hsum := (tail_transform_recovery N a t hN ha ht p).2
  have hF := energyF_pos N a t ha ht
  have he : ∀ i : Fin N, 0 < referenceWeight (N : ℝ) (i.val : ℝ) := by
    intro i
    exact referenceWeight_pos (by exact_mod_cast hN) (Nat.cast_nonneg i.val)
      (by exact_mod_cast i.isLt)
  have hRsum : (∑ i : Fin N, 1 / referenceWeight (N : ℝ) (i.val : ℝ)) = referenceReciprocalSum N :=
    Fin.sum_univ_eq_sum_range (fun i => 1 / referenceWeight (N : ℝ) (i : ℝ)) N
  have hnorm : (∑ i, tailU a t p i) = 1 / energyF N a t := by
    apply (eq_div_iff (ne_of_gt hF)).mpr
    rw [hpsum] at hsum
    simpa only [mul_comm] using hsum.symm
  have hR : 0 < ∑ i : Fin N, 1 / referenceWeight (N : ℝ) (i.val : ℝ) := by
    rw [hRsum]
    exact referenceReciprocalSum_positive N hN
  have hbound := normalized_energy_lower_bound (fun i : Fin N => referenceWeight (N : ℝ) (i.val : ℝ))
    (tailU a t p) (energyF N a t) he (ne_of_gt hF) hnorm hR
  rw [hRsum] at hbound
  rw [hid]
  exact hbound.trans (mul_le_mul_of_nonneg_left hdom (sq_nonneg _))

end
end CriticalExtrapolation.Paper
