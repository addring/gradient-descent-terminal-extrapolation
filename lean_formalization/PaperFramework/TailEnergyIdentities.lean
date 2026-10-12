import PaperFramework.TridiagonalStructure

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem zeroExtend_at {N : ℕ} (u : Vec N) (i : Fin N) : zeroExtend u i.val = u i := by
  simp [zeroExtend, i.isLt]

theorem tail_after_terminal {N : ℕ} (u : Vec N) (k : ℕ) (hk : N ≤ k) : tail u k = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have h := (Finset.mem_filter.mp hi).2
  omega

theorem tail_step_natural {N : ℕ} (u : Vec N) (k : ℕ) :
    tail u k = zeroExtend u k + tail u (k + 1) := by
  by_cases hk : k < N
  · simpa only [zeroExtend, dif_pos hk] using tail_step u ⟨k, hk⟩
  · rw [tail_after_terminal u k (by omega), tail_after_terminal u (k + 1) (by omega)]
    simp [zeroExtend, hk]

theorem sum_fin_natural_differences (N : ℕ) (z : ℕ → ℝ) :
    (∑ i : Fin N, (z i.val - z (i.val + 1))) = z 0 - z N := by
  rw [Fin.sum_univ_eq_sum_range (fun k => z k - z (k + 1)) N]
  exact sum_differences z N

theorem tail_transform_coordinate (N : ℕ) (a t : ℝ)
    (hN : 0 < N) (ha : 0 ≤ a) (ht : 1 ≤ t) (p : Vec N) (i : Fin N) :
    p i = energyZeta N a t i.val * tailU a t p i + tail (tailU a t p) (i.val + 1) := by
  have hsets : Finset.univ.filter (fun j : Fin N => i < j) =
      Finset.univ.filter (fun j : Fin N => i.val + 1 ≤ j.val) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    omega
  simpa only [hsets, tail] using (tail_transform_recovery N a t hN ha ht p).1 i

theorem tail_transform_coordinate_extended (N : ℕ) (a t : ℝ)
    (hN : 0 < N) (ha : 0 ≤ a) (ht : 1 ≤ t) (p : Vec N) (k : ℕ) (hk : k ≤ N) :
    zeroExtend p k = energyZeta N a t k * zeroExtend (tailU a t p) k +
      tail (tailU a t p) (k + 1) := by
  by_cases hk' : k < N
  · simpa only [zeroExtend, dif_pos hk'] using tail_transform_coordinate N a t hN ha ht p ⟨k, hk'⟩
  · have heq : k = N := by omega
    subst k
    simp [zeroExtend, tail_after_terminal _ _ (Nat.le_succ N)]

theorem tail_transform_difference (N : ℕ) (a t : ℝ)
    (hN : 0 < N) (ha : 0 ≤ a) (ht : 1 ≤ t) (p : Vec N) (i : Fin N) :
    difference p i = energyZeta N a t i.val * tailU a t p i -
      (energyZeta N a t i.val - 2) * zeroExtend (tailU a t p) (i.val + 1) := by
  have hnext := tail_transform_coordinate_extended N a t hN ha ht p (i.val + 1) (by omega)
  have hz : energyZeta N a t (i.val + 1) = energyZeta N a t i.val - 1 := by
    simp only [energyZeta, Nat.cast_add, Nat.cast_one]
    ring
  unfold difference
  rw [tail_transform_coordinate N a t hN ha ht p i, hnext, hz,
    tail_step_natural (tailU a t p) (i.val + 1)]
  ring

theorem tail_ratio_eq_transformed_tail (N : ℕ) (a t : ℝ) (p : Vec N) (i : Fin N) :
    tail p i.val / energyZeta N a t i.val = tail (tailU a t p) i.val :=
  (sum_tailU_from N a t p i.val (by omega)).symm

theorem energy_factor_transformed (N : ℕ) (a t : ℝ)
    (hN : 0 < N) (ha : 0 ≤ a) (ht : 1 ≤ t) (p : Vec N) (i : Fin N) :
    (tail p i.val - t * p i) / energyD N a i.val =
      tail (tailU a t p) i.val -
        t * (energyZeta N a t i.val - 1) / energyD N a i.val * tailU a t p i := by
  have htail : tail p i.val = energyZeta N a t i.val * tail (tailU a t p) i.val := by
    rw [← tail_ratio_eq_transformed_tail]
    exact (mul_div_cancel₀ _ (ne_of_gt (energyZeta_pos N a t ha ht i.val (by omega)))).symm
  have hcoord : p i = (energyZeta N a t i.val - 1) * tailU a t p i +
      tail (tailU a t p) i.val := by
    rw [tail_transform_coordinate N a t hN ha ht p i, tail_step (tailU a t p) i]
    ring
  have hd := ne_of_gt (energyD_pos N a ha i)
  rw [htail, hcoord, energyZeta_eq_D_add]
  field_simp
  ring

theorem sum_mul_tail_finite {N : ℕ} (u : Vec N) :
    2 * (∑ i, u i * tail u i.val) = (∑ i, u i) ^ 2 + ∑ i, (u i) ^ 2 := by
  have hpoint : ∀ i : Fin N, 2 * (u i * tail u i.val) =
      ((tail u i.val) ^ 2 - (tail u (i.val + 1)) ^ 2) + (u i) ^ 2 := by
    intro i
    rw [tail_step u i]
    ring
  calc
    _ = ∑ i, (((tail u i.val) ^ 2 - (tail u (i.val + 1)) ^ 2) + (u i) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => hpoint i)
    _ = _ := by
      rw [Finset.sum_add_distrib, sum_fin_natural_differences N (fun k => (tail u k) ^ 2)]
      simp [tail_zero, tail_terminal]

/-- Summation by parts with a vanishing terminal flux. -/
theorem weighted_difference_tail_identity (N : ℕ) (a t : ℝ)
    (hN : 0 < N) (ha : 0 ≤ a) (ht : 1 ≤ t) (p : Vec N) :
    (∑ i, ((i.val : ℝ) + 1) * difference p i * tail (tailU a t p) i.val) =
      energyF N a t * (∑ i, tailU a t p i * tail (tailU a t p) i.val) -
        ∑ i, ((i.val : ℝ) + 1) * (energyZeta N a t i.val - 2) *
          tailU a t p i * zeroExtend (tailU a t p) (i.val + 1) := by
  let u := tailU a t p
  let b : ℕ → ℝ := fun k => (k : ℝ) * (energyZeta N a t k - 1) * zeroExtend u k * tail u k
  have hb : (∑ i : Fin N, (b i.val - b (i.val + 1))) = 0 := by
    rw [sum_fin_natural_differences]
    simp [b, tail_terminal]
  have hpoint : ∀ i : Fin N,
      ((i.val : ℝ) + 1) * difference p i * tail u i.val =
        energyF N a t * (u i * tail u i.val) -
          ((i.val : ℝ) + 1) * (energyZeta N a t i.val - 2) * u i * zeroExtend u (i.val + 1) +
          (b i.val - b (i.val + 1)) := by
    intro i
    rw [tail_transform_difference N a t hN ha ht p i]
    change ((i.val : ℝ) + 1) * (energyZeta N a t i.val * u i -
      (energyZeta N a t i.val - 2) * zeroExtend u (i.val + 1)) * tail u i.val = _
    simp only [b, zeroExtend_at, energyZeta, Nat.cast_add, Nat.cast_one]
    rw [tail_step u i]
    ring
  calc
    _ = ∑ i, (energyF N a t * (u i * tail u i.val) -
        ((i.val : ℝ) + 1) * (energyZeta N a t i.val - 2) * u i * zeroExtend u (i.val + 1) +
          (b i.val - b (i.val + 1))) := Finset.sum_congr rfl (fun i _ => hpoint i)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hb, add_zero]

end
end CriticalExtrapolation.Paper
