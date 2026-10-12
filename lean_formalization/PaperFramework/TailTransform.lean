import PaperFramework.Definitions
import Mathlib.Algebra.BigOperators.Intervals

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem sum_fin_suffix_eq_Ico (N k : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ i.val), f i.val) =
      ∑ i ∈ Finset.Ico k N, f i := by
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hi).2, i.isLt⟩
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro i hi
    refine ⟨⟨i, (Finset.mem_Ico.mp hi).2⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_Ico.mp hi).1⟩
  · intro i hi
    rfl

theorem tail_zero {N : ℕ} (p : Vec N) : tail p 0 = ∑ i, p i := by
  simp [tail]

theorem tail_terminal {N : ℕ} (p : Vec N) : tail p N = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have h := (Finset.mem_filter.mp hi).2
  omega

theorem tail_step {N : ℕ} (p : Vec N) (i : Fin N) :
    tail p i.val = p i + tail p (i.val + 1) := by
  have hsets : Finset.univ.filter (fun j : Fin N => i.val ≤ j.val) =
      insert i (Finset.univ.filter (fun j : Fin N => i.val + 1 ≤ j.val)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases hij : j = i
      · exact Or.inl hij
      · exact Or.inr (by have : j.val ≠ i.val := fun h => hij (Fin.ext h); omega)
    · rintro (rfl | h) <;> omega
  unfold tail
  rw [hsets, Finset.sum_insert]
  simp

theorem energyZeta_pos (N : ℕ) (a t : ℝ) (ha : 0 ≤ a) (ht : 1 ≤ t)
    (k : ℕ) (hk : k ≤ N) : 0 < energyZeta N a t k := by
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  unfold energyZeta energyF
  linarith

theorem sum_tailU_from (N : ℕ) (a t : ℝ) (p : Vec N) (k : ℕ) (hk : k ≤ N) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ i.val), tailU a t p i) =
      tail p k / energyZeta N a t k := by
  let z : ℕ → ℝ := fun j => tail p j / energyZeta N a t j
  change (∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ i.val),
    (z i.val - z (i.val + 1))) = z k
  rw [sum_fin_suffix_eq_Ico N k (fun j => z j - z (j + 1)), Finset.sum_Ico_eq_sub _ hk,
    sum_differences, sum_differences]
  have hz : z N = 0 := by simp [z, tail_terminal]
  rw [hz]
  ring

/-- Equation (3.3), with only the genuine output zero boundary. -/
theorem tail_transform_recovery (N : ℕ) (a t : ℝ) (hN : 0 < N) (ha : 0 ≤ a) (ht : 1 ≤ t)
    (p : Vec N) :
    (∀ i, p i = energyZeta N a t i.val * tailU a t p i +
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j), tailU a t p j) ∧
    (∑ i, p i) = energyF N a t * ∑ i, tailU a t p i := by
  constructor
  · intro i
    have hsets : Finset.univ.filter (fun j : Fin N => i < j) =
        Finset.univ.filter (fun j : Fin N => i.val + 1 ≤ j.val) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
      omega
    rw [hsets, sum_tailU_from N a t p (i.val + 1) (by omega)]
    have hz₀ := ne_of_gt (energyZeta_pos N a t ha ht i.val (by omega))
    have hz₁ := ne_of_gt (energyZeta_pos N a t ha ht (i.val + 1) (by omega))
    have hstep := tail_step p i
    have hzeta : energyZeta N a t (i.val + 1) = energyZeta N a t i.val - 1 := by
      simp only [energyZeta, Nat.cast_add, Nat.cast_one]
      ring
    change p i = energyZeta N a t i.val *
      (tail p i.val / energyZeta N a t i.val -
        tail p (i.val + 1) / energyZeta N a t (i.val + 1)) +
      tail p (i.val + 1) / energyZeta N a t (i.val + 1)
    field_simp
    rw [hstep, hzeta]
    ring
  · have hsum := sum_tailU_from N a t p 0 (Nat.zero_le N)
    simp only [Nat.zero_le, Finset.filter_true, tail_zero, energyZeta, Nat.cast_zero, sub_zero] at hsum
    rw [hsum, mul_div_cancel₀]
    exact ne_of_gt (by simpa [energyZeta] using energyZeta_pos N a t ha ht 0 (Nat.zero_le N))

theorem tail_transform_injective (N : ℕ) (a t : ℝ) (hN : 0 < N) (ha : 0 ≤ a) (ht : 1 ≤ t) :
    Function.Injective (tailU (N := N) a t) := by
  intro p q hpq
  funext i
  rw [(tail_transform_recovery N a t hN ha ht p).1 i,
    (tail_transform_recovery N a t hN ha ht q).1 i, hpq]

theorem tailU_zero (N : ℕ) (a t : ℝ) : tailU (N := N) a t 0 = 0 := by
  funext i
  simp [tailU, tailZ, tail]

end
end CriticalExtrapolation.Paper
