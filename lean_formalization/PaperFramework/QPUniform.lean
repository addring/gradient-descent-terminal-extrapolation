import PaperFramework.QPGeometry
import Mathlib.Order.Interval.Finset.Fin

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def uniformDirection (N : ℕ) : Vec N := fun _ => 1 / (N : ℝ)
def descendingMass (N : ℕ) : ℝ := ∑ i : Fin N, ((N : ℝ) - (i.val : ℝ))
def descendingDirection (N : ℕ) : Vec N := fun i =>
  ((N : ℝ) - (i.val : ℝ)) / descendingMass N

theorem queryK_positive (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (i : Fin N) :
    0 < queryK N h c i := by
  have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
  have hNc : (N : ℝ) ≤ (N : ℝ) * c := le_mul_of_one_le_right (Nat.cast_nonneg N) hp.c_ge_one
  exact mul_pos hp.h_pos (by linarith)

theorem uniform_normalized (N : ℕ) (hN : 0 < N) : (∑ i, uniformDirection N i) = 1 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp [uniformDirection, hNr]

theorem uniform_prefix (N : ℕ) (i : Fin N) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), uniformDirection N j) =
      (i.val : ℝ) / N := by
  simp [uniformDirection, Finset.filter_gt_eq_Iio, Fin.card_Iio, div_eq_mul_inv]

theorem uniform_slope (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (i : Fin N) :
    slope h c (uniformDirection N) i = 1 / (N : ℝ) - 1 / ((N : ℝ) * queryK N h c i) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp.n_pos
  have hK := ne_of_gt (queryK_positive N h c hp i)
  unfold slope applyT
  rw [uniform_normalized N hp.n_pos, uniform_prefix]
  unfold uniformDirection
  field_simp
  unfold queryK
  ring

theorem uniform_slopes_strict (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (i j : Fin N) (hij : i.val + 1 = j.val) :
    slope h c (uniformDirection N) j < slope h c (uniformDirection N) i := by
  have hN : (0 : ℝ) < N := by exact_mod_cast hp.n_pos
  have hijr : (i.val : ℝ) < j.val := by exact_mod_cast (show i.val < j.val by omega)
  have hK : queryK N h c j < queryK N h c i := by
    unfold queryK
    exact mul_lt_mul_of_pos_left (sub_lt_sub_left hijr _) hp.h_pos
  have hinv := one_div_lt_one_div_of_lt (mul_pos hN (queryK_positive N h c hp j))
    (mul_lt_mul_of_pos_left hK hN)
  rw [uniform_slope N h c hp j, uniform_slope N h c hp i]
  linarith

theorem uniform_difference_nonnegative (N : ℕ) (hN : 0 < N) (i : Fin N) :
    0 ≤ difference (uniformDirection N) i := by
  unfold difference uniformDirection zeroExtend
  split_ifs
  · simp
  · simp only [sub_zero]
    exact (one_div_pos.mpr (by exact_mod_cast hN)).le

theorem uniform_feasible (N : ℕ) (h c : ℝ) (hp : Parameters N h c) :
    Feasible h c (uniformDirection N) :=
  ⟨uniform_normalized N hp.n_pos, uniform_difference_nonnegative N hp.n_pos,
    fun i j hij => (uniform_slopes_strict N h c hp i j hij).le⟩

theorem descendingMass_positive (N : ℕ) (hN : 0 < N) : 0 < descendingMass N := by
  apply Finset.sum_pos'
  · intro i _
    have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
    linarith
  · refine ⟨⟨0, hN⟩, Finset.mem_univ _, ?_⟩
    simpa using (show (0 : ℝ) < N by exact_mod_cast hN)

theorem descending_normalized (N : ℕ) (hN : 0 < N) :
    (∑ i, descendingDirection N i) = 1 := by
  unfold descendingDirection
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (descendingMass_positive N hN))

theorem descending_difference (N : ℕ) (i : Fin N) :
    difference (descendingDirection N) i = 1 / descendingMass N := by
  unfold difference descendingDirection zeroExtend
  split_ifs with hn
  · simp only [Nat.cast_add, Nat.cast_one]
    ring
  · have hi : (N : ℝ) - (i.val : ℝ) = 1 := by
      have hn' : N = i.val + 1 := by omega
      have hnR : (N : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hn'
      linarith
    simp only [sub_zero, hi]

end
end CriticalExtrapolation.Paper
