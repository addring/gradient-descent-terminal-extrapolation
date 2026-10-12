import PaperFramework.TridiagonalStructure

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- (3.9) is restricted to the zero-sum subspace when c≠1. -/
theorem objective_energy_on_zero_sum (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (v : Vec N) (hsum : (∑ i, v i) = 0) :
    chainObjective h c v / (h ^ 2 * c) =
      homogeneousEnergy ((N : ℝ) * (c - 1)) (1 / h) v := by
  have hh : h ≠ 0 := ne_of_gt hp.h_pos
  have hc : c ≠ 0 := ne_of_gt (by linarith [hp.c_ge_one])
  have ha : 0 ≤ (N : ℝ) * (c - 1) := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hp.c_ge_one)
  have hslope : ∀ i : Fin N, slope h c v i =
      (tail v i.val - (1 / h) * v i) / energyD N ((N : ℝ) * (c - 1)) i.val := by
    intro i
    have htotal : (∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), v j) + tail v i.val = 0 := by
      have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => j < i) v
      simpa only [not_lt, Fin.le_def, tail, hsum] using hpart
    have hK : queryK N h c i = h * energyD N ((N : ℝ) * (c - 1)) i.val := by
      unfold queryK energyD
      ring
    have hT : applyT h c v i = h * tail v i.val - v i := by
      unfold applyT
      rw [hsum]
      rw [show tail v i.val = -(∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), v j) by
        linarith [htotal]]
      ring
    have hd := ne_of_gt (energyD_pos N ((N : ℝ) * (c - 1)) ha i)
    unfold slope
    rw [hK, hT]
    field_simp <;> ring
  have hterms : (∑ i, ((i.val : ℝ) + 1) * difference v i * slope h c v i) =
      ∑ i, ((i.val : ℝ) + 1) * difference v i * (tail v i.val - (1 / h) * v i) /
        energyD N ((N : ℝ) * (c - 1)) i.val := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hslope]
    ring
  have hS : 1 + (N : ℝ) * h * c = h * energyF N ((N : ℝ) * (c - 1)) (1 / h) := by
    unfold energyF
    field_simp
    ring
  unfold chainObjective homogeneousEnergy
  rw [hsum, hterms, hS]
  field_simp
  ring


theorem objective_energy_at_one (N : ℕ) (h : ℝ) (hp : Parameters N h 1) (v : Vec N) :
    chainObjective h 1 v / h ^ 2 = homogeneousEnergy 0 (1 / h) v := by
  have hh : h ≠ 0 := ne_of_gt hp.h_pos
  have hslope : ∀ i : Fin N, slope h 1 v i =
      (tail v i.val - (1 / h) * v i) / energyD N 0 i.val := by
    intro i
    have htotal : (∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), v j) + tail v i.val = ∑ j, v j := by
      simpa only [not_lt, Fin.le_def, tail] using
        Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => j < i) v
    have hK : queryK N h 1 i = h * energyD N 0 i.val := by
      unfold queryK energyD
      ring
    have hT : applyT h 1 v i = h * tail v i.val - v i := by
      unfold applyT
      rw [show (∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), v j) =
        (∑ j, v j) - tail v i.val by linarith [htotal]]
      ring
    have hd := ne_of_gt (energyD_pos N 0 (by norm_num) i)
    unfold slope
    rw [hK, hT]
    field_simp
  have hterms : (∑ i, ((i.val : ℝ) + 1) * difference v i * slope h 1 v i) =
      ∑ i, ((i.val : ℝ) + 1) * difference v i * (tail v i.val - (1 / h) * v i) /
        energyD N 0 i.val := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hslope]
    ring
  have hS : 1 + (N : ℝ) * h * 1 = h * energyF N 0 (1 / h) := by
    unfold energyF
    field_simp
    ring
  unfold chainObjective homogeneousEnergy
  rw [hterms, hS]
  field_simp

end
end CriticalExtrapolation.Paper

