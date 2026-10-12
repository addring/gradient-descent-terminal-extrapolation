import PaperFramework.KKTCoordinates

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem slope_second_difference (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (p i j : Fin N) (hpi : p.val + 1 = i.val) (hij : i.val + 1 = j.val) :
    queryK N h c p * (slope h c β p - slope h c β i) -
      queryK N h c j * (slope h c β i - slope h c β j) =
        difference β i - (1 - h) * difference β p := by
  have hpK := ne_of_gt (queryK_positive N h c hp p)
  have hiK := ne_of_gt (queryK_positive N h c hp i)
  have hjK := ne_of_gt (queryK_positive N h c hp j)
  have hTpi := applyT_adjacent h c β p i hpi
  have hTij := applyT_adjacent h c β i j hij
  have hKpi := queryK_adjacent h c p i hpi
  have hKij := queryK_adjacent h c i j hij
  have hd := difference_adjacent β p i hpi
  unfold slope
  field_simp
  rw [hTij]
  simp_rw [hTpi, hKij, hKpi, hd]
  ring

theorem slope_gap_increases_at_flat (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (hβ : Feasible h c β)
    (p i j : Fin N) (hpi : p.val + 1 = i.val) (hij : i.val + 1 = j.val)
    (hd : difference β i = 0) :
    slope h c β p - slope h c β i < slope h c β i - slope h c β j := by
  have hs := slope_second_difference N h c hp β p i j hpi hij
  rw [hd, zero_sub] at hs
  have hgap := sub_pos.mpr (slope_strict_of_zero_difference N h c hp hh β hβ i j hij hd)
  have hKpi := queryK_adjacent h c p i hpi
  have hKij := queryK_adjacent h c i j hij
  have hKp := queryK_positive N h c hp p
  have hδ := mul_nonneg (sub_pos.mpr hh).le (hβ.2.1 p)
  have hdiff : 0 < (queryK N h c p - queryK N h c j) *
      (slope h c β i - slope h c β j) :=
    mul_pos (by linarith [hp.h_pos]) hgap
  nlinarith

theorem kktSlopeMoment_at_first (N : ℕ) (h c : ℝ) (β : Vec N)
    (i : Fin N) (hi : i.val = 0) : kktSlopeMoment h c β i = slope h c β i := by
  simp [kktSlopeMoment, backwardDifference, previousCoordinate, hi]

theorem kktSlopeMoment_at_successor {N : ℕ} (h c : ℝ) (β : Vec N)
    (i j : Fin N) (hij : i.val + 1 = j.val) :
    kktSlopeMoment h c β j = ((j.val : ℝ) + 1) * slope h c β j -
      ((i.val : ℝ) + 1) * slope h c β i := by
  unfold kktSlopeMoment backwardDifference
  rw [← hij, previousCoordinate_succ]
  simp only [hij]

theorem kktSlopeMoment_drop_at_flat (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (hβ : Feasible h c β)
    (i j : Fin N) (hij : i.val + 1 = j.val) (hd : difference β i = 0) :
    kktSlopeMoment h c β j < kktSlopeMoment h c β i := by
  have hgap := slope_strict_of_zero_difference N h c hp hh β hβ i j hij hd
  have hijR : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij.symm
  rw [kktSlopeMoment_at_successor h c β i j hij, hijR]
  by_cases hi : i.val = 0
  · rw [kktSlopeMoment_at_first N h c β i hi, hi]
    norm_num
    linarith
  · let p : Fin N := ⟨i.val - 1, by omega⟩
    have hpi : p.val + 1 = i.val := by dsimp [p]; omega
    have hpiR : (p.val : ℝ) + 1 = i.val := by exact_mod_cast hpi
    have hinc := slope_gap_increases_at_flat N h c hp hh β hβ p i j hpi hij hd
    rw [kktSlopeMoment_at_successor h c β p i hpi, hpiR]
    have hm := mul_nonneg (Nat.cast_nonneg (α := ℝ) i.val) (sub_nonneg.mpr (le_of_lt hinc))
    nlinarith

end
end CriticalExtrapolation.Paper
