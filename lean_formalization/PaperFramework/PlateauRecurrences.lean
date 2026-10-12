import PaperFramework.KKTRowPositivity

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem scaledMu_zero_of_strict_slope {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν)
    (i j : Fin N) (hij : i.val + 1 = j.val)
    (hs : slope h c β j < slope h c β i) : scaledMu h c μ i.val = 0 := by
  let k : Fin (N - 1) := ⟨i.val, by omega⟩
  have hleft : slopeLeft k = i := Fin.ext rfl
  have hright : slopeRight k = j := Fin.ext hij
  have hc := hkkt.slope_complementarity k
  rw [hleft, hright] at hc
  have hz := (mul_eq_zero.mp hc).resolve_right (ne_of_gt (sub_pos.mpr hs))
  unfold scaledMu
  rw [dif_pos k.isLt]
  change μ k / (2 * h * c * S N h c) = 0
  rw [hz, zero_div]

theorem plateau_boundary_multipliers {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν)
    (a b : Fin N) (hplateau : IsMaximalSlopePlateau h c β a b) :
    previousMu h c μ a.val = 0 ∧ scaledMu h c μ b.val = 0 := by
  constructor
  · by_cases ha : a.val = 0
    · simp [previousMu, ha]
    · let p : Fin N := ⟨a.val - 1, by omega⟩
      have hpa : p.val + 1 = a.val := by dsimp [p]; omega
      have hs := hplateau.2.2.1 p hpa
      rw [← hpa, previousMu_succ]
      exact scaledMu_zero_of_strict_slope h c β μ ν hkkt p a hpa hs
  · by_cases hb : b.val + 1 < N
    · let j : Fin N := ⟨b.val + 1, hb⟩
      exact scaledMu_zero_of_strict_slope h c β μ ν hkkt b j rfl
        (hplateau.2.2.2 j rfl)
    · simp [scaledMu, show ¬ b.val < N - 1 by omega]

theorem kkt_adjacent_reduced (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν)
    (i j : Fin N) (hij : i.val + 1 = j.val) :
    kktRowWeight h c β μ i - (1 - h) * kktRowWeight h c β μ j =
      kktSlopeMoment h c β i - kktSlopeMoment h c β j := by
  have hν := kkt_difference_multipliers_zero N h c hp hh β μ ν hkkt
  have hf : scaledNu h c ν = 0 := by funext k; simp [scaledNu, hν k]
  have hs := kkt_adjacent_balance N h c hp β μ ν hkkt i j hij
  rw [hf] at hs
  simp [previousCoordinate, zeroExtend] at hs
  linarith

theorem equal_slope_row_weight_step (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i j : Fin N) (hij : i.val + 1 = j.val)
    (hs : slope h c β i = slope h c β j) :
    kktRowWeight h c β μ i ≤ kktRowWeight h c β μ j := by
  have hjR : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij.symm
  have hUj : kktSlopeMoment h c β j = slope h c β i := by
    rw [kktSlopeMoment_at_successor h c β i j hij, ← hs, hjR]
    ring
  have hUi := kktSlopeMoment_le_slope N h c β hkkt.feasible i
  have hbal := kkt_adjacent_reduced N h c hp hh β μ ν hkkt i j hij
  rw [hUj] at hbal
  have hwj : 0 < kktRowWeight h c β μ j :=
    div_pos (kkt_row_moments_positive N h c hp hh β μ ν hkkt j)
      (queryK_positive N h c hp j)
  nlinarith [mul_pos hp.h_pos hwj]

theorem equal_slope_difference_step (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (hβ : Feasible h c β) (p i j : Fin N)
    (hpi : p.val + 1 = i.val) (hij : i.val + 1 = j.val)
    (hs : slope h c β p = slope h c β i) : difference β i ≤ difference β p := by
  have heq := slope_second_difference N h c hp β p i j hpi hij
  rw [hs, sub_self, mul_zero, zero_sub] at heq
  have hgap := mul_nonneg (queryK_positive N h c hp j).le
    (sub_nonneg.mpr (hβ.2.2 i j hij))
  have hδ := mul_nonneg hp.h_pos.le (hβ.2.1 p)
  nlinarith

/-- Three equal consecutive slopes give the geometric difference recurrence. -/
theorem plateau_difference_recurrence (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (p i j : Fin N) (hpi : p.val + 1 = i.val) (hij : i.val + 1 = j.val)
    (hpiSlope : slope h c β p = slope h c β i)
    (hijSlope : slope h c β i = slope h c β j) :
    difference β i = (1 - h) * difference β p := by
  have heq := slope_second_difference N h c hp β p i j hpi hij
  rw [hpiSlope, hijSlope] at heq
  simp only [sub_self, mul_zero, sub_zero] at heq
  linarith

end
end CriticalExtrapolation.Paper
