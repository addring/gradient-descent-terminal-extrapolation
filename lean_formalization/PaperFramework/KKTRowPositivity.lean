import PaperFramework.KKTStrictOrder

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem kktSlopeMoment_le_slope (N : ℕ) (h c : ℝ) (β : Vec N)
    (hβ : Feasible h c β) (i : Fin N) : kktSlopeMoment h c β i ≤ slope h c β i := by
  by_cases hi : i.val = 0
  · exact (kktSlopeMoment_at_first N h c β i hi).le
  · let p : Fin N := ⟨i.val - 1, by omega⟩
    have hpi : p.val + 1 = i.val := by dsimp [p]; omega
    have hpiR : (p.val : ℝ) + 1 = i.val := by exact_mod_cast hpi
    rw [kktSlopeMoment_at_successor h c β p i hpi, hpiR]
    have hs := hβ.2.2 p i hpi
    have hm := mul_nonneg (Nat.cast_nonneg (α := ℝ) i.val) (sub_nonneg.mpr hs)
    nlinarith

/-- Positivity propagates from the first row. A nonpositive next row would
force an active slope constraint and contradict the adjacent KKT equation. -/
theorem kkt_row_moments_positive (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) : ∀ i, 0 < rowMoment h c β μ i := by
  have hδ := kkt_strict_differences N h c hp hh β μ ν hkkt
  have hν := kkt_difference_multipliers_zero N h c hp hh β μ ν hkkt
  have hf : scaledNu h c ν = 0 := by funext i; simp [scaledNu, hν i]
  have he := scaledMu_nonnegative N h c hp μ hkkt.mu_nonnegative
  have hfirst : 0 < rowMoment h c β μ ⟨0, hp.n_pos⟩ := by
    have hd := hδ ⟨0, hp.n_pos⟩
    have hm := he 0
    simpa [rowMoment, previousMu] using add_pos_of_pos_of_nonneg hd hm
  have hstep : ∀ i j : Fin N, i.val + 1 = j.val →
      0 < rowMoment h c β μ i → 0 < rowMoment h c β μ j := by
    intro i j hij hi
    by_contra hn
    have hj : rowMoment h c β μ j ≤ 0 := le_of_not_gt hn
    have hprev : previousMu h c μ j.val = scaledMu h c μ i.val := by
      rw [← hij, previousMu_succ]
    have hepos : 0 < scaledMu h c μ i.val := by
      have hd := mul_pos (by positivity : 0 < (j.val : ℝ) + 1) (hδ j)
      have hej := he j.val
      unfold rowMoment at hj
      rw [hprev] at hj
      linarith
    let k : Fin (N - 1) := ⟨i.val, by omega⟩
    have hleft : slopeLeft k = i := Fin.ext rfl
    have hright : slopeRight k = j := Fin.ext hij
    have hμ : μ k ≠ 0 := by
      intro hz
      unfold scaledMu at hepos
      rw [dif_pos k.isLt] at hepos
      change 0 < μ k / (2 * h * c * S N h c) at hepos
      rw [hz, zero_div] at hepos
      exact lt_irrefl 0 hepos
    have hs := (mul_eq_zero.mp (hkkt.slope_complementarity k)).resolve_left hμ
    rw [hleft, hright] at hs
    have heq := sub_eq_zero.mp hs
    have hijR : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij.symm
    have hUj : kktSlopeMoment h c β j = slope h c β i := by
      rw [kktSlopeMoment_at_successor h c β i j hij, ← heq, hijR]
      ring
    have hUi := kktSlopeMoment_le_slope N h c β hkkt.feasible i
    have hbalance := kkt_adjacent_balance N h c hp β μ ν hkkt i j hij
    rw [hf] at hbalance
    simp only [Pi.zero_apply, previousCoordinate, zeroExtend, dite_eq_ite,
      ite_self, sub_zero, mul_zero, zero_sub] at hbalance
    rw [hUj] at hbalance
    have hwi : 0 < kktRowWeight h c β μ i :=
      div_pos hi (queryK_positive N h c hp i)
    have hwj : kktRowWeight h c β μ j ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hj (queryK_positive N h c hp j).le
    have hm := mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr hh).le hwj
    linarith
  have hall : ∀ k (hk : k < N), 0 < rowMoment h c β μ ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact hfirst
    | succ k ih =>
      intro hk
      exact hstep ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl (ih (by omega))
  intro i
  exact hall i.val i.isLt

/-- Section 5: positivity precedes any construction of flow probabilities. -/
theorem row_moments_positive_normalized (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (β : Vec N) (hβ : IsOptimizer h c β)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν) :
    (∀ i, 0 < rowMoment h c β μ i) ∧ (∑ i, rowMoment h c β μ i) = 1 := by
  refine ⟨kkt_row_moments_positive N h c hp hh β μ ν hkkt, ?_⟩
  rw [row_moments_sum, hβ.1.1]

end
end CriticalExtrapolation.Paper
