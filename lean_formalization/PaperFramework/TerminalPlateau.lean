import PaperFramework.TerminalPlateauSums

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem feasible_slopes_antitone {N : ℕ} (h c : ℝ) (β : Vec N)
    (hβ : Feasible h c β) : Antitone (slope h c β) := by
  cases N with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    exact hβ.2.2 i.castSucc i.succ rfl

theorem terminal_slope_plateau_exists {N : ℕ} (h c : ℝ) (β : Vec N)
    (hβ : Feasible h c β) (b : Fin N) (hb : b.val + 1 = N) :
    ∃ a : Fin N, IsMaximalSlopePlateau h c β a b := by
  classical
  let s := Finset.univ.filter (fun i : Fin N => slope h c β i = slope h c β b)
  have hbmem : b ∈ s := by simp [s]
  have hs : s.Nonempty := ⟨b, hbmem⟩
  let a := s.min' hs
  have hamem : a ∈ s := Finset.min'_mem s hs
  have haeq : slope h c β a = slope h c β b := (Finset.mem_filter.mp hamem).2
  have hab : a ≤ b := Finset.min'_le s b hbmem
  have hmono := feasible_slopes_antitone h c β hβ
  refine ⟨a, hab, ?_, ?_, ?_⟩
  · intro i hai hib
    exact le_antisymm (hmono hai) (by rw [haeq]; exact hmono hib)
  · intro i hia
    have hia' : i < a := by change i.val < a.val; omega
    have hle : slope h c β a ≤ slope h c β i := hmono hia'.le
    apply lt_of_le_of_ne hle
    intro heq
    have himem : i ∈ s := by simp [s, ← haeq, heq]
    have hmin : a ≤ i := Finset.min'_le s i himem
    exact (not_le_of_gt hia') hmin
  · intro i hbi
    have hi := i.isLt
    omega

theorem queryK_ge_h (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (i : Fin N) :
    h ≤ queryK N h c i := by
  have hi : (i.val : ℝ) + 1 ≤ N := by exact_mod_cast i.isLt
  have hNc : (N : ℝ) ≤ (N : ℝ) * c := le_mul_of_one_le_right (Nat.cast_nonneg N) hp.c_ge_one
  unfold queryK
  nlinarith [mul_nonneg hp.h_pos.le (by linarith : 0 ≤ (N : ℝ) * c - i.val - 1)]

theorem terminal_potential_coefficient_bound (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (hsize : 1 ≤ (N : ℝ) * h ^ 2) (b : Fin N) :
    (queryK N h c b + (1 - h)) / h ≤ (N : ℝ) * queryK N h c b := by
  have hKb := queryK_ge_h N h c hp b
  have hr : 0 ≤ h - h ^ 2 := by nlinarith [hp.h_pos]
  have hNh : 0 ≤ (N : ℝ) * h - 1 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) hr]
  apply (div_le_iff₀ hp.h_pos).mpr
  nlinarith [mul_nonneg hNh (sub_nonneg.mpr hKb)]

/-- The terminal estimate follows already from the size condition and full KKT. -/
theorem terminal_plateau_endpoint_of_kkt (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (hsize : 1 ≤ (N : ℝ) * h ^ 2)
    (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν)
    (b : Fin N) (hb : b.val + 1 = N) : β b < rowMoment h c β μ b := by
  obtain ⟨a, hplateau⟩ := terminal_slope_plateau_exists h c β hkkt.feasible b hb
  have hlo := terminal_weighted_differences_lower N h c β hkkt.feasible a b hplateau.1 hb
  rw [← plateau_row_moments_sum h c β μ ν hkkt a b hplateau] at hlo
  have hhi := plateau_row_sum_strict_upper N h c hp hh β μ ν hkkt a b hplateau
  have hwb : 0 < kktRowWeight h c β μ b :=
    div_pos (kkt_row_moments_positive N h c hp hh β μ ν hkkt b) (queryK_positive N h c hp b)
  have hcoef := mul_le_mul_of_nonneg_right (terminal_potential_coefficient_bound N h c hp hh hsize b) hwb.le
  have hrow : rowMoment h c β μ b = queryK N h c b * kktRowWeight h c β μ b := by
    unfold kktRowWeight
    field_simp [ne_of_gt (queryK_positive N h c hp b)]
  have hproduct : (N : ℝ) * β b < (N : ℝ) * rowMoment h c β μ b := by
    rw [hrow]
    nlinarith
  exact (mul_lt_mul_iff_of_pos_left (by exact_mod_cast hp.n_pos : (0 : ℝ) < N)).mp hproduct

/-- Equation (5.5), preserving the original statement and its boundary cases. -/
theorem terminal_plateau_endpoint (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (hsize : 1 ≤ (N : ℝ) * h ^ 2) (hΦ : 0 ≤ auxiliaryValue N h c)
    (β : Vec N) (hβ : IsOptimizer h c β)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν)
    (b : Fin N) (hb : b.val + 1 = N) : β b < rowMoment h c β μ b :=
  terminal_plateau_endpoint_of_kkt N h c hp hh hsize β μ ν hkkt b hb

end
end CriticalExtrapolation.Paper
