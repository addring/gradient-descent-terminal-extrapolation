import PaperFramework.SlopeCurvature
import PaperFramework.RowMomentNormalization

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem kkt_multiplier_scale_positive (N : ℕ) (h c : ℝ) (hp : Parameters N h c) :
    0 < 2 * h * c * S N h c := by
  have hh := hp.h_pos
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hp.c_ge_one
  unfold S
  positivity

theorem scaledMu_nonnegative (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (μ : Fin (N - 1) → ℝ) (hμ : ∀ k, 0 ≤ μ k) (i : ℕ) :
    0 ≤ scaledMu h c μ i := by
  unfold scaledMu
  split_ifs
  · exact div_nonneg (hμ _) (kkt_multiplier_scale_positive N h c hp).le
  · exact le_rfl

theorem kkt_weights_at_flat (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i j : Fin N)
    (hij : i.val + 1 = j.val) (hd : difference β i = 0) :
    kktRowWeight h c β μ i ≤ 0 ∧ 0 ≤ kktRowWeight h c β μ j := by
  let k : Fin (N - 1) := ⟨i.val, by omega⟩
  have hleft : slopeLeft k = i := Fin.ext rfl
  have hright : slopeRight k = j := Fin.ext hij
  have heq : β (slopeLeft k) = β (slopeRight k) := by
    rw [hleft, hright]
    rw [difference_adjacent β i j hij] at hd
    exact sub_eq_zero.mp hd
  have hμ := slope_multiplier_zero_of_equal_coordinates N h c hp hh β μ ν hkkt k heq
  have he : scaledMu h c μ i.val = 0 := by
    unfold scaledMu
    rw [dif_pos k.isLt]
    change μ k / (2 * h * c * S N h c) = 0
    rw [hμ, zero_div]
  have hprev : 0 ≤ previousMu h c μ i.val := by
    unfold previousMu
    split_ifs
    · exact le_rfl
    · exact scaledMu_nonnegative N h c hp μ hkkt.mu_nonnegative _
  have hprevj : previousMu h c μ j.val = 0 := by
    rw [← hij, previousMu_succ, he]
  constructor
  · unfold kktRowWeight rowMoment
    rw [hd, he]
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · exact (queryK_positive N h c hp i).le
  · unfold kktRowWeight rowMoment
    rw [hprevj, sub_zero]
    apply div_nonneg
    · exact add_nonneg (mul_nonneg (by positivity) (hkkt.feasible.2.1 j))
        (scaledMu_nonnegative N h c hp μ hkkt.mu_nonnegative _)
    · exact (queryK_positive N h c hp j).le

theorem kkt_flat_curvature_negative (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i j : Fin N)
    (hij : i.val + 1 = j.val) (hd : difference β i = 0) :
    2 * scaledNu h c ν i - previousCoordinate (scaledNu h c ν) i.val - scaledNu h c ν j < 0 := by
  have hb := kkt_adjacent_balance N h c hp β μ ν hkkt i j hij
  have hw := kkt_weights_at_flat N h c hp hh β μ ν hkkt i j hij hd
  have hU := kktSlopeMoment_drop_at_flat N h c hp hh β hkkt.feasible i j hij hd
  have hm := mul_nonneg (sub_pos.mpr hh).le hw.2
  linarith [hw.1]

/-- A maximum principle on the support of a nonnegative sequence. -/
theorem zero_of_strict_curvature_on_support (N : ℕ) (hN : 0 < N) (f : Vec N)
    (hf : ∀ i, 0 ≤ f i) (hterminal : ∀ b : Fin N, b.val + 1 = N → f b = 0)
    (hcurv : ∀ i j : Fin N, i.val + 1 = j.val → 0 < f i →
      2 * f i - previousCoordinate f i.val - f j < 0) : ∀ i, f i = 0 := by
  classical
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ f
    ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hzero : f i = 0 := by
    by_contra hne
    have hpos : 0 < f i := lt_of_le_of_ne (hf i) (Ne.symm hne)
    have hi : i.val + 1 < N := by
      by_contra hn
      exact hne (hterminal i (by omega))
    let j : Fin N := ⟨i.val + 1, hi⟩
    have hc := hcurv i j rfl hpos
    have hj := hmax j (Finset.mem_univ j)
    have hp : previousCoordinate f i.val ≤ f i := by
      unfold previousCoordinate
      split_ifs with hi0
      · exact hf i
      · let p : Fin N := ⟨i.val - 1, by omega⟩
        change zeroExtend f p.val ≤ f i
        rw [zeroExtend_at]
        exact hmax p (Finset.mem_univ p)
    linarith
  intro k
  have hk := hmax k (Finset.mem_univ k)
  rw [hzero] at hk
  exact le_antisymm hk (hf k)

/-- Vanishing is derived from full KKT and the maximum principle, not assumed. -/
theorem kkt_difference_multipliers_zero (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) : ∀ i, ν i = 0 := by
  have hscale := kkt_multiplier_scale_positive N h c hp
  have hf : ∀ i, 0 ≤ scaledNu h c ν i :=
    fun i => div_nonneg (hkkt.nu_nonnegative i) hscale.le
  have hterminal : ∀ b : Fin N, b.val + 1 = N → scaledNu h c ν b = 0 := by
    intro b hb
    unfold scaledNu
    rw [terminal_difference_multiplier_zero N h c hp hh β μ ν hkkt b hb, zero_div]
  have hcurv : ∀ i j : Fin N, i.val + 1 = j.val → 0 < scaledNu h c ν i →
      2 * scaledNu h c ν i - previousCoordinate (scaledNu h c ν) i.val - scaledNu h c ν j < 0 := by
    intro i j hij hpos
    have hν : ν i ≠ 0 := by
      intro hz
      simp [scaledNu, hz] at hpos
    have hd := (mul_eq_zero.mp (hkkt.difference_complementarity i)).resolve_left hν
    exact kkt_flat_curvature_negative N h c hp hh β μ ν hkkt i j hij hd
  have hzero := zero_of_strict_curvature_on_support N hp.n_pos (scaledNu h c ν)
    hf hterminal hcurv
  intro i
  have hz : ν i / (2 * h * c * S N h c) = 0 := hzero i
  exact (div_eq_zero_iff.mp hz).resolve_right (ne_of_gt hscale)

theorem kkt_strict_differences (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) : ∀ i, 0 < difference β i := by
  have hν := kkt_difference_multipliers_zero N h c hp hh β μ ν hkkt
  have hf : scaledNu h c ν = 0 := by
    funext i
    simp [scaledNu, hν i]
  intro i
  by_cases hi : i.val + 1 < N
  · by_contra hn
    have hd : difference β i = 0 := le_antisymm (le_of_not_gt hn) (hkkt.feasible.2.1 i)
    let j : Fin N := ⟨i.val + 1, hi⟩
    have hc := kkt_flat_curvature_negative N h c hp hh β μ ν hkkt i j rfl hd
    rw [hf] at hc
    simp [previousCoordinate, zeroExtend] at hc
  · have hb : i.val + 1 = N := by omega
    have hd : difference β i = β i := by simp [difference, zeroExtend, hb]
    rw [hd]
    exact feasible_terminal_positive N h c hp hh β hkkt.feasible i hb

/-- Equation (4.4), derived from the full KKT system. -/
theorem optimizer_strict_order (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (β : Vec N) (hβ : IsOptimizer h c β) : ∀ i, 0 < difference β i := by
  obtain ⟨μ, ν, hkkt⟩ := complete_kkt_exists N h c hp β hβ
  exact kkt_strict_differences N h c hp hh β μ ν hkkt

theorem difference_multipliers_vanish (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (β : Vec N) (hβ : IsOptimizer h c β)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν) : ∀ i, ν i = 0 := by
  have horder := optimizer_strict_order N h c hp hh β hβ
  intro i
  exact (mul_eq_zero.mp (hkkt.difference_complementarity i)).resolve_right (ne_of_gt (horder i))

end
end CriticalExtrapolation.Paper
