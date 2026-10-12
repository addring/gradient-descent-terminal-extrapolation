import PaperFramework.TerminalPlateau
import PaperFramework.NonterminalPlateau
import PaperFramework.FlowBasics

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- The numerator controlling nonnegativity of the interior flow probability. -/
def probabilityNumerator {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (i : Fin N) : ℝ :=
  (i.val : ℝ) * rowMoment h c β μ i - previousMu h c μ i.val

theorem probabilityNumerator_step {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (i j : Fin N) (hij : i.val + 1 = j.val) :
    probabilityNumerator h c β μ j - probabilityNumerator h c β μ i =
      ((i.val : ℝ) + 1) * (rowMoment h c β μ j - rowMoment h c β μ i + difference β i) := by
  have hj : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij.symm
  unfold probabilityNumerator
  rw [hj, ← hij, previousMu_succ]
  unfold rowMoment
  ring

theorem equal_slope_row_weight_recurrence (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (p i j : Fin N)
    (hpi : p.val + 1 = i.val) (hij : i.val + 1 = j.val)
    (hsp : slope h c β p = slope h c β i) (hsi : slope h c β i = slope h c β j) :
    kktRowWeight h c β μ i = (1 - h) * kktRowWeight h c β μ j := by
  have hiR : (i.val : ℝ) = (p.val : ℝ) + 1 := by exact_mod_cast hpi.symm
  have hjR : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij.symm
  have hUi : kktSlopeMoment h c β i = slope h c β i := by
    rw [kktSlopeMoment_at_successor h c β p i hpi, hsp, hiR]
    ring
  have hUj : kktSlopeMoment h c β j = slope h c β i := by
    rw [kktSlopeMoment_at_successor h c β i j hij, ← hsi, hjR]
    ring
  have hb := kkt_adjacent_reduced N h c hp hh β μ ν hkkt i j hij
  rw [hUi, hUj, sub_self] at hb
  linarith

/-- Once an increment is nonpositive, the next interior increment is negative. -/
theorem plateau_increment_sign (h K wp wi wj d : ℝ) (hh0 : 0 < h) (hh1 : h < 1)
    (hwi : 0 < wi) (hwj : 0 < wj) (hd : 0 < d)
    (hwp : wp ≤ (1 - h) * wi) (hrec : wi = (1 - h) * wj)
    (hK : 0 < K) (hprev : (K - h) * wi - K * wp + d ≤ 0) :
    (K - 2 * h) * wj - (K - h) * wi + (1 - h) * d < 0 := by
  have hbase : h * (K - 1) * wi + d ≤ 0 := by
    have hm := mul_le_mul_of_nonneg_left hwp hK.le
    nlinarith
  have hK1 : K < 1 := by
    by_contra hn
    have hm := mul_nonneg (mul_nonneg hh0.le (sub_nonneg.mpr (le_of_not_gt hn))) hwi.le
    linarith
  have hr : 0 < 1 - h := sub_pos.mpr hh1
  have hr2 : (1 - h) ^ 2 ≤ 1 := by nlinarith
  have hkneg : K - 1 < 0 := by linarith
  have hcmp : K - h - 1 < (1 - h) ^ 2 * (K - 1) := by
    have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr2) hkneg.le
    nlinarith
  have hm := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hcmp hh0) hwj
  have hb := mul_nonpos_of_nonneg_of_nonpos hr.le hbase
  rw [hrec] at hb
  rw [hrec]
  nlinarith only [hm, hb]

theorem interval_nonnegative_of_no_local_minimum {N : ℕ} (f : Vec N) (a b : Fin N)
    (hab : a ≤ b) (ha : 0 ≤ f a) (hb : 0 ≤ f b)
    (hstep : ∀ p i j : Fin N, a ≤ p → j ≤ b → p.val + 1 = i.val →
      i.val + 1 = j.val → f i ≤ f p → f j < f i) :
    ∀ i, a ≤ i → i ≤ b → 0 ≤ f i := by
  classical
  have hs : (Finset.Icc a b).Nonempty := ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, hab⟩⟩
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image (Finset.Icc a b) f hs
  have hk' := Finset.mem_Icc.mp hk
  have hk0 : 0 ≤ f k := by
    by_contra hn
    have hneg : f k < 0 := lt_of_not_ge hn
    have hka : k ≠ a := by intro heq; subst k; linarith
    have hkb : k ≠ b := by intro heq; subst k; linarith
    have hka' : a.val < k.val := by
      have hle : a.val ≤ k.val := hk'.1
      have hne : k.val ≠ a.val := fun heq => hka (Fin.ext heq)
      omega
    have hkb' : k.val < b.val := by
      have hle : k.val ≤ b.val := hk'.2
      have hne : k.val ≠ b.val := fun heq => hkb (Fin.ext heq)
      omega
    let p : Fin N := ⟨k.val - 1, by omega⟩
    let j : Fin N := ⟨k.val + 1, by omega⟩
    have hp : a ≤ p := by change a.val ≤ k.val - 1; omega
    have hj : j ≤ b := by change k.val + 1 ≤ b.val; omega
    have hpk : p.val + 1 = k.val := by dsimp [p]; omega
    have hkj : k.val + 1 = j.val := rfl
    have hleft := hmin p (Finset.mem_Icc.mpr ⟨hp, by change k.val - 1 ≤ b.val; omega⟩)
    have hright := hmin j (Finset.mem_Icc.mpr ⟨by change a.val ≤ k.val + 1; omega, hj⟩)
    exact (not_lt_of_ge hright) (hstep p k j hp hj hpk hkj hleft)
  intro i hai hib
  exact le_trans hk0 (hmin i (Finset.mem_Icc.mpr ⟨hai, hib⟩))

theorem probabilityNumerator_factor {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (i : Fin N) :
    probabilityNumerator h c β μ i = ((i.val : ℝ) + 1) *
      ((i.val : ℝ) * flowEll h c β μ i.val - previousMu h c μ i.val) := by
  rw [flowEll_at_coordinate]
  unfold probabilityNumerator rowMoment
  field_simp [show (i.val : ℝ) + 1 ≠ 0 by positivity]
  ring

theorem flowProbability_nonnegative_of_numerator (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i : Fin N)
    (hi : 0 ≤ probabilityNumerator h c β μ i) : 0 ≤ flowProbability h c β μ i.val := by
  by_cases hib : i.val = 0 ∨ i.val = N
  · simp [flowProbability, hib]
  · have hip : 0 < (i.val : ℝ) := by exact_mod_cast (show 0 < i.val by omega)
    have hden := mul_pos hip (kkt_flowEll_positive N h c hp hh β μ ν hkkt i)
    rw [probabilityNumerator_factor] at hi
    have hgap := (mul_nonneg_iff_of_pos_left (by positivity : 0 < (i.val : ℝ) + 1)).mp hi
    rw [flowProbability, if_neg hib]
    apply sub_nonneg.mpr
    apply (div_le_one hden).mpr
    simpa [previousMu, show i.val ≠ 0 by tauto] using (sub_nonneg.mp hgap)

theorem probabilityNumerator_no_local_minimum (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (p i j : Fin N)
    (hpi : p.val + 1 = i.val) (hij : i.val + 1 = j.val)
    (hsp : slope h c β p = slope h c β i) (hsi : slope h c β i = slope h c β j)
    (hle : probabilityNumerator h c β μ i ≤ probabilityNumerator h c β μ p) :
    probabilityNumerator h c β μ j < probabilityNumerator h c β μ i := by
  have hwpos : ∀ k, 0 < kktRowWeight h c β μ k := fun k =>
    div_pos (kkt_row_moments_positive N h c hp hh β μ ν hkkt k) (queryK_positive N h c hp k)
  have hrow : ∀ k, rowMoment h c β μ k = queryK N h c k * kktRowWeight h c β μ k := by
    intro k
    unfold kktRowWeight
    field_simp [ne_of_gt (queryK_positive N h c hp k)]
  have hstep := probabilityNumerator_step h c β μ p i hpi
  have hprev : rowMoment h c β μ i - rowMoment h c β μ p + difference β p ≤ 0 := by
    by_contra hn
    have hq := mul_pos (by positivity : 0 < (p.val : ℝ) + 1) (lt_of_not_ge hn)
    linarith
  rw [hrow i, hrow p, queryK_adjacent h c p i hpi] at hprev
  have hnext := plateau_increment_sign h (queryK N h c p)
    (kktRowWeight h c β μ p) (kktRowWeight h c β μ i) (kktRowWeight h c β μ j)
    (difference β p) hp.h_pos hh (hwpos i) (hwpos j)
    (kkt_strict_differences N h c hp hh β μ ν hkkt p)
    (equal_slope_row_weight_contraction N h c hp hh β μ ν hkkt p i hpi hsp)
    (equal_slope_row_weight_recurrence N h c hp hh β μ ν hkkt p i j hpi hij hsp hsi)
    (queryK_positive N h c hp p) hprev
  have hd := plateau_difference_recurrence N h c hp β p i j hpi hij hsp hsi
  have hq : rowMoment h c β μ j - rowMoment h c β μ i + difference β i < 0 := by
    rw [hrow j, hrow i, queryK_adjacent h c i j hij, queryK_adjacent h c p i hpi, hd]
    convert hnext using 1 <;> ring
  have hstep' := probabilityNumerator_step h c β μ i j hij
  have hn := mul_neg_of_pos_of_neg (by positivity : 0 < (i.val : ℝ) + 1) hq
  linarith

end
end CriticalExtrapolation.Paper
