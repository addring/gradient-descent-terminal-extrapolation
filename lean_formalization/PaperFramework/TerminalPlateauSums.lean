import PaperFramework.PlateauSums

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem interval_sum_bound_of_step {N : ℕ} (m P : Vec N) (a b : Fin N) (hab : a ≤ b)
    (hstep : ∀ i j : Fin N, a ≤ i → j ≤ b → i.val + 1 = j.val → m j ≤ P j - P i) :
    (∑ i ∈ Finset.Icc a b, m i) ≤ m a + P b - P a := by
  classical
  let C := m a - P a + previousCoordinate P a.val
  have hpoint : ∀ i ∈ Finset.Icc a b, m i ≤
      P i - previousCoordinate P i.val + (if i = a then C else 0) := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    by_cases hia : i = a
    · subst i; simp [C]
    · have hai : a.val < i.val := by
        have hle : a.val ≤ i.val := hi'.1
        have hne : a.val ≠ i.val := fun hv => hia (Fin.ext hv.symm)
        omega
      let p : Fin N := ⟨i.val - 1, by omega⟩
      have hpi : p.val + 1 = i.val := by dsimp [p]; omega
      have hpa : a ≤ p := by change a.val ≤ i.val - 1; omega
      have hpv : previousCoordinate P i.val = P p := by
        rw [← hpi, previousCoordinate_succ]
      rw [if_neg hia, add_zero, hpv]
      exact hstep p i hpa hi'.2 hpi
  have hs := Finset.sum_le_sum hpoint
  have ht := sum_fin_Icc_difference a b hab (previousCoordinate P)
  simp only [previousCoordinate_succ] at ht
  have hsel : (∑ i ∈ Finset.Icc a b, if i = a then C else 0) = C := by
    simp [Finset.mem_Icc, hab]
  rw [Finset.sum_add_distrib, ht, hsel] at hs
  dsimp [C] at hs
  linarith

theorem terminal_weighted_differences {N : ℕ} (β : Vec N) (a b : Fin N)
    (hab : a ≤ b) (hb : b.val + 1 = N) :
    (∑ i ∈ Finset.Icc a b, ((i.val : ℝ) + 1) * difference β i) =
      (∑ i ∈ Finset.Icc a b, β i) + (a.val : ℝ) * β a := by
  let z : ℕ → ℝ := fun k => (k : ℝ) * zeroExtend β k
  have hpoint : ∀ i : Fin N, ((i.val : ℝ) + 1) * difference β i =
      β i - (z (i.val + 1) - z i.val) := by
    intro i
    dsimp [z]
    rw [zeroExtend_at]
    simp only [Nat.cast_add, Nat.cast_one, difference]
    ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  rw [sum_fin_Icc_difference a b hab]
  simp [z, hb, zeroExtend_at, zeroExtend]

theorem terminal_weighted_differences_lower (N : ℕ) (h c : ℝ) (β : Vec N)
    (hβ : Feasible h c β) (a b : Fin N) (hab : a ≤ b) (hb : b.val + 1 = N) :
    (N : ℝ) * β b ≤ ∑ i ∈ Finset.Icc a b, ((i.val : ℝ) + 1) * difference β i := by
  have hmono := antitone_of_differences β hβ.2.1
  have hs : ((Finset.Icc a b).card : ℝ) * β b ≤ ∑ i ∈ Finset.Icc a b, β i := by
    calc
      _ = ∑ i ∈ Finset.Icc a b, β b := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi => hmono (Finset.mem_Icc.mp hi).2)
  have ha := mul_le_mul_of_nonneg_left (hmono hab) (Nat.cast_nonneg (α := ℝ) a.val)
  have hcard : ((Finset.Icc a b).card : ℝ) + (a.val : ℝ) = N := by
    rw [Fin.card_Icc, hb, Nat.cast_sub (by have := a.isLt; omega)]
    ring
  rw [terminal_weighted_differences β a b hab hb]
  nlinarith [congrArg (fun x : ℝ => x * β b) hcard]

theorem equal_slope_row_weight_contraction (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i j : Fin N) (hij : i.val + 1 = j.val)
    (hs : slope h c β i = slope h c β j) :
    kktRowWeight h c β μ i ≤ (1 - h) * kktRowWeight h c β μ j := by
  have hjR : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij.symm
  have hUj : kktSlopeMoment h c β j = slope h c β i := by
    rw [kktSlopeMoment_at_successor h c β i j hij, ← hs, hjR]
    ring
  have hUi := kktSlopeMoment_le_slope N h c β hkkt.feasible i
  have hbal := kkt_adjacent_reduced N h c hp hh β μ ν hkkt i j hij
  rw [hUj] at hbal
  linarith

/-- The finite geometric bound, expressed as a telescoping potential. -/
theorem plateau_row_sum_strict_upper (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (a b : Fin N)
    (hplateau : IsMaximalSlopePlateau h c β a b) :
    (∑ i ∈ Finset.Icc a b, rowMoment h c β μ i) <
      ((queryK N h c b + (1 - h)) / h) * kktRowWeight h c β μ b := by
  let P : Vec N := fun i => ((queryK N h c i + (1 - h)) / h) * kktRowWeight h c β μ i
  have hrow : ∀ i, rowMoment h c β μ i = queryK N h c i * kktRowWeight h c β μ i := by
    intro i
    unfold kktRowWeight
    field_simp [ne_of_gt (queryK_positive N h c hp i)]
  have hstep : ∀ i j : Fin N, a ≤ i → j ≤ b → i.val + 1 = j.val →
      rowMoment h c β μ j ≤ P j - P i := by
    intro i j hai hjb hij
    have hij' : i ≤ j := by change i.val ≤ j.val; omega
    have hslope := (hplateau.2.1 i hai (le_trans hij' hjb)).trans
      (hplateau.2.1 j (le_trans hai hij') hjb).symm
    have hw := equal_slope_row_weight_contraction N h c hp hh β μ ν hkkt i j hij hslope
    have hcoef : 0 ≤ (queryK N h c i + (1 - h)) / h :=
      (div_pos (add_pos (queryK_positive N h c hp i) (sub_pos.mpr hh)) hp.h_pos).le
    have hmul := mul_le_mul_of_nonneg_left hw hcoef
    have heq : P j - ((queryK N h c i + (1 - h)) / h) *
        ((1 - h) * kktRowWeight h c β μ j) = rowMoment h c β μ j := by
      dsimp [P]
      rw [hrow j]
      field_simp [ne_of_gt hp.h_pos]
      rw [queryK_adjacent h c i j hij]
      ring
    change rowMoment h c β μ j ≤ P j -
      ((queryK N h c i + (1 - h)) / h) * kktRowWeight h c β μ i
    linarith
  have hs := interval_sum_bound_of_step (rowMoment h c β μ) P a b hplateau.1 hstep
  have hwa : 0 < kktRowWeight h c β μ a :=
    div_pos (kkt_row_moments_positive N h c hp hh β μ ν hkkt a) (queryK_positive N h c hp a)
  have hPa : rowMoment h c β μ a < P a := by
    rw [hrow a]
    dsimp [P]
    apply mul_lt_mul_of_pos_right _ hwa
    apply (lt_div_iff₀ hp.h_pos).mpr
    have hm := mul_pos (sub_pos.mpr hh) (by linarith [queryK_positive N h c hp a] : 0 < queryK N h c a + 1)
    nlinarith
  change (∑ i ∈ Finset.Icc a b, rowMoment h c β μ i) < P b
  linarith

end
end CriticalExtrapolation.Paper
