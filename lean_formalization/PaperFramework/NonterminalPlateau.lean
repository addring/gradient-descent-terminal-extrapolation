import PaperFramework.PlateauSums

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- Equation (5.2), by summing monotone row weights and direction differences. -/
theorem nonterminal_plateau_endpoint (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (β : Vec N) (hβ : IsOptimizer h c β)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν)
    (a b : Fin N) (hplateau : IsMaximalSlopePlateau h c β a b) (hb : b.val + 1 < N) :
    difference β b ≤ rowMoment h c β μ b := by
  have hweight : 0 < ∑ i ∈ Finset.Icc a b, ((i.val : ℝ) + 1) := by
    apply Finset.sum_pos'
    · intro i _; positivity
    · exact ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, hplateau.1⟩, by positivity⟩
  have hlow : difference β b * (∑ i ∈ Finset.Icc a b, ((i.val : ℝ) + 1)) ≤
      ∑ i ∈ Finset.Icc a b, ((i.val : ℝ) + 1) * difference β i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hd := nonterminal_plateau_difference_bound N h c hp β hβ.1 a b hplateau hb i hi'.1 hi'.2
    nlinarith [mul_nonneg (by positivity : 0 ≤ (i.val : ℝ) + 1) (sub_nonneg.mpr hd)]
  have hrow : ∀ i, rowMoment h c β μ i = queryK N h c i * kktRowWeight h c β μ i := by
    intro i
    unfold kktRowWeight
    field_simp [ne_of_gt (queryK_positive N h c hp i)]
  have hhigh : (∑ i ∈ Finset.Icc a b, rowMoment h c β μ i) ≤
      kktRowWeight h c β μ b * (∑ i ∈ Finset.Icc a b, queryK N h c i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hw := plateau_row_weight_bound N h c hp hh β μ ν hkkt a b hplateau i hi'.1 hi'.2
    rw [hrow i]
    nlinarith [mul_nonneg (queryK_positive N h c hp i).le (sub_nonneg.mpr hw)]
  have hwb : 0 < kktRowWeight h c β μ b :=
    div_pos (kkt_row_moments_positive N h c hp hh β μ ν hkkt b) (queryK_positive N h c hp b)
  have hK := mul_le_mul_of_nonneg_left (interval_queryK_bound N h c hp a b) hwb.le
  rw [plateau_row_moments_sum h c β μ ν hkkt a b hplateau] at hhigh
  have hproduct : difference β b * (∑ i ∈ Finset.Icc a b, ((i.val : ℝ) + 1)) ≤
      rowMoment h c β μ b * (∑ i ∈ Finset.Icc a b, ((i.val : ℝ) + 1)) := by
    rw [hrow b]
    calc
      _ ≤ _ := hlow
      _ ≤ _ := hhigh
      _ ≤ _ := by nlinarith [hK]
  exact (mul_le_mul_iff_left₀ hweight).mp hproduct

end
end CriticalExtrapolation.Paper
