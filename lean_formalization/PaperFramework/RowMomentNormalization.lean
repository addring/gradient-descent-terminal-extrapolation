import PaperFramework.TailEnergyIdentities

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem weighted_differences_sum {N : ℕ} (β : Vec N) :
    (∑ i, ((i.val : ℝ) + 1) * difference β i) = ∑ i, β i := by
  have hpoint : ∀ i : Fin N, difference β i =
      zeroExtend β i.val - zeroExtend β (i.val + 1) := by
    intro i
    rw [zeroExtend_at]
    rfl
  simp_rw [hpoint]
  have hs := sum_weighted_differences_zero_boundary (zeroExtend β) N
    (by simp [zeroExtend])
  rw [← Fin.sum_univ_eq_sum_range] at hs
  rw [← Fin.sum_univ_eq_sum_range] at hs
  simpa only [zeroExtend_at] using hs

theorem previousMu_succ {N : ℕ} (h c : ℝ) (μ : Fin (N - 1) → ℝ) (i : ℕ) :
    previousMu h c μ (i + 1) = scaledMu h c μ i := by
  simp [previousMu]

theorem multiplier_differences_sum {N : ℕ} (h c : ℝ) (μ : Fin (N - 1) → ℝ) :
    (∑ i : Fin N, (scaledMu h c μ i.val - previousMu h c μ i.val)) = 0 := by
  have hterminal : previousMu h c μ N = 0 := by
    unfold previousMu
    split_ifs
    · rfl
    · simp [scaledMu]
  have hs : (∑ i : Fin N, (scaledMu h c μ i.val - previousMu h c μ i.val)) =
      -(∑ i : Fin N, (previousMu h c μ i.val - scaledMu h c μ i.val)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  have ht' := sum_fin_natural_differences N (previousMu h c μ)
  rw [hterminal] at ht'
  simp only [previousMu_succ, sub_zero] at ht'
  have hzero : previousMu h c μ 0 = 0 := by simp [previousMu]
  rw [hzero] at ht'
  rw [ht', neg_zero]

/-- Normalization follows just from telescoping, independently of KKT or positivity. -/
theorem row_moments_sum {N : ℕ} (h c : ℝ) (β : Vec N) (μ : Fin (N - 1) → ℝ) :
    (∑ i, rowMoment h c β μ i) = ∑ i, β i := by
  have hs : (∑ i, rowMoment h c β μ i) =
      (∑ i, ((i.val : ℝ) + 1) * difference β i) +
      ∑ i : Fin N, (scaledMu h c μ i.val - previousMu h c μ i.val) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold rowMoment
    ring
  rw [hs, weighted_differences_sum, multiplier_differences_sum, add_zero]

end
end CriticalExtrapolation.Paper
