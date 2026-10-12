import PaperFramework.FiniteIntervalSums

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem row_moments_interval {N : ℕ} (h c : ℝ) (β : Vec N) (μ : Fin (N - 1) → ℝ)
    (a b : Fin N) (hab : a ≤ b) :
    (∑ i ∈ Finset.Icc a b, rowMoment h c β μ i) =
      (∑ i ∈ Finset.Icc a b, ((i.val : ℝ) + 1) * difference β i) +
        scaledMu h c μ b.val - previousMu h c μ a.val := by
  have hpoint : ∀ i : Fin N, rowMoment h c β μ i =
      ((i.val : ℝ) + 1) * difference β i +
        (previousMu h c μ (i.val + 1) - previousMu h c μ i.val) := by
    intro i
    rw [previousMu_succ]
    unfold rowMoment
    ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [sum_fin_Icc_difference a b hab, previousMu_succ]
  ring

theorem plateau_row_moments_sum {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν)
    (a b : Fin N) (hplateau : IsMaximalSlopePlateau h c β a b) :
    (∑ i ∈ Finset.Icc a b, rowMoment h c β μ i) =
      ∑ i ∈ Finset.Icc a b, ((i.val : ℝ) + 1) * difference β i := by
  have he := plateau_boundary_multipliers h c β μ ν hkkt a b hplateau
  rw [row_moments_interval h c β μ a b hplateau.1, he.1, he.2, add_zero, sub_zero]

theorem plateau_row_weight_bound (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν)
    (a b : Fin N) (hplateau : IsMaximalSlopePlateau h c β a b)
    (i : Fin N) (hai : a ≤ i) (hib : i ≤ b) :
    kktRowWeight h c β μ i ≤ kktRowWeight h c β μ b := by
  apply fin_interval_mono (kktRowWeight h c β μ) i b hib
  intro x y hix hyb hxy
  have hxy' : x ≤ y := by change x.val ≤ y.val; omega
  have hax := le_trans hai hix
  have hay := le_trans hax hxy'
  have hxb := le_trans hxy' hyb
  exact equal_slope_row_weight_step N h c hp hh β μ ν hkkt x y hxy
    ((hplateau.2.1 x hax hxb).trans (hplateau.2.1 y hay hyb).symm)

theorem nonterminal_plateau_difference_bound (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (hβ : Feasible h c β) (a b : Fin N)
    (hplateau : IsMaximalSlopePlateau h c β a b) (hb : b.val + 1 < N)
    (i : Fin N) (hai : a ≤ i) (hib : i ≤ b) : difference β b ≤ difference β i := by
  apply fin_interval_antitone (difference β) i b hib
  intro x y hix hyb hxy
  have hxy' : x ≤ y := by change x.val ≤ y.val; omega
  have hax := le_trans hai hix
  have hay := le_trans hax hxy'
  have hxb := le_trans hxy' hyb
  have hyN : y.val + 1 < N := by have : y.val ≤ b.val := hyb; omega
  let j : Fin N := ⟨y.val + 1, hyN⟩
  exact equal_slope_difference_step N h c hp β hβ x y j hxy rfl
    ((hplateau.2.1 x hax hxb).trans (hplateau.2.1 y hay hyb).symm)

end
end CriticalExtrapolation.Paper
