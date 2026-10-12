import PaperFramework.FullConjugatePotential

namespace CriticalExtrapolation.Paper
noncomputable section

/-- Strong convexity gives the full one-half quadratic growth at every conjugate minimizer. -/
theorem full_conjugate_minimizer_quadratic_growth {N d : ℕ} (data : Sample N d)
    (x u v : Space d) (hu : FullConjugateMinimizer data x u) :
    fullConjugatePotential data u - inner ℝ x u + ‖u - v‖ ^ 2 / 2 ≤
      fullConjugatePotential data v - inner ℝ x v := by
  let q : ℝ := ‖u - v‖ ^ 2 / 2
  let gap : ℝ := (fullConjugatePotential data v - inner ℝ x v) -
    (fullConjugatePotential data u - inner ℝ x u)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hgap : 0 ≤ gap := sub_nonneg.mpr (hu v)
  suffices hqgap : q ≤ gap by dsimp [q, gap] at hqgap; linarith
  by_cases hq : q = 0
  · rwa [hq]
  have hqpos : 0 < q := lt_of_le_of_ne hq0 (fun h => hq h.symm)
  apply le_of_forall_pos_le_add
  intro ε hε
  let τ : ℝ := min 1 (ε / q)
  have hτpos : 0 < τ := lt_min zero_lt_one (div_pos hε hqpos)
  have hτone : τ ≤ 1 := min_le_left _ _
  have hτq : τ * q ≤ ε := (le_div_iff₀ hqpos).mp (min_le_right 1 (ε / q))
  have hs := (fullConjugatePotential_strongConvex data).2 (Set.mem_univ u) (Set.mem_univ v)
    (show 0 ≤ 1 - τ by linarith) hτpos.le (show 1 - τ + τ = 1 by ring)
  simp only [smul_eq_mul] at hs
  change fullConjugatePotential data ((1 - τ) • u + τ • v) ≤
    (1 - τ) * fullConjugatePotential data u + τ * fullConjugatePotential data v -
      (1 - τ) * τ * ((1 : ℝ) / 2 * ‖u - v‖ ^ 2) at hs
  have hqnorm : (1 : ℝ) / 2 * ‖u - v‖ ^ 2 = q := by dsimp [q]; ring
  rw [hqnorm] at hs
  have hm := hu ((1 - τ) • u + τ • v)
  have hi : inner ℝ x ((1 - τ) • u + τ • v) =
      (1 - τ) * inner ℝ x u + τ * inner ℝ x v := by
    simp only [inner_add_right, real_inner_smul_right]
  rw [hi] at hm
  have hproduct : τ * ((1 - τ) * q - gap) ≤ 0 := by
    dsimp [gap]
    nlinarith only [hs, hm]
  have hpart : (1 - τ) * q ≤ gap := by
    have hnonpos : (1 - τ) * q - gap ≤ 0 := by
      refine le_of_mul_le_mul_left ?_ hτpos
      simpa only [mul_zero] using hproduct
    linarith
  nlinarith only [hpart, hτq]

theorem full_conjugate_optimizer_firm_nonexpansive_proved {N d : ℕ} (data : Sample N d)
    (x z u v : Space d) (hu : FullConjugateMinimizer data x u)
    (hv : FullConjugateMinimizer data z v) :
    ‖u - v‖ ^ 2 ≤ inner ℝ (x - z) (u - v) := by
  have hxu := full_conjugate_minimizer_quadratic_growth data x u v hu
  have hzv := full_conjugate_minimizer_quadratic_growth data z v u hv
  rw [norm_sub_rev] at hzv
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  linarith

end
end CriticalExtrapolation.Paper

