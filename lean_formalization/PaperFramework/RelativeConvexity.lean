import PaperFramework.Energy

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem quadraticForm_mix_gap {N : ℕ} (M : Mat N) (x y : Vec N) (a b : ℝ) (hab : a + b = 1) :
    a * quadraticForm M x + b * quadraticForm M y - quadraticForm M (a • x + b • y) =
      a * b * quadraticForm M (x - y) := by
  have hb : b = 1 - a := by linarith
  subst b
  unfold quadraticForm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem normalization_affine_convex (N : ℕ) : Convex ℝ {β : Vec N | (∑ i, β i) = 1} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy
  change (∑ i, (a * x i + b * y i)) = 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx, hy]
  simpa only [mul_one] using hab

/-- Strict convexity on the original normalization affine space, derived from zero-sum positivity. -/
theorem relative_strict_convexity (N : ℕ) (h c : ℝ) (hp : Parameters N h c) :
    StrictConvexOn ℝ {β : Vec N | (∑ i, β i) = 1} (chainObjective h c) := by
  refine ⟨normalization_affine_convex N, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy
  have hsum : (∑ i, (x - y) i) = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hx, hy, sub_self]
  have hpositive := objective_positive_on_zero_sum N h c hp (x - y) hsum (sub_ne_zero.mpr hxy)
  have hgap : a * chainObjective h c x + b * chainObjective h c y -
      chainObjective h c (a • x + b • y) = a * b * chainObjective h c (x - y) := by
    simp_rw [chainObjective_matrix N h c hp]
    exact quadraticForm_mix_gap (M₀ N h c) x y a b hab
  have hprod := mul_pos (mul_pos ha hb) hpositive
  change chainObjective h c (a • x + b • y) < a * chainObjective h c x + b * chainObjective h c y
  linarith

end
end CriticalExtrapolation.Paper
