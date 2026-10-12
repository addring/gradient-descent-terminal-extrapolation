import PaperFramework.NegativeAlgebra
import PaperFramework.VecTwo
import PaperFramework.RowMomentNormalization

namespace CriticalExtrapolation.Paper
open scoped BigOperators
open Filter Topology
noncomputable section

theorem backwardA_sum {N : ℕ} (h c : ℝ) (β : Vec N) :
    (∑ i, backwardA h c β i) = -∑ i, ((i.val : ℝ) + 1) * difference β i * slope h c β i := by
  rw [← weighted_differences_sum (backwardA h c β)]
  simp_rw [(backward_recursions h c β _).1]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem perturbationInitial_coordinates {N : ℕ} (h c ε : ℝ) (β : Vec N) :
    perturbationInitial h c ε β =
      vec2 (S N h c + h * c * (∑ i, backwardA h c β i) * ε ^ 2 +
        h * c * (∑ i, backwardB h c β i) * ε ^ 4)
        (h * c * (∑ i, β i) * ε) := by
  unfold perturbationInitial perturbationGradient
  rw [vec2_sum, vec2_smul, vec2_add]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.sum_mul, mul_one, zero_add]
  simp only [S]
  congr 1 <;> ring

/-- The exact polynomial in (11.5), retaining all fourth-, sixth- and eighth-order terms. -/
theorem perturbation_radius_expansion {N : ℕ} (h c : ℝ) (β : Vec N)
    (hβ : ∑ i, β i = 1) :
    ∃ b₄ b₆ b₈ : ℝ, ∀ ε : ℝ,
      ‖perturbationInitial h c ε β‖ ^ 2 - S N h c ^ 2 =
        chainObjective h c β * ε ^ 2 + b₄ * ε ^ 4 + b₆ * ε ^ 6 + b₈ * ε ^ 8 := by
  let U : ℝ := h * c * (∑ i, backwardA h c β i)
  let V : ℝ := h * c * (∑ i, backwardB h c β i)
  have hcoefficient : chainObjective h c β = 2 * S N h c * U + (h * c) ^ 2 := by
    dsimp [U]
    rw [backwardA_sum]
    unfold chainObjective S
    rw [hβ]
    ring
  refine ⟨U ^ 2 + 2 * S N h c * V, 2 * U * V, V ^ 2, ?_⟩
  intro ε
  rw [perturbationInitial_coordinates, vec2_norm_sq, hβ, hcoefficient]
  change (S N h c + U * ε ^ 2 + V * ε ^ 4) ^ 2 + (h * c * 1 * ε) ^ 2 - S N h c ^ 2 = _
  ring

end
end CriticalExtrapolation.Paper

