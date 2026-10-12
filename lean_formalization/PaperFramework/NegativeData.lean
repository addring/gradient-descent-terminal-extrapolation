import PaperFramework.QuadraticProgramKKT
import PaperFramework.NegativeAlgebra
import PaperFramework.NegativeRadius
import PaperFramework.NegativeSmall
import PaperFramework.NegativePolynomial
import PaperFramework.NegativeAllSlacks

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

theorem perturbation_all_directed_slacks (N : ℕ) (h c : ℝ)
    (hp : Parameters N h c) (β : Vec N) (hβ : StrictlyFeasible h c β) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∀ i j,
      0 ≤ slack (perturbationSample h c ε β) i j := by
  exact perturbation_all_directed_slacks_of_strict N h c hp β hβ

/-- A common finite perturbation size satisfies every slack and strictly improves the radius. -/
theorem negative_direction_finite_data (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (hβ : StrictlyFeasible h c β) (hQ : chainObjective h c β < 0) :
    ∃ ε > 0, (∀ i j, 0 ≤ slack (perturbationSample h c ε β) i j) ∧
      0 < ‖perturbationInitial h c ε β‖ ∧ ‖perturbationInitial h c ε β‖ < S N h c := by
  obtain ⟨ε₀, hε₀, hslacks⟩ := perturbation_all_directed_slacks N h c hp β hβ
  obtain ⟨δ, hδ, hradius⟩ := perturbation_radius_strict_small N h c hp β hβ.1 hQ
  let ε : ℝ := min ε₀ δ / 2
  have hε : 0 < ε := div_pos (lt_min hε₀ hδ) (by norm_num)
  have hε₀lt : ε < ε₀ := by have := min_le_left ε₀ δ; dsimp [ε]; linarith
  have hεδ : ε < δ := by have := min_le_right ε₀ δ; dsimp [ε]; linarith
  exact ⟨ε, hε, hslacks ε ⟨hε, hε₀lt⟩, hradius ε ⟨hε, hεδ⟩⟩

end
end CriticalExtrapolation.Paper

