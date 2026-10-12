import PaperFramework.NegativeRadius

namespace CriticalExtrapolation.Paper
open scoped BigOperators
open Filter Topology
noncomputable section

theorem perturbation_radius_strict_small (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (hβ : ∑ i, β i = 1) (hQ : chainObjective h c β < 0) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀,
      0 < ‖perturbationInitial h c ε β‖ ∧ ‖perturbationInitial h c ε β‖ < S N h c := by
  obtain ⟨b₄, b₆, b₈, hexp⟩ := perturbation_radius_expansion h c β hβ
  let P : ℝ → ℝ := fun ε => chainObjective h c β + b₄ * ε ^ 2 + b₆ * ε ^ 4 + b₈ * ε ^ 6
  let X : ℝ → ℝ := fun ε => S N h c + h * c * (∑ i, backwardA h c β i) * ε ^ 2 +
    h * c * (∑ i, backwardB h c β i) * ε ^ 4
  have hS : 0 < S N h c := by
    have := hp.h_pos
    have := hp.c_ge_one
    unfold S
    positivity
  have hPcont : Continuous P := by dsimp [P]; fun_prop
  have hXcont : Continuous X := by dsimp [X]; fun_prop
  have hnegative : ∀ᶠ ε : ℝ in 𝓝 0, P ε < 0 :=
    hPcont.continuousAt.eventually_lt continuousAt_const (by simpa [P] using hQ)
  have hpositive : ∀ᶠ ε : ℝ in 𝓝 0, 0 < X ε :=
    continuousAt_const.eventually_lt hXcont.continuousAt (by simpa [X] using hS)
  obtain ⟨l, u, hlu, hall⟩ := (hnegative.and hpositive).exists_Ioo_subset
  refine ⟨u, hlu.2, ?_⟩
  intro ε hε
  obtain ⟨hP, hX⟩ := hall ⟨by linarith [hlu.1, hε.1], hε.2⟩
  have hsq : ‖perturbationInitial h c ε β‖ ^ 2 - S N h c ^ 2 = ε ^ 2 * P ε := by
    rw [hexp]
    dsimp [P]
    ring
  have hnegativeSq : ‖perturbationInitial h c ε β‖ ^ 2 < S N h c ^ 2 := by
    have := mul_neg_of_pos_of_neg (sq_pos_of_pos hε.1) hP
    linarith
  have hnorm := norm_nonneg (perturbationInitial h c ε β)
  have hcoords : ‖perturbationInitial h c ε β‖ ^ 2 = (X ε) ^ 2 + (h * c * ε) ^ 2 := by
    rw [perturbationInitial_coordinates, vec2_norm_sq, hβ]
    simp only [mul_one]
    rfl
  constructor
  · nlinarith [sq_pos_of_pos hX, sq_nonneg (h * c * ε)]
  · nlinarith

end
end CriticalExtrapolation.Paper

