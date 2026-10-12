import PaperFramework.NegativeLocalSlacks
import PaperFramework.NegativeBackward
import Mathlib.Topology.Order.LeftRightNhds

namespace CriticalExtrapolation.Paper
open scoped BigOperators
open Filter Topology
noncomputable section

theorem perturbation_minimizer_slack_eventually (N : ℕ) (h c : ℝ)
    (hp : Parameters N h c) (β : Vec N) (i : Fin N) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < slack (perturbationSample h c ε β) (ordinaryQuery i) (starQuery N) := by
  let p : ℝ → ℝ := fun ε =>
    (1 + backwardA h c β i * ε ^ 2 + backwardB h c β i * ε ^ 4) *
      (queryK N h c i + applyT h c (backwardA h c β) i * ε ^ 2 +
        applyT h c (backwardB h c β) i * ε ^ 4) +
      (β i * ε) * (applyT h c β i * ε)
  have hid : ∀ ε, slack (perturbationSample h c ε β) (ordinaryQuery i) (starQuery N) = p ε := by
    intro ε
    rw [perturbation_slack_identity, perturbation_ordinary_residual, perturbation_ordinary_gradient]
    have hg : (perturbationSample h c ε β).g (starQuery N) = 0 := rfl
    rw [hg, sub_zero]
    unfold perturbationGradient
    rw [vec2_inner]
  have hcont : Continuous p := by dsimp [p]; fun_prop
  have hpos : ∀ᶠ ε : ℝ in 𝓝 0, 0 < p ε :=
    continuousAt_const.eventually_lt hcont.continuousAt
      (by simpa [p] using queryK_positive N h c hp i)
  exact (hpos.filter_mono nhdsWithin_le_nhds).mono (fun ε hε => by rwa [hid])

theorem perturbation_nonadjacent_slack_eventually (N : ℕ) (h c : ℝ)
    (hp : Parameters N h c) (β : Vec N) (hβ : StrictlyFeasible h c β)
    (i : Fin N) (j : Fin (N + 1))
    (hij : j.val < i.val ∨ i.val + 1 < j.val) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < slack (perturbationSample h c ε β) (ordinaryQuery i) (some j) := by
  let A := backwardA h c β
  let B := backwardB h c β
  let ΔA := A i - zeroExtend A j.val
  let ΔB := B i - zeroExtend B j.val
  let P := applyT h c A i
  let V := applyT h c B i
  let p : ℝ → ℝ := fun ε =>
    queryK N h c i * negativeLeading h c β i j.val +
      (queryK N h c i * ΔB + P * ΔA) * ε ^ 2 +
      (V * ΔA + P * ΔB) * ε ^ 4 + V * ΔB * ε ^ 6
  have hlead : 0 < negativeLeading h c β i j.val := by
    rcases hij with hb | hf
    · exact negativeLeading_backward_strict h c β hβ i j.val hb
    · exact negativeLeading_forward_strict h c β hβ i j.val hf (by omega)
  have hcont : Continuous p := by dsimp [p]; fun_prop
  have hpos : ∀ᶠ ε : ℝ in 𝓝 0, 0 < p ε :=
    continuousAt_const.eventually_lt hcont.continuousAt
      (by simpa [p] using mul_pos (queryK_positive N h c hp i) hlead)
  have hid : ∀ ε, slack (perturbationSample h c ε β) (ordinaryQuery i) (some j) = ε ^ 2 * p ε := by
    intro ε
    rw [ordinary_slack_polynomial h c ε hp β]
    dsimp [p, negativeLeading, A, B, ΔA, ΔB, P, V]
    ring
  filter_upwards [hpos.filter_mono nhdsWithin_le_nhds,
    (show ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin)] with ε hε hεpos
  rw [hid]
  exact mul_pos (sq_pos_of_pos hεpos) hε

end
end CriticalExtrapolation.Paper
