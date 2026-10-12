import PaperFramework.FlowSlackAlgebra

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem norm_three_term_identity {d : ℕ} (a b : ℝ) (q z v : Space d) :
    ‖a • q + z + b • v‖ ^ 2 - a ^ 2 * ‖q‖ ^ 2 =
      ‖z‖ ^ 2 + b ^ 2 * ‖v‖ ^ 2 + 2 * a * inner ℝ q z +
        2 * b * inner ℝ v z + 2 * a * b * inner ℝ v q := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, conj_trivial]
  rw [real_inner_comm z q, real_inner_comm z v, real_inner_comm q v]
  ring

/-- The full certificate identity for the actual global function and actual GD output. -/
theorem forward_flow_identity_proved {d : ℕ} (I : Instance d 1 1) (N : ℕ) (h c : ℝ)
    (hp : Parameters N h c) (F : Flow N) (hF : AdmissibleFlow F) :
    let data := sampledInstance I N h c
    let q := gradient I.f (output I N h c)
    let z := output I N h c - I.minimizer - q
    ‖I.initial - I.minimizer‖ ^ 2 - (S N h c) ^ 2 * ‖q‖ ^ 2 =
      ‖z‖ ^ 2 + (∑ i, ∑ j, flowMatrix h c F i j *
        inner ℝ (data.g (ordinaryQuery i) - q) (data.g (ordinaryQuery j) - q)) +
      2 * h * c * (∑ i, slack data (starQuery N) (ordinaryQuery i)) +
      2 * slack data (starQuery N) (outputQuery N) +
      2 * S N h c * slack data (outputQuery N) (starQuery N) +
      (∑ e ∈ edges N, lambda h c F e * slack data (ordinaryQuery e.1) (some e.2)) +
      ∑ i, outputMultiplier h c F i * slack data (outputQuery N) (ordinaryQuery i) := by
  let q := gradient I.f (output I N h c)
  let z := output I N h c - I.minimizer - q
  let raw := sampledInstance I N h c
  let data := translatedSample raw I.minimizer
  let v : Fin N → Space d := fun i => raw.g (ordinaryQuery i) - q
  have hstarx : data.x (starQuery N) = 0 := by simp [data, raw, translatedSample, sampledInstance, starQuery]
  have hstarg : data.g (starQuery N) = 0 := sampled_star_gradient (N := N) I h c
  have hgrad : ∀ j, data.g (some j) = q + flowVectorExtend v j := by
    intro j
    by_cases hj : j.val < N
    · let i : Fin N := ⟨j.val, hj⟩
      have hji : j = i.castSucc := by apply Fin.ext; rfl
      rw [hji, flowVectorExtend_ordinary]
      change raw.g (ordinaryQuery i) = q + (raw.g (ordinaryQuery i) - q)
      abel
    · have hji : j = Fin.last N := by apply Fin.ext; simp; omega
      rw [hji, flowVectorExtend_output, add_zero]
      exact sampled_output_gradient (N := N) I h c
  have hout : data.x (outputQuery N) - data.g (outputQuery N) = z := by
    change raw.x (outputQuery N) - I.minimizer - raw.g (outputQuery N) = z
    rw [sampled_output_position, sampled_output_gradient]
  have hord : ∀ i, data.x (ordinaryQuery i) - data.g (ordinaryQuery i) =
      (queryK N h c i) • q + z + flowVectorT h c v i := by
    intro i
    exact sampled_ordinary_geometry I h c i
  have hw := weighted_slack_flow_identity h c hp F hF data q z v hstarx hstarg hgrad hout hord
  simp only [data, translated_slack] at hw
  have hm := vector_flow_quadratic_identity h c F v
  have hn := norm_three_term_identity (S N h c) (h * c) q z (∑ i, v i)
  have hi : I.initial - I.minimizer = (S N h c) • q + z + (h * c) • ∑ i, v i :=
    sampled_initial_geometry I h c
  rw [← hi] at hn
  change ‖I.initial - I.minimizer‖ ^ 2 - (S N h c) ^ 2 * ‖q‖ ^ 2 =
    ‖z‖ ^ 2 + (∑ i, ∑ j, flowMatrix h c F i j * inner ℝ (v i) (v j)) +
      2 * h * c * (∑ i, slack raw (starQuery N) (ordinaryQuery i)) +
      2 * slack raw (starQuery N) (outputQuery N) +
      2 * S N h c * slack raw (outputQuery N) (starQuery N) +
      (∑ e ∈ edges N, lambda h c F e * slack raw (ordinaryQuery e.1) (some e.2)) +
      ∑ i, outputMultiplier h c F i * slack raw (outputQuery N) (ordinaryQuery i)
  linear_combination hn - hm - hw

end
end CriticalExtrapolation.Paper
