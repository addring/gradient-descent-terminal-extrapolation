import PaperFramework.Interpolation
import PaperFramework.FlowTransport
import PaperFramework.ForwardNonnegativity
import PaperFramework.ForwardFlowAlgebra
import PaperFramework.FlowIdentityProof

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- (2.6), translated by the minimizer. `q` is the gradient at output y, never at x_N. -/
theorem forward_flow_identity {d : ℕ} (I : Instance d 1 1) (N : ℕ) (h c : ℝ)
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
  exact forward_flow_identity_proved I N h c hp F hF

theorem forward_certificate_per_instance {d : ℕ} (I : Instance d 1 1) (N : ℕ) (h c : ℝ)
    (hp : Parameters N h c) (F : Flow N) (hF : AdmissibleFlow F)
    (hM : NonnegativeQuadratic (flowMatrix h c F)) :
    ‖gradient I.f (output I N h c)‖ ≤ 1 / S N h c := by
  have hid := forward_flow_identity I N h c hp F hF
  have hslack := sampled_slacks_nonnegative I N h c
  have hmult := output_multipliers_positive N h c hp F hF
  have hnonneg := forward_remainder_nonnegative h c hp F hF hM
    (sampledInstance I N h c) hslack (gradient I.f (output I N h c))
    (output I N h c - I.minimizer - gradient I.f (output I N h c))
  rw [← hid] at hnonneg
  exact forward_gradient_bound_of_nonnegative I N h c hp hnonneg

/-- (2.7): the certificate applies to the actual supremum over all finite dimensions. -/
theorem forward_certificate_exact (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (F : Flow N) (hF : AdmissibleFlow F) (hM : NonnegativeQuadratic (flowMatrix h c F)) :
    worstGradient N h c 1 1 = 1 / S N h c := by
  have hlower := huber_lower_bound N h c 1 1 hp zero_lt_one zero_lt_one
  simp only [one_mul] at hlower
  have hupper : ∀ d (I : Instance d 1 1),
      ‖gradient I.f (output I N h c)‖ ≤ 1 / S N h c :=
    fun d I => forward_certificate_per_instance I N h c hp F hF hM
  apply le_antisymm _ hlower
  apply csSup_le (instance_values_nonempty_bounded N h c 1 1 zero_lt_one zero_lt_one).1
  rintro r ⟨d, I, rfl⟩
  exact hupper d I

end
end CriticalExtrapolation.Paper
