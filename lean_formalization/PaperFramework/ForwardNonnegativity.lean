import PaperFramework.VectorQuadratic
import PaperFramework.FlowTransport

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem S_positive (N : ℕ) (h c : ℝ) (hp : Parameters N h c) : 0 < S N h c := by
  unfold S
  have hh := hp.h_pos
  have hc : 0 ≤ c := le_trans zero_le_one hp.c_ge_one
  positivity

theorem flow_lambda_nonnegative (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (F : Flow N) (hF : AdmissibleFlow F) (e : Edge N) (he : e ∈ edges N) :
    0 ≤ lambda h c F e := by
  unfold lambda
  have hh := hp.h_pos
  have hc : 0 ≤ c := le_trans zero_le_one hp.c_ge_one
  exact mul_nonneg (div_nonneg (by have := S_positive N h c hp; positivity)
    (queryK_positive N h c hp e.1).le) (hF.1 e he)

/-- Every term on the right of the forward identity is nonnegative. -/
theorem forward_remainder_nonnegative {N d : ℕ} (h c : ℝ) (hp : Parameters N h c)
    (F : Flow N) (hF : AdmissibleFlow F) (hM : NonnegativeQuadratic (flowMatrix h c F))
    (data : Sample N d) (hs : ∀ i j, 0 ≤ slack data i j) (q z : Space d) :
    0 ≤ ‖z‖ ^ 2 + (∑ i, ∑ j, flowMatrix h c F i j *
        inner ℝ (data.g (ordinaryQuery i) - q) (data.g (ordinaryQuery j) - q)) +
      2 * h * c * (∑ i, slack data (starQuery N) (ordinaryQuery i)) +
      2 * slack data (starQuery N) (outputQuery N) +
      2 * S N h c * slack data (outputQuery N) (starQuery N) +
      (∑ e ∈ edges N, lambda h c F e * slack data (ordinaryQuery e.1) (some e.2)) +
      ∑ i, outputMultiplier h c F i * slack data (outputQuery N) (ordinaryQuery i) := by
  have hh := hp.h_pos
  have hc : 0 ≤ c := le_trans zero_le_one hp.c_ge_one
  have hmatrix := vector_quadratic_nonnegative (flowMatrix h c F) hM
    (fun i => data.g (ordinaryQuery i) - q)
  have hstar : 0 ≤ ∑ i, slack data (starQuery N) (ordinaryQuery i) :=
    Finset.sum_nonneg (fun i _ => hs _ _)
  have hedges : 0 ≤ ∑ e ∈ edges N,
      lambda h c F e * slack data (ordinaryQuery e.1) (some e.2) :=
    Finset.sum_nonneg (fun e he => mul_nonneg (flow_lambda_nonnegative N h c hp F hF e he) (hs _ _))
  have hout : 0 ≤ ∑ i, outputMultiplier h c F i * slack data (outputQuery N) (ordinaryQuery i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (output_multipliers_positive N h c hp F hF i).le (hs _ _))
  have hS := S_positive N h c hp
  have h1 : 0 ≤ 2 * h * c * (∑ i, slack data (starQuery N) (ordinaryQuery i)) := by positivity
  have h2 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hs (starQuery N) (outputQuery N))
  have h3 := mul_nonneg (by positivity : 0 ≤ 2 * S N h c) (hs (outputQuery N) (starQuery N))
  linarith [sq_nonneg ‖z‖]

theorem forward_gradient_bound_of_nonnegative {d : ℕ} (I : Instance d 1 1)
    (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hid : 0 ≤ ‖I.initial - I.minimizer‖ ^ 2 -
      (S N h c) ^ 2 * ‖gradient I.f (output I N h c)‖ ^ 2) :
    ‖gradient I.f (output I N h c)‖ ≤ 1 / S N h c := by
  have hS := S_positive N h c hp
  have hr : ‖I.initial - I.minimizer‖ ^ 2 ≤ 1 := by
    nlinarith [I.radius, norm_nonneg (I.initial - I.minimizer)]
  have hsq : (S N h c * ‖gradient I.f (output I N h c)‖) ^ 2 ≤ 1 := by
    nlinarith only [hid, hr]
  have hprod : S N h c * ‖gradient I.f (output I N h c)‖ ≤ 1 := by nlinarith only [hsq]
  exact (le_div_iff₀ hS).mpr (by simpa [mul_comm] using hprod)

end
end CriticalExtrapolation.Paper
