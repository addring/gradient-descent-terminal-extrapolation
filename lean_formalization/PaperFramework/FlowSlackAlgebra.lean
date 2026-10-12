import PaperFramework.FlowTrajectory
import PaperFramework.FlowTransport

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def translatedSample {N d : ℕ} (data : Sample N d) (a : Space d) : Sample N d where
  x := fun i => data.x i - a
  g := data.g
  value := data.value

theorem translated_slack {N d : ℕ} (data : Sample N d) (a : Space d) (i j : Query N) :
    slack (translatedSample data a) i j = slack data i j := by
  simp only [slack, translatedSample]
  congr 2
  abel

theorem flow_vector_edge_pairing {N d : ℕ} (F : Flow N)
    (v : Fin N → Space d) (z : Space d) :
    (∑ e ∈ edges N, F e * inner ℝ (v e.1 - flowVectorExtend v e.2) z) =
      ∑ i, (outflow F i - inflow F i) * inner ℝ (v i) z := by
  have hpair := flow_pairing_with_sink F (fun j => inner ℝ (flowVectorExtend v j) z)
  simpa only [flowVectorExtend_ordinary, flowVectorExtend_output, inner_zero_left,
    sub_zero, inner_sub_left] using hpair

theorem flow_lambda_queryK {N : ℕ} (h c : ℝ) (hp : Parameters N h c)
    (F : Flow N) (e : Edge N) :
    lambda h c F e * queryK N h c e.1 = 2 * h * c * S N h c * F e := by
  have hK := ne_of_gt (queryK_positive N h c hp e.1)
  unfold lambda
  field_simp

theorem flow_edge_query_pairing {N d : ℕ} (h c : ℝ) (hp : Parameters N h c)
    (F : Flow N) (hF : AdmissibleFlow F) (v : Fin N → Space d) (q : Space d) :
    (∑ e ∈ edges N, lambda h c F e *
      inner ℝ (v e.1 - flowVectorExtend v e.2) ((queryK N h c e.1) • q)) =
      2 * h * c * S N h c * inner ℝ (∑ i, v i) q := by
  simp_rw [inner_smul_right, ← mul_assoc, flow_lambda_queryK h c hp F]
  simp_rw [mul_assoc (2 * h * c * S N h c)]
  rw [← Finset.mul_sum, flow_vector_edge_pairing]
  simp_rw [hF.2, one_mul]
  rw [sum_inner]

theorem flow_edge_output_pairing {N d : ℕ} (h c : ℝ) (F : Flow N)
    (v : Fin N → Space d) (z : Space d) :
    (∑ e ∈ edges N, lambda h c F e * inner ℝ (v e.1 - flowVectorExtend v e.2) z) -
      (∑ i, outputMultiplier h c F i * inner ℝ (v i) z) =
      2 * h * c * inner ℝ (∑ i, v i) z := by
  rw [flow_vector_edge_pairing, ← Finset.sum_sub_distrib, sum_inner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold outputMultiplier
  ring

/-- Exact weighted slack algebra after translation; the trajectory hypotheses are verified
for actual instances separately, and are not additional assumptions of the certificate. -/
theorem weighted_slack_flow_identity {N d : ℕ} (h c : ℝ) (hp : Parameters N h c)
    (F : Flow N) (hF : AdmissibleFlow F) (data : Sample N d)
    (q z : Space d) (v : Fin N → Space d)
    (hstarx : data.x (starQuery N) = 0) (hstarg : data.g (starQuery N) = 0)
    (hgrad : ∀ j, data.g (some j) = q + flowVectorExtend v j)
    (hout : data.x (outputQuery N) - data.g (outputQuery N) = z)
    (hord : ∀ i, data.x (ordinaryQuery i) - data.g (ordinaryQuery i) =
      (queryK N h c i) • q + z + flowVectorT h c v i) :
    2 * h * c * (∑ i, slack data (starQuery N) (ordinaryQuery i)) +
      2 * slack data (starQuery N) (outputQuery N) +
      2 * S N h c * slack data (outputQuery N) (starQuery N) +
      (∑ e ∈ edges N, lambda h c F e * slack data (ordinaryQuery e.1) (some e.2)) +
      (∑ i, outputMultiplier h c F i * slack data (outputQuery N) (ordinaryQuery i)) =
    2 * S N h c * inner ℝ q z +
      2 * h * c * inner ℝ (∑ i, v i) z +
      2 * h * c * S N h c * inner ℝ (∑ i, v i) q +
      ∑ e ∈ edges N, lambda h c F e *
        inner ℝ (v e.1 - flowVectorExtend v e.2) (flowVectorT h c v e.1) := by
  have hgout : data.g (outputQuery N) = q := by
    simpa only [outputQuery, flowVectorExtend_output, add_zero] using hgrad (Fin.last N)
  have hgord : ∀ i, data.g (ordinaryQuery i) = q + v i := by
    intro i
    simpa only [ordinaryQuery, flowVectorExtend_ordinary] using hgrad i.castSucc
  have hsstar : ∀ j, slack data (starQuery N) j =
      samplePotential data (starQuery N) - samplePotential data j := by
    intro j
    rw [slack_potential_identity, hstarx, hstarg]
    simp
  have hsoutstar : slack data (outputQuery N) (starQuery N) =
      samplePotential data (outputQuery N) - samplePotential data (starQuery N) +
        inner ℝ q z := by
    rw [slack_potential_identity, hout, hgout, hstarg, sub_zero]
  have hsoutord : ∀ i, slack data (outputQuery N) (ordinaryQuery i) =
      samplePotential data (outputQuery N) - samplePotential data (ordinaryQuery i) -
        inner ℝ (v i) z := by
    intro i
    rw [slack_potential_identity, hout, hgout, hgord]
    simp only [sub_add_cancel_left, inner_neg_left]
    ring
  have hsedge : ∀ e : Edge N, slack data (ordinaryQuery e.1) (some e.2) =
      samplePotential data (ordinaryQuery e.1) - samplePotential data (some e.2) +
        inner ℝ (v e.1 - flowVectorExtend v e.2)
          ((queryK N h c e.1) • q + z + flowVectorT h c v e.1) := by
    intro e
    rw [slack_potential_identity, hord, hgord, hgrad]
    congr 2
    abel
  have hpot := forward_potentials_cancel h c F (samplePotential data)
  simp_rw [mul_sub, Finset.sum_sub_distrib] at hpot
  have hquery := flow_edge_query_pairing h c hp F hF v q
  have hz := flow_edge_output_pairing h c F v z
  simp_rw [hsstar, hsoutstar, hsoutord, hsedge, inner_add_right, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linear_combination hpot + hquery + hz

end
end CriticalExtrapolation.Paper
