import PaperFramework.FlowTransport

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def samplePotential {N d : ℕ} (data : Sample N d) (i : Query N) : ℝ :=
  data.value i - inner ℝ (data.g i) (data.x i) + ‖data.g i‖ ^ 2 / 2

/-- The directed slack in the potential form used in the paper's algebraic proof. -/
theorem slack_potential_identity {N d : ℕ} (data : Sample N d) (i j : Query N) :
    slack data i j = samplePotential data i - samplePotential data j +
      inner ℝ (data.g i - data.g j) (data.x i - data.g i) := by
  simp only [slack, samplePotential, norm_sub_sq_real, inner_sub_left, inner_sub_right,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm (data.g j) (data.g i)]
  ring

theorem flow_divergence_pairing {N : ℕ} (F : Flow N) (v : Vec N) :
    (∑ e ∈ edges N, F e * (v e.1 - zeroExtend v e.2.val)) =
      ∑ i, (outflow F i - inflow F i) * v i := by
  simp_rw [← flow_basis_difference_apply v, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  have hf := flow_basis_flux F (fun _ => 1) i
  simpa only [mul_one] using congrArg (fun r : ℝ => r * v i) hf

theorem admissible_flow_pairing {N : ℕ} (F : Flow N) (hF : AdmissibleFlow F) (v : Vec N) :
    (∑ e ∈ edges N, F e * (v e.1 - zeroExtend v e.2.val)) = ∑ i, v i := by
  rw [flow_divergence_pairing]
  simp_rw [hF.2, one_mul]

theorem flow_pairing_with_sink {N : ℕ} (F : Flow N) (v : Fin (N + 1) → ℝ) :
    (∑ e ∈ edges N, F e * (v e.1.castSucc - v e.2)) =
      ∑ i, (outflow F i - inflow F i) * (v i.castSucc - v (Fin.last N)) := by
  let p : Vec N := fun i => v i.castSucc - v (Fin.last N)
  have hp : ∀ j : Fin (N + 1), zeroExtend p j.val = v j - v (Fin.last N) := by
    intro j
    by_cases hj : j.val < N
    · simp only [zeroExtend, dif_pos hj, p]
      congr 2
    · have hjlast : j = Fin.last N := by apply Fin.ext; simp; omega
      simp [zeroExtend, hj, hjlast]
  have he : ∀ e : Edge N, p e.1 - zeroExtend p e.2.val = v e.1.castSucc - v e.2 := by
    intro e
    rw [hp]
    dsimp [p]
    ring
  simpa only [he, p] using flow_divergence_pairing F p

/-- Cancellation of every function-value potential, including the output sink. -/
theorem forward_potentials_cancel {N : ℕ} (h c : ℝ) (F : Flow N) (A : Query N → ℝ) :
    2 * h * c * (∑ i : Fin N, (A (starQuery N) - A (ordinaryQuery i))) +
      2 * (A (starQuery N) - A (outputQuery N)) +
      2 * S N h c * (A (outputQuery N) - A (starQuery N)) +
      (∑ e ∈ edges N, lambda h c F e * (A (ordinaryQuery e.1) - A (some e.2))) +
      (∑ i, outputMultiplier h c F i * (A (outputQuery N) - A (ordinaryQuery i))) = 0 := by
  have he := flow_pairing_with_sink (lambda h c F) (fun j => A (some j))
  change (∑ e ∈ edges N, lambda h c F e * (A (ordinaryQuery e.1) - A (some e.2))) =
    ∑ i, (outflow (lambda h c F) i - inflow (lambda h c F) i) *
      (A (ordinaryQuery i) - A (outputQuery N)) at he
  rw [he]
  have hcombine : (∑ i, (outflow (lambda h c F) i - inflow (lambda h c F) i) *
        (A (ordinaryQuery i) - A (outputQuery N))) +
      (∑ i, outputMultiplier h c F i * (A (outputQuery N) - A (ordinaryQuery i))) =
      2 * h * c * ∑ i, (A (ordinaryQuery i) - A (outputQuery N)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold outputMultiplier
    ring
  have hstar : 2 * h * c * (∑ i : Fin N, (A (starQuery N) - A (ordinaryQuery i))) +
      2 * h * c * (∑ i : Fin N, (A (ordinaryQuery i) - A (outputQuery N))) =
      2 * h * c * (N : ℝ) * (A (starQuery N) - A (outputQuery N)) := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    simp only [sub_add_sub_cancel, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hg := hcombine
  unfold S
  linear_combination hg + hstar

end
end CriticalExtrapolation.Paper
