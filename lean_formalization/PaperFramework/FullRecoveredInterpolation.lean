import PaperFramework.FullRecoveredSmoothness

namespace CriticalExtrapolation.Paper
noncomputable section

/-- General interpolation uses the directed slack j→i, with its full function value. -/
theorem full_affine_sample_slack_identity {N d : ℕ} (data : Sample N d) (i j : Query N) :
    interpolationIntercept data i -
      (inner ℝ (data.x j - data.g j) (data.g i - data.g j) + interpolationIntercept data j) =
      slack data j i := by
  simp only [interpolationIntercept, slack, inner_sub_left, inner_sub_right,
    norm_sub_sq_real, real_inner_self_eq_norm_sq]
  rw [real_inner_comm (data.g i) (data.x j), real_inner_comm (data.g j) (data.x j)]
  ring

theorem fullConjugatePotential_at_sample {N d : ℕ} (data : Sample N d)
    (hslack : ∀ i j, 0 ≤ slack data i j) (i : Query N) :
    fullConjugatePotential data (data.g i) = inner ℝ (data.g i) (data.x i) - data.value i := by
  classical
  have hterm : ∀ j, inner ℝ (data.x j - data.g j) (data.g i - data.g j) +
      interpolationIntercept data j ≤ interpolationIntercept data i := by
    intro j
    exact sub_nonneg.mp (by rw [full_affine_sample_slack_identity]; exact hslack j i)
  have hmaxle : fullConjugateAffineMaximum data (data.g i) ≤ interpolationIntercept data i := by
    unfold fullConjugateAffineMaximum
    apply Finset.sup'_le
    intro j _
    exact hterm j
  have hmaxge : interpolationIntercept data i ≤ fullConjugateAffineMaximum data (data.g i) := by
    have h := Finset.le_sup' (fun j : Query N =>
      inner ℝ (data.x j - data.g j) (data.g i - data.g j) + interpolationIntercept data j)
        (Finset.mem_univ i)
    simpa only [sub_self, inner_zero_right, zero_add] using h
  have hmax := le_antisymm hmaxle hmaxge
  rw [fullConjugatePotential, hmax, interpolationIntercept]
  ring

theorem full_sample_gradient_conjugate_minimizer {N d : ℕ} (data : Sample N d)
    (hslack : ∀ i j, 0 ≤ slack data i j) (i : Query N) :
    FullConjugateMinimizer data (data.x i) (data.g i) := by
  intro v
  rw [fullConjugatePotential_at_sample data hslack i, real_inner_comm (data.g i) (data.x i)]
  have hs := fullConjugatePotential_support_lower data i v
  simp only [interpolationIntercept, inner_sub_left, inner_sub_right,
    real_inner_self_eq_norm_sq] at hs
  rw [real_inner_comm (data.g i) (data.x i)] at hs
  have hnorm := norm_sub_sq_real (data.g i) v
  nlinarith [sq_nonneg ‖data.g i - v‖]

theorem full_recovered_function_interpolates {N d : ℕ} (data : Sample N d)
    (hslack : ∀ i j, 0 ≤ slack data i j) : Interpolates data (fullRecoveredFunction data) := by
  constructor
  · intro i
    have hi := full_sample_gradient_conjugate_minimizer data hslack i
    rw [full_conjugate_minimizer_recovered_value data (data.x i) (data.g i) hi,
      fullConjugatePotential_at_sample data hslack i, real_inner_comm (data.x i) (data.g i)]
    ring
  · intro i
    exact (full_recovered_hasGradientAt data (data.x i) (data.g i)
      (full_sample_gradient_conjugate_minimizer data hslack i)).gradient

theorem smooth_convex_interpolation_sufficient_proved {N d : ℕ} (data : Sample N d)
    (hslack : ∀ i j, 0 ≤ slack data i j) :
    ∃ f : Space d → ℝ, SmoothConvexOne f ∧ Interpolates data f := by
  exact ⟨fullRecoveredFunction data, (full_recovered_function_global_smoothness_proved data).1,
    full_recovered_function_interpolates data hslack⟩

end
end CriticalExtrapolation.Paper
