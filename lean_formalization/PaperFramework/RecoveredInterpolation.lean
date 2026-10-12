import PaperFramework.RecoveredSmoothness

namespace CriticalExtrapolation.Paper
noncomputable section

theorem conjugatePotential_at_sample {N d : ℕ} (data : Sample N d)
    (hvalue : ∀ i, data.value i = inner ℝ (data.g i) (data.x i) - ‖data.g i‖ ^ 2 / 2)
    (hslack : ∀ i j, 0 ≤ slack data i j) (i : Query N) :
    conjugatePotential data (data.g i) = ‖data.g i‖ ^ 2 / 2 := by
  classical
  have hterm : ∀ j, inner ℝ (data.x j - data.g j) (data.g i - data.g j) ≤ 0 := by
    intro j
    have hs := hslack j i
    rw [special_value_slack_identity data hvalue j i, real_inner_comm] at hs
    rw [show data.g i - data.g j = -(data.g j - data.g i) by abel, inner_neg_right]
    exact neg_nonpos.mpr hs
  have hmaxle : conjugateAffineMaximum data (data.g i) ≤ 0 := by
    unfold conjugateAffineMaximum
    apply Finset.sup'_le
    intro j _
    exact hterm j
  have hmaxge : 0 ≤ conjugateAffineMaximum data (data.g i) := by
    have h := Finset.le_sup' (fun j : Query N =>
      inner ℝ (data.x j - data.g j) (data.g i - data.g j)) (Finset.mem_univ i)
    simpa only [sub_self, inner_zero_right] using h
  have hmax : conjugateAffineMaximum data (data.g i) = 0 := le_antisymm hmaxle hmaxge
  rw [conjugatePotential, ← conjugateAffineMaximum_eq_sup, hmax, add_zero]

theorem sample_gradient_conjugate_minimizer {N d : ℕ} (data : Sample N d)
    (hvalue : ∀ i, data.value i = inner ℝ (data.g i) (data.x i) - ‖data.g i‖ ^ 2 / 2)
    (hslack : ∀ i j, 0 ≤ slack data i j) (i : Query N) :
    ConjugateMinimizer data (data.x i) (data.g i) := by
  intro v
  rw [conjugatePotential_at_sample data hvalue hslack i]
  have hs := conjugatePotential_support_lower data i v
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq] at hs
  have hnorm := norm_sub_sq_real (data.g i) v
  nlinarith [sq_nonneg ‖data.g i - v‖]

theorem recovered_function_interpolates_proved {N d : ℕ} (data : Sample N d)
    (hvalue : ∀ i, data.value i = inner ℝ (data.g i) (data.x i) - ‖data.g i‖ ^ 2 / 2)
    (hslack : ∀ i j, 0 ≤ slack data i j) :
    Interpolates data (recoveredFunction data) := by
  constructor
  · intro i
    have hi := sample_gradient_conjugate_minimizer data hvalue hslack i
    rw [conjugate_minimizer_recovered_value data (data.x i) (data.g i) hi,
      conjugatePotential_at_sample data hvalue hslack i, hvalue i,
      real_inner_comm (data.x i) (data.g i)]
  · intro i
    exact (recovered_hasGradientAt data (data.x i) (data.g i)
      (sample_gradient_conjugate_minimizer data hvalue hslack i)).gradient

end
end CriticalExtrapolation.Paper
