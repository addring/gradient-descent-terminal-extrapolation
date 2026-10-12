import PaperFramework.NegativeRadius
import PaperFramework.FlowBasics

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem perturbationGradient_sum {N : ℕ} (h c ε : ℝ) (β : Vec N) (s : Finset (Fin N)) :
    (∑ i ∈ s, perturbationGradient h c ε β i) =
      vec2 ((s.card : ℝ) + (∑ i ∈ s, backwardA h c β i) * ε ^ 2 +
        (∑ i ∈ s, backwardB h c β i) * ε ^ 4) ((∑ i ∈ s, β i) * ε) := by
  unfold perturbationGradient
  rw [vec2_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.sum_mul]

theorem perturbation_ordinary_residual (N : ℕ) (h c ε : ℝ) (β : Vec N) (i : Fin N) :
    (perturbationSample h c ε β).x (ordinaryQuery i) -
      (perturbationSample h c ε β).g (ordinaryQuery i) =
      vec2 (queryK N h c i + applyT h c (backwardA h c β) i * ε ^ 2 +
        applyT h c (backwardB h c β) i * ε ^ 4) (applyT h c β i * ε) := by
  simp only [perturbationSample, ordinaryQuery, Fin.val_castSucc, dif_pos i.isLt]
  change perturbationInitial h c ε β - h •
      (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val < i.val), perturbationGradient h c ε β j) -
        perturbationGradient h c ε β i = _
  rw [perturbationInitial_coordinates, perturbationGradient_sum, vec2_smul]
  unfold perturbationGradient
  rw [vec2_sub, vec2_sub]
  have hcard : ((Finset.univ.filter (fun j : Fin N => j.val < i.val)).card : ℝ) = i.val := by
    simp only [← Fin.lt_def, Finset.filter_gt_eq_Iio, Fin.card_Iio]
  rw [hcard]
  simp only [← Fin.lt_def]
  simp only [S, queryK, applyT]
  congr 1 <;> ring

theorem perturbation_ordinary_gradient (N : ℕ) (h c ε : ℝ) (β : Vec N) (i : Fin N) :
    (perturbationSample h c ε β).g (ordinaryQuery i) = perturbationGradient h c ε β i := by
  simp [perturbationSample, ordinaryQuery, i.isLt]

theorem perturbation_extended_gradient (N : ℕ) (h c ε : ℝ) (β : Vec N) (j : Fin (N + 1)) :
    (perturbationSample h c ε β).g (some j) =
      vec2 (1 + zeroExtend (backwardA h c β) j.val * ε ^ 2 +
        zeroExtend (backwardB h c β) j.val * ε ^ 4) (zeroExtend β j.val * ε) := by
  by_cases hj : j.val < N
  · simp [perturbationSample, perturbationGradient, zeroExtend, hj]
  · simp [perturbationSample, zeroExtend, hj]

/-- Equation (11.4) in its actual parameter domain; K_i is nonzero. -/
theorem ordinary_slack_polynomial {N : ℕ} (h c ε : ℝ) (hp : Parameters N h c) (β : Vec N)
    (i : Fin N) (j : Fin (N + 1)) :
    let A := backwardA h c β
    let B := backwardB h c β
    let ΔA := A i - zeroExtend A j.val
    let ΔB := B i - zeroExtend B j.val
    let Δβ := β i - zeroExtend β j.val
    let P := applyT h c A i
    let V := applyT h c B i
    slack (perturbationSample h c ε β) (ordinaryQuery i) (some j) =
      queryK N h c i * (ΔA + slope h c β i * Δβ) * ε ^ 2 +
      (queryK N h c i * ΔB + P * ΔA) * ε ^ 4 +
      (V * ΔA + P * ΔB) * ε ^ 6 + V * ΔB * ε ^ 8 := by
  dsimp only
  rw [perturbation_slack_identity, perturbation_ordinary_residual,
    perturbation_extended_gradient N h c ε β j, perturbation_ordinary_gradient]
  unfold perturbationGradient
  rw [vec2_sub, vec2_inner]
  have hK : queryK N h c i ≠ 0 := ne_of_gt (queryK_positive N h c hp i)
  have hT : applyT h c β i = queryK N h c i * slope h c β i := by
    unfold slope
    field_simp [hK]
  rw [hT]
  ring

/-- The old parameter-free skeleton was false at h=0; the paper excludes this case. -/
theorem ordinary_slack_parameter_counterexample :
    slack (perturbationSample (N := 1) 0 1 1 (fun _ => 1))
      (ordinaryQuery ⟨0, by decide⟩) (outputQuery 1) = -1 := by
  have hA : backwardA (N := 1) 0 1 (fun _ => 1) = 0 := by
    funext i
    simp [backwardA, slope, queryK]
  have hB : backwardB (N := 1) 0 1 (fun _ => 1) = 0 := by
    funext i
    simp [backwardB, queryK]
  rw [perturbation_slack_identity]
  norm_num [perturbationSample, ordinaryQuery, outputQuery, perturbationInitial,
    perturbationGradient, hA, hB, vec2_sub, vec2_inner]

end
end CriticalExtrapolation.Paper
