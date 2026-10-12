import PaperFramework.NegativePolynomial

namespace CriticalExtrapolation.Paper
open scoped BigOperators
open Filter Topology
noncomputable section

theorem perturbation_distinguished_residual (N : ℕ) (h c ε : ℝ) (β : Vec N) :
    (perturbationSample h c ε β).x (starQuery N) -
        (perturbationSample h c ε β).g (starQuery N) = 0 ∧
      (perturbationSample h c ε β).x (outputQuery N) -
        (perturbationSample h c ε β).g (outputQuery N) = 0 := by
  simp [perturbationSample, starQuery, outputQuery]

theorem perturbation_distinguished_slacks (N : ℕ) (h c ε : ℝ) (β : Vec N)
    (j : Query N) :
    slack (perturbationSample h c ε β) (starQuery N) j = 0 ∧
      slack (perturbationSample h c ε β) (outputQuery N) j = 0 := by
  obtain ⟨hs, ho⟩ := perturbation_distinguished_residual N h c ε β
  constructor <;> rw [perturbation_slack_identity]
  · rw [hs, inner_zero_right]
  · rw [ho, inner_zero_right]

/-- The quartic coefficient is exactly one, also for the last ordinary-to-output edge. -/
theorem perturbation_adjacent_slack (N : ℕ) (h c ε : ℝ) (hp : Parameters N h c)
    (β : Vec N) (i : Fin N) :
    let A := backwardA h c β
    let B := backwardB h c β
    let P := applyT h c A i
    let V := applyT h c B i
    slack (perturbationSample h c ε β) (ordinaryQuery i) (some i.succ) =
      ε ^ 4 * (1 + (V * difference A i + P * difference B i) * ε ^ 2 +
        V * difference B i * ε ^ 4) := by
  dsimp only
  rw [ordinary_slack_polynomial h c ε hp β]
  dsimp only [Fin.val_succ]
  change queryK N h c i * (difference (backwardA h c β) i +
      slope h c β i * difference β i) * ε ^ 2 +
      (queryK N h c i * difference (backwardB h c β) i +
        applyT h c (backwardA h c β) i * difference (backwardA h c β) i) * ε ^ 4 +
      (applyT h c (backwardB h c β) i * difference (backwardA h c β) i +
        applyT h c (backwardA h c β) i * difference (backwardB h c β) i) * ε ^ 6 +
      applyT h c (backwardB h c β) i * difference (backwardB h c β) i * ε ^ 8 = _
  obtain ⟨hA, hB⟩ := backward_recursions h c β i
  have hsecond : difference (backwardA h c β) i + slope h c β i * difference β i = 0 := by
    rw [hA]
    ring
  have hfourth : queryK N h c i * difference (backwardB h c β) i +
      applyT h c (backwardA h c β) i * difference (backwardA h c β) i = 1 := by
    rw [hB]
    field_simp [ne_of_gt (queryK_positive N h c hp i)]
    <;> ring
  rw [hsecond, hfourth]
  ring

theorem perturbation_adjacent_slack_strict_small (N : ℕ) (h c : ℝ)
    (hp : Parameters N h c) (β : Vec N) (i : Fin N) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀,
      0 < slack (perturbationSample h c ε β) (ordinaryQuery i) (some i.succ) := by
  let A := backwardA h c β
  let B := backwardB h c β
  let P := applyT h c A i
  let V := applyT h c B i
  let p : ℝ → ℝ := fun ε => 1 + (V * difference A i + P * difference B i) * ε ^ 2 +
    V * difference B i * ε ^ 4
  have hpcont : Continuous p := by dsimp [p]; fun_prop
  have hpos : ∀ᶠ ε : ℝ in 𝓝 0, 0 < p ε :=
    continuousAt_const.eventually_lt hpcont.continuousAt (by norm_num [p])
  obtain ⟨l, u, hlu, hall⟩ := hpos.exists_Ioo_subset
  refine ⟨u, hlu.2, ?_⟩
  intro ε hε
  rw [perturbation_adjacent_slack N h c ε hp β i]
  exact mul_pos (pow_pos hε.1 4) (hall ⟨by linarith [hlu.1, hε.1], hε.2⟩)

end
end CriticalExtrapolation.Paper
