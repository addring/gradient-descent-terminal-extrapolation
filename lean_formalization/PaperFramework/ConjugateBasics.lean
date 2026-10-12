import PaperFramework.NegativeAlgebra

namespace CriticalExtrapolation.Paper
noncomputable section

def ConjugateMinimizer {N d : ℕ} (data : Sample N d) (x u : Space d) : Prop :=
  ∀ v, conjugatePotential data u - inner ℝ x u ≤ conjugatePotential data v - inner ℝ x v

theorem conjugate_minimizer_recovered_value {N d : ℕ} (data : Sample N d)
    (x u : Space d) (hu : ConjugateMinimizer data x u) :
    recoveredFunction data x = inner ℝ x u - conjugatePotential data u := by
  have hbdd : BddAbove {r | ∃ v, r = inner ℝ x v - conjugatePotential data v} := by
    refine ⟨inner ℝ x u - conjugatePotential data u, ?_⟩
    rintro r ⟨v, rfl⟩
    have hv := hu v
    linarith
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨inner ℝ x u - conjugatePotential data u, u, rfl⟩
    · rintro r ⟨v, rfl⟩
      have hv := hu v
      linarith
  · exact le_csSup hbdd ⟨u, rfl⟩

theorem recoveredFunction_nonnegative_of_zero_potential {N d : ℕ} (data : Sample N d)
    (hexists : ∀ x, ∃ u, ConjugateMinimizer data x u)
    (hzero : conjugatePotential data 0 = 0) : ∀ x, 0 ≤ recoveredFunction data x := by
  intro x
  obtain ⟨u, hu⟩ := hexists x
  rw [conjugate_minimizer_recovered_value data x u hu]
  have hbound := hu 0
  simp only [hzero, inner_zero_right, sub_zero] at hbound
  linarith

theorem perturbation_zero_conjugate_potential (N : ℕ) (h c ε : ℝ) (β : Vec N)
    (hslack : ∀ i j, 0 ≤ slack (perturbationSample h c ε β) i j) :
    conjugatePotential (perturbationSample h c ε β) 0 = 0 := by
  let data := perturbationSample h c ε β
  have hg : data.g (starQuery N) = 0 := rfl
  have hx : data.x (starQuery N) = 0 := rfl
  have hterm : ∀ i, inner ℝ (data.x i - data.g i) ((0 : Space 2) - data.g i) ≤ 0 := by
    intro i
    have hs := hslack i (starQuery N)
    rw [perturbation_slack_identity] at hs
    change 0 ≤ inner ℝ (data.g i - data.g (starQuery N)) (data.x i - data.g i) at hs
    rw [hg, sub_zero, real_inner_comm] at hs
    simpa only [zero_sub, inner_neg_right] using neg_nonpos.mpr hs
  have hbdd : BddAbove {r : ℝ | ∃ i, r = inner ℝ (data.x i - data.g i) (0 - data.g i)} := by
    refine ⟨0, ?_⟩
    rintro r ⟨i, rfl⟩
    exact hterm i
  have hmem : (0 : ℝ) ∈ {r | ∃ i, r = inner ℝ (data.x i - data.g i) (0 - data.g i)} := by
    refine ⟨starQuery N, ?_⟩
    simp [hx, hg]
  have hsup : sSup {r : ℝ | ∃ i, r = inner ℝ (data.x i - data.g i) (0 - data.g i)} = 0 := by
    apply le_antisymm
    · exact csSup_le ⟨0, hmem⟩ (by rintro r ⟨i, rfl⟩; exact hterm i)
    · exact le_csSup hbdd hmem
  change ‖(0 : Space 2)‖ ^ 2 / 2 + _ = 0
  rw [hsup]
  simp

end
end CriticalExtrapolation.Paper
