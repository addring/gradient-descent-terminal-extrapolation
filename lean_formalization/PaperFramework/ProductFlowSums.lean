import PaperFramework.FiniteIntervalSums

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def flowSurvival (π : ℕ → ℝ) (i j : ℕ) : ℝ := ∏ k ∈ Finset.Ioo i j, (1 - π k)

theorem flowSurvival_adjacent (π : ℕ → ℝ) (i : ℕ) : flowSurvival π i (i + 1) = 1 := by
  have he : Finset.Ioo i (i + 1) = ∅ := by ext k; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega
  simp [flowSurvival, he]

theorem flowSurvival_step (π : ℕ → ℝ) (i j : ℕ) (hij : i < j) :
    flowSurvival π i (j + 1) = flowSurvival π i j * (1 - π j) := by
  have he : Finset.Ioo i (j + 1) = insert j (Finset.Ioo i j) := by
    ext k
    simp only [Finset.mem_Ioo, Finset.mem_insert]
    omega
  unfold flowSurvival
  rw [he, Finset.prod_insert (by simp)]
  ring

theorem natural_interval_sum_difference (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b, (f k - f (k + 1))) = f a - f b := by
  have hs : ∀ n, (∑ k ∈ Finset.range n, (f k - f (k + 1))) = f 0 - f n := by
    intro n
    have he := sum_differences f n
    simp only [Finset.sum_sub_distrib] at he ⊢
    linarith
  rw [Finset.sum_Ico_eq_sub _ hab, hs, hs]
  ring

theorem productFlow_exit_mass (π : ℕ → ℝ) (N i : ℕ) (hi : i < N) (hN : π N = 1) :
    (∑ j ∈ Finset.Ico (i + 1) (N + 1), π j * flowSurvival π i j) = 1 := by
  have hpoint : ∀ j ∈ Finset.Ico (i + 1) (N + 1),
      π j * flowSurvival π i j = flowSurvival π i j - flowSurvival π i (j + 1) := by
    intro j hj
    rw [flowSurvival_step π i j (by have := Finset.mem_Ico.mp hj; omega)]
    ring
  rw [Finset.sum_congr rfl hpoint,
    natural_interval_sum_difference (flowSurvival π i) (i + 1) (N + 1) (by omega),
    flowSurvival_adjacent, flowSurvival_step π i N hi, hN]
  ring

theorem productFlow_weighted_exit (π β ℓ : ℕ → ℝ) (N i : ℕ) (hi : i < N)
    (hN : π N = 1)
    (hrec : ∀ j, 0 < j → j ≤ N →
      ℓ (j - 1) = β (j - 1) - β j + (1 - π j) * ℓ j) :
    (∑ j ∈ Finset.Ico (i + 1) (N + 1),
      π j * flowSurvival π i j * (β i - β j)) = ℓ i := by
  let z : ℕ → ℝ := fun j => flowSurvival π i j * (β i - β (j - 1) + ℓ (j - 1))
  have hpoint : ∀ j ∈ Finset.Ico (i + 1) (N + 1),
      π j * flowSurvival π i j * (β i - β j) = z j - z (j + 1) := by
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    dsimp [z]
    rw [flowSurvival_step π i j (by omega), hrec j (by omega) (by omega)]
    ring
  rw [Finset.sum_congr rfl hpoint,
    natural_interval_sum_difference z (i + 1) (N + 1) (by omega)]
  dsimp [z]
  rw [flowSurvival_adjacent, flowSurvival_step π i N hi, hN]
  simp

theorem productFlow_arrival_mass (π : ℕ → ℝ) (i : ℕ) :
    (∑ k ∈ Finset.range i, (1 + (k : ℝ) * π k) * flowSurvival π k i) = i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, flowSurvival_adjacent]
    have heq : (∑ k ∈ Finset.range i, (1 + (k : ℝ) * π k) * flowSurvival π k (i + 1)) =
        (∑ k ∈ Finset.range i, (1 + (k : ℝ) * π k) * flowSurvival π k i) * (1 - π i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [flowSurvival_step π k i (Finset.mem_range.mp hk)]
      ring
    rw [heq, ih]
    push_cast
    ring

theorem sum_outgoing_natural {N : ℕ} (F : ℕ → ℕ → ℝ) (i : Fin N) :
    (∑ e ∈ (edges N).filter (fun e => e.1 = i), F e.1.val e.2.val) =
      ∑ j ∈ Finset.Ico (i.val + 1) (N + 1), F i.val j := by
  apply Finset.sum_bij (fun e _ => e.2.val)
  · intro e he
    have he' := Finset.mem_filter.mp he
    have heorder := (Finset.mem_filter.mp he'.1).2
    rw [he'.2] at heorder
    exact Finset.mem_Ico.mpr ⟨by omega, e.2.isLt⟩
  · intro e he e' he' heq
    have hel := (Finset.mem_filter.mp he).2
    have her := (Finset.mem_filter.mp he').2
    exact Prod.ext (hel.trans her.symm) (Fin.ext heq)
  · intro j hj
    have hj' := Finset.mem_Ico.mp hj
    refine ⟨(i, ⟨j, hj'.2⟩), ?_, rfl⟩
    simp only [Finset.mem_filter, edges, Finset.mem_univ, true_and]
    exact ⟨by omega, trivial⟩
  · intro e he
    rw [(Finset.mem_filter.mp he).2]

theorem sum_incoming_natural {N : ℕ} (F : ℕ → ℕ → ℝ) (i : Fin N) :
    (∑ e ∈ (edges N).filter (fun e => e.2.val = i.val), F e.1.val e.2.val) =
      ∑ j ∈ Finset.range i.val, F j i.val := by
  apply Finset.sum_bij (fun e _ => e.1.val)
  · intro e he
    have he' := Finset.mem_filter.mp he
    have heorder := (Finset.mem_filter.mp he'.1).2
    rw [he'.2] at heorder
    exact Finset.mem_range.mpr heorder
  · intro e he e' he' heq
    have hel := (Finset.mem_filter.mp he).2
    have her := (Finset.mem_filter.mp he').2
    exact Prod.ext (Fin.ext heq) (Fin.ext (hel.trans her.symm))
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    refine ⟨(⟨j, by omega⟩, i.castSucc), ?_, rfl⟩
    simp only [Finset.mem_filter, edges, Finset.mem_univ, true_and]
    exact ⟨hj', rfl⟩
  · intro e he
    rw [(Finset.mem_filter.mp he).2]

end
end CriticalExtrapolation.Paper
