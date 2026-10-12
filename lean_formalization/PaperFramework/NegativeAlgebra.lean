import PaperFramework.TailTransform
import PaperFramework.ForwardFlowAlgebra

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem difference_tail_integral {N : ℕ} (w : Vec N) (i : Fin N) :
    difference (fun j : Fin N => tail w j.val) i = w i := by
  have hs := tail_step w i
  by_cases hi : i.val + 1 < N
  · simpa only [difference, zeroExtend, dif_pos hi] using (sub_eq_iff_eq_add.mpr (by linarith : tail w i.val = w i + tail w (i.val + 1)))
  · have heq : i.val + 1 = N := by omega
    rw [heq, tail_terminal] at hs
    simp only [difference, zeroExtend, dif_neg hi, sub_zero]
    simpa using hs

theorem difference_neg {N : ℕ} (v : Vec N) (i : Fin N) : difference (-v) i = -difference v i := by
  unfold difference zeroExtend
  split_ifs <;> simp <;> ring

/-- The output boundary remains zero only for differences, exactly as in (11.1). -/
theorem backward_recursions {N : ℕ} (h c : ℝ) (β : Vec N) (i : Fin N) :
    difference (backwardA h c β) i = -difference β i * slope h c β i ∧
    difference (backwardB h c β) i =
      (1 - difference (backwardA h c β) i * applyT h c (backwardA h c β) i) /
        queryK N h c i := by
  have hA : backwardA h c β = -(fun j : Fin N => tail (fun k => difference β k * slope h c β k) j.val) := by
    funext j
    simp only [backwardA, tail, Fin.le_def, Pi.neg_apply]
  have hB : backwardB h c β = fun j : Fin N => tail
      (fun k => (1 - difference (backwardA h c β) k * applyT h c (backwardA h c β) k) /
        queryK N h c k) j.val := by
    funext j
    simp only [backwardB, tail, Fin.le_def]
  constructor
  · rw [hA, difference_neg, difference_tail_integral]
    ring
  · rw [hB, difference_tail_integral]

theorem special_value_slack_identity {N d : ℕ} (data : Sample N d)
    (hvalue : ∀ i, data.value i = inner ℝ (data.g i) (data.x i) - ‖data.g i‖ ^ 2 / 2)
    (i j : Query N) :
    slack data i j = inner ℝ (data.g i - data.g j) (data.x i - data.g i) := by
  rw [slack_potential_identity]
  have hzero : ∀ k, samplePotential data k = 0 := by intro k; simp [samplePotential, hvalue k]
  rw [hzero, hzero]
  ring

/-- Every assigned value in the counterexample uses the same supporting quadratic. -/
theorem perturbation_slack_identity {N : ℕ} (h c ε : ℝ) (β : Vec N)
    (i j : Query N) :
    slack (perturbationSample h c ε β) i j =
      inner ℝ ((perturbationSample h c ε β).g i - (perturbationSample h c ε β).g j)
        ((perturbationSample h c ε β).x i - (perturbationSample h c ε β).g i) := by
  exact special_value_slack_identity _ (fun _ => rfl) i j

end
end CriticalExtrapolation.Paper
