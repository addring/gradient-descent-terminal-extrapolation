import PaperFramework.TrialReferenceTail
import PaperFramework.TrialReferenceModel

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem reciprocal_right_product_sum (N : ℕ) :
    (∑ i : Fin N, 1 / (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1))) =
      1 - 1 / ((N : ℝ) + 1) := by
  have hh : (∑ i : Fin N, 1 / (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1))) =
      ∑ i : Fin N, 1 / (((N - i.val : ℕ) : ℝ) * (((N - i.val : ℕ) : ℝ) + 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.le_of_lt i.isLt)]
  rw [hh, trial_reverse_sum N (fun j => 1 / ((j : ℝ) * ((j : ℝ) + 1)))]
  simp only [Nat.cast_add, Nat.cast_one]
  simp_rw [show ∀ k : ℕ, ((k : ℝ) + 1) * ((k : ℝ) + 1 + 1) =
    ((k : ℝ) + 1) * ((k : ℝ) + 2) from fun _ => by ring]
  exact trial_reciprocal_product_sum N

theorem reciprocal_shifted_right_sum (N : ℕ) :
    (∑ i : Fin N, 1 / ((N : ℝ) - i.val + 1)) =
      harmonicSum N - (N : ℝ) / ((N : ℝ) + 1) := by
  have hp : (∑ i : Fin N, (1 / ((N : ℝ) - i.val) -
      1 / ((N : ℝ) - i.val + 1))) =
      ∑ i : Fin N, 1 / (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
    have hj : 0 < (N : ℝ) - i.val := sub_pos.mpr hi
    field_simp [ne_of_gt hj, ne_of_gt (show 0 < (N : ℝ) - i.val + 1 by linarith)]
    <;> ring
  rw [Finset.sum_sub_distrib, trial_reciprocal_right_sum, reciprocal_right_product_sum] at hp
  have he : 1 - 1 / ((N : ℝ) + 1) = (N : ℝ) / ((N : ℝ) + 1) := by
    field_simp [ne_of_gt (show 0 < (N : ℝ) + 1 by positivity)]
    <;> ring
  rw [he] at hp
  linarith only [hp]

/-- Exact control of the left-tail remainder by a finite telescoping sum. -/
theorem trialLeft_remainder_weighted_sum (N : ℕ) (t : ℝ) (ht : 1 ≤ t) :
    (∑ i : Fin N, (tail (trialLeft N t) i.val -
      ((N : ℝ) - i.val) / ((N : ℝ) + 2 * t)) /
        (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1))) =
      (∑ i : Fin N, ((i.val : ℝ) + 1) / ((i.val : ℝ) + 2 * t)) /
        (((N : ℝ) + 2 * t) * ((N : ℝ) + 1)) := by
  let H : ℝ := ∑ i : Fin N, 1 / ((i.val : ℝ) + 2 * t)
  have hT : 0 < (N : ℝ) + 2 * t := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have htail := reciprocal_weighted_tail_identity N (trialLeft N t)
  change (∑ i : Fin N, tail (trialLeft N t) i.val /
      (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1))) =
      (∑ i : Fin N, (1 / ((i.val : ℝ) + 2 * t)) / ((N : ℝ) - i.val)) -
        H / ((N : ℝ) + 1) at htail
  have hcross : (∑ i : Fin N, (1 / ((i.val : ℝ) + 2 * t)) / ((N : ℝ) - i.val)) =
      (H + harmonicSum N) / ((N : ℝ) + 2 * t) := by
    calc
      _ = ∑ i : Fin N, (1 / ((i.val : ℝ) + 2 * t) + 1 / ((N : ℝ) - i.val)) /
          ((N : ℝ) + 2 * t) := by
        apply Finset.sum_congr rfl
        intro i _
        have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
        have hu : 0 < (i.val : ℝ) + 2 * t := by have := Nat.cast_nonneg (α := ℝ) i.val; linarith
        field_simp [ne_of_gt hT, ne_of_gt hu, ne_of_gt (sub_pos.mpr hi)]
        <;> ring
      _ = _ := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, trial_reciprocal_right_sum]
  have hnum : (∑ i : Fin N, ((i.val : ℝ) + 1) / ((i.val : ℝ) + 2 * t)) =
      (N : ℝ) + (1 - 2 * t) * H := by
    have hp : ∀ i : Fin N, ((i.val : ℝ) + 1) / ((i.val : ℝ) + 2 * t) =
        1 + (1 - 2 * t) * (1 / ((i.val : ℝ) + 2 * t)) := by
      intro i
      have hu : 0 < (i.val : ℝ) + 2 * t := by have := Nat.cast_nonneg (α := ℝ) i.val; linarith
      field_simp [ne_of_gt hu]
      <;> ring
    simp_rw [hp]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rfl
  have hp : ∀ i : Fin N, (tail (trialLeft N t) i.val -
      ((N : ℝ) - i.val) / ((N : ℝ) + 2 * t)) /
      (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1)) =
      tail (trialLeft N t) i.val / (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1)) -
        (1 / ((N : ℝ) + 2 * t)) * (1 / ((N : ℝ) - i.val + 1)) := by
    intro i
    have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
    have hj : 0 < (N : ℝ) - i.val := sub_pos.mpr hi
    field_simp [ne_of_gt hT, ne_of_gt hj, ne_of_gt (show 0 < (N : ℝ) - i.val + 1 by linarith)]
    <;> ring
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, htail, hcross,
    reciprocal_shifted_right_sum N, hnum]
  field_simp [ne_of_gt hT, ne_of_gt (show 0 < (N : ℝ) + 1 by positivity)]
  <;> ring

end
end CriticalExtrapolation.Paper
