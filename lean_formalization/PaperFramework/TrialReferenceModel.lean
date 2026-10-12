import PaperFramework.TrialReferenceAlgebra

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def referencePoleA (n s : ℝ) : ℝ :=
  2 * n * (n + 1) / (n + s) ^ 2 + 2 * (n + 1) ^ 2 / (n + s) ^ 3

def referencePoleB (n s : ℝ) : ℝ :=
  (n + 1) ^ 2 / (n + s) ^ 2 - 2 * s * (n + 1) / (n + s)

def referencePoleD (n s : ℝ) : ℝ := (n + 1) ^ 2 / (n + s) ^ 2

/-- Partial fractions for the reciprocal model of the two endpoint contributions. -/
theorem scalar_reference_partial_fraction (n s i : ℝ) (hn : 0 < n) (hs : 2 ≤ s)
    (hi0 : 0 ≤ i) (hi : i < n) :
    (n + 1) ^ 2 * referenceWeight n i / ((n - i) ^ 2 * (i + s) ^ 2) =
      referencePoleA n s * (1 / (i + s) + 1 / (n - i)) +
        referencePoleB n s / (i + s) ^ 2 + referencePoleD n s / (n - i) ^ 2 := by
  have hu : 0 < i + s := by linarith
  have hj : 0 < n - i := sub_pos.mpr hi
  have hT : 0 < n + s := by linarith
  rw [referenceWeight_eq_product n i (ne_of_gt (show 0 < n + 1 by linarith))]
  unfold referencePoleA referencePoleB referencePoleD
  field_simp [ne_of_gt hu, ne_of_gt hj, ne_of_gt hT,
    ne_of_gt (show 0 < n + 1 by linarith)]
  <;> ring

theorem trial_baseline_reciprocal_difference (N : ℕ) (t : ℝ) (ht : 1 ≤ t) (i : Fin N) :
    tailU 0 1 (trialVector N t) i -
        1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t)) =
      2 * t / ((N : ℝ) * ((N : ℝ) + 2 * t) * ((N : ℝ) - i.val + 1)) -
        (tail (trialLeft N t) i.val - ((N : ℝ) - i.val) / ((N : ℝ) + 2 * t)) /
          (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1)) -
        2 * t * shiftedHarmonic t (N - i.val) /
          ((N : ℝ) * ((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1)) := by
  have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
  have hn : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  have hu : 0 < (i.val : ℝ) + 2 * t := by have := Nat.cast_nonneg (α := ℝ) i.val; linarith
  have hj : 0 < (N : ℝ) - i.val := sub_pos.mpr hi
  have hT : 0 < (N : ℝ) + 2 * t := by linarith
  rw [trial_baseline_tailU_identity N t ht i]
  simp only [Nat.cast_sub (Nat.le_of_lt i.isLt)]
  field_simp [ne_of_gt hn, ne_of_gt hu, ne_of_gt hj, ne_of_gt hT,
    ne_of_gt (show 0 < (N : ℝ) - i.val + 1 by linarith)]
  <;> ring

end
end CriticalExtrapolation.Paper
