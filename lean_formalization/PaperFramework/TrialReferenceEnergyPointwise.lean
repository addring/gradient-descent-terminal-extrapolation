import PaperFramework.TrialReferenceErrorPointwise

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem reference_model_prefactor_upper (N : ℕ) (t : ℝ) (hN : 0 < N) (ht : 1 ≤ t)
    (i : Fin N) :
    ((N : ℝ) + 1) ^ 2 * referenceWeight (N : ℝ) (i.val : ℝ) *
      (1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t))) ≤ 12 * (N : ℝ) := by
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : 0 < (N : ℝ) := by linarith
  have hi0 : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  have hiN : (i.val : ℝ) + 1 ≤ N := by exact_mod_cast i.isLt
  have hu : 0 < (i.val : ℝ) + 2 * t := by linarith
  have hj : 0 < (N : ℝ) - i.val := by linarith
  have hweight := referenceWeight_le_three (s := 2 * t) hn hi0 hiN (by linarith)
  have hm : 0 ≤ 1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t)) := by positivity
  have hwm : referenceWeight (N : ℝ) (i.val : ℝ) *
      (1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t))) ≤ 3 / (N : ℝ) := by
    calc
      _ ≤ (3 * ((i.val : ℝ) + 2 * t) * ((N : ℝ) - i.val) / (N : ℝ)) *
          (1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t))) :=
        mul_le_mul_of_nonneg_right hweight hm
      _ = _ := by
        field_simp [ne_of_gt hn0, ne_of_gt hu, ne_of_gt hj]
        <;> ring
  have hs : ((N : ℝ) + 1) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((N : ℝ) - 1)]
  calc
    _ = ((N : ℝ) + 1) ^ 2 * (referenceWeight (N : ℝ) (i.val : ℝ) *
        (1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t)))) := by ring
    _ ≤ ((N : ℝ) + 1) ^ 2 * (3 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hwm (sq_nonneg _)
    _ ≤ 4 * (N : ℝ) ^ 2 * (3 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by field_simp [ne_of_gt hn0] <;> ring

theorem trial_reference_pointwise_energy_error (N : ℕ) (t : ℝ) (hN : 0 < N)
    (ht : 1 ≤ t) (i : Fin N) :
    |((N : ℝ) + 1) ^ 2 * referenceWeight (N : ℝ) (i.val : ℝ) *
        (tailU 0 1 (trialVector N t) i) ^ 2 -
      ((N : ℝ) + 1) ^ 2 * referenceWeight (N : ℝ) (i.val : ℝ) *
        (1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t))) ^ 2| ≤
      12 * (2 + 2 * t) * (N : ℝ) *
        |tailU 0 1 (trialVector N t) i -
          1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t))| := by
  let A : ℝ := ((N : ℝ) + 1) ^ 2 * referenceWeight (N : ℝ) (i.val : ℝ)
  let p : ℝ := tailU 0 1 (trialVector N t) i
  let m : ℝ := 1 / (((N : ℝ) - i.val) * ((i.val : ℝ) + 2 * t))
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hi : (i.val : ℝ) + 1 ≤ N := by exact_mod_cast i.isLt
  have hi0 : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  have hj : 0 < (N : ℝ) - i.val := by linarith
  have hu : 0 < (i.val : ℝ) + 2 * t := by linarith
  have hp0 : 0 ≤ p := (trial_baseline_tailU_bounds N t ht i).1.le
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hA0 : 0 ≤ A := mul_nonneg (sq_nonneg _)
    (referenceWeight_pos hn hi0 hi).le
  have hp : p ≤ (1 + 2 * t) * m := by
    convert trial_baseline_reciprocal_upper N t ht i using 1 <;> dsimp [p, m] <;> ring
  have hsum : p + m ≤ (2 + 2 * t) * m := by linarith only [hp]
  have hAm : A * m ≤ 12 * (N : ℝ) := reference_model_prefactor_upper N t hN ht i
  change |A * p ^ 2 - A * m ^ 2| ≤ 12 * (2 + 2 * t) * (N : ℝ) * |p - m|
  calc
    _ = A * |p - m| * (p + m) := by
      rw [show A * p ^ 2 - A * m ^ 2 = A * (p - m) * (p + m) by ring,
        abs_mul, abs_mul, abs_of_nonneg hA0, abs_of_nonneg (add_nonneg hp0 hm0)]
    _ ≤ A * |p - m| * ((2 + 2 * t) * m) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hA0 (abs_nonneg _))
    _ = (2 + 2 * t) * (A * m) * |p - m| := by ring
    _ ≤ (2 + 2 * t) * (12 * (N : ℝ)) * |p - m| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAm (by linarith)) (abs_nonneg _)
    _ = _ := by ring

end
end CriticalExtrapolation.Paper
