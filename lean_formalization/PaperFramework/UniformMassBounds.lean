import PaperFramework.UniformScaledAlgebra

namespace CriticalExtrapolation.Paper
noncomputable section

theorem shiftMass_unit_bounds (a t : ℝ) (ha : 0 ≤ a) (ht : 0 < t) :
    0 ≤ shiftMass a t ∧ shiftMass a t ≤ 1 := by
  have hat : 0 < a + t := by linarith
  exact ⟨div_nonneg ht.le hat.le, (div_le_one hat).mpr (by linarith)⟩

theorem shiftMass_square_unit_bounds (a t : ℝ) (ha : 0 ≤ a) (ht : 0 < t) :
    0 ≤ (shiftMass a t) ^ 2 ∧ (shiftMass a t) ^ 2 ≤ 1 := by
  have hm := shiftMass_unit_bounds a t ha ht
  constructor
  · positivity
  · nlinarith [mul_nonneg hm.1 (sub_nonneg.mpr hm.2)]

theorem shiftMass_square_error_bound (a t : ℝ) (ha : 0 ≤ a) (ht : 0 < t) :
    |(shiftMass a t) ^ 2 - 1| ≤ 2 * a / t := by
  have hm := shiftMass_unit_bounds a t ha ht
  have hm2 := shiftMass_square_unit_bounds a t ha ht
  have hat : 0 < a + t := by linarith
  have hid : 1 - shiftMass a t = a / (a + t) := by
    unfold shiftMass
    field_simp [ne_of_gt hat]
    <;> ring
  have he : 1 - shiftMass a t ≤ a / t := by
    rw [hid]
    exact div_le_div_of_nonneg_left ha ht (by linarith)
  rw [abs_of_nonpos (by linarith only [hm2.2] : (shiftMass a t) ^ 2 - 1 ≤ 0)]
  calc
    _ ≤ 2 * (1 - shiftMass a t) := by nlinarith [sq_nonneg (1 - shiftMass a t)]
    _ ≤ 2 * (a / t) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

theorem scaled_mass_main_error_bound (a t v k K : ℝ) (ha : 0 ≤ a) (ht : 0 < t)
    (hk : k ∈ Set.Icc (0 : ℝ) K) :
    |(shiftMass a t) ^ 2 * (v - k ^ 2) - (1 - k ^ 2)| ≤
      |v - 1| + (1 + K ^ 2) * (2 * a / t) := by
  have hm2 := shiftMass_square_unit_bounds a t ha ht
  have he := shiftMass_square_error_bound a t ha ht
  have hk2 : k ^ 2 ≤ K ^ 2 := by nlinarith [hk.1, hk.2]
  have habs : |1 - k ^ 2| ≤ 1 + K ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg k, sq_nonneg K]
  calc
    _ = |(shiftMass a t) ^ 2 * (v - 1) +
        ((shiftMass a t) ^ 2 - 1) * (1 - k ^ 2)| := by congr 1; ring
    _ ≤ |(shiftMass a t) ^ 2 * (v - 1)| +
        |((shiftMass a t) ^ 2 - 1) * (1 - k ^ 2)| := by
      simpa only [Real.norm_eq_abs] using norm_add_le
        ((shiftMass a t) ^ 2 * (v - 1)) (((shiftMass a t) ^ 2 - 1) * (1 - k ^ 2))
    _ ≤ |v - 1| + (1 + K ^ 2) * (2 * a / t) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hm2.1]
      apply add_le_add
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right hm2.2 (abs_nonneg (v - 1))
      · calc
          _ ≤ (2 * a / t) * (1 + K ^ 2) :=
            mul_le_mul he habs (abs_nonneg _) (by positivity)
          _ = _ := by ring

end
end CriticalExtrapolation.Paper
