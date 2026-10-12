import PaperFramework.TrialBasics

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem sum_real_range (j : ℕ) : (∑ k ∈ Finset.range j, (k : ℝ)) = (j : ℝ) * ((j : ℝ) - 1) / 2 := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, ih]; simp only [Nat.cast_add, Nat.cast_one]; ring

theorem reciprocal_defect_identity (j : ℕ) (u : ℝ) (hu : 0 < u) :
    u * (∑ k ∈ Finset.range j, 1 / (u + (k : ℝ))) =
      (j : ℝ) - ∑ k ∈ Finset.range j, (k : ℝ) / (u + (k : ℝ)) := by
  rw [Finset.mul_sum]
  have hpoint : ∀ k : ℕ, u * (1 / (u + (k : ℝ))) = 1 - (k : ℝ) / (u + (k : ℝ)) := by
    intro k
    have hd : u + (k : ℝ) ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hu (Nat.cast_nonneg _))
    field_simp [hd]
    <;> ring
  simp_rw [hpoint, Finset.sum_sub_distrib]
  simp

theorem reciprocal_defect_lower (j : ℕ) (hj : 2 ≤ j) (u : ℝ) (hu : 0 < u) :
    (j : ℝ) * ((j : ℝ) - 1) / (2 * (u + (j : ℝ) - 1)) ≤
      ∑ k ∈ Finset.range j, (k : ℝ) / (u + (k : ℝ)) := by
  have hJ : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hd : 0 < u + (j : ℝ) - 1 := by linarith
  have hsum : (∑ k ∈ Finset.range j, (k : ℝ) / (u + (j : ℝ) - 1)) ≤
      ∑ k ∈ Finset.range j, (k : ℝ) / (u + (k : ℝ)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkR : (k : ℝ) + 1 ≤ j := by exact_mod_cast Finset.mem_range.mp hk
    have hk0 := Nat.cast_nonneg (α := ℝ) k
    have hdk : 0 < u + (k : ℝ) := by linarith
    apply (div_le_div_iff₀ hd hdk).mpr
    nlinarith [mul_nonneg hk0 (by linarith : 0 ≤ (j : ℝ) - 1 - k)]
  rw [← Finset.sum_div, sum_real_range] at hsum
  simpa only [div_div] using hsum

/-- The positive polynomial in the paper's left endpoint slope estimate. -/
theorem trial_left_remainder_positive (j : ℕ) (hj : 2 ≤ j) (t u : ℝ)
    (ht : 1 ≤ t) (hu : 2 * t ≤ u) :
    0 < t - t * (j : ℝ) / (u + 1) +
      (j : ℝ) * ((j : ℝ) - 1) / (2 * (u + (j : ℝ) - 1)) := by
  have hJ : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u + 1 := by linarith
  have hd : 0 < u + (j : ℝ) - 1 := by linarith
  have hid : 2 * (u + 1) * (u + (j : ℝ) - 1) *
      (t - t * (j : ℝ) / (u + 1) + (j : ℝ) * ((j : ℝ) - 1) / (2 * (u + (j : ℝ) - 1))) =
      2 * t * u ^ 2 + ((j : ℝ) - 1) * ((j : ℝ) * (u + 1 - 2 * t) + 2 * t) := by
    field_simp [ne_of_gt hu1, ne_of_gt hd]
    <;> ring
  have hfirst : 0 < 2 * t * u ^ 2 := mul_pos (by positivity) (sq_pos_of_pos hu0)
  have hsecond : 0 ≤ ((j : ℝ) - 1) * ((j : ℝ) * (u + 1 - 2 * t) + 2 * t) := by
    apply mul_nonneg (by linarith)
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by positivity)
  have hproduct : 0 < 2 * (u + 1) * (u + (j : ℝ) - 1) *
      (t - t * (j : ℝ) / (u + 1) + (j : ℝ) * ((j : ℝ) - 1) / (2 * (u + (j : ℝ) - 1))) := by
    rw [hid]
    linarith
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < 2 * (u + 1) * (u + (j : ℝ) - 1))).mp hproduct

/-- Strict slope inequality for the left reciprocal endpoint profile, before normalization. -/
theorem trial_left_slope_positive (j : ℕ) (hj : 2 ≤ j) (a t u : ℝ)
    (ha : 0 ≤ a) (ht : 1 ≤ t) (hu : 2 * t ≤ u) :
    0 < ((j : ℝ) + a + t) / u - (∑ k ∈ Finset.range j, 1 / (u + (k : ℝ))) -
      t * ((j : ℝ) + a) * (1 / u - 1 / (u + 1)) := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u + 1 := by linarith
  have hdefect := reciprocal_defect_identity j u hu0
  have hlower := reciprocal_defect_lower j hj u hu0
  have hpositive := trial_left_remainder_positive j hj t u ht hu
  have hid : u * (((j : ℝ) + a + t) / u -
      (∑ k ∈ Finset.range j, 1 / (u + (k : ℝ))) - t * ((j : ℝ) + a) * (1 / u - 1 / (u + 1))) =
      a * (1 - t / (u + 1)) + t - t * (j : ℝ) / (u + 1) +
        ∑ k ∈ Finset.range j, (k : ℝ) / (u + (k : ℝ)) := by
    have htmp : u * (((j : ℝ) + a + t) / u -
        (∑ k ∈ Finset.range j, 1 / (u + (k : ℝ))) - t * ((j : ℝ) + a) * (1 / u - 1 / (u + 1))) =
        (j : ℝ) + a + t - u * (∑ k ∈ Finset.range j, 1 / (u + (k : ℝ))) -
          t * ((j : ℝ) + a) / (u + 1) := by
      field_simp [ne_of_gt hu0, ne_of_gt hu1]
      <;> ring
    rw [htmp, hdefect]
    ring
  have hcoef : 0 ≤ 1 - t / (u + 1) := by
    have hdiv : t / (u + 1) ≤ 1 := (div_le_one hu1).mpr (by linarith)
    linarith
  have hproduct : 0 < u * (((j : ℝ) + a + t) / u -
      (∑ k ∈ Finset.range j, 1 / (u + (k : ℝ))) - t * ((j : ℝ) + a) * (1 / u - 1 / (u + 1))) := by
    rw [hid]
    linarith [mul_nonneg ha hcoef]
  exact (mul_pos_iff_of_pos_left hu0).mp hproduct

end
end CriticalExtrapolation.Paper
