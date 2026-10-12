import PaperFramework.TrialBaseline

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem trial_baseline_endpoint_bound (N : ℕ) (t : ℝ) (ht : 1 ≤ t) (i : Fin N) :
    let j : ℝ := ((N - i.val : ℕ) : ℝ)
    0 < tailU 0 1 (trialVector N t) i ∧
      tailU 0 1 (trialVector N t) i ≤
        1 / (N : ℝ) * (1 / ((i.val : ℝ) + 2 * t) + 2 / j) := by
  let j : ℝ := ((N - i.val : ℕ) : ℝ)
  let u : ℝ := (i.val : ℝ) + 2 * t
  have hJ : 0 < j := by dsimp [j]; exact_mod_cast (show 0 < N - i.val by omega)
  have hN : 0 < (N : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  have hu : 0 < u := by dsimp [u]; have := Nat.cast_nonneg (α := ℝ) i.val; linarith
  have hjR : j = (N : ℝ) - (i.val : ℝ) := by dsimp [j]; rw [Nat.cast_sub (by omega)]
  have hfirst : 1 / (j * u) ≤ 1 / (N : ℝ) * (1 / u + 1 / j) := by
    have hid : 1 / (N : ℝ) * (1 / u + 1 / j) - 1 / (j * u) =
        2 * t / ((N : ℝ) * j * u) := by
      field_simp [ne_of_gt hN, ne_of_gt hJ, ne_of_gt hu]
      dsimp [u]
      rw [hjR]
      ring
    apply sub_nonneg.mp
    rw [hid]
    positivity
  have hsecond : 1 / ((N : ℝ) * (j + 1)) ≤ 1 / ((N : ℝ) * j) :=
    one_div_le_one_div_of_le (mul_pos hN hJ) (by nlinarith)
  have hbounds := trial_baseline_tailU_bounds N t ht i
  refine ⟨hbounds.1, hbounds.2.trans ?_⟩
  change 1 / (j * u) + 1 / ((N : ℝ) * (j + 1)) ≤ 1 / (N : ℝ) * (1 / u + 2 / j)
  calc
    _ ≤ 1 / (N : ℝ) * (1 / u + 1 / j) + 1 / ((N : ℝ) * j) := add_le_add hfirst hsecond
    _ = _ := by ring

/-- Equation (9.4b) with the genuine corrected weight, including every endpoint index. -/
theorem trial_reference_remainder_majorant (t : ℝ) (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ N, 0 < N → ∀ i : Fin N,
      ((N : ℝ) + 1) ^ 2 * referenceWeight (N : ℝ) (i.val : ℝ) *
        (tailU 0 1 (trialVector N t) i) ^ 2 ≤
      C * (1 / ((i.val : ℝ) + 2 * t) + 1 / ((N : ℝ) - (i.val : ℝ))) := by
  let C : ℝ := 12 * (9 + 8 * t)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N hNat i
  let j : ℝ := ((N - i.val : ℕ) : ℝ)
  let u : ℝ := (i.val : ℝ) + 2 * t
  let p : ℝ := tailU 0 1 (trialVector N t) i
  let b : ℝ := 1 / (N : ℝ) * (1 / u + 2 / j)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN : 0 < (N : ℝ) := by linarith
  have hI : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  have hIN : (i.val : ℝ) + 1 ≤ N := by exact_mod_cast i.isLt
  have hJ : 0 < j := by dsimp [j]; exact_mod_cast (show 0 < N - i.val by omega)
  have hu : 0 < u := by dsimp [u]; linarith
  have hjR : j = (N : ℝ) - (i.val : ℝ) := by dsimp [j]; rw [Nat.cast_sub (by omega)]
  have hweight := referenceWeight_le_three (s := 2 * t) hN1 hI hIN (by linarith)
  rw [← hjR] at hweight
  change referenceWeight (N : ℝ) (i.val : ℝ) ≤ 3 * u * j / (N : ℝ) at hweight
  have hr0 : 0 ≤ 3 * u * j / (N : ℝ) := by positivity
  have hb := trial_baseline_endpoint_bound N t ht i
  change 0 < p ∧ p ≤ b at hb
  have hb0 : 0 ≤ b := hb.1.le.trans hb.2
  have hsq : p ^ 2 ≤ b ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (add_nonneg hb.1.le hb0)]
  have hproduct := mul_le_mul hweight hsq (sq_nonneg p) hr0
  have hscaled := mul_le_mul_of_nonneg_left hproduct (sq_nonneg ((N : ℝ) + 1))
  have hsize : ((N : ℝ) + 1) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith [sq_nonneg ((N : ℝ) - 1)]
  have hsizeProduct := mul_le_mul_of_nonneg_right hsize (mul_nonneg hr0 (sq_nonneg b))
  have hjN : j ≤ (N : ℝ) := by linarith
  have huN : u ≤ (1 + 2 * t) * (N : ℝ) := by
    dsimp [u]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * t) (sub_nonneg.mpr hN1)]
  have hfracJ : j / (N : ℝ) ≤ 1 := (div_le_one hN).mpr hjN
  have hfracU : u / (N : ℝ) ≤ 1 + 2 * t := (div_le_iff₀ hN).mpr huN
  have hterm1 := div_le_div_of_nonneg_right hfracJ hu.le
  have hterm2 := one_div_le_one_div_of_le hJ hjN
  have hterm3 := div_le_div_of_nonneg_right hfracU hJ.le
  rw [← hjR]
  change ((N : ℝ) + 1) ^ 2 * referenceWeight (N : ℝ) (i.val : ℝ) * p ^ 2 ≤ C * (1 / u + 1 / j)
  calc
    _ = ((N : ℝ) + 1) ^ 2 * (referenceWeight (N : ℝ) (i.val : ℝ) * p ^ 2) := by ring
    _ ≤ ((N : ℝ) + 1) ^ 2 * ((3 * u * j / (N : ℝ)) * b ^ 2) := hscaled
    _ ≤ 4 * (N : ℝ) ^ 2 * ((3 * u * j / (N : ℝ)) * b ^ 2) := hsizeProduct
    _ = 12 * ((j / (N : ℝ)) / u + 4 * (1 / (N : ℝ)) + 4 * ((u / (N : ℝ)) / j)) := by
      dsimp [b]
      field_simp [ne_of_gt hN, ne_of_gt hJ, ne_of_gt hu]
      <;> ring
    _ ≤ 12 * (1 / u + 4 * (1 / j) + 4 * ((1 + 2 * t) / j)) := by
      nlinarith [hterm1, hterm2, hterm3]
    _ ≤ C * (1 / u + 1 / j) := by
      have hid : C * (1 / u + 1 / j) - 12 * (1 / u + 4 * (1 / j) + 4 * ((1 + 2 * t) / j)) =
          12 * ((8 + 8 * t) * (1 / u) + 1 / j) := by dsimp [C]; ring
      apply sub_nonneg.mp
      rw [hid]
      positivity

end
end CriticalExtrapolation.Paper
