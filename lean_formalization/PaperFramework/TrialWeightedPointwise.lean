import PaperFramework.TrialWeightedAlgebra

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem trial_right_scalar_weight_bound (n x j t q : ℝ)
    (hn : 0 < n) (hx : n / 2 < x) (hx0 : 0 ≤ x) (hj : 2 ≤ j)
    (hnx : n = x + j) (ht : 1 ≤ t) (hq : 0 ≤ q) :
    n * ((x + 1) * (1 / ((x + 2 * t) * (x + 2 * t + 1)) +
      1 / (n * (j + 2 * t)))) * (1 / (x + 2 * t) + q / n) / j ≤
      4 * (2 + q) / (n * j) + (2 + q) / (j * (j + 1)) := by
  have hu : 0 < x + 2 * t := by linarith
  have hu1 : 0 < x + 2 * t + 1 := by linarith
  have hj0 : 0 < j := by linarith
  have hjt : 0 < j + 2 * t := by linarith
  have hr : 1 / (x + 2 * t) ≤ 2 / n := by
    apply (div_le_div_iff₀ hu hn).mpr
    linarith
  have hA : (x + 1) / ((x + 2 * t) * (x + 2 * t + 1)) ≤ 4 / n := by
    calc
      _ ≤ 1 / (x + 2 * t + 1) := by
        apply (div_le_div_iff₀ (mul_pos hu hu1) hu1).mpr
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (show x + 1 ≤ x + 2 * t by linarith) hu1.le
      _ ≤ 2 / n := by
        apply (div_le_div_iff₀ hu1 hn).mpr
        linarith
      _ ≤ 4 / n := div_le_div_of_nonneg_right (by norm_num) hn.le
  have hB : (x + 1) / (n * (j + 2 * t)) ≤ 1 / (j + 1) := by
    calc
      _ ≤ 1 / (j + 2 * t) := by
        apply (div_le_div_iff₀ (mul_pos hn hjt) hjt).mpr
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (show x + 1 ≤ n by linarith) hjt.le
      _ ≤ 1 / (j + 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
  have hg : (x + 1) * (1 / ((x + 2 * t) * (x + 2 * t + 1)) +
      1 / (n * (j + 2 * t))) ≤ 4 / n + 1 / (j + 1) := by
    calc
      _ = (x + 1) / ((x + 2 * t) * (x + 2 * t + 1)) +
          (x + 1) / (n * (j + 2 * t)) := by ring
      _ ≤ _ := add_le_add hA hB
  have hv : 1 / (x + 2 * t) + q / n ≤ (2 + q) / n := by
    calc
      _ ≤ 2 / n + q / n := add_le_add hr (le_refl _)
      _ = _ := by ring
  have hv0 : 0 ≤ 1 / (x + 2 * t) + q / n := by positivity
  have hg0 : 0 ≤ 4 / n + 1 / (j + 1) := by positivity
  calc
    _ ≤ n * (4 / n + 1 / (j + 1)) * ((2 + q) / n) / j := by
      apply div_le_div_of_nonneg_right _ hj0.le
      calc
        _ ≤ n * (4 / n + 1 / (j + 1)) * (1 / (x + 2 * t) + q / n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hn.le) hv0
        _ ≤ _ := mul_le_mul_of_nonneg_left hv (mul_nonneg hn.le hg0)
    _ = _ := by
      field_simp [ne_of_gt hn, ne_of_gt hj0, ne_of_gt (show 0 < j + 1 by linarith)]
      <;> ring

/-- The three-region estimate retains the terminal difference, bounded by the last summand. -/
theorem trial_weighted_pointwise (N : ℕ) (t : ℝ) (hN : 0 < N) (ht : 1 ≤ t)
    (i : Fin N) :
    (N : ℝ) * (((i.val : ℝ) + 1) * difference (trialVector N t) i) * trialVector N t i /
        ((N : ℝ) - i.val) ≤
      2 * (((i.val : ℝ) + 1) * difference (trialVector N t) i * trialVector N t i) +
        4 * (2 + shiftedHarmonic t N) / ((N : ℝ) * ((N : ℝ) - i.val)) +
        (8 + shiftedHarmonic t (N - i.val)) /
          (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1)) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
  have hi0 : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  have hj : 0 < (N : ℝ) - i.val := sub_pos.mpr hi
  have hv : 0 ≤ trialVector N t i := (trialVector_positive N t ht i).le
  have hg : 0 ≤ ((i.val : ℝ) + 1) * difference (trialVector N t) i :=
    mul_nonneg (by positivity) (trialVector_differences_nonnegative N t ht i)
  have hq := shiftedHarmonic_nonnegative t ht (N - i.val)
  have hQ := shiftedHarmonic_nonnegative t ht N
  have hrest0 : 0 ≤ 4 * (2 + shiftedHarmonic t N) /
      ((N : ℝ) * ((N : ℝ) - i.val)) := by positivity
  have hlast0 : 0 ≤ (8 + shiftedHarmonic t (N - i.val)) /
      (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1)) := by positivity
  by_cases hleft : (i.val : ℝ) ≤ (N : ℝ) / 2
  · have hc : (N : ℝ) / ((N : ℝ) - i.val) ≤ 2 := by
      apply (div_le_iff₀ hj).mpr
      linarith
    have hb := mul_le_mul_of_nonneg_right hc (mul_nonneg hg hv)
    have he : (N : ℝ) * (((i.val : ℝ) + 1) * difference (trialVector N t) i) *
        trialVector N t i / ((N : ℝ) - i.val) =
        ((N : ℝ) / ((N : ℝ) - i.val)) *
          (((i.val : ℝ) + 1) * difference (trialVector N t) i * trialVector N t i) := by ring
    rw [he]
    linarith only [hb, hrest0, hlast0]
  · by_cases hterminal : i.val + 1 = N
    · have hiR : (i.val : ℝ) + 1 = N := by exact_mod_cast hterminal
      have hj1 : (N : ℝ) - i.val = 1 := by linarith
      have hnxt : ¬i.val + 1 < N := by omega
      have hd : difference (trialVector N t) i = trialVector N t i := by
        simp [difference, zeroExtend, hnxt]
      have hup := (le_div_iff₀ hn).mp (trialVector_terminal_upper N t ht i hterminal)
      have hs : ((N : ℝ) * trialVector N t i) ^ 2 ≤ 4 := by
        nlinarith [mul_nonneg hn.le hv]
      rw [hiR, hd, hj1]
      simp only [div_one]
      have hz : 0 ≤ 2 * ((N : ℝ) * trialVector N t i * trialVector N t i) := by positivity
      have hr : 0 ≤ 4 * (2 + shiftedHarmonic t N) / ((N : ℝ) * 1) := by positivity
      nlinarith only [hs, hz, hr, hq]
    · have hnext : i.val + 1 < N := by omega
      have hj2 : (2 : ℝ) ≤ (N : ℝ) - i.val := by
        have hh : i.val + 2 ≤ N := by omega
        have hhR : (i.val : ℝ) + 2 ≤ N := by exact_mod_cast hh
        linarith
      have hdiff := trialVector_difference_adjacent N t ht i ⟨i.val + 1, hnext⟩ rfl
      rw [Nat.cast_sub (Nat.le_of_lt i.isLt)] at hdiff
      have hb := trial_right_scalar_weight_bound (N : ℝ) (i.val : ℝ) ((N : ℝ) - i.val)
        t (shiftedHarmonic t (N - i.val)) hn (lt_of_not_ge hleft) hi0 hj2 (by ring) ht hq
      have hb' : (N : ℝ) * (((i.val : ℝ) + 1) * difference (trialVector N t) i) *
          trialVector N t i / ((N : ℝ) - i.val) ≤
          4 * (2 + shiftedHarmonic t (N - i.val)) / ((N : ℝ) * ((N : ℝ) - i.val)) +
          (2 + shiftedHarmonic t (N - i.val)) /
            (((N : ℝ) - i.val) * ((N : ℝ) - i.val + 1)) := by
        simpa only [hdiff, trialVector, Nat.cast_sub (Nat.le_of_lt i.isLt)] using hb
      have hmono := shiftedHarmonic_monotone t ht (Nat.sub_le N i.val)
      have hfirst := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add (le_refl (2 : ℝ)) hmono) (by norm_num : (0 : ℝ) ≤ 4))
        (mul_pos hn hj).le
      have hlast := div_le_div_of_nonneg_right
        (show 2 + shiftedHarmonic t (N - i.val) ≤ 8 + shiftedHarmonic t (N - i.val) by linarith)
        (mul_pos hj (by linarith : 0 < (N : ℝ) - i.val + 1)).le
      have hz : 0 ≤ 2 * (((i.val : ℝ) + 1) * difference (trialVector N t) i * trialVector N t i) :=
        mul_nonneg (by norm_num) (mul_nonneg hg hv)
      linarith only [hb', hfirst, hlast, hz]

end
end CriticalExtrapolation.Paper
