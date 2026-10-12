import PaperFramework.TrialNormalization

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem trial_baseline_tailU_identity (N : ℕ) (t : ℝ) (ht : 1 ≤ t) (i : Fin N) :
    let j : ℝ := ((N - i.val : ℕ) : ℝ)
    tailU 0 1 (trialVector N t) i =
      ((j + 1) / ((i.val : ℝ) + 2 * t) - tail (trialLeft N t) i.val +
        (j - 2 * t * shiftedHarmonic t (N - i.val)) / (N : ℝ)) / (j * (j + 1)) := by
  dsimp only
  let j : ℝ := ((N - i.val : ℕ) : ℝ)
  have hJ : 0 < j := by dsimp [j]; exact_mod_cast (show 0 < N - i.val by omega)
  have hN : 0 < (N : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  have hu : 0 < (i.val : ℝ) + 2 * t := by have := Nat.cast_nonneg (α := ℝ) i.val; linarith
  have hjR : j = (N : ℝ) - (i.val : ℝ) := by dsimp [j]; rw [Nat.cast_sub (by omega)]
  have htail := tail_step (trialVector N t) i
  have hnext : tail (trialVector N t) (i.val + 1) =
      tail (trialVector N t) i.val - trialVector N t i := by linarith
  have hsplit : tail (trialVector N t) i.val =
      tail (trialLeft N t) i.val + tail (trialRight N t) i.val := by
    rw [trialVector_profiles]
    simp only [tail, Pi.add_apply, Finset.sum_add_distrib]
  simp only [tailU, tailZ, energyZeta, energyF, Fin.val_castSucc, Fin.val_succ,
    Nat.cast_add, Nat.cast_one, add_zero]
  rw [show (N : ℝ) + 1 - (i.val : ℝ) = j + 1 by linarith,
    show (N : ℝ) + 1 - ((i.val : ℝ) + 1) = j by linarith,
    hnext, hsplit, trialRight_tail N t ht i]
  simp only [trialVector]
  change (tail (trialLeft N t) i.val + ((j + 2 * t + 1) * shiftedHarmonic t (N - i.val) / (N : ℝ) -
      j / (N : ℝ))) / (j + 1) -
      (tail (trialLeft N t) i.val + ((j + 2 * t + 1) * shiftedHarmonic t (N - i.val) / (N : ℝ) -
        j / (N : ℝ)) - (1 / ((i.val : ℝ) + 2 * t) + shiftedHarmonic t (N - i.val) / (N : ℝ))) / j =
      ((j + 1) / ((i.val : ℝ) + 2 * t) - tail (trialLeft N t) i.val +
        (j - 2 * t * shiftedHarmonic t (N - i.val)) / (N : ℝ)) / (j * (j + 1))
  field_simp [ne_of_gt hJ, ne_of_gt hN, ne_of_gt hu, ne_of_gt (show 0 < j + 1 by linarith)]
  <;> ring

theorem trialLeft_tail_upper (N : ℕ) (t : ℝ) (ht : 1 ≤ t) (i : Fin N) :
    tail (trialLeft N t) i.val ≤ ((N - i.val : ℕ) : ℝ) / ((i.val : ℝ) + 2 * t) := by
  have hu : 0 < (i.val : ℝ) + 2 * t := by have := Nat.cast_nonneg (α := ℝ) i.val; linarith
  rw [trialLeft_tail]
  calc
    _ ≤ ∑ k ∈ Finset.range (N - i.val), 1 / ((i.val : ℝ) + 2 * t) := by
      apply Finset.sum_le_sum
      intro k _
      exact one_div_le_one_div_of_le hu (le_add_of_nonneg_right (Nat.cast_nonneg _))
    _ = _ := by simp [div_eq_mul_inv]

theorem trialLeft_tail_nonnegative (N : ℕ) (t : ℝ) (ht : 1 ≤ t) (i : Fin N) :
    0 ≤ tail (trialLeft N t) i.val := by
  rw [trialLeft_tail]
  apply Finset.sum_nonneg
  intro k _
  have := Nat.cast_nonneg (α := ℝ) i.val
  have := Nat.cast_nonneg (α := ℝ) k
  exact div_nonneg zero_le_one (by linarith)

theorem trial_baseline_tailU_bounds (N : ℕ) (t : ℝ) (ht : 1 ≤ t) (i : Fin N) :
    let j : ℝ := ((N - i.val : ℕ) : ℝ)
    0 < tailU 0 1 (trialVector N t) i ∧
      tailU 0 1 (trialVector N t) i ≤
        1 / (j * ((i.val : ℝ) + 2 * t)) + 1 / ((N : ℝ) * (j + 1)) := by
  dsimp only
  let j : ℝ := ((N - i.val : ℕ) : ℝ)
  let u : ℝ := (i.val : ℝ) + 2 * t
  have hJ : 0 < j := by dsimp [j]; exact_mod_cast (show 0 < N - i.val by omega)
  have hN : 0 < (N : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  have hu : 0 < u := by dsimp [u]; have := Nat.cast_nonneg (α := ℝ) i.val; linarith
  have hs : 0 < 2 * t + 1 := by linarith
  have hq0 := shiftedHarmonic_nonnegative t ht (N - i.val)
  have hq := (le_div_iff₀ hs).mp (shiftedHarmonic_upper t ht (N - i.val))
  have hright : 0 ≤ j - 2 * t * shiftedHarmonic t (N - i.val) := by change _ ≤ j at hq; nlinarith
  have hleft := trialLeft_tail_upper N t ht i
  have hleft0 := trialLeft_tail_nonnegative N t ht i
  have hleftPos : 0 < (j + 1) / u - tail (trialLeft N t) i.val := by
    have hrecip := one_div_pos.mpr hu
    change tail (trialLeft N t) i.val ≤ j / u at hleft
    rw [add_div]
    linarith
  rw [trial_baseline_tailU_identity N t ht i]
  change 0 < ((j + 1) / u - tail (trialLeft N t) i.val +
      (j - 2 * t * shiftedHarmonic t (N - i.val)) / (N : ℝ)) / (j * (j + 1)) ∧ _
  constructor
  · exact div_pos (add_pos_of_pos_of_nonneg hleftPos (div_nonneg hright hN.le))
      (mul_pos hJ (by linarith))
  · apply (div_le_iff₀ (mul_pos hJ (show 0 < j + 1 by linarith))).mpr
    have hid : (1 / (j * u) + 1 / ((N : ℝ) * (j + 1))) * (j * (j + 1)) =
        (j + 1) / u + j / (N : ℝ) := by
      field_simp [ne_of_gt hJ, ne_of_gt hN, ne_of_gt hu, ne_of_gt (show 0 < j + 1 by linarith)]
      <;> ring
    rw [hid]
    have hqterm : 0 ≤ 2 * t * shiftedHarmonic t (N - i.val) / (N : ℝ) := by positivity
    rw [sub_div]
    linarith

end
end CriticalExtrapolation.Paper
