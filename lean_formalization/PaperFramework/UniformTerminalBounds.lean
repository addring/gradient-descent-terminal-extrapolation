import PaperFramework.TrialPerturbationProfiles

namespace CriticalExtrapolation.Paper
noncomputable section

theorem normalizedTrial_terminal_log_upper (N : ℕ) (t : ℝ) (hN : 1 < N) (ht : 1 ≤ t)
    (i : Fin N) (hi : i.val + 1 = N)
    (hH : Real.log (N : ℝ) ≤ trialNormalization N t) :
    0 ≤ Real.log (N : ℝ) * normalizedTrial N t i ∧
      Real.log (N : ℝ) * normalizedTrial N t i ≤ 2 / (N : ℝ) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos hn
  have hp := trialVector_positive N t ht i
  have hH0 := trial_normalization_positive N t (by omega) ht
  have hratio : Real.log (N : ℝ) / trialNormalization N t ≤ 1 := (div_le_one hH0).mpr hH
  constructor
  · exact mul_nonneg hl.le (div_nonneg hp.le hH0.le)
  · change Real.log (N : ℝ) * (trialVector N t i / trialNormalization N t) ≤ _
    calc
      _ = (Real.log (N : ℝ) / trialNormalization N t) * trialVector N t i := by ring
      _ ≤ trialVector N t i := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio hp.le
      _ ≤ _ := trialVector_terminal_upper N t ht i hi

theorem shiftMass_shiftB_nat_upper (N : ℕ) (a t : ℝ) (hN : 0 < N)
    (ha : 0 ≤ a) (ht : 0 < t) :
    0 ≤ shiftMass a t * shiftB N a t * (N : ℝ) ∧
      shiftMass a t * shiftB N a t * (N : ℝ) ≤ a / t := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hat : 0 < a + t := by linarith
  have hm0 : 0 ≤ shiftMass a t := div_nonneg ht.le hat.le
  have hm1 : shiftMass a t ≤ 1 := (div_le_one hat).mpr (by linarith)
  have hB0 : 0 ≤ shiftB N a t := div_nonneg ha (by positivity)
  have heq : shiftMass a t * shiftB N a t * (N : ℝ) = shiftMass a t * (a / (a + t)) := by
    unfold shiftB
    field_simp [ne_of_gt hn, ne_of_gt hat]
    <;> ring
  refine ⟨mul_nonneg (mul_nonneg hm0 hB0) hn.le, ?_⟩
  rw [heq]
  calc
    _ ≤ 1 * (a / t) := mul_le_mul hm1
      (div_le_div_of_nonneg_left ha ht (by linarith)) (by positivity) (by norm_num)
    _ = _ := one_mul _

theorem trial_terminal_scaled_correction_bound (N : ℕ) (a t : ℝ) (hN : 1 < N)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (ht : 1 ≤ t) (i : Fin N) (hi : i.val + 1 = N)
    (hH : Real.log (N : ℝ) ≤ trialNormalization N t) :
    0 ≤ Real.log (N : ℝ) *
      (2 * energyF N a t * shiftMass a t * shiftB N a t * (N : ℝ) * (t - 1) /
        (a + 1) * normalizedTrial N t i) ∧
    Real.log (N : ℝ) *
      (2 * energyF N a t * shiftMass a t * shiftB N a t * (N : ℝ) * (t - 1) /
        (a + 1) * normalizedTrial N t i) ≤ 4 * (t + 2) * (t - 1) * a / t := by
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : 0 < (N : ℝ) := by linarith
  have ht0 : 0 < t := by linarith
  have htm : 0 ≤ t - 1 := by linarith
  have ha0 : 0 ≤ a := ha.1
  have hF0 : 0 ≤ energyF N a t := by unfold energyF; linarith [ha.1]
  have hF : energyF N a t ≤ (N : ℝ) * (t + 2) := by
    unfold energyF
    nlinarith [ha.2, mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ t + 1 by linarith)]
  have hm := shiftMass_shiftB_nat_upper N a t (by omega) ha.1 ht0
  have hlast := normalizedTrial_terminal_log_upper N t hN ht i hi hH
  have htr0 : 0 ≤ (t - 1) / (a + 1) := div_nonneg (by linarith) (by linarith [ha.1])
  have htr : (t - 1) / (a + 1) ≤ t - 1 := by
    apply (div_le_iff₀ (by linarith [ha.1] : 0 < a + 1)).mpr
    nlinarith [mul_nonneg (show 0 ≤ t - 1 by linarith) ha.1]
  have hid : Real.log (N : ℝ) *
      (2 * energyF N a t * shiftMass a t * shiftB N a t * (N : ℝ) * (t - 1) /
        (a + 1) * normalizedTrial N t i) =
      2 * energyF N a t * (shiftMass a t * shiftB N a t * (N : ℝ)) *
        ((t - 1) / (a + 1)) * (Real.log (N : ℝ) * normalizedTrial N t i) := by ring
  rw [hid]
  constructor
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hm.1) htr0) hlast.1
  · calc
      _ ≤ 2 * ((N : ℝ) * (t + 2)) * (a / t) * (t - 1) * (2 / (N : ℝ)) := by
        have h2F : 2 * energyF N a t ≤ 2 * ((N : ℝ) * (t + 2)) :=
          mul_le_mul_of_nonneg_left hF (by norm_num)
        have h01 := mul_le_mul h2F hm.2 hm.1
          (show 0 ≤ 2 * ((N : ℝ) * (t + 2)) by positivity)
        have h02 := mul_le_mul h01 htr htr0
          (show 0 ≤ 2 * ((N : ℝ) * (t + 2)) * (a / t) by positivity)
        exact mul_le_mul h02 hlast.2 hlast.1 (by positivity)
      _ = _ := by field_simp [ne_of_gt hn0, ne_of_gt ht0] <;> ring

end
end CriticalExtrapolation.Paper
