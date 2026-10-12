import PaperFramework.TrialWeightedSum

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem trial_baseline_J_nonnegative (N : ℕ) (t : ℝ) (ht : 1 ≤ t) :
    0 ≤ trialEnergyJ 0 1 (trialVector N t) := by
  unfold trialEnergyJ
  apply Finset.sum_nonneg
  intro i _
  have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
  have hw := (trial_tail_bounds N t ht i).1
  have hd := trialVector_differences_nonnegative N t ht i
  unfold energyD
  simp only [add_zero, one_mul]
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) hd) hw) (sub_pos.mpr hi).le

theorem trial_parameter_le_one (t a : ℝ) (ht : 1 ≤ t)
    (ha : a ∈ Set.Icc (0 : ℝ) (trialParameterMax t)) : a ≤ 1 := by
  have hp : 0 < 2 * t + 1 := by linarith
  exact ha.2.trans ((div_le_one hp).mpr (by linarith))

theorem trial_J_difference_log_bound (N : ℕ) (a t : ℝ) (hN : 0 < N) (ht : 1 ≤ t)
    (ha : a ∈ Set.Icc (0 : ℝ) (trialParameterMax t)) :
    |trialEnergyJ a t (trialVector N t) - trialEnergyJ 0 1 (trialVector N t)| ≤
      t * trialWeightConstant t * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ)) / (N : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hc : 0 ≤ a + t - 1 := by linarith [ha.1]
  have hct : a + t - 1 ≤ t := by linarith [trial_parameter_le_one t a ht ha]
  have hd := trial_J_parameter_difference_bound N a t ha.1 ht
  have hw := trial_weighted_sum_log_bound N t hN ht
  have hC : 0 ≤ trialWeightConstant t * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ)) := by
    exact mul_nonneg (trialWeightConstant_positive t).le (by positivity)
  apply (le_div_iff₀ hn).mpr
  calc
    _ ≤ (a + t - 1) * ((N : ℝ) *
        (∑ i : Fin N, ((i.val : ℝ) + 1) * difference (trialVector N t) i *
          trialVector N t i / ((N : ℝ) - i.val))) := by
      have hh := mul_le_mul_of_nonneg_right hd hn.le
      simpa only [mul_assoc, mul_comm (N : ℝ), mul_left_comm (N : ℝ)] using hh
    _ ≤ (a + t - 1) *
        (trialWeightConstant t * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hw hc
    _ ≤ t * (trialWeightConstant t * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ))) :=
      mul_le_mul_of_nonneg_right hct hC
    _ = _ := by ring

theorem trial_normalization_square_bound (N : ℕ) (t : ℝ) (hN : 0 < N) (ht : 1 ≤ t) :
    (trialNormalization N t) ^ 2 ≤
      8 * (Real.log (N : ℝ)) ^ 2 + 2 * (4 * t + 2) ^ 2 := by
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hl := Real.log_nonneg hn
  have hh := (abs_le.mp (trial_normalization_log_error N t hN ht)).2
  have hp := (trial_normalization_positive N t hN ht).le
  have hupper : trialNormalization N t ≤ 2 * Real.log (N : ℝ) + (4 * t + 2) := by linarith
  have hs : (trialNormalization N t) ^ 2 ≤
      (2 * Real.log (N : ℝ) + (4 * t + 2)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hupper)
      (by linarith : 0 ≤ 2 * Real.log (N : ℝ) + (4 * t + 2) + trialNormalization N t)]
  nlinarith [sq_nonneg (2 * Real.log (N : ℝ) - (4 * t + 2))]

theorem trial_reference_J_log_bound (N : ℕ) (t : ℝ) (hN : 0 < N) (ht : 1 ≤ t) :
    2 * t * trialEnergyJ 0 1 (trialVector N t) ≤
      t * (8 + 2 * (4 * t + 2) ^ 2) * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ)) := by
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : 0 < (N : ℝ) := by linarith
  have hu := trial_baseline_J_upper N t hN ht
  have hs := trial_normalization_square_bound N t hN ht
  have hB : 0 ≤ 2 * (4 * t + 2) ^ 2 := by positivity
  have hBdiv : 2 * (4 * t + 2) ^ 2 / (N : ℝ) ≤ 2 * (4 * t + 2) ^ 2 :=
    (div_le_iff₀ hn0).mpr (le_mul_of_one_le_right hB hn)
  have hL : 0 ≤ (Real.log (N : ℝ)) ^ 2 / (N : ℝ) := by positivity
  calc
    _ ≤ t * (trialNormalization N t) ^ 2 / ((N : ℝ) + 1) := by
      have hh := mul_le_mul_of_nonneg_left hu (by linarith : 0 ≤ 2 * t)
      have he : 2 * t * ((trialNormalization N t) ^ 2 / (2 * ((N : ℝ) + 1))) =
          t * (trialNormalization N t) ^ 2 / ((N : ℝ) + 1) := by
        field_simp [ne_of_gt (show 0 < (N : ℝ) + 1 by positivity)]
        <;> ring
      rw [he] at hh
      exact hh
    _ ≤ t * (trialNormalization N t) ^ 2 / (N : ℝ) := by
      apply (div_le_div_iff₀ (by positivity) hn0).mpr
      exact mul_le_mul_of_nonneg_left (by linarith : (N : ℝ) ≤ (N : ℝ) + 1) (by positivity)
    _ ≤ t * (8 * (Real.log (N : ℝ)) ^ 2 + 2 * (4 * t + 2) ^ 2) / (N : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by linarith)) hn0.le
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hBdiv (by linarith : 0 ≤ t)
      have hmore := mul_nonneg (mul_nonneg (by linarith : 0 ≤ t) hB) hL
      simp only [div_eq_mul_inv] at hh hmore ⊢
      nlinarith only [hh, hmore, ht]

def trialPerturbationConstant (t : ℝ) : ℝ :=
  t * (8 + 2 * (4 * t + 2) ^ 2) + 2 * (t + 2) * t * trialWeightConstant t + 1

theorem trial_energy_uniform_perturbation_proved (t : ℝ) (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ N, 0 < N → ∀ a ∈ Set.Icc (0 : ℝ) (trialParameterMax t),
      |homogeneousEnergy a t (trialVector N t) - homogeneousEnergy 0 1 (trialVector N t)| ≤
        C * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ)) := by
  refine ⟨trialPerturbationConstant t, ?_, ?_⟩
  · unfold trialPerturbationConstant
    have hC := trialWeightConstant_positive t
    have ht0 : 0 < t := by linarith
    positivity
  · intro N hN a ha
    have hn : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hn0 : 0 < (N : ℝ) := by linarith
    have ha1 := trial_parameter_le_one t a ht ha
    have hc : 0 ≤ a + t - 1 := by linarith [ha.1]
    have hct : a + t - 1 ≤ t := by linarith
    have hJ0 := trial_baseline_J_nonnegative N t ht
    have hF : 0 ≤ energyF N a t := by unfold energyF; linarith [ha.1]
    have hFup : energyF N a t / (N : ℝ) ≤ t + 2 := by
      apply (div_le_iff₀ hn0).mpr
      unfold energyF
      nlinarith [mul_nonneg (by linarith : 0 ≤ t + 1) (sub_nonneg.mpr hn)]
    have hd := trial_J_difference_log_bound N a t hN ht ha
    have hbase := trial_reference_J_log_bound N t hN ht
    have hK : 0 ≤ 1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ) := by positivity
    have hC := (trialWeightConstant_positive t).le
    have hpert : 2 * energyF N a t *
        |trialEnergyJ a t (trialVector N t) - trialEnergyJ 0 1 (trialVector N t)| ≤
        2 * (t + 2) * t * trialWeightConstant t *
          (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ)) := by
      calc
        _ ≤ 2 * energyF N a t *
            (t * trialWeightConstant t * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ)) / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num) hF)
        _ = (energyF N a t / (N : ℝ)) *
            (2 * t * trialWeightConstant t * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ))) := by ring
        _ ≤ _ := by
          have hM : 0 ≤ 2 * t * trialWeightConstant t *
              (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ)) :=
            mul_nonneg (mul_nonneg
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ t)) hC) hK
          have hh := mul_le_mul_of_nonneg_right hFup hM
          convert hh using 1 <;> ring
    have he := homogeneousEnergy_parameter_difference a t (trialVector N t)
    rw [he]
    have hab : |-2 * (a + t - 1) * trialEnergyJ 0 1 (trialVector N t)| =
        2 * (a + t - 1) * trialEnergyJ 0 1 (trialVector N t) := by
      rw [abs_of_nonpos (by nlinarith [mul_nonneg hc hJ0])]
      ring
    have hac : |-2 * energyF N a t *
        (trialEnergyJ a t (trialVector N t) - trialEnergyJ 0 1 (trialVector N t))| =
        2 * energyF N a t *
          |trialEnergyJ a t (trialVector N t) - trialEnergyJ 0 1 (trialVector N t)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hF]
      norm_num
    have htriangle : |-2 * (a + t - 1) * trialEnergyJ 0 1 (trialVector N t) -
        2 * energyF N a t * (trialEnergyJ a t (trialVector N t) -
          trialEnergyJ 0 1 (trialVector N t))| ≤
        2 * (a + t - 1) * trialEnergyJ 0 1 (trialVector N t) +
          2 * energyF N a t *
            |trialEnergyJ a t (trialVector N t) - trialEnergyJ 0 1 (trialVector N t)| := by
      have hh := norm_add_le
        (-2 * (a + t - 1) * trialEnergyJ 0 1 (trialVector N t))
        (-2 * energyF N a t * (trialEnergyJ a t (trialVector N t) -
          trialEnergyJ 0 1 (trialVector N t)))
      simp only [Real.norm_eq_abs, hab, hac] at hh
      rw [show -2 * (a + t - 1) * trialEnergyJ 0 1 (trialVector N t) -
          2 * energyF N a t * (trialEnergyJ a t (trialVector N t) -
            trialEnergyJ 0 1 (trialVector N t)) =
          -2 * (a + t - 1) * trialEnergyJ 0 1 (trialVector N t) +
            (-2 * energyF N a t * (trialEnergyJ a t (trialVector N t) -
              trialEnergyJ 0 1 (trialVector N t))) by ring]
      exact hh
    have hbase' : 2 * (a + t - 1) * trialEnergyJ 0 1 (trialVector N t) ≤
        t * (8 + 2 * (4 * t + 2) ^ 2) * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ)) := by
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hct (by norm_num : (0 : ℝ) ≤ 2)) hJ0).trans hbase
    unfold trialPerturbationConstant
    linarith only [htriangle, hbase', hpert, hK]

end
end CriticalExtrapolation.Paper
