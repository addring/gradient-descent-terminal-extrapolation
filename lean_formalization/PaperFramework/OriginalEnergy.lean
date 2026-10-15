import PaperFramework.TrialAsymptotics

namespace CriticalExtrapolation.Paper
open scoped BigOperators
open Filter Topology
noncomputable section

def originalEnergyConstant (A t : ℝ) : ℝ :=
  2 * (A + t + 1) * (A + t) * trialWeightConstant t

/-- A one-sided estimate suffices, and holds on every fixed compact a interval. -/
theorem original_energy_perturbation_upper (N : ℕ) (a t A : ℝ)
    (hN : 0 < N) (ht : 1 ≤ t) (hA : 0 ≤ A) (ha : a ∈ Set.Icc (0 : ℝ) A) :
    homogeneousEnergy a t (trialVector N t) ≤
      homogeneousEnergy 0 1 (trialVector N t) +
        originalEnergyConstant A t * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ)) := by
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : 0 < (N : ℝ) := by linarith
  have ht0 : 0 < t := by linarith
  have hc : 0 ≤ a + t - 1 := by linarith [ha.1]
  have hct : a + t - 1 ≤ A + t := by linarith [ha.2]
  have hJ0 := trial_baseline_J_nonnegative N t ht
  have hF : 0 ≤ energyF N a t := by unfold energyF; linarith [ha.1]
  have hFup : energyF N a t / (N : ℝ) ≤ A + t + 1 := by
    apply (div_le_iff₀ hn0).mpr
    unfold energyF
    nlinarith [ha.2, mul_nonneg (sub_nonneg.mpr hn) (by linarith : 0 ≤ A + t)]
  have hd := trial_J_parameter_difference_bound N a t ha.1 ht
  have hw := trial_weighted_sum_log_bound N t hN ht
  let K : ℝ := trialWeightConstant t * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; exact mul_nonneg (trialWeightConstant_positive t).le (by positivity)
  have hdiff : |trialEnergyJ a t (trialVector N t) - trialEnergyJ 0 1 (trialVector N t)| ≤
      (A + t) * K / (N : ℝ) := by
    apply (le_div_iff₀ hn0).mpr
    calc
      _ ≤ (a + t - 1) * ((N : ℝ) *
          (∑ i : Fin N, ((i.val : ℝ) + 1) * difference (trialVector N t) i *
            trialVector N t i / ((N : ℝ) - i.val))) := by
        have hh := mul_le_mul_of_nonneg_right hd hn0.le
        convert hh using 1 <;> ring
      _ ≤ (a + t - 1) * K := mul_le_mul_of_nonneg_left hw hc
      _ ≤ (A + t) * K := mul_le_mul_of_nonneg_right hct hK
  have hpert : 2 * energyF N a t *
      |trialEnergyJ a t (trialVector N t) - trialEnergyJ 0 1 (trialVector N t)| ≤
      originalEnergyConstant A t * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ)) := by
    calc
      _ ≤ 2 * energyF N a t * ((A + t) * K / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = (energyF N a t / (N : ℝ)) * (2 * (A + t) * K) := by ring
      _ ≤ (A + t + 1) * (2 * (A + t) * K) :=
        mul_le_mul_of_nonneg_right hFup (by positivity)
      _ = _ := by unfold originalEnergyConstant; dsimp [K]; ring
  have he := homogeneousEnergy_parameter_difference a t (trialVector N t)
  have habs := neg_abs_le (trialEnergyJ a t (trialVector N t) - trialEnergyJ 0 1 (trialVector N t))
  have hprod := mul_le_mul_of_nonneg_left habs (show 0 ≤ 2 * energyF N a t by positivity)
  have hnonneg := mul_nonneg hc hJ0
  linarith only [he, hprod, hnonneg, hpert]

/-- Uniform upper energy asymptotic on any fixed interval [0,A]. -/
theorem original_energy_eventual_upper (t A δ : ℝ)
    (ht : 1 ≤ t) (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ a ∈ Set.Icc (0 : ℝ) A,
      Real.log (N : ℝ) * homogeneousEnergy a t (normalizedTrial N t) < 1 + δ := by
  let l : ℕ → ℝ := fun N => Real.log (N : ℝ)
  let H : ℕ → ℝ := fun N => trialNormalization N t
  let v : ℕ → ℝ := fun N =>
    (homogeneousEnergy 0 1 (trialVector N t) / l N) / (H N / l N) ^ 2
  let b : ℕ → ℝ := fun N =>
    originalEnergyConstant A t * (1 / l N + l N / (N : ℝ)) / (H N / l N) ^ 2
  have hratio := trialNormalization_div_log_tendsto t ht
  have hv : Tendsto v atTop (𝓝 1) := by
    convert (trial_reference_energy_limit t ht).div (hratio.pow 2)
      (by norm_num : (2 : ℝ) ^ 2 ≠ 0) using 1 <;> norm_num
  have hinv : Tendsto (fun N => 1 / l N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hb : Tendsto b atTop (𝓝 0) := by
    convert ((tendsto_const_nhds (x := originalEnergyConstant A t)).mul
      (hinv.add log_div_nat_tendsto_zero)).div (hratio.pow 2)
      (by norm_num : (2 : ℝ) ^ 2 ≠ 0) using 1 <;> norm_num
  have hsmall : ∀ᶠ N in atTop, v N + b N < 1 + δ := by
    have hlim : Tendsto (fun N => v N + b N) atTop (𝓝 1) := by simpa using hv.add hb
    exact hlim.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hsmall, eventually_ge_atTop 2] with N hs hN
  intro a ha
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hl : 0 < l N := Real.log_pos hNr
  have hH : 0 < H N := trial_normalization_positive N t (by omega) ht
  have hbound := mul_le_mul_of_nonneg_left
    (original_energy_perturbation_upper N a t A (by omega) ht hA ha)
    (show 0 ≤ l N / (H N) ^ 2 by positivity)
  have hid : l N / (H N) ^ 2 *
      (homogeneousEnergy 0 1 (trialVector N t) +
        originalEnergyConstant A t * (1 + (l N) ^ 2 / (N : ℝ))) = v N + b N := by
    dsimp [v, b]
    have hn : (N : ℝ) ≠ 0 := ne_of_gt (by positivity : 0 < (N : ℝ))
    field_simp [ne_of_gt hl, ne_of_gt hH, hn]
    <;> ring
  rw [hid] at hbound
  rw [normalizedTrial_energy]
  change l N * (homogeneousEnergy a t (trialVector N t) / (H N) ^ 2) < _
  have he : l N * (homogeneousEnergy a t (trialVector N t) / (H N) ^ 2) =
      l N / (H N) ^ 2 * homogeneousEnergy a t (trialVector N t) := by ring
  rw [he]
  exact hbound.trans_lt hs

end
end CriticalExtrapolation.Paper
