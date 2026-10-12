import PaperFramework.TrialUniformAlgebra

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

/-- Composition of the two genuine energy estimates with the normalization asymptotic.
This lemma does not prove those estimates; the original energy obligations remain separate. -/
theorem trial_energy_uniform_limit_from_estimates (t : ℝ) (ht : 1 ≤ t)
    (href : Tendsto (fun N : ℕ => homogeneousEnergy 0 1 (trialVector N t) /
      Real.log (N : ℝ)) atTop (𝓝 4))
    (hpert : ∃ C : ℝ, 0 < C ∧ ∀ N, 0 < N → ∀ a ∈ Set.Icc (0 : ℝ) (trialParameterMax t),
      |homogeneousEnergy a t (trialVector N t) - homogeneousEnergy 0 1 (trialVector N t)| ≤
        C * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ))) :
    UniformOn 0 (trialParameterMax t)
      (fun N a => Real.log (N : ℝ) * homogeneousEnergy a t (normalizedTrial N t))
      (fun _ => 1) := by
  obtain ⟨C, hC, hpertC⟩ := hpert
  let l : ℕ → ℝ := fun N => Real.log (N : ℝ)
  let H : ℕ → ℝ := fun N => trialNormalization N t
  let v : ℕ → ℝ := fun N => (homogeneousEnergy 0 1 (trialVector N t) / l N) / (H N / l N) ^ 2
  let b : ℕ → ℝ := fun N => C * (1 / l N + l N / (N : ℝ)) / (H N / l N) ^ 2
  have hratio : Tendsto (fun N => H N / l N) atTop (𝓝 2) :=
    trialNormalization_div_log_tendsto t ht
  have hv : Tendsto v atTop (𝓝 1) := by
    convert href.div (hratio.pow 2) (by norm_num : (2 : ℝ) ^ 2 ≠ 0) using 1 <;> norm_num
  have hinv : Tendsto (fun N => 1 / l N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hb : Tendsto b atTop (𝓝 0) := by
    convert ((tendsto_const_nhds (x := C)).mul (hinv.add log_div_nat_tendsto_zero)).div
      (hratio.pow 2) (by norm_num : (2 : ℝ) ^ 2 ≠ 0) using 1 <;> norm_num
  apply uniformOn_of_tendsto_error_bound 0 (trialParameterMax t) 1 _ v b hv hb
  filter_upwards [eventually_ge_atTop 2] with N hN
  intro a ha
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hl : 0 < l N := Real.log_pos hNr
  have hH : 0 < H N := trial_normalization_positive N t (by omega) ht
  have hcoef : 0 ≤ l N / (H N) ^ 2 := div_nonneg hl.le (sq_nonneg _)
  have hid : l N * (homogeneousEnergy a t (trialVector N t) / (H N) ^ 2) - v N =
      l N / (H N) ^ 2 * (homogeneousEnergy a t (trialVector N t) -
        homogeneousEnergy 0 1 (trialVector N t)) := by
    dsimp [v]
    field_simp [ne_of_gt hl, ne_of_gt hH]
    <;> ring
  change |l N * homogeneousEnergy a t (normalizedTrial N t) - v N| ≤ b N
  rw [normalizedTrial_energy, hid, abs_mul, abs_of_nonneg hcoef]
  calc
    _ ≤ l N / (H N) ^ 2 * (C * (1 + (l N) ^ 2 / (N : ℝ))) :=
      mul_le_mul_of_nonneg_left (hpertC N (by omega) a ha) hcoef
    _ = b N := by
      dsimp [b]
      field_simp [ne_of_gt hl, ne_of_gt hH]
      <;> ring

end
end CriticalExtrapolation.Paper
