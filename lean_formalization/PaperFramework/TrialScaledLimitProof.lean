import PaperFramework.TrialScaledIdentity
import PaperFramework.UniformMassBounds
import PaperFramework.UniformTerminalBounds
import PaperFramework.UniformErrorBounds
import PaperFramework.TrialReferenceModelLimit
import PaperFramework.TrialUniformLimitProof
import PaperFramework.TrialPerturbationProof

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

theorem trial_energy_scaled_parameter_uniform_limit (h : ℝ) (hh : 0 < h)
    (hh1 : h ≤ 1) (K : ℝ) :
    UniformOn 0 K (fun N k => Real.log (N : ℝ) *
      homogeneousEnergy (scaledA N h k) (1 / h) (normalizedTrial N (1 / h))) (fun _ => 1) := by
  have ht : 1 ≤ 1 / h := (le_div_iff₀ hh).mpr (by simpa using hh1)
  have he := trial_energy_uniform_limit_from_estimates (1 / h) ht
    (trial_reference_energy_limit_proved (1 / h) ht) (trial_energy_uniform_perturbation_proved (1 / h) ht)
  intro ε hε
  filter_upwards [he ε hε, eventual_scaled_parameter_range h K hh] with N hE hA
  intro k hk
  exact hE (scaledA N h k) (hA k hk)

theorem trialNormalization_eventually_ge_log (t : ℝ) (ht : 1 ≤ t) :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≤ trialNormalization N t := by
  have hr := (trialNormalization_div_log_tendsto t ht).eventually
    (eventually_gt_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [hr, eventually_gt_atTop 1] with N hR hN
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hh := (lt_div_iff₀ (Real.log_pos hn)).mp hR
  simpa only [one_mul] using hh.le

theorem trial_objective_uniform_scaled_limit_proved (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (K : ℝ) :
    UniformOn 0 K
      (fun N k => Real.log (N : ℝ) / (h ^ 2 * scaledC N h k) *
        chainObjective h (scaledC N h k) (trialDirection N (scaledA N h k) (1 / h)))
      (fun k => 1 - k ^ 2) := by
  let t : ℝ := 1 / h
  let e : ℕ → ℝ → ℝ := fun N k => Real.log (N : ℝ) *
    homogeneousEnergy (scaledA N h k) t (normalizedTrial N t)
  let C : ℝ := 4 * (t + 2) * (t - 1) / t
  let b : ℕ → ℝ := fun N => (1 + K ^ 2) * (2 * scaledA N h K / t) +
    Real.log (N : ℝ) * scaledA N h K / (N : ℝ) + C * scaledA N h K
  have ht : 1 ≤ t := (le_div_iff₀ hh).mpr (by simpa using hh1)
  have ht0 : 0 < t := by linarith
  have hC : 0 ≤ C := div_nonneg (mul_nonneg (by positivity) (by linarith)) ht0.le
  have he : UniformOn 0 K e (fun _ => 1) := trial_energy_scaled_parameter_uniform_limit h hh hh1 K
  have hmass : Tendsto (fun N : ℕ => (1 + K ^ 2) * (2 * scaledA N h K / t))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 1 + K ^ 2)).mul
      (((tendsto_const_nhds (x := (2 : ℝ))).mul (scaledA_tendsto_zero h K hh)).div_const t)
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa only [zero_add, mul_zero] using
      (hmass.add (log_scaledA_div_nat_tendsto_zero h K hh)).add
        ((tendsto_const_nhds (x := C)).mul (scaledA_tendsto_zero h K hh))
  apply uniformOn_of_error_plus_uniform 0 K _ e _ b he hb
  filter_upwards [eventually_gt_atTop 1, eventual_scaled_parameter_range h K hh,
    trialNormalization_eventually_ge_log t ht] with N hN hA hH
  intro k hk
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos hn
  have ha := hA k hk
  have ha0 : 0 ≤ scaledA N h k := ha.1
  have ha01 : scaledA N h k ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨ha.1, trial_parameter_le_one t (scaledA N h k) ht ha⟩
  have hmono : scaledA N h k ≤ scaledA N h K := div_le_div_of_nonneg_right hk.2 (by positivity)
  have hmain := scaled_mass_main_error_bound (scaledA N h k) t (e N k) k K ha.1 ht0 hk
  have hmassmono : (1 + K ^ 2) * (2 * scaledA N h k / t) ≤
      (1 + K ^ 2) * (2 * scaledA N h K / t) :=
    mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmono (by norm_num)) ht0.le) (by positivity)
  have hmain' := abs_le.mp (hmain.trans (add_le_add (le_refl _) hmassmono))
  have hd0 : 0 ≤ Real.log (N : ℝ) * scaledA N h k / (N : ℝ) := by positivity
  have hd : Real.log (N : ℝ) * scaledA N h k / (N : ℝ) ≤
      Real.log (N : ℝ) * scaledA N h K / (N : ℝ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hl.le) (Nat.cast_nonneg _)
  let i : Fin N := ⟨N - 1, by omega⟩
  let corr : ℝ := Real.log (N : ℝ) *
    (2 * energyF N (scaledA N h k) t * shiftMass (scaledA N h k) t *
      shiftB N (scaledA N h k) t * (N : ℝ) * (t - 1) /
      (scaledA N h k + 1) * normalizedTrial N t i)
  have hc := trial_terminal_scaled_correction_bound N (scaledA N h k) t hN ha01 ht i
    (by dsimp [i]; omega) hH
  have hc0 : 0 ≤ corr := hc.1
  have hcK : corr ≤ C * scaledA N h K := by
    calc
      _ ≤ 4 * (t + 2) * (t - 1) * scaledA N h k / t := hc.2
      _ = C * scaledA N h k := by dsimp [C]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmono hC
  rw [trial_objective_scaled_identity N h k hN hh hh1 hk.1]
  change |(shiftMass (scaledA N h k) t) ^ 2 * (e N k - k ^ 2) -
    Real.log (N : ℝ) * scaledA N h k / (N : ℝ) + corr - (1 - k ^ 2)| ≤ |e N k - 1| + b N
  dsimp only [b]
  apply abs_le.mpr
  constructor <;> linarith [hmain'.1, hmain'.2]

end
end CriticalExtrapolation.Paper
