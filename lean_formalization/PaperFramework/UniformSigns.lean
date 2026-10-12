import PaperFramework.ScaledParameters
import PaperFramework.TrialDirection

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

theorem eventual_positive_initial_interval_of_limit (h ε : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hε : 0 < ε) (hε1 : ε < 1)
    (hlim : UniformOn 0 1 (fun N k => Real.log (N : ℝ) / (h ^ 2 * scaledC N h k) * auxiliaryValue N h (scaledC N h k)) (fun k => 1 - k ^ 2)) :
    ∀ᶠ N in atTop, ∀ k ∈ Set.Icc (0 : ℝ) (1 - ε),
      0 < auxiliaryValue N h (scaledC N h k) := by
  let δ : ℝ := 1 - (1 - ε) ^ 2
  have hδ : 0 < δ := by dsimp [δ]; nlinarith
  have hbound := hlim (δ / 2) (by positivity)
  filter_upwards [hbound, eventually_gt_atTop 1] with N hN hlarge
  intro k hk
  have hk1 : k ∈ Set.Icc (0 : ℝ) 1 := ⟨hk.1, by linarith [hk.2]⟩
  have herr := (abs_lt.mp (hN k hk1)).1
  have hsq : k ^ 2 ≤ (1 - ε) ^ 2 := by
    nlinarith [mul_nonneg (by linarith [hk.2] : 0 ≤ 1 - ε - k)
      (by linarith [hk.1] : 0 ≤ 1 - ε + k)]
  have hprod : 0 < Real.log (N : ℝ) / (h ^ 2 * scaledC N h k) *
      auxiliaryValue N h (scaledC N h k) := by dsimp [δ] at herr; linarith
  have hcoef : 0 < Real.log (N : ℝ) / (h ^ 2 * scaledC N h k) := by
    have hNr : (1 : ℝ) < N := by exact_mod_cast hlarge
    exact div_pos (Real.log_pos hNr)
      (mul_pos (sq_pos_of_pos hh) (lt_of_lt_of_le zero_lt_one (scaledC_ge_one N h k hh hk.1)))
  exact (mul_pos_iff_of_pos_left hcoef).mp hprod

theorem eventual_strictly_feasible_negative_trial_of_limit (h ε : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hε : 0 < ε)
    (hlim : UniformOn 0 (2 + ε) (fun N k => Real.log (N : ℝ) / (h ^ 2 * scaledC N h k) * chainObjective h (scaledC N h k) (trialDirection N (scaledA N h k) (1 / h))) (fun k => 1 - k ^ 2)) :
    ∀ᶠ N in atTop,
      StrictlyFeasible h (scaledC N h (1 + ε)) (trialDirection N (scaledA N h (1 + ε)) (1 / h)) ∧
      chainObjective h (scaledC N h (1 + ε)) (trialDirection N (scaledA N h (1 + ε)) (1 / h)) < 0 := by
  have hpoint : 1 + ε ∈ Set.Icc (0 : ℝ) (2 + ε) := ⟨by linarith, by linarith⟩
  let δ : ℝ := (1 + ε) ^ 2 - 1
  have hδ : 0 < δ := by dsimp [δ]; nlinarith
  have hbound := hlim (δ / 2) (by positivity)
  filter_upwards [hbound, eventual_scaled_parameter_range h (2 + ε) hh,
    eventually_gt_atTop 1] with N hN ha hlarge
  have hp := scaledC_parameters N h (1 + ε) (by omega) hh hh1 (by linarith)
  have hid := scaledA_identity N h (1 + ε) hlarge hh
  have hstrict := trial_strict_feasibility N h (scaledC N h (1 + ε)) hp
    (by rw [hid]; exact (ha (1 + ε) hpoint).2)
  rw [hid] at hstrict
  refine ⟨hstrict, ?_⟩
  have herr := (abs_lt.mp (hN (1 + ε) hpoint)).2
  have hprod : Real.log (N : ℝ) / (h ^ 2 * scaledC N h (1 + ε)) *
      chainObjective h (scaledC N h (1 + ε)) (trialDirection N (scaledA N h (1 + ε)) (1 / h)) < 0 := by
    dsimp [δ] at herr
    linarith
  have hcoef : 0 < Real.log (N : ℝ) / (h ^ 2 * scaledC N h (1 + ε)) := by
    have hNr : (1 : ℝ) < N := by exact_mod_cast hlarge
    exact div_pos (Real.log_pos hNr) (mul_pos (sq_pos_of_pos hh) (lt_of_lt_of_le zero_lt_one hp.c_ge_one))
  by_contra hnonneg
  exact (not_lt_of_ge (mul_nonneg hcoef.le (le_of_not_gt hnonneg))) hprod


end
end CriticalExtrapolation.Paper

