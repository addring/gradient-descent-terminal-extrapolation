import PaperFramework.UniformLowerLimit
import PaperFramework.TrialScaledLimitProof

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

theorem uniformOn_of_sandwich (lo hi : ℝ) (f l u : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hl : UniformOn lo hi l g) (hu : UniformOn lo hi u g)
    (hb : ∀ᶠ N in atTop, ∀ k ∈ Set.Icc lo hi, l N k ≤ f N k ∧ f N k ≤ u N k) :
    UniformOn lo hi f g := by
  intro ε hε
  filter_upwards [hl ε hε, hu ε hε, hb] with N hL hU hB
  intro k hk
  have hL' := abs_lt.mp (hL k hk)
  have hU' := abs_lt.mp (hU k hk)
  have hB' := hB k hk
  apply abs_lt.mpr
  constructor <;> linarith [hL'.1, hU'.2, hB'.1, hB'.2]

theorem auxiliaryValue_le_chainObjective (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (hβ : Feasible h c β) : auxiliaryValue N h c ≤ chainObjective h c β := by
  obtain ⟨p, hpopt, _⟩ := optimizer_exists_unique N h c hp
  rw [auxiliaryValue_attained N h c hp p hpopt]
  exact hpopt.2 β hβ

theorem auxiliary_uniform_scaled_limit_proved (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (K : ℝ) :
    UniformOn 0 K
      (fun N k => Real.log (N : ℝ) / (h ^ 2 * scaledC N h k) *
        auxiliaryValue N h (scaledC N h k)) (fun k => 1 - k ^ 2) := by
  apply uniformOn_of_sandwich 0 K _
    (fun N k => Real.log (N : ℝ) * finiteLowerBound N h (scaledC N h k))
    (fun N k => Real.log (N : ℝ) / (h ^ 2 * scaledC N h k) *
      chainObjective h (scaledC N h k) (trialDirection N (scaledA N h k) (1 / h))) _
    (finiteLowerBound_uniform_scaled_limit h hh K)
    (trial_objective_uniform_scaled_limit_proved h hh hh1 K)
  filter_upwards [eventually_gt_atTop 1, eventual_scaled_parameter_range h K hh] with N hN hA
  intro k hk
  have hp := scaledC_parameters N h k (by omega) hh hh1 hk.1
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos hn
  have hc : 0 < scaledC N h k := lt_of_lt_of_le zero_lt_one hp.c_ge_one
  have hcoef : 0 ≤ Real.log (N : ℝ) / (h ^ 2 * scaledC N h k) :=
    (div_pos hl (mul_pos (sq_pos_of_pos hh) hc)).le
  have htrial := trial_strict_feasibility N h (scaledC N h k) hp
    (by rw [scaledA_identity N h k hN hh]; exact (hA k hk).2)
  rw [scaledA_identity N h k hN hh] at htrial
  constructor
  · calc
      _ ≤ Real.log (N : ℝ) * (auxiliaryValue N h (scaledC N h k) / (h ^ 2 * scaledC N h k)) :=
        mul_le_mul_of_nonneg_left (qp_energy_lower_bound N h (scaledC N h k) hp) hl.le
      _ = _ := by ring
  · exact mul_le_mul_of_nonneg_left
      (auxiliaryValue_le_chainObjective N h (scaledC N h k) hp _
        (strictlyFeasible_feasible h (scaledC N h k) _ htrial)) hcoef

end
end CriticalExtrapolation.Paper
