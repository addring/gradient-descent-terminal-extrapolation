import PaperFramework.Sufficiency
import PaperFramework.GlobalRealization
import PaperFramework.UniformLimit
import PaperFramework.InitialInterval
import PaperFramework.ScaledParameters
import PaperFramework.FiniteLowerAtOne
import PaperFramework.ChainContinuity
import PaperFramework.LargeQuadratic

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

/-- Finite-horizon validity near one follows from the positive chain matrix and continuity. -/
theorem near_one_validity (N : ℕ) (h L D : ℝ) (hN : 0 < N)
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 0 < L) (hD : 0 < D) :
    ∃ δ > 0, ∀ c ∈ Set.Icc (1 : ℝ) (1 + δ),
      worstGradient N h c L D = L * D / S N h c := by
  obtain ⟨δ, hδ, hmatrix⟩ := Metric.eventually_nhds_iff.mp
    (chain_positive_near_one N h hN hh hh1)
  refine ⟨δ / 2, by positivity, ?_⟩
  intro c hc
  have hdist : dist c 1 < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hc.1)]
    linarith [hc.2]
  have hpos := hmatrix hdist
  have hM : NonnegativeQuadratic (M₀ N h c) := by
    intro p
    by_cases hp : p = 0
    · simp [hp, quadraticForm]
    · exact (hpos p hp).le
  have hp : Parameters N h c := ⟨hN, hh, hh1, hc.1⟩
  have hunit := forward_certificate_exact N h c hp (chainFlow N) (chainFlow_admissible N) hM
  rw [worstGradient_scaling N h c L D hp hL hD, hunit]
  simp only [div_eq_mul_inv, one_mul, mul_assoc]

/-- A quadratic actual function eventually violates the proposed bound as c grows. -/
theorem large_coefficient_failure (N : ℕ) (h L D : ℝ) (hN : 0 < N)
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 0 < L) (hD : 0 < D) :
    ∃ C ≥ 1, L * D / S N h C < worstGradient N h C L D := by
  exact large_coefficient_failure_proved N h L D hN hh hh1 hL hD

theorem initial_endpoints_nonempty_bounded (N : ℕ) (h L D : ℝ) (hN : 0 < N)
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 0 < L) (hD : 0 < D) :
    (initialValidityEndpoints N h L D).Nonempty ∧
      BddAbove (initialValidityEndpoints N h L D) := by
  obtain ⟨δ, hδ, hvalid⟩ := near_one_validity N h L D hN hh hh1 hL hD
  obtain ⟨B, hB, hfailure⟩ := large_coefficient_failure N h L D hN hh hh1 hL hD
  exact initial_endpoints_of_interval_and_failure N h L D (1 + δ) (by linarith)
    hvalid B hB hfailure

theorem eventual_lower_interval_open_step (h L D ε : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hL : 0 < L) (hD : 0 < D)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ N in atTop, ∀ c ∈ Set.Icc (1 : ℝ) (scaledC N h (1 - ε)),
      worstGradient N h c L D = L * D / S N h c := by
  have hpositive := eventual_positive_initial_interval h ε hh hh1.le hε hε1
  have hcoordinates : ∀ᶠ N : ℕ in atTop,
      (1 ≤ (N : ℝ) * h ^ 2) ∧ ∀ c ∈ Set.Icc (1 : ℝ) (scaledC N h (1 - ε)),
        Parameters N h c ∧ ∃ k ∈ Set.Icc (0 : ℝ) (1 - ε), scaledC N h k = c := by
    filter_upwards [eventual_step_square h hh, eventually_gt_atTop 1] with N hs hN
    exact ⟨hs, fun c hc => scaled_interval_coordinates N h (1 - ε) hN hh hh1.le c hc⟩
  filter_upwards [hpositive, hcoordinates] with N hpos hcoord
  intro c hc
  obtain ⟨hp, k, hk, heq⟩ := hcoord.2 c hc
  have hΦ : 0 ≤ auxiliaryValue N h c := by
    rw [← heq]
    exact (hpos k hk).le
  exact qp_sufficiency N h c L D hp hL hD hh1 hcoord.1 hΦ

/-- First pass a step-size bound for each fixed function; only then take its supremum. -/
theorem sufficiency_at_unit_step (N : ℕ) (c L D : ℝ) (hN : 1 < N) (hc : 1 ≤ c)
    (hL : 0 < L) (hD : 0 < D) (hlower : 0 < finiteLowerBound N 1 c) :
    worstGradient N 1 c L D = L * D / S N 1 c := by
  have hhuber := huber_lower_bound N 1 c L D ⟨by omega, zero_lt_one, le_rfl, hc⟩ hL hD
  have hcontinuous := finite_lower_bound_continuous_at_one N c (by omega) hc
  have hpositive : ∀ᶠ h : ℝ in 𝓝 1, 0 < finiteLowerBound N h c :=
    continuousAt_const.eventually_lt hcontinuous hlower
  have hsizeCont : ContinuousAt (fun h : ℝ => (N : ℝ) * h ^ 2) 1 := by fun_prop
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hsize : ∀ᶠ h : ℝ in 𝓝 1, 1 < (N : ℝ) * h ^ 2 :=
    continuousAt_const.eventually_lt hsizeCont (by simpa using hNr)
  have hposStep : ∀ᶠ h : ℝ in 𝓝[<] 1, 0 < h :=
    (show ∀ᶠ h : ℝ in 𝓝 1, 0 < h from Ioi_mem_nhds zero_lt_one).filter_mono
      nhdsWithin_le_nhds
  have hltStep : ∀ᶠ h : ℝ in 𝓝[<] 1, h < 1 := self_mem_nhdsWithin
  apply le_antisymm _ hhuber
  apply csSup_le (instance_values_nonempty_bounded N 1 c L D hL hD).1
  rintro r ⟨d, I, rfl⟩
  have hbound : ∀ᶠ h : ℝ in 𝓝[<] 1,
      ‖gradient I.f (output I N h c)‖ ≤ L * D / S N h c := by
    filter_upwards [hpositive.filter_mono nhdsWithin_le_nhds,
      hsize.filter_mono nhdsWithin_le_nhds, hposStep, hltStep] with h hlow hs hpos hlt
    have hp : Parameters N h c := ⟨by omega, hpos, hlt.le, hc⟩
    have henergy := qp_energy_lower_bound N h c hp
    have hΦ : 0 ≤ auxiliaryValue N h c := by
      have hden : 0 < h ^ 2 * c := mul_pos (sq_pos_of_pos hpos) (lt_of_lt_of_le zero_lt_one hc)
      have hratio : 0 < auxiliaryValue N h c / (h ^ 2 * c) := lt_of_lt_of_le hlow henergy
      exact ((div_pos_iff_of_pos_right hden).mp hratio).le
    have heq := qp_sufficiency N h c L D hp hL hD hlt hs.le hΦ
    have hsup := le_csSup (instance_values_nonempty_bounded N h c L D hL hD).2 ⟨d, I, rfl⟩
    change ‖gradient I.f (output I N h c)‖ ≤ worstGradient N h c L D at hsup
    rwa [heq] at hsup
  have hgrad : Tendsto (fun h : ℝ => ‖gradient I.f (output I N h c)‖)
      (𝓝[<] 1) (𝓝 ‖gradient I.f (output I N 1 c)‖) :=
    (continuous_output_gradient_norm I hL.le N c).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hden : S N 1 c ≠ 0 := ne_of_gt (S_positive N 1 c ⟨by omega, zero_lt_one, le_rfl, hc⟩)
  have hdenCont : ContinuousAt (fun h : ℝ => S N h c) 1 := by unfold S; fun_prop
  have hrhsCont : ContinuousAt (fun h : ℝ => L * D / S N h c) 1 :=
    continuousAt_const.div hdenCont hden
  have hrhs := hrhsCont.tendsto.mono_left
    (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
  exact le_of_tendsto_of_tendsto hgrad hrhs hbound

theorem eventual_lower_interval_fixed_step (h L D ε : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 0 < L) (hD : 0 < D)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ N in atTop, ∀ c ∈ Set.Icc (1 : ℝ) (scaledC N h (1 - ε)),
      worstGradient N h c L D = L * D / S N h c := by
  rcases lt_or_eq_of_le hh1 with hopen | rfl
  · exact eventual_lower_interval_open_step h L D ε hh hopen hL hD hε hε1
  · have hfinite := eventual_finite_lower_bound_at_one ε hε hε1
    have hlarge : ∀ᶠ N : ℕ in atTop, 1 < N := eventually_gt_atTop 1
    filter_upwards [hfinite, hlarge] with N hf hN
    intro c hc
    exact sufficiency_at_unit_step N c L D hN hc.1 hL hD (hf c hc)

theorem eventual_upper_failure_fixed_step (h L D ε : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 0 < L) (hD : 0 < D) (hε : 0 < ε) :
    ∀ᶠ N in atTop,
      L * D / S N h (scaledC N h (1 + ε)) <
        worstGradient N h (scaledC N h (1 + ε)) L D := by
  have hnegative := eventual_strictly_feasible_negative_trial h ε hh hh1 hε
  have hparams : ∀ᶠ N in atTop, Parameters N h (scaledC N h (1 + ε)) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact scaledC_parameters N h (1 + ε) hN hh hh1 (by linarith)
  filter_upwards [hnegative, hparams] with N hneg hp
  exact negative_direction_failure N h (scaledC N h (1 + ε)) L D hp hL hD
    (trialDirection N (scaledA N h (1 + ε)) (1 / h)) hneg.1 hneg.2

/-- Equations (12.1)--(12.2) concern the actual full validity interval. -/
theorem critical_interval_sandwich (h L D ε : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 0 < L) (hD : 0 < D)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ N in atTop,
      scaledC N h (1 - ε) ≤ criticalCoefficient N h L D ∧
      criticalCoefficient N h L D ≤ scaledC N h (1 + ε) := by
  have hlower := eventual_lower_interval_fixed_step h L D ε hh hh1 hL hD hε hε1
  have hupper := eventual_upper_failure_fixed_step h L D ε hh hh1 hL hD hε
  have hparams : ∀ᶠ N in atTop, 0 < N ∧ 1 ≤ scaledC N h (1 - ε) ∧
      1 ≤ scaledC N h (1 + ε) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact ⟨hN, scaledC_ge_one N h (1 - ε) hh (by linarith),
      scaledC_ge_one N h (1 + ε) hh (by linarith)⟩
  filter_upwards [hlower, hupper, hparams] with N hvalid hfailure hp
  obtain ⟨hne, hbdd⟩ := initial_endpoints_nonempty_bounded N h L D hp.1 hh hh1 hL hD
  exact ⟨critical_lower_of_interval N h L D (scaledC N h (1 - ε)) hp.2.1 hvalid hbdd,
    critical_upper_of_failure N h L D (scaledC N h (1 + ε)) hp.2.2 hfailure hne⟩

end
end CriticalExtrapolation.Paper
