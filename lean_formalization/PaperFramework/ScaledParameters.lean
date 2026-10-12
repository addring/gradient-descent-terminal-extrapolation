import PaperFramework.InitialInterval

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

theorem scaledC_ge_one (N : ℕ) (h k : ℝ) (hh : 0 < h) (hk : 0 ≤ k) :
    1 ≤ scaledC N h k := by
  unfold scaledC
  exact le_add_of_nonneg_right (div_nonneg hk (by positivity))

theorem scaledC_parameters (N : ℕ) (h k : ℝ) (hN : 0 < N)
    (hh : 0 < h) (hh1 : h ≤ 1) (hk : 0 ≤ k) : Parameters N h (scaledC N h k) :=
  ⟨hN, hh, hh1, scaledC_ge_one N h k hh hk⟩

theorem scaledA_identity (N : ℕ) (h k : ℝ) (hN : 1 < N) (hh : 0 < h) :
    (N : ℝ) * (scaledC N h k - 1) = scaledA N h k := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt (Real.log (N : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Real.log_pos hNr))
  unfold scaledC scaledA
  field_simp [hn, ne_of_gt hh, hs]
  <;> ring

theorem scaled_interval_coordinates (N : ℕ) (h K : ℝ) (hN : 1 < N)
    (hh : 0 < h) (hh1 : h ≤ 1) (c : ℝ) (hc : c ∈ Set.Icc (1 : ℝ) (scaledC N h K)) :
    Parameters N h c ∧ ∃ k ∈ Set.Icc (0 : ℝ) K, scaledC N h k = c := by
  let s : ℝ := h * (N : ℝ) * Real.sqrt (Real.log (N : ℝ))
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < s := mul_pos (mul_pos hh (lt_trans zero_lt_one hNr))
    (Real.sqrt_pos.mpr (Real.log_pos hNr))
  refine ⟨⟨by omega, hh, hh1, hc.1⟩, s * (c - 1), ⟨?_, ?_⟩, ?_⟩
  · exact mul_nonneg hs.le (sub_nonneg.mpr hc.1)
  · have hbound := mul_le_mul_of_nonneg_left (sub_le_sub_right hc.2 1) hs.le
    have hrescale := scaledC_rescale N h K (ne_of_gt hs)
    change s * (scaledC N h K - 1) = K at hrescale
    linarith
  · change 1 + s * (c - 1) / s = c
    rw [mul_div_cancel_left₀ _ (ne_of_gt hs)]
    ring

theorem sqrt_log_nat_tendsto_atTop :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log (N : ℝ))) atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hlog.eventually (eventually_ge_atTop (b ^ 2))] with N hN
  exact Real.le_sqrt_of_sq_le hN

theorem scaledA_tendsto_zero (h k : ℝ) (hh : 0 < h) :
    Tendsto (fun N : ℕ => scaledA N h k) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop (sqrt_log_nat_tendsto_atTop.const_mul_atTop hh)

theorem eventual_step_square (h : ℝ) (hh : 0 < h) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ (N : ℝ) * h ^ 2 := by
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) * h ^ 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (sq_pos_of_pos hh)
  exact hlim.eventually (eventually_ge_atTop 1)

theorem eventual_scaled_parameter_range (h K : ℝ) (hh : 0 < h) :
    ∀ᶠ N : ℕ in atTop, ∀ k ∈ Set.Icc (0 : ℝ) K,
      scaledA N h k ∈ Set.Icc (0 : ℝ) (trialParameterMax (1 / h)) := by
  have hmax : 0 < trialParameterMax (1 / h) := by unfold trialParameterMax; positivity
  have hupper := (scaledA_tendsto_zero h K hh).eventually (eventually_lt_nhds hmax)
  filter_upwards [hupper] with N hN
  intro k hk
  refine ⟨div_nonneg hk.1 (by positivity), ?_⟩
  exact (div_le_div_of_nonneg_right hk.2 (by positivity)).trans hN.le

end
end CriticalExtrapolation.Paper
