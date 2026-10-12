import PaperFramework.NormalizedEnergyBound

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

theorem referenceReciprocalSum_div_log_tendsto :
    Tendsto (fun N : ℕ => referenceReciprocalSum N / Real.log (N : ℝ)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun N : ℕ => |(referenceReciprocalSum N - Real.log (N : ℝ)) /
      Real.log (N : ℝ)|) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) _
      (tendsto_const_nhds.div_atTop hlog : Tendsto (fun N : ℕ => (9 : ℝ) / Real.log (N : ℝ)) atTop (𝓝 0))
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hL := Real.log_pos hNr
    rw [abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right (referenceReciprocalSum_log_error N hN).le hL.le
  have he : Tendsto (fun N : ℕ => (referenceReciprocalSum N - Real.log (N : ℝ)) /
      Real.log (N : ℝ)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hz)
  have hr : Tendsto (fun N : ℕ => (referenceReciprocalSum N - Real.log (N : ℝ)) /
      Real.log (N : ℝ) + 1) atTop (𝓝 1) := by
    simpa using he.add (tendsto_const_nhds (x := (1 : ℝ)))
  apply hr.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  field_simp [ne_of_gt (Real.log_pos hNr)]
  <;> ring

theorem log_div_referenceReciprocalSum_tendsto :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) / referenceReciprocalSum N) atTop (𝓝 1) := by
  simpa only [inv_div, inv_one] using referenceReciprocalSum_div_log_tendsto.inv₀ (by norm_num)

theorem log_div_nat_tendsto_zero :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

end
end CriticalExtrapolation.Paper
