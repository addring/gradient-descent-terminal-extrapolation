import PaperFramework.SmoothnessNormalization
import PaperFramework.InstanceDilation
import PaperFramework.InstanceBounds

namespace CriticalExtrapolation.Paper
noncomputable section

theorem actual_value_normalization {d : ℕ} {L D : ℝ} (I : Instance d L D)
    (hL : 0 < L) (hD : 0 < D) (N : ℕ) (h c : ℝ) :
    ∃ J : Instance d 1 1, ‖gradient I.f (output I N h c)‖ =
      L * D * ‖gradient J.f (output J N h c)‖ := by
  let U := unitSmoothInstance I hL
  have hrad : D⁻¹ * D ≤ 1 := by rw [inv_mul_cancel₀ hD.ne']
  let J := dilatedInstance U 1 1 D⁻¹ zero_lt_one (inv_pos.mpr hD) hrad
  have hnorm : ‖gradient J.f (output J N h c)‖ =
      D⁻¹ * (L⁻¹ * ‖gradient I.f (output I N h c)‖) := by
    change ‖gradient (dilatedInstance U 1 1 D⁻¹ zero_lt_one (inv_pos.mpr hD) hrad).f
      (output (dilatedInstance U 1 1 D⁻¹ zero_lt_one (inv_pos.mpr hD) hrad) N h c)‖ = _
    rw [dilatedInstance_output, dilatedInstance_gradient, unitSmoothInstance_output,
      unitSmoothInstance_gradient]
    simp only [one_mul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hD), abs_of_pos (inv_pos.mpr hL)]
  refine ⟨J, ?_⟩
  rw [hnorm]
  field_simp [hL.ne', hD.ne']

theorem actual_value_scaling {d : ℕ} (J : Instance d 1 1) (L D : ℝ)
    (hL : 0 < L) (hD : 0 < D) (N : ℕ) (h c : ℝ) :
    ∃ I : Instance d L D, ‖gradient I.f (output I N h c)‖ =
      L * D * ‖gradient J.f (output J N h c)‖ := by
  have hrad : D * 1 ≤ D := by simp
  refine ⟨dilatedInstance J L D D hL hD hrad, ?_⟩
  rw [dilatedInstance_output, dilatedInstance_gradient, norm_smul,
    Real.norm_eq_abs, abs_of_pos (mul_pos hL hD)]

theorem worstGradient_scaling_proved (N : ℕ) (h c L D : ℝ)
    (hL : 0 < L) (hD : 0 < D) :
    worstGradient N h c L D = L * D * worstGradient N h c 1 1 := by
  obtain ⟨hnonempty, hbdd⟩ := actual_instance_values_nonempty_bounded N h c L D hL hD
  obtain ⟨hnonempty1, hbdd1⟩ := actual_instance_values_nonempty_bounded N h c 1 1
    zero_lt_one zero_lt_one
  have hLD := mul_pos hL hD
  apply le_antisymm
  · apply csSup_le hnonempty
    rintro r ⟨d, I, rfl⟩
    obtain ⟨J, hJ⟩ := actual_value_normalization I hL hD N h c
    rw [hJ]
    exact mul_le_mul_of_nonneg_left (le_csSup hbdd1 ⟨d, J, rfl⟩) hLD.le
  · have hunit : worstGradient N h c 1 1 ≤ worstGradient N h c L D / (L * D) := by
      apply csSup_le hnonempty1
      rintro r ⟨d, J, rfl⟩
      obtain ⟨I, hI⟩ := actual_value_scaling J L D hL hD N h c
      have hbound : ‖gradient I.f (output I N h c)‖ ≤ worstGradient N h c L D :=
        le_csSup hbdd ⟨d, I, rfl⟩
      rw [hI] at hbound
      apply (le_div_iff₀ hLD).mpr
      simpa only [mul_comm] using hbound
    calc
      L * D * worstGradient N h c 1 1 ≤
          L * D * (worstGradient N h c L D / (L * D)) :=
        mul_le_mul_of_nonneg_left hunit hLD.le
      _ = worstGradient N h c L D := by field_simp [hLD.ne']

end
end CriticalExtrapolation.Paper
