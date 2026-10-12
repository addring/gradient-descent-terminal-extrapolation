import PaperFramework.QuadraticActual
import PaperFramework.InstanceBounds

namespace CriticalExtrapolation.Paper
noncomputable section

theorem large_coefficient_failure_proved (N : ℕ) (h L D : ℝ) (hN : 0 < N)
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 0 < L) (hD : 0 < D) :
    ∃ C ≥ 1, L * D / S N h C < worstGradient N h C L D := by
  let δ : ℝ := 1 - (1 - h) ^ N
  have hpowlt : (1 - h) ^ N < 1 :=
    pow_lt_one₀ (sub_nonneg.mpr hh1) (by linarith) (Nat.ne_of_gt hN)
  have hδ : 0 < δ := sub_pos.mpr hpowlt
  have hδle : δ ≤ 1 := by
    have hp : 0 ≤ (1 - h) ^ N := pow_nonneg (sub_nonneg.mpr hh1) N
    dsimp [δ]
    linarith
  let C : ℝ := 2 / δ
  have hC : 1 ≤ C := by
    apply (le_div_iff₀ hδ).mpr
    linarith
  let I₀ := quadraticUnitInstance 1 unitOne
  have hrad : D * ‖unitOne‖ ≤ D := by rw [unitOne_norm, mul_one]
  let I := dilatedInstance I₀ L D D hL hD hrad
  have hcoeff : 1 - C * (1 - (1 - h) ^ N) = -1 := by
    change 1 - (2 / δ) * δ = -1
    rw [div_mul_cancel₀ _ hδ.ne']
    norm_num
  have hbasegrad : gradient I₀.f (output I₀ N h C) = -unitOne := by
    change gradient halfSquaredNorm (output (quadraticUnitInstance 1 unitOne) N h C) = _
    rw [quadraticUnitInstance_output, hcoeff, halfSquaredNorm_gradient, neg_one_smul]
  have hgrad : ‖gradient I.f (output I N h C)‖ = L * D := by
    change ‖gradient (dilatedInstance I₀ L D D hL hD hrad).f
      (output (dilatedInstance I₀ L D D hL hD hrad) N h C)‖ = _
    rw [dilatedInstance_output, dilatedInstance_gradient, hbasegrad, norm_smul,
      Real.norm_eq_abs, abs_of_pos (mul_pos hL hD), norm_neg, unitOne_norm, mul_one]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hS : 1 < S N h C := by
    exact lt_add_of_pos_right 1 (mul_pos (mul_pos hNr hh) hCpos)
  have hstrict : L * D / S N h C < L * D := by
    apply (div_lt_iff₀ (lt_trans zero_lt_one hS)).mpr
    simpa only [mul_one] using mul_lt_mul_of_pos_left hS (mul_pos hL hD)
  refine ⟨C, hC, ?_⟩
  obtain ⟨_, hbdd⟩ := actual_instance_values_nonempty_bounded N h C L D hL hD
  have hsup : ‖gradient I.f (output I N h C)‖ ≤ worstGradient N h C L D :=
    le_csSup hbdd ⟨1, I, rfl⟩
  rw [hgrad] at hsup
  exact hstrict.trans_le hsup

end
end CriticalExtrapolation.Paper
