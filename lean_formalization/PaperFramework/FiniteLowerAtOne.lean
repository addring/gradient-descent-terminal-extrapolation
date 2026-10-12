import PaperFramework.ReferenceRatio
import PaperFramework.ScaledParameters
import PaperFramework.EnergyLowerBound

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

theorem scaledA_unit_log_square (N : ℕ) (k : ℝ) (hN : 1 < N) :
    Real.log (N : ℝ) * (scaledA N 1 k) ^ 2 = k ^ 2 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hL := Real.log_pos hNr
  unfold scaledA
  simp only [one_mul]
  calc
    _ = (Real.log (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) ^ 2) * k ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt hL.le, div_self (ne_of_gt hL), one_mul]

/-- The strict finite lower bound is positive over the whole initial interval at h=1. -/
theorem eventual_finite_lower_bound_at_one (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ N in atTop, ∀ c ∈ Set.Icc (1 : ℝ) (scaledC N 1 (1 - ε)),
      0 < finiteLowerBound N 1 c := by
  let K : ℝ := 1 - ε
  let δ : ℝ := 1 - K ^ 2
  have hK : 0 < K := by dsimp [K]; linarith
  have hδ : 0 < δ := by dsimp [δ, K]; nlinarith
  have hratio : ∀ᶠ N : ℕ in atTop,
      1 - δ / 4 < Real.log (N : ℝ) / referenceReciprocalSum N :=
    log_div_referenceReciprocalSum_tendsto.eventually (Ioi_mem_nhds (by linarith))
  have herror : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) / (N : ℝ) < δ / 16 :=
    log_div_nat_tendsto_zero.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [hratio, herror, eventual_scaled_parameter_range 1 K zero_lt_one,
    eventually_gt_atTop 1] with N hR hE hrange hN
  intro c hc
  obtain ⟨_, k, hk, heq⟩ := scaled_interval_coordinates N 1 K hN zero_lt_one le_rfl c hc
  rw [← heq]
  let a : ℝ := scaledA N 1 k
  have ha : 0 ≤ a := (hrange k hk).1
  have ha1 : a ≤ 1 := (hrange k hk).2.trans (by norm_num [trialParameterMax])
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by linarith
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  have hsquare := scaledA_unit_log_square N k hN
  change Real.log (N : ℝ) * a ^ 2 = k ^ 2 at hsquare
  have hsq : k ^ 2 ≤ K ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk.2) (add_nonneg hK.le hk.1)]
  have hlead : 4 * Real.log (N : ℝ) / (N : ℝ) <
      Real.log (N : ℝ) / referenceReciprocalSum N - k ^ 2 := by
    dsimp [δ] at hR hE
    have hδ' : 0 < 1 - K ^ 2 := hδ
    rw [mul_div_assoc]
    nlinarith only [hR, hE, hsq, hδ']
  have hid : Real.log (N : ℝ) * (1 / referenceReciprocalSum N - a ^ 2 - 4 / (N : ℝ)) =
      Real.log (N : ℝ) / referenceReciprocalSum N - k ^ 2 - 4 * Real.log (N : ℝ) / (N : ℝ) := by
    linear_combination -hsquare
  have hnum : 4 / (N : ℝ) < 1 / referenceReciprocalSum N - a ^ 2 := by
    have hproduct : 0 < Real.log (N : ℝ) * (1 / referenceReciprocalSum N - a ^ 2 - 4 / (N : ℝ)) := by
      rw [hid]
      linarith
    have := (mul_pos_iff_of_pos_left hL).mp hproduct
    linarith
  have hden : 0 < (a + 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hcoef : a * (a + 1) ^ 2 ≤ 4 := by
    have hsqA : (a + 1) ^ 2 ≤ 4 := by nlinarith [mul_nonneg ha (sub_nonneg.mpr ha1)]
    have hm := mul_le_mul_of_nonneg_left hsqA ha
    nlinarith
  have hterm : a / (N : ℝ) * (a + 1) ^ 2 ≤ 4 / (N : ℝ) := by
    simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hcoef hNpos.le
  simp only [finiteLowerBound, one_div_one, one_pow]
  change 0 < (1 / referenceReciprocalSum N - ((N : ℝ) * (scaledC N 1 k - 1)) ^ 2) /
      ((N : ℝ) * (scaledC N 1 k - 1) + 1) ^ 2 - (N : ℝ) * (scaledC N 1 k - 1) / (N : ℝ)
  rw [scaledA_identity N 1 k hN zero_lt_one]
  change 0 < (1 / referenceReciprocalSum N - a ^ 2) / (a + 1) ^ 2 - a / (N : ℝ)
  exact sub_pos.mpr ((lt_div_iff₀ hden).mpr (lt_of_le_of_lt hterm hnum))

end
end CriticalExtrapolation.Paper
