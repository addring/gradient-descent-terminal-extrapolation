import PaperFramework.QuadraticProgramKKT
import PaperFramework.FeasibleFloor
import PaperFramework.NormalizedEnergyBound
import PaperFramework.ShiftedEnergy

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def finiteLowerBound (N : ℕ) (h c : ℝ) : ℝ :=
  let a := (N : ℝ) * (c - 1)
  let t := 1 / h
  (t ^ 2 / referenceReciprocalSum N - a ^ 2) / (a + t) ^ 2 - a / (N : ℝ)

/-- (7.5), independent of the sufficiency/certificate branch. -/
theorem qp_energy_lower_bound (N : ℕ) (h c : ℝ) (hp : Parameters N h c) :
    finiteLowerBound N h c ≤ auxiliaryValue N h c / (h ^ 2 * c) := by
  obtain ⟨β, hβ, _⟩ := optimizer_exists_unique N h c hp
  obtain ⟨p, hpos, hsum, hshift⟩ := feasible_shift_representation N h c hp β hβ.1
  have hid := affine_shift_energy_identity N h c hp p hsum
  have hvalue := auxiliaryValue_attained N h c hp β hβ
  let a : ℝ := (N : ℝ) * (c - 1)
  let t : ℝ := 1 / h
  have hN : (0 : ℝ) < N := by exact_mod_cast hp.n_pos
  have ha : 0 ≤ a := mul_nonneg hN.le (sub_nonneg.mpr hp.c_ge_one)
  have ht : 1 ≤ t := (le_div_iff₀ hp.h_pos).mpr (by simpa using hp.h_le_one)
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hat : 0 < a + t := add_pos_of_nonneg_of_pos ha htpos
  have hm : 0 ≤ shiftMass a t := (div_pos htpos hat).le
  have hB : 0 ≤ shiftB N a t := div_nonneg ha (mul_nonneg hN.le hat.le)
  have henergy := full_space_energy_lower_bound N a t hp.n_pos ha ht p hsum
  have hscaled := mul_le_mul_of_nonneg_left henergy (sq_nonneg (shiftMass a t))
  have hcorrection : 0 ≤ 2 * energyF N a t * shiftMass a t * shiftB N a t * (N : ℝ) * (t - 1) /
      (a + 1) * p ⟨N - 1, by have := hp.n_pos; omega⟩ := by
    have hF := energyF_pos N a t ha ht
    exact mul_nonneg (div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hm) hB) hN.le)
        (sub_nonneg.mpr ht)) (by linarith)) (hpos _)
  have hbaseline : finiteLowerBound N h c = (shiftMass a t) ^ 2 * (1 / referenceReciprocalSum N) -
      a ^ 2 / (a + t) ^ 2 - a / (N : ℝ) := by
    change (t ^ 2 / referenceReciprocalSum N - a ^ 2) / (a + t) ^ 2 - a / (N : ℝ) = _
    rw [show (shiftMass a t) ^ 2 = t ^ 2 / (a + t) ^ 2 by exact div_pow t (a + t) 2]
    ring
  rw [hvalue, hshift, hid, hbaseline]
  change (shiftMass a t) ^ 2 * (1 / referenceReciprocalSum N) - a ^ 2 / (a + t) ^ 2 - a / (N : ℝ) ≤
    (shiftMass a t) ^ 2 * homogeneousEnergy a t p - a ^ 2 / (a + t) ^ 2 - a / (N : ℝ) + _
  linarith only [hscaled, hcorrection]

theorem finite_lower_bound_continuous_at_one (N : ℕ) (c : ℝ) (hN : 0 < N) (hc : 1 ≤ c) :
    ContinuousAt (fun h : ℝ => finiteLowerBound N h c) 1 := by
  have ha : 0 ≤ (N : ℝ) * (c - 1) := mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hc)
  have hden : (N : ℝ) * (c - 1) + 1 ≠ 0 := by linarith
  have ht : ContinuousAt (fun h : ℝ => 1 / h) 1 :=
    continuousAt_const.div continuousAt_id (by norm_num)
  change ContinuousAt (fun h : ℝ =>
    ((1 / h) ^ 2 / referenceReciprocalSum N - ((N : ℝ) * (c - 1)) ^ 2) /
      ((N : ℝ) * (c - 1) + 1 / h) ^ 2 - (N : ℝ) * (c - 1) / (N : ℝ)) 1
  apply ContinuousAt.sub _ continuousAt_const
  apply ContinuousAt.div
  · exact ((ht.pow 2).div_const _).sub continuousAt_const
  · exact (continuousAt_const.add ht).pow 2
  · simpa using pow_ne_zero 2 hden

end
end CriticalExtrapolation.Paper
