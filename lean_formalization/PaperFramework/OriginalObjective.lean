import PaperFramework.OriginalEnergy
import PaperFramework.OriginalFeasibility
import PaperFramework.CriticalInterval

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

def originalTerminal {N : ℕ} (a t : ℝ) (p : Vec N) (i : Fin N) : ℝ :=
  2 * energyF N a t * t * a * (t - 1) / (a + 1) * p i

theorem original_trial_identity (N : ℕ) (h c : ℝ) (hp : Parameters N h c) :
    let a := (N : ℝ) * (c - 1)
    let t := 1 / h
    (a + t) ^ 2 / (h ^ 2 * c) * chainObjective h c (trialDirection N a t) =
      t ^ 2 * homogeneousEnergy a t (normalizedTrial N t) - a ^ 2 -
        a * (a + t) ^ 2 / (N : ℝ) +
        originalTerminal a t (normalizedTrial N t) ⟨N - 1, by have := hp.n_pos; omega⟩ := by
  let a : ℝ := (N : ℝ) * (c - 1)
  let t : ℝ := 1 / h
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hp.c_ge_one)
  have ht : 0 < t := one_div_pos.mpr hp.h_pos
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp.n_pos
  have hat : a + t ≠ 0 := ne_of_gt (by linarith : 0 < a + t)
  have ha1 : a + 1 ≠ 0 := ne_of_gt (by linarith : 0 < a + 1)
  have he := affine_shift_energy_identity N h c hp (normalizedTrial N t)
    (normalizedTrial_normalized N t hp.n_pos (by
      dsimp [t]; exact (le_div_iff₀ hp.h_pos).mpr (by simpa using hp.h_le_one)))
  change chainObjective h c (trialDirection N a t) / (h ^ 2 * c) =
    (shiftMass a t) ^ 2 * homogeneousEnergy a t (normalizedTrial N t) -
      a ^ 2 / (a + t) ^ 2 - a / (N : ℝ) +
      2 * energyF N a t * shiftMass a t * shiftB N a t * (N : ℝ) * (t - 1) /
        (a + 1) * normalizedTrial N t ⟨N - 1, by have := hp.n_pos; omega⟩ at he
  change (a + t) ^ 2 / (h ^ 2 * c) * chainObjective h c (trialDirection N a t) =
    t ^ 2 * homogeneousEnergy a t (normalizedTrial N t) - a ^ 2 -
      a * (a + t) ^ 2 / (N : ℝ) +
      originalTerminal a t (normalizedTrial N t) ⟨N - 1, by have := hp.n_pos; omega⟩
  calc
    _ = (a + t) ^ 2 * (chainObjective h c (trialDirection N a t) / (h ^ 2 * c)) := by ring
    _ = _ := by
      rw [he]
      dsimp only [shiftMass, shiftB, originalTerminal]
      field_simp [hat, hn, ha1]
      <;> ring

theorem original_terminal_log_upper (N : ℕ) (a t : ℝ)
    (hN : 1 < N) (ht : 1 ≤ t) (hsize : 4 * t ≤ (N : ℝ))
    (ha : a ∈ Set.Icc (0 : ℝ) (2 * t)) (i : Fin N) (hi : i.val + 1 = N)
    (hV : Real.log (N : ℝ) ≤ trialNormalization N t) :
    Real.log (N : ℝ) * originalTerminal a t (normalizedTrial N t) i ≤
      8 * t * (t - 1) * a := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hF0 : 0 ≤ energyF N a t := by unfold energyF; linarith [ha.1]
  have hF : energyF N a t ≤ 2 * (N : ℝ) := by unfold energyF; linarith [ha.2]
  have hlast := normalizedTrial_terminal_log_upper N t hN ht i hi hV
  have ha0 : 0 ≤ a := ha.1
  have ht1 : 0 ≤ t - 1 := sub_nonneg.mpr ht
  have htr0 : 0 ≤ (t - 1) / (a + 1) := by positivity
  have htr : (t - 1) / (a + 1) ≤ t - 1 := by
    apply (div_le_iff₀ (by linarith [ha.1] : 0 < a + 1)).mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ t - 1) ha.1]
  have hid : Real.log (N : ℝ) * originalTerminal a t (normalizedTrial N t) i =
      (2 * energyF N a t) * (t * a) * ((t - 1) / (a + 1)) *
        (Real.log (N : ℝ) * normalizedTrial N t i) := by unfold originalTerminal; ring
  rw [hid]
  calc
    _ ≤ (2 * (2 * (N : ℝ))) * (t * a) * (t - 1) * (2 / (N : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hF (by norm_num : (0 : ℝ) ≤ 2))
        (mul_nonneg (by linarith : 0 ≤ t) ha.1)
      have h2 := mul_le_mul h1 htr htr0 (by positivity)
      exact mul_le_mul h2 hlast.2 hlast.1 (by positivity)
    _ = _ := by
      field_simp [hn.ne']
      <;> ring

/-- Elementary strict margin after setting x = sqrt(log N) * a. -/
theorem original_negative_scalar (t ε x : ℝ) (ht : 0 < t) (hε : 0 < ε)
    (hx : (1 + ε) * t ≤ x) :
    t ^ 2 * (1 + ε) - x ^ 2 + (ε * t / 2) * x < 0 := by
  have hx0 : 0 < x := by nlinarith
  have hcoef : 0 < (1 + ε / 2) * t := by positivity
  have h1 : (1 + ε) * t * x ≤ x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) hx0.le]
  have h2 := mul_le_mul_of_nonneg_left hx hcoef.le
  have hstrict : 0 < ε / 2 * (1 + ε) * t ^ 2 := by positivity
  calc
    _ ≤ t ^ 2 * (1 + ε) - ((1 + ε / 2) * t) * x := by nlinarith only [h1]
    _ ≤ t ^ 2 * (1 + ε) - ((1 + ε / 2) * t) * ((1 + ε) * t) :=
      sub_le_sub_left h2 _
    _ = -(ε / 2 * (1 + ε) * t ^ 2) := by ring
    _ < 0 := neg_neg_of_pos hstrict

/-- The entire bounded interval above the critical scale has negative trial objective. -/
theorem original_eventual_negative_trial (h ε : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ a ∈ Set.Icc (scaledA N h (1 + ε)) (2 * (1 / h)),
        chainObjective h (1 + a / (N : ℝ)) (trialDirection N a (1 / h)) < 0 := by
  let t : ℝ := 1 / h
  have ht : 1 ≤ t := (le_div_iff₀ hh).mpr (by simpa using hh1)
  have ht0 : 0 < t := by linarith
  have henergy := original_energy_eventual_upper t (2 * t) ε ht (by positivity) hε
  have hlarge : ∀ᶠ N : ℕ in atTop, 4 * t ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (4 * t))
  have hcorr : ∀ᶠ N : ℕ in atTop,
      8 * t * (t - 1) ≤ (ε * t / 2) * Real.sqrt (Real.log (N : ℝ)) :=
    (sqrt_log_nat_tendsto_atTop.const_mul_atTop (by positivity : 0 < ε * t / 2)).eventually
      (eventually_ge_atTop _)
  filter_upwards [henergy, hlarge, hcorr, trialNormalization_eventually_ge_log t ht,
    eventually_gt_atTop 1] with N hE hsize hK hV hN
  intro a ha
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  let l : ℝ := Real.log (N : ℝ)
  let s : ℝ := Real.sqrt l
  have hl : 0 < l := Real.log_pos hNr
  have hs : 0 < s := Real.sqrt_pos.mpr hl
  have hs2 : s ^ 2 = l := Real.sq_sqrt hl.le
  have hscaled : 0 ≤ scaledA N h (1 + ε) := by unfold scaledA; positivity
  have ha0 : 0 ≤ a := hscaled.trans ha.1
  have haA : a ∈ Set.Icc (0 : ℝ) (2 * t) := ⟨ha0, ha.2⟩
  have hax : (1 + ε) * t ≤ s * a := by
    have hb := (div_le_iff₀ (mul_pos hh hs)).mp ha.1
    change 1 + ε ≤ a * (h * s) at hb
    have hm := mul_le_mul_of_nonneg_left hb ht0.le
    have hth : t * h = 1 := by dsimp [t]; field_simp [hh.ne']
    calc
      (1 + ε) * t = t * (1 + ε) := by ring
      _ ≤ t * (a * (h * s)) := hm
      _ = (t * h) * (s * a) := by ring
      _ = s * a := by rw [hth, one_mul]
  have hneg := original_negative_scalar t ε (s * a) ht0 hε hax
  have hc : 1 ≤ 1 + a / (N : ℝ) :=
    le_add_of_nonneg_right (div_nonneg ha0 hn.le)
  have hp : Parameters N h (1 + a / (N : ℝ)) := ⟨by omega, hh, hh1, hc⟩
  have haeq : (N : ℝ) * ((1 + a / (N : ℝ)) - 1) = a := by
    field_simp [hn.ne']
    <;> ring
  have he := original_trial_identity N h (1 + a / (N : ℝ)) hp
  dsimp only at he
  rw [haeq] at he
  let i : Fin N := ⟨N - 1, by omega⟩
  have hterm := original_terminal_log_upper N a t hN ht hsize haA i
    (by dsimp [i]; omega) hV
  have hener := mul_lt_mul_of_pos_left (hE a haA) (sq_pos_of_pos ht0)
  have hka := mul_le_mul_of_nonneg_right hK ha0
  have hdrop : 0 ≤ l * (a * (a + t) ^ 2 / (N : ℝ)) := by positivity
  have hmul := congrArg (fun z : ℝ => l * z) he
  change l * ((a + t) ^ 2 / (h ^ 2 * (1 + a / (N : ℝ))) *
      chainObjective h (1 + a / (N : ℝ)) (trialDirection N a t)) =
    l * (t ^ 2 * homogeneousEnergy a t (normalizedTrial N t) - a ^ 2 -
      a * (a + t) ^ 2 / (N : ℝ) + originalTerminal a t (normalizedTrial N t) i) at hmul
  have hnegative : l * ((a + t) ^ 2 / (h ^ 2 * (1 + a / (N : ℝ))) *
      chainObjective h (1 + a / (N : ℝ)) (trialDirection N a t)) < 0 := by
    rw [hmul]
    change l * (t ^ 2 * homogeneousEnergy a t (normalizedTrial N t) - a ^ 2 -
      a * (a + t) ^ 2 / (N : ℝ) + originalTerminal a t (normalizedTrial N t) i) < 0
    have hsqa : (s * a) ^ 2 = l * a ^ 2 := by rw [mul_pow, hs2]
    rw [hsqa] at hneg
    dsimp [l, s] at hka hterm hener hneg hdrop ⊢
    nlinarith only [hka, hterm, hener, hneg, hdrop]
  have hfactor : 0 < (a + t) ^ 2 / (h ^ 2 * (1 + a / (N : ℝ))) := by positivity
  have hq := neg_of_mul_neg_right hnegative hl.le
  exact neg_of_mul_neg_right hq hfactor.le

end
end CriticalExtrapolation.Paper
