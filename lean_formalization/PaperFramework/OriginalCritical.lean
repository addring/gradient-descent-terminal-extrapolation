import PaperFramework.OriginalObjective
import PaperFramework.OriginalQuadratic

/-!
The Luner--Grimmer pointwise equality-set definition. This is separate from
`criticalCoefficient`, which is the initial-interval endpoint.
Audit OriginalAudit.lean for the complete axiom dependencies of this extension.
-/

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

def originalValiditySet (N : ℕ) (h L D : ℝ) : Set ℝ :=
  {c | 1 ≤ c ∧ worstGradient N h c L D = L * D / S N h c}

noncomputable def originalCriticalCoefficient (N : ℕ) (h L D : ℝ) : ℝ :=
  sSup (originalValiditySet N h L D)

/-- All coefficients on the right, with a single eventual bound in N. -/
theorem original_eventual_upper_failure_fixed_step (h L D ε : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 0 < L) (hD : 0 < D) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c ≥ scaledC N h (1 + ε),
      L * D / S N h c < worstGradient N h c L D := by
  have hnegative := original_eventual_negative_trial h ε hh hh1 hε
  have htail := original_quadratic_tail_failure h L D hh hh1 hL hD
  have hlarge : ∀ᶠ N : ℕ in atTop, 4 * (1 / h) ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hnegative, htail, hlarge, eventually_gt_atTop 1] with N hneg hquad hsize hN
  intro c hc
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hc1 : 1 ≤ c := (scaledC_ge_one N h (1 + ε) hh (by linarith)).trans hc
  have hp : Parameters N h c := ⟨by omega, hh, hh1, hc1⟩
  let a : ℝ := (N : ℝ) * (c - 1)
  have ha : scaledA N h (1 + ε) ≤ a := by
    rw [← scaledA_identity N h (1 + ε) hN hh]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hc 1) hn.le
  have hceq : 1 + a / (N : ℝ) = c := by
    dsimp [a]
    field_simp [hn.ne']
    <;> ring
  by_cases hbounded : a ≤ 2 * (1 / h)
  · have hQ := hneg a ⟨ha, hbounded⟩
    rw [hceq] at hQ
    exact negative_direction_failure N h c L D hp hL hD
      (trialDirection N a (1 / h)) (original_trial_strict_feasibility N h c hp hsize) hQ
  · have hfail := hquad a (le_of_not_ge hbounded)
    rwa [hceq] at hfail

theorem original_critical_sandwich (h L D ε : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 0 < L) (hD : 0 < D)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ N : ℕ in atTop,
      scaledC N h (1 - ε) ≤ originalCriticalCoefficient N h L D ∧
      originalCriticalCoefficient N h L D ≤ scaledC N h (1 + ε) := by
  have hlower := eventual_lower_interval_fixed_step h L D ε hh hh1 hL hD hε hε1
  have hupper := original_eventual_upper_failure_fixed_step h L D ε hh hh1 hL hD hε
  filter_upwards [hlower, hupper] with N hlo hhi
  have hcm : 1 ≤ scaledC N h (1 - ε) := scaledC_ge_one N h (1 - ε) hh (by linarith)
  have hmem : scaledC N h (1 - ε) ∈ originalValiditySet N h L D :=
    ⟨hcm, hlo _ ⟨hcm, le_rfl⟩⟩
  have hbound : ∀ c ∈ originalValiditySet N h L D, c ≤ scaledC N h (1 + ε) := by
    intro c hc
    by_contra h
    exact (ne_of_gt (hhi c (le_of_lt (lt_of_not_ge h)))) hc.2
  have hbdd : BddAbove (originalValiditySet N h L D) := ⟨scaledC N h (1 + ε), hbound⟩
  exact ⟨le_csSup hbdd hmem, csSup_le ⟨_, hmem⟩ (fun c hc => hbound c hc)⟩

/-- Sharp critical scale using exactly the original pointwise definition. -/
theorem original_sharp_critical_scale (L D h : ℝ)
    (hL : 0 < L) (hD : 0 < D) (hh : 0 < h) (hh1 : h ≤ 1) :
    Tendsto (fun N : ℕ => h * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) *
      (originalCriticalCoefficient N h L D - 1)) atTop (𝓝 1) := by
  apply scaled_limit_of_interval_sandwich h hh (fun N => originalCriticalCoefficient N h L D)
  intro ε hε
  exact original_critical_sandwich h L D ε hh hh1 hL hD hε.1 hε.2

/-- The claimed positive inverse-linear lower scale in Conjecture 5.1 fails. -/
theorem original_critical_increment_small (L D h : ℝ)
    (hL : 0 < L) (hD : 0 < D) (hh : 0 < h) (hh1 : h ≤ 1) :
    Tendsto (fun N : ℕ => (N : ℝ) * (originalCriticalCoefficient N h L D - 1))
      atTop (𝓝 0) := by
  have hmain := original_sharp_critical_scale L D h hL hD hh hh1
  have hinv : Tendsto (fun N : ℕ => 1 / (h * Real.sqrt (Real.log (N : ℝ))))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (sqrt_log_nat_tendsto_atTop.const_mul_atTop hh)
  have hlim := hmain.mul hinv
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt (Real.log (N : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.mpr (Real.log_pos hNr)).ne'
  field_simp [hh.ne', hs]
  <;> ring

theorem original_no_positive_inverse_linear_lower_bound (L D h κ : ℝ)
    (hL : 0 < L) (hD : 0 < D) (hh : 0 < h) (hh1 : h ≤ 1) (hκ : 0 < κ) :
    ¬ (∀ᶠ N : ℕ in atTop, κ ≤ (N : ℝ) * (originalCriticalCoefficient N h L D - 1)) := by
  intro hbound
  have hsmall := (original_critical_increment_small L D h hL hD hh hh1).eventually
    (gt_mem_nhds hκ)
  obtain ⟨N, hN⟩ := (hbound.and hsmall).exists
  exact (not_lt_of_ge hN.1) hN.2

/-- Already h=L=D=1 contradicts the positive lower half of Conjecture 5.1. -/
theorem original_conjecture_5_1_false :
    ¬ ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ N : ℕ in atTop,
      κ / (N : ℝ) ≤ originalCriticalCoefficient N 1 1 1 - 1 := by
  rintro ⟨κ, hκ, hbound⟩
  apply original_no_positive_inverse_linear_lower_bound 1 1 1 κ
    zero_lt_one zero_lt_one zero_lt_one le_rfl hκ
  filter_upwards [hbound, eventually_gt_atTop 0] with N hb hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hm := (div_le_iff₀ hn).mp hb
  nlinarith

end
end CriticalExtrapolation.Paper
