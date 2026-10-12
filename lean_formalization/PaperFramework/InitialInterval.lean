import PaperFramework.Definitions

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

theorem initial_endpoints_of_interval_and_failure (N : ℕ) (h L D C : ℝ)
    (hC : 1 ≤ C)
    (hvalid : ∀ c ∈ Set.Icc (1 : ℝ) C, worstGradient N h c L D = L * D / S N h c)
    (B : ℝ) (hB : 1 ≤ B) (hfailure : L * D / S N h B < worstGradient N h B L D) :
    (initialValidityEndpoints N h L D).Nonempty ∧ BddAbove (initialValidityEndpoints N h L D) := by
  refine ⟨⟨C, hC, hvalid⟩, ⟨B, ?_⟩⟩
  intro b hb
  by_contra h
  have hBb : B ≤ b := (lt_of_not_ge h).le
  have heq := hb.2 B ⟨hB, hBb⟩
  exact (ne_of_gt hfailure) heq

theorem critical_lower_of_interval (N : ℕ) (h L D C : ℝ) (hC : 1 ≤ C)
    (hvalid : ∀ c ∈ Set.Icc (1 : ℝ) C, worstGradient N h c L D = L * D / S N h c)
    (hbdd : BddAbove (initialValidityEndpoints N h L D)) :
    C ≤ criticalCoefficient N h L D := by
  exact le_csSup hbdd ⟨hC, hvalid⟩

/-- A single failure bounds the entire initial interval, without monotonicity. -/
theorem critical_upper_of_failure (N : ℕ) (h L D C : ℝ) (hC : 1 ≤ C)
    (hfailure : L * D / S N h C < worstGradient N h C L D)
    (hne : (initialValidityEndpoints N h L D).Nonempty) :
    criticalCoefficient N h L D ≤ C := by
  apply csSup_le hne
  intro b hb
  by_contra h
  have hcb : C ≤ b := le_of_lt (lt_of_not_ge h)
  have heq := hb.2 C ⟨hC, hcb⟩
  exact (ne_of_gt hfailure) heq

theorem scaledC_rescale (N : ℕ) (h k : ℝ)
    (hs : h * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≠ 0) :
    h * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) * (scaledC N h k - 1) = k := by
  simpa only [scaledC, add_sub_cancel_left, mul_comm] using div_mul_cancel₀ k hs

/-- The final limit needs only the two-sided interval sandwich. -/
theorem scaled_limit_of_interval_sandwich (h : ℝ) (hh : 0 < h) (b : ℕ → ℝ)
    (hb : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ᶠ N in atTop,
      scaledC N h (1 - ε) ≤ b N ∧ b N ≤ scaledC N h (1 + ε)) :
    Tendsto (fun N : ℕ => h * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) * (b N - 1))
      atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  filter_upwards [hb δ ⟨hδ, hδ1⟩, eventually_ge_atTop 2] with N hbounds hN
  let s : ℝ := h * (N : ℝ) * Real.sqrt (Real.log (N : ℝ))
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hs : 0 < s := mul_pos (mul_pos hh (lt_trans zero_lt_one hNr))
    (Real.sqrt_pos.mpr (Real.log_pos hNr))
  have hminus := scaledC_rescale N h (1 - δ) (ne_of_gt hs)
  have hplus := scaledC_rescale N h (1 + δ) (ne_of_gt hs)
  change s * (scaledC N h (1 - δ) - 1) = 1 - δ at hminus
  change s * (scaledC N h (1 + δ) - 1) = 1 + δ at hplus
  have hlo := mul_le_mul_of_nonneg_left hbounds.1 hs.le
  have hhi := mul_le_mul_of_nonneg_left hbounds.2 hs.le
  change |s * (b N - 1) - 1| < ε
  apply abs_lt.mpr
  constructor <;> nlinarith only [hlo, hhi, hminus, hplus, hδε]

end
end CriticalExtrapolation.Paper
