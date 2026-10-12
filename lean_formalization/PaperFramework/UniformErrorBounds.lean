import PaperFramework.TrialUniformAlgebra
import PaperFramework.ScaledParameters

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

theorem uniformOn_of_uniform_error_bound (lo hi : ℝ) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (b : ℕ → ℝ) (hb : Tendsto b atTop (𝓝 0))
    (hbound : ∀ᶠ N in atTop, ∀ k ∈ Set.Icc lo hi, |f N k - g k| ≤ b N) :
    UniformOn lo hi f g := by
  intro ε hε
  have hsmall := hb.eventually (gt_mem_nhds hε)
  filter_upwards [hbound, hsmall] with N hN hs
  intro k hk
  exact lt_of_le_of_lt (hN k hk) hs

theorem uniformOn_of_error_plus_uniform (lo hi : ℝ) (f e : ℕ → ℝ → ℝ)
    (g : ℝ → ℝ) (b : ℕ → ℝ) (he : UniformOn lo hi e (fun _ => 1))
    (hb : Tendsto b atTop (𝓝 0))
    (hbound : ∀ᶠ N in atTop, ∀ k ∈ Set.Icc lo hi,
      |f N k - g k| ≤ |e N k - 1| + b N) : UniformOn lo hi f g := by
  intro ε hε
  have hsmall := hb.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
  filter_upwards [hbound, he (ε / 2) (by positivity), hsmall] with N hN hE hs
  intro k hk
  have he' := hE k hk
  have hb' := hN k hk
  linarith

theorem sqrt_log_div_nat_tendsto_zero :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log (N : ℝ)) / (N : ℝ)) atTop (𝓝 0) := by
  have hrec : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun N : ℕ => 1 / (N : ℝ) + Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by simpa only [zero_add] using hrec.add log_div_nat_tendsto_zero
  apply squeeze_zero' (Eventually.of_forall (fun N => div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))) _ hb
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hl : 0 ≤ Real.log (N : ℝ) := (Real.log_pos hn).le
  have hs : Real.sqrt (Real.log (N : ℝ)) ≤ 1 + Real.log (N : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith [sq_nonneg (Real.log (N : ℝ))]⟩
  calc
    _ ≤ (1 + Real.log (N : ℝ)) / (N : ℝ) :=
      div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)
    _ = _ := by ring

theorem log_scaledA_div_nat_tendsto_zero (h K : ℝ) (hh : 0 < h) :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) * scaledA N h K / (N : ℝ))
      atTop (𝓝 0) := by
  have hh' : Tendsto (fun N : ℕ => (K / h) *
      (Real.sqrt (Real.log (N : ℝ)) / (N : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := K / h)).mul sqrt_log_div_nat_tendsto_zero
  apply hh'.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hl : 0 ≤ Real.log (N : ℝ) := (Real.log_pos hn).le
  have hs : Real.sqrt (Real.log (N : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Real.log_pos hn))
  unfold scaledA
  field_simp [ne_of_gt hh, hs]
  rw [Real.sq_sqrt hl]

end
end CriticalExtrapolation.Paper
