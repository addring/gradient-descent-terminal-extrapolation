import PaperFramework.TrialNormalization
import PaperFramework.ReferenceRatio

namespace CriticalExtrapolation.Paper
open scoped BigOperators
open Filter Topology
noncomputable section

theorem uniformOn_of_tendsto_error_bound (lo hi a : ℝ) (f : ℕ → ℝ → ℝ)
    (v b : ℕ → ℝ) (hv : Tendsto v atTop (𝓝 a)) (hb : Tendsto b atTop (𝓝 0))
    (hbound : ∀ᶠ N in atTop, ∀ k ∈ Set.Icc lo hi, |f N k - v N| ≤ b N) :
    UniformOn lo hi f (fun _ => a) := by
  intro ε hε
  have hnear : ∀ᶠ N in atTop, |v N - a| < ε / 2 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hv) (ε / 2) (by positivity)
  have hsmall : ∀ᶠ N in atTop, b N < ε / 2 :=
    hb.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
  filter_upwards [hbound, hnear, hsmall] with N hN hn hs
  intro k hk
  calc
    |f N k - a| = |(f N k - v N) + (v N - a)| := by congr 1; ring
    _ ≤ |f N k - v N| + |v N - a| := by
      simpa only [Real.norm_eq_abs] using norm_add_le (f N k - v N) (v N - a)
    _ < ε := by linarith [hN k hk]

theorem trialNormalization_div_log_tendsto (t : ℝ) (ht : 1 ≤ t) :
    Tendsto (fun N : ℕ => trialNormalization N t / Real.log (N : ℝ)) atTop (𝓝 2) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun N : ℕ => |(trialNormalization N t - 2 * Real.log (N : ℝ)) /
      Real.log (N : ℝ)|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _
      (tendsto_const_nhds.div_atTop hlog :
        Tendsto (fun N : ℕ => (4 * t + 2) / Real.log (N : ℝ)) atTop (𝓝 0))
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hL := Real.log_pos hNr
    rw [abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right (trial_normalization_log_error N t (by omega) ht) hL.le
  have he : Tendsto (fun N : ℕ => (trialNormalization N t - 2 * Real.log (N : ℝ)) /
      Real.log (N : ℝ)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hz)
  have hr : Tendsto (fun N : ℕ => (trialNormalization N t - 2 * Real.log (N : ℝ)) /
      Real.log (N : ℝ) + 2) atTop (𝓝 2) := by
    simpa using he.add (tendsto_const_nhds (x := (2 : ℝ)))
  apply hr.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  field_simp [ne_of_gt (Real.log_pos hNr)]
  <;> ring

theorem tail_smul {N : ℕ} (r : ℝ) (p : Vec N) (i : ℕ) :
    tail (r • p) i = r * tail p i := by
  simp only [tail, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem difference_smul {N : ℕ} (r : ℝ) (p : Vec N) (i : Fin N) :
    difference (r • p) i = r * difference p i := by
  unfold difference zeroExtend
  by_cases hi : i.val + 1 < N <;> simp [hi, mul_sub]

theorem homogeneousEnergy_smul {N : ℕ} (a t r : ℝ) (p : Vec N) :
    homogeneousEnergy a t (r • p) = r ^ 2 * homogeneousEnergy a t p := by
  have hs : (∑ i, ((i.val : ℝ) + 1) * difference (r • p) i *
      (tail (r • p) i.val - t * (r • p) i) / energyD N a i.val) =
      r ^ 2 * ∑ i, ((i.val : ℝ) + 1) * difference p i *
        (tail p i.val - t * p i) / energyD N a i.val := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [difference_smul, tail_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  unfold homogeneousEnergy
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

theorem normalizedTrial_energy {N : ℕ} (a t : ℝ) :
    homogeneousEnergy a t (normalizedTrial N t) =
      homogeneousEnergy a t (trialVector N t) / (trialNormalization N t) ^ 2 := by
  have he : normalizedTrial N t = (trialNormalization N t)⁻¹ • trialVector N t := by
    ext i
    simp [normalizedTrial, div_eq_mul_inv, mul_comm]
  rw [he, homogeneousEnergy_smul]
  ring

end
end CriticalExtrapolation.Paper
