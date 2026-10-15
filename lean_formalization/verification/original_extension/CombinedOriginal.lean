import PaperFramework.TrialDirection
import PaperFramework.TrialAsymptotics
import PaperFramework.LargeQuadratic
import Mathlib.Analysis.SpecificLimits.Normed
import PaperFramework.CriticalInterval


/- Source: PaperFramework/OriginalFeasibility.lean -/

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- The reciprocal part dominates the possible negative harmonic contribution. -/
theorem original_reciprocal_margin (N i : ℕ) (t : ℝ)
    (ht : 1 ≤ t) (hN : 4 * t ≤ (N : ℝ)) (hi : i < N) :
    1 / (2 * (N : ℝ)) <
      ((i : ℝ) + t + 1) / (((i : ℝ) + 2 * t) * ((i : ℝ) + 2 * t + 1)) := by
  have hn : 0 < (N : ℝ) := by linarith
  have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
  have hin : (i : ℝ) < N := by exact_mod_cast hi
  let u : ℝ := (i : ℝ) + 2 * t
  have hu : 0 < u := by dsimp [u]; linarith
  have hu1 : 0 < u + 1 := by linarith
  have hid : ((i : ℝ) + t + 1) / (u * (u + 1)) =
      (1 - t / (u + 1)) / u := by
    dsimp [u]
    field_simp
    <;> ring
  change 1 / (2 * (N : ℝ)) < ((i : ℝ) + t + 1) / (u * (u + 1))
  rw [hid]
  by_cases hsmall : (i : ℝ) < 2 * t
  · have hu4 : u < 4 * t := by dsimp [u]; linarith
    have hhalf : t / (u + 1) < 1 / 2 := by
      apply (div_lt_iff₀ hu1).mpr
      dsimp [u]
      linarith
    have hfirst : 1 / (2 * (N : ℝ)) ≤ 1 / (8 * t) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hsecond : 1 / (8 * t) < 1 / (2 * u) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have hthird : 1 / (2 * u) < (1 - t / (u + 1)) / u := by
      apply (lt_div_iff₀ hu).mpr
      have he : 1 / (2 * u) * u = (1 : ℝ) / 2 := by field_simp
      rw [he]
      linarith
    exact hfirst.trans_lt (hsecond.trans hthird)
  · have hu4 : 4 * t ≤ u := by dsimp [u]; linarith
    have huN : u ≤ 3 * (N : ℝ) / 2 := by dsimp [u]; linarith
    have hquarter : t / (u + 1) < 1 / 4 := by
      apply (div_lt_iff₀ hu1).mpr
      linarith
    have hfirst : 1 / (2 * (N : ℝ)) ≤ (3 / 4 : ℝ) / u := by
      apply (le_div_iff₀ hu).mpr
      rw [show 1 / (2 * (N : ℝ)) * u = u / (2 * (N : ℝ)) by ring]
      apply (div_le_iff₀ (by positivity : 0 < 2 * (N : ℝ))).mpr
      linarith
    have hsecond : (3 / 4 : ℝ) / u < (1 - t / (u + 1)) / u :=
      div_lt_div_of_pos_right (by linarith) hu
    exact hfirst.trans_lt hsecond

theorem original_trial_coefficient_positive (N : ℕ) (t : ℝ)
    (ht : 1 ≤ t) (hN : 4 * t ≤ (N : ℝ))
    (i j : Fin N) (hij : i.val + 1 = j.val) :
    0 < t * trialVector N t j - (t - 1) * trialVector N t i := by
  have hn : 0 < (N : ℝ) := by linarith
  have hnat : N - i.val = N - j.val + 1 := by omega
  have hjR : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij.symm
  have hstep : shiftedHarmonic t (N - i.val) =
      shiftedHarmonic t (N - j.val) +
        1 / (((N - i.val : ℕ) : ℝ) + 2 * t) := by
    rw [hnat, shiftedHarmonic_step]
    congr 2
    push_cast
    ring
  have hden : 0 < ((N - i.val : ℕ) : ℝ) + 2 * t := by positivity
  have hfrac : (t - 1) / (((N - i.val : ℕ) : ℝ) + 2 * t) < 1 / 2 := by
    apply (div_lt_iff₀ hden).mpr
    have hj0 := Nat.cast_nonneg (α := ℝ) (N - i.val)
    linarith
  have hH := shiftedHarmonic_nonnegative t ht (N - j.val)
  have hmargin := original_reciprocal_margin N i.val t ht hN i.isLt
  have hi0 := Nat.cast_nonneg (α := ℝ) i.val
  have hu : 0 < (i.val : ℝ) + 2 * t := by linarith
  have hu1 : 0 < (i.val : ℝ) + 2 * t + 1 := by linarith
  have hid : t * trialVector N t j - (t - 1) * trialVector N t i =
      ((i.val : ℝ) + t + 1) / (((i.val : ℝ) + 2 * t) * ((i.val : ℝ) + 2 * t + 1)) +
      (shiftedHarmonic t (N - j.val) -
        (t - 1) / (((N - i.val : ℕ) : ℝ) + 2 * t)) / (N : ℝ) := by
    simp only [trialVector, hjR, hstep]
    field_simp
    <;> ring
  rw [hid]
  have hright : -(1 / (2 * (N : ℝ))) <
      (shiftedHarmonic t (N - j.val) -
        (t - 1) / (((N - i.val : ℕ) : ℝ) + 2 * t)) / (N : ℝ) := by
    apply (lt_div_iff₀ hn).mpr
    have he : -(1 / (2 * (N : ℝ))) * (N : ℝ) = -(1 / 2 : ℝ) := by field_simp
    rw [he]
    linarith
  linarith

/-- The strict slope ordering persists for every nonnegative shifted parameter. -/
theorem original_trial_functional_positive (N : ℕ) (a t : ℝ)
    (ha : 0 ≤ a) (ht : 1 ≤ t) (hN : 4 * t ≤ (N : ℝ))
    (i j : Fin N) (hij : i.val + 1 = j.val) :
    0 < trialSlopeFunctional a t (trialVector N t) i := by
  have hbase := trialVector_functional_positive N 0 t (by norm_num) ht
    (by unfold trialParameterMax; positivity) i j hij
  have hcoef := original_trial_coefficient_positive N t ht hN i j hij
  have hid : trialSlopeFunctional a t (trialVector N t) i =
      trialSlopeFunctional 0 t (trialVector N t) i +
        a * (t * trialVector N t j - (t - 1) * trialVector N t i) := by
    unfold trialSlopeFunctional energyD
    rw [difference_adjacent _ i j hij]
    ring
  rw [hid]
  exact add_pos_of_pos_of_nonneg hbase (mul_nonneg ha hcoef.le)

/-- Unlike the earlier lemma, this has no upper bound on N(c-1). -/
theorem original_trial_strict_feasibility (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hN : 4 * (1 / h) ≤ (N : ℝ)) :
    StrictlyFeasible h c (trialDirection N ((N : ℝ) * (c - 1)) (1 / h)) := by
  let a : ℝ := (N : ℝ) * (c - 1)
  let t : ℝ := 1 / h
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hp.c_ge_one)
  have ht : 1 ≤ t := (le_div_iff₀ hp.h_pos).mpr (by simpa using hp.h_le_one)
  have ht0 : 0 < t := by linarith
  have hV := trial_normalization_positive N t hp.n_pos ht
  have hsum := normalizedTrial_normalized N t hp.n_pos ht
  change StrictlyFeasible h c (shiftedDirection a t (normalizedTrial N t))
  refine ⟨shifted_direction_normalized N a t hp.n_pos ha ht0 _ hsum, ?_, ?_⟩
  · intro i
    rw [shifted_direction_difference]
    have hm : 0 < shiftMass a t := div_pos ht0 (by linarith)
    have hb : 0 ≤ shiftB N a t := by unfold shiftB; positivity
    have he : 0 ≤ (if i.val + 1 = N then shiftB N a t else 0) := by
      split_ifs <;> positivity
    exact add_pos_of_pos_of_nonneg
      (mul_pos hm (normalizedTrial_differences_positive N t hp.n_pos ht i)) he
  · intro i j hij
    apply shifted_slopes_strict_of_functional N h c hp _ hsum i j hij
    rw [trialSlopeFunctional_normalized]
    exact div_pos (original_trial_functional_positive N a t ha ht hN i j hij) hV

end
end CriticalExtrapolation.Paper


/- Source: PaperFramework/OriginalEnergy.lean -/

namespace CriticalExtrapolation.Paper
open scoped BigOperators
open Filter Topology
noncomputable section

def originalEnergyConstant (A t : ℝ) : ℝ :=
  2 * (A + t + 1) * (A + t) * trialWeightConstant t

/-- A one-sided estimate suffices, and holds on every fixed compact a interval. -/
theorem original_energy_perturbation_upper (N : ℕ) (a t A : ℝ)
    (hN : 0 < N) (ht : 1 ≤ t) (hA : 0 ≤ A) (ha : a ∈ Set.Icc (0 : ℝ) A) :
    homogeneousEnergy a t (trialVector N t) ≤
      homogeneousEnergy 0 1 (trialVector N t) +
        originalEnergyConstant A t * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ)) := by
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : 0 < (N : ℝ) := by linarith
  have ht0 : 0 < t := by linarith
  have hc : 0 ≤ a + t - 1 := by linarith [ha.1]
  have hct : a + t - 1 ≤ A + t := by linarith [ha.2]
  have hJ0 := trial_baseline_J_nonnegative N t ht
  have hF : 0 ≤ energyF N a t := by unfold energyF; linarith [ha.1]
  have hFup : energyF N a t / (N : ℝ) ≤ A + t + 1 := by
    apply (div_le_iff₀ hn0).mpr
    unfold energyF
    nlinarith [ha.2, mul_nonneg (sub_nonneg.mpr hn) (by linarith : 0 ≤ A + t)]
  have hd := trial_J_parameter_difference_bound N a t ha.1 ht
  have hw := trial_weighted_sum_log_bound N t hN ht
  let K : ℝ := trialWeightConstant t * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; exact mul_nonneg (trialWeightConstant_positive t).le (by positivity)
  have hdiff : |trialEnergyJ a t (trialVector N t) - trialEnergyJ 0 1 (trialVector N t)| ≤
      (A + t) * K / (N : ℝ) := by
    apply (le_div_iff₀ hn0).mpr
    calc
      _ ≤ (a + t - 1) * ((N : ℝ) *
          (∑ i : Fin N, ((i.val : ℝ) + 1) * difference (trialVector N t) i *
            trialVector N t i / ((N : ℝ) - i.val))) := by
        have hh := mul_le_mul_of_nonneg_right hd hn0.le
        convert hh using 1 <;> ring
      _ ≤ (a + t - 1) * K := mul_le_mul_of_nonneg_left hw hc
      _ ≤ (A + t) * K := mul_le_mul_of_nonneg_right hct hK
  have hpert : 2 * energyF N a t *
      |trialEnergyJ a t (trialVector N t) - trialEnergyJ 0 1 (trialVector N t)| ≤
      originalEnergyConstant A t * (1 + (Real.log (N : ℝ)) ^ 2 / (N : ℝ)) := by
    calc
      _ ≤ 2 * energyF N a t * ((A + t) * K / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = (energyF N a t / (N : ℝ)) * (2 * (A + t) * K) := by ring
      _ ≤ (A + t + 1) * (2 * (A + t) * K) :=
        mul_le_mul_of_nonneg_right hFup (by positivity)
      _ = _ := by unfold originalEnergyConstant; dsimp [K]; ring
  have he := homogeneousEnergy_parameter_difference a t (trialVector N t)
  have habs := neg_abs_le (trialEnergyJ a t (trialVector N t) - trialEnergyJ 0 1 (trialVector N t))
  have hprod := mul_le_mul_of_nonneg_left habs (show 0 ≤ 2 * energyF N a t by positivity)
  have hnonneg := mul_nonneg hc hJ0
  linarith only [he, hprod, hnonneg, hpert]

/-- Uniform upper energy asymptotic on any fixed interval [0,A]. -/
theorem original_energy_eventual_upper (t A δ : ℝ)
    (ht : 1 ≤ t) (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ a ∈ Set.Icc (0 : ℝ) A,
      Real.log (N : ℝ) * homogeneousEnergy a t (normalizedTrial N t) < 1 + δ := by
  let l : ℕ → ℝ := fun N => Real.log (N : ℝ)
  let H : ℕ → ℝ := fun N => trialNormalization N t
  let v : ℕ → ℝ := fun N =>
    (homogeneousEnergy 0 1 (trialVector N t) / l N) / (H N / l N) ^ 2
  let b : ℕ → ℝ := fun N =>
    originalEnergyConstant A t * (1 / l N + l N / (N : ℝ)) / (H N / l N) ^ 2
  have hratio := trialNormalization_div_log_tendsto t ht
  have hv : Tendsto v atTop (𝓝 1) := by
    convert (trial_reference_energy_limit t ht).div (hratio.pow 2)
      (by norm_num : (2 : ℝ) ^ 2 ≠ 0) using 1 <;> norm_num
  have hinv : Tendsto (fun N => 1 / l N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hb : Tendsto b atTop (𝓝 0) := by
    convert ((tendsto_const_nhds (x := originalEnergyConstant A t)).mul
      (hinv.add log_div_nat_tendsto_zero)).div (hratio.pow 2)
      (by norm_num : (2 : ℝ) ^ 2 ≠ 0) using 1 <;> norm_num
  have hsmall : ∀ᶠ N in atTop, v N + b N < 1 + δ := by
    have hlim : Tendsto (fun N => v N + b N) atTop (𝓝 1) := by simpa using hv.add hb
    exact hlim.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hsmall, eventually_ge_atTop 2] with N hs hN
  intro a ha
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hl : 0 < l N := Real.log_pos hNr
  have hH : 0 < H N := trial_normalization_positive N t (by omega) ht
  have hbound := mul_le_mul_of_nonneg_left
    (original_energy_perturbation_upper N a t A (by omega) ht hA ha)
    (show 0 ≤ l N / (H N) ^ 2 by positivity)
  have hid : l N / (H N) ^ 2 *
      (homogeneousEnergy 0 1 (trialVector N t) +
        originalEnergyConstant A t * (1 + (l N) ^ 2 / (N : ℝ))) = v N + b N := by
    dsimp [v, b]
    have hn : (N : ℝ) ≠ 0 := ne_of_gt (by positivity : 0 < (N : ℝ))
    field_simp [ne_of_gt hl, ne_of_gt hH, hn]
    <;> ring
  rw [hid] at hbound
  rw [normalizedTrial_energy]
  change l N * (homogeneousEnergy a t (trialVector N t) / (H N) ^ 2) < _
  have he : l N * (homogeneousEnergy a t (trialVector N t) / (H N) ^ 2) =
      l N / (H N) ^ 2 * homogeneousEnergy a t (trialVector N t) := by ring
  rw [he]
  exact hbound.trans_lt hs

end
end CriticalExtrapolation.Paper


/- Source: PaperFramework/OriginalQuadratic.lean -/

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

theorem original_quadratic_tail_decay (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 2 * (1 / h)) * (1 - h) ^ N)
      atTop (𝓝 0) := by
  have hr : 0 ≤ 1 - h := by linarith
  have hr1 : 1 - h < 1 := by linarith
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1
  have hnp := tendsto_self_mul_const_pow_of_lt_one hr hr1
  convert hnp.add ((tendsto_const_nhds (x := 2 * (1 / h))).mul hp) using 1
  · ext N
    ring
  · simp

/-- A single quadratic covers the entire unbounded right tail, uniformly in a. -/
theorem original_quadratic_tail_failure (h L D : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 0 < L) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, ∀ a ≥ 2 * (1 / h),
      L * D / S N h (1 + a / (N : ℝ)) <
        worstGradient N h (1 + a / (N : ℝ)) L D := by
  let t : ℝ := 1 / h
  have ht : 0 < t := one_div_pos.mpr hh
  have hsmall : ∀ᶠ N : ℕ in atTop,
      ((N : ℝ) + 2 * t) * (1 - h) ^ N < t :=
    (original_quadratic_tail_decay h hh hh1).eventually (gt_mem_nhds ht)
  filter_upwards [hsmall, eventually_gt_atTop 0] with N hs hN
  intro a ha
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have ha0 : 0 ≤ a := by linarith
  let c : ℝ := 1 + a / (N : ℝ)
  have hc : 1 ≤ c := by
    dsimp [c]
    exact le_add_of_nonneg_right (div_nonneg ha0 hn.le)
  let r : ℝ := (1 - h) ^ N
  have hr1 : r ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  let y : ℝ := 1 - c * (1 - r)
  have hid : (N : ℝ) * (-y) = a * (1 - r) - (N : ℝ) * r := by
    dsimp [y, c]
    field_simp [hn.ne']
    <;> ring
  have hny : t < (N : ℝ) * (-y) := by
    rw [hid]
    have hm := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hr1)
    change ((N : ℝ) + 2 * t) * r < t at hs
    nlinarith only [hm, hs]
  have hy : t / (N : ℝ) < -y := by
    apply (div_lt_iff₀ hn).mpr
    nlinarith only [hny]
  have hB : 1 / S N h c < t / (N : ℝ) := by
    have he : S N h c = h * ((N : ℝ) + a + t) := by
      dsimp [S, c, t]
      field_simp [hn.ne', hh.ne']
      <;> ring
    have hbound : 1 / S N h c = t / ((N : ℝ) + a + t) := by
      rw [he]
      dsimp [t]
      field_simp
    rw [hbound]
    exact div_lt_div_of_pos_left ht hn (by linarith)
  let I₀ := quadraticUnitInstance 1 unitOne
  have hrad : D * ‖unitOne‖ ≤ D := by rw [unitOne_norm, mul_one]
  let I := dilatedInstance I₀ L D D hL hD hrad
  have hbase : ‖gradient I₀.f (output I₀ N h c)‖ = |y| := by
    change ‖gradient halfSquaredNorm (output (quadraticUnitInstance 1 unitOne) N h c)‖ = _
    rw [quadraticUnitInstance_output, halfSquaredNorm_gradient, norm_smul,
      Real.norm_eq_abs, unitOne_norm, mul_one]
  have hgrad : ‖gradient I.f (output I N h c)‖ = L * D * |y| := by
    change ‖gradient (dilatedInstance I₀ L D D hL hD hrad).f
      (output (dilatedInstance I₀ L D D hL hD hrad) N h c)‖ = _
    rw [dilatedInstance_output, dilatedInstance_gradient, norm_smul,
      Real.norm_eq_abs, abs_of_pos (mul_pos hL hD), hbase]
  have hstrict := mul_lt_mul_of_pos_left
    ((hB.trans hy).trans_le (neg_le_abs y)) (mul_pos hL hD)
  have hactual : L * D / S N h c < ‖gradient I.f (output I N h c)‖ := by
    rw [hgrad]
    convert hstrict using 1 <;> ring
  have hsup : ‖gradient I.f (output I N h c)‖ ≤ worstGradient N h c L D :=
    le_csSup (instance_values_nonempty_bounded N h c L D hL hD).2 ⟨1, I, rfl⟩
  exact hactual.trans_le hsup

end
end CriticalExtrapolation.Paper


/- Source: PaperFramework/OriginalObjective.lean -/

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


/- Source: PaperFramework/OriginalCritical.lean -/

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


/- Source: OriginalExtension.lean -/

/-! The pointwise-definition extension. This separate entry
allows the established initial-interval library to retain its existing scope. -/


/- Source: OriginalAudit.lean -/

#print CriticalExtrapolation.Paper.originalValiditySet
#print CriticalExtrapolation.Paper.originalCriticalCoefficient
#print CriticalExtrapolation.Paper.original_eventual_upper_failure_fixed_step
#print CriticalExtrapolation.Paper.original_sharp_critical_scale
#print axioms CriticalExtrapolation.Paper.original_reciprocal_margin
#print axioms CriticalExtrapolation.Paper.original_trial_coefficient_positive
#print axioms CriticalExtrapolation.Paper.original_trial_functional_positive
#print axioms CriticalExtrapolation.Paper.original_trial_strict_feasibility
#print axioms CriticalExtrapolation.Paper.original_energy_perturbation_upper
#print axioms CriticalExtrapolation.Paper.original_energy_eventual_upper
#print axioms CriticalExtrapolation.Paper.original_trial_identity
#print axioms CriticalExtrapolation.Paper.original_terminal_log_upper
#print axioms CriticalExtrapolation.Paper.original_negative_scalar
#print axioms CriticalExtrapolation.Paper.original_eventual_negative_trial
#print axioms CriticalExtrapolation.Paper.original_quadratic_tail_decay
#print axioms CriticalExtrapolation.Paper.original_quadratic_tail_failure
#print axioms CriticalExtrapolation.Paper.original_eventual_upper_failure_fixed_step
#print axioms CriticalExtrapolation.Paper.original_critical_sandwich
#print axioms CriticalExtrapolation.Paper.original_sharp_critical_scale
#print axioms CriticalExtrapolation.Paper.original_critical_increment_small
#print axioms CriticalExtrapolation.Paper.original_no_positive_inverse_linear_lower_bound
#print axioms CriticalExtrapolation.Paper.original_conjecture_5_1_false

