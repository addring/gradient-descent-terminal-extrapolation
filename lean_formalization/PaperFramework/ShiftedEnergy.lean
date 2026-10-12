import PaperFramework.FeasibleFloor
import PaperFramework.RowMomentNormalization
import PaperFramework.NormalizedEnergyBound

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem shifted_direction_normalized (N : ℕ) (a t : ℝ) (hN : 0 < N)
    (ha : 0 ≤ a) (ht : 0 < t) (p : Vec N) (hp : (∑ i, p i) = 1) :
    (∑ i, shiftedDirection a t p i) = 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hat : a + t ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos ha ht)
  simp only [shiftedDirection, Finset.sum_add_distrib, ← Finset.mul_sum, hp,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  unfold shiftB shiftMass
  field_simp [hn, hat]
  <;> ring

theorem shifted_direction_difference {N : ℕ} (a t : ℝ) (p : Vec N) (i : Fin N) :
    difference (shiftedDirection a t p) i = shiftMass a t * difference p i +
      (if i.val + 1 = N then shiftB N a t else 0) := by
  by_cases hi : i.val + 1 < N
  · have hn : i.val + 1 ≠ N := by omega
    simp [difference, shiftedDirection, zeroExtend, hi, hn]
    <;> ring
  · have heq : i.val + 1 = N := by omega
    simp [difference, shiftedDirection, zeroExtend, hi, heq]
    <;> ring

theorem shifted_direction_slope (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (p : Vec N) (hpsum : (∑ i, p i) = 1) (i : Fin N) :
    slope h c (shiftedDirection ((N : ℝ) * (c - 1)) (1 / h) p) i =
      shiftB N ((N : ℝ) * (c - 1)) (1 / h) +
      shiftMass ((N : ℝ) * (c - 1)) (1 / h) *
        (tail p i.val - (1 / h) * p i) / energyD N ((N : ℝ) * (c - 1)) i.val := by
  let a : ℝ := (N : ℝ) * (c - 1)
  let t : ℝ := 1 / h
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hp.c_ge_one)
  have ht : 0 < t := one_div_pos.mpr hp.h_pos
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp.n_pos
  have hh : h ≠ 0 := ne_of_gt hp.h_pos
  have hat : a + t ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos ha ht)
  have hd : energyD N a i.val ≠ 0 := ne_of_gt (energyD_pos N a ha i)
  have hK := ne_of_gt (queryK_positive N h c hp i)
  have hKformula : queryK N h c i = h * energyD N a i.val := by
    unfold queryK energyD
    dsimp [a]
    ring
  have hnorm := shifted_direction_normalized N a t hp.n_pos ha ht p hpsum
  have hprefix : (∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), shiftedDirection a t p j) =
      (i.val : ℝ) * shiftB N a t + shiftMass a t *
        ∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), p j := by
    simp [shiftedDirection, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.filter_gt_eq_Iio, Fin.card_Iio]
  have htotal : (∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), p j) + tail p i.val = 1 := by
    simpa only [not_lt, Fin.le_def, tail, hpsum] using
      Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => j < i) p
  have hpre : (∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), p j) = 1 - tail p i.val := by
    linarith
  change slope h c (shiftedDirection a t p) i =
    shiftB N a t + shiftMass a t * (tail p i.val - t * p i) / energyD N a i.val
  unfold slope applyT
  rw [hnorm, hprefix, hpre]
  rw [hKformula]
  unfold shiftedDirection shiftB shiftMass
  field_simp [hn, hh, hat, hd]
  unfold energyD
  dsimp [a, t]
  field_simp [hh]
  <;> ring

/-- The terminal correction is retained in the exact affine energy expansion. -/
theorem affine_shift_energy_identity (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (p : Vec N) (hpsum : (∑ i, p i) = 1) :
    let a := (N : ℝ) * (c - 1)
    let t := 1 / h
    chainObjective h c (shiftedDirection a t p) / (h ^ 2 * c) =
      (shiftMass a t) ^ 2 * homogeneousEnergy a t p - a ^ 2 / (a + t) ^ 2 - a / (N : ℝ) +
      2 * energyF N a t * shiftMass a t * shiftB N a t * (N : ℝ) * (t - 1) /
        (a + 1) * p ⟨N - 1, by have := hp.n_pos; omega⟩ := by
  let a : ℝ := (N : ℝ) * (c - 1)
  let t : ℝ := 1 / h
  let B := shiftB N a t
  let m := shiftMass a t
  let F := energyF N a t
  let r : Vec N := fun i => (tail p i.val - t * p i) / energyD N a i.val
  let b : Fin N := ⟨N - 1, by have := hp.n_pos; omega⟩
  have hb : b.val + 1 = N := by dsimp [b]; have := hp.n_pos; omega
  have hbR : (b.val : ℝ) + 1 = N := by exact_mod_cast hb
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hp.c_ge_one)
  have ht : 0 < t := one_div_pos.mpr hp.h_pos
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp.n_pos
  have hh : h ≠ 0 := ne_of_gt hp.h_pos
  have hc : c ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp.c_ge_one)
  have hat : a + t ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos ha ht)
  have hnorm := shifted_direction_normalized N a t hp.n_pos ha ht p hpsum
  have hr : r b = (1 - t) * p b / (a + 1) := by
    have htail := tail_step p b
    rw [hb, tail_terminal] at htail
    dsimp [r, energyD]
    rw [htail, ← hbR]
    ring
  have hslope : ∀ i, slope h c (shiftedDirection a t p) i = B + m * r i := by
    intro i
    simpa only [B, m, r, a, t, mul_div_assoc] using shifted_direction_slope N h c hp p hpsum i
  have hdiff : ∀ i, difference (shiftedDirection a t p) i =
      m * difference p i + if i = b then B else 0 := by
    intro i
    have heq : (i.val + 1 = N) ↔ i = b := by
      constructor
      · intro hi; apply Fin.ext; dsimp [b]; omega
      · rintro rfl; exact hb
    simpa only [m, B, heq] using shifted_direction_difference a t p i
  have hterms : (∑ i, ((i.val : ℝ) + 1) * difference (shiftedDirection a t p) i *
      slope h c (shiftedDirection a t p) i) =
      m * B + m ^ 2 * (∑ i, ((i.val : ℝ) + 1) * difference p i * r i) +
        (N : ℝ) * B * (B + m * r b) := by
    have hpoint : ∀ i : Fin N, ((i.val : ℝ) + 1) * difference (shiftedDirection a t p) i *
        slope h c (shiftedDirection a t p) i =
        m * B * (((i.val : ℝ) + 1) * difference p i) +
        m ^ 2 * (((i.val : ℝ) + 1) * difference p i * r i) +
        (if i = b then ((i.val : ℝ) + 1) * B * (B + m * r i) else 0) := by
      intro i
      rw [hslope, hdiff]
      split_ifs <;> ring
    simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [weighted_differences_sum, hpsum]
    simp [hbR]
  have hS : 1 + (N : ℝ) * h * c = h * F := by
    dsimp [F, energyF, a, t]
    field_simp
    <;> ring
  have hconst : c - m ^ 2 - 2 * F * (m * B + (N : ℝ) * B ^ 2) =
      -a ^ 2 / (a + t) ^ 2 - a / (N : ℝ) := by
    dsimp only [B, m, F, shiftB, shiftMass, energyF]
    field_simp [hn, hat]
    dsimp [a, t]
    field_simp [hh]
    <;> ring
  change chainObjective h c (shiftedDirection a t p) / (h ^ 2 * c) =
    m ^ 2 * homogeneousEnergy a t p - a ^ 2 / (a + t) ^ 2 - a / (N : ℝ) +
      2 * F * m * B * (N : ℝ) * (t - 1) / (a + 1) * p b
  unfold chainObjective homogeneousEnergy
  rw [hnorm, hpsum, hterms, hS]
  have heq : (∑ i, ((i.val : ℝ) + 1) * difference p i *
      (tail p i.val - t * p i) / energyD N a i.val) =
      ∑ i, ((i.val : ℝ) + 1) * difference p i * r i := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [r]
    ring
  rw [heq, hr]
  have hcancel : (h ^ 2 * c ^ 2 - 2 * h * c * (h * F) *
      (m * B + m ^ 2 * (∑ i, ((i.val : ℝ) + 1) * difference p i * r i) +
        (N : ℝ) * B * (B + m * ((1 - t) * p b / (a + 1))))) / (h ^ 2 * c) =
      c - 2 * F * (m * B + m ^ 2 * (∑ i, ((i.val : ℝ) + 1) * difference p i * r i) +
        (N : ℝ) * B * (B + m * ((1 - t) * p b / (a + 1)))) := by
    field_simp [hh, hc]
    <;> ring
  norm_num only [one_pow, mul_one]
  rw [hcancel]
  linear_combination hconst

end
end CriticalExtrapolation.Paper
