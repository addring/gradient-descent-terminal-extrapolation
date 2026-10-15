import PaperFramework.TrialDirection

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
