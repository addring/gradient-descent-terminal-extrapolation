import PaperFramework.FeasiblePositivity

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- The non-strict gap propagation includes the unit step. -/
theorem feasible_gap_nonnegative (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (hβ : Feasible h c β) : ∀ i, 0 ≤ feasibilityGap h c β i := by
  have hall : ∀ k (hk : k < N), 0 ≤ feasibilityGap h c β ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact (feasibilityGap_first_positive N h c hp β hβ).le
    | succ k ih =>
      intro hk
      let i : Fin N := ⟨k, by omega⟩
      let j : Fin N := ⟨k + 1, hk⟩
      have hKi := queryK_positive N h c hp i
      have hKj := queryK_positive N h c hp j
      have hδ : difference β i ≤ h * feasibilityGap h c β i / queryK N h c i := by
        have hs := slope_gap_adjacent N h c hp β i j rfl
        have hnonneg := mul_nonneg hKj.le (sub_nonneg.mpr (hβ.2.2 i j rfl))
        linarith
      have heq : feasibilityGap h c β j -
          (1 - h) * queryK N h c j / queryK N h c i * feasibilityGap h c β i =
          (queryK N h c j + 1) *
            (h * feasibilityGap h c β i / queryK N h c i - difference β i) := by
        rw [feasibilityGap_adjacent h c β i j rfl]
        field_simp
        rw [queryK_adjacent h c i j rfl]
        ring
      have hprod := mul_nonneg (by linarith : 0 ≤ queryK N h c j + 1) (sub_nonneg.mpr hδ)
      have hbase := mul_nonneg (div_nonneg
        (mul_nonneg (sub_nonneg.mpr hp.h_le_one) hKj.le) hKi.le) (ih (by omega))
      change 0 ≤ feasibilityGap h c β j
      change 0 ≤ (1 - h) * queryK N h c j / queryK N h c i * feasibilityGap h c β i at hbase
      linarith
  intro i
  exact hall i.val i.isLt

theorem feasible_coordinate_floor (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (hβ : Feasible h c β) :
    ∀ i, shiftB N ((N : ℝ) * (c - 1)) (1 / h) ≤ β i := by
  have hN : (0 : ℝ) < N := by exact_mod_cast hp.n_pos
  have hh := hp.h_pos
  have ha : 0 ≤ (N : ℝ) * (c - 1) := mul_nonneg hN.le (sub_nonneg.mpr hp.c_ge_one)
  have hden : 0 < 1 + (N : ℝ) * h * (c - 1) := by
    nlinarith [mul_nonneg hh.le ha]
  let b : Fin N := ⟨N - 1, by have := hp.n_pos; omega⟩
  have hb : b.val + 1 = N := by dsimp [b]; have := hp.n_pos; omega
  have hgap := feasible_gap_nonnegative N h c hp β hβ b
  rw [feasibilityGap_terminal N h c β hβ.1 b hb] at hgap
  have hfloor : h * (c - 1) / (1 + (N : ℝ) * h * (c - 1)) ≤ β b :=
    (div_le_iff₀ hden).mpr (by nlinarith only [hgap])
  have hid : shiftB N ((N : ℝ) * (c - 1)) (1 / h) =
      h * (c - 1) / (1 + (N : ℝ) * h * (c - 1)) := by
    have ht : 0 < (N : ℝ) * (c - 1) + 1 / h := add_pos_of_nonneg_of_pos ha (one_div_pos.mpr hh)
    unfold shiftB
    field_simp [ne_of_gt hh, ne_of_gt hN, ne_of_gt hden, ne_of_gt ht]
    <;> ring
  intro i
  rw [hid]
  exact hfloor.trans (antitone_of_differences β hβ.2.1 (show i ≤ b by change i.val ≤ N - 1; omega))

theorem feasible_shift_representation (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (hβ : Feasible h c β) :
    ∃ p : Vec N, (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      β = shiftedDirection ((N : ℝ) * (c - 1)) (1 / h) p := by
  let a : ℝ := (N : ℝ) * (c - 1)
  let t : ℝ := 1 / h
  let B := shiftB N a t
  let m := shiftMass a t
  have hN : (0 : ℝ) < N := by exact_mod_cast hp.n_pos
  have ha : 0 ≤ a := mul_nonneg hN.le (sub_nonneg.mpr hp.c_ge_one)
  have ht : 0 < t := one_div_pos.mpr hp.h_pos
  have hat : 0 < a + t := add_pos_of_nonneg_of_pos ha ht
  have hm : 0 < m := div_pos ht hat
  let p : Vec N := fun i => (β i - B) / m
  have hmass : (N : ℝ) * B + m = 1 := by
    dsimp [B, m, shiftB, shiftMass]
    field_simp [ne_of_gt hN, ne_of_gt hat]
    <;> ring
  refine ⟨p, ?_, ?_, ?_⟩
  · intro i
    exact div_nonneg (sub_nonneg.mpr (feasible_coordinate_floor N h c hp β hβ i)) hm.le
  · change (∑ i, (β i - B) / m) = 1
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hβ.1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    apply (div_eq_one_iff_eq (ne_of_gt hm)).mpr
    linarith
  · funext i
    change β i = B + m * ((β i - B) / m)
    field_simp [ne_of_gt hm]
    <;> ring

end
end CriticalExtrapolation.Paper
