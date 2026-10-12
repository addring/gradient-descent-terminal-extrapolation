import PaperFramework.QPUniform
import Mathlib.Order.Fin.Basic

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- The quantity B in (4.1), written without division. -/
def feasibilityGap {N : ℕ} (h c : ℝ) (β : Vec N) (i : Fin N) : ℝ :=
  queryK N h c i * β i - applyT h c β i

theorem difference_adjacent {N : ℕ} (β : Vec N) (i j : Fin N)
    (hij : i.val + 1 = j.val) : difference β i = β i - β j := by
  have hj : i.val + 1 < N := by omega
  simp only [difference, zeroExtend, dif_pos hj]
  congr 1
  exact congrArg β (Fin.ext hij)

theorem antitone_of_differences {N : ℕ} (β : Vec N)
    (hd : ∀ i, 0 ≤ difference β i) : Antitone β := by
  cases N with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    have hi := hd i.castSucc
    rw [difference_adjacent β i.castSucc i.succ rfl] at hi
    linarith

theorem prefix_sum_adjacent {N : ℕ} (β : Vec N) (i j : Fin N)
    (hij : i.val + 1 = j.val) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin N => k < j), β k) =
      (∑ k ∈ Finset.univ.filter (fun k : Fin N => k < i), β k) + β i := by
  classical
  have hs : Finset.univ.filter (fun k : Fin N => k < j) =
      insert i (Finset.univ.filter (fun k : Fin N => k < i)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.lt_def, Fin.ext_iff]
    omega
  rw [hs, Finset.sum_insert (by simp)]
  ring

theorem applyT_adjacent {N : ℕ} (h c : ℝ) (β : Vec N) (i j : Fin N)
    (hij : i.val + 1 = j.val) :
    applyT h c β j = applyT h c β i - h * β i + difference β i := by
  rw [difference_adjacent β i j hij]
  unfold applyT
  rw [prefix_sum_adjacent β i j hij]
  ring

theorem queryK_adjacent {N : ℕ} (h c : ℝ) (i j : Fin N)
    (hij : i.val + 1 = j.val) : queryK N h c j = queryK N h c i - h := by
  have hijr : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij.symm
  simp only [queryK, hijr]
  ring

theorem feasibilityGap_eq (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (i : Fin N) :
    feasibilityGap h c β i = queryK N h c i * (β i - slope h c β i) := by
  unfold feasibilityGap slope
  field_simp [ne_of_gt (queryK_positive N h c hp i)]

theorem feasibilityGap_adjacent {N : ℕ} (h c : ℝ) (β : Vec N)
    (i j : Fin N) (hij : i.val + 1 = j.val) :
    feasibilityGap h c β j = feasibilityGap h c β i -
      (queryK N h c j + 1) * difference β i := by
  unfold feasibilityGap
  rw [applyT_adjacent h c β i j hij, queryK_adjacent h c i j hij,
    difference_adjacent β i j hij]
  ring

theorem slope_gap_adjacent (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (i j : Fin N) (hij : i.val + 1 = j.val) :
    queryK N h c j * (slope h c β i - slope h c β j) =
      h * feasibilityGap h c β i / queryK N h c i - difference β i := by
  have hi := ne_of_gt (queryK_positive N h c hp i)
  have hj := ne_of_gt (queryK_positive N h c hp j)
  unfold slope feasibilityGap
  field_simp
  rw [applyT_adjacent h c β i j hij, queryK_adjacent h c i j hij]
  ring

theorem feasible_first_coordinate_lower_bound (N : ℕ) (h c : ℝ)
    (hp : Parameters N h c) (β : Vec N) (hβ : Feasible h c β) :
    1 / (N : ℝ) ≤ β ⟨0, hp.n_pos⟩ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast hp.n_pos
  apply (div_le_iff₀ hN).mpr
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => antitone_of_differences β hβ.2.1 (show (⟨0, hp.n_pos⟩ : Fin N) ≤ i by
      change 0 ≤ i.val
      exact Nat.zero_le _))
  simpa [hβ.1, mul_comm] using hs

theorem feasibilityGap_first_positive (N : ℕ) (h c : ℝ)
    (hp : Parameters N h c) (β : Vec N) (hβ : Feasible h c β) :
    0 < feasibilityGap h c β ⟨0, hp.n_pos⟩ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast hp.n_pos
  have hb := feasible_first_coordinate_lower_bound N h c hp β hβ
  have hprod : 1 ≤ (N : ℝ) * β ⟨0, hp.n_pos⟩ := by
    have := (div_le_iff₀ hN).mp hb
    nlinarith
  have hhc : 0 ≤ h * c := mul_nonneg hp.h_pos.le (by linarith [hp.c_ge_one])
  have hbpos : 0 < β ⟨0, hp.n_pos⟩ := lt_of_lt_of_le (one_div_pos.mpr hN) hb
  simp only [feasibilityGap, queryK, applyT, hβ.1, Nat.cast_zero, sub_zero, mul_one]
  have hempty : Finset.univ.filter (fun j : Fin N => j < ⟨0, hp.n_pos⟩) = ∅ := by
    ext j
    simp [Fin.lt_def]
  rw [hempty]
  simp only [Finset.sum_empty, mul_zero, sub_zero]
  nlinarith [mul_nonneg hhc (sub_nonneg.mpr hprod)]

theorem feasibilityGap_propagates (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (hβ : Feasible h c β)
    (i j : Fin N) (hij : i.val + 1 = j.val) (hi : 0 < feasibilityGap h c β i) :
    0 < feasibilityGap h c β j := by
  have hKi := queryK_positive N h c hp i
  have hKj := queryK_positive N h c hp j
  have hδ : difference β i ≤ h * feasibilityGap h c β i / queryK N h c i := by
    have hs := slope_gap_adjacent N h c hp β i j hij
    have hnonneg := mul_nonneg hKj.le (sub_nonneg.mpr (hβ.2.2 i j hij))
    linarith
  have hbound : (1 - h) * queryK N h c j / queryK N h c i *
      feasibilityGap h c β i ≤ feasibilityGap h c β j := by
    have heq : feasibilityGap h c β j -
        (1 - h) * queryK N h c j / queryK N h c i * feasibilityGap h c β i =
        (queryK N h c j + 1) *
          (h * feasibilityGap h c β i / queryK N h c i - difference β i) := by
      rw [feasibilityGap_adjacent h c β i j hij]
      field_simp
      rw [queryK_adjacent h c i j hij]
      ring
    have hm := mul_nonneg (by linarith : 0 ≤ queryK N h c j + 1) (sub_nonneg.mpr hδ)
    linarith
  exact lt_of_lt_of_le (mul_pos (div_pos (mul_pos (sub_pos.mpr hh) hKj) hKi) hi) hbound

theorem feasible_gap_positive (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (hβ : Feasible h c β) :
    ∀ i, 0 < feasibilityGap h c β i := by
  intro i
  have hall : ∀ k (hk : k < N), 0 < feasibilityGap h c β ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact feasibilityGap_first_positive N h c hp β hβ
    | succ k ih =>
      intro hk
      exact feasibilityGap_propagates N h c hp hh β hβ ⟨k, by omega⟩ ⟨k + 1, hk⟩
        rfl (ih (by omega))
  exact hall i.val i.isLt

theorem feasibilityGap_terminal (N : ℕ) (h c : ℝ) (β : Vec N)
    (hnorm : (∑ i, β i) = 1) (b : Fin N) (hb : b.val + 1 = N) :
    feasibilityGap h c β b = (1 + (N : ℝ) * h * (c - 1)) * β b - h * (c - 1) := by
  classical
  have hs : Finset.univ = insert b (Finset.univ.filter (fun i : Fin N => i < b)) := by
    symm
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    by_cases hi : i = b
    · simp [hi]
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change i.val < b.val
      have hine : i.val ≠ b.val := fun hv => hi (Fin.ext hv)
      have hiN := i.isLt
      omega
  have hsum : (∑ i ∈ Finset.univ.filter (fun i : Fin N => i < b), β i) = 1 - β b := by
    have ht := hnorm
    rw [hs, Finset.sum_insert (by simp)] at ht
    linarith
  have hbR : (b.val : ℝ) + 1 = N := by exact_mod_cast hb
  unfold feasibilityGap queryK applyT
  rw [hnorm, hsum]
  rw [← hbR]
  ring

theorem feasible_terminal_positive (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (hβ : Feasible h c β)
    (b : Fin N) (hb : b.val + 1 = N) : 0 < β b := by
  have hB := feasible_gap_positive N h c hp hh β hβ b
  rw [feasibilityGap_terminal N h c β hβ.1 b hb] at hB
  have hc : 0 ≤ h * (c - 1) := mul_nonneg hp.h_pos.le (sub_nonneg.mpr hp.c_ge_one)
  have hcoeff : 0 ≤ 1 + (N : ℝ) * h * (c - 1) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg N) hc]
  by_contra hn
  have hm := mul_nonpos_of_nonneg_of_nonpos hcoeff (le_of_not_gt hn)
  linarith

theorem feasible_coordinates_positive (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (hβ : Feasible h c β) : ∀ i, 0 < β i := by
  have hN := hp.n_pos
  let b : Fin N := ⟨N - 1, by omega⟩
  have hb : b.val + 1 = N := by dsimp [b]; omega
  intro i
  exact lt_of_lt_of_le (feasible_terminal_positive N h c hp hh β hβ b hb)
    (antitone_of_differences β hβ.2.1 (show i ≤ b by
      change i.val ≤ N - 1
      omega))

theorem slope_strict_of_zero_difference (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (hβ : Feasible h c β)
    (i j : Fin N) (hij : i.val + 1 = j.val) (hd : difference β i = 0) :
    slope h c β j < slope h c β i := by
  have hs := slope_gap_adjacent N h c hp β i j hij
  rw [hd, sub_zero] at hs
  have hpos := div_pos (mul_pos hp.h_pos (feasible_gap_positive N h c hp hh β hβ i))
    (queryK_positive N h c hp i)
  have hgap : 0 < slope h c β i - slope h c β j :=
    (mul_pos_iff_of_pos_left (queryK_positive N h c hp j)).mp (hs.symm ▸ hpos)
  linarith

end
end CriticalExtrapolation.Paper
