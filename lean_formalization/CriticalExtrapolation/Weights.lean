import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Corrected weights, equations (7.4a), (7.4b), (9.4a).
The real-index lemmas apply in particular to every natural index `0 ≤ i < N`.
-/

namespace CriticalExtrapolation

noncomputable def referenceWeight (n i : ℝ) : ℝ :=
  2 * i + 1 - 2 * i * (i + 1) / (n + 1)

noncomputable def comparisonWeight (n i : ℝ) : ℝ :=
  2 * (i + 1) * (n - i) / (n + 1)

noncomputable def weightRemainder (n i : ℝ) : ℝ :=
  -1 + 2 * (i + 1) / (n + 1)

theorem referenceWeight_eq_comparison_add (n i : ℝ) (hn : n + 1 ≠ 0) :
    referenceWeight n i = comparisonWeight n i + weightRemainder n i := by
  unfold referenceWeight comparisonWeight weightRemainder
  field_simp
  ring

theorem referenceWeight_eq_product (n i : ℝ) (hn : n + 1 ≠ 0) :
    referenceWeight n i = 1 + 2 * i * (n - i) / (n + 1) := by
  unfold referenceWeight
  field_simp
  ring

theorem weightRemainder_abs_le_one {n i : ℝ}
    (hi : 0 ≤ i) (hin : i + 1 ≤ n) :
    |weightRemainder n i| ≤ 1 := by
  have hd : 0 < n + 1 := by linarith
  unfold weightRemainder
  apply abs_le.mpr
  constructor
  · have : 0 ≤ 2 * (i + 1) / (n + 1) :=
      div_nonneg (by linarith) (le_of_lt hd)
    linarith
  · have : 2 * (i + 1) / (n + 1) ≤ 2 :=
      (div_le_iff₀ hd).mpr (by linarith)
    linarith

theorem comparisonWeight_lower {n i : ℝ}
    (hn : 2 ≤ n) (hi : 0 ≤ i) (hin : i + 1 ≤ n) :
    4 / 3 ≤ comparisonWeight n i := by
  have hd : 0 < n + 1 := by linarith
  have hp : 0 ≤ i * (n - i - 1) := mul_nonneg hi (by linarith)
  unfold comparisonWeight
  apply (le_div_iff₀ hd).mpr
  nlinarith only [hp, hn]

theorem referenceWeight_quarter_comparison {n i : ℝ}
    (hn : 2 ≤ n) (hi : 0 ≤ i) (hin : i + 1 ≤ n) :
    comparisonWeight n i / 4 ≤ referenceWeight n i := by
  have hq := comparisonWeight_lower hn hi hin
  have hr := weightRemainder_abs_le_one hi hin
  rw [referenceWeight_eq_comparison_add n i (by linarith)]
  have := (abs_le.mp hr).1
  linarith

theorem referenceWeight_pos {n i : ℝ}
    (hn : 1 ≤ n) (hi : 0 ≤ i) (hin : i + 1 ≤ n) :
    0 < referenceWeight n i := by
  rw [referenceWeight_eq_product n i (by linarith)]
  have : 0 ≤ 2 * i * (n - i) / (n + 1) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  linarith

theorem referenceWeight_le_three {n i s : ℝ}
    (hn : 1 ≤ n) (hi : 0 ≤ i) (hin : i + 1 ≤ n) (hs : 1 ≤ s) :
    referenceWeight n i ≤ 3 * (i + s) * (n - i) / n := by
  have hn0 : 0 < n := by linarith
  have hd : 0 < n + 1 := by linarith
  have hprod : n ≤ (i + s) * (n - i) := by
    have h1 : 0 ≤ i * (n - i - 1) := mul_nonneg hi (by linarith)
    have h2 : 0 ≤ (s - 1) * (n - i) := mul_nonneg (by linarith) (by linarith)
    nlinarith only [h1, h2]
  have hmid : 2 * i * (n - i) / (n + 1) ≤
      2 * (i + s) * (n - i) / n := by
    apply (div_le_div_iff₀ hd hn0).mpr
    have h1 : 0 ≤ 2 * i * (n - i) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ 2 * s * (n - i) * (n + 1) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (le_of_lt hd)
    nlinarith only [h1, h2]
  rw [referenceWeight_eq_product n i (ne_of_gt hd)]
  have hunit : 1 ≤ (i + s) * (n - i) / n :=
    (le_div_iff₀ hn0).mpr (by simpa using hprod)
  calc
    1 + 2 * i * (n - i) / (n + 1) ≤
        (i + s) * (n - i) / n + 2 * (i + s) * (n - i) / n :=
      add_le_add hunit hmid
    _ = 3 * (i + s) * (n - i) / n := by ring

/-- Absolute reciprocal stability; no sign of the reciprocal difference is assumed. -/
theorem reciprocal_stability {e q : ℝ}
    (hq : 0 < q) (he : q / 4 ≤ e) (hr : |e - q| ≤ 1) :
    |1 / e - 1 / q| ≤ 4 / q ^ 2 := by
  have he0 : 0 < e := by linarith
  have heq : 0 < e * q := mul_pos he0 hq
  have hqq : 0 < q ^ 2 := sq_pos_of_pos hq
  have hid : 1 / e - 1 / q = (q - e) / (e * q) := by
    field_simp
  rw [hid, abs_div, abs_of_pos heq, abs_sub_comm]
  apply (div_le_div_iff₀ heq hqq).mpr
  have h1 : |e - q| * q ^ 2 ≤ q ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right hr (le_of_lt hqq)
  have h2 : q ^ 2 ≤ 4 * (e * q) := by
    have := mul_le_mul_of_nonneg_right he (le_of_lt hq)
    nlinarith only [this]
  exact h1.trans h2

theorem inverse_comparisonWeight {n i : ℝ}
    (hi : 0 ≤ i) (hin : i + 1 ≤ n) :
    1 / comparisonWeight n i = (1 / (i + 1) + 1 / (n - i)) / 2 := by
  have ha : i + 1 ≠ 0 := by linarith
  have hb : n - i ≠ 0 := by linarith
  have hn : n + 1 ≠ 0 := by linarith
  unfold comparisonWeight
  field_simp
  ring

/-- Equation (7.4b) for every index. -/
theorem reciprocal_referenceWeight_error {n i : ℝ}
    (hn : 2 ≤ n) (hi : 0 ≤ i) (hin : i + 1 ≤ n) :
    |1 / referenceWeight n i - 1 / comparisonWeight n i| ≤
      2 * (1 / (i + 1) ^ 2 + 1 / (n - i) ^ 2) := by
  have hq0 : 0 < comparisonWeight n i := by
    have := comparisonWeight_lower hn hi hin
    linarith
  have hr : |referenceWeight n i - comparisonWeight n i| ≤ 1 := by
    rw [referenceWeight_eq_comparison_add n i (by linarith)]
    simpa using weightRemainder_abs_le_one hi hin
  have hs := reciprocal_stability hq0 (referenceWeight_quarter_comparison hn hi hin) hr
  have hid : 4 / comparisonWeight n i ^ 2 =
      (1 / (i + 1) + 1 / (n - i)) ^ 2 := by
    have := inverse_comparisonWeight hi hin
    calc
      _ = 4 * (1 / comparisonWeight n i) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  rw [hid] at hs
  have hbound : (1 / (i + 1) + 1 / (n - i)) ^ 2 ≤
      2 * (1 / (i + 1) ^ 2 + 1 / (n - i) ^ 2) := by
    calc
      _ ≤ 2 * ((1 / (i + 1)) ^ 2 + (1 / (n - i)) ^ 2) := by
        nlinarith only [sq_nonneg (1 / (i + 1) - 1 / (n - i))]
      _ = _ := by simp only [div_pow, one_pow]
  exact hs.trans hbound

end CriticalExtrapolation
