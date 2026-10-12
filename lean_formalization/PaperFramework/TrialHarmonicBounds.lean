import PaperFramework.TrialPerturbationProfiles
import PaperFramework.TrialNormalization

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem trial_reciprocal_product_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) = 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [h1, h2]
    <;> ring

theorem shiftedHarmonic_weighted_telescope (t : ℝ) (ht : 1 ≤ t) (n : ℕ) :
    (∑ k ∈ Finset.range n, shiftedHarmonic t (k + 1) /
      (((k : ℝ) + 1) * ((k : ℝ) + 2))) =
      (∑ k ∈ Finset.range n, 1 / (((k : ℝ) + 1) * ((k : ℝ) + 1 + 2 * t))) -
        shiftedHarmonic t n / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp [shiftedHarmonic]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, shiftedHarmonic_step]
    simp only [Nat.cast_add, Nat.cast_one]
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    have htN : (n : ℝ) + 1 + 2 * t ≠ 0 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    field_simp [h1, h2, htN]
    <;> ring

theorem shiftedHarmonic_weighted_sum_upper (t : ℝ) (ht : 1 ≤ t) (n : ℕ) :
    (∑ k ∈ Finset.range n, shiftedHarmonic t (k + 1) /
      (((k : ℝ) + 1) * ((k : ℝ) + 2))) ≤ 1 := by
  rw [shiftedHarmonic_weighted_telescope t ht]
  calc
    _ ≤ ∑ k ∈ Finset.range n, 1 / (((k : ℝ) + 1) * ((k : ℝ) + 1 + 2 * t)) :=
      sub_le_self _ (div_nonneg (shiftedHarmonic_nonnegative t ht n) (by positivity))
    _ ≤ ∑ k ∈ Finset.range n, 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
      apply Finset.sum_le_sum
      intro k _
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ 1 := by
      rw [trial_reciprocal_product_sum]
      have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith

theorem trial_reciprocal_square_sum_upper (n : ℕ) :
    (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) ^ 2) ≤ 2 := by
  calc
    _ ≤ 2 * ∑ k ∈ Finset.range n, 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [hk]
    _ ≤ 2 := by
      rw [trial_reciprocal_product_sum]
      have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith

theorem trialLeft_square_sum_upper (N : ℕ) (t : ℝ) (ht : 1 ≤ t) :
    (∑ i : Fin N, (1 / ((i.val : ℝ) + 2 * t)) ^ 2) ≤ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (1 / ((k : ℝ) + 2 * t)) ^ 2) N]
  refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (trial_reciprocal_square_sum_upper N)
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hrec := one_div_le_one_div_of_le (by positivity : 0 < (k : ℝ) + 1)
    (show (k : ℝ) + 1 ≤ (k : ℝ) + 2 * t by linarith)
  have hp : 0 ≤ 1 / ((k : ℝ) + 2 * t) := by positivity
  have hq : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
  have hs : (1 / ((k : ℝ) + 2 * t)) ^ 2 ≤ (1 / ((k : ℝ) + 1)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrec) (add_nonneg hp hq)]
  simpa only [div_pow, one_pow] using hs

theorem trialVector_square_sum_upper (N : ℕ) (t : ℝ) (hN : 0 < N) (ht : 1 ≤ t) :
    (∑ i, (trialVector N t i) ^ 2) ≤ 4 + 2 * (shiftedHarmonic t N) ^ 2 / (N : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hright : (∑ i : Fin N, (shiftedHarmonic t (N - i.val) / (N : ℝ)) ^ 2) ≤
      (shiftedHarmonic t N) ^ 2 / (N : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin N, (shiftedHarmonic t N / (N : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hq := div_le_div_of_nonneg_right
          (shiftedHarmonic_monotone t ht (Nat.sub_le N i.val)) hn.le
        have hp : 0 ≤ shiftedHarmonic t (N - i.val) / (N : ℝ) :=
          div_nonneg (shiftedHarmonic_nonnegative t ht _) hn.le
        have hQ : 0 ≤ shiftedHarmonic t N / (N : ℝ) :=
          div_nonneg (shiftedHarmonic_nonnegative t ht _) hn.le
        nlinarith [mul_nonneg (sub_nonneg.mpr hq) (add_nonneg hp hQ)]
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [ne_of_gt hn]
        <;> ring
  have hleft := trialLeft_square_sum_upper N t ht
  calc
    _ ≤ 2 * (∑ i : Fin N, (1 / ((i.val : ℝ) + 2 * t)) ^ 2) +
        2 * ∑ i : Fin N, (shiftedHarmonic t (N - i.val) / (N : ℝ)) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      unfold trialVector
      nlinarith [sq_nonneg (1 / ((i.val : ℝ) + 2 * t) - shiftedHarmonic t (N - i.val) / (N : ℝ))]
    _ ≤ _ := by
      calc
        _ ≤ 2 * 2 + 2 * ((shiftedHarmonic t N) ^ 2 / (N : ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_left hleft (by norm_num))
            (mul_le_mul_of_nonneg_left hright (by norm_num))
        _ = _ := by ring

end
end CriticalExtrapolation.Paper
