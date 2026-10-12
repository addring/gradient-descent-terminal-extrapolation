import PaperFramework.TrialPerturbationProfiles
import PaperFramework.RowMomentNormalization
import PaperFramework.Energy

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem zeroExtend_pointwise_sq {N : ℕ} (p : Vec N) (k : ℕ) :
    zeroExtend (fun i => (p i) ^ 2) k = (zeroExtend p k) ^ 2 := by
  by_cases hk : k < N <;> simp [zeroExtend, hk]

theorem weighted_square_differences_sum {N : ℕ} (p : Vec N) :
    (∑ i, ((i.val : ℝ) + 1) * ((p i) ^ 2 - (zeroExtend p (i.val + 1)) ^ 2)) =
      ∑ i, (p i) ^ 2 := by
  calc
    _ = ∑ i, ((i.val : ℝ) + 1) * difference (fun j => (p j) ^ 2) i := by
      apply Finset.sum_congr rfl
      intro i _
      change ((i.val : ℝ) + 1) * ((p i) ^ 2 - (zeroExtend p (i.val + 1)) ^ 2) =
        ((i.val : ℝ) + 1) * ((p i) ^ 2 - zeroExtend (fun j => (p j) ^ 2) (i.val + 1))
      exact congrArg (fun z => ((i.val : ℝ) + 1) * ((p i) ^ 2 - z))
        (zeroExtend_pointwise_sq p (i.val + 1)).symm
    _ = _ := weighted_differences_sum (fun i => (p i) ^ 2)

theorem weighted_difference_product_bound {N : ℕ} (p : Vec N)
    (hp : ∀ i, 0 ≤ p i) (hdiff : ∀ i, 0 ≤ difference p i) :
    (∑ i, ((i.val : ℝ) + 1) * difference p i * p i) ≤ ∑ i, (p i) ^ 2 := by
  rw [← weighted_square_differences_sum]
  apply Finset.sum_le_sum
  intro i _
  have hn : 0 ≤ zeroExtend p (i.val + 1) := by
    by_cases hi : i.val + 1 < N
    · simpa only [zeroExtend, dif_pos hi] using hp ⟨i.val + 1, hi⟩
    · simp [zeroExtend, hi]
  have hv : difference p i * p i ≤ (p i) ^ 2 - (zeroExtend p (i.val + 1)) ^ 2 := by
    have hm := mul_nonneg (hdiff i) hn
    unfold difference at hm ⊢
    nlinarith only [hm]
  have hc : 0 ≤ (i.val : ℝ) + 1 := by positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hv hc

theorem trialVector_differences_nonnegative (N : ℕ) (t : ℝ) (ht : 1 ≤ t) :
    ∀ i, 0 ≤ difference (trialVector N t) i := by
  intro i
  unfold difference
  by_cases hi : i.val + 1 < N
  · rw [zeroExtend, dif_pos hi]
    apply sub_nonneg.mpr
    exact trialVector_antitone N t ht (show i ≤ (⟨i.val + 1, hi⟩ : Fin N) by change i.val ≤ i.val + 1; omega)
  · simp only [zeroExtend, dif_neg hi, sub_zero]
    exact (trialVector_positive N t ht i).le

theorem scalar_J_perturbation_bound (a t j p w : ℝ) (ha : 0 ≤ a) (ht : 1 ≤ t)
    (hj : 0 < j) (hp : 0 ≤ p) (hw0 : 0 ≤ w - p) (hw : w - p ≤ (j - 1) * p) :
    0 ≤ a * (w - p) / (j * (j + a)) + (t - 1) * p / (j + a) ∧
      a * (w - p) / (j * (j + a)) + (t - 1) * p / (j + a) ≤ (a + t - 1) * p / j := by
  have hja : 0 < j + a := add_pos_of_pos_of_nonneg hj ha
  have ht1 : 0 ≤ t - 1 := sub_nonneg.mpr ht
  constructor
  · exact add_nonneg (div_nonneg (mul_nonneg ha hw0) (mul_pos hj hja).le)
      (div_nonneg (mul_nonneg ht1 hp) hja.le)
  · have hwp : w - p ≤ (j + a) * p :=
      hw.trans (mul_le_mul_of_nonneg_right (by linarith : j - 1 ≤ j + a) hp)
    have hA : a * (w - p) / (j * (j + a)) ≤ a * p / j := by
      apply (div_le_iff₀ (mul_pos hj hja)).mpr
      rw [show a * p / j * (j * (j + a)) = a * p * (j + a) by
        field_simp [ne_of_gt hj] <;> ring]
      nlinarith only [mul_le_mul_of_nonneg_left hwp ha]
    have hB : (t - 1) * p / (j + a) ≤ (t - 1) * p / j := by
      apply (div_le_div_iff₀ hja hj).mpr
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ha) (mul_nonneg ht1 hp)
    calc
      _ ≤ a * p / j + (t - 1) * p / j := add_le_add hA hB
      _ = _ := by ring

/-- The J perturbation bound for the actual trial vector, as in the document. -/
theorem trial_J_parameter_difference_bound (N : ℕ) (a t : ℝ) (ha : 0 ≤ a) (ht : 1 ≤ t) :
    |trialEnergyJ a t (trialVector N t) - trialEnergyJ 0 1 (trialVector N t)| ≤
      (a + t - 1) * ∑ i, ((i.val : ℝ) + 1) * difference (trialVector N t) i *
        trialVector N t i / ((N : ℝ) - i.val) := by
  let v := trialVector N t
  let γ : Vec N := fun i => ((i.val : ℝ) + 1) * difference v i
  let τ : Vec N := fun i => a * (tail v i.val - v i) /
      (((N : ℝ) - i.val) * (((N : ℝ) - i.val) + a)) +
        (t - 1) * v i / (((N : ℝ) - i.val) + a)
  have hγ : ∀ i, 0 ≤ γ i := by
    intro i
    exact mul_nonneg (by positivity) (trialVector_differences_nonnegative N t ht i)
  have hτ : ∀ i, 0 ≤ τ i ∧ τ i ≤ (a + t - 1) * v i / ((N : ℝ) - i.val) := by
    intro i
    have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
    have hw := trial_tail_bounds N t ht i
    rw [Nat.cast_sub (Nat.le_of_lt i.isLt)] at hw
    exact scalar_J_perturbation_bound a t ((N : ℝ) - i.val) (v i) (tail v i.val)
      ha ht (sub_pos.mpr hi) (trialVector_positive N t ht i).le hw.1 hw.2
  have hden : ∀ i : Fin N, (N : ℝ) + a - i.val = ((N : ℝ) - i.val) + a := fun _ => by ring
  have hid := trialEnergyJ_parameter_difference a t ha v
  simp_rw [hden] at hid
  change trialEnergyJ a t v - trialEnergyJ 0 1 v = -(∑ i, γ i * τ i) at hid
  rw [hid, abs_neg, abs_of_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hγ i) (hτ i).1))]
  calc
    _ ≤ ∑ i, γ i * ((a + t - 1) * v i / ((N : ℝ) - i.val)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hτ i).2 (hγ i))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [γ, v]
      ring

theorem trial_baseline_J_upper (N : ℕ) (t : ℝ) (hN : 0 < N) (ht : 1 ≤ t) :
    trialEnergyJ 0 1 (trialVector N t) ≤ (trialNormalization N t) ^ 2 / (2 * ((N : ℝ) + 1)) := by
  have hp : trialVector N t ≠ 0 := by
    intro he
    exact (ne_of_gt (trialVector_positive N t ht ⟨0, hN⟩)) (congrFun he ⟨0, hN⟩)
  have hE := (homogeneousEnergy_positive N 0 1 hN (by norm_num) (by norm_num)
    (trialVector N t) hp).le
  rw [homogeneousEnergy_eq_trialEnergyJ] at hE
  simp only [energyF, add_zero] at hE
  apply (le_div_iff₀ (by positivity : 0 < 2 * ((N : ℝ) + 1))).mpr
  change trialEnergyJ 0 1 (trialVector N t) * (2 * ((N : ℝ) + 1)) ≤
    (∑ i, trialVector N t i) ^ 2
  nlinarith only [hE]

end
end CriticalExtrapolation.Paper
