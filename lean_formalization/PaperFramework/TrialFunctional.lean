import PaperFramework.ShiftedEnergy
import PaperFramework.TrialSlopeScalar
import PaperFramework.TrialRightScalar

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- The linear expression L_i(v) in the paper's strict slope proof. -/
def trialSlopeFunctional {N : ℕ} (a t : ℝ) (v : Vec N) (i : Fin N) : ℝ :=
  (energyD N a i.val + t) * v i - tail v i.val - t * energyD N a i.val * difference v i

theorem trialSlopeFunctional_add {N : ℕ} (a t : ℝ) (v w : Vec N) (i : Fin N) :
    trialSlopeFunctional a t (v + w) i = trialSlopeFunctional a t v i + trialSlopeFunctional a t w i := by
  unfold trialSlopeFunctional difference tail zeroExtend
  split_ifs <;> simp only [Pi.add_apply, Finset.sum_add_distrib] <;> ring

theorem trialSlopeFunctional_smul {N : ℕ} (a t r : ℝ) (v : Vec N) (i : Fin N) :
    trialSlopeFunctional a t (r • v) i = r * trialSlopeFunctional a t v i := by
  unfold trialSlopeFunctional difference tail zeroExtend
  split_ifs <;> simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] <;> ring

theorem trialSlopeFunctional_normalized (N : ℕ) (a t : ℝ) (i : Fin N) :
    trialSlopeFunctional a t (normalizedTrial N t) i =
      trialSlopeFunctional a t (trialVector N t) i / trialNormalization N t := by
  have heq : normalizedTrial N t = (1 / trialNormalization N t) • trialVector N t := by
    funext k
    simp [normalizedTrial, div_eq_mul_inv, mul_comm]
  rw [heq, trialSlopeFunctional_smul]
  ring

theorem trialSlopeFunctional_gap {N : ℕ} (a t : ℝ) (ha : 0 ≤ a)
    (v : Vec N) (i j : Fin N) (hij : i.val + 1 = j.val) :
    energyD N a i.val * energyD N a j.val *
      ((tail v i.val - t * v i) / energyD N a i.val -
        (tail v j.val - t * v j) / energyD N a j.val) = trialSlopeFunctional a t v i := by
  have hi := ne_of_gt (energyD_pos N a ha i)
  have hj := ne_of_gt (energyD_pos N a ha j)
  have htail := tail_step v i
  rw [hij] at htail
  have hjR : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij.symm
  unfold trialSlopeFunctional
  rw [difference_adjacent v i j hij, htail]
  field_simp [hi, hj]
  unfold energyD
  rw [hjR]
  ring

theorem shifted_slopes_strict_of_functional (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (p : Vec N) (hpsum : (∑ k, p k) = 1) (i j : Fin N) (hij : i.val + 1 = j.val)
    (hfun : 0 < trialSlopeFunctional ((N : ℝ) * (c - 1)) (1 / h) p i) :
    slope h c (shiftedDirection ((N : ℝ) * (c - 1)) (1 / h) p) j <
      slope h c (shiftedDirection ((N : ℝ) * (c - 1)) (1 / h) p) i := by
  let a : ℝ := (N : ℝ) * (c - 1)
  let t : ℝ := 1 / h
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hp.c_ge_one)
  have ht : 0 < t := one_div_pos.mpr hp.h_pos
  have hm : 0 < shiftMass a t := div_pos ht (add_pos_of_nonneg_of_pos ha ht)
  have hgap := trialSlopeFunctional_gap a t ha p i j hij
  have hprod : 0 < energyD N a i.val * energyD N a j.val *
      ((tail p i.val - t * p i) / energyD N a i.val -
        (tail p j.val - t * p j) / energyD N a j.val) := by
    rw [hgap]
    exact hfun
  have hratio : (tail p j.val - t * p j) / energyD N a j.val <
      (tail p i.val - t * p i) / energyD N a i.val := by
    have hx := (mul_pos_iff_of_pos_left (mul_pos (energyD_pos N a ha i) (energyD_pos N a ha j))).mp hprod
    linarith
  simp_rw [shifted_direction_slope N h c hp p hpsum]
  simp only [mul_div_assoc]
  change shiftB N a t + shiftMass a t * ((tail p j.val - t * p j) / energyD N a j.val) <
    shiftB N a t + shiftMass a t * ((tail p i.val - t * p i) / energyD N a i.val)
  exact add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left hratio hm)

end
end CriticalExtrapolation.Paper
