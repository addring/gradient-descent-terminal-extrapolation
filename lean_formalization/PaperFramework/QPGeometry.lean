import PaperFramework.Definitions
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Function

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem continuous_difference {N : ℕ} (i : Fin N) :
    Continuous (fun β : Vec N => difference β i) := by
  unfold difference zeroExtend
  split_ifs <;> fun_prop

theorem continuous_applyT {N : ℕ} (h c : ℝ) (i : Fin N) :
    Continuous (fun β : Vec N => applyT h c β i) := by
  unfold applyT
  fun_prop

theorem continuous_slope {N : ℕ} (h c : ℝ) (i : Fin N) :
    Continuous (fun β : Vec N => slope h c β i) :=
  (continuous_applyT h c i).div_const _

theorem continuous_chainObjective (N : ℕ) (h c : ℝ) :
    Continuous (chainObjective (N := N) h c) := by
  unfold chainObjective
  apply Continuous.sub
  · fun_prop
  · apply Continuous.mul continuous_const
    apply continuous_finset_sum
    intro i _
    exact (continuous_const.mul (continuous_difference i)).mul (continuous_slope h c i)

theorem nonnegative_of_differences {N : ℕ} (β : Vec N)
    (hd : ∀ i, 0 ≤ difference β i) : ∀ i, 0 ≤ β i := by
  cases N with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    intro i
    induction i using Fin.reverseInduction with
    | last => simpa [difference, zeroExtend] using hd (Fin.last n)
    | cast i ih =>
      have hi := hd i.castSucc
      have hext : zeroExtend β (i.castSucc.val + 1) = β i.succ := by
        simp [zeroExtend, Nat.succ_lt_succ i.isLt]
        rfl
      rw [difference, hext] at hi
      linarith

theorem feasible_coordinate_bounds {N : ℕ} (h c : ℝ) (β : Vec N)
    (hβ : Feasible h c β) (i : Fin N) : 0 ≤ β i ∧ β i ≤ 1 := by
  have hnonneg := nonnegative_of_differences β hβ.2.1
  refine ⟨hnonneg i, ?_⟩
  calc β i ≤ ∑ j, β j := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
       _ = 1 := hβ.1

theorem feasible_set_closed (N : ℕ) (h c : ℝ) :
    IsClosed {β : Vec N | Feasible h c β} := by
  have hnorm : IsClosed {β : Vec N | (∑ i, β i) = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hd : IsClosed {β : Vec N | ∀ i, 0 ≤ difference β i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_difference i))
  have hs : IsClosed {β : Vec N | ∀ i j : Fin N, i.val + 1 = j.val →
      slope h c β j ≤ slope h c β i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter
      (fun _ => isClosed_le (continuous_slope h c j) (continuous_slope h c i))))
  exact hnorm.inter (hd.inter hs)

theorem feasible_set_compact (N : ℕ) (h c : ℝ) (hp : Parameters N h c) :
    IsCompact {β : Vec N | Feasible h c β} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : Vec N) 1)).of_isClosed_subset
    (feasible_set_closed N h c)
  intro β hβ
  exact ⟨fun i => (feasible_coordinate_bounds h c β hβ i).1,
    fun i => (feasible_coordinate_bounds h c β hβ i).2⟩

theorem difference_mix {N : ℕ} (x y : Vec N) (a b : ℝ) (i : Fin N) :
    difference (a • x + b • y) i = a * difference x i + b * difference y i := by
  unfold difference zeroExtend
  split_ifs <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem slope_mix {N : ℕ} (h c : ℝ) (x y : Vec N) (a b : ℝ) (i : Fin N) :
    slope h c (a • x + b • y) i = a * slope h c x i + b * slope h c y i := by
  unfold slope applyT
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

theorem feasible_set_convex (N : ℕ) (h c : ℝ) : Convex ℝ {β : Vec N | Feasible h c β} := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · change (∑ i, (a * x i + b * y i)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.1, hy.1]
    simpa only [mul_one] using hab
  · intro i
    rw [difference_mix]
    exact add_nonneg (mul_nonneg ha (hx.2.1 i)) (mul_nonneg hb (hy.2.1 i))
  · intro i j hij
    rw [slope_mix, slope_mix]
    exact add_le_add (mul_le_mul_of_nonneg_left (hx.2.2 i j hij) ha)
      (mul_le_mul_of_nonneg_left (hy.2.2 i j hij) hb)

end
end CriticalExtrapolation.Paper
