import PaperFramework.NegativeAlgebra
import Mathlib.Order.Fin.Basic

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def negativeLeading {N : ℕ} (h c : ℝ) (β : Vec N) (i : Fin N) (j : ℕ) : ℝ :=
  backwardA h c β i - zeroExtend (backwardA h c β) j +
    slope h c β i * (β i - zeroExtend β j)

theorem strict_feasible_slopes_strictAnti {N : ℕ} (h c : ℝ) (β : Vec N)
    (hβ : StrictlyFeasible h c β) : StrictAnti (slope h c β) := by
  cases N with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    exact hβ.2.2 i.castSucc i.succ rfl

theorem negativeLeading_self {N : ℕ} (h c : ℝ) (β : Vec N) (i : Fin N) :
    negativeLeading h c β i i.val = 0 := by
  simp [negativeLeading, zeroExtend, i.isLt]

theorem negativeLeading_adjacent {N : ℕ} (h c : ℝ) (β : Vec N) (i : Fin N) :
    negativeLeading h c β i (i.val + 1) = 0 := by
  have hA := (backward_recursions h c β i).1
  change difference (backwardA h c β) i + slope h c β i * difference β i = 0
  rw [hA]
  ring

theorem negativeLeading_step {N : ℕ} (h c : ℝ) (β : Vec N) (i k : Fin N) :
    negativeLeading h c β i (k.val + 1) - negativeLeading h c β i k.val =
      difference β k * (slope h c β i - slope h c β k) := by
  have hA := (backward_recursions h c β k).1
  simp only [negativeLeading, difference, zeroExtend, dif_pos k.isLt] at hA ⊢
  linear_combination hA

/-- The output index is permitted, but each slope used by the induction is ordinary. -/
theorem negativeLeading_forward_strict {N : ℕ} (h c : ℝ) (β : Vec N)
    (hβ : StrictlyFeasible h c β) (i : Fin N) (j : ℕ)
    (hij : i.val + 1 < j) (hj : j ≤ N) : 0 < negativeLeading h c β i j := by
  have hanti := strict_feasible_slopes_strictAnti h c β hβ
  have hall : ∀ k : ℕ, i.val + 1 ≤ k → k ≤ N →
      0 ≤ negativeLeading h c β i k ∧
        (i.val + 1 < k → 0 < negativeLeading h c β i k) := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro hk hkN
      by_cases heq : k + 1 = i.val + 1
      · rw [heq, negativeLeading_adjacent]
        exact ⟨le_rfl, by omega⟩
      · have hklo : i.val + 1 ≤ k := by omega
        have hklt : k < N := by omega
        have hprev := (ih hklo (by omega)).1
        have hs : slope h c β ⟨k, hklt⟩ < slope h c β i :=
          hanti (show i < ⟨k, hklt⟩ by change i.val < k; omega)
        have hinc := mul_pos (hβ.2.1 ⟨k, hklt⟩) (sub_pos.mpr hs)
        have hstep := negativeLeading_step h c β i ⟨k, hklt⟩
        simp only [Fin.val_mk] at hstep
        have hpos : 0 < negativeLeading h c β i (k + 1) := by linarith
        exact ⟨hpos.le, fun _ => hpos⟩
  exact (hall j (by omega) hj).2 hij

end
end CriticalExtrapolation.Paper
