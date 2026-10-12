import PaperFramework.NegativeLeading
import Mathlib.Order.Interval.Set.Monotone

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem negativeLeading_backward_strict {N : ℕ} (h c : ℝ) (β : Vec N)
    (hβ : StrictlyFeasible h c β) (i : Fin N) (j : ℕ)
    (hji : j < i.val) : 0 < negativeLeading h c β i j := by
  have hanti := strict_feasible_slopes_strictAnti h c β hβ
  have hstep : ∀ k : ℕ, k < i.val →
      negativeLeading h c β i (k + 1) < negativeLeading h c β i k := by
    intro k hk
    have hkN : k < N := by omega
    have hs : slope h c β i < slope h c β ⟨k, hkN⟩ :=
      hanti (show (⟨k, hkN⟩ : Fin N) < i from hk)
    have hnegative := mul_neg_of_pos_of_neg (hβ.2.1 ⟨k, hkN⟩) (sub_neg.mpr hs)
    have hid := negativeLeading_step h c β i ⟨k, hkN⟩
    simp only [Fin.val_mk] at hid
    linarith
  have hmono : StrictAntiOn (negativeLeading h c β i) (Set.Iic i.val) :=
    strictAntiOn_Iic_of_succ_lt (fun k hk => by
      change negativeLeading h c β i (k + 1) < negativeLeading h c β i k
      exact hstep k hk)
  have hs := hmono (show j ∈ Set.Iic i.val from hji.le)
    (show i.val ∈ Set.Iic i.val from Nat.le_refl i.val) hji
  rwa [negativeLeading_self] at hs

end
end CriticalExtrapolation.Paper
