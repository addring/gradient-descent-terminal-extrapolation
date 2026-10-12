import PaperFramework.QuadraticProgramKKT
import PaperFramework.FeasiblePositivity
import Mathlib.Data.Finset.Max

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- On a constant direction block, complementarity kills the slope multipliers. -/
theorem slope_multiplier_zero_of_equal_coordinates (N : ℕ) (h c : ℝ)
    (hp : Parameters N h c) (hh : h < 1) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν)
    (k : Fin (N - 1)) (hk : β (slopeLeft k) = β (slopeRight k)) : μ k = 0 := by
  have hd : difference β (slopeLeft k) = 0 := by
    rw [difference_adjacent β (slopeLeft k) (slopeRight k) rfl, hk, sub_self]
  have hs := slope_strict_of_zero_difference N h c hp hh β hkkt.feasible
    (slopeLeft k) (slopeRight k) rfl hd
  exact (mul_eq_zero.mp (hkkt.slope_complementarity k)).resolve_right
    (ne_of_gt (sub_pos.mpr hs))

/-- The terminal difference multiplier vanishes before strict ordering is known. -/
theorem terminal_difference_multiplier_zero (N : ℕ) (h c : ℝ)
    (hp : Parameters N h c) (hh : h < 1) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν)
    (b : Fin N) (hb : b.val + 1 = N) : ν b = 0 := by
  have hd : difference β b = β b := by simp [difference, zeroExtend, hb]
  have hc := hkkt.difference_complementarity b
  rw [hd] at hc
  exact (mul_eq_zero.mp hc).resolve_right
    (ne_of_gt (feasible_terminal_positive N h c hp hh β hkkt.feasible b hb))

/-- A finite nonnegative sequence with zero endpoints has an interior point
with nonnegative discrete second difference. The index shift also covers a
zero multiplier to the left of coordinate zero. -/
theorem finite_discrete_maximum (f : ℕ → ℝ) (a b : ℕ) (hab : a + 1 < b)
    (ha : f a = 0) (hb : f b = 0)
    (hnonneg : ∀ i, a < i → i < b → 0 ≤ f i) :
    ∃ i, a < i ∧ i < b ∧ 0 ≤ 2 * f i - f (i - 1) - f (i + 1) := by
  classical
  let s := Finset.Ioo a b
  have hs : s.Nonempty := ⟨a + 1, by simp [s]; omega⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s f hs
  have hi' : a < i ∧ i < b := by simpa [s] using hi
  have hfi := hnonneg i hi'.1 hi'.2
  have hleft : f (i - 1) ≤ f i := by
    by_cases hia : i - 1 = a
    · simpa [hia, ha] using hfi
    · exact hmax (i - 1) (by simp [s]; omega)
  have hright : f (i + 1) ≤ f i := by
    by_cases hib : i + 1 = b
    · simpa [hib, hb] using hfi
    · exact hmax (i + 1) (by simp [s]; omega)
  exact ⟨i, hi'.1, hi'.2, by linarith⟩

end
end CriticalExtrapolation.Paper
