import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace CriticalExtrapolation

/-- Diagonal entry identity in (3.6), with ζ=d+t and F=ζ+i. -/
theorem tridiagonal_diagonal_split (d t i : ℝ)
    (hd : d ≠ 0) (hF : d + t + i ≠ 0) :
    2 * t * (i + 1) * (d + t) * (d + t - 1) / (d * (d + t + i)) - 1 =
      (2 * i + 1 - 2 * i * (i + 1) / (d + t + i)) +
        (t - 1) / (d + t + i) * (2 * (i + 1) * (d + t) ^ 2 / d) := by
  field_simp
  ring

/-- Neighbor entry identity in (3.6). -/
theorem tridiagonal_neighbor_split (d t i : ℝ) :
    -((t - 1) * (i + 1) * (d + t) * (d + t - 2) / (d * (d + t + i))) =
      (t - 1) / (d + t + i) * (-((i + 1) * (d + t) * (d + t - 2) / d)) := by
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The strict scalar row lower bound (3.7), valid at the boundary rows as well. -/
theorem tridiagonal_row_lower_pos {d ζ i : ℝ}
    (hd : 0 < d) (hζ : 2 ≤ ζ) (hi : 0 ≤ i) :
    0 < (i + 1) * ζ * (ζ + 2) / d - i * (ζ ^ 2 - 1) / (d + 1) := by
  have hd1 : 0 < d + 1 := by linarith
  have hA : 0 < ζ * (ζ + 2) / d :=
    div_pos (mul_pos (by linarith) (by linarith)) hd
  have hAB : (ζ ^ 2 - 1) / (d + 1) < ζ * (ζ + 2) / d := by
    apply (div_lt_div_iff₀ hd1 hd).mpr
    have hp : 0 < 2 * ζ * d := mul_pos (by linarith) hd
    nlinarith [sq_nonneg ζ]
  have hmul : 0 ≤ i * (ζ * (ζ + 2) / d - (ζ ^ 2 - 1) / (d + 1)) :=
    mul_nonneg hi (by linarith)
  have heq : (i + 1) * ζ * (ζ + 2) / d - i * (ζ ^ 2 - 1) / (d + 1) =
      ζ * (ζ + 2) / d + i * (ζ * (ζ + 2) / d - (ζ ^ 2 - 1) / (d + 1)) := by
    ring
  rw [heq]
  linarith

end CriticalExtrapolation
