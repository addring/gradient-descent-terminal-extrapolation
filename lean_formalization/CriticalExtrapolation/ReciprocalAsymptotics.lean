import CriticalExtrapolation.ReciprocalSums
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Asymptotics.Defs

namespace CriticalExtrapolation

open Filter Asymptotics

theorem harmonicSum_eq_harmonic (N : ℕ) : harmonicSum N = (harmonic N : ℝ) := by
  simp [harmonicSum, harmonic, Nat.cast_add, Nat.cast_one, one_div]

theorem harmonicSum_log_error (N : ℕ) (hN : 1 ≤ N) :
    |harmonicSum N - Real.log (N : ℝ)| ≤ 1 := by
  rw [harmonicSum_eq_harmonic]
  have hpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog : Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_le_log hpos (by norm_cast; omega)
  have hlower := log_add_one_le_harmonic N
  have hupper := harmonic_le_one_add_log N
  apply abs_le.mpr
  constructor <;> linarith

/-- A concrete all-N bound proving (7.4) for the true corrected weights. -/
theorem referenceReciprocalSum_log_error (N : ℕ) (hN : 2 ≤ N) :
    |referenceReciprocalSum N - Real.log (N : ℝ)| < 9 := by
  have hR := referenceReciprocalSum_error N hN
  have hH := harmonicSum_log_error N (by omega)
  have htriangle := abs_add_le (referenceReciprocalSum N - harmonicSum N)
    (harmonicSum N - Real.log (N : ℝ))
  have hid : referenceReciprocalSum N - harmonicSum N +
      (harmonicSum N - Real.log (N : ℝ)) = referenceReciprocalSum N - Real.log (N : ℝ) := by
    ring
  rw [hid] at htriangle
  linarith

/-- The paper's R⁰_N = log N + O(1), in mathlib's Landau notation. -/
theorem referenceReciprocalSum_sub_log_isBigO :
    (fun N : ℕ => referenceReciprocalSum N - Real.log (N : ℝ)) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 9
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  simpa only [Real.norm_eq_abs, norm_one, mul_one] using
    le_of_lt (referenceReciprocalSum_log_error N hN)

end CriticalExtrapolation
