import PaperFramework.RecoveredInterpolation
import PaperFramework.FirstOrderConvex
import PaperFramework.QuadraticActual
import PaperFramework.ForwardNonnegativity

namespace CriticalExtrapolation.Paper
noncomputable section

def envelopeCoefficient (N : ℕ) (h c : ℝ) (j : Fin (N + 1)) : ℝ :=
  if j.val < N then 1 - (j.val : ℝ) * h / S N h c else 1 / S N h c

def flatEnvelopeSample (N : ℕ) (h c : ℝ) : Sample N 1 :=
  let xs : Query N → Space 1 := fun q => match q with
    | none => 0
    | some j => envelopeCoefficient N h c j • unitOne
  let gs : Query N → Space 1 := fun q => match q with
    | none => 0
    | some _ => (1 / S N h c) • unitOne
  { x := xs, g := gs, value := fun q => inner ℝ (gs q) (xs q) - ‖gs q‖ ^ 2 / 2 }

theorem envelopeCoefficient_lower (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (j : Fin (N + 1)) : 1 / S N h c ≤ envelopeCoefficient N h c j := by
  have hS := S_positive N h c hp
  unfold envelopeCoefficient
  split_ifs with hj
  · have hjR : (j.val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt hj)
    have hNC : (j.val : ℝ) ≤ (N : ℝ) * c :=
      hjR.trans (le_mul_of_one_le_right (Nat.cast_nonneg N) hp.c_ge_one)
    have hnum : 1 ≤ S N h c - (j.val : ℝ) * h := by
      unfold S
      nlinarith [mul_nonneg hp.h_pos.le (sub_nonneg.mpr hNC)]
    have hid : 1 - (j.val : ℝ) * h / S N h c =
        (S N h c - (j.val : ℝ) * h) / S N h c := by field_simp [hS.ne']
    rw [hid]
    exact div_le_div_of_nonneg_right hnum hS.le
  · exact le_rfl

theorem flatEnvelope_all_slacks (N : ℕ) (h c : ℝ) (hp : Parameters N h c) :
    ∀ i j, 0 ≤ slack (flatEnvelopeSample N h c) i j := by
  have he : inner ℝ unitOne unitOne = 1 := by
    rw [real_inner_self_eq_norm_sq, unitOne_norm]
    norm_num
  have hvalue : ∀ i, (flatEnvelopeSample N h c).value i =
      inner ℝ ((flatEnvelopeSample N h c).g i) ((flatEnvelopeSample N h c).x i) -
        ‖(flatEnvelopeSample N h c).g i‖ ^ 2 / 2 := fun _ => rfl
  intro i j
  rw [special_value_slack_identity (flatEnvelopeSample N h c) hvalue]
  cases i with
  | none => cases j <;> simp [flatEnvelopeSample]
  | some i =>
    cases j with
    | none =>
      change 0 ≤ inner ℝ ((1 / S N h c) • unitOne - 0)
        (envelopeCoefficient N h c i • unitOne - (1 / S N h c) • unitOne)
      simp only [sub_zero, ← sub_smul, real_inner_smul_left, real_inner_smul_right, he, mul_one]
      exact mul_nonneg (sub_nonneg.mpr (envelopeCoefficient_lower N h c hp i))
        (one_div_pos.mpr (S_positive N h c hp)).le
    | some j => simp [flatEnvelopeSample]

theorem flatEnvelope_global_recovery (N : ℕ) (h c : ℝ) (hp : Parameters N h c) :
    let data := flatEnvelopeSample N h c
    SmoothConvexOne (recoveredFunction data) ∧ Interpolates data (recoveredFunction data) ∧
      ∀ x, recoveredFunction data 0 ≤ recoveredFunction data x := by
  let data := flatEnvelopeSample N h c
  have hsmooth := (recovered_function_global_smoothness_proved data).1
  have hvalue : ∀ i, data.value i = inner ℝ (data.g i) (data.x i) - ‖data.g i‖ ^ 2 / 2 :=
    fun _ => rfl
  have hinterp := recovered_function_interpolates_proved data hvalue (flatEnvelope_all_slacks N h c hp)
  refine ⟨hsmooth, hinterp, ?_⟩
  have hgrad0 : gradient (recoveredFunction data) 0 = 0 := hinterp.2 (starQuery N)
  intro x
  have hs := convex_gradient_support (recoveredFunction data) hsmooth.1 hsmooth.2.1 0 x
  simpa only [hgrad0, inner_zero_left, add_zero] using hs

end
end CriticalExtrapolation.Paper
