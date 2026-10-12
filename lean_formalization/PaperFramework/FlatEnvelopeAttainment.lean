import PaperFramework.FlatEnvelopeData
import PaperFramework.WorstScaling

namespace CriticalExtrapolation.Paper
noncomputable section

theorem flatEnvelope_iterate {N : ℕ} (I : Instance 1 1 1) (h c : ℝ)
    (hinit : I.initial = unitOne) (hinterp : Interpolates (flatEnvelopeSample N h c) I.f) :
    ∀ n, n ≤ N → iterate I h n = (1 - (n : ℝ) * h / S N h c) • unitOne := by
  intro n
  induction n with
  | zero => intro _; simpa only [iterate, Nat.cast_zero, zero_mul, zero_div, sub_zero, one_smul] using hinit
  | succ n ih =>
    intro hn
    have hnlt : n < N := by omega
    have hprev := ih (by omega)
    have hg : gradient I.f (iterate I h n) = (1 / S N h c) • unitOne := by
      rw [hprev]
      have hs := hinterp.2 (ordinaryQuery (⟨n, hnlt⟩ : Fin N))
      simpa [flatEnvelopeSample, envelopeCoefficient, ordinaryQuery, hnlt] using hs
    rw [iterate, div_one, hg, hprev]
    simp only [Nat.cast_succ, Nat.cast_add, Nat.cast_one]
    module

theorem flatEnvelope_output {N : ℕ} (I : Instance 1 1 1) (h c : ℝ)
    (hp : Parameters N h c) (hinit : I.initial = unitOne)
    (hinterp : Interpolates (flatEnvelopeSample N h c) I.f) :
    output I N h c = (1 / S N h c) • unitOne := by
  have hcoeff : 1 - c * ((N : ℝ) * h / S N h c) = 1 / S N h c := by
    have hS := (S_positive N h c hp).ne'
    field_simp [hS] <;> unfold S <;> ring
  rw [output, flatEnvelope_iterate I h c hinit hinterp N le_rfl, hinit]
  calc
    _ = (1 - c * ((N : ℝ) * h / S N h c)) • unitOne := by module
    _ = _ := by rw [hcoeff]

/-- The global recovery agrees with the paper's constant-gradient Huber trajectory. -/
theorem flatEnvelope_attainment_unit (N : ℕ) (h c : ℝ) (hp : Parameters N h c) :
    ∃ I : Instance 1 1 1, ‖gradient I.f (output I N h c)‖ = 1 / S N h c := by
  obtain ⟨hsmooth, hinterp, hmin⟩ := flatEnvelope_global_recovery N h c hp
  let I : Instance 1 1 1 := {
    f := recoveredFunction (flatEnvelopeSample N h c)
    convex := hsmooth.1
    differentiable := hsmooth.2.1
    gradient_lipschitz := by intro x z; simpa only [one_mul] using hsmooth.2.2 x z
    initial := unitOne
    minimizer := 0
    minimizes := hmin
    radius := by rw [sub_zero, unitOne_norm] }
  have hout := flatEnvelope_output I h c hp rfl hinterp
  have hg : gradient I.f (output I N h c) = (1 / S N h c) • unitOne := by
    rw [hout]
    have hs := hinterp.2 (outputQuery N)
    simpa [I, flatEnvelopeSample, envelopeCoefficient, outputQuery] using hs
  refine ⟨I, ?_⟩
  rw [hg, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (S_positive N h c hp)),
    unitOne_norm, mul_one]

theorem envelope_attainment_by_flat_recovery (N : ℕ) (h c L D : ℝ)
    (hp : Parameters N h c) (hL : 0 < L) (hD : 0 < D) :
    ∃ I : Instance 1 L D, ‖gradient I.f (output I N h c)‖ = L * D / S N h c := by
  obtain ⟨J, hJ⟩ := flatEnvelope_attainment_unit N h c hp
  obtain ⟨I, hI⟩ := actual_value_scaling J L D hL hD N h c
  refine ⟨I, ?_⟩
  rw [hI, hJ]
  simp only [div_eq_mul_inv, one_mul, mul_assoc]

end
end CriticalExtrapolation.Paper
