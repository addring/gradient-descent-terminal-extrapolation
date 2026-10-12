import PaperFramework.InstanceBounds
import PaperFramework.WorstScaling
import PaperFramework.FlatEnvelopeAttainment
import PaperFramework.RadiusInstance

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

/-- Section 1: actual instance supremum is well-defined for positive scales. -/
theorem instance_values_nonempty_bounded (N : ℕ) (h c L D : ℝ)
    (hL : 0 < L) (hD : 0 < D) :
    ({r : ℝ | ∃ (d : ℕ) (I : Instance d L D),
      r = ‖gradient I.f (output I N h c)‖}).Nonempty ∧
    BddAbove {r : ℝ | ∃ (d : ℕ) (I : Instance d L D),
      r = ‖gradient I.f (output I N h c)‖} := by
  exact actual_instance_values_nonempty_bounded N h c L D hL hD

/-- (1.5): a global instance realizing the Huber finite trajectory attains the proposed value.
The recovery extension used here is recorded in FORMALIZATION_NOTES.md. -/
theorem huber_attainment (N : ℕ) (h c L D : ℝ)
    (hp : Parameters N h c) (hL : 0 < L) (hD : 0 < D) :
    ∃ I : Instance 1 L D, ‖gradient I.f (output I N h c)‖ = L * D / S N h c := by
  exact envelope_attainment_by_flat_recovery N h c L D hp hL hD

theorem huber_lower_bound (N : ℕ) (h c L D : ℝ)
    (hp : Parameters N h c) (hL : 0 < L) (hD : 0 < D) :
    L * D / S N h c ≤ worstGradient N h c L D := by
  obtain ⟨I, hI⟩ := huber_attainment N h c L D hp hL hD
  have hbounded := (instance_values_nonempty_bounded N h c L D hL hD).2
  rw [← hI]
  exact le_csSup hbounded ⟨1, I, rfl⟩

theorem worstGradient_scaling (N : ℕ) (h c L D : ℝ)
    (hp : Parameters N h c) (hL : 0 < L) (hD : 0 < D) :
    worstGradient N h c L D = L * D * worstGradient N h c 1 1 := by
  exact worstGradient_scaling_proved N h c L D hL hD

/-- The initial radius equality and inequality give the same dimension-independent supremum. -/
theorem radius_equality_embedding {d : ℕ} {L D : ℝ}
    (I : Instance d L D) (hL : 0 < L) (hD : 0 < D) :
    ∃ J : Instance (d + 1) L D, ‖J.initial - J.minimizer‖ = D ∧
      ∀ N h c, ‖gradient J.f (output J N h c)‖ = ‖gradient I.f (output I N h c)‖ := by
  exact radius_equality_embedding_proved I hL hD

end
end CriticalExtrapolation.Paper
