import PaperFramework.ProblemAndHuber
import PaperFramework.SmoothDescent
import PaperFramework.FullRecoveredInterpolation

namespace CriticalExtrapolation.Paper
noncomputable section

/-- (2.1): smooth convex interpolation is necessary for all directed pairs. -/
theorem smooth_convex_interpolation_necessary {d : ℕ} (f : Space d → ℝ)
    (hf : SmoothConvexOne f) (x z : Space d) :
    0 ≤ f x - f z - inner ℝ (gradient f z) (x - z) -
      ‖gradient f x - gradient f z‖ ^ 2 / 2 := by
  exact smooth_convex_interpolation_necessary_proved f hf x z

/-- General finite interpolation sufficiency, including a global function on all of Space d. -/
theorem smooth_convex_interpolation_sufficient {N d : ℕ} (data : Sample N d)
    (hdata : ∀ i j, 0 ≤ slack data i j) :
    ∃ f : Space d → ℝ, SmoothConvexOne f ∧ Interpolates data f := by
  exact smooth_convex_interpolation_sufficient_proved data hdata

theorem sampled_slacks_nonnegative {d : ℕ} (I : Instance d 1 1) (N : ℕ) (h c : ℝ) :
    ∀ i j, 0 ≤ slack (sampledInstance I N h c) i j := by
  have hf : SmoothConvexOne I.f := ⟨I.convex, I.differentiable, by
    intro x z
    simpa using I.gradient_lipschitz x z⟩
  intro i j
  exact smooth_convex_interpolation_necessary I.f hf _ _

end
end CriticalExtrapolation.Paper
