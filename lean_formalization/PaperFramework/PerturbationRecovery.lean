import PaperFramework.RecoveredInterpolation
import PaperFramework.NegativeData

namespace CriticalExtrapolation.Paper
noncomputable section

theorem perturbation_global_function_proved (N : ℕ) (h c ε : ℝ) (β : Vec N)
    (hslack : ∀ i j, 0 ≤ slack (perturbationSample h c ε β) i j) :
    let data := perturbationSample h c ε β
    SmoothConvexOne (recoveredFunction data) ∧ Interpolates data (recoveredFunction data) ∧
      (∀ x, recoveredFunction data 0 ≤ recoveredFunction data x) := by
  have hsmooth := recovered_function_global_smoothness_proved (perturbationSample h c ε β)
  have hvalues : ∀ i, (perturbationSample h c ε β).value i =
      inner ℝ ((perturbationSample h c ε β).g i) ((perturbationSample h c ε β).x i) -
        ‖(perturbationSample h c ε β).g i‖ ^ 2 / 2 := fun _ => rfl
  have hdata := recovered_function_interpolates_proved (perturbationSample h c ε β) hvalues hslack
  refine ⟨hsmooth.1, hdata, ?_⟩
  have hx : (perturbationSample h c ε β).x (starQuery N) = 0 := rfl
  have hv : (perturbationSample h c ε β).value (starQuery N) = 0 := by
    simp [perturbationSample, starQuery]
  have hfzero := hdata.1 (starQuery N)
  rw [hx, hv] at hfzero
  intro x
  rw [hfzero]
  exact recoveredFunction_nonnegative_of_zero_potential (perturbationSample h c ε β)
    (fun z => (conjugate_minimizer_exists_unique_proved (perturbationSample h c ε β) z).exists)
    (perturbation_zero_conjugate_potential N h c ε β hslack) x

end
end CriticalExtrapolation.Paper
