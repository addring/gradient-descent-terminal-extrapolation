import PaperFramework.NegativeData
import PaperFramework.Interpolation
import PaperFramework.QPStrictNegative
import PaperFramework.NegativeInstance

namespace CriticalExtrapolation.Paper
noncomputable section

/-- The finite maximum plus the squared norm has a unique conjugate optimizer globally. -/
theorem conjugate_minimizer_exists_unique {N d : ℕ} (data : Sample N d) (x : Space d) :
    ∃! u, ConjugateMinimizer data x u := by
  exact conjugate_minimizer_exists_unique_proved data x

theorem conjugate_optimizer_firm_nonexpansive {N d : ℕ} (data : Sample N d)
    (x z u v : Space d) (hu : ConjugateMinimizer data x u)
    (hv : ConjugateMinimizer data z v) :
    ‖u - v‖ ^ 2 ≤ inner ℝ (x - z) (u - v) := by
  exact conjugate_optimizer_firm_nonexpansive_proved data x z u v hu hv

theorem recovered_function_global_smoothness {N d : ℕ} (data : Sample N d) :
    SmoothConvexOne (recoveredFunction data) ∧
      ∀ x u, ConjugateMinimizer data x u → gradient (recoveredFunction data) x = u := by
  exact recovered_function_global_smoothness_proved data

/-- This recovery formula is for the special values (11.2); arbitrary values use Interpolation. -/
theorem recovered_function_interpolates {N d : ℕ} (data : Sample N d)
    (hvalue : ∀ i, data.value i = inner ℝ (data.g i) (data.x i) - ‖data.g i‖ ^ 2 / 2)
    (hslack : ∀ i j, 0 ≤ slack data i j) :
    Interpolates data (recoveredFunction data) := by
  exact recovered_function_interpolates_proved data hvalue hslack

theorem perturbation_global_function (N : ℕ) (h c ε : ℝ) (β : Vec N)
    (hslack : ∀ i j, 0 ≤ slack (perturbationSample h c ε β) i j) :
    let data := perturbationSample h c ε β
    SmoothConvexOne (recoveredFunction data) ∧ Interpolates data (recoveredFunction data) ∧
      (∀ x, recoveredFunction data 0 ≤ recoveredFunction data x) := by
  have hsmooth := recovered_function_global_smoothness (perturbationSample h c ε β)
  have hinterp := recovered_function_interpolates (perturbationSample h c ε β)
  have hvalues : ∀ i, (perturbationSample h c ε β).value i =
      inner ℝ ((perturbationSample h c ε β).g i) ((perturbationSample h c ε β).x i) -
        ‖(perturbationSample h c ε β).g i‖ ^ 2 / 2 := fun _ => rfl
  have hdata := hinterp hvalues hslack
  refine ⟨hsmooth.1, hdata, ?_⟩
  have hx : (perturbationSample h c ε β).x (starQuery N) = 0 := rfl
  have hv : (perturbationSample h c ε β).value (starQuery N) = 0 := by
    simp [perturbationSample, starQuery]
  have hfzero := hdata.1 (starQuery N)
  rw [hx, hv] at hfzero
  intro x
  rw [hfzero]
  exact recoveredFunction_nonnegative_of_zero_potential (perturbationSample h c ε β)
    (fun z => (conjugate_minimizer_exists_unique (perturbationSample h c ε β) z).exists)
    (perturbation_zero_conjugate_potential N h c ε β hslack) x

/-- Proposition 11: an actual globally defined two-dimensional counterexample, after scaling. -/
theorem negative_direction_realization (N : ℕ) (h c L D : ℝ) (hp : Parameters N h c)
    (hL : 0 < L) (hD : 0 < D) (β : Vec N)
    (hβ : StrictlyFeasible h c β) (hQ : chainObjective h c β < 0) :
    ∃ I : Instance 2 L D, L * D / S N h c < ‖gradient I.f (output I N h c)‖ := by
  exact negative_direction_realization_proved N h c L D hp hL hD β hβ hQ

theorem negative_direction_failure (N : ℕ) (h c L D : ℝ) (hp : Parameters N h c)
    (hL : 0 < L) (hD : 0 < D) (β : Vec N)
    (hβ : StrictlyFeasible h c β) (hQ : chainObjective h c β < 0) :
    L * D / S N h c < worstGradient N h c L D := by
  obtain ⟨I, hI⟩ := negative_direction_realization N h c L D hp hL hD β hβ hQ
  obtain ⟨_, hbdd⟩ := instance_values_nonempty_bounded N h c L D hL hD
  exact lt_of_lt_of_le hI (le_csSup hbdd ⟨2, I, rfl⟩)

end
end CriticalExtrapolation.Paper
