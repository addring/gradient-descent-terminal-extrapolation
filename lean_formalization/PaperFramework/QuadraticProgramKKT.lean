import PaperFramework.QPExistence
import PaperFramework.QPValue
import PaperFramework.FiniteQPKKT
import PaperFramework.QPLinearConstraints

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- (3.10): full KKT before setting any difference multiplier to zero. -/
theorem complete_kkt_exists (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (hβ : IsOptimizer h c β) :
    ∃ (μ : Fin (N - 1) → ℝ) (ν : Vec N), CompleteKKT h c β μ ν := by
  obtain ⟨γ, hγ⟩ := strictly_feasible_direction_exists N h c hp
  have hlinear := (qp_feasible_iff h c β).mp hβ.1
  have hγnorm : qpNormalization N γ = 1 := by
    rw [qpNormalization_apply]
    exact hγ.1
  have hmin : ∀ p, qpNormalization N p = 1 →
      (∀ i, 0 ≤ qpConstraintLinear h c i p) →
      quadraticForm (M₀ N h c) β ≤ quadraticForm (M₀ N h c) p := by
    intro p hn ha
    rw [← chainObjective_matrix N h c hp β, ← chainObjective_matrix N h c hp p]
    exact hβ.2 p ((qp_feasible_iff h c p).mpr ⟨hn, ha⟩)
  obtain ⟨w, hw, hcomp, hstation⟩ := finite_qp_kkt (M₀ N h c)
    (chain_matrix_symmetric N h c) (qpNormalization N) (qpConstraintLinear h c)
    β γ hlinear.1 hlinear.2 hγnorm (qpConstraint_positive_of_strict h c γ hγ) hmin
  refine ⟨(fun i => w (Sum.inl i)), (fun i => w (Sum.inr i)), {
    feasible := hβ.1
    mu_nonnegative := fun i => hw (Sum.inl i)
    nu_nonnegative := fun i => hw (Sum.inr i)
    slope_complementarity := ?_
    difference_complementarity := ?_
    stationarity := ?_ }⟩
  · intro i
    simpa only [qpConstraint_slope] using hcomp (Sum.inl i)
  · intro i
    simpa only [qpConstraint_difference] using hcomp (Sum.inr i)
  · intro i
    have hs := hstation (Pi.single i 1)
    have hgrad : quadraticGradient (M₀ N h c) β (Pi.single i 1) =
        2 * ∑ j, M₀ N h c i j * β j := coordinateLinear_single _ i
    have hnorm : qpNormalization N (Pi.single i 1) = 1 := coordinateLinear_single 1 i
    rw [hgrad, hnorm, mul_one, Fintype.sum_sum_type,
      ← chainObjective_matrix N h c hp β, ← auxiliaryValue_attained N h c hp β hβ] at hs
    simpa only [qpConstraintLinear, coordinateLinear_single, mul_comm, add_assoc] using hs

end
end CriticalExtrapolation.Paper
