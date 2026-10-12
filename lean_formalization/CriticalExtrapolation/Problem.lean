import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Faithful definitions for equations (1.1)--(1.4). No main theorem is claimed here. -/

namespace CriticalExtrapolation

open Filter Topology

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The original global function class, including a specified minimizer and initialization. -/
structure Instance (d : ℕ) (L D : ℝ) where
  f : Space d → ℝ
  convex : ConvexOn ℝ Set.univ f
  differentiable : Differentiable ℝ f
  gradient_lipschitz : ∀ x z, ‖gradient f x - gradient f z‖ ≤ L * ‖x - z‖
  initial : Space d
  minimizer : Space d
  minimizes : ∀ x, f minimizer ≤ f x
  radius : ‖initial - minimizer‖ ≤ D

/-- Only the ordinary iterates. The extrapolated output is defined separately. -/
noncomputable def iterate {d : ℕ} {L D : ℝ} (I : Instance d L D) (h : ℝ) : ℕ → Space d
  | 0 => I.initial
  | n + 1 => iterate I h n - (h / L) • gradient I.f (iterate I h n)

noncomputable def output {d : ℕ} {L D : ℝ}
    (I : Instance d L D) (N : ℕ) (h c : ℝ) : Space d :=
  I.initial + c • (iterate I h N - I.initial)

/-- Supremum over every finite dimension, not over interpolation data or QP vectors.
Boundedness and nonemptiness of this set remain proof obligations. -/
noncomputable def worstGradient (N : ℕ) (h c L D : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ (d : ℕ) (I : Instance d L D), r = ‖gradient I.f (output I N h c)‖}

def initialValidityEndpoints (N : ℕ) (h L D : ℝ) : Set ℝ :=
  {C | 1 ≤ C ∧ ∀ c ∈ Set.Icc (1 : ℝ) C,
    worstGradient N h c L D = L * D / (1 + (N : ℝ) * h * c)}

/-- The entire initial validity interval. No monotonicity or QP-root assumption. -/
noncomputable def criticalCoefficient (N : ℕ) (h L D : ℝ) : ℝ :=
  sSup (initialValidityEndpoints N h L D)

/-- A specification, not a proved theorem. Positive L,D are retained until scaling is proved. -/
def MainTheoremStatement : Prop :=
  ∀ (L D h : ℝ), 0 < L → 0 < D → 0 < h → h ≤ 1 →
    Tendsto (fun N : ℕ => h * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) *
      (criticalCoefficient N h L D - 1)) atTop (𝓝 1)

end CriticalExtrapolation
