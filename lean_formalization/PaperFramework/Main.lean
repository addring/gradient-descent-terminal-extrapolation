import PaperFramework.CriticalInterval

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

/-- The sharp critical scale for the actual worst-case output gradient over all finite dimensions. -/
theorem sharp_critical_scale (L D h : ℝ)
    (hL : 0 < L) (hD : 0 < D) (hh : 0 < h) (hh1 : h ≤ 1) :
    Tendsto (fun N : ℕ => h * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) *
      (criticalCoefficient N h L D - 1)) atTop (𝓝 1) := by
  apply scaled_limit_of_interval_sandwich h hh (fun N => criticalCoefficient N h L D)
  intro ε hε
  exact critical_interval_sandwich h L D ε hh hh1 hL hD hε.1 hε.2

theorem main_theorem : MainTheoremStatement := by
  intro L D h hL hD hh hh1
  exact sharp_critical_scale L D h hL hD hh hh1

end
end CriticalExtrapolation.Paper
