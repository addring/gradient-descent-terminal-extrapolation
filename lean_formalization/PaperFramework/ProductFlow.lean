import PaperFramework.OrderAndPlateaus
import PaperFramework.FlowOffDiagonal

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- (6.7): this wrapper actually applies the previously kernel-checked SOS theorem. -/
theorem kkt_flow_matrix_nonnegative (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (hsize : 1 ≤ (N : ℝ) * h ^ 2) (hΦ : 0 ≤ auxiliaryValue N h c)
    (β : Vec N) (hβ : IsOptimizer h c β)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν) :
    NonnegativeQuadratic (flowMatrix h c (kktProductFlow h c β μ)) := by
  obtain ⟨hsym, hoff⟩ := kkt_flow_matrix_signs N h c hp hh hsize hΦ β hβ μ ν hkkt
  have hkernel := kkt_flow_matrix_kernel N h c hp hh hsize hΦ β hβ μ ν hkkt
  have hpositive := optimizer_coordinates_positive N h c hp hh β hβ
  exact quadratic_form_nonnegative _ β _ hsym hkernel hpositive hΦ
    (fun i j hij => le_of_lt (hoff i j hij))

end
end CriticalExtrapolation.Paper
