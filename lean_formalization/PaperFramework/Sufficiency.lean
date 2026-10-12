import PaperFramework.ProductFlow
import PaperFramework.ForwardCertificate

namespace CriticalExtrapolation.Paper
noncomputable section

/-- Theorem (6.8), only in the proved-to-be-needed certificate region. -/
theorem qp_sufficiency_normalized (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (hsize : 1 ≤ (N : ℝ) * h ^ 2) (hΦ : 0 ≤ auxiliaryValue N h c) :
    worstGradient N h c 1 1 = 1 / S N h c := by
  obtain ⟨β, hβ, _⟩ := optimizer_exists_unique N h c hp
  obtain ⟨μ, ν, hkkt⟩ := complete_kkt_exists N h c hp β hβ
  exact forward_certificate_exact N h c hp (kktProductFlow h c β μ)
    (kkt_product_flow_admissible N h c hp hh hsize hΦ β hβ μ ν hkkt)
    (kkt_flow_matrix_nonnegative N h c hp hh hsize hΦ β hβ μ ν hkkt)

theorem qp_sufficiency (N : ℕ) (h c L D : ℝ) (hp : Parameters N h c)
    (hL : 0 < L) (hD : 0 < D) (hh : h < 1)
    (hsize : 1 ≤ (N : ℝ) * h ^ 2) (hΦ : 0 ≤ auxiliaryValue N h c) :
    worstGradient N h c L D = L * D / S N h c := by
  rw [worstGradient_scaling N h c L D hp hL hD,
    qp_sufficiency_normalized N h c hp hh hsize hΦ]
  ring

end
end CriticalExtrapolation.Paper
