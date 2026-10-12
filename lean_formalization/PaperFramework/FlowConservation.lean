import PaperFramework.ProductFlowSums
import PaperFramework.FlowProbabilities

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem productFlow_outflow (N : ℕ) (π : ℕ → ℝ) (hπ : π N = 1) (i : Fin N) :
    outflow (fun e : Edge N => productFlow (fun k => 1 + (k : ℝ) * π k) π e.1.val e.2.val) i =
      1 + (i.val : ℝ) * π i.val := by
  unfold outflow
  rw [sum_outgoing_natural]
  simp only [productFlow, mul_assoc]
  change (∑ j ∈ Finset.Ico (i.val + 1) (N + 1),
    (1 + (i.val : ℝ) * π i.val) * (π j * flowSurvival π i.val j)) = _
  rw [← Finset.mul_sum, productFlow_exit_mass π N i.val i.isLt hπ, mul_one]

theorem productFlow_inflow (N : ℕ) (π : ℕ → ℝ) (i : Fin N) :
    inflow (fun e : Edge N => productFlow (fun k => 1 + (k : ℝ) * π k) π e.1.val e.2.val) i =
      (i.val : ℝ) * π i.val := by
  unfold inflow
  rw [sum_incoming_natural]
  have heq : ∀ k, productFlow (fun k => 1 + (k : ℝ) * π k) π k i.val =
      ((1 + (k : ℝ) * π k) * flowSurvival π k i.val) * π i.val := by
    intro k
    unfold productFlow flowSurvival
    ring
  simp_rw [heq]
  rw [← Finset.sum_mul, productFlow_arrival_mass]

theorem natural_productFlow_admissible (N : ℕ) (π : ℕ → ℝ)
    (hπ : ∀ i ≤ N, π i ∈ Set.Icc (0 : ℝ) 1) (hN : π N = 1) :
    AdmissibleFlow (fun e : Edge N => productFlow (fun k => 1 + (k : ℝ) * π k) π e.1.val e.2.val) := by
  constructor
  · intro e he
    have hj : e.2.val ≤ N := by have := e.2.isLt; omega
    have hi := hπ e.1.val e.1.isLt.le
    have hp := hπ e.2.val hj
    unfold productFlow
    apply mul_nonneg
    · exact mul_nonneg (add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hi.1)) hp.1
    · apply Finset.prod_nonneg
      intro k hk
      have hki := Finset.mem_Ioo.mp hk
      exact sub_nonneg.mpr (hπ k (by omega)).2
  · intro i
    rw [productFlow_outflow N π hN i, productFlow_inflow]
    ring

theorem kkt_product_flow_admissible (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (hsize : 1 ≤ (N : ℝ) * h ^ 2) (hΦ : 0 ≤ auxiliaryValue N h c)
    (β : Vec N) (hβ : IsOptimizer h c β)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν) :
    AdmissibleFlow (kktProductFlow h c β μ) :=
  natural_productFlow_admissible N (flowProbability h c β μ)
    (kkt_probabilities_in_unit_interval N h c hp hh hsize hΦ β hβ μ ν hkkt)
    (flowProbability_boundary h c β μ).2

end
end CriticalExtrapolation.Paper
