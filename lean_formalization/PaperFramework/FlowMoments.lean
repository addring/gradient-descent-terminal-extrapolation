import PaperFramework.FlowConservation

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem flow_survival_ell (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i : Fin N) :
    (1 - flowProbability h c β μ i.val) * flowEll h c β μ i.val =
      previousMu h c μ i.val / (i.val : ℝ) := by
  by_cases hi : i.val = 0
  · simp [flowProbability, previousMu, hi]
  · have hiR : (i.val : ℝ) ≠ 0 := by exact_mod_cast hi
    have hiN : i.val ≠ N := ne_of_lt i.isLt
    have he := ne_of_gt (kkt_flowEll_positive N h c hp hh β μ ν hkkt i)
    simp only [flowProbability, hi, hiN, or_self, if_false, previousMu]
    field_simp [hiR, he]
    <;> ring

theorem flowEll_recurrence (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (j : ℕ) (hj : 0 < j) (hjN : j ≤ N) :
    flowEll h c β μ (j - 1) = zeroExtend β (j - 1) - zeroExtend β j +
      (1 - flowProbability h c β μ j) * flowEll h c β μ j := by
  have hjstep : j - 1 + 1 = j := by omega
  have hjR : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by exact_mod_cast hjstep
  have heq : flowEll h c β μ (j - 1) = zeroExtend β (j - 1) - zeroExtend β j +
      scaledMu h c μ (j - 1) / (j : ℝ) := by
    unfold flowEll
    rw [hjstep, hjR]
  rw [heq]
  by_cases he : j = N
  · subst j
    simp [flowProbability, scaledMu]
  · have hjlt : j < N := by omega
    have hs := flow_survival_ell N h c hp hh β μ ν hkkt ⟨j, hjlt⟩
    simp only [previousMu, show j ≠ 0 by omega, if_false] at hs
    rw [hs]

theorem flow_departure_moment (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i : Fin N) :
    (1 + (i.val : ℝ) * flowProbability h c β μ i.val) * flowEll h c β μ i.val =
      rowMoment h c β μ i := by
  have he : ((i.val : ℝ) + 1) * flowEll h c β μ i.val =
      ((i.val : ℝ) + 1) * difference β i + scaledMu h c μ i.val := by
    rw [flowEll_at_coordinate]
    field_simp [show (i.val : ℝ) + 1 ≠ 0 by positivity]
  have hs : (i.val : ℝ) * ((1 - flowProbability h c β μ i.val) * flowEll h c β μ i.val) =
      previousMu h c μ i.val := by
    rw [flow_survival_ell N h c hp hh β μ ν hkkt i]
    by_cases hi : i.val = 0
    · simp [previousMu, hi]
    · have hiR : (i.val : ℝ) ≠ 0 := by exact_mod_cast hi
      field_simp [hiR]
  unfold rowMoment
  nlinarith only [he, hs]

theorem kkt_product_flow_row_moments (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (hsize : 1 ≤ (N : ℝ) * h ^ 2) (hΦ : 0 ≤ auxiliaryValue N h c)
    (β : Vec N) (hβ : IsOptimizer h c β)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν) :
    ∀ i, (∑ e ∈ (edges N).filter (fun e => e.1 = i),
      kktProductFlow h c β μ e * (β i - zeroExtend β e.2.val)) = rowMoment h c β μ i := by
  intro i
  let π := flowProbability h c β μ
  let O : ℕ → ℝ := fun k => 1 + (k : ℝ) * π k
  change (∑ e ∈ (edges N).filter (fun e => e.1 = i),
    productFlow O π e.1.val e.2.val * (β i - zeroExtend β e.2.val)) = _
  rw [sum_outgoing_natural (fun k j => productFlow O π k j * (β i - zeroExtend β j)) i]
  have hpnt : ∀ j, productFlow O π i.val j * (β i - zeroExtend β j) =
      O i.val * (π j * flowSurvival π i.val j * (zeroExtend β i.val - zeroExtend β j)) := by
    intro j
    rw [zeroExtend_at]
    unfold productFlow flowSurvival
    ring
  simp_rw [hpnt]
  rw [← Finset.mul_sum, productFlow_weighted_exit π (zeroExtend β) (flowEll h c β μ) N i.val
    i.isLt (flowProbability_boundary h c β μ).2
    (flowEll_recurrence N h c hp hh β μ ν hkkt)]
  exact flow_departure_moment N h c hp hh β μ ν hkkt i

end
end CriticalExtrapolation.Paper
