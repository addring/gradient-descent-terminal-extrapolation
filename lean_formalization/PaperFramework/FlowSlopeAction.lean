import PaperFramework.FlowMatrixAction

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem flow_basis_flux {N : ℕ} (F : Flow N) (v : Vec N) (i : Fin N) :
    (∑ e ∈ edges N, F e * (extendedBasis e.1.castSucc i - extendedBasis e.2 i) * v e.1) =
      outflow (fun e => F e * v e.1) i - inflow (fun e => F e * v e.1) i := by
  unfold outflow inflow
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [extendedBasis, Fin.val_castSucc, Fin.ext_iff]
  split_ifs <;> ring

theorem outflow_source_weight {N : ℕ} (F : Flow N) (v : Vec N) (i : Fin N) :
    outflow (fun e => F e * v e.1) i = outflow F i * v i := by
  unfold outflow
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  change F e * v e.1 = F e * v i
  rw [(Finset.mem_filter.mp he).2]

theorem inflow_predecessor_weight {N : ℕ} (F : Flow N) (v : Vec N)
    (hF : ∀ e ∈ edges N, 0 ≤ F e)
    (hsupport : ∀ e ∈ edges N, 0 < F e →
      ∀ k : Fin N, e.1.val ≤ k.val → k.val < e.2.val → v k = v e.1) (i : Fin N) :
    inflow (fun e => F e * v e.1) i = inflow F i * previousCoordinate v i.val := by
  unfold inflow
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  have he' := Finset.mem_filter.mp he
  have heorder := (Finset.mem_filter.mp he'.1).2
  have hie := he'.2
  by_cases hz : F e = 0
  · simp [hz]
  · have hp : 0 < F e := lt_of_le_of_ne (hF e he'.1) (Ne.symm hz)
    have hi : i.val ≠ 0 := by omega
    let p : Fin N := ⟨i.val - 1, by omega⟩
    have hsp := hsupport e he'.1 hp p (by dsimp [p]; omega) (by dsimp [p]; omega)
    have hprev : previousCoordinate v i.val = v p := by
      simp [previousCoordinate, hi, zeroExtend, p, show i.val - 1 < N by omega]
    rw [hprev, hsp]

theorem kkt_flow_slope_action (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (hsize : 1 ≤ (N : ℝ) * h ^ 2) (hΦ : 0 ≤ auxiliaryValue N h c)
    (β : Vec N) (hβ : IsOptimizer h c β)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν) (i : Fin N) :
    (∑ e ∈ edges N, kktProductFlow h c β μ e *
      (extendedBasis e.1.castSucc i - extendedBasis e.2 i) * slope h c β e.1) =
      kktSlopeMoment h c β i := by
  have hflow := kkt_product_flow_admissible N h c hp hh hsize hΦ β hβ μ ν hkkt
  have hs := kkt_product_flow_support N h c hp hh β hβ μ ν hkkt
  rw [flow_basis_flux, outflow_source_weight,
    inflow_predecessor_weight _ _ hflow.1 hs]
  have hout := productFlow_outflow N (flowProbability h c β μ) (flowProbability_boundary h c β μ).2 i
  have hin := productFlow_inflow N (flowProbability h c β μ) i
  change outflow (kktProductFlow h c β μ) i = _ at hout
  change inflow (kktProductFlow h c β μ) i = _ at hin
  rw [hout, hin]
  by_cases hi : i.val = 0
  · rw [kktSlopeMoment_at_first N h c β i hi]
    simp [hi]
  · let p : Fin N := ⟨i.val - 1, by omega⟩
    have hpi : p.val + 1 = i.val := by dsimp [p]; omega
    have hiR : (i.val : ℝ) = (p.val : ℝ) + 1 := by exact_mod_cast hpi.symm
    have hprev : previousCoordinate (slope h c β) i.val = slope h c β p := by
      rw [← hpi, previousCoordinate_succ]
    rw [hprev, kktSlopeMoment_at_successor h c β p i hpi]
    have hc := flow_survival_complementarity h c β μ ν hkkt p i hpi
    have hmul := congrArg (fun x : ℝ => (i.val : ℝ) * x) hc
    rw [hiR] at hmul ⊢
    nlinarith only [hmul]

theorem kkt_flow_matrix_kernel (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (hsize : 1 ≤ (N : ℝ) * h ^ 2) (hΦ : 0 ≤ auxiliaryValue N h c)
    (β : Vec N) (hβ : IsOptimizer h c β)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν) :
    ∀ i, (∑ j, flowMatrix h c (kktProductFlow h c β μ) i j * β j) = auxiliaryValue N h c := by
  intro i
  have hm := kkt_product_flow_row_moments N h c hp hh hsize hΦ β hβ μ ν hkkt
  rw [flow_matrix_action_edges, hkkt.feasible.1, mul_one,
    kkt_flow_slope_action N h c hp hh hsize hΦ β hβ μ ν hkkt i,
    flow_row_weight_action h c _ β (rowMoment h c β μ) hm i]
  have hν := kkt_difference_multipliers_zero N h c hp hh β μ ν hkkt
  have hf : scaledNu h c ν = 0 := by funext k; simp [scaledNu, hν k]
  have hbal := kkt_coordinate_balance N h c hp β μ ν hkkt i
  rw [hf] at hbal
  simp only [backwardDifference, Pi.zero_apply, previousCoordinate, zeroExtend,
    dite_eq_ite, ite_self, sub_zero, add_zero] at hbal
  change kktSlopeMoment h c β i + (∑ k, TEntry h c k i * kktRowWeight h c β μ k) =
    kktConstant N h c at hbal
  change h ^ 2 * c ^ 2 - h * c * S N h c *
    (kktSlopeMoment h c β i + ∑ k, TEntry h c k i * kktRowWeight h c β μ k) = _
  rw [hbal]
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hp.c_ge_one
  have hS : 0 < S N h c := by
    have hhpos := hp.h_pos
    unfold S
    positivity
  unfold kktConstant
  field_simp [ne_of_gt hp.h_pos, ne_of_gt hc, ne_of_gt hS]
  <;> ring

end
end CriticalExtrapolation.Paper
