import PaperFramework.FlowEntrySums

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem flowTransport_lower_entry {N : ℕ} (h c : ℝ) (F : Flow N)
    (i j : Fin N) (hij : i < j) :
    flowTransport h c F j i = h * (c - 1) * flowRho h c F j +
      (1 - h) * (F (i, j.castSucc) / queryK N h c i) - h *
        ∑ e ∈ ((edges N).filter (fun e => e.2.val = j.val)).filter (fun e => e.1 < i),
          F e / queryK N h c e.1 := by
  let W : Flow N := fun e => F e / queryK N h c e.1
  have hpoint : ∀ e : Edge N, W e * TEntry h c e.1 i = h * (c - 1) * W e +
      h * (if e.1 < i then W e else 0) - (1 - h) * (if e.1 = i then W e else 0) := by
    intro e
    rcases lt_trichotomy e.1 i with he | he | he
    · simp [TEntry, he, not_lt_of_gt he, ne_of_lt he]
      <;> ring
    · simp [he, TEntry]
      <;> ring
    · simp [TEntry, he, not_lt_of_gt he, ne_of_gt he]
      <;> ring
  have hpre : (∑ e ∈ (edges N).filter (fun e => e.2.val = j.val), if e.1 < i then W e else 0) =
      ∑ e ∈ ((edges N).filter (fun e => e.2.val = j.val)).filter (fun e => e.1 < i), W e := by
    exact (Finset.sum_filter (s := (edges N).filter (fun e => e.2.val = j.val))
      (fun e => e.1 < i) W).symm
  have hin : inflow (fun e => W e * TEntry h c e.1 i) j =
      h * (c - 1) * inflow W j +
        h * (∑ e ∈ ((edges N).filter (fun e => e.2.val = j.val)).filter (fun e => e.1 < i), W e) -
          (1 - h) * W (i, j.castSucc) := by
    unfold inflow
    simp_rw [hpoint, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hpre, inflow_source_selector W i j hij]
  have hT : TEntry h c j i = h * (c - 1) := by
    simp [TEntry, hij, ne_of_gt hij]
    <;> ring
  rw [flowTransport_outgoing_incoming, hT]
  change outflow F j / queryK N h c j * (h * (c - 1)) -
    inflow (fun e => W e * TEntry h c e.1 i) j = _
  rw [hin]
  unfold flowRho
  dsimp [W]
  ring

theorem kkt_flowTransport_lower_entry {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (i j : Fin N) (hij : i < j) :
    flowTransport h c (kktProductFlow h c β μ) j i =
      h * (c - 1) * flowRho h c (kktProductFlow h c β μ) j +
        flowProbability h c β μ j.val * flowSurvival (flowProbability h c β μ) i.val j.val *
          ((1 - h) * flowAlpha h c β μ i -
            h * (1 - flowProbability h c β μ i.val) * flowHistory h c β μ i.val) := by
  rw [flowTransport_lower_entry h c _ i j hij, kkt_weighted_inflow_prefix h c β μ i j hij,
    kkt_flow_weighted_edge]
  change h * (c - 1) * flowRho h c (kktProductFlow h c β μ) j +
    (1 - h) * (flowAlpha h c β μ i * flowProbability h c β μ j.val *
      flowSurvival (flowProbability h c β μ) i.val j.val) - _ = _
  ring

theorem kkt_flow_matrix_off_diagonal_negative (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (hsize : 1 ≤ (N : ℝ) * h ^ 2) (hΦ : 0 ≤ auxiliaryValue N h c)
    (β : Vec N) (hβ : IsOptimizer h c β) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i j : Fin N) (hij : i < j) :
    flowMatrix h c (kktProductFlow h c β μ) i j < 0 := by
  let F := kktProductFlow h c β μ
  have hF := kkt_product_flow_admissible N h c hp hh hsize hΦ β hβ μ ν hkkt
  have hπ := kkt_probabilities_in_unit_interval N h c hp hh hsize hΦ β hβ μ ν hkkt
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hp.c_ge_one
  have hhc := mul_pos hp.h_pos hc
  have hK := queryK_positive N h c hp i
  have hKS := queryK_lt_S N h c hp i
  have hS := lt_trans hK hKS
  have hρi := flowRho_lower_bound N h c hp F hF i
  have hρj : 0 ≤ flowRho h c F j := le_trans
    (div_nonneg zero_le_one (queryK_positive N h c hp j).le) (flowRho_lower_bound N h c hp F hF j)
  have hfrac : h * c / S N h c < h * c / queryK N h c i :=
    (div_lt_div_iff₀ hS hK).mpr (mul_lt_mul_of_pos_left hKS hhc)
  have hρi' : h * c / queryK N h c i ≤ h * c * flowRho h c F i := by
    simpa only [one_div, div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hρi hhc.le
  have hterm₁ : 0 ≤ h * (c - 1) * flowRho h c F j :=
    mul_nonneg (mul_nonneg hp.h_pos.le (sub_nonneg.mpr hp.c_ge_one)) hρj
  have hsur : 0 ≤ flowSurvival (flowProbability h c β μ) i.val j.val := by
    apply Finset.prod_nonneg
    intro k hk
    have hk' := Finset.mem_Ioo.mp hk
    exact sub_nonneg.mpr (hπ k (by have := j.isLt; omega)).2
  have hfactor : 0 < (1 - h) * flowAlpha h c β μ i -
      h * (1 - flowProbability h c β μ i.val) * flowHistory h c β μ i.val :=
    sub_pos.mpr (flowHistory_strict_bound N h c hp hh β μ ν hkkt i)
  have hterm₂ := mul_nonneg (mul_nonneg (hπ j.val j.isLt.le).1 hsur) hfactor.le
  have hbracket : h * c / S N h c <
      h * c * flowRho h c F i + h * (c - 1) * flowRho h c F j +
        flowProbability h c β μ j.val * flowSurvival (flowProbability h c β μ) i.val j.val *
          ((1 - h) * flowAlpha h c β μ i -
            h * (1 - flowProbability h c β μ i.val) * flowHistory h c β μ i.val) := by
    linarith
  have hmul := mul_lt_mul_of_pos_left hbracket (mul_pos hhc hS)
  have hcancel : (h * c * S N h c) * (h * c / S N h c) = h ^ 2 * c ^ 2 := by
    field_simp [ne_of_gt hS]
    <;> ring
  rw [hcancel] at hmul
  rw [flow_matrix_transport, flowTransport_upper_entry N h c _ i j hij,
    kkt_flowTransport_lower_entry h c β μ i j hij]
  change h ^ 2 * c ^ 2 - h * c * S N h c *
    (h * c * flowRho h c F i + (h * (c - 1) * flowRho h c F j + _)) < 0
  linarith

theorem kkt_flow_matrix_signs (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (hsize : 1 ≤ (N : ℝ) * h ^ 2) (hΦ : 0 ≤ auxiliaryValue N h c)
    (β : Vec N) (hβ : IsOptimizer h c β)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν) :
    (∀ i j, flowMatrix h c (kktProductFlow h c β μ) i j =
      flowMatrix h c (kktProductFlow h c β μ) j i) ∧
    (∀ i j, i ≠ j → flowMatrix h c (kktProductFlow h c β μ) i j < 0) := by
  refine ⟨flow_matrix_symmetric h c _, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact kkt_flow_matrix_off_diagonal_negative N h c hp hh hsize hΦ β hβ μ ν hkkt i j hij
  · rw [flow_matrix_symmetric h c _ i j]
    exact kkt_flow_matrix_off_diagonal_negative N h c hp hh hsize hΦ β hβ μ ν hkkt j i hji

end
end CriticalExtrapolation.Paper
