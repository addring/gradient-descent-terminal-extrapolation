import PaperFramework.FlowSlopeAction

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def flowTransport {N : ℕ} (h c : ℝ) (F : Flow N) (i j : Fin N) : ℝ :=
  ∑ e ∈ edges N, (F e / queryK N h c e.1) *
    (extendedBasis e.1.castSucc i - extendedBasis e.2 i) * TEntry h c e.1 j

def flowRho {N : ℕ} (h c : ℝ) (F : Flow N) (i : Fin N) : ℝ :=
  outflow F i / queryK N h c i - inflow (fun e => F e / queryK N h c e.1) i

theorem flow_matrix_transport {N : ℕ} (h c : ℝ) (F : Flow N) (i j : Fin N) :
    flowMatrix h c F i j = h ^ 2 * c ^ 2 - h * c * S N h c *
      (flowTransport h c F i j + flowTransport h c F j i) := by
  unfold flowMatrix flowTransport
  rw [← Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem queryK_antitone (N : ℕ) (h c : ℝ) (hp : Parameters N h c) :
    Antitone (queryK N h c) := by
  intro i j hij
  have hijR : (i.val : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hij
  unfold queryK
  nlinarith [mul_nonneg hp.h_pos.le (sub_nonneg.mpr hijR)]

theorem queryK_lt_S (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (i : Fin N) :
    queryK N h c i < S N h c := by
  unfold queryK S
  nlinarith [mul_nonneg hp.h_pos.le (Nat.cast_nonneg (α := ℝ) i.val)]

theorem flowRho_lower_bound (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (F : Flow N) (hF : AdmissibleFlow F) (i : Fin N) :
    1 / queryK N h c i ≤ flowRho h c F i := by
  have hs : inflow (fun e => F e / queryK N h c e.1) i ≤ inflow F i / queryK N h c i := by
    unfold inflow
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro e he
    have he' := Finset.mem_filter.mp he
    have horder := (Finset.mem_filter.mp he'.1).2
    have heq := he'.2
    have hei : e.1 ≤ i := by change e.1.val ≤ i.val; omega
    apply (div_le_div_iff₀ (queryK_positive N h c hp e.1) (queryK_positive N h c hp i)).mpr
    exact mul_le_mul_of_nonneg_left (queryK_antitone N h c hp hei) (hF.1 e he'.1)
  calc
    _ = (outflow F i - inflow F i) / queryK N h c i := by rw [hF.2 i]
    _ = outflow F i / queryK N h c i - inflow F i / queryK N h c i := sub_div _ _ _
    _ ≤ flowRho h c F i := by unfold flowRho; linarith

theorem flowTransport_outgoing_incoming {N : ℕ} (h c : ℝ) (F : Flow N) (i j : Fin N) :
    flowTransport h c F i j = outflow F i / queryK N h c i * TEntry h c i j -
      inflow (fun e => (F e / queryK N h c e.1) * TEntry h c e.1 j) i := by
  rw [flowTransport, flow_basis_flux (fun e => F e / queryK N h c e.1)
    (fun k => TEntry h c k j) i]
  congr 1
  unfold outflow
  rw [Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  change (F e / queryK N h c e.1) * TEntry h c e.1 j =
    (F e / queryK N h c i) * TEntry h c i j
  rw [(Finset.mem_filter.mp he).2]

theorem flowTransport_upper_entry (N : ℕ) (h c : ℝ) (F : Flow N)
    (i j : Fin N) (hij : i < j) : flowTransport h c F i j = h * c * flowRho h c F i := by
  have hTi : TEntry h c i j = h * c := by simp [TEntry, not_lt_of_gt hij, ne_of_lt hij]
  have hin : inflow (fun e => (F e / queryK N h c e.1) * TEntry h c e.1 j) i =
      h * c * inflow (fun e => F e / queryK N h c e.1) i := by
    unfold inflow
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have he' := Finset.mem_filter.mp he
    have horder := (Finset.mem_filter.mp he'.1).2
    have heq := he'.2
    have hei : e.1 < i := by change e.1.val < i.val; omega
    have hej : e.1 < j := lt_trans hei hij
    simp [TEntry, not_lt_of_gt hej, ne_of_lt hej, mul_comm]
  rw [flowTransport_outgoing_incoming, hTi, hin]
  unfold flowRho
  ring

theorem outputMultiplier_eq_rho {N : ℕ} (h c : ℝ) (F : Flow N) (i : Fin N) :
    outputMultiplier h c F i = 2 * h * c * S N h c * flowRho h c F i - 2 * h * c := by
  have ho : outflow (lambda h c F) i =
      2 * h * c * S N h c * (outflow F i / queryK N h c i) := by
    unfold outflow lambda
    rw [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    change (2 * h * c * S N h c / queryK N h c e.1) * F e =
      2 * h * c * S N h c * (F e / queryK N h c i)
    rw [(Finset.mem_filter.mp he).2]
    ring
  have hi : inflow (lambda h c F) i =
      2 * h * c * S N h c * inflow (fun e => F e / queryK N h c e.1) i := by
    unfold inflow lambda
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  unfold outputMultiplier
  rw [ho, hi]
  unfold flowRho
  ring

theorem output_multipliers_positive (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (F : Flow N) (hF : AdmissibleFlow F) :
    ∀ i, 0 < outputMultiplier h c F i := by
  intro i
  have hK := queryK_positive N h c hp i
  have hKS := queryK_lt_S N h c hp i
  have hS : 0 < S N h c := lt_trans hK hKS
  have hfrac : 1 < S N h c / queryK N h c i := by
    apply (lt_div_iff₀ hK).mpr
    simpa using hKS
  have hr := mul_le_mul_of_nonneg_left (flowRho_lower_bound N h c hp F hF i) hS.le
  have hr' : S N h c / queryK N h c i ≤ S N h c * flowRho h c F i := by
    simpa only [one_div, div_eq_mul_inv, one_mul] using hr
  have hgap : 0 < S N h c * flowRho h c F i - 1 := by linarith
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hp.c_ge_one
  have hprod := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hp.h_pos hc)) hgap
  rw [outputMultiplier_eq_rho]
  nlinarith only [hprod]

end
end CriticalExtrapolation.Paper
