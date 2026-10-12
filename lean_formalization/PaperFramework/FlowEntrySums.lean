import PaperFramework.FlowTransport
import PaperFramework.FlowSignRecurrence

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem flowSurvival_split (π : ℕ → ℝ) (k i j : ℕ) (hki : k < i) (hij : i < j) :
    flowSurvival π k j = flowSurvival π k i * (1 - π i) * flowSurvival π i j := by
  have hconv : ∀ a b : ℕ, Finset.Ioo a b = Finset.Ico (a + 1) b := by
    intro a b
    ext x
    simp only [Finset.mem_Ioo, Finset.mem_Ico]
    omega
  simp only [flowSurvival, hconv]
  rw [← Finset.prod_Ico_consecutive (fun x => 1 - π x) (show k + 1 ≤ i by omega) hij.le,
    Finset.prod_eq_prod_Ico_succ_bot hij]
  ring

theorem sum_incoming_before_natural {N : ℕ} (F : ℕ → ℕ → ℝ) (i j : Fin N) (hij : i < j) :
    (∑ e ∈ ((edges N).filter (fun e => e.2.val = j.val)).filter (fun e => e.1 < i),
      F e.1.val e.2.val) = ∑ k ∈ Finset.range i.val, F k j.val := by
  rw [Finset.sum_filter]
  change (∑ e ∈ (edges N).filter (fun e => e.2.val = j.val),
    (fun k l => if k < i.val then F k l else 0) e.1.val e.2.val) = _
  rw [sum_incoming_natural (fun k l => if k < i.val then F k l else 0) j]
  change (∑ k ∈ Finset.range j.val, if k < i.val then F k j.val else 0) = _
  rw [← Finset.sum_filter]
  have heq : (Finset.range j.val).filter (fun k => k < i.val) = Finset.range i.val := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    have hij' : i.val < j.val := hij
    omega
  rw [heq]

theorem inflow_source_selector {N : ℕ} (F : Flow N) (i j : Fin N) (hij : i < j) :
    (∑ e ∈ (edges N).filter (fun e => e.2.val = j.val), if e.1 = i then F e else 0) =
      F (i, j.castSucc) := by
  classical
  let e₀ : Edge N := (i, j.castSucc)
  have he₀ : e₀ ∈ (edges N).filter (fun e => e.2.val = j.val) := by
    simp [e₀, edges, show i.val < j.val from hij]
  rw [Finset.sum_eq_single e₀]
  · simp [e₀]
  · intro e he hne
    have hdest := (Finset.mem_filter.mp he).2
    have hsrc : e.1 ≠ i := by
      intro hsrc
      exact hne (Prod.ext hsrc (Fin.ext hdest))
    simp [hsrc]
  · exact fun hn => (hn he₀).elim

theorem kkt_flow_weighted_edge {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (e : Edge N) :
    kktProductFlow h c β μ e / queryK N h c e.1 =
      flowAlpha h c β μ e.1 * flowProbability h c β μ e.2.val *
        flowSurvival (flowProbability h c β μ) e.1.val e.2.val := by
  unfold kktProductFlow productFlow flowAlpha flowSurvival
  ring

theorem kkt_weighted_inflow_prefix {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (i j : Fin N) (hij : i < j) :
    (∑ e ∈ ((edges N).filter (fun e => e.2.val = j.val)).filter (fun e => e.1 < i),
      kktProductFlow h c β μ e / queryK N h c e.1) =
      flowProbability h c β μ j.val * flowSurvival (flowProbability h c β μ) i.val j.val *
        (1 - flowProbability h c β μ i.val) * flowHistory h c β μ i.val := by
  have hpnt : ∀ e : Edge N, kktProductFlow h c β μ e / queryK N h c e.1 =
      zeroExtend (flowAlpha h c β μ) e.1.val * flowProbability h c β μ e.2.val *
        flowSurvival (flowProbability h c β μ) e.1.val e.2.val := by
    intro e
    rw [zeroExtend_at, kkt_flow_weighted_edge]
  simp_rw [hpnt]
  rw [sum_incoming_before_natural (fun k l => zeroExtend (flowAlpha h c β μ) k *
    flowProbability h c β μ l * flowSurvival (flowProbability h c β μ) k l) i j hij]
  unfold flowHistory
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [flowSurvival_split _ k i.val j.val (Finset.mem_range.mp hk) hij]
  ring

end
end CriticalExtrapolation.Paper
