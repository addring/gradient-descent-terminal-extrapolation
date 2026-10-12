import PaperFramework.FlowMoments

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem extendedBasis_apply {N : ℕ} (β : Vec N) (i : Fin (N + 1)) :
    (∑ j, extendedBasis i j * β j) = zeroExtend β i.val := by
  simp only [extendedBasis, ite_mul, one_mul, zero_mul]
  exact sum_fin_value_selector β i.val

theorem flow_basis_difference_apply {N : ℕ} (β : Vec N) (e : Edge N) :
    (∑ j, (extendedBasis e.1.castSucc j - extendedBasis e.2 j) * β j) =
      β e.1 - zeroExtend β e.2.val := by
  simp_rw [sub_mul, Finset.sum_sub_distrib, extendedBasis_apply]
  change zeroExtend β e.1.val - zeroExtend β e.2.val = β e.1 - zeroExtend β e.2.val
  rw [zeroExtend_at]

theorem flow_matrix_symmetric {N : ℕ} (h c : ℝ) (F : Flow N) (i j : Fin N) :
    flowMatrix h c F i j = flowMatrix h c F j i := by
  unfold flowMatrix
  congr 2
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem flow_matrix_action_edges {N : ℕ} (h c : ℝ) (F : Flow N) (β : Vec N) (i : Fin N) :
    (∑ j, flowMatrix h c F i j * β j) = h ^ 2 * c ^ 2 * (∑ j, β j) - h * c * S N h c *
      ((∑ e ∈ edges N, F e * (extendedBasis e.1.castSucc i - extendedBasis e.2 i) * slope h c β e.1) +
       ∑ e ∈ edges N, TEntry h c e.1 i *
         (F e * (β e.1 - zeroExtend β e.2.val) / queryK N h c e.1)) := by
  have hsum : (∑ j, (∑ e ∈ edges N, (F e / queryK N h c e.1) *
        ((extendedBasis e.1.castSucc i - extendedBasis e.2 i) * TEntry h c e.1 j +
          TEntry h c e.1 i * (extendedBasis e.1.castSucc j - extendedBasis e.2 j))) * β j) =
      ∑ e ∈ edges N, (F e / queryK N h c e.1) *
        ((extendedBasis e.1.castSucc i - extendedBasis e.2 i) * applyT h c β e.1 +
          TEntry h c e.1 i * (β e.1 - zeroExtend β e.2.val)) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp_rw [mul_assoc, ← Finset.mul_sum, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum, TEntry_apply, flow_basis_difference_apply]
  have hsplit : (∑ e ∈ edges N, (F e / queryK N h c e.1) *
        ((extendedBasis e.1.castSucc i - extendedBasis e.2 i) * applyT h c β e.1 +
          TEntry h c e.1 i * (β e.1 - zeroExtend β e.2.val))) =
      (∑ e ∈ edges N, F e * (extendedBasis e.1.castSucc i - extendedBasis e.2 i) * slope h c β e.1) +
        ∑ e ∈ edges N, TEntry h c e.1 i *
          (F e * (β e.1 - zeroExtend β e.2.val) / queryK N h c e.1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    unfold slope
    ring
  calc
    _ = h ^ 2 * c ^ 2 * (∑ j, β j) - h * c * S N h c *
        (∑ j, (∑ e ∈ edges N, (F e / queryK N h c e.1) *
          ((extendedBasis e.1.castSucc i - extendedBasis e.2 i) * TEntry h c e.1 j +
            TEntry h c e.1 i * (extendedBasis e.1.castSucc j - extendedBasis e.2 j))) * β j) := by
      simp_rw [flowMatrix, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    _ = _ := by rw [hsum, hsplit]

theorem flow_row_weight_action {N : ℕ} (h c : ℝ) (F : Flow N) (β : Vec N) (m : Vec N)
    (hm : ∀ k, (∑ e ∈ (edges N).filter (fun e => e.1 = k),
      F e * (β k - zeroExtend β e.2.val)) = m k) (i : Fin N) :
    (∑ e ∈ edges N, TEntry h c e.1 i *
      (F e * (β e.1 - zeroExtend β e.2.val) / queryK N h c e.1)) =
      ∑ k, TEntry h c k i * (m k / queryK N h c k) := by
  rw [← Finset.sum_fiberwise (edges N) (fun e : Edge N => e.1)]
  apply Finset.sum_congr rfl
  intro k _
  have heq : (∑ e ∈ (edges N).filter (fun e => e.1 = k), TEntry h c e.1 i *
      (F e * (β e.1 - zeroExtend β e.2.val) / queryK N h c e.1)) =
      ∑ e ∈ (edges N).filter (fun e => e.1 = k), TEntry h c k i *
        (F e * (β k - zeroExtend β e.2.val) / queryK N h c k) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.mp he).2]
  rw [heq, ← Finset.mul_sum, ← Finset.sum_div, hm k]

end
end CriticalExtrapolation.Paper
