import PaperFramework.ChainMatrix
import PaperFramework.FlowMatrixAction

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem quadraticForm_finset_sum {N : ℕ} {α : Type*} (s : Finset α)
    (M : α → Mat N) (β : Vec N) :
    quadraticForm (fun i j => ∑ k ∈ s, M k i j) β =
      ∑ k ∈ s, quadraticForm (M k) β := by
  unfold quadraticForm
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ i, ∑ k ∈ s, ∑ j, M k i j * β i * β j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

/-- The symmetric matrix term is precisely the edge pairing in the certificate. -/
theorem scalar_flow_quadratic_identity {N : ℕ} (h c : ℝ) (F : Flow N) (β : Vec N) :
    quadraticForm (flowMatrix h c F) β = h ^ 2 * c ^ 2 * (∑ i, β i) ^ 2 -
      ∑ e ∈ edges N, lambda h c F e * (β e.1 - zeroExtend β e.2.val) * applyT h c β e.1 := by
  unfold flowMatrix
  rw [quadraticForm_sub, quadraticForm_constant, quadraticForm_scale, quadraticForm_finset_sum]
  simp_rw [quadraticForm_scale, quadraticForm_rank_two, flow_basis_difference_apply, TEntry_apply]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  unfold lambda
  ring

end
end CriticalExtrapolation.Paper
