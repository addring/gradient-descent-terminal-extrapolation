import PaperFramework.FlowQuadratic
import PaperFramework.VectorQuadratic

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem space_finset_sum_apply {d : ℕ} {α : Type*} (s : Finset α)
    (v : α → Space d) (k : Fin d) : (∑ i ∈ s, v i) k = ∑ i ∈ s, v i k := by
  exact map_sum (PiLp.projₗ (p := 2) (𝕜 := ℝ) (fun _ : Fin d => ℝ) k) v s

def flowVectorExtend {N d : ℕ} (v : Fin N → Space d) (j : Fin (N + 1)) : Space d :=
  ∑ i, extendedBasis j i • v i

def flowVectorT {N d : ℕ} (h c : ℝ) (v : Fin N → Space d) (i : Fin N) : Space d :=
  ∑ j, TEntry h c i j • v j

theorem flowVectorExtend_apply {N d : ℕ} (v : Fin N → Space d)
    (j : Fin (N + 1)) (k : Fin d) :
    flowVectorExtend v j k = zeroExtend (fun i => v i k) j.val := by
  simp only [flowVectorExtend, space_finset_sum_apply, PiLp.smul_apply, smul_eq_mul]
  exact extendedBasis_apply (fun i => v i k) j

theorem flowVectorT_apply {N d : ℕ} (h c : ℝ) (v : Fin N → Space d)
    (i : Fin N) (k : Fin d) : flowVectorT h c v i k = applyT h c (fun j => v j k) i := by
  simp only [flowVectorT, space_finset_sum_apply, PiLp.smul_apply, smul_eq_mul]
  exact TEntry_apply h c (fun j => v j k) i

theorem space_norm_sq_coordinates {d : ℕ} (x : Space d) :
    ‖x‖ ^ 2 = ∑ k : Fin d, (x k) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

/-- Coordinatewise lifting of the exact flow matrix identity to any finite dimension. -/
theorem vector_flow_quadratic_identity {N d : ℕ} (h c : ℝ) (F : Flow N)
    (v : Fin N → Space d) :
    (∑ i, ∑ j, flowMatrix h c F i j * inner ℝ (v i) (v j)) =
      h ^ 2 * c ^ 2 * ‖∑ i, v i‖ ^ 2 -
      ∑ e ∈ edges N, lambda h c F e *
        inner ℝ (v e.1 - flowVectorExtend v e.2) (flowVectorT h c v e.1) := by
  rw [vector_quadratic_coordinates]
  simp_rw [scalar_flow_quadratic_identity, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [space_norm_sq_coordinates]
  simp only [space_finset_sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [PiLp.inner_apply, Finset.mul_sum]
  simp only [PiLp.sub_apply, flowVectorExtend_apply, flowVectorT_apply,
    RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro k _
  ring

end
end CriticalExtrapolation.Paper
