import PaperFramework.Definitions

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- The vector quadratic form is the sum of the scalar forms in each Euclidean coordinate. -/
theorem vector_quadratic_coordinates {N d : ℕ} (M : Mat N) (v : Fin N → Space d) :
    (∑ i, ∑ j, M i j * inner ℝ (v i) (v j)) =
      ∑ k : Fin d, quadraticForm M (fun i => v i k) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ i, ∑ k : Fin d, ∑ j, M i j * (v j k * v i k) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k : Fin d, ∑ i, ∑ j, M i j * (v j k * v i k) := Finset.sum_comm
    _ = _ := by
      unfold quadraticForm
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem vector_quadratic_nonnegative {N d : ℕ} (M : Mat N)
    (hM : NonnegativeQuadratic M) (v : Fin N → Space d) :
    0 ≤ ∑ i, ∑ j, M i j * inner ℝ (v i) (v j) := by
  rw [vector_quadratic_coordinates]
  exact Finset.sum_nonneg (fun k _ => hM (fun i => v i k))

end
end CriticalExtrapolation.Paper
