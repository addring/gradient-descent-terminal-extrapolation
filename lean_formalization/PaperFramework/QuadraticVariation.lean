import PaperFramework.ChainMatrix
import PaperFramework.QPGeometry

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def coordinateLinear {N : ℕ} (w : Vec N) : Vec N →ₗ[ℝ] ℝ where
  toFun v := ∑ i, w i * v i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def quadraticGradient {N : ℕ} (M : Mat N) (β : Vec N) : Vec N →ₗ[ℝ] ℝ :=
  coordinateLinear (fun i => 2 * ∑ j, M i j * β j)

theorem coordinateLinear_single {N : ℕ} (w : Vec N) (i : Fin N) :
    coordinateLinear w (Pi.single i 1) = w i := by
  simp [coordinateLinear, Pi.single_apply, mul_ite]

theorem chain_matrix_symmetric (N : ℕ) (h c : ℝ) (i j : Fin N) :
    M₀ N h c i j = M₀ N h c j i := by
  rw [chain_matrix_entries, chain_matrix_entries]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem quadraticGradient_apply {N : ℕ} (M : Mat N) (β v : Vec N) :
    quadraticGradient M β v = 2 * ∑ i, ∑ j, M i j * β j * v i := by
  unfold quadraticGradient coordinateLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadraticGradient_self {N : ℕ} (M : Mat N) (β : Vec N) :
    quadraticGradient M β β = 2 * quadraticForm M β := by
  rw [quadraticGradient_apply]
  unfold quadraticForm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_cross_symmetry {N : ℕ} (M : Mat N)
    (hM : ∀ i j, M i j = M j i) (β v : Vec N) :
    (∑ i, ∑ j, M i j * β i * v j) = ∑ i, ∑ j, M i j * β j * v i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hM j i]

theorem quadraticForm_line_expansion {N : ℕ} (M : Mat N)
    (hM : ∀ i j, M i j = M j i) (β v : Vec N) (t : ℝ) :
    quadraticForm M (β + t • v) = quadraticForm M β +
      t * quadraticGradient M β v + t ^ 2 * quadraticForm M v := by
  have hexpand : quadraticForm M (β + t • v) = quadraticForm M β +
      t * (∑ i, ∑ j, M i j * β i * v j) +
      t * (∑ i, ∑ j, M i j * β j * v i) + t ^ 2 * quadraticForm M v := by
    unfold quadraticForm
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand, quadratic_cross_symmetry M hM, quadraticGradient_apply]
  ring

end
end CriticalExtrapolation.Paper
