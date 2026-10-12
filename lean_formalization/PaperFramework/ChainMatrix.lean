import PaperFramework.TridiagonalQuadratic
import PaperFramework.TailEnergyIdentities

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem TEntry_apply {N : ℕ} (h c : ℝ) (β : Vec N) (i : Fin N) :
    (∑ j, TEntry h c i j * β j) = applyT h c β i := by
  have hprefix : (∑ j : Fin N, (if j < i then h else 0) * β j) =
      h * ∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), β j := by
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j < i <;> simp [hj]
  have hdiag : (∑ j : Fin N, (if i = j then (1 : ℝ) else 0) * β j) = β i := by
    simp [ite_mul]
  unfold TEntry applyT
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [hprefix, hdiag, ← Finset.mul_sum]

theorem DEntry_apply {N : ℕ} (β : Vec N) (i : Fin N) :
    (∑ j, DEntry i j * β j) = difference β i := by
  unfold DEntry difference
  simp_rw [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  rw [sum_fin_value_selector]
  simp

theorem quadraticForm_constant {N : ℕ} (r : ℝ) (β : Vec N) :
    quadraticForm (fun _ _ => r) β = r * (∑ i, β i) ^ 2 := by
  calc
    _ = ∑ i, β i * (r * ∑ j, β j) := by
      unfold quadraticForm
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem quadraticForm_scale {N : ℕ} (r : ℝ) (M : Mat N) (β : Vec N) :
    quadraticForm (fun i j => r * M i j) β = r * quadraticForm M β := by
  unfold quadraticForm
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadraticForm_sub {N : ℕ} (A B : Mat N) (β : Vec N) :
    quadraticForm (fun i j => A i j - B i j) β = quadraticForm A β - quadraticForm B β := by
  unfold quadraticForm
  simp_rw [sub_mul, Finset.sum_sub_distrib]

theorem quadraticForm_sum {N : ℕ} (M : Fin N → Mat N) (β : Vec N) :
    quadraticForm (fun i j => ∑ k, M k i j) β = ∑ k, quadraticForm (M k) β := by
  unfold quadraticForm
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ i, ∑ k, ∑ j, M k i j * β i * β j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem quadraticForm_rank_two {N : ℕ} (v w β : Vec N) :
    quadraticForm (fun i j => v i * w j + w i * v j) β =
      2 * (∑ i, v i * β i) * ∑ j, w j * β j := by
  have houter : ∀ v w : Vec N, (∑ i, ∑ j, v i * w j * β i * β j) =
      (∑ i, v i * β i) * ∑ j, w j * β j := by
    intro v w
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold quadraticForm
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [houter, houter]
  ring

theorem chain_flow_sum {N : ℕ} (w : Edge N → ℝ) :
    (∑ e ∈ edges N, chainFlow N e * w e) =
      ∑ i : Fin N, ((i.val : ℝ) + 1) * w (i, i.succ) := by
  unfold edges
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i.succ]
  · simp [chainFlow]
  · intro j _ hji
    have hval : j.val ≠ i.val + 1 := by
      intro h
      exact hji (Fin.ext h)
    simp [chainFlow, hval]
  · simp

theorem chain_basis_difference {N : ℕ} (k i : Fin N) :
    extendedBasis k.castSucc i - extendedBasis k.succ i = DEntry k i := by
  simp [extendedBasis, DEntry, Fin.ext_iff]

theorem chain_matrix_entries (N : ℕ) (h c : ℝ) (i j : Fin N) :
    M₀ N h c i j = h ^ 2 * c ^ 2 - h * c * S N h c *
      ∑ k, (((k.val : ℝ) + 1) / queryK N h c k) *
        (DEntry k i * TEntry h c k j + TEntry h c k i * DEntry k j) := by
  let g : Edge N → ℝ := fun e =>
    (extendedBasis e.1.castSucc i - extendedBasis e.2 i) * TEntry h c e.1 j +
      TEntry h c e.1 i * (extendedBasis e.1.castSucc j - extendedBasis e.2 j)
  have hsum : (∑ e ∈ edges N, (chainFlow N e / queryK N h c e.1) * g e) =
      ∑ k, (((k.val : ℝ) + 1) / queryK N h c k) *
        (DEntry k i * TEntry h c k j + TEntry h c k i * DEntry k j) := by
    calc
      _ = ∑ e ∈ edges N, chainFlow N e * (g e / queryK N h c e.1) := by
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = ∑ k, ((k.val : ℝ) + 1) * (g (k, k.succ) / queryK N h c k) := chain_flow_sum _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        dsimp only [g]
        rw [chain_basis_difference, chain_basis_difference]
        ring
  exact congrArg (fun x => h ^ 2 * c ^ 2 - h * c * S N h c * x) hsum

theorem chainObjective_matrix (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (β : Vec N) :
    chainObjective h c β = quadraticForm (M₀ N h c) β := by
  have hM : M₀ N h c = fun i j => h ^ 2 * c ^ 2 - h * c * S N h c *
      ∑ k, (((k.val : ℝ) + 1) / queryK N h c k) *
        (DEntry k i * TEntry h c k j + TEntry h c k i * DEntry k j) := by
    funext i j
    exact chain_matrix_entries N h c i j
  rw [hM, quadraticForm_sub, quadraticForm_constant, quadraticForm_scale, quadraticForm_sum]
  simp_rw [quadraticForm_scale, quadraticForm_rank_two, DEntry_apply, TEntry_apply]
  have hsum : (∑ k, (((k.val : ℝ) + 1) / queryK N h c k) *
      (2 * difference β k * applyT h c β k)) =
      2 * ∑ k, ((k.val : ℝ) + 1) * difference β k * slope h c β k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold slope
    ring
  rw [hsum]
  unfold chainObjective S
  ring

end
end CriticalExtrapolation.Paper
