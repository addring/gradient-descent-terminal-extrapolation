import PaperFramework.TailEnergyIdentities
import PaperFramework.TridiagonalQuadratic

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem energy_local_coefficients (N : ℕ) (a t : ℝ)
    (ha : 0 ≤ a) (ht : 1 ≤ t) (i : Fin N) (u v : ℝ) :
    -(energyF N a t) ^ 2 * u ^ 2 +
      2 * energyF N a t * (((i.val : ℝ) + 1) * (energyZeta N a t i.val - 2) * u * v) +
      2 * energyF N a t * (((i.val : ℝ) + 1) *
        (energyZeta N a t i.val * u - (energyZeta N a t i.val - 2) * v) *
          (t * (energyZeta N a t i.val - 1) / energyD N a i.val) * u) =
      (energyF N a t) ^ 2 * (energyDiagonal N a t i.val * u ^ 2 +
        2 * (energyNeighbor N a t i.val * u * v)) := by
  have hd := ne_of_gt (energyD_pos N a ha i)
  have hF := ne_of_gt (energyF_pos N a t ha ht)
  unfold energyDiagonal energyNeighbor
  simp only [energyZeta_eq_D_add]
  field_simp
  ring

/-- Equations (3.4)--(3.5), for every real vector and all admissible real parameters. -/
theorem tridiagonal_energy_identity (N : ℕ) (a t : ℝ)
    (hN : 0 < N) (ha : 0 ≤ a) (ht : 1 ≤ t) (p : Vec N) :
    homogeneousEnergy a t p = (energyF N a t) ^ 2 * quadraticForm (E N a t) (tailU a t p) := by
  let u := tailU a t p
  let F := energyF N a t
  let J := ∑ i, u i * tail u i.val
  let b : Vec N := fun i => ((i.val : ℝ) + 1) * (energyZeta N a t i.val - 2) *
    u i * zeroExtend u (i.val + 1)
  let v : Vec N := fun i => ((i.val : ℝ) + 1) * difference p i *
    (t * (energyZeta N a t i.val - 1) / energyD N a i.val) * u i
  have hsum : (∑ i, p i) = F * ∑ i, u i := (tail_transform_recovery N a t hN ha ht p).2
  have hparts : (∑ i, ((i.val : ℝ) + 1) * difference p i * tail u i.val) =
      F * J - ∑ i, b i := weighted_difference_tail_identity N a t hN ha ht p
  have hsquare : (∑ i, u i) ^ 2 = 2 * J - ∑ i, (u i) ^ 2 := by
    have h := sum_mul_tail_finite u
    change 2 * J = _ at h
    linarith
  have hterms : (∑ i, ((i.val : ℝ) + 1) * difference p i *
      (tail p i.val - t * p i) / energyD N a i.val) = F * J - (∑ i, b i) - ∑ i, v i := by
    calc
      _ = ∑ i, (((i.val : ℝ) + 1) * difference p i * tail u i.val - v i) := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = ((i.val : ℝ) + 1) * difference p i *
              ((tail p i.val - t * p i) / energyD N a i.val) := by ring
          _ = _ := by
            rw [energy_factor_transformed N a t hN ha ht p i]
            dsimp only [v, u]
            ring
      _ = _ := by rw [Finset.sum_sub_distrib, hparts]
  have henergy : homogeneousEnergy a t p =
      -F ^ 2 * (∑ i, (u i) ^ 2) + 2 * F * (∑ i, b i) + 2 * F * ∑ i, v i := by
    unfold homogeneousEnergy
    rw [hsum, hterms, mul_pow, hsquare]
    change F ^ 2 * (2 * J - ∑ i, (u i) ^ 2) - 2 * F *
      (F * J - (∑ i, b i) - ∑ i, v i) = _
    ring
  have hpoint : ∀ i : Fin N, -F ^ 2 * (u i) ^ 2 + 2 * F * b i + 2 * F * v i =
      F ^ 2 * (energyDiagonal N a t i.val * (u i) ^ 2 +
        2 * (energyNeighbor N a t i.val * u i * zeroExtend u (i.val + 1))) := by
    intro i
    dsimp only [b, v, F]
    rw [tail_transform_difference N a t hN ha ht p i]
    exact energy_local_coefficients N a t ha ht i (u i) (zeroExtend u (i.val + 1))
  calc
    homogeneousEnergy a t p =
        ∑ i, (-F ^ 2 * (u i) ^ 2 + 2 * F * b i + 2 * F * v i) := by
      rw [henergy]
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = ∑ i, F ^ 2 * (energyDiagonal N a t i.val * (u i) ^ 2 +
        2 * (energyNeighbor N a t i.val * u i * zeroExtend u (i.val + 1))) :=
      Finset.sum_congr rfl (fun i _ => hpoint i)
    _ = F ^ 2 * quadraticForm (E N a t) u := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← energy_quadratic_neighbors]

end
end CriticalExtrapolation.Paper
