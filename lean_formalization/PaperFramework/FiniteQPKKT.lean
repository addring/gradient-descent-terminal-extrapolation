import PaperFramework.FiniteQPFirstOrder
import PaperFramework.FarkasMultipliers

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- Full KKT for a symmetric quadratic objective on one normalized affine space and
a finite family of linear inequalities, with a strictly feasible normalized point. -/
theorem finite_qp_kkt {N : ℕ} {ι : Type*} [Fintype ι]
    (M : Mat N) (hM : ∀ i j, M i j = M j i)
    (ℓ : Vec N →ₗ[ℝ] ℝ) (A : ι → Vec N →ₗ[ℝ] ℝ) (β γ : Vec N)
    (hℓ : ℓ β = 1) (hβ : ∀ i, 0 ≤ A i β)
    (hγℓ : ℓ γ = 1) (hγ : ∀ i, 0 < A i γ)
    (hmin : ∀ p, ℓ p = 1 → (∀ i, 0 ≤ A i p) → quadraticForm M β ≤ quadraticForm M p) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∀ i, w i * A i β = 0) ∧
      ∀ v, quadraticGradient M β v =
        2 * quadraticForm M β * ℓ v + ∑ i, w i * A i v := by
  classical
  let I := {i : ι // A i β = 0}
  let A₀ : LinearMap.ker ℓ →ₗ[ℝ] (I → ℝ) :=
    LinearMap.pi (fun i => (A i.val).comp (LinearMap.ker ℓ).subtype)
  let g₀ : LinearMap.ker ℓ →ₗ[ℝ] ℝ :=
    (quadraticGradient M β).comp (LinearMap.ker ℓ).subtype
  have hpositive : ∀ v, (∀ i, 0 ≤ A₀ v i) → 0 ≤ g₀ v := by
    intro v hv
    exact finite_qp_first_order M hM ℓ A β hℓ hβ hmin v.val
      (LinearMap.mem_ker.mp v.property) (fun i hi => hv ⟨i, hi⟩)
  have hstrict : ∃ d, ∀ i, 0 < A₀ d i := by
    refine ⟨⟨γ - β, ?_⟩, ?_⟩
    · change ℓ (γ - β) = 0
      simp only [map_sub, hγℓ, hℓ, sub_self]
    · intro i
      change 0 < A i.val (γ - β)
      rw [map_sub, i.property, sub_zero]
      exact hγ i.val
  obtain ⟨μ, hμ, hrepresentation⟩ := nonnegative_multiplier_representation A₀ g₀ hpositive hstrict
  let w : ι → ℝ := fun i => if hi : A i β = 0 then μ ⟨i, hi⟩ else 0
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    by_cases hi : A i β = 0
    · simpa only [w, dif_pos hi] using hμ ⟨i, hi⟩
    · simp [w, hi]
  have hcomp : ∀ i, w i * A i β = 0 := by
    intro i
    by_cases hi : A i β = 0 <;> simp [w, hi]
  have hsum : ∀ v : Vec N, (∑ i : I, μ i * A i.val v) = ∑ i, w i * A i v := by
    intro v
    calc
      _ = ∑ i : I, w i.val * A i.val v := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [w, dif_pos i.property]
        rfl
      _ = ∑ i ∈ Finset.univ.filter (fun i => A i β = 0), w i * A i v :=
        (Finset.sum_subtype (p := fun i => A i β = 0) (Finset.univ.filter (fun i : ι => A i β = 0))
          (fun i => by simp) (fun i => w i * A i v)).symm
      _ = _ := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : A i β = 0 <;> simp [w, hi]
  have hrepzero : ∀ v : Vec N, ℓ v = 0 →
      quadraticGradient M β v = ∑ i, w i * A i v := by
    intro v hv
    have heq := hrepresentation ⟨v, hv⟩
    change quadraticGradient M β v = ∑ i : I, μ i * A i.val v at heq
    exact heq.trans (hsum v)
  refine ⟨w, hw, hcomp, ?_⟩
  intro v
  have hvzero : ℓ (v - ℓ v • β) = 0 := by
    simp only [map_sub, map_smul, hℓ, smul_eq_mul, mul_one, sub_self]
  have heq := hrepzero (v - ℓ v • β) hvzero
  have hsumzero : (∑ i, w i * A i (v - ℓ v • β)) = ∑ i, w i * A i v := by
    apply Finset.sum_congr rfl
    intro i _
    rw [map_sub, map_smul, smul_eq_mul]
    calc
      _ = w i * A i v - ℓ v * (w i * A i β) := by ring
      _ = _ := by rw [hcomp]; ring
  rw [map_sub, map_smul, smul_eq_mul, quadraticGradient_self, hsumzero] at heq
  nlinarith

end
end CriticalExtrapolation.Paper

