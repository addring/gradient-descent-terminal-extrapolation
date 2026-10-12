import PaperFramework.Definitions
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.LinearAlgebra.Pi

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- Finite linear inequalities with a strictly positive direction admit nonnegative
multiplier representations. This will be applied to the active QP constraints. -/
theorem nonnegative_multiplier_representation {E ι : Type*} [AddCommGroup E]
    [Module ℝ E] [Fintype ι] (A : E →ₗ[ℝ] (ι → ℝ)) (g : E →ₗ[ℝ] ℝ)
    (hpositive : ∀ x, (∀ i, 0 ≤ A x i) → 0 ≤ g x)
    (hstrict : ∃ d, ∀ i, 0 < A d i) :
    ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ ∀ x, g x = ∑ i, μ i * A x i := by
  classical
  obtain ⟨d, hd⟩ := hstrict
  have hfactor : ∀ x y, A x = A y → g x = g y := by
    intro x y hxy
    have h₁ := hpositive (x - y) (by simp [map_sub, hxy])
    have h₂ := hpositive (y - x) (by simp [map_sub, hxy])
    simp only [map_sub] at h₁ h₂
    linarith
  choose preimage hpreimage using (fun y : LinearMap.range A => y.property)
  let f : LinearMap.range A →ₗ[ℝ] ℝ := {
    toFun := fun y => g (preimage y)
    map_add' := by
      intro x y
      calc
        g (preimage (x + y)) = g (preimage x + preimage y) :=
          hfactor _ _ (by simp only [map_add, hpreimage]; rfl)
        _ = _ := g.map_add _ _
    map_smul' := by
      intro a x
      calc
        g (preimage (a • x)) = g (a • preimage x) :=
          hfactor _ _ (by simp only [map_smul, hpreimage]; rfl)
        _ = _ := g.map_smul _ _ }
  let p : (ι → ℝ) →ₗ.[ℝ] ℝ := ⟨LinearMap.range A, f⟩
  let C : ConvexCone ℝ (ι → ℝ) := {
    carrier := {v | ∀ i, 0 ≤ v i}
    smul_mem' := fun a ha v hv i => mul_nonneg ha.le (hv i)
    add_mem' := fun v hv w hw i => add_nonneg (hv i) (hw i) }
  have hp : ∀ y : p.domain, (y : ι → ℝ) ∈ C → 0 ≤ p y := by
    intro y hy
    exact hpositive (preimage y) (by simpa only [hpreimage] using hy)
  have hdense : ∀ y : ι → ℝ, ∃ x : p.domain, (x : ι → ℝ) + y ∈ C := by
    intro y
    obtain ⟨M, hM⟩ := Finite.bddAbove_range (fun i => -y i / A d i)
    refine ⟨⟨A (M • d), LinearMap.mem_range_self A _⟩, ?_⟩
    intro i
    have hi := (div_le_iff₀ (hd i)).mp (hM (Set.mem_range_self i))
    change 0 ≤ A (M • d) i + y i
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    linarith
  obtain ⟨G, hagree, hnonnegative⟩ := riesz_extension C p hp hdense
  let μ : ι → ℝ := fun i => G (Pi.single i 1)
  have hμ : ∀ i, 0 ≤ μ i := by
    intro i
    apply hnonnegative
    intro j
    by_cases hji : j = i <;> simp [Pi.single_apply, hji]
  have hG : ∀ v : ι → ℝ, G v = ∑ i, μ i * v i := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have heq : (Pi.single i (v i) : ι → ℝ) = v i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
      ext j
      by_cases hij : i = j <;> simp [Pi.single_apply, hij]
    rw [heq, map_smul]
    change v i * μ i = μ i * v i
    ring
  refine ⟨μ, hμ, fun x => ?_⟩
  have hx := hagree ⟨A x, LinearMap.mem_range_self A x⟩
  have hpx : p ⟨A x, LinearMap.mem_range_self A x⟩ = g x :=
    hfactor _ _ (hpreimage ⟨A x, LinearMap.mem_range_self A x⟩)
  rw [hpx] at hx
  exact hx.symm.trans (hG (A x))

end
end CriticalExtrapolation.Paper
