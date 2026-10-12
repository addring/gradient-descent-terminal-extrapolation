import PaperFramework.QuadraticVariation

namespace CriticalExtrapolation.Paper
open scoped BigOperators
open Filter Topology
noncomputable section

theorem finite_constraints_feasible_ray {E ι : Type*} [AddCommGroup E]
    [Module ℝ E] [Fintype ι] (A : ι → E →ₗ[ℝ] ℝ) (β v : E)
    (hβ : ∀ i, 0 ≤ A i β) (hv : ∀ i, A i β = 0 → 0 ≤ A i v) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ i, 0 ≤ A i (β + t • v) := by
  classical
  rw [Filter.eventually_all]
  intro i
  by_cases hi : A i β = 0
  · have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    filter_upwards [ht] with t ht
    simpa only [map_add, map_smul, smul_eq_mul, hi, zero_add] using mul_nonneg ht.le (hv i hi)
  · have hi' : 0 < A i β := lt_of_le_of_ne (hβ i) (Ne.symm hi)
    have hc : Continuous (fun t : ℝ => A i (β + t • v)) := by
      simp only [map_add, map_smul, smul_eq_mul]
      fun_prop
    have he : ∀ᶠ t : ℝ in 𝓝 0, 0 < A i (β + t • v) :=
      continuousAt_const.eventually_lt hc.continuousAt (by simpa using hi')
    exact (he.filter_mono nhdsWithin_le_nhds).mono (fun _ h => h.le)

/-- One-sided optimality on every ray satisfying the active linear inequalities. -/
theorem finite_qp_first_order {N : ℕ} {ι : Type*} [Fintype ι]
    (M : Mat N) (hM : ∀ i j, M i j = M j i)
    (ℓ : Vec N →ₗ[ℝ] ℝ) (A : ι → Vec N →ₗ[ℝ] ℝ) (β : Vec N)
    (hℓ : ℓ β = 1) (hβ : ∀ i, 0 ≤ A i β)
    (hmin : ∀ p, ℓ p = 1 → (∀ i, 0 ≤ A i p) → quadraticForm M β ≤ quadraticForm M p)
    (v : Vec N) (hzero : ℓ v = 0) (hv : ∀ i, A i β = 0 → 0 ≤ A i v) :
    0 ≤ quadraticGradient M β v := by
  by_contra hnot
  have hg : quadraticGradient M β v < 0 := lt_of_not_ge hnot
  have hc : Continuous (fun t : ℝ => quadraticGradient M β v + t * quadraticForm M v) := by
    fun_prop
  have hneg : ∀ᶠ t : ℝ in 𝓝 0, quadraticGradient M β v + t * quadraticForm M v < 0 :=
    hc.continuousAt.eventually_lt continuousAt_const (by simpa using hg)
  have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hneg' := hneg.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hfeasible := finite_constraints_feasible_ray A β v hβ hv
  obtain ⟨t, ht, hneg, hfeasible⟩ := (ht.and (hneg'.and hfeasible)).exists
  have hnorm : ℓ (β + t • v) = 1 := by simp only [map_add, map_smul, hℓ, hzero, smul_zero, add_zero]
  have hbound := hmin (β + t • v) hnorm hfeasible
  rw [quadraticForm_line_expansion M hM] at hbound
  have hproduct := mul_neg_of_pos_of_neg ht hneg
  nlinarith

end
end CriticalExtrapolation.Paper
