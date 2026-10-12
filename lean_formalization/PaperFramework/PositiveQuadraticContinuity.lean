import PaperFramework.Definitions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.Compact

namespace CriticalExtrapolation.Paper
open Filter Topology
open scoped BigOperators
noncomputable section

theorem quadraticForm_smul {N : ℕ} (M : Mat N) (a : ℝ) (p : Vec N) :
    quadraticForm M (a • p) = a ^ 2 * quadraticForm M p := by
  unfold quadraticForm
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem positiveQuadratic_of_unit_sphere {N : ℕ} (M : Mat N)
    (hM : ∀ p : Vec N, ‖p‖ = 1 → 0 < quadraticForm M p) : PositiveQuadratic M := by
  intro p hp
  have hnorm : 0 < ‖p‖ := norm_pos_iff.mpr hp
  let q : Vec N := ‖p‖⁻¹ • p
  have hqnorm : ‖q‖ = 1 := by
    dsimp [q]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm),
      inv_mul_cancel₀ hnorm.ne']
  have hq := hM q hqnorm
  have hpq : p = ‖p‖ • q := by
    simp only [q, smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
  rw [hpq, quadraticForm_smul]
  exact mul_pos (sq_pos_of_pos hnorm) hq

theorem positiveQuadratic_eventually {N : ℕ} (M : ℝ → Mat N) (c₀ : ℝ)
    (hcont : ∀ p : Vec N, ContinuousAt
      (fun z : ℝ × Vec N => quadraticForm (M z.1) z.2) (c₀, p))
    (hpos : PositiveQuadratic (M c₀)) :
    ∀ᶠ c in 𝓝 c₀, PositiveQuadratic (M c) := by
  have hcompact : IsCompact (Metric.sphere (0 : Vec N) 1) := isCompact_sphere _ _
  have hevent : ∀ᶠ c in 𝓝 c₀, ∀ p ∈ Metric.sphere (0 : Vec N) 1,
      0 < quadraticForm (M c) p := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro p hp
    have hnorm : ‖p‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hp
    have hpne : p ≠ 0 := by intro h; simp [h] at hnorm
    exact (hcont p).eventually (Ioi_mem_nhds (hpos p hpne))
  filter_upwards [hevent] with c hc
  apply positiveQuadratic_of_unit_sphere
  intro p hp
  exact hc p (by simpa only [Metric.mem_sphere, dist_zero_right] using hp)

end
end CriticalExtrapolation.Paper
