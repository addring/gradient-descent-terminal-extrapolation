import PaperFramework.Definitions

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem vec2_inner (a b c d : ℝ) : inner ℝ (vec2 a b) (vec2 c d) = a * c + b * d := by
  simp [vec2, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two]
  <;> ring

theorem vec2_norm_sq (a b : ℝ) : ‖vec2 a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, vec2_inner]
  ring

theorem vec2_add (a b c d : ℝ) : vec2 a b + vec2 c d = vec2 (a + c) (b + d) := by
  ext k
  fin_cases k <;> simp [vec2]

theorem vec2_sub (a b c d : ℝ) : vec2 a b - vec2 c d = vec2 (a - c) (b - d) := by
  ext k
  fin_cases k <;> simp [vec2]

theorem vec2_smul (r a b : ℝ) : r • vec2 a b = vec2 (r * a) (r * b) := by
  ext k
  fin_cases k <;> simp [vec2]

theorem vec2_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, vec2 (a i) (b i)) = vec2 (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext k; fin_cases k <;> simp [vec2]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, ih, vec2_add]

end
end CriticalExtrapolation.Paper
