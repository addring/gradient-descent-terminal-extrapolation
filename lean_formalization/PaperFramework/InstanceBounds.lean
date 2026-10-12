import PaperFramework.Definitions
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

/-- Fermat's theorem at the specified global minimizer. -/
theorem instance_gradient_minimizer {d : ℕ} {L D : ℝ} (I : Instance d L D) :
    gradient I.f I.minimizer = 0 := by
  exact I.gradient_at_minimizer

theorem instance_gradient_bound {d : ℕ} {L D : ℝ} (I : Instance d L D)
    (x : Space d) : ‖gradient I.f x‖ ≤ L * ‖x - I.minimizer‖ := by
  simpa [instance_gradient_minimizer I] using I.gradient_lipschitz x I.minimizer

/-- A coarse bound valid for every real step, sufficient to bound the actual supremum. -/
theorem instance_iterate_radius_bound {d : ℕ} {L D : ℝ} (I : Instance d L D)
    (hL : 0 < L) (h : ℝ) (n : ℕ) :
    ‖iterate I h n - I.minimizer‖ ≤ (1 + |h|) ^ n * D := by
  induction n with
  | zero => simpa [iterate] using I.radius
  | succ n ih =>
    have hg := instance_gradient_bound I (iterate I h n)
    have hstep : |h / L| * ‖gradient I.f (iterate I h n)‖ ≤
        |h| * ‖iterate I h n - I.minimizer‖ := by
      calc
        _ ≤ |h / L| * (L * ‖iterate I h n - I.minimizer‖) :=
          mul_le_mul_of_nonneg_left hg (abs_nonneg _)
        _ = _ := by rw [abs_div, abs_of_pos hL]; field_simp
    calc
      _ = ‖(iterate I h n - I.minimizer) - (h / L) • gradient I.f (iterate I h n)‖ := by
        congr 1; simp only [iterate]; abel
      _ ≤ ‖iterate I h n - I.minimizer‖ +
          ‖(h / L) • gradient I.f (iterate I h n)‖ := norm_sub_le _ _
      _ ≤ (1 + |h|) * ‖iterate I h n - I.minimizer‖ := by
        rw [norm_smul, Real.norm_eq_abs]; nlinarith only [hstep]
      _ ≤ (1 + |h|) * ((1 + |h|) ^ n * D) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [pow_succ]; ring

theorem instance_output_gradient_bound {d : ℕ} {L D : ℝ} (I : Instance d L D)
    (hL : 0 < L) (N : ℕ) (h c : ℝ) :
    ‖gradient I.f (output I N h c)‖ ≤
      L * (D + |c| * ((1 + |h|) ^ N * D + D)) := by
  have hi : ‖iterate I h N - I.initial‖ ≤ (1 + |h|) ^ N * D + D := by
    calc
      _ = ‖(iterate I h N - I.minimizer) - (I.initial - I.minimizer)‖ := by
        congr 1; abel
      _ ≤ _ := norm_sub_le _ _
      _ ≤ _ := add_le_add (instance_iterate_radius_bound I hL h N) I.radius
  have hy : ‖output I N h c - I.minimizer‖ ≤
      D + |c| * ((1 + |h|) ^ N * D + D) := by
    calc
      _ = ‖(I.initial - I.minimizer) + c • (iterate I h N - I.initial)‖ := by
        congr 1; unfold output; abel
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add I.radius (mul_le_mul_of_nonneg_left hi (abs_nonneg _))
  exact (instance_gradient_bound I _).trans (mul_le_mul_of_nonneg_left hy hL.le)

/-- A constant function supplies an actual instance, including in dimension zero. -/
def constantInstance (d : ℕ) (L D : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D) : Instance d L D where
  f := fun _ => 0
  convex := convexOn_const 0 convex_univ
  differentiable := differentiable_const 0
  gradient_lipschitz := by intro x z; simp; positivity
  initial := 0
  minimizer := 0
  minimizes := by intro x; rfl
  radius := by simpa using hD

theorem constantInstance_gradient (d : ℕ) (L D : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (x : Space d) : gradient (constantInstance d L D hL hD).f x = 0 := by
  exact gradient_fun_const x 0

theorem actual_instance_values_nonempty_bounded (N : ℕ) (h c L D : ℝ)
    (hL : 0 < L) (hD : 0 < D) :
    ({r : ℝ | ∃ (d : ℕ) (I : Instance d L D),
      r = ‖gradient I.f (output I N h c)‖}).Nonempty ∧
    BddAbove {r : ℝ | ∃ (d : ℕ) (I : Instance d L D),
      r = ‖gradient I.f (output I N h c)‖} := by
  refine ⟨⟨0, 0, constantInstance 0 L D hL.le hD.le, ?_⟩,
    ⟨L * (D + |c| * ((1 + |h|) ^ N * D + D)), ?_⟩⟩
  · simp [constantInstance_gradient]
  · rintro r ⟨d, I, rfl⟩
    exact instance_output_gradient_bound I hL N h c

end
end CriticalExtrapolation.Paper
