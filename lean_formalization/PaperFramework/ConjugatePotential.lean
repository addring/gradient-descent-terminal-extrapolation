import PaperFramework.ConjugateBasics
import Mathlib.Analysis.Convex.Strong
import Mathlib.Topology.Order.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Finset

namespace CriticalExtrapolation.Paper
noncomputable section

def conjugateAffineMaximum {N d : ℕ} (data : Sample N d) (u : Space d) : ℝ :=
  (Finset.univ : Finset (Query N)).sup' Finset.univ_nonempty
    (fun i => inner ℝ (data.x i - data.g i) (u - data.g i))

theorem conjugateAffineMaximum_eq_sup {N d : ℕ} (data : Sample N d) (u : Space d) :
    conjugateAffineMaximum data u =
      sSup {r : ℝ | ∃ i, r = inner ℝ (data.x i - data.g i) (u - data.g i)} := by
  classical
  unfold conjugateAffineMaximum
  rw [Finset.sup'_eq_csSup_image]
  congr 1
  ext r
  simp only [Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and, Set.mem_setOf_eq]
  exact exists_congr (fun _ => eq_comm)

theorem conjugateAffineMaximum_continuous {N d : ℕ} (data : Sample N d) :
    Continuous (conjugateAffineMaximum data) := by
  classical
  unfold conjugateAffineMaximum
  apply Continuous.finset_sup'_apply
  intro i _
  fun_prop

theorem conjugateAffineMaximum_convex {N d : ℕ} (data : Sample N d) :
    ConvexOn ℝ Set.univ (conjugateAffineMaximum data) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change conjugateAffineMaximum data (a • x + b • y) ≤
    a * conjugateAffineMaximum data x + b * conjugateAffineMaximum data y
  unfold conjugateAffineMaximum
  apply Finset.sup'_le
  intro i _
  have hid : inner ℝ (data.x i - data.g i) (a • x + b • y - data.g i) =
      a * inner ℝ (data.x i - data.g i) (x - data.g i) +
        b * inner ℝ (data.x i - data.g i) (y - data.g i) := by
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
    linear_combination (congrArg (fun r : ℝ => r * inner ℝ (data.x i - data.g i) (data.g i)) hab)
  rw [hid]
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (Finset.le_sup' (fun j : Query N => inner ℝ (data.x j - data.g j) (x - data.g j))
        (Finset.mem_univ i)) ha)
    (mul_le_mul_of_nonneg_left
      (Finset.le_sup' (fun j : Query N => inner ℝ (data.x j - data.g j) (y - data.g j))
        (Finset.mem_univ i)) hb)

theorem conjugatePotential_continuous {N d : ℕ} (data : Sample N d) :
    Continuous (conjugatePotential data) := by
  have hnorm : Continuous (fun u : Space d => ‖u‖ ^ 2 / 2) := by fun_prop
  convert hnorm.add (conjugateAffineMaximum_continuous data) using 1
  funext u
  rw [conjugatePotential, conjugateAffineMaximum_eq_sup]

theorem conjugatePotential_strongConvex {N d : ℕ} (data : Sample N d) :
    StrongConvexOn Set.univ 1 (conjugatePotential data) := by
  apply strongConvexOn_iff_convex.mpr
  convert conjugateAffineMaximum_convex data using 1
  funext u
  rw [conjugatePotential, conjugateAffineMaximum_eq_sup]
  ring

end
end CriticalExtrapolation.Paper
