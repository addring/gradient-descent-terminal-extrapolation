import PaperFramework.ConjugatePotential

namespace CriticalExtrapolation.Paper
noncomputable section

/-- The intercept required for general function values, absent from the special data formula. -/
def interpolationIntercept {N d : ℕ} (data : Sample N d) (i : Query N) : ℝ :=
  inner ℝ (data.g i) (data.x i) - ‖data.g i‖ ^ 2 / 2 - data.value i

def fullConjugateAffineMaximum {N d : ℕ} (data : Sample N d) (u : Space d) : ℝ :=
  (Finset.univ : Finset (Query N)).sup' Finset.univ_nonempty
    (fun i => inner ℝ (data.x i - data.g i) (u - data.g i) + interpolationIntercept data i)

def fullConjugatePotential {N d : ℕ} (data : Sample N d) (u : Space d) : ℝ :=
  ‖u‖ ^ 2 / 2 + fullConjugateAffineMaximum data u

def fullRecoveredFunction {N d : ℕ} (data : Sample N d) (x : Space d) : ℝ :=
  sSup {r | ∃ u, r = inner ℝ x u - fullConjugatePotential data u}

def FullConjugateMinimizer {N d : ℕ} (data : Sample N d) (x u : Space d) : Prop :=
  ∀ v, fullConjugatePotential data u - inner ℝ x u ≤ fullConjugatePotential data v - inner ℝ x v

theorem fullConjugateAffineMaximum_continuous {N d : ℕ} (data : Sample N d) :
    Continuous (fullConjugateAffineMaximum data) := by
  classical
  unfold fullConjugateAffineMaximum
  apply Continuous.finset_sup'_apply
  intro i _
  fun_prop

theorem fullConjugateAffineMaximum_convex {N d : ℕ} (data : Sample N d) :
    ConvexOn ℝ Set.univ (fullConjugateAffineMaximum data) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change fullConjugateAffineMaximum data (a • x + b • y) ≤
    a * fullConjugateAffineMaximum data x + b * fullConjugateAffineMaximum data y
  unfold fullConjugateAffineMaximum
  apply Finset.sup'_le
  intro i _
  have hid : inner ℝ (data.x i - data.g i) (a • x + b • y - data.g i) +
      interpolationIntercept data i =
    a * (inner ℝ (data.x i - data.g i) (x - data.g i) + interpolationIntercept data i) +
    b * (inner ℝ (data.x i - data.g i) (y - data.g i) + interpolationIntercept data i) := by
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
    linear_combination (congrArg (fun r : ℝ => r *
      (inner ℝ (data.x i - data.g i) (data.g i) - interpolationIntercept data i)) hab)
  rw [hid]
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (Finset.le_sup' (fun j : Query N => inner ℝ (data.x j - data.g j) (x - data.g j) +
        interpolationIntercept data j) (Finset.mem_univ i)) ha)
    (mul_le_mul_of_nonneg_left
      (Finset.le_sup' (fun j : Query N => inner ℝ (data.x j - data.g j) (y - data.g j) +
        interpolationIntercept data j) (Finset.mem_univ i)) hb)

theorem fullConjugatePotential_continuous {N d : ℕ} (data : Sample N d) :
    Continuous (fullConjugatePotential data) := by
  exact (by fun_prop : Continuous (fun u : Space d => ‖u‖ ^ 2 / 2)).add
    (fullConjugateAffineMaximum_continuous data)

theorem fullConjugatePotential_strongConvex {N d : ℕ} (data : Sample N d) :
    StrongConvexOn Set.univ 1 (fullConjugatePotential data) := by
  apply strongConvexOn_iff_convex.mpr
  convert fullConjugateAffineMaximum_convex data using 1
  funext u
  unfold fullConjugatePotential
  ring

theorem full_conjugate_minimizer_recovered_value {N d : ℕ} (data : Sample N d)
    (x u : Space d) (hu : FullConjugateMinimizer data x u) :
    fullRecoveredFunction data x = inner ℝ x u - fullConjugatePotential data u := by
  have hbdd : BddAbove {r | ∃ v, r = inner ℝ x v - fullConjugatePotential data v} := by
    refine ⟨inner ℝ x u - fullConjugatePotential data u, ?_⟩
    rintro r ⟨v, rfl⟩
    have hv := hu v
    linarith
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨inner ℝ x u - fullConjugatePotential data u, u, rfl⟩
    · rintro r ⟨v, rfl⟩
      have hv := hu v
      linarith
  · exact le_csSup hbdd ⟨u, rfl⟩

end
end CriticalExtrapolation.Paper
