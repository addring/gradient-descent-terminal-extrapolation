import PaperFramework.QPUniform

namespace CriticalExtrapolation.Paper
open scoped BigOperators
open Filter Topology
noncomputable section

/-- The normalized affine perturbation of the uniform vector. -/
def uniformPerturbation (N : ℕ) (η : ℝ) : Vec N :=
  (1 - η) • uniformDirection N + η • descendingDirection N

theorem continuous_uniformPerturbation (N : ℕ) : Continuous (uniformPerturbation N) := by
  unfold uniformPerturbation
  fun_prop

theorem uniformPerturbation_normalized (N : ℕ) (hN : 0 < N) (η : ℝ) :
    (∑ i, uniformPerturbation N η i) = 1 := by
  simp only [uniformPerturbation, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, uniform_normalized N hN,
    descending_normalized N hN]
  ring

theorem uniformPerturbation_differences_positive (N : ℕ) (hN : 0 < N) (η : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) (i : Fin N) :
    0 < difference (uniformPerturbation N η) i := by
  rw [uniformPerturbation, difference_mix, descending_difference]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr hη1) (uniform_difference_nonnegative N hN i))
    (mul_pos hη (one_div_pos.mpr (descendingMass_positive N hN)))

theorem uniformPerturbation_slopes_eventually (N : ℕ) (h c : ℝ) (hp : Parameters N h c) :
    ∀ᶠ η : ℝ in 𝓝 0, ∀ i j : Fin N, i.val + 1 = j.val →
      slope h c (uniformPerturbation N η) j < slope h c (uniformPerturbation N η) i := by
  simp only [Filter.eventually_all]
  intro i j hij
  apply ((continuous_slope h c j).comp (continuous_uniformPerturbation N)).continuousAt.eventually_lt
    ((continuous_slope h c i).comp (continuous_uniformPerturbation N)).continuousAt
  simpa [uniformPerturbation] using uniform_slopes_strict N h c hp i j hij

theorem strictly_feasible_direction_exists (N : ℕ) (h c : ℝ) (hp : Parameters N h c) :
    ∃ β : Vec N, StrictlyFeasible h c β := by
  have hpos : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  have hlt : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have horder := (uniformPerturbation_slopes_eventually N h c hp).filter_mono
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  obtain ⟨η, hη, hη1, hs⟩ := (hpos.and (hlt.and horder)).exists
  exact ⟨uniformPerturbation N η, uniformPerturbation_normalized N hp.n_pos η,
    uniformPerturbation_differences_positive N hp.n_pos η hη hη1.le, hs⟩

theorem strictlyFeasible_feasible {N : ℕ} (h c : ℝ) (β : Vec N)
    (hβ : StrictlyFeasible h c β) : Feasible h c β :=
  ⟨hβ.1, fun i => (hβ.2.1 i).le, fun i j hij => (hβ.2.2 i j hij).le⟩

end
end CriticalExtrapolation.Paper
