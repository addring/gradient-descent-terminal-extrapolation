import PaperFramework.QPExistence
import PaperFramework.QPValue

namespace CriticalExtrapolation.Paper
open scoped BigOperators
open Filter Topology
noncomputable section

theorem feasible_mix_strict {N : ℕ} (h c : ℝ) (β γ : Vec N)
    (hβ : Feasible h c β) (hγ : StrictlyFeasible h c γ) (η : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    StrictlyFeasible h c ((1 - η) • β + η • γ) := by
  refine ⟨?_, ?_, ?_⟩
  · change (∑ i, ((1 - η) * β i + η * γ i)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hβ.1, hγ.1]
    ring
  · intro i
    rw [difference_mix]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr hη1) (hβ.2.1 i)) (mul_pos hη (hγ.2.1 i))
  · intro i j hij
    rw [slope_mix, slope_mix]
    exact add_lt_add_of_le_of_lt
      (mul_le_mul_of_nonneg_left (hβ.2.2 i j hij) (sub_nonneg.mpr hη1))
      (mul_lt_mul_of_pos_left (hγ.2.2 i j hij) hη)

theorem feasible_negative_has_strict_negative (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (hβ : Feasible h c β) (hQ : chainObjective h c β < 0) :
    ∃ γ : Vec N, StrictlyFeasible h c γ ∧ chainObjective h c γ < 0 := by
  obtain ⟨γ, hγ⟩ := strictly_feasible_direction_exists N h c hp
  have hcQ : Continuous (fun η : ℝ => chainObjective h c ((1 - η) • β + η • γ)) :=
    (continuous_chainObjective N h c).comp (by fun_prop)
  have hnegative : ∀ᶠ η : ℝ in 𝓝 0, chainObjective h c ((1 - η) • β + η • γ) < 0 :=
    hcQ.continuousAt.eventually_lt continuousAt_const (by simpa using hQ)
  have hpos : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  have hlt : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hnegative' := hnegative.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  obtain ⟨η, hη, hη1, hneg⟩ := (hpos.and (hlt.and hnegative')).exists
  exact ⟨(1 - η) • β + η • γ, feasible_mix_strict h c β γ hβ hγ η hη hη1.le, hneg⟩

theorem negative_optimizer_has_strict_negative_direction (N : ℕ) (h c : ℝ)
    (hp : Parameters N h c) (hΦ : auxiliaryValue N h c < 0) :
    ∃ β : Vec N, StrictlyFeasible h c β ∧ chainObjective h c β < 0 := by
  obtain ⟨β, hβ, _⟩ := optimizer_exists_unique N h c hp
  rw [auxiliaryValue_attained N h c hp β hβ] at hΦ
  exact feasible_negative_has_strict_negative N h c hp β hβ.1 hΦ

end
end CriticalExtrapolation.Paper
