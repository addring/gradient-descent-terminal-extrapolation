import PaperFramework.PlateauRecurrences

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem optimizer_coordinates_positive (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (hβ : IsOptimizer h c β) : ∀ i, 0 < β i :=
  feasible_coordinates_positive N h c hp hh β hβ.1

theorem flowEll_at_coordinate {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (i : Fin N) :
    flowEll h c β μ i.val = difference β i + scaledMu h c μ i.val / ((i.val : ℝ) + 1) := by
  simp only [flowEll, difference, zeroExtend_at]

theorem kkt_flowEll_positive (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i : Fin N) : 0 < flowEll h c β μ i.val := by
  rw [flowEll_at_coordinate]
  exact add_pos_of_pos_of_nonneg (kkt_strict_differences N h c hp hh β μ ν hkkt i)
    (div_nonneg (scaledMu_nonnegative N h c hp μ hkkt.mu_nonnegative i.val)
      (by positivity))

theorem flowProbability_boundary {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) :
    flowProbability h c β μ 0 = 1 ∧ flowProbability h c β μ N = 1 := by
  simp [flowProbability]

theorem kkt_flowProbability_le_one (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i : ℕ) (hi : i ≤ N) :
    flowProbability h c β μ i ≤ 1 := by
  by_cases hib : i = 0 ∨ i = N
  · simp [flowProbability, hib]
  · have hil : i < N := by omega
    have he := kkt_flowEll_positive N h c hp hh β μ ν hkkt ⟨i, hil⟩
    have hmu := scaledMu_nonnegative N h c hp μ hkkt.mu_nonnegative (i - 1)
    rw [flowProbability, if_neg hib]
    exact sub_le_self _ (div_nonneg hmu (mul_nonneg (Nat.cast_nonneg i) he.le))

theorem flowProbability_one_of_strict_slope {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν)
    (i j : Fin N) (hij : i.val + 1 = j.val)
    (hs : slope h c β j < slope h c β i) : flowProbability h c β μ j.val = 1 := by
  have hz := scaledMu_zero_of_strict_slope h c β μ ν hkkt i j hij hs
  have hj : j.val - 1 = i.val := by omega
  simp [flowProbability, hj, hz]

theorem flow_survival_complementarity {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν)
    (i j : Fin N) (hij : i.val + 1 = j.val) :
    (1 - flowProbability h c β μ j.val) * (slope h c β i - slope h c β j) = 0 := by
  have hle := hkkt.feasible.2.2 i j hij
  rcases lt_or_eq_of_le hle with hs | hs
  · rw [flowProbability_one_of_strict_slope h c β μ ν hkkt i j hij hs]
    ring
  · rw [hs]
    ring

/-- A positive edge stays within one slope plateau up to its last departing node. -/
theorem kkt_product_flow_support (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (β : Vec N) (hβ : IsOptimizer h c β)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν)
    (e : Edge N) (he : e ∈ edges N) (hF : 0 < kktProductFlow h c β μ e) :
    ∀ k : Fin N, e.1.val ≤ k.val → k.val < e.2.val → slope h c β k = slope h c β e.1 := by
  have hcomp : ∀ k ∈ Finset.Ioo e.1.val e.2.val,
      (1 - flowProbability h c β μ k) *
        (zeroExtend (slope h c β) (k - 1) - zeroExtend (slope h c β) k) = 0 := by
    intro k hk
    have hki := Finset.mem_Ioo.mp hk
    have hek := e.2.isLt
    let i : Fin N := ⟨k - 1, by omega⟩
    let j : Fin N := ⟨k, by omega⟩
    have hij : i.val + 1 = j.val := by dsimp [i, j]; omega
    have hc := flow_survival_complementarity h c β μ ν hkkt i j hij
    simpa only [← zeroExtend_at (slope h c β) i, ← zeroExtend_at (slope h c β) j] using hc
  have hs := positive_productFlow_support
    (fun i => 1 + (i : ℝ) * flowProbability h c β μ i)
    (flowProbability h c β μ) (zeroExtend (slope h c β)) e.1.val e.2.val hF hcomp
  intro k hik hkj
  simpa only [zeroExtend_at] using hs k.val hik hkj

end
end CriticalExtrapolation.Paper
