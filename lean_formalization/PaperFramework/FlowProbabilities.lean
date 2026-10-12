import PaperFramework.FlowProbabilityPreparation

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem slope_plateau_exists {N : ℕ} (h c : ℝ) (β : Vec N)
    (hβ : Feasible h c β) (k : Fin N) :
    ∃ a b : Fin N, a ≤ k ∧ k ≤ b ∧ IsMaximalSlopePlateau h c β a b := by
  classical
  let s := Finset.univ.filter (fun i : Fin N => slope h c β i = slope h c β k)
  have hkmem : k ∈ s := by simp [s]
  have hs : s.Nonempty := ⟨k, hkmem⟩
  let a := s.min' hs
  let b := s.max' hs
  have hamem : a ∈ s := Finset.min'_mem s hs
  have hbmem : b ∈ s := Finset.max'_mem s hs
  have haeq : slope h c β a = slope h c β k := (Finset.mem_filter.mp hamem).2
  have hbeq : slope h c β b = slope h c β k := (Finset.mem_filter.mp hbmem).2
  have hak : a ≤ k := Finset.min'_le s k hkmem
  have hkb : k ≤ b := Finset.le_max' s k hkmem
  have hmono := feasible_slopes_antitone h c β hβ
  refine ⟨a, b, hak, hkb, le_trans hak hkb, ?_, ?_, ?_⟩
  · intro i hai hib
    exact le_antisymm (hmono hai) (by rw [haeq, ← hbeq]; exact hmono hib)
  · intro i hia
    have hia' : i < a := by change i.val < a.val; omega
    apply lt_of_le_of_ne (hmono hia'.le)
    intro heq
    have himem : i ∈ s := by simp [s, ← haeq, heq]
    exact (not_le_of_gt hia') (Finset.min'_le s i himem)
  · intro i hbi
    have hbi' : b < i := by change b.val < i.val; omega
    apply lt_of_le_of_ne (hmono hbi'.le)
    intro heq
    have himem : i ∈ s := by simp [s, heq, hbeq]
    exact (not_le_of_gt hbi') (Finset.le_max' s i himem)

theorem plateau_probabilityNumerator_nonnegative (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (hh : h < 1) (hsize : 1 ≤ (N : ℝ) * h ^ 2) (hΦ : 0 ≤ auxiliaryValue N h c)
    (β : Vec N) (hβ : IsOptimizer h c β) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (a b : Fin N)
    (hplateau : IsMaximalSlopePlateau h c β a b) :
    ∀ i, a ≤ i → i ≤ b → 0 ≤ probabilityNumerator h c β μ i := by
  obtain ⟨haμ, hbμ⟩ := plateau_boundary_multipliers h c β μ ν hkkt a b hplateau
  have ha : 0 ≤ probabilityNumerator h c β μ a := by
    unfold probabilityNumerator
    rw [haμ, sub_zero]
    exact mul_nonneg (Nat.cast_nonneg a.val) (kkt_row_moments_positive N h c hp hh β μ ν hkkt a).le
  have hbd : difference β b ≤ rowMoment h c β μ b := by
    by_cases hb : b.val + 1 < N
    · exact nonterminal_plateau_endpoint N h c hp hh β hβ μ ν hkkt a b hplateau hb
    · have hb' : b.val + 1 = N := by omega
      have ht := terminal_plateau_endpoint N h c hp hh hsize hΦ β hβ μ ν hkkt b hb'
      simpa [difference, zeroExtend, hb'] using ht.le
  have hb : 0 ≤ probabilityNumerator h c β μ b := by
    have heq : probabilityNumerator h c β μ b =
        ((b.val : ℝ) + 1) * (rowMoment h c β μ b - difference β b) := by
      unfold probabilityNumerator rowMoment
      rw [hbμ]
      ring
    rw [heq]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hbd)
  apply interval_nonnegative_of_no_local_minimum _ a b hplateau.1 ha hb
  intro p i j hap hjb hpi hij hle
  have hpi' : p ≤ i := by change p.val ≤ i.val; omega
  have hij' : i ≤ j := by change i.val ≤ j.val; omega
  have hip := hplateau.2.1 p hap (le_trans hpi' (le_trans hij' hjb))
  have hii := hplateau.2.1 i (le_trans hap hpi') (le_trans hij' hjb)
  have hijj := hplateau.2.1 j (le_trans hap (le_trans hpi' hij')) hjb
  exact probabilityNumerator_no_local_minimum N h c hp hh β μ ν hkkt p i j hpi hij
    (hip.trans hii.symm) (hii.trans hijj.symm) hle

/-- Both plateau endpoint estimates control every interior probability. -/
theorem kkt_probabilities_in_unit_interval (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (hsize : 1 ≤ (N : ℝ) * h ^ 2) (hΦ : 0 ≤ auxiliaryValue N h c)
    (β : Vec N) (hβ : IsOptimizer h c β)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) (hkkt : CompleteKKT h c β μ ν) :
    ∀ i ≤ N, flowProbability h c β μ i ∈ Set.Icc (0 : ℝ) 1 := by
  intro i hi
  refine ⟨?_, kkt_flowProbability_le_one N h c hp hh β μ ν hkkt i hi⟩
  by_cases hiN : i = N
  · simp [hiN, flowProbability]
  · let k : Fin N := ⟨i, by omega⟩
    obtain ⟨a, b, hak, hkb, hplateau⟩ := slope_plateau_exists h c β hkkt.feasible k
    exact flowProbability_nonnegative_of_numerator N h c hp hh β μ ν hkkt k
      (plateau_probabilityNumerator_nonnegative N h c hp hh hsize hΦ β hβ μ ν hkkt
        a b hplateau k hak hkb)

end
end CriticalExtrapolation.Paper
