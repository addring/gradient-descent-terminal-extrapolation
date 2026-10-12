import PaperFramework.PositiveQuadraticContinuity
import PaperFramework.Energy
import PaperFramework.ChainMatrix
import PaperFramework.ForwardFlowAlgebra
import PaperFramework.RowMomentNormalization

namespace CriticalExtrapolation.Paper
open Filter Topology
open scoped BigOperators
noncomputable section

theorem chainFlow_admissible (N : ℕ) : AdmissibleFlow (chainFlow N) := by
  classical
  constructor
  · intro e _
    unfold chainFlow
    split_ifs <;> positivity
  · intro i
    have hpair : ∀ v : Vec N,
        (∑ j, (outflow (chainFlow N) j - inflow (chainFlow N) j) * v j) = ∑ j, v j := by
      intro v
      rw [← flow_divergence_pairing, chain_flow_sum]
      simpa only [difference, Fin.val_succ] using weighted_differences_sum v
    simpa using hpair (fun j => if j = i then 1 else 0)

theorem chain_quadratic_continuous_at_one (N : ℕ) (h : ℝ)
    (hN : 0 < N) (hh : 0 < h) (hh1 : h ≤ 1) (p : Vec N) :
    ContinuousAt (fun z : ℝ × Vec N => quadraticForm (M₀ N h z.1) z.2) (1, p) := by
  have hK : ∀ i : Fin N, queryK N h 1 i ≠ 0 :=
    fun i => (queryK_positive N h 1 ⟨hN, hh, hh1, le_rfl⟩ i).ne'
  unfold quadraticForm M₀ flowMatrix S TEntry queryK
  fun_prop (disch := exact hK _)

theorem chain_positive_near_one (N : ℕ) (h : ℝ)
    (hN : 0 < N) (hh : 0 < h) (hh1 : h ≤ 1) :
    ∀ᶠ c in 𝓝 (1 : ℝ), PositiveQuadratic (M₀ N h c) := by
  exact positiveQuadratic_eventually (M₀ N h) 1
    (chain_quadratic_continuous_at_one N h hN hh hh1)
    (chain_at_one_positive N h ⟨hN, hh, hh1, le_rfl⟩)

end
end CriticalExtrapolation.Paper
