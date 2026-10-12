import PaperFramework.Definitions

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem auxiliaryValue_attained (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (hβ : IsOptimizer h c β) :
    auxiliaryValue N h c = chainObjective h c β := by
  let values := {r : ℝ | ∃ p : Vec N, Feasible h c p ∧ r = chainObjective h c p}
  have hmem : chainObjective h c β ∈ values := ⟨β, hβ.1, rfl⟩
  have hlower : ∀ r ∈ values, chainObjective h c β ≤ r := by
    rintro r ⟨p, hp, rfl⟩
    exact hβ.2 p hp
  change sInf values = chainObjective h c β
  exact le_antisymm (csInf_le ⟨chainObjective h c β, hlower⟩ hmem)
    (le_csInf ⟨_, hmem⟩ hlower)

end
end CriticalExtrapolation.Paper
