import PaperFramework.QPSlater
import PaperFramework.RelativeConvexity

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem optimizer_exists_unique (N : ℕ) (h c : ℝ) (hp : Parameters N h c) :
    ∃! β : Vec N, IsOptimizer h c β := by
  have hcompact := feasible_set_compact N h c hp
  have hnonempty : {β : Vec N | Feasible h c β}.Nonempty :=
    ⟨uniformDirection N, uniform_feasible N h c hp⟩
  obtain ⟨β, hβ, hmin⟩ := hcompact.exists_isMinOn hnonempty
    (continuous_chainObjective N h c).continuousOn
  refine ⟨β, ⟨hβ, hmin⟩, ?_⟩
  intro γ hγ
  have hstrict := (relative_strict_convexity N h c hp).subset
    (show {β : Vec N | Feasible h c β} ⊆ {β | (∑ i, β i) = 1} from fun _ hx => hx.1)
    (feasible_set_convex N h c)
  exact hstrict.eq_of_isMinOn hγ.2 hmin hγ.1 hβ

end
end CriticalExtrapolation.Paper
