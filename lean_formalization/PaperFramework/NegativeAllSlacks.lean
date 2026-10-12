import PaperFramework.NegativeSlackSigns
import Mathlib.Order.Filter.Finite

namespace CriticalExtrapolation.Paper
open Filter Topology
noncomputable section

theorem perturbation_pair_slack_eventually (N : ℕ) (h c : ℝ)
    (hp : Parameters N h c) (β : Vec N) (hβ : StrictlyFeasible h c β)
    (i j : Query N) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 ≤ slack (perturbationSample h c ε β) i j := by
  cases i with
  | none =>
    exact Eventually.of_forall (fun ε => by
      simpa only [starQuery] using
        (le_of_eq (perturbation_distinguished_slacks N h c ε β j).1.symm))
  | some i =>
    by_cases hi : i.val < N
    · let ii : Fin N := ⟨i.val, hi⟩
      have hquery : ordinaryQuery ii = some i := by
        unfold ordinaryQuery
        congr 1
      rw [← hquery]
      cases j with
      | none =>
        exact (perturbation_minimizer_slack_eventually N h c hp β ii).mono (fun _ hε => hε.le)
      | some j =>
        by_cases heq : ii.val = j.val
        · have hsame : some j = ordinaryQuery ii := by
            unfold ordinaryQuery
            congr 1
            exact Fin.ext heq.symm
          rw [hsame]
          exact Eventually.of_forall (fun ε => by
            rw [perturbation_slack_identity, sub_self, inner_zero_left])
        · by_cases hadj : ii.val + 1 = j.val
          · have hnext : j = ii.succ := Fin.ext hadj.symm
            rw [hnext]
            obtain ⟨ε₀, hε₀, hall⟩ := perturbation_adjacent_slack_strict_small N h c hp β ii
            filter_upwards [
              (show ∀ᶠ ε : ℝ in 𝓝 0, ε < ε₀ from Iio_mem_nhds hε₀).filter_mono
                nhdsWithin_le_nhds,
              (show ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin)] with ε hupper hpos
            exact (hall ε ⟨hpos, hupper⟩).le
          · exact (perturbation_nonadjacent_slack_eventually N h c hp β hβ ii j
              (by omega)).mono (fun _ hε => hε.le)
    · have houtput : some i = outputQuery N := by
        unfold outputQuery
        congr 1
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      rw [houtput]
      exact Eventually.of_forall (fun ε => by
        rw [(perturbation_distinguished_slacks N h c ε β j).2])

/-- Finiteness supplies one common perturbation size for every ordered pair. -/
theorem perturbation_all_directed_slacks_of_strict (N : ℕ) (h c : ℝ)
    (hp : Parameters N h c) (β : Vec N) (hβ : StrictlyFeasible h c β) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∀ i j,
      0 ≤ slack (perturbationSample h c ε β) i j := by
  have hcommon : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ i j : Query N,
      0 ≤ slack (perturbationSample h c ε β) i j :=
    eventually_all.mpr (fun i => eventually_all.mpr (fun j =>
      perturbation_pair_slack_eventually N h c hp β hβ i j))
  obtain ⟨ε₀, hε₀, hall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hcommon
  exact ⟨ε₀, hε₀, fun ε hε => hall hε⟩

end
end CriticalExtrapolation.Paper
