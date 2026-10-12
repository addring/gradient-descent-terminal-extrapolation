import PaperFramework.NegativeAlgebra

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem perturbation_prefix_sum_succ {N : ℕ} (h c ε : ℝ) (β : Vec N)
    (n : ℕ) (hn : n < N) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < n + 1),
      perturbationGradient h c ε β i) =
    (∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < n),
      perturbationGradient h c ε β i) + perturbationGradient h c ε β ⟨n, hn⟩ := by
  classical
  have hset : Finset.univ.filter (fun i : Fin N => i.val < n + 1) =
      insert ⟨n, hn⟩ (Finset.univ.filter (fun i : Fin N => i.val < n)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hnot : (⟨n, hn⟩ : Fin N) ∉ Finset.univ.filter (fun i : Fin N => i.val < n) := by
    simp
  rw [hset, Finset.sum_insert hnot, add_comm]

theorem perturbation_iterate_formula {N : ℕ} {R : ℝ} (I : Instance 2 1 R)
    (h c ε : ℝ) (β : Vec N) (hinit : I.initial = perturbationInitial h c ε β)
    (hinterp : Interpolates (perturbationSample h c ε β) I.f) :
    ∀ n, n ≤ N → iterate I h n = perturbationInitial h c ε β - h •
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < n), perturbationGradient h c ε β i := by
  classical
  intro n
  induction n with
  | zero => intro _; simp [iterate, hinit]
  | succ n ih =>
    intro hn
    have hnlt : n < N := by omega
    have hprev := ih (by omega)
    have hg : gradient I.f (iterate I h n) = perturbationGradient h c ε β ⟨n, hnlt⟩ := by
      rw [hprev]
      have hs := hinterp.2 (ordinaryQuery (⟨n, hnlt⟩ : Fin N))
      simpa [perturbationSample, ordinaryQuery, hnlt] using hs
    rw [iterate, div_one, hg, hprev, perturbation_prefix_sum_succ h c ε β n hnlt]
    simp only [smul_add]
    abel

theorem perturbation_output_formula {N : ℕ} {R : ℝ} (I : Instance 2 1 R)
    (h c ε : ℝ) (β : Vec N) (hinit : I.initial = perturbationInitial h c ε β)
    (hinterp : Interpolates (perturbationSample h c ε β) I.f) :
    output I N h c = vec2 1 0 := by
  classical
  have hsum : Finset.univ.filter (fun i : Fin N => i.val < N) = Finset.univ := by
    ext i
    simp [i.isLt]
  rw [output, perturbation_iterate_formula I h c ε β hinit hinterp N le_rfl,
    hsum, hinit]
  simp only [sub_sub_cancel_left, smul_neg, smul_smul]
  rw [perturbationInitial]
  have hmul : c * h = h * c := mul_comm _ _
  rw [hmul]
  abel

end
end CriticalExtrapolation.Paper
