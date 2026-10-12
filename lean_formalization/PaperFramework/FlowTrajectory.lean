import PaperFramework.FlowVectorQuadratic
import PaperFramework.ForwardFlowAlgebra

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem sampled_ordinary_position {d N : ℕ} (I : Instance d 1 1) (h c : ℝ)
    (i : Fin N) : (sampledInstance I N h c).x (ordinaryQuery i) = iterate I h i.val := by
  simp [sampledInstance, ordinaryQuery, i.isLt]

theorem sampled_ordinary_gradient {d N : ℕ} (I : Instance d 1 1) (h c : ℝ)
    (i : Fin N) : (sampledInstance I N h c).g (ordinaryQuery i) =
      gradient I.f (iterate I h i.val) := by
  simp [sampledInstance, ordinaryQuery, i.isLt]

theorem sampled_output_position {d N : ℕ} (I : Instance d 1 1) (h c : ℝ) :
    (sampledInstance I N h c).x (outputQuery N) = output I N h c := by
  simp [sampledInstance, outputQuery]

theorem sampled_output_gradient {d N : ℕ} (I : Instance d 1 1) (h c : ℝ) :
    (sampledInstance I N h c).g (outputQuery N) = gradient I.f (output I N h c) := by
  simp [sampledInstance, outputQuery]

theorem sampled_star_gradient {d N : ℕ} (I : Instance d 1 1) (h c : ℝ) :
    (sampledInstance I N h c).g (starQuery N) = 0 := by
  exact I.gradient_at_minimizer

theorem space_prefix_sum_succ {N d : ℕ} (v : Fin N → Space d) (n : ℕ) (hn : n < N) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < n + 1), v i) =
      (∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < n), v i) + v ⟨n, hn⟩ := by
  classical
  have hset : Finset.univ.filter (fun i : Fin N => i.val < n + 1) =
      insert ⟨n, hn⟩ (Finset.univ.filter (fun i : Fin N => i.val < n)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hnot : (⟨n, hn⟩ : Fin N) ∉ Finset.univ.filter (fun i : Fin N => i.val < n) := by simp
  rw [hset, Finset.sum_insert hnot, add_comm]

/-- Exact unrolling for the sampled ordinary gradients, with no output gradient substituted. -/
theorem sampled_iterate_prefix {N d : ℕ} (I : Instance d 1 1) (h c : ℝ) :
    ∀ n, n ≤ N → iterate I h n = I.initial - h •
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < n),
        (sampledInstance I N h c).g (ordinaryQuery i) := by
  classical
  intro n
  induction n with
  | zero => intro _; simp [iterate]
  | succ n ih =>
    intro hn
    have hnlt : n < N := by omega
    rw [iterate, div_one, ← sampled_ordinary_gradient I h c ⟨n, hnlt⟩,
      ih (by omega), space_prefix_sum_succ _ n hnlt]
    simp only [smul_add]
    abel

theorem sampled_output_total {N d : ℕ} (I : Instance d 1 1) (h c : ℝ) :
    output I N h c = I.initial - (h * c) •
      ∑ i : Fin N, (sampledInstance I N h c).g (ordinaryQuery i) := by
  classical
  have hset : Finset.univ.filter (fun i : Fin N => i.val < N) = Finset.univ := by
    ext i
    simp [i.isLt]
  rw [output, sampled_iterate_prefix I h c N le_rfl, hset]
  simp only [sub_sub_cancel_left, smul_neg, smul_smul, mul_comm c h]
  abel

theorem flowVectorExtend_ordinary {N d : ℕ} (v : Fin N → Space d) (i : Fin N) :
    flowVectorExtend v i.castSucc = v i := by
  ext k
  rw [flowVectorExtend_apply]
  exact zeroExtend_at _ i

theorem flowVectorExtend_output {N d : ℕ} (v : Fin N → Space d) :
    flowVectorExtend v (Fin.last N) = 0 := by
  ext k
  simp [flowVectorExtend_apply, zeroExtend]

theorem flowVectorT_prefix {N d : ℕ} (h c : ℝ) (v : Fin N → Space d) (i : Fin N) :
    flowVectorT h c v i = (h * c) • (∑ j, v j) -
      h • (∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), v j) - v i := by
  ext k
  simp only [flowVectorT_apply, applyT, PiLp.sub_apply, PiLp.smul_apply,
    space_finset_sum_apply, smul_eq_mul]

theorem fin_prefix_card {N : ℕ} (i : Fin N) :
    (Finset.univ.filter (fun j : Fin N => j.val < i.val)).card = i.val := by
  have hset : Finset.univ.filter (fun j : Fin N => j.val < i.val) = Finset.Iio i := by
    ext j
    simp
  rw [hset, Fin.card_Iio]

/-- The displacement from the minimizer uses the gradient at the actual output. -/
theorem sampled_initial_geometry {N d : ℕ} (I : Instance d 1 1) (h c : ℝ) :
    let q := gradient I.f (output I N h c)
    let z := output I N h c - I.minimizer - q
    let v := fun i : Fin N => (sampledInstance I N h c).g (ordinaryQuery i) - q
    I.initial - I.minimizer = (S N h c) • q + z + (h * c) • ∑ i, v i := by
  dsimp only
  ext k
  have ho := congrArg (fun x : Space d => x k) (sampled_output_total (N := N) I h c)
  simp only [PiLp.sub_apply, PiLp.smul_apply, space_finset_sum_apply, smul_eq_mul] at ho ⊢
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    space_finset_sum_apply, smul_eq_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, S]
  linear_combination -ho

theorem sampled_ordinary_geometry {N d : ℕ} (I : Instance d 1 1) (h c : ℝ)
    (i : Fin N) :
    let q := gradient I.f (output I N h c)
    let z := output I N h c - I.minimizer - q
    let v := fun j : Fin N => (sampledInstance I N h c).g (ordinaryQuery j) - q
    (sampledInstance I N h c).x (ordinaryQuery i) - I.minimizer -
      (sampledInstance I N h c).g (ordinaryQuery i) =
      (queryK N h c i) • q + z + flowVectorT h c v i := by
  dsimp only
  rw [sampled_ordinary_position, sampled_iterate_prefix I h c i.val (Nat.le_of_lt i.isLt),
    flowVectorT_prefix]
  have hset : Finset.univ.filter (fun j : Fin N => j < i) =
      Finset.univ.filter (fun j : Fin N => j.val < i.val) := rfl
  rw [hset]
  ext k
  have ho := congrArg (fun x : Space d => x k) (sampled_output_total (N := N) I h c)
  simp only [PiLp.sub_apply, PiLp.smul_apply, space_finset_sum_apply, smul_eq_mul] at ho
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    space_finset_sum_apply, smul_eq_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, fin_prefix_card,
    nsmul_eq_mul, queryK]
  linear_combination -ho

end
end CriticalExtrapolation.Paper
