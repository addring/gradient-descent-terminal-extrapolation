import PaperFramework.PlateauRecurrences

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

theorem fin_interval_mono {N : ℕ} (f : Vec N) (a b : Fin N) (hab : a ≤ b)
    (hstep : ∀ i j : Fin N, a ≤ i → j ≤ b → i.val + 1 = j.val → f i ≤ f j) :
    f a ≤ f b := by
  have hall : ∀ k (hk : k < N), a.val ≤ k → k ≤ b.val → f a ≤ f ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk ha hb
      have heq : a = ⟨0, hk⟩ := Fin.ext (by change a.val = 0; omega)
      rw [heq]
    | succ k ih =>
      intro hk ha hb
      by_cases heq : a.val = k + 1
      · have heq' : a = ⟨k + 1, hk⟩ := Fin.ext heq
        rw [heq']
      · have hkN : k < N := by omega
        exact le_trans (ih hkN (by omega) (by omega))
          (hstep ⟨k, hkN⟩ ⟨k + 1, hk⟩ (by change a.val ≤ k; omega)
            (by exact hb) rfl)
  exact hall b.val b.isLt hab le_rfl

theorem fin_interval_antitone {N : ℕ} (f : Vec N) (a b : Fin N) (hab : a ≤ b)
    (hstep : ∀ i j : Fin N, a ≤ i → j ≤ b → i.val + 1 = j.val → f j ≤ f i) :
    f b ≤ f a := by
  have hs := fin_interval_mono (fun i => -f i) a b hab
    (fun i j hai hjb hij => neg_le_neg (hstep i j hai hjb hij))
  linarith

theorem sum_fin_Icc_natural {N : ℕ} (a b : Fin N) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.Icc a b, f i.val) = ∑ k ∈ Finset.Ico a.val (b.val + 1), f k := by
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    have hi' := Finset.mem_Icc.mp hi
    exact Finset.mem_Ico.mpr ⟨hi'.1, by have := hi'.2; change i.val ≤ b.val at this; omega⟩
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro k hk
    have hk' := Finset.mem_Ico.mp hk
    refine ⟨⟨k, by omega⟩, ?_, rfl⟩
    exact Finset.mem_Icc.mpr ⟨hk'.1, by change k ≤ b.val; omega⟩
  · intro i _
    rfl

theorem sum_fin_Icc_difference {N : ℕ} (a b : Fin N) (hab : a ≤ b) (z : ℕ → ℝ) :
    (∑ i ∈ Finset.Icc a b, (z (i.val + 1) - z i.val)) = z (b.val + 1) - z a.val := by
  rw [sum_fin_Icc_natural a b (fun k => z (k + 1) - z k)]
  have hs : ∀ n, (∑ k ∈ Finset.range n, (z (k + 1) - z k)) = z n - z 0 := by
    intro n
    have heq := sum_differences z n
    simp only [Finset.sum_sub_distrib] at heq ⊢
    linarith
  rw [Finset.sum_Ico_eq_sub _ (by have := hab; change a.val ≤ b.val at this; omega), hs, hs]
  ring

theorem sum_fin_Icc_index (N : ℕ) (a b : Fin N) :
    2 * (∑ i ∈ Finset.Icc a b, (i.val : ℝ)) =
      ((a.val : ℝ) + (b.val : ℝ)) * (Finset.Icc a b).card := by
  have hreflect : (∑ i ∈ Finset.Icc a b, ((a.val + b.val - i.val : ℕ) : ℝ)) =
      ∑ i ∈ Finset.Icc a b, (i.val : ℝ) := by
    apply Finset.sum_bij (fun i hi => (⟨a.val + b.val - i.val, by
      have hi' := Finset.mem_Icc.mp hi
      have hai : a.val ≤ i.val := hi'.1
      omega⟩ : Fin N))
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hai : a.val ≤ i.val := hi'.1
      have hib : i.val ≤ b.val := hi'.2
      apply Finset.mem_Icc.mpr
      constructor
      · change a.val ≤ a.val + b.val - i.val
        omega
      · change a.val + b.val - i.val ≤ b.val
        omega
    · intro i hi j hj heq
      have hi' := Finset.mem_Icc.mp hi
      have hj' := Finset.mem_Icc.mp hj
      have hib : i.val ≤ b.val := hi'.2
      have hjb : j.val ≤ b.val := hj'.2
      have hv := congrArg Fin.val heq
      apply Fin.ext
      dsimp at hv
      omega
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      have haj : a.val ≤ j.val := hj'.1
      have hjb : j.val ≤ b.val := hj'.2
      let i : Fin N := ⟨a.val + b.val - j.val, by omega⟩
      have hi : i ∈ Finset.Icc a b := by
        apply Finset.mem_Icc.mpr
        constructor
        · change a.val ≤ a.val + b.val - j.val
          omega
        · change a.val + b.val - j.val ≤ b.val
          omega
      refine ⟨i, hi, ?_⟩
      apply Fin.ext
      dsimp [i]
      omega
    · intro i hi
      rfl
  have hcast : ∀ i ∈ Finset.Icc a b,
      ((a.val + b.val - i.val : ℕ) : ℝ) = (a.val : ℝ) + (b.val : ℝ) - i.val := by
    intro i hi
    have hib : i.val ≤ b.val := (Finset.mem_Icc.mp hi).2
    rw [Nat.cast_sub (by omega), Nat.cast_add]
  rw [Finset.sum_congr rfl hcast, Finset.sum_sub_distrib] at hreflect
  simp only [Finset.sum_const, nsmul_eq_mul] at hreflect
  nlinarith

theorem interval_queryK_bound (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (a b : Fin N) :
    (∑ i ∈ Finset.Icc a b, queryK N h c i) ≤
      queryK N h c b * (∑ i ∈ Finset.Icc a b, ((i.val : ℝ) + 1)) := by
  have hb : (b.val : ℝ) + 1 ≤ N := by exact_mod_cast b.isLt
  have hNc : (N : ℝ) ≤ (N : ℝ) * c := le_mul_of_one_le_right (Nat.cast_nonneg N) hp.c_ge_one
  have hKb : h ≤ queryK N h c b := by
    unfold queryK
    nlinarith [mul_nonneg hp.h_pos.le (by linarith : 0 ≤ (N : ℝ) * c - b.val - 1)]
  have hind := sum_fin_Icc_index N a b
  have hsum : (∑ i ∈ Finset.Icc a b, queryK N h c i) =
      ((Finset.Icc a b).card : ℝ) * (queryK N h c b + h * b.val) -
        h * (∑ i ∈ Finset.Icc a b, (i.val : ℝ)) := by
    calc
      _ = ∑ i ∈ Finset.Icc a b, (queryK N h c b + h * b.val - h * i.val) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold queryK
        ring
      _ = _ := by simp [Finset.sum_sub_distrib, ← Finset.mul_sum] <;> ring
  have hweight : (∑ i ∈ Finset.Icc a b, ((i.val : ℝ) + 1)) =
      (∑ i ∈ Finset.Icc a b, (i.val : ℝ)) + (Finset.Icc a b).card := by simp [Finset.sum_add_distrib]
  have hcoef : 2 * queryK N h c b + h * ((b.val : ℝ) - a.val) ≤
      queryK N h c b * ((a.val : ℝ) + b.val + 2) := by
    have hm := mul_nonneg (sub_nonneg.mpr hKb)
      (add_nonneg (Nat.cast_nonneg (α := ℝ) a.val) (Nat.cast_nonneg (α := ℝ) b.val))
    have ha := mul_nonneg hp.h_pos.le (Nat.cast_nonneg (α := ℝ) a.val)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg (α := ℝ) (Finset.Icc a b).card)
  rw [hsum, hweight]
  nlinarith [congrArg (fun x : ℝ => h * x) hind,
    congrArg (fun x : ℝ => queryK N h c b * x) hind]

end
end CriticalExtrapolation.Paper
