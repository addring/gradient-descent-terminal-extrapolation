import PaperFramework.KKTOrderPreparation

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

/-- A genuine zero left boundary, with natural indices to avoid negative subscripts. -/
def previousCoordinate {N : ℕ} (v : Vec N) (i : ℕ) : ℝ :=
  if i = 0 then 0 else zeroExtend v (i - 1)

def backwardDifference {N : ℕ} (v : Vec N) (i : Fin N) : ℝ :=
  v i - previousCoordinate v i.val

theorem previousCoordinate_succ {N : ℕ} (v : Vec N) (i : Fin N) :
    previousCoordinate v (i.val + 1) = v i := by
  simp [previousCoordinate, zeroExtend_at]

theorem DEntry_transpose {N : ℕ} (v : Vec N) (i : Fin N) :
    (∑ k, DEntry k i * v k) = backwardDifference v i := by
  classical
  have hs : (∑ k : Fin N, if k.val + 1 = i.val then v k else 0) =
      previousCoordinate v i.val := by
    by_cases hi : i.val = 0
    · simp [hi, previousCoordinate]
    · let p : Fin N := ⟨i.val - 1, by omega⟩
      have hp : p.val + 1 = i.val := by dsimp [p]; omega
      have hpn : i.val - 1 < N := by omega
      rw [Finset.sum_eq_single p]
      · simp [hp, previousCoordinate, hi, zeroExtend, p, hpn]
      · intro k _ hkp
        have hne : k.val + 1 ≠ i.val := by
          intro heq
          apply hkp
          apply Fin.ext
          dsimp [p]
          omega
        simp [hne]
      · simp
  unfold DEntry backwardDifference
  simp_rw [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  rw [hs]
  simp

theorem adjacent_summation_by_parts {N : ℕ} (u : Fin (N - 1) → ℝ) (v : Vec N) :
    (∑ k, u k * (v (slopeLeft k) - v (slopeRight k))) =
      ∑ i : Fin N, (zeroExtend u i.val - previousCoordinate u i.val) * v i := by
  cases N with
  | zero => simp
  | succ n =>
    change (∑ k : Fin n, u k * (v k.castSucc - v k.succ)) =
      ∑ i : Fin (n + 1), (zeroExtend u i.val - previousCoordinate u i.val) * v i
    have hleft : (∑ i : Fin (n + 1), zeroExtend u i.val * v i) =
        ∑ k : Fin n, u k * v k.castSucc := by
      rw [Fin.sum_univ_castSucc]
      change (∑ k : Fin n, zeroExtend u k.val * v k.castSucc) +
        zeroExtend u n * v (Fin.last n) = _
      simp only [zeroExtend_at]
      have hz : zeroExtend u n = 0 := by simp [zeroExtend]
      rw [hz, zero_mul, add_zero]
    have hright : (∑ i : Fin (n + 1), previousCoordinate u i.val * v i) =
        ∑ k : Fin n, u k * v k.succ := by
      rw [Fin.sum_univ_succ]
      simp [previousCoordinate, zeroExtend_at]
    simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]
    rw [hleft, hright]

theorem scaledMu_zeroExtend {N : ℕ} (h c : ℝ) (μ : Fin (N - 1) → ℝ) (i : ℕ) :
    scaledMu h c μ i = zeroExtend (fun k => μ k / (2 * h * c * S N h c)) i := by
  unfold scaledMu zeroExtend
  split_ifs <;> rfl

theorem previousMu_coordinate {N : ℕ} (h c : ℝ) (μ : Fin (N - 1) → ℝ) (i : ℕ) :
    previousMu h c μ i =
      previousCoordinate (fun k => μ k / (2 * h * c * S N h c)) i := by
  unfold previousMu previousCoordinate
  split_ifs
  · rfl
  · exact scaledMu_zeroExtend h c μ (i - 1)

theorem AEntry_transpose_scaled {N : ℕ} (h c : ℝ)
    (μ : Fin (N - 1) → ℝ) (i : Fin N) :
    (∑ k, AEntry h c k i * μ k) / (2 * h * c * S N h c) =
      ∑ k, TEntry h c k i *
        ((scaledMu h c μ k.val - previousMu h c μ k.val) / queryK N h c k) := by
  have hs := adjacent_summation_by_parts (fun k => μ k / (2 * h * c * S N h c))
    (fun k => REntry h c k i)
  simp_rw [← scaledMu_zeroExtend, ← previousMu_coordinate] at hs
  calc
    _ = ∑ k, (μ k / (2 * h * c * S N h c)) *
        (REntry h c (slopeLeft k) i - REntry h c (slopeRight k) i) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      unfold AEntry
      ring
    _ = _ := by
      rw [hs]
      apply Finset.sum_congr rfl
      intro k _
      unfold REntry
      ring

theorem TEntry_column_difference {N : ℕ} (h c : ℝ) (i j k : Fin N)
    (hij : i.val + 1 = j.val) :
    TEntry h c k i - TEntry h c k j =
      -(if k = i then 1 else 0) + (1 - h) * (if k = j then 1 else 0) := by
  have hij' : i < j := by change i.val < j.val; omega
  by_cases hki : k = i
  · subst k
    simp [TEntry, hij'.ne, not_lt.mpr hij'.le]
  · by_cases hkj : k = j
    · subst k
      simp [TEntry, hki, hij']
    · have hcmp : (i < k) = (j < k) := by
        apply propext
        have hkval : k.val ≠ j.val := fun heq => hkj (Fin.ext heq)
        simp only [Fin.lt_def]
        omega
      simp [TEntry, hki, hkj, hcmp]

theorem TEntry_transpose_adjacent {N : ℕ} (h c : ℝ) (w : Vec N)
    (i j : Fin N) (hij : i.val + 1 = j.val) :
    (∑ k, TEntry h c k i * w k) - (∑ k, TEntry h c k j * w k) =
      -w i + (1 - h) * w j := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul, TEntry_column_difference h c i j _ hij]
  simp [add_mul, Finset.sum_add_distrib, ite_mul]

end
end CriticalExtrapolation.Paper
