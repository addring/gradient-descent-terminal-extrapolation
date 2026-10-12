import PaperFramework.TransposeIdentities

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def kktSlopeMoment {N : ℕ} (h c : ℝ) (β : Vec N) : Vec N :=
  backwardDifference (fun i => ((i.val : ℝ) + 1) * slope h c β i)

def kktRowWeight {N : ℕ} (h c : ℝ) (β : Vec N) (μ : Fin (N - 1) → ℝ) : Vec N :=
  fun i => rowMoment h c β μ i / queryK N h c i

def scaledNu {N : ℕ} (h c : ℝ) (ν : Vec N) : Vec N :=
  fun i => ν i / (2 * h * c * S N h c)

def kktConstant (N : ℕ) (h c : ℝ) : ℝ :=
  h * c / S N h c - auxiliaryValue N h c / (h * c * S N h c)

theorem chain_matrix_action (N : ℕ) (h c : ℝ) (β : Vec N) (i : Fin N) :
    (∑ j, M₀ N h c i j * β j) = h ^ 2 * c ^ 2 * (∑ j, β j) - h * c * S N h c *
      (kktSlopeMoment h c β i +
        ∑ k, TEntry h c k i * (((k.val : ℝ) + 1) * difference β k / queryK N h c k)) := by
  have hsum : (∑ j, (∑ k, (((k.val : ℝ) + 1) / queryK N h c k) *
        (DEntry k i * TEntry h c k j + TEntry h c k i * DEntry k j)) * β j) =
      ∑ k, (((k.val : ℝ) + 1) / queryK N h c k) *
        (DEntry k i * applyT h c β k + TEntry h c k i * difference β k) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp_rw [mul_assoc, ← Finset.mul_sum, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum, TEntry_apply, DEntry_apply]
  have hsplit : (∑ k, (((k.val : ℝ) + 1) / queryK N h c k) *
        (DEntry k i * applyT h c β k + TEntry h c k i * difference β k)) =
      (∑ k, DEntry k i * (((k.val : ℝ) + 1) * slope h c β k)) +
        ∑ k, TEntry h c k i * (((k.val : ℝ) + 1) * difference β k / queryK N h c k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    unfold slope
    ring
  calc
    _ = h ^ 2 * c ^ 2 * (∑ j, β j) - h * c * S N h c *
        (∑ j, (∑ k, (((k.val : ℝ) + 1) / queryK N h c k) *
          (DEntry k i * TEntry h c k j + TEntry h c k i * DEntry k j)) * β j) := by
      simp_rw [chain_matrix_entries, sub_mul, Finset.sum_sub_distrib,
        mul_assoc, ← Finset.mul_sum]
    _ = _ := by rw [hsum, hsplit, DEntry_transpose]; rfl

theorem scaledNu_transpose {N : ℕ} (h c : ℝ) (ν : Vec N) (i : Fin N) :
    backwardDifference (scaledNu h c ν) i =
      (∑ k, DEntry k i * ν k) / (2 * h * c * S N h c) := by
  rw [← DEntry_transpose]
  simp only [scaledNu, ← mul_div_assoc, ← Finset.sum_div]

theorem kktRowWeight_split {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (i : Fin N) :
    (∑ k, TEntry h c k i * kktRowWeight h c β μ k) =
      (∑ k, TEntry h c k i * (((k.val : ℝ) + 1) * difference β k / queryK N h c k)) +
        ∑ k, TEntry h c k i *
          ((scaledMu h c μ k.val - previousMu h c μ k.val) / queryK N h c k) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold kktRowWeight rowMoment
  ring

/-- The full KKT equation in the U + Tᵀw + Dᵀf form, retaining f. -/
theorem kkt_coordinate_balance (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i : Fin N) :
    kktSlopeMoment h c β i + (∑ k, TEntry h c k i * kktRowWeight h c β μ k) +
      backwardDifference (scaledNu h c ν) i = kktConstant N h c := by
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hp.c_ge_one
  have hh := hp.h_pos
  have hS : 0 < S N h c := by
    unfold S
    positivity
  have hden : h * c * S N h c ≠ 0 := ne_of_gt (mul_pos (mul_pos hp.h_pos hc) hS)
  have hs := hkkt.stationarity i
  rw [chain_matrix_action, hkkt.feasible.1, mul_one] at hs
  rw [kktRowWeight_split, ← AEntry_transpose_scaled, scaledNu_transpose]
  unfold kktConstant
  field_simp
  simp only [← mul_div_assoc, ← mul_assoc] at hs
  nlinarith [hs]

/-- Equation (4.3), including the zero left boundary and all difference multipliers. -/
theorem kkt_adjacent_balance (N : ℕ) (h c : ℝ) (hp : Parameters N h c)
    (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i j : Fin N) (hij : i.val + 1 = j.val) :
    2 * scaledNu h c ν i - previousCoordinate (scaledNu h c ν) i.val - scaledNu h c ν j =
      kktRowWeight h c β μ i - (1 - h) * kktRowWeight h c β μ j -
        (kktSlopeMoment h c β i - kktSlopeMoment h c β j) := by
  have hi := kkt_coordinate_balance N h c hp β μ ν hkkt i
  have hj := kkt_coordinate_balance N h c hp β μ ν hkkt j
  have hT := TEntry_transpose_adjacent h c (kktRowWeight h c β μ) i j hij
  have hprev : previousCoordinate (scaledNu h c ν) j.val = scaledNu h c ν i := by
    rw [← hij]
    exact previousCoordinate_succ _ i
  unfold backwardDifference at hi hj
  rw [hprev] at hj
  linarith

end
end CriticalExtrapolation.Paper
