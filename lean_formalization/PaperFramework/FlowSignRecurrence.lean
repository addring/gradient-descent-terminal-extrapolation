import PaperFramework.FlowMoments

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def flowAlpha {N : ℕ} (h c : ℝ) (β : Vec N) (μ : Fin (N - 1) → ℝ) (i : Fin N) : ℝ :=
  (1 + (i.val : ℝ) * flowProbability h c β μ i.val) / queryK N h c i

def flowHistory {N : ℕ} (h c : ℝ) (β : Vec N) (μ : Fin (N - 1) → ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range i, zeroExtend (flowAlpha h c β μ) k * flowSurvival (flowProbability h c β μ) k i

theorem flowAlpha_moment (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i : Fin N) :
    flowAlpha h c β μ i * flowEll h c β μ i.val = kktRowWeight h c β μ i := by
  unfold flowAlpha kktRowWeight
  rw [div_mul_eq_mul_div, flow_departure_moment N h c hp hh β μ ν hkkt i]

theorem flowAlpha_positive (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i : Fin N) : 0 < flowAlpha h c β μ i := by
  have hm := flowAlpha_moment N h c hp hh β μ ν hkkt i
  have hw : 0 < kktRowWeight h c β μ i :=
    div_pos (kkt_row_moments_positive N h c hp hh β μ ν hkkt i) (queryK_positive N h c hp i)
  exact (mul_pos_iff_of_pos_right (kkt_flowEll_positive N h c hp hh β μ ν hkkt i)).mp (hm.symm ▸ hw)

theorem flowHistory_step {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (i : Fin N) :
    flowHistory h c β μ (i.val + 1) = flowAlpha h c β μ i +
      (1 - flowProbability h c β μ i.val) * flowHistory h c β μ i.val := by
  unfold flowHistory
  rw [Finset.sum_range_succ, flowSurvival_adjacent, zeroExtend_at, mul_one]
  have heq : (∑ k ∈ Finset.range i.val, zeroExtend (flowAlpha h c β μ) k *
      flowSurvival (flowProbability h c β μ) k (i.val + 1)) =
      (1 - flowProbability h c β μ i.val) *
        ∑ k ∈ Finset.range i.val, zeroExtend (flowAlpha h c β μ) k *
          flowSurvival (flowProbability h c β μ) k i.val := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [flowSurvival_step _ k i.val (Finset.mem_range.mp hk)]
    ring
  rw [heq]
  ring

theorem flowHistory_nonnegative (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i : ℕ) (hi : i ≤ N) : 0 ≤ flowHistory h c β μ i := by
  apply Finset.sum_nonneg
  intro k hk
  have hkN : k < N := by have := Finset.mem_range.mp hk; omega
  have hα : 0 ≤ zeroExtend (flowAlpha h c β μ) k := by
    change 0 ≤ zeroExtend (flowAlpha h c β μ) (⟨k, hkN⟩ : Fin N).val
    rw [zeroExtend_at]
    exact (flowAlpha_positive N h c hp hh β μ ν hkkt ⟨k, hkN⟩).le
  apply mul_nonneg hα
  apply Finset.prod_nonneg
  intro j hj
  have hj' := Finset.mem_Ioo.mp hj
  exact sub_nonneg.mpr (kkt_flowProbability_le_one N h c hp hh β μ ν hkkt j (by omega))

theorem flowAlpha_contraction (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i j : Fin N) (hij : i.val + 1 = j.val)
    (hs : slope h c β i = slope h c β j) :
    (1 - flowProbability h c β μ j.val) * flowAlpha h c β μ i <
      (1 - h) * flowAlpha h c β μ j := by
  have hw := equal_slope_row_weight_contraction N h c hp hh β μ ν hkkt i j hij hs
  have hr := flowEll_recurrence N h c hp hh β μ ν hkkt j.val (by omega) j.isLt.le
  have hj : j.val - 1 = i.val := by omega
  rw [hj, zeroExtend_at, zeroExtend_at, ← difference_adjacent β i j hij] at hr
  have hαi := flowAlpha_moment N h c hp hh β μ ν hkkt i
  have hαj := flowAlpha_moment N h c hp hh β μ ν hkkt j
  have hprod := mul_pos (flowAlpha_positive N h c hp hh β μ ν hkkt i)
    (kkt_strict_differences N h c hp hh β μ ν hkkt i)
  have heq := congrArg (fun x : ℝ => flowAlpha h c β μ i * x) hr
  rw [← hαi, ← hαj] at hw
  apply (mul_lt_mul_iff_of_pos_right (kkt_flowEll_positive N h c hp hh β μ ν hkkt j)).mp
  nlinarith only [heq, hw, hprod]

theorem flowHistory_strict_bound (N : ℕ) (h c : ℝ) (hp : Parameters N h c) (hh : h < 1)
    (β : Vec N) (μ : Fin (N - 1) → ℝ) (ν : Vec N)
    (hkkt : CompleteKKT h c β μ ν) (i : Fin N) :
    h * (1 - flowProbability h c β μ i.val) * flowHistory h c β μ i.val <
      (1 - h) * flowAlpha h c β μ i := by
  have hall : ∀ k (hk : k < N),
      h * (1 - flowProbability h c β μ k) * flowHistory h c β μ k <
        (1 - h) * flowAlpha h c β μ ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hr := mul_pos (sub_pos.mpr hh) (flowAlpha_positive N h c hp hh β μ ν hkkt ⟨0, hk⟩)
      simpa [flowHistory] using hr
    | succ k ih =>
      intro hk
      let p : Fin N := ⟨k, by omega⟩
      let j : Fin N := ⟨k + 1, hk⟩
      have hpi : p.val + 1 = j.val := rfl
      have hind := ih p.isLt
      have hz := flowHistory_step h c β μ p
      have hzbound : h * flowHistory h c β μ j.val < flowAlpha h c β μ p := by
        change flowHistory h c β μ j.val = _ at hz
        change h * (1 - flowProbability h c β μ p.val) * flowHistory h c β μ p.val <
          (1 - h) * flowAlpha h c β μ p at hind
        rw [hz]
        nlinarith only [hind]
      change h * (1 - flowProbability h c β μ j.val) * flowHistory h c β μ j.val < _
      rcases lt_or_eq_of_le (hkkt.feasible.2.2 p j hpi) with hs | hs
      · rw [flowProbability_one_of_strict_slope h c β μ ν hkkt p j hpi hs]
        simpa using mul_pos (sub_pos.mpr hh) (flowAlpha_positive N h c hp hh β μ ν hkkt j)
      · have hsur : 0 ≤ 1 - flowProbability h c β μ j.val :=
          sub_nonneg.mpr (kkt_flowProbability_le_one N h c hp hh β μ ν hkkt j.val j.isLt.le)
        have hm := mul_le_mul_of_nonneg_left hzbound.le hsur
        have hc := flowAlpha_contraction N h c hp hh β μ ν hkkt p j hpi hs.symm
        nlinarith only [hm, hc]
  exact hall i.val i.isLt

end
end CriticalExtrapolation.Paper
