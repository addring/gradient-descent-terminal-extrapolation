import PaperFramework.RadiusCoordinates

namespace CriticalExtrapolation.Paper
open scoped BigOperators
noncomputable section

def radiusAppend {d : ℕ} (x : Space d) (r : ℝ) : Space (d + 1) :=
  WithLp.toLp 2 (Fin.snoc x.ofLp r)

theorem radiusAppend_castSucc_apply {d : ℕ} (x : Space d) (r : ℝ) (i : Fin d) :
    radiusAppend x r i.castSucc = x i := by simp [radiusAppend]

theorem radiusAppend_last_apply {d : ℕ} (x : Space d) (r : ℝ) :
    radiusAppend x r (Fin.last d) = r := by simp [radiusAppend]

theorem radiusDrop_radiusAppend {d : ℕ} (x : Space d) (r : ℝ) :
    radiusDrop d (radiusAppend x r) = x := by
  ext i
  rw [radiusDrop_apply, radiusAppend_castSucc_apply]

theorem radiusAppend_sub {d : ℕ} (x y : Space d) (a b : ℝ) :
    radiusAppend x a - radiusAppend y b = radiusAppend (x - y) (a - b) := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [PiLp.sub_apply, radiusAppend_last_apply]
  · simp only [PiLp.sub_apply, radiusAppend_castSucc_apply]

theorem radiusAppend_norm_sq {d : ℕ} (x : Space d) (r : ℝ) :
    ‖radiusAppend x r‖ ^ 2 = ‖x‖ ^ 2 + r ^ 2 := by
  rw [space_norm_sq_coordinates, Fin.sum_univ_castSucc]
  simp only [radiusAppend_castSucc_apply, radiusAppend_last_apply, ← space_norm_sq_coordinates]

theorem radius_append_equal_radius {d : ℕ} {D : ℝ} (x : Space d)
    (hD : 0 < D) (hx : ‖x‖ ≤ D) :
    ‖radiusAppend x (Real.sqrt (D ^ 2 - ‖x‖ ^ 2))‖ = D := by
  have hsq : 0 ≤ D ^ 2 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have hs := radiusAppend_norm_sq x (Real.sqrt (D ^ 2 - ‖x‖ ^ 2))
  rw [Real.sq_sqrt hsq] at hs
  nlinarith [norm_nonneg (radiusAppend x (Real.sqrt (D ^ 2 - ‖x‖ ^ 2)))]

def radiusExtendedInstance {d : ℕ} {L D : ℝ} (I : Instance d L D) (r : ℝ)
    (hL : 0 < L) (hrad : ‖radiusAppend (I.initial - I.minimizer) r‖ ≤ D) :
    Instance (d + 1) L D where
  f := fun x => I.f (radiusDrop d x)
  convex := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simpa only [map_add, map_smul] using
      I.convex.2 (Set.mem_univ (radiusDrop d x)) (Set.mem_univ (radiusDrop d y)) ha hb hab
  differentiable := by
    intro x
    exact (radius_extension_hasGradientAt I.f x _ (I.differentiable _).hasGradientAt).differentiableAt
  gradient_lipschitz := by
    intro x y
    rw [radius_extension_gradient I.f I.differentiable,
      radius_extension_gradient I.f I.differentiable, ← map_sub, radiusLift_norm]
    exact (I.gradient_lipschitz _ _).trans
      (mul_le_mul_of_nonneg_left (by simpa only [map_sub] using radiusDrop_norm_le (x - y)) hL.le)
  initial := radiusAppend I.initial r
  minimizer := radiusAppend I.minimizer 0
  minimizes := by intro x; simpa only [radiusDrop_radiusAppend] using I.minimizes (radiusDrop d x)
  radius := by simpa only [radiusAppend_sub, sub_zero] using hrad

theorem radiusExtendedInstance_gradient {d : ℕ} {L D : ℝ} (I : Instance d L D) (r : ℝ)
    (hL : 0 < L) (hrad : ‖radiusAppend (I.initial - I.minimizer) r‖ ≤ D)
    (x : Space (d + 1)) :
    gradient (radiusExtendedInstance I r hL hrad).f x = radiusLift d (gradient I.f (radiusDrop d x)) :=
  radius_extension_gradient I.f I.differentiable x

theorem radiusExtendedInstance_iterate {d : ℕ} {L D : ℝ} (I : Instance d L D) (r : ℝ)
    (hL : 0 < L) (hrad : ‖radiusAppend (I.initial - I.minimizer) r‖ ≤ D) (h : ℝ) (n : ℕ) :
    radiusDrop d (iterate (radiusExtendedInstance I r hL hrad) h n) = iterate I h n := by
  induction n with
  | zero => exact radiusDrop_radiusAppend I.initial r
  | succ n ih =>
    rw [iterate, map_sub, map_smul, radiusExtendedInstance_gradient, radiusDrop_radiusLift,
      ih, iterate]

theorem radiusExtendedInstance_output {d : ℕ} {L D : ℝ} (I : Instance d L D) (r : ℝ)
    (hL : 0 < L) (hrad : ‖radiusAppend (I.initial - I.minimizer) r‖ ≤ D) (N : ℕ) (h c : ℝ) :
    radiusDrop d (output (radiusExtendedInstance I r hL hrad) N h c) = output I N h c := by
  simp only [output, map_add, map_smul, map_sub, radiusExtendedInstance_iterate]
  change radiusDrop d (radiusAppend I.initial r) +
    c • (iterate I h N - radiusDrop d (radiusAppend I.initial r)) = _
  rw [radiusDrop_radiusAppend]

theorem radius_equality_embedding_proved {d : ℕ} {L D : ℝ}
    (I : Instance d L D) (hL : 0 < L) (hD : 0 < D) :
    ∃ J : Instance (d + 1) L D, ‖J.initial - J.minimizer‖ = D ∧
      ∀ N h c, ‖gradient J.f (output J N h c)‖ = ‖gradient I.f (output I N h c)‖ := by
  let r := Real.sqrt (D ^ 2 - ‖I.initial - I.minimizer‖ ^ 2)
  have hrad : ‖radiusAppend (I.initial - I.minimizer) r‖ = D :=
    radius_append_equal_radius _ hD I.radius
  let J := radiusExtendedInstance I r hL hrad.le
  refine ⟨J, ?_, ?_⟩
  · change ‖radiusAppend I.initial r - radiusAppend I.minimizer 0‖ = D
    simpa only [radiusAppend_sub, sub_zero] using hrad
  · intro N h c
    rw [radiusExtendedInstance_gradient, radiusLift_norm, radiusExtendedInstance_output]

end
end CriticalExtrapolation.Paper
