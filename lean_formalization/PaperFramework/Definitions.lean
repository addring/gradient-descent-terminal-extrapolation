import CriticalExtrapolation
import Mathlib.Data.Fintype.Option
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Shared mathematical objects for the whole-paper skeleton.
This namespace is separate from the fully proved foundation. Unfinished results live in the
other `PaperFramework` files and may use `sorry`, as requested on 2026-10-11.
-/

namespace CriticalExtrapolation.Paper

open scoped BigOperators
open Filter Topology

noncomputable section

structure Parameters (N : ℕ) (h c : ℝ) : Prop where
  n_pos : 0 < N
  h_pos : 0 < h
  h_le_one : h ≤ 1
  c_ge_one : 1 ≤ c

def S (N : ℕ) (h c : ℝ) : ℝ := 1 + (N : ℝ) * h * c

abbrev Vec (N : ℕ) := Direction N
abbrev Mat (N : ℕ) := Matrix (Fin N) (Fin N) ℝ

def quadraticForm {N : ℕ} (M : Mat N) (p : Vec N) : ℝ :=
  ∑ i, ∑ j, M i j * p i * p j

def NonnegativeQuadratic {N : ℕ} (M : Mat N) : Prop := ∀ p, 0 ≤ quadraticForm M p
def PositiveQuadratic {N : ℕ} (M : Mat N) : Prop := ∀ p, p ≠ 0 → 0 < quadraticForm M p

def TEntry {N : ℕ} (h c : ℝ) (i j : Fin N) : ℝ :=
  h * c - (if j < i then h else 0) - (if i = j then 1 else 0)

def DEntry {N : ℕ} (i j : Fin N) : ℝ :=
  (if i = j then 1 else 0) - (if i.val + 1 = j.val then 1 else 0)

def REntry {N : ℕ} (h c : ℝ) (i j : Fin N) : ℝ := TEntry h c i j / queryK N h c i

def slopeLeft {N : ℕ} (i : Fin (N - 1)) : Fin N := ⟨i.val, by omega⟩
def slopeRight {N : ℕ} (i : Fin (N - 1)) : Fin N := ⟨i.val + 1, by omega⟩

def AEntry {N : ℕ} (h c : ℝ) (i : Fin (N - 1)) (j : Fin N) : ℝ :=
  REntry h c (slopeLeft i) j - REntry h c (slopeRight i) j

abbrev Edge (N : ℕ) := Fin N × Fin (N + 1)
abbrev Flow (N : ℕ) := Edge N → ℝ

def edges (N : ℕ) : Finset (Edge N) := Finset.univ.filter (fun e => e.1.val < e.2.val)

def outflow {N : ℕ} (F : Flow N) (i : Fin N) : ℝ :=
  ∑ e ∈ (edges N).filter (fun e => e.1 = i), F e

def inflow {N : ℕ} (F : Flow N) (i : Fin N) : ℝ :=
  ∑ e ∈ (edges N).filter (fun e => e.2.val = i.val), F e

def AdmissibleFlow {N : ℕ} (F : Flow N) : Prop :=
  (∀ e ∈ edges N, 0 ≤ F e) ∧ ∀ i, outflow F i - inflow F i = 1

/-- The virtual output basis vector is zero, although it is an actual flow sink. -/
def extendedBasis {N : ℕ} (i : Fin (N + 1)) (k : Fin N) : ℝ :=
  if i.val = k.val then 1 else 0

def flowMatrix {N : ℕ} (h c : ℝ) (F : Flow N) : Mat N := fun i j =>
  h ^ 2 * c ^ 2 - h * c * S N h c * ∑ e ∈ edges N,
    (F e / queryK N h c e.1) *
      ((extendedBasis e.1.castSucc i - extendedBasis e.2 i) * TEntry h c e.1 j +
        TEntry h c e.1 i * (extendedBasis e.1.castSucc j - extendedBasis e.2 j))

def chainFlow (N : ℕ) : Flow N := fun e =>
  if e.2.val = e.1.val + 1 then (e.1.val : ℝ) + 1 else 0

def M₀ (N : ℕ) (h c : ℝ) : Mat N := flowMatrix h c (chainFlow N)

def lambda {N : ℕ} (h c : ℝ) (F : Flow N) (e : Edge N) : ℝ :=
  2 * h * c * S N h c / queryK N h c e.1 * F e

def outputMultiplier {N : ℕ} (h c : ℝ) (F : Flow N) (i : Fin N) : ℝ :=
  outflow (lambda h c F) i - inflow (lambda h c F) i - 2 * h * c

def IsOptimizer {N : ℕ} (h c : ℝ) (β : Vec N) : Prop :=
  Feasible h c β ∧ ∀ p : Vec N, Feasible h c p → chainObjective h c β ≤ chainObjective h c p

/-- All N difference multipliers and all N−1 slope multipliers are retained. -/
structure CompleteKKT {N : ℕ} (h c : ℝ) (β : Vec N)
    (μ : Fin (N - 1) → ℝ) (ν : Vec N) : Prop where
  feasible : Feasible h c β
  mu_nonnegative : ∀ i, 0 ≤ μ i
  nu_nonnegative : ∀ i, 0 ≤ ν i
  slope_complementarity : ∀ i,
    μ i * (slope h c β (slopeLeft i) - slope h c β (slopeRight i)) = 0
  difference_complementarity : ∀ i, ν i * difference β i = 0
  stationarity : ∀ i,
    2 * (∑ j, M₀ N h c i j * β j) = 2 * auxiliaryValue N h c +
      (∑ k, AEntry h c k i * μ k) + ∑ k, DEntry k i * ν k

def scaledMu {N : ℕ} (h c : ℝ) (μ : Fin (N - 1) → ℝ) (i : ℕ) : ℝ :=
  if hi : i < N - 1 then μ ⟨i, hi⟩ / (2 * h * c * S N h c) else 0

def previousMu {N : ℕ} (h c : ℝ) (μ : Fin (N - 1) → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else scaledMu h c μ (i - 1)

def rowMoment {N : ℕ} (h c : ℝ) (β : Vec N) (μ : Fin (N - 1) → ℝ) (i : Fin N) : ℝ :=
  ((i.val : ℝ) + 1) * difference β i + scaledMu h c μ i.val - previousMu h c μ i.val

def IsMaximalSlopePlateau {N : ℕ} (h c : ℝ) (β : Vec N) (a b : Fin N) : Prop :=
  a ≤ b ∧ (∀ i, a ≤ i → i ≤ b → slope h c β i = slope h c β a) ∧
    (∀ i, i.val + 1 = a.val → slope h c β a < slope h c β i) ∧
    (∀ i, b.val + 1 = i.val → slope h c β i < slope h c β b)

def flowEll {N : ℕ} (h c : ℝ) (β : Vec N) (μ : Fin (N - 1) → ℝ) (i : ℕ) : ℝ :=
  zeroExtend β i - zeroExtend β (i + 1) + scaledMu h c μ i / ((i : ℝ) + 1)

def flowProbability {N : ℕ} (h c : ℝ) (β : Vec N) (μ : Fin (N - 1) → ℝ) (i : ℕ) : ℝ :=
  if i = 0 ∨ i = N then 1 else
    1 - scaledMu h c μ (i - 1) / ((i : ℝ) * flowEll h c β μ i)

def kktProductFlow {N : ℕ} (h c : ℝ) (β : Vec N) (μ : Fin (N - 1) → ℝ) : Flow N := fun e =>
  productFlow (fun i => 1 + (i : ℝ) * flowProbability h c β μ i)
    (flowProbability h c β μ) e.1.val e.2.val

def tail {N : ℕ} (p : Vec N) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin N => i ≤ j.val), p j

def energyF (N : ℕ) (a t : ℝ) : ℝ := (N : ℝ) + a + t
def energyD (N : ℕ) (a : ℝ) (i : ℕ) : ℝ := (N : ℝ) + a - (i : ℝ)
def energyZeta (N : ℕ) (a t : ℝ) (i : ℕ) : ℝ := energyF N a t - (i : ℝ)

def tailZ {N : ℕ} (a t : ℝ) (p : Vec N) (i : Fin (N + 1)) : ℝ :=
  tail p i.val / energyZeta N a t i.val

def tailU {N : ℕ} (a t : ℝ) (p : Vec N) (i : Fin N) : ℝ :=
  tailZ a t p i.castSucc - tailZ a t p i.succ

def homogeneousEnergy {N : ℕ} (a t : ℝ) (p : Vec N) : ℝ :=
  (∑ i, p i) ^ 2 - 2 * energyF N a t * ∑ i,
    ((i.val : ℝ) + 1) * difference p i * (tail p i.val - t * p i) / energyD N a i.val

def energyDiagonal (N : ℕ) (a t : ℝ) (i : ℕ) : ℝ :=
  2 * t * ((i : ℝ) + 1) * energyZeta N a t i * (energyZeta N a t i - 1) /
    (energyD N a i * energyF N a t) - 1

def energyNeighbor (N : ℕ) (a t : ℝ) (i : ℕ) : ℝ :=
  -((t - 1) * ((i : ℝ) + 1) * energyZeta N a t i * (energyZeta N a t i - 2) /
    (energyD N a i * energyF N a t))

def E (N : ℕ) (a t : ℝ) : Mat N := fun i j =>
  if i = j then energyDiagonal N a t i.val else
  if i.val + 1 = j.val then energyNeighbor N a t i.val else
  if j.val + 1 = i.val then energyNeighbor N a t j.val else 0

def H (N : ℕ) (a t : ℝ) : Mat N := fun i j =>
  if i = j then 2 * ((i.val : ℝ) + 1) * energyZeta N a t i.val ^ 2 / energyD N a i.val else
  if i.val + 1 = j.val then
    -(((i.val : ℝ) + 1) * energyZeta N a t i.val * (energyZeta N a t i.val - 2) / energyD N a i.val)
  else if j.val + 1 = i.val then
    -(((j.val : ℝ) + 1) * energyZeta N a t j.val * (energyZeta N a t j.val - 2) / energyD N a j.val)
  else 0

def shiftB (N : ℕ) (a t : ℝ) : ℝ := a / ((N : ℝ) * (a + t))
def shiftMass (a t : ℝ) : ℝ := t / (a + t)
def shiftedDirection {N : ℕ} (a t : ℝ) (p : Vec N) : Vec N :=
  fun i => shiftB N a t + shiftMass a t * p i

def shiftedHarmonic (t : ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range j, 1 / ((k : ℝ) + 1 + 2 * t)

def trialVector (N : ℕ) (t : ℝ) : Vec N := fun i =>
  1 / ((i.val : ℝ) + 2 * t) + shiftedHarmonic t (N - i.val) / (N : ℝ)

def trialNormalization (N : ℕ) (t : ℝ) : ℝ := ∑ i, trialVector N t i
def normalizedTrial (N : ℕ) (t : ℝ) : Vec N := fun i => trialVector N t i / trialNormalization N t
def trialDirection (N : ℕ) (a t : ℝ) : Vec N := shiftedDirection a t (normalizedTrial N t)
def trialParameterMax (t : ℝ) : ℝ := 1 / (2 * t + 1)

def scaledC (N : ℕ) (h k : ℝ) : ℝ := 1 + k / (h * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)))
def scaledA (N : ℕ) (h k : ℝ) : ℝ := k / (h * Real.sqrt (Real.log (N : ℝ)))

def UniformOn (lo hi : ℝ) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ N in atTop, ∀ k ∈ Set.Icc lo hi, |f N k - g k| < ε

/-- `none` is the minimizer; `some (Fin.last N)` is the output, not the terminal iterate. -/
abbrev Query (N : ℕ) := Option (Fin (N + 1))
def starQuery (N : ℕ) : Query N := none
def ordinaryQuery {N : ℕ} (i : Fin N) : Query N := some i.castSucc
def outputQuery (N : ℕ) : Query N := some (Fin.last N)

structure Sample (N d : ℕ) where
  x : Query N → Space d
  g : Query N → Space d
  value : Query N → ℝ

def slack {N d : ℕ} (data : Sample N d) (i j : Query N) : ℝ :=
  data.value i - data.value j - inner ℝ (data.g j) (data.x i - data.x j) -
    ‖data.g i - data.g j‖ ^ 2 / 2

def Interpolates {N d : ℕ} (data : Sample N d) (f : Space d → ℝ) : Prop :=
  (∀ i, f (data.x i) = data.value i) ∧ ∀ i, gradient f (data.x i) = data.g i

def SmoothConvexOne {d : ℕ} (f : Space d → ℝ) : Prop :=
  ConvexOn ℝ Set.univ f ∧ Differentiable ℝ f ∧
    ∀ x z, ‖gradient f x - gradient f z‖ ≤ ‖x - z‖

def sampledInstance {d : ℕ} (I : Instance d 1 1) (N' : ℕ) (h c : ℝ) : Sample N' d where
  x := fun q => match q with
    | none => I.minimizer
    | some i => if i.val < N' then iterate I h i.val else output I N' h c
  g := fun q => gradient I.f (match q with
    | none => I.minimizer
    | some i => if i.val < N' then iterate I h i.val else output I N' h c)
  value := fun q => I.f (match q with
    | none => I.minimizer
    | some i => if i.val < N' then iterate I h i.val else output I N' h c)

def conjugatePotential {N d : ℕ} (data : Sample N d) (u : Space d) : ℝ :=
  ‖u‖ ^ 2 / 2 + sSup {r | ∃ i, r = inner ℝ (data.x i - data.g i) (u - data.g i)}

def recoveredFunction {N d : ℕ} (data : Sample N d) (x : Space d) : ℝ :=
  sSup {r | ∃ u, r = inner ℝ x u - conjugatePotential data u}

def backwardA {N : ℕ} (h c : ℝ) (β : Vec N) : Vec N := fun i =>
  -(∑ j ∈ Finset.univ.filter (fun j : Fin N => i ≤ j), difference β j * slope h c β j)

def backwardB {N : ℕ} (h c : ℝ) (β : Vec N) : Vec N := fun i =>
  ∑ j ∈ Finset.univ.filter (fun j : Fin N => i ≤ j),
    (1 - difference (backwardA h c β) j * applyT h c (backwardA h c β) j) / queryK N h c j

def vec2 (a b : ℝ) : Space 2 := WithLp.toLp 2 (fun k : Fin 2 => if k.val = 0 then a else b)

def perturbationGradient {N : ℕ} (h c ε : ℝ) (β : Vec N) (i : Fin N) : Space 2 :=
  vec2 (1 + backwardA h c β i * ε ^ 2 + backwardB h c β i * ε ^ 4) (β i * ε)

def perturbationInitial {N : ℕ} (h c ε : ℝ) (β : Vec N) : Space 2 :=
  vec2 1 0 + (h * c) • ∑ i, perturbationGradient h c ε β i

def perturbationSample {N : ℕ} (h c ε : ℝ) (β : Vec N) : Sample N 2 :=
  let xs : Query N → Space 2 := fun q => match q with
    | none => 0
    | some j => if hi : j.val < N then
        perturbationInitial h c ε β - h •
          ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < j.val), perturbationGradient h c ε β i
        else vec2 1 0
  let gs : Query N → Space 2 := fun q => match q with
    | none => 0
    | some j => if hi : j.val < N then perturbationGradient h c ε β ⟨j.val, hi⟩ else vec2 1 0
  { x := xs, g := gs, value := fun q => inner ℝ (gs q) (xs q) - ‖gs q‖ ^ 2 / 2 }

end
end CriticalExtrapolation.Paper
