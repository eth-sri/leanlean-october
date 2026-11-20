module
public import Mathlib.Algebra.Quaternion
public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.RingTheory.Finiteness.Prod
public import Glennie.Compact.Affine20.Relabel

/-! The shared literal definitions for all finite and intrinsic observations. -/
@[expose] public section
namespace Glennie.SubmissionR03
noncomputable section
open Glennie Compact.Affine20
def f0 : Fin 3 := ⟨0, Nat.zero_lt_succ 2⟩
def f1 : Fin 3 := ⟨1, Nat.lt_succ_of_le (Nat.le_succ 1)⟩
def f2 : Fin 3 := ⟨2, Nat.lt_succ_self 2⟩
def b0 : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩
def b1 : Fin 2 := ⟨1, Nat.lt_succ_self 1⟩
/-- The complete triple-trace block and three pair-trace blocks. -/
def fullLedger (T : Triple) : Ledger54 :=
  (ledger (T f0) (T f1) (T f2),
   fun i j => inner (T f0 i) (T f1 j),
   fun j k => inner (T f1 j) (T f2 k),
   fun k i => inner (T f2 k) (T f0 i))
/-- The fixed frame encoder or its Jordan square. -/
def framePower (p : Fin 3 → Albert) (s : Fin 2) : Albert :=
  if s = b0 then encoder p else jordan (encoder p) (encoder p)
def qSingle (T : Triple) (v : Fin 3) (s : Fin 2) : ℝ :=
  inner (framePower (T v) b0) (framePower (T v) s)
def qPair (T : Triple) (v w : Fin 3) (s t : Fin 2) : ℝ :=
  inner (framePower (T v) s) (framePower (T w) t)
def qTriple (T : Triple) (s t u : Fin 2) : ℝ :=
  trace (jordan (jordan (framePower (T f0) s) (framePower (T f1) t))
    (framePower (T f2) u))
/-- Six single-frame readings, twelve pair readings and eight triple readings. -/
def q26 (T : Triple) : Fin 26 → ℝ := ![
  qSingle T f0 b0, qSingle T f0 b1, qSingle T f1 b0, qSingle T f1 b1,
  qSingle T f2 b0, qSingle T f2 b1,
  qPair T f0 f1 b0 b0, qPair T f0 f1 b0 b1,
  qPair T f0 f1 b1 b0, qPair T f0 f1 b1 b1,
  qPair T f1 f2 b0 b0, qPair T f1 f2 b0 b1,
  qPair T f1 f2 b1 b0, qPair T f1 f2 b1 b1,
  qPair T f2 f0 b0 b0, qPair T f2 f0 b0 b1,
  qPair T f2 f0 b1 b0, qPair T f2 f0 b1 b1,
  qTriple T b0 b0 b0, qTriple T b0 b0 b1,
  qTriple T b0 b1 b0, qTriple T b0 b1 b1,
  qTriple T b1 b0 b0, qTriple T b1 b0 b1,
  qTriple T b1 b1 b0, qTriple T b1 b1 b1]
/-- The signed scalar of the three fixed-orientation frame encoders. -/
def phiOf (T : Triple) : ℝ :=
  phi (encoder (T f0)) (encoder (T f1)) (encoder (T f2))
/-- An explicit flat reference with ordered outcomes. -/
def quatI : Quaternion ℝ := ⟨0,1,0,0⟩
def quatJ : Quaternion ℝ := ⟨0,0,1,0⟩
def quatK : Quaternion ℝ := ⟨0,0,0,1⟩
def octI : Octonion := (quatI,0)
def octK : Octonion := (quatK,0)
def octL : Octonion := (0,1)
def octJL : Octonion := (0,quatJ)
def witnessZ : Albert := ⟨0,0,0,octJL,-octL,-octK⟩
def flatScale : ℝ := 1 / Real.sqrt 3
def flatXN : Albert := ⟨1, 0, -1, 0, 0, 0⟩
def flatY1 : Albert := ⟨0, 0, 0, octScalar 1, -octI, octScalar 1⟩
def projectorFrame (x : Albert) : Fin 3 → Albert :=
  ![(1 / (Nat.cast 2 : ℝ)) • (jordan x x - x), 1 - jordan x x,
    (1 / (Nat.cast 2 : ℝ)) • (jordan x x + x)]
def flatBase : Triple := ![projectorFrame flatXN,
  projectorFrame (flatScale • flatY1), projectorFrame (flatScale • witnessZ)]
/-- A single automorphism acts on every label of all three frames. -/
def mapAtoms (g : CompactAutomorphism) (T : Triple) : Triple :=
  fun a i => g.equiv (T a i)
/-- Six algebraic readings use an unnormalized input y. -/
def contrast (x y z v : Albert) : ℝ :=
  inner z (U y (U x (U z v)) - U x (U y (U z v)))
def halfAmplitude (x : Albert) : Albert :=
  (1 / (Nat.cast 2 : ℝ)) • ((1 : Albert) + x)
def delta (x y z a rho : Albert) : ℝ := contrast x y z (U a rho)
def score (T : Triple) : ℝ :=
  let x := encoder (T f0)
  let y := encoder (T f1)
  let z := encoder (T f2)
  4 * delta x y z (halfAmplitude x) y -
    delta x y z x y - delta x y z 1 y
/-- Q20 is the final twenty Q26 readings; the first six are fixed on actual frames. -/
def q20 (T : Triple) : Fin 20 → ℝ :=
  fun i => q26 T ⟨i.val + 6, Nat.add_lt_add_right i.2 6⟩
def centred (L : Ledger54) (i j k : Fin 3) : ℝ :=
  L.1 i j k - (L.2.1 i j + L.2.2.1 j k + L.2.2.2 k i) / (Nat.cast 3 : ℝ) + (Nat.cast 2 : ℝ) / (Nat.cast 9 : ℝ)
def encode20 (L : Ledger54) : Fin 20 → ℝ :=
  ![L.2.1 f0 f0 - 1 / (Nat.cast 3 : ℝ), L.2.1 f0 f1 - 1 / (Nat.cast 3 : ℝ), L.2.1 f1 f0 - 1 / (Nat.cast 3 : ℝ), L.2.1 f1 f1 - 1 / (Nat.cast 3 : ℝ),
    L.2.2.1 f0 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.1 f0 f1 - 1 / (Nat.cast 3 : ℝ), L.2.2.1 f1 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.1 f1 f1 - 1 / (Nat.cast 3 : ℝ),
    L.2.2.2 f0 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.2 f0 f1 - 1 / (Nat.cast 3 : ℝ), L.2.2.2 f1 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.2 f1 f1 - 1 / (Nat.cast 3 : ℝ),
    centred L f0 f0 f0, centred L f0 f0 f1, centred L f0 f1 f0, centred L f0 f1 f1,
    centred L f1 f0 f0, centred L f1 f0 f1, centred L f1 f1 f0, centred L f1 f1 f1]
/-- The chart decoder uses zero-margin 2-by-2 and 2-by-2-by-2 lifts. -/
def ext3 (x y : ℝ) : Fin 3 → ℝ := ![x, y, -(x + y)]
def lift4 (a b c d : ℝ) (i j : Fin 3) : ℝ := ext3 (ext3 a b j) (ext3 c d j) i
def lift8 (h000 h001 h010 h011 h100 h101 h110 h111 : ℝ) (i j k : Fin 3) : ℝ :=
  ext3 (ext3 (ext3 h000 h001 k) (ext3 h010 h011 k) j)
    (ext3 (ext3 h100 h101 k) (ext3 h110 h111 k) j) i
def decP (v : Fin 20 → ℝ) (i j : Fin 3) : ℝ := 1 / (Nat.cast 3 : ℝ) + lift4 (v 0) (v 1) (v 2) (v 3) i j
def decQ (v : Fin 20 → ℝ) (j k : Fin 3) : ℝ := 1 / (Nat.cast 3 : ℝ) + lift4 (v 4) (v 5) (v 6) (v 7) j k
def decR (v : Fin 20 → ℝ) (k i : Fin 3) : ℝ := 1 / (Nat.cast 3 : ℝ) + lift4 (v 8) (v 9) (v 10) (v 11) k i
def decC (v : Fin 20 → ℝ) (i j k : Fin 3) : ℝ :=
  lift8 (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) i j k +
    (decP v i j + decQ v j k + decR v k i) / (Nat.cast 3 : ℝ) - (Nat.cast 2 : ℝ) / (Nat.cast 9 : ℝ)
def decode20 (v : Fin 20 → ℝ) : Ledger54 := (decC v, decP v, decQ v, decR v)
/-- Full admitted fibers and the simultaneous product-and-trace automorphism orbit. -/
def fibre54 (b : Fin 20 → ℝ) : Set Triple :=
  {T | (∀ a : Fin 3, Frame (T a)) ∧ fullLedger T = decode20 b}
def fibre20 (b : Fin 20 → ℝ) : Set Triple :=
  {T | (∀ a : Fin 3, Frame (T a)) ∧ encode20 (fullLedger T) = b}
def autOrbit (S : Triple) : Set Triple :=
  {T | ∃ g : CompactAutomorphism, mapAtoms g S = T}
/-- Six raw algebraic readings, in h+, h-, x+, x-, 1+, 1- order. -/
structure Readouts where
  hPlus : ℝ
  hMinus : ℝ
  xPlus : ℝ
  xMinus : ℝ
  onePlus : ℝ
  oneMinus : ℝ
def weightedScore (r : Readouts) : ℝ :=
  4 * r.hPlus - 4 * r.hMinus - r.xPlus + r.xMinus - r.onePlus + r.oneMinus
def rawPlus (x y z a : Albert) : ℝ :=
  inner z (U y (U x (U z (U a y))))
def rawMinus (x y z a : Albert) : ℝ :=
  inner z (U x (U y (U z (U a y))))
def exactReadouts (T : Triple) : Readouts :=
  let x := encoder (T f0)
  let y := encoder (T f1)
  let z := encoder (T f2)
  ⟨rawPlus x y z (halfAmplitude x), rawMinus x y z (halfAmplitude x),
   rawPlus x y z x, rawMinus x y z x, rawPlus x y z 1, rawMinus x y z 1⟩
def ErrorsAtMost (noisy exact : Readouts) (ε : ℝ) : Prop :=
  |noisy.hPlus - exact.hPlus| ≤ ε ∧
  |noisy.hMinus - exact.hMinus| ≤ ε ∧
  |noisy.xPlus - exact.xPlus| ≤ ε ∧
  |noisy.xMinus - exact.xMinus| ≤ ε ∧
  |noisy.onePlus - exact.onePlus| ≤ ε ∧
  |noisy.oneMinus - exact.oneMinus| ≤ ε
/-- The native raw trace norm, used to state perturbation radii independently. -/
def nA (x : Albert) : ℝ := Real.sqrt (inner x x)
def noisyPhi (r : Readouts) : ℝ := weightedScore r / (Nat.cast 2 : ℝ)
/-- The coordinatewise special Jordan product in arbitrary Euclidean dimension. -/
def diagonalNProduct {n : ℕ} (a b : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp (Nat.cast 2 : ENNReal) (fun i => a i * b i)
/-- The same 27 fixed bracketed words evaluated in any marked product. -/
def witnessX : Albert := ⟨-1,0,1,0,0,0⟩
def witnessY : Albert := ⟨0,0,0,octScalar 1,octI,octScalar 1⟩
def nativeMarks : Fin 3 → Albert := ![witnessX,witnessY,witnessZ]
def wordValues {E : Type*} (e : E) (a : Fin 3 → E)
    (j : E → E → E) : Fin 27 → E :=
  let x := a f0
  let y := a f1
  let z := a f2
  let xx := j x x
  let xy := j x y
  let xz := j x z
  let yy := j y y
  let yz := j y z
  let zz := j z z
  ![e, x, y, z, xx, xy, xz, yy, yz, zz,
    j x xy, j x xz, j x yy, j x yz, j x zz,
    j y xz, j y yz, j y zz,
    j xx yy, j xx yz, j xx zz, j xy yz, j xy zz, j yy zz,
    j x (j y xz), j x (j y yz), j x (j y zz)]
def nativeWordValues : Fin 27 → Albert := wordValues 1 nativeMarks jordan
def candidateWordValues {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Fin 27 → E :=
  wordValues e a (fun x y => j x y)
/-- The generated unital product-closed submodule is independent of the list. -/
def generated {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Submodule ℝ E :=
  sInf {K : Submodule ℝ E | e ∈ K ∧ (∀ i, a i ∈ K) ∧
    (∀ x ∈ K, ∀ y ∈ K, j x y ∈ K)}
/-- Three fully determined families of scalar data from the fixed native words. -/
structure Match27 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Prop where
  gram : ∀ i k,
    Inner.inner ℝ (candidateWordValues e a j i) (candidateWordValues e a j k) =
      inner (nativeWordValues i) (nativeWordValues k)
  mixed : ∀ i k l,
    Inner.inner ℝ (j (candidateWordValues e a j i) (candidateWordValues e a j k))
      (candidateWordValues e a j l) =
      inner (jordan (nativeWordValues i) (nativeWordValues k)) (nativeWordValues l)
  product_sq : ∀ i k,
    Inner.inner ℝ (j (candidateWordValues e a j i) (candidateWordValues e a j k))
      (j (candidateWordValues e a j i) (candidateWordValues e a j k)) =
      inner (jordan (nativeWordValues i) (nativeWordValues k))
        (jordan (nativeWordValues i) (nativeWordValues k))
end
end Glennie.SubmissionR03

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
set_option autoImplicit false
structure BasedCubic (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  form : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ
  swap12 : ∀ x y z : E, form ![x, y, z] = form ![y, x, z]
  swap23 : ∀ x y z : E, form ![x, y, z] = form ![x, z, y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def cubic (P : BasedCubic E) (x : E) : ℝ := P.form (fun _ : Fin 3 => x)
def metric (P : BasedCubic E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (-1 / 3 : ℝ) • fderiv ℝ
    (fun y : E => fderiv ℝ (fun z : E => Real.log (cubic P z)) y) x
def tangent (P : BasedCubic E) (e : E) : Submodule ℝ E :=
  (fderiv ℝ (cubic P) e).ker
def traceAt (P : BasedCubic E) (e : E) : E →L[ℝ] ℝ := fderiv ℝ (cubic P) e
def rawPair (P : BasedCubic E) (e : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (traceAt P e).smulRight (traceAt P e) -
    fderiv ℝ (fun z : E => fderiv ℝ (cubic P) z) e
def adjoint (P : BasedCubic E) (e x : E) : E :=
  (rawPair P e).inverse (fderiv ℝ (cubic P) x)
def product (P : BasedCubic E) (e x y : E) : E :=
  (1 / 2 : ℝ) • ((adjoint P e (x + y) - adjoint P e x - adjoint P e y) +
    traceAt P e x • y + traceAt P e y • x -
    (traceAt P e x * traceAt P e y - rawPair P e x y) • e)
section TangentOperators
variable (P : BasedCubic E) (e : E)
local notation "W" => tangent P e
local instance tangentDualNormedAddCommGroup : NormedAddCommGroup (W →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentDualNormedSpace : NormedSpace ℝ (W →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentBilinearNormedAddCommGroup :
    NormedAddCommGroup (W →L[ℝ] W →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W) (F := W →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentBilinearNormedSpace : NormedSpace ℝ (W →L[ℝ] W →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := W →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentTrilinearNormedAddCommGroup :
    NormedAddCommGroup (W →L[ℝ] W →L[ℝ] W →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W) (F := W →L[ℝ] W →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentTrilinearNormedSpace :
    NormedSpace ℝ (W →L[ℝ] W →L[ℝ] W →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := W →L[ℝ] W →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentEndNormedAddCommGroup : NormedAddCommGroup (W →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W) (F := W) (σ₁₂ := RingHom.id ℝ)
local instance tangentEndNormedSpace : NormedSpace ℝ (W →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := W) (σ₁₂ := RingHom.id ℝ)
local instance tangentVectorBilinearNormedAddCommGroup :
    NormedAddCommGroup (W →L[ℝ] W →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W) (F := W →L[ℝ] W) (σ₁₂ := RingHom.id ℝ)
local instance tangentVectorBilinearNormedSpace : NormedSpace ℝ (W →L[ℝ] W →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := W →L[ℝ] W) (σ₁₂ := RingHom.id ℝ)
local instance tangentInverseNormedAddCommGroup :
    NormedAddCommGroup ((W →L[ℝ] ℝ) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W →L[ℝ] ℝ) (F := W) (σ₁₂ := RingHom.id ℝ)
local instance tangentInverseNormedSpace : NormedSpace ℝ ((W →L[ℝ] ℝ) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W →L[ℝ] ℝ) (F := W) (σ₁₂ := RingHom.id ℝ)
/-- The restricted derivative metric, viewed as the tangent-to-dual map. -/
def tangentMetricDual : W →L[ℝ] W →L[ℝ] ℝ :=
  (metric P e).bilinearComp (tangent P e).subtypeL (tangent P e).subtypeL
/-- Total Mathlib inverse; positivity will prove it is the genuine inverse. -/
def tangentMetricRaise : (W →L[ℝ] ℝ) →L[ℝ] W :=
  (tangentMetricDual P e).inverse
/-- Literal restriction of the given form, without any prescribed curvature. -/
def tangentCubicForm : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => W) ℝ :=
  P.form.compContinuousLinearMap (fun _ : Fin 3 => (tangent P e).subtypeL)
def tangentCubicCurried : W →L[ℝ] W →L[ℝ] W →L[ℝ] ℝ :=
  (((continuousMultilinearCurryFin1 ℝ W (W →L[ℝ] ℝ)).toContinuousLinearEquiv).toContinuousLinearMap).comp
    ((tangentCubicForm P e).curryRight.curryLeft)
/-- Raising the last cubic slot by the actual restricted metric. -/
def independentRaisedCubic : W →L[ℝ] W →L[ℝ] W :=
  ((ContinuousLinearMap.compL ℝ W (W →L[ℝ] ℝ) W)
    (tangentMetricRaise P e)).comp (tangentCubicCurried P e)
/-- Full basepoint formula; its equality to actual curvature is a theorem below. -/
def independentCurvature (u v w : W) : W :=
  -(tangentMetricDual P e v w) • u + (tangentMetricDual P e u w) • v -
    independentRaisedCubic P e u (independentRaisedCubic P e v w) +
    independentRaisedCubic P e v (independentRaisedCubic P e u w)
end TangentOperators
local instance taskAmbientDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := E) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientBilinearNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientTrilinearNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientTrilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientEndNorm : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := E) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientEndSpace : NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := E) (F := E) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientVectorBilinearNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := E →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientVectorBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := E) (F := E →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientInverseNorm : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E →L[ℝ] ℝ) (F := E) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientInverseSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := E →L[ℝ] ℝ) (F := E) (σ₁₂ := RingHom.id ℝ)
/-- Literal derivative of the varying normalized log-Hessian metric. -/
def ambientMetricD1 (P : BasedCubic E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (metric P) x
/-- Three-term affine Koszul covector, before any Hessian-symmetry shortcut. -/
def ambientKoszulTensor (P : BasedCubic E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (ambientMetricD1 P x + (ambientMetricD1 P x).flip -
    ((((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv).toContinuousLinearMap :
      (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ).comp
      (ambientMetricD1 P x).flip))
/-- Actual ambient affine connection coefficient. Positivity later proves that
the total metric inverse is the genuine inverse near the normalized base. -/
def ambientConnection (P : BasedCubic E) (x : E) : E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)
    (metric P x).inverse).comp (ambientKoszulTensor P x)
/-- Actual covariant derivative in a constant affine direction. -/
def ambientCovariantDerivative (P : BasedCubic E) (u : E)
    (Y : E → E) (x : E) : E :=
  fderiv ℝ Y x u + ambientConnection P x u (Y x)
/-- Actual curvature on all ambient vectors. The constant direction fields
commute, so their Lie bracket vanishes. This is not a product definition. -/
def ambientCurvature (P : BasedCubic E) (x u v w : E) : E :=
  ambientCovariantDerivative P u (ambientCovariantDerivative P v (fun _ : E => w)) x -
    ambientCovariantDerivative P v (ambientCovariantDerivative P u (fun _ : E => w)) x
end
end Glennie.SubmissionR04Intrinsic
namespace Glennie.SubmissionR04Intrinsic.Local
noncomputable section
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev Triple (E : Type*) := Fin 3 → Fin 3 → E
abbrev Ledger54 := Glennie.Compact.Affine20.Ledger54
abbrev Chart := Fin 20 → ℝ
structure Frame (e : E) (t : E → ℝ) (j : E → E → E)
    (p : Fin 3 → E) : Prop where
  trace_one : ∀ i, t (p i) = 1
  idempotent : ∀ i, j (p i) (p i) = p i
  orthogonal : ∀ i k, i ≠ k → j (p i) (p k) = 0
  sum_unit : p 0 + p 1 + p 2 = e
def encoder (p : Fin 3 → E) : E := p 2 - p 0
def pairing (t : E → ℝ) (j : E → E → E) (x y : E) : ℝ := t (j x y)
def quad (j : E → E → E) (x z : E) : E :=
  (2 : ℝ) • j x (j x z) - j (j x x) z
def phi (t : E → ℝ) (j : E → E → E) (x y z : E) : ℝ :=
  pairing t j (quad j x (quad j y z) - quad j y (quad j x z))
    (quad j z (j x y))
def ledger (t : E → ℝ) (j : E → E → E) (T : Triple E) : Ledger54 :=
  (fun i k l => t (j (j (T 0 i) (T 1 k)) (T 2 l)),
   fun i k => pairing t j (T 0 i) (T 1 k),
   fun k l => pairing t j (T 1 k) (T 2 l),
   fun l i => pairing t j (T 2 l) (T 0 i))
def power (j : E → E → E) (p : Fin 3 → E) (s : Fin 2) : E :=
  if s = 0 then encoder p else j (encoder p) (encoder p)
def qSingle (t : E → ℝ) (j : E → E → E)
    (T : Triple E) (v : Fin 3) (s : Fin 2) : ℝ :=
  pairing t j (power j (T v) 0) (power j (T v) s)
def qPair (t : E → ℝ) (j : E → E → E)
    (T : Triple E) (v w : Fin 3) (s r : Fin 2) : ℝ :=
  pairing t j (power j (T v) s) (power j (T w) r)
def qTriple (t : E → ℝ) (j : E → E → E)
    (T : Triple E) (s r u : Fin 2) : ℝ :=
  t (j (j (power j (T 0) s) (power j (T 1) r)) (power j (T 2) u))
def q26 (t : E → ℝ) (j : E → E → E) (T : Triple E) : Fin 26 → ℝ := ![
  qSingle t j T 0 0, qSingle t j T 0 1,
  qSingle t j T 1 0, qSingle t j T 1 1,
  qSingle t j T 2 0, qSingle t j T 2 1,
  qPair t j T 0 1 0 0, qPair t j T 0 1 0 1,
  qPair t j T 0 1 1 0, qPair t j T 0 1 1 1,
  qPair t j T 1 2 0 0, qPair t j T 1 2 0 1,
  qPair t j T 1 2 1 0, qPair t j T 1 2 1 1,
  qPair t j T 2 0 0 0, qPair t j T 2 0 0 1,
  qPair t j T 2 0 1 0, qPair t j T 2 0 1 1,
  qTriple t j T 0 0 0, qTriple t j T 0 0 1,
  qTriple t j T 0 1 0, qTriple t j T 0 1 1,
  qTriple t j T 1 0 0, qTriple t j T 1 0 1,
  qTriple t j T 1 1 0, qTriple t j T 1 1 1]
def half (e x : E) : E := (1 / 2 : ℝ) • (e + x)
def contrast (t : E → ℝ) (j : E → E → E) (x y z v : E) : ℝ :=
  pairing t j z
    (quad j y (quad j x (quad j z v)) - quad j x (quad j y (quad j z v)))
def delta (t : E → ℝ) (j : E → E → E) (x y z a rho : E) : ℝ :=
  contrast t j x y z (quad j a rho)
def score (e : E) (t : E → ℝ) (j : E → E → E) (T : Triple E) : ℝ :=
  let x := encoder (T 0)
  let y := encoder (T 1)
  let z := encoder (T 2)
  4 * delta t j x y z (half e x) y - delta t j x y z x y - delta t j x y z e y
structure Automorphism (t : E → ℝ) (j : E → E → E) where
  equiv : E ≃ₗ[ℝ] E
  map_product : ∀ x y, equiv (j x y) = j (equiv x) (equiv y)
  map_trace : ∀ x, t (equiv x) = t x
def mapAtoms {t : E → ℝ} {j : E → E → E}
    (g : Automorphism t j) (T : Triple E) : Triple E := fun a i => g.equiv (T a i)
def orbit (t : E → ℝ) (j : E → E → E) (S : Triple E) : Set (Triple E) :=
  {T | ∃ g : Automorphism t j, mapAtoms g S = T}
def fibre54 (e : E) (t : E → ℝ) (j : E → E → E) (b : Chart) : Set (Triple E) :=
  {T | (∀ a, Frame e t j (T a)) ∧ ledger t j T = Glennie.SubmissionR03.decode20 b}
def fibre20 (e : E) (t : E → ℝ) (j : E → E → E) (b : Chart) : Set (Triple E) :=
  {T | (∀ a, Frame e t j (T a)) ∧ Glennie.SubmissionR03.encode20 (ledger t j T) = b}
def SameSign (e : E) (t : E → ℝ) (j : E → E → E) (T S : Triple E) : Prop :=
  (score e t j T < 0 ∧ score e t j S < 0) ∨
    (0 < score e t j T ∧ 0 < score e t j S)
def Admitted (e : E) (t : E → ℝ) (j : E → E → E)
    (V : Set Chart) (T : Triple E) : Prop :=
  (∀ a, Frame e t j (T a)) ∧ Glennie.SubmissionR03.encode20 (ledger t j T) ∈ V
def TwoOrbitSections (e : E) (t : E → ℝ) (j : E → E → E) (V : Set Chart) : Prop :=
  ∃ secPos secNeg : Chart → Triple E,
    ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
    (∀ b ∈ V, ∀ a, Frame e t j (secPos b a)) ∧
    (∀ b ∈ V, ∀ a, Frame e t j (secNeg b a)) ∧
    (∀ b ∈ V, ledger t j (secPos b) = Glennie.SubmissionR03.decode20 b) ∧
    (∀ b ∈ V, ledger t j (secNeg b) = Glennie.SubmissionR03.decode20 b) ∧
    (∀ b ∈ V, 0 < score e t j (secPos b)) ∧
    (∀ b ∈ V, score e t j (secNeg b) < 0) ∧
    (∀ b ∈ V, fibre54 e t j b = orbit t j (secNeg b) ∪ orbit t j (secPos b)) ∧
    (∀ b ∈ V, Disjoint (orbit t j (secNeg b)) (orbit t j (secPos b))) ∧
    (∀ b ∈ V, fibre20 e t j b = fibre54 e t j b)
def ScoreComplete (e : E) (t : E → ℝ) (j : E → E → E) (V : Set Chart) : Prop :=
  ∀ T S : Triple E, (∀ a, Frame e t j (T a)) → (∀ a, Frame e t j (S a)) →
    Glennie.SubmissionR03.encode20 (ledger t j T) ∈ V →
    score e t j T ≠ 0 ∧
      ((T ∈ orbit t j S) ↔ q26 t j T = q26 t j S ∧ SameSign e t j T S)
/-- OUTPUT data. The final public theorem must construct this record. -/
structure Result (e : E) (N : E → ℝ) (t : E → ℝ)
    (a B : E → E → ℝ) (j Gamma : E → E → E) (R : E → E → E → E)
    (nativeN : Glennie.Albert → ℝ) where
  A : E ≃ₗ[ℝ] Glennie.Albert
  map_unit : A e = 1
  map_norm : ∀ x, nativeN (A x) = N x
  map_metric : ∀ x y, a x y = Glennie.inner (A x) (A y) / 3
  map_raw_pairing : ∀ x y, B x y = Glennie.inner (A x) (A y)
  map_trace : ∀ x, t x = Glennie.trace (A x)
  map_product : ∀ x y, A (j x y) = Glennie.jordan (A x) (A y)
  map_connection : ∀ x y, A (Gamma x y) = -Glennie.jordan (A x) (A y)
  map_curvature : ∀ u v w, A (R u v w) =
    -(Glennie.jordan (A u) (Glennie.jordan (A v) (A w)) -
      Glennie.jordan (A v) (Glennie.jordan (A u) (A w)))
  V : Set Chart
  V_open : IsOpen V
  flat_mem : Glennie.SubmissionR03.encode20
    (ledger t j (fun f i => A.symm (Glennie.SubmissionR03.flatBase f i))) ∈ V
  two_orbits : TwoOrbitSections e t j V
  score_complete : ScoreComplete e t j V
  q26_iff_ledger : ∀ T S : Triple E,
    (∀ f, Frame e t j (T f)) → (∀ f, Frame e t j (S f)) →
    (q26 t j T = q26 t j S ↔ ledger t j T = ledger t j S)
  score_eq_two_phi : ∀ T : Triple E,
    score e t j T = 2 * phi t j (encoder (T 0)) (encoder (T 1)) (encoder (T 2))
  atoms_generate : ∀ T : Triple E, Admitted e t j V T →
    ∀ K : Submodule ℝ E, (∀ p ∈ K, ∀ q ∈ K, j p q ∈ K) →
      (∀ f i, T f i ∈ K) → K = ⊤
  atom_stabilizer : ∀ T : Triple E, Admitted e t j V T →
    ∀ g : Automorphism t j, mapAtoms g T = T → g.equiv = LinearEquiv.refl ℝ E
  atom_derivation : ∀ T : Triple E, Admitted e t j V T →
    ∀ D : E →ₗ[ℝ] E, (∀ p q, D (j p q) = j (D p) q + j p (D q)) →
      (∀ f i, D (T f i) = 0) → D = 0
end
end Glennie.SubmissionR04Intrinsic.Local
@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
set_option autoImplicit false
def nativeCubic (x : Albert) : ℝ :=
  (Glennie.trace x ^ 3 - 3 * Glennie.trace x * Glennie.inner x x +
    2 * Glennie.inner x (jordan x x)) / 6
theorem nativeTrace_add (x y : Albert) :
    Glennie.trace (x + y) = Glennie.trace x + Glennie.trace y := by
  have h0 : (x+y).d0 = x.d0+y.d0 := rfl
  have h1 : (x+y).d1 = x.d1+y.d1 := rfl
  have h2 : (x+y).d2 = x.d2+y.d2 := rfl
  simp only [Glennie.trace, h0, h1, h2]
  ring
theorem nativeTrace_smul (r : ℝ) (x : Albert) :
    Glennie.trace (r • x) = r • Glennie.trace x := by
  have h0 : (r • x).d0 = r*x.d0 := rfl
  have h1 : (r • x).d1 = r*x.d1 := rfl
  have h2 : (r • x).d2 = r*x.d2 := rfl
  simp only [Glennie.trace, h0, h1, h2, smul_eq_mul]
  ring
def nativeTraceLinear : Albert →ₗ[ℝ] ℝ where
  toFun := Glennie.trace
  map_add' := nativeTrace_add
  map_smul' := nativeTrace_smul
abbrev NativeTangent := nativeTraceLinear.ker
def nativeProject (x : Albert) : NativeTangent := by
  refine ⟨x - (Glennie.trace x / 3) • (1 : Albert), ?_⟩
  change nativeTraceLinear (x - (Glennie.trace x / 3) • (1 : Albert)) = 0
  rw [map_sub, map_smul]
  have hu : nativeTraceLinear (1 : Albert) = 3 := by
    change (1 : ℝ) + 1 + 1 = 3
    norm_num
  rw [hu]
  change Glennie.trace x - (Glennie.trace x / 3) * 3 = 0
  ring
def nativeMetric (u v : NativeTangent) : ℝ :=
  Glennie.inner (u : Albert) (v : Albert) / 3
def nativeK (u v : NativeTangent) : NativeTangent :=
  nativeProject (Glennie.jordan (u : Albert) (v : Albert))
def nativeCurvature (u v w : NativeTangent) : NativeTangent :=
  -(nativeMetric v w) • u + (nativeMetric u w) • v -
    nativeK u (nativeK v w) + nativeK v (nativeK u w)
abbrev ReconstructionResult {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : BasedCubic E) (e : E) :=
  Local.Result e (cubic P) (fun x => traceAt P e x)
    (fun x y => metric P e x y) (fun x y => rawPair P e x y) (product P e)
    (fun x y => ambientConnection P e x y) (ambientCurvature P e) nativeCubic
end
end Glennie.SubmissionR04Intrinsic
