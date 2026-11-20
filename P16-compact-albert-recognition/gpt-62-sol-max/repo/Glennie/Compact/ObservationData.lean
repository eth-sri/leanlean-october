/- Protected observation and reconstruction data. -/
module

public import Glennie.Native.Statements
public import Glennie.Theorems.ProjectorFrame
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Glennie.Compact.OperationalPhi
public import Glennie.Compact.NativeQFamilyLedger
meta import Glennie.Compact.NativeQFamilyLedger
meta import Lean.Elab.Command
@[expose] public section

namespace Glennie.SubmissionR03
noncomputable section
open Glennie.Compact.Affine20

def score (T : Triple) : ℝ :=
  let x := encoder (T f0)
  let y := encoder (T f1)
  let z := encoder (T f2)
  4 * delta x y z (halfAmplitude x) y -
    delta x y z x y - delta x y z 1 y
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

def noisyPhi (r : Readouts) : ℝ := weightedScore r / (Nat.cast 2 : ℝ)


end
end Glennie.SubmissionR03

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
variable (e : E) (t : E → ℝ) (j : E → E → E)

def encoder (p : Fin 3 → E) : E := p 2 - p 0
def pairing (x y : E) : ℝ := t (j x y)
def quad (x z : E) : E :=
  (2 : ℝ) • j x (j x z) - j (j x x) z
def phi (x y z : E) : ℝ :=
  pairing t j (quad j x (quad j y z) - quad j y (quad j x z))
    (quad j z (j x y))
def ledger (T : Triple E) : Ledger54 :=
  (fun i k l => t (j (j (T 0 i) (T 1 k)) (T 2 l)),
   fun i k => pairing t j (T 0 i) (T 1 k),
   fun k l => pairing t j (T 1 k) (T 2 l),
   fun l i => pairing t j (T 2 l) (T 0 i))
def power (p : Fin 3 → E) (s : Fin 2) : E :=
  if s = 0 then encoder p else j (encoder p) (encoder p)
def qSingle
    (T : Triple E) (v : Fin 3) (s : Fin 2) : ℝ :=
  pairing t j (power j (T v) 0) (power j (T v) s)
def qPair
    (T : Triple E) (v w : Fin 3) (s r : Fin 2) : ℝ :=
  pairing t j (power j (T v) s) (power j (T w) r)
def qTriple
    (T : Triple E) (s r u : Fin 2) : ℝ :=
  t (j (j (power j (T 0) s) (power j (T 1) r)) (power j (T 2) u))
def q26 (T : Triple E) : Fin 26 → ℝ := qFamilyTable% (qSingle t j T) (qPair t j T) (qTriple t j T) using 0 1 2 0 1
def half (x : E) : E := (1 / 2 : ℝ) • (e + x)
def contrast (x y z v : E) : ℝ :=
  pairing t j z
    (quad j y (quad j x (quad j z v)) - quad j x (quad j y (quad j z v)))
def delta (x y z a rho : E) : ℝ :=
  contrast t j x y z (quad j a rho)
def score (T : Triple E) : ℝ :=
  let x := encoder (T 0)
  let y := encoder (T 1)
  let z := encoder (T 2)
  4 * delta t j x y z (half e x) y - delta t j x y z x y - delta t j x y z e y

end
end Glennie.SubmissionR04Intrinsic.Local

namespace Glennie.SubmissionR03
noncomputable section

def flatScale : ℝ := 1 / Real.sqrt 3
def flatXN : Albert := ⟨1, 0, -1, 0, 0, 0⟩
def flatY1 : Albert := ⟨0, 0, 0, octScalar 1, -octI, octScalar 1⟩

def flatBase : Glennie.Compact.Affine20.Triple := ![projectorFrame flatXN,
  projectorFrame (flatScale • flatY1), projectorFrame (flatScale • witnessZ)]

end
end Glennie.SubmissionR03

namespace Glennie.SubmissionR03
noncomputable section
open Glennie.Compact.Affine20

/-- The signed scalar of the three fixed-orientation frame encoders. -/
def phiOf (T : Triple) : ℝ :=
  phi (encoder (T f0)) (encoder (T f1)) (encoder (T f2))

end
end Glennie.SubmissionR03

namespace Glennie.SubmissionR04Intrinsic

noncomputable section
set_option autoImplicit false

structure BasedCubic (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  form : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ
  swap12 : ∀ x y z : E, form ![x, y, z] = form ![y, x, z]
  swap23 : ∀ x y z : E, form ![x, y, z] = form ![x, z, y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (P : BasedCubic E) (e : E)

def cubic (x : E) : ℝ := P.form (fun _ : Fin 3 => x)
def metric (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (-1 / 3 : ℝ) • fderiv ℝ
    (fun y : E => fderiv ℝ (fun z : E => Real.log (cubic P z)) y) x
def tangent : Submodule ℝ E :=
  (fderiv ℝ (cubic P) e).ker
def traceAt : E →L[ℝ] ℝ := fderiv ℝ (cubic P) e
def rawPair : E →L[ℝ] E →L[ℝ] ℝ :=
  (traceAt P e).smulRight (traceAt P e) -
    fderiv ℝ (fun z : E => fderiv ℝ (cubic P) z) e
def adjoint (x : E) : E :=
  (rawPair P e).inverse (fderiv ℝ (cubic P) x)
def product (x y : E) : E :=
  (1 / 2 : ℝ) • ((adjoint P e (x + y) - adjoint P e x - adjoint P e y) +
    traceAt P e x • y + traceAt P e y • x -
    (traceAt P e x * traceAt P e y - rawPair P e x y) • e)
local notation "operatorNormedAdd(" X "," Y ")" =>
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := X) (F := Y) (σ₁₂ := RingHom.id ℝ)
local notation "operatorNormedSpace(" X "," Y ")" =>
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := X) (F := Y) (σ₁₂ := RingHom.id ℝ)

section TangentOperators
local notation "W" => tangent P e

open Lean in
local macro "operator_instances " stem:ident " : " X:term "," Y:term : command => do
  let mk (suffix : String) := mkIdent (Name.mkSimple (stem.getId.toString ++ suffix))
  `(local instance $(mk "NormedAddCommGroup"):ident : NormedAddCommGroup ($X →L[ℝ] $Y) := operatorNormedAdd($X,$Y)
    local instance $(mk "NormedSpace"):ident : NormedSpace ℝ ($X →L[ℝ] $Y) := operatorNormedSpace($X,$Y))

operator_instances tangentDual : W, ℝ
operator_instances tangentBilinear : W, W →L[ℝ] ℝ
operator_instances tangentTrilinear : W, W →L[ℝ] W →L[ℝ] ℝ
operator_instances tangentEnd : W, W
operator_instances tangentVectorBilinear : W, W →L[ℝ] W
operator_instances tangentInverse : W →L[ℝ] ℝ, W

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
local instance taskAmbientDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := operatorNormedAdd(E,ℝ)
local instance taskAmbientDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := operatorNormedSpace(E,ℝ)
local instance taskAmbientEndSpace : NormedSpace ℝ (E →L[ℝ] E) := operatorNormedSpace(E,E)
/-- Literal derivative of the varying normalized log-Hessian metric. -/
def ambientMetricD1 (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (metric P) x
/-- Three-term affine Koszul covector, before any Hessian-symmetry shortcut. -/
def ambientKoszulTensor (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (ambientMetricD1 P x + (ambientMetricD1 P x).flip -
    ((((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv).toContinuousLinearMap :
      (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ).comp
      (ambientMetricD1 P x).flip))
/-- Actual ambient affine connection coefficient. Positivity later proves that
the total metric inverse is the genuine inverse near the normalized base. -/
def ambientConnection (x : E) : E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)
    (metric P x).inverse).comp (ambientKoszulTensor P x)
/-- Actual covariant derivative in a constant affine direction. -/
def ambientCovariantDerivative (u : E)
    (Y : E → E) (x : E) : E :=
  fderiv ℝ Y x u + ambientConnection P x u (Y x)
/-- Actual curvature on all ambient vectors. The constant direction fields
commute, so their Lie bracket vanishes. This is not a product definition. -/
def ambientCurvature (x u v w : E) : E :=
  ambientCovariantDerivative P u (ambientCovariantDerivative P v (fun _ : E => w)) x -
    ambientCovariantDerivative P v (ambientCovariantDerivative P u (fun _ : E => w)) x

end
end Glennie.SubmissionR04Intrinsic

namespace Glennie.SubmissionR04Intrinsic.Local
noncomputable section
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
structure Automorphism (t : E → ℝ) (j : E → E → E) where
  equiv : E ≃ₗ[ℝ] E
  map_product : ∀ x y, equiv (j x y) = j (equiv x) (equiv y)
  map_trace : ∀ x, t (equiv x) = t x
def mapAtoms {t : E → ℝ} {j : E → E → E}
    (g : Automorphism t j) (T : Triple E) : Triple E := fun a i => g.equiv (T a i)
section
variable (e : E) (t : E → ℝ) (j : E → E → E)

def orbit (S : Triple E) : Set (Triple E) :=
  {T | ∃ g : Automorphism t j, mapAtoms g S = T}
def fibre54 (b : Chart) : Set (Triple E) :=
  {T | (∀ a, Frame e t j (T a)) ∧ ledger t j T = Glennie.SubmissionR03.decode20 b}
def fibre20 (b : Chart) : Set (Triple E) :=
  {T | (∀ a, Frame e t j (T a)) ∧ Glennie.SubmissionR03.encode20 (ledger t j T) = b}
def SameSign (T S : Triple E) : Prop :=
  (score e t j T < 0 ∧ score e t j S < 0) ∨
    (0 < score e t j T ∧ 0 < score e t j S)
def Admitted
    (V : Set Chart) (T : Triple E) : Prop :=
  (∀ a, Frame e t j (T a)) ∧ Glennie.SubmissionR03.encode20 (ledger t j T) ∈ V
def TwoOrbitSections (V : Set Chart) : Prop :=
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
def ScoreComplete (V : Set Chart) : Prop :=
  ∀ T S : Triple E, (∀ a, Frame e t j (T a)) → (∀ a, Frame e t j (S a)) →
    Glennie.SubmissionR03.encode20 (ledger t j T) ∈ V →
    score e t j T ≠ 0 ∧
      ((T ∈ orbit t j S) ↔ q26 t j T = q26 t j S ∧ SameSign e t j T S)
end

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

namespace Glennie.SubmissionR03

open Glennie.Compact.Affine20

theorem score_eq_two_phi (T : Triple) : score T = 2 * phiOf T :=
  division_free (encoder (T 0)) (encoder (T 1)) (encoder (T 2))

end Glennie.SubmissionR03
