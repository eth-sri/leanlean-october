module
public import Glennie.Compact.ExactCoordinates
public import Glennie.Theorems.ProjectorFrame
public import Glennie.Theorems.Frames
public import Glennie.UnitShifts
public import Mathlib.Algebra.QuadraticAlgebra.Basic
meta import Mathlib.Algebra.QuadraticAlgebra.Basic
meta import Glennie.Compact.ExactCoordinates

/-! Compute the uniform ledger and the Jacobian in a common exact realization
of ℚ[√3]. All numerical identities are transferred across a ring homomorphism. -/
@[expose] public section
namespace Glennie.Compact.FlatBase
noncomputable section
export _root_.Glennie.SubmissionR03 (flatScale flatXN flatY1)
theorem flatScale_sq : flatScale ^ 2 = 1 / 3 := by
  simp [flatScale]

def flatFrameP : Fin 3 → Albert := projectorFrame flatXN
def flatFrameQ : Fin 3 → Albert := projectorFrame (flatScale • flatY1)
def flatFrameR : Fin 3 → Albert := projectorFrame (flatScale • witnessZ)
theorem flatFrameP_encoder : encoder flatFrameP = flatXN := projectorFrame_encoder _
theorem flatFrameQ_encoder : encoder flatFrameQ = flatScale • flatY1 := projectorFrame_encoder _
theorem flatFrameR_encoder : encoder flatFrameR = flatScale • witnessZ := projectorFrame_encoder _

theorem flat_phi : phi (encoder flatFrameP) (encoder flatFrameQ) (encoder flatFrameR) = -4 / 27 := by
  have d : IsDiagonal flatXN := ⟨rfl,rfl,rfl⟩
  have c : InComplexSector flatY1 := by simp [InComplexSector,OctInComplex,flatY1,show SubmissionR03.octI = octI from rfl,octI,quatI,octScalar]
  have v : phi flatXN flatY1 witnessZ = -4 := by
    rw [phi_of_diagonal_complex _ _ _ d c]
    norm_num [flatXN, flatY1,show SubmissionR03.octI = octI from rfl, witnessZ, octI, octK, octJL, octL, quatI, quatJ, quatK,
      octScalar, complexPart, Matrix.det_fin_three, hiddenMatrix, hiddenColumn, Complex.mul_im, Complex.mul_re]
  rw [flatFrameP_encoder, flatFrameQ_encoder, flatFrameR_encoder, phi_smul_second, phi_smul_third, v]
  linear_combination (norm := ring_nf) (-4 * flatScale^4 - 4/3 * flatScale^2 - 4/9) * flatScale_sq

end
end Glennie.Compact.FlatBase

namespace Glennie.Compact.NativeFlatRank20
open Glennie.Exact FlatBase

abbrev K := QuadraticAlgebra ℚ 3 0
abbrev half : K := ⟨1/2,0⟩
abbrev scale : K := ⟨0,1/3⟩
abbrev j := prod (R := K) half
noncomputable def φ : K →+* ℝ :=
  (QuadraticAlgebra.lift ⟨Real.sqrt 3, by norm_num [Real.mul_self_sqrt]⟩).toRingHom

@[simp] theorem cast_half : φ half = 1/2 := by
  norm_num [φ, QuadraticAlgebra.lift_apply_apply, Rat.smul_def]
@[simp] private theorem cast_scale : φ scale = flatScale := by
  simp [φ, QuadraticAlgebra.lift_apply_apply, Rat.smul_def, flatScale]
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

open Qq in
meta instance : Lean.ToExpr K where
  toTypeExpr := q(K)
  toExpr x :=
    let a : Q(ℚ) := Lean.toExpr x.re; let b : Q(ℚ) := Lean.toExpr x.im
    q((⟨$a,$b⟩ : K))

open Qq in
meta instance : Lean.ToExpr (Quaternion K) where
  toTypeExpr := q(Quaternion K)
  toExpr x :=
    let a : Q(K) := Lean.toExpr x.re; let b : Q(K) := Lean.toExpr x.imI
    let c : Q(K) := Lean.toExpr x.imJ; let d : Q(K) := Lean.toExpr x.imK
    q((⟨$a,$b,$c,$d⟩ : Quaternion K))

def project (x : A K) :=
  let xx := j x x
  ![half • (xx - x), Exact.one - xx, half • (xx + x)]
private theorem realize_project (x : A K) (i : Fin 3) :
    realize φ (project x i) = projectorFrame (realize φ x) i := by
  fin_cases i <;> simp [project, projectorFrame, j, realize_prod _ _ cast_half]

def X : A K := (1,0,-1,0,0,0)
def flat (a i : Fin 3) := project (![X, scale • markY (-1), scale • markZ] a) i
noncomputable abbrev T := ![flatFrameP, flatFrameQ, flatFrameR]
private theorem flat_real (a i : Fin 3) : realize φ (flat a i) = T a i := by
  have hx : realize φ X = flatXN := by ext <;> simp [realize, mapQ, mapO, X, flatXN]
  have hy : realize φ (markY (-1)) = flatY1 := by
    ext <;> simp [markY, realize, mapQ, mapO, flatY1,show SubmissionR03.octI = octI from rfl, octScalar, octI, quatI]
  fin_cases a <;> simp [flat, realize_project, hx, hy, flatFrameP, flatFrameQ, flatFrameR, T]

-- Materialize intermediate values and check each table against its specification.
-- This keeps the kernel from re-expanding a tree of nested Jordan products.
set_option synthInstance.maxSize 2000
deriving instance DecidableEq for QuaternionAlgebra

def atoms : Fin 3 → Fin 3 → A K := eval% flat
private theorem check_atoms : atoms = flat := by funext a i; fin_cases a <;> fin_cases i <;> decide +kernel
theorem atoms_real (a i : Fin 3) : realize φ (atoms a i) = T a i := check_atoms ▸ flat_real a i

def pairAt (a i k : Fin 3) := j (atoms (a+1) i) (atoms (a+2) k)
def pairs : Fin 3 → Fin 3 → Fin 3 → A K := eval% pairAt
theorem check_pairs : pairs = pairAt := by
  funext a i; fin_cases a <;> fin_cases i <;> decide +kernel

private theorem uniform_cells (i k l : Fin 3) : pairing (pairs 2 i k) (atoms 2 l) = (⟨1/9,0⟩ : K) := by
  fin_cases i <;> fin_cases k <;> fin_cases l <;> decide +kernel

private theorem literal_uniform : UniformLedger flatFrameP flatFrameQ flatFrameR := by
  intro i k l
  have h := congrArg φ (uniform_cells i k l)
  rw [cast_pairing, check_pairs, pairAt, j, realize_prod _ _ cast_half, atoms_real, atoms_real, atoms_real] at h
  simpa [φ, QuadraticAlgebra.lift_apply_apply, Rat.smul_def, ledger, inner, T] using h

open SubmissionR03 (fullLedger)
private theorem cast_frac (r : ℚ) : φ (⟨r,0⟩ : K) = r := by simp [φ,QuadraticAlgebra.lift_apply_apply,Rat.smul_def]

theorem flat_ledger : fullLedger T =
    (fun _ _ _ => 1/9,fun _ _ => 1/3,fun _ _ => 1/3,fun _ _ => 1/3) := by
  have q : ∀ a i k, pairing (atoms a i) (atoms (a+1) k) = (⟨1/3,0⟩ : K) := by decide +kernel
  have p (a i k : Fin 3) : inner (T a i) (T (a+1) k) = 1/3 := by
    simpa [cast_pairing,atoms_real,cast_frac] using congrArg φ (q a i k)
  exact Prod.ext (funext fun i => funext fun k => funext (literal_uniform i k))
    (Prod.ext (funext fun i => funext (p 0 i)) (Prod.ext (funext fun i => funext (p 1 i)) (funext fun i => funext (p 2 i))))

def tr (x : A K) := x.1 + x.2.1 + x.2.2.1
theorem flat_frames (a : Fin 3) : Frame (T a) := by
  have cert : ∀ a : Fin 3, (∀ i, tr (atoms a i) = 1) ∧
      (∀ i k, j (atoms a i) (atoms a k) = if i = k then atoms a i else 0) ∧
      atoms a 0 + atoms a 1 + atoms a 2 = Exact.one := by decide +kernel
  obtain ⟨ht,hp,hs⟩ := cert a
  have t (x : A K) : φ (tr x) = trace (realize φ x) := by simp [realize,tr,trace]
  have m (i k) := congrArg (realize φ) (hp i k)
  simp only [j,realize_prod _ _ cast_half,atoms_real,apply_ite (realize φ),realize_zero] at m
  exact ⟨fun i => by simpa [t,atoms_real] using congrArg φ (ht i),
    fun i => by simpa using m i i, fun i k h => by simpa [h] using m i k,
    by simpa only [realize_add,atoms_real,realize_one] using congrArg (realize φ) hs⟩
end Glennie.Compact.NativeFlatRank20

namespace Glennie.Compact.FlatBase
theorem flatFrameP_frame : Frame flatFrameP := NativeFlatRank20.flat_frames 0
end Glennie.Compact.FlatBase
