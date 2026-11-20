module
public import Glennie.Compact.ObservationData
public import Glennie.ExactCoordinates
meta import Glennie.ExactCoordinates
public import Glennie.Theorems.ProjectorFrame
public import Glennie.Compact.Affine20.Relabel
public import Glennie.Theorems.Frames
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.QuadraticAlgebra.Basic
meta import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Glennie.BasicLaws
public import Glennie.SectorFactor
public import Mathlib.Data.Rat.Cast.Defs
meta import Mathlib.Data.Rat.Defs
@[expose] public section
namespace Glennie.ExactCoordinates
open scoped Quaternion

variable {R : Type*} [CommRing R]

def flatX : Coords R := ⟨1, 0, -1, 0, 0, 0⟩
def flatY : Coords R := ⟨0, 0, 0, (1, 0), (⟨0,-1,0,0⟩, 0), (1, 0)⟩

noncomputable section

variable (f : R →+* ℝ)

@[simp] theorem realize_flatX : realize f flatX = ⟨1, 0, -1, 0, 0, 0⟩ := by
  ext <;> simp [realize, flatX, rq, ro]

@[simp] theorem realize_flatY : realize f flatY = ⟨0, 0, 0, octScalar 1, -octI, octScalar 1⟩ := by
  ext <;> norm_num [realize, flatY, rq, ro, octScalar, octI, quatI]


end
end Glennie.ExactCoordinates

namespace Glennie.Compact.FlatBase

open Glennie.ExactCoordinates
open scoped QuadraticAlgebra Quaternion

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The flat elements and their coordinates -/

export Glennie.SubmissionR03 (flatBase flatScale flatXN flatY1)

theorem flatScale_sq : flatScale ^ 2 = 1 / 3 := by simp [flatScale]


private theorem phi_flat_unscaled : phi flatXN flatY1 witnessZ = -4 := by
  have h := phi_diagonal_complex_factor 1 0 (-1) 0 0 0 1 (-Complex.I) 1 witnessZ
  norm_num [flatXN, flatY1, diagonalAlbert, complexAlbert, complexOct, octI, quatI, octScalar,
    hiddenMatrix, hiddenColumn, witnessZ, octJL, octL, octK, quatJ, quatK,
    Matrix.det_fin_three, Complex.mul_re, Complex.mul_im, Complex.star_def] at h ⊢
  exact h

abbrev flatFrameP := flatBase 0
abbrev flatFrameQ := flatBase 1
abbrev flatFrameR := flatBase 2
theorem flatFrameP_encoder : encoder flatFrameP = flatXN := projectorFrame_encoder _
theorem flatFrameQ_encoder : encoder flatFrameQ = flatScale • flatY1 := projectorFrame_encoder _
theorem flatFrameR_encoder : encoder flatFrameR = flatScale • witnessZ := projectorFrame_encoder _

theorem flat_phi :
    phi (encoder flatFrameP) (encoder flatFrameQ) (encoder flatFrameR) = -4 / 27 := by
  rw [flatFrameP_encoder, flatFrameQ_encoder, flatFrameR_encoder,
    phi_smul_second, phi_smul_third, phi_flat_unscaled]
  calc
    _ = -4 * (flatScale ^ 2) ^ 3 := by ring
    _ = -4 / 27 := by rw [flatScale_sq]; norm_num

abbrev FlatScalar := QuadraticAlgebra ℤ 3 0

noncomputable def sqrt3Map : FlatScalar →+* ℝ :=
  (QuadraticAlgebra.lift ⟨Real.sqrt 3, by simp⟩).toRingHom

@[simp] theorem sqrt3Map_omega : sqrt3Map ω = Real.sqrt 3 := by simp [sqrt3Map]


-- These frames are scaled by 36 so their coordinates lie in ℤ[√3].
def scaledProject {R : Type*} [CommRing R] (x : Coords R) : Fin 3 → Coords R :=
  let x2 := doubled x x
  ![x2 - (6 : R) • x, (36 : R) • 1 - (2 : R) • x2, x2 + (6 : R) • x]
def scaledFrame {R : Type*} [CommRing R] (s : R) : Fin 3 → Fin 3 → Coords R :=
  ![scaledProject ((3 : R) • flatX),
    scaledProject (s • flatY),
    scaledProject (s • marks R 2)]

private theorem realize_project (x : Coords FlatScalar) (y : Albert) (i : Fin 3)
    (h : realize sqrt3Map x = (3 : ℝ) • y) :
    realize sqrt3Map (scaledProject x i) = (36 : ℝ) • projectorFrame y i := by
  fin_cases i <;>
    norm_num [scaledProject, projectorFrame, h, jordan_smul_left, jordan_smul_right, smul_smul,
      smul_add, smul_sub, map_ofNat]

private theorem scale_eq : (3 : ℝ) * flatScale = Real.sqrt 3 := by unfold flatScale <;> grind

@[simp] theorem realize_scaledFrame (a i : Fin 3) :
    realize sqrt3Map (scaledFrame ω a i) = (36 : ℝ) • flatBase a i := by
  fin_cases a <;> apply realize_project
  all_goals simp [smul_smul, scale_eq, map_ofNat, flatXN, flatY1, SubmissionR03.nativeMarks]

private theorem trace_check (a i : Fin 3) : tr (scaledFrame (ω : FlatScalar) a i) = 36 := by
  fin_cases a <;> fin_cases i <;> decide +kernel

private theorem product_check (a i j : Fin 3) :
    doubled (scaledFrame (ω : FlatScalar) a i) (scaledFrame ω a j) =
      (if i = j then (72 : FlatScalar) else 0) • scaledFrame ω a i := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;> decide +kernel

private theorem unit_check (a : Fin 3) :
    scaledFrame (ω : FlatScalar) a 0 + scaledFrame ω a 1 + scaledFrame ω a 2 = (36 : FlatScalar) • 1 := by
  fin_cases a <;> decide +kernel

theorem flatBase_frames (a : Fin 3) : Frame (flatBase a) := by
  let p := flatBase a
  change Frame p
  have hj (i j : Fin 3) : jordan (p i) (p j) = (if i = j then (1 : ℝ) else 0) • p i := by
    have h := congrArg (realize sqrt3Map) (product_check a i j)
    apply smul_right_injective Albert (by norm_num : (2592 : ℝ) ≠ 0)
    by_cases he : i = j <;>
      norm_num [p, he, apply_ite, jordan_smul_left, jordan_smul_right, smul_smul, map_ofNat] at h ⊢ <;> assumption
  refine ⟨?_, fun i => by simpa [p] using hj i i, fun i j h => by simpa [p, h] using hj i j, ?_⟩
  · intro i
    have h := congrArg sqrt3Map (trace_check a i)
    norm_num [p, map_ofNat, trace_smul] at h ⊢
    exact h
  · apply smul_right_injective Albert (by norm_num : (36 : ℝ) ≠ 0)
    simpa [p, ← smul_add, map_ofNat] using congrArg (realize sqrt3Map) (unit_check a)

theorem flatFrameP_frame : Frame flatFrameP := flatBase_frames 0
theorem flatFrameQ_frame : Frame flatFrameQ := flatBase_frames 1
theorem flatFrameR_frame : Frame flatFrameR := flatBase_frames 2

section
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

@[simp] theorem map_scaledProject (x : Coords R) (i : Fin 3) :
    coeffMap f (scaledProject x i) = scaledProject (coeffMap f x) i := by
  fin_cases i <;> simp [scaledProject, map_ofNat]

@[simp] theorem map_scaledFrame (s : R) (a i : Fin 3) :
    coeffMap f (scaledFrame s a i) = scaledFrame (f s) a i := by
  fin_cases a <;> change coeffMap f (scaledProject _ i) = scaledProject _ i
  all_goals simp only [map_scaledProject, coeffMap_smul, map_ofNat]
  all_goals
    apply congrArg (fun v => scaledProject (_ • v) i)
    apply Coords.ext
    all_goals try simp [coeffMap, marks, flatX, flatY]
    all_goals ext <;> simp [ rq, ro,  ]

end

private def tripleNumerator (i j k : Fin 3) : FlatScalar :=
  tr (doubled (doubled (scaledFrame ω 0 i) (scaledFrame ω 1 j)) (scaledFrame ω 2 k))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
theorem flat_uniform : UniformLedger flatFrameP flatFrameQ flatFrameR := by
  intro i j k
  have h (i j k : Fin 3) : tripleNumerator i j k = 20736 := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel
  have hh := congrArg sqrt3Map (h i j k)
  norm_num [map_ofNat, tripleNumerator, trace_smul, jordan_smul_left, jordan_smul_right, smul_smul] at hh
  unfold ledger
  linarith


/-- The three 9-entry pair-overlap blocks of a uniform frame triple are all 1/3. -/
theorem uniform_pair_blocks (p q r : Fin 3 → Albert) (hp : Frame p) (hq : Frame q)
    (hr : Frame r) (hu : UniformLedger p q r) (i j : Fin 3) :
    inner (p i) (q j) = 1 / 3 ∧ inner (q i) (r j) = 1 / 3 ∧ inner (r i) (p j) = 1 / 3 :=
  ⟨uniformLedger_pair_overlap p q r hr hu i j,
    uniformLedger_pair_overlap q r p hp (uniformLedger_cyclic p q r hu) i j,
    uniformLedger_pair_overlap r p q hq
      (uniformLedger_cyclic q r p (uniformLedger_cyclic p q r hu)) i j⟩

end
end Glennie.Compact.FlatBase
