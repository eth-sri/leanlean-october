module

public import GS.CompactFibres
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-! Field-generic matrix algebra, Cayley calculus and Frobenius geometry over `RCLike 𝕜`,
shared by the real orthogonal and the complex unitary cases. -/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix InnerProductSpace
open scoped ComplexOrder
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

set_option hygiene false in
scoped notation "𝕄" => Matrix (Fin n) (Fin n) 𝕜

/-- Entries connecting different block labels vanish. -/
def Supp (block : Fin n → ℕ) (A : 𝕄) : Prop := ∀ i j, block i ≠ block j → A i j = 0

namespace Supp
variable {block : Fin n → ℕ} {A B : 𝕄}
theorem one : Supp block (1 : 𝕄) := fun i j h => by simp [show i ≠ j by grind]
theorem conjTranspose (h : Supp block A) : Supp block Aᴴ := fun i j h' => by aesop
theorem add (hA : Supp block A) (hB : Supp block B) : Supp block (A + B) := fun i j h => by
  simp [hA i j h, hB i j h]
theorem smul (a : ℝ) (hA : Supp block A) : Supp block (a • A) := fun i j h => by aesop
theorem mul (hA : Supp block A) (hB : Supp block B) : Supp block (A * B) := fun i j h => by
  rw [mul_apply]; exact Finset.sum_eq_zero fun t _ => by by_cases block i = block t <;> aesop
end Supp

/-- The unitary equations. -/
def Uni (A : 𝕄) : Prop := Aᴴ * A = 1 ∧ A * Aᴴ = 1

section
variable {A : 𝕄}
theorem uni_iff : Uni A ↔ A ∈ unitaryGroup (Fin n) 𝕜 :=
  by rfl

theorem Uni.of (h : Aᴴ * A = 1) : Uni A := ⟨h, mul_eq_one_comm.mp h⟩
theorem Uni.conjTranspose (h : Uni A) : Uni Aᴴ := uni_iff.2 (Unitary.star_mem (uni_iff.1 h))
end

theorem Uni.mul {A B : 𝕄} (hA : Uni A) (hB : Uni B) : Uni (A * B) :=
  uni_iff.2 (mul_mem (uni_iff.1 hA) (uni_iff.1 hB))

/-! ## Cayley algebra -/

section
variable {A X Y : 𝕄}
theorem cancel_left (hA : A.det ≠ 0) (h : A * X = A * Y) : X = Y :=
  ((isUnit_iff_isUnit_det A).2 hA.isUnit).mul_left_cancel h

theorem cancel_right (hA : A.det ≠ 0) (h : X * A = Y * A) : X = Y :=
  ((isUnit_iff_isUnit_det A).2 hA.isUnit).mul_right_cancel h

theorem cancel_congruence (hA : A.det ≠ 0) (h : Aᴴ * X * A = Aᴴ * Y * A) : X = Y :=
  cancel_left (by simp_all) (cancel_right hA h)

end

section
variable (A : 𝕄)
def cayley : 𝕄 := (1 - A) * (1 + A)⁻¹

def admissible : Prop := (1 + A).det ≠ 0

end

section
variable {A : 𝕄}
theorem cayley_mul (hA : admissible A) : cayley A * (1 + A) = 1 - A := by
  simp [cayley, Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hA)]

theorem one_add_cayley_mul (hA : admissible A) :
    (1 + cayley A) * (1 + A) = (2 : ℝ) • (1 : 𝕄) := by
  rw [Matrix.add_mul, Matrix.one_mul, cayley_mul hA, two_smul]; abel

theorem admissible_cayley (hA : admissible A) : admissible (cayley A) :=
  det_ne_zero_of_right_inverse (B := (1 / 2 : ℝ) • (1 + A)) <| by
    rw [Matrix.mul_smul, one_add_cayley_mul hA, smul_smul]; norm_num

theorem cayley_involutive (hA : admissible A) : cayley (cayley A) = A := by
  apply cancel_right (admissible_cayley hA)
  rw [cayley_mul (admissible_cayley hA)]
  apply cancel_right hA
  rw [Matrix.sub_mul, Matrix.one_mul, cayley_mul hA, Matrix.mul_assoc, one_add_cayley_mul hA,
    two_smul, Matrix.mul_add]
  noncomm_ring

theorem cayley_conj_mul (hA : admissible A) :
    (1 + A)ᴴ * (cayley A)ᴴ = (1 - A)ᴴ := by
  rw [← conjTranspose_mul, cayley_mul hA]

theorem cayley_unitary (hs : Aᴴ = -A) (hA : admissible A) : Uni (cayley A) := by
  refine .of (cancel_congruence (Y := 1) hA ?_)
  rw [show (1 + A)ᴴ * ((cayley A)ᴴ * cayley A) * (1 + A) =
    ((1 + A)ᴴ * (cayley A)ᴴ) * (cayley A * (1 + A)) by noncomm_ring, cayley_conj_mul hA,
    cayley_mul hA]
  simp_all
  noncomm_ring

end

theorem cayley_isSkew {Q : 𝕄} (hQ : Uni Q) (hd : admissible Q) :
    (cayley Q)ᴴ = -cayley Q := by
  refine eq_neg_of_add_eq_zero_left (cancel_congruence (Y := 0) hd ?_)
  rw [show (1 + Q)ᴴ * ((cayley Q)ᴴ + cayley Q) * (1 + Q) = ((1 + Q)ᴴ * (cayley Q)ᴴ) * (1 + Q) +
    (1 + Q)ᴴ * (cayley Q * (1 + Q)) by noncomm_ring, cayley_conj_mul hd, cayley_mul hd]
  simp
  noncomm_ring
  simp [hQ.1]

@[simp] theorem cayley_zero : cayley (0 : 𝕄) = 1 := by simp [cayley]

@[simp] theorem admissible_one : admissible (1 : 𝕄) := by
  simpa using admissible_cayley (A := (0 : 𝕄)) (by simp [admissible])

theorem admissible_of_isSkew {A : 𝕄} (hA : Aᴴ = -A) : admissible A := by
  have hpos := PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self A)
  have he : (1 - A) * (1 + A) = 1 + Aᴴ * A := by rw [hA]; noncomm_ring
  have hdet := isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp hpos.isUnit)
  rw [← he, det_mul] at hdet
  aesop

theorem cayley_intertwine {A B P : 𝕄} (hA : admissible A) (hB : admissible B) (h : A * P = P * B) :
    cayley A * P = P * cayley B := by
  apply cancel_right hB
  rw [Matrix.mul_assoc, show P * (1 + B) = (1 + A) * P by simp [Matrix.mul_add, Matrix.add_mul, h],
    ← Matrix.mul_assoc, cayley_mul hA, Matrix.mul_assoc, cayley_mul hB]
  simp [Matrix.sub_mul, Matrix.mul_sub, h]

/-! ## Smoothness over real scalars -/

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smooth_mul_at {A B : E → 𝕄} {x : E} (hA : ContDiffAt ℝ ⊤ A x) (hB : ContDiffAt ℝ ⊤ B x) :
    ContDiffAt ℝ ⊤ (fun y => A y * B y) x := by
  refine contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => ?_
  simp only [Matrix.mul_apply]
  fun_prop

theorem smooth_conjTranspose_at {A : E → 𝕄} {x : E} (hA : ContDiffAt ℝ ⊤ A x) :
    ContDiffAt ℝ ⊤ (fun y => (A y)ᴴ) x :=
  contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j =>
    (RCLike.conjCLE (K := 𝕜)).contDiff.contDiffAt.comp x (contDiffAt_pi.mp (contDiffAt_pi.mp hA j) i)

theorem smooth_matrix_product {A B : E → 𝕄} (hA : ContDiff ℝ ⊤ A) (hB : ContDiff ℝ ⊤ B) :
    ContDiff ℝ ⊤ (fun x => A x * B x) :=
  contDiff_iff_contDiffAt.2 fun _ => smooth_mul_at hA.contDiffAt hB.contDiffAt

theorem smooth_det : ContDiff ℝ ⊤ (fun A : 𝕄 => A.det) := by
  simp only [det_apply']
  fun_prop

theorem smooth_inverse_at (A : 𝕄) (hA : A.det ≠ 0) : ContDiffAt ℝ ⊤ (fun B : 𝕄 => B⁻¹) A := by
  simp only [inv_def, Ring.inverse_eq_inv]
  refine contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => ?_
  simp only [Matrix.smul_apply, adjugate_apply, smul_eq_mul]
  refine (smooth_det.contDiffAt.inv hA).mul (smooth_det.contDiffAt.comp _ ?_)
  refine contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b => ?_
  simp only [updateRow_apply]
  split_ifs <;> fun_prop

theorem smooth_cayley_comp_at {A : E → 𝕄} {x : E} (hA : ContDiffAt ℝ ⊤ A x) (hd : admissible (A x)) :
    ContDiffAt ℝ ⊤ (fun y => cayley (A y)) x :=
  smooth_mul_at (contDiffAt_const.sub hA) ((smooth_inverse_at _ hd).comp x (contDiffAt_const.add hA))

theorem admissible_open : IsOpen {A : 𝕄 | admissible A} :=
  isOpen_ne.preimage (smooth_det.continuous.comp (continuous_const.add continuous_id))

end Smooth

theorem hasDerivAt_matrix_mul {f g : ℝ → 𝕄} {u v : 𝕄} {t : ℝ} (hf : HasDerivAt f u t) (hg : HasDerivAt g v t) :
    HasDerivAt (fun t => f t * g t) (u * g t + f t * v) t := by
  refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i)) k).mul ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hg k)) j)

theorem hasDerivAt_matrix_conjTranspose {f : ℝ → 𝕄} {u : 𝕄} (hf : HasDerivAt f u 0) :
    HasDerivAt (fun t => (f t)ᴴ) uᴴ 0 :=
  hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf j)) i).star

def tangentParam (B₂ P B₁ C Ω : 𝕄) : 𝕄 := B₂ * C * P * B₁ + B₂ * P * Ω * B₁

theorem hasDerivAt_product2 (P : 𝕄) {f g : ℝ → 𝕄} {u v : 𝕄} (hf : HasDerivAt f u 0) (hg : HasDerivAt g v 0) :
    HasDerivAt (fun t => f t * P * g t) (u * P * g 0 + f 0 * P * v) 0 := by
  simpa using hasDerivAt_matrix_mul (hasDerivAt_matrix_mul hf (hasDerivAt_const 0 P)) hg

/-- Cayley normalization with derivative the identity at zero. -/
def unitCayley (A : 𝕄) : 𝕄 := cayley ((-1 / 2 : ℝ) • A)

@[simp] theorem unitCayley_zero : unitCayley (0 : 𝕄) = 1 := by simp [unitCayley]

theorem skew_smul {A : 𝕄} (a : ℝ) (hA : Aᴴ = -A) : (a • A)ᴴ = -(a • A) := by aesop

theorem unitCayley_smooth_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → 𝕄) (hs : ContDiff ℝ ⊤ A) (hk : ∀ x, (A x)ᴴ = -A x) :
    ContDiff ℝ ⊤ (fun x => unitCayley (A x)) :=
  contDiff_iff_contDiffAt.2 fun x => smooth_cayley_comp_at (hs.contDiffAt.const_smul _)
    (admissible_of_isSkew (skew_smul _ (hk x)))

section
variable (A : 𝕄)
theorem cayley_line_derivative (hk : Aᴴ = -A) :
    HasDerivAt (fun t : ℝ => cayley (t • A)) ((-2 : ℝ) • A) 0 := by
  have hA := ((hasDerivAt_id' (x := (0 : ℝ))).smul_const A).congr_deriv (one_smul ℝ A)
  obtain ⟨D, hd⟩ : ∃ D, HasDerivAt (fun t : ℝ => cayley (t • A)) D 0 :=
    ⟨_, ((smooth_cayley_comp_at (A := fun t : ℝ => t • A) (by fun_prop) (x := 0)
      (by simp [admissible])).differentiableAt (by simp)).hasDerivAt⟩
  have hm := hasDerivAt_matrix_mul hd (hA.const_add 1)
  rw [show (fun t : ℝ => cayley (t • A) * (1 + t • A)) = fun t => 1 - t • A from
    funext fun t => cayley_mul (admissible_of_isSkew (skew_smul t hk))] at hm
  have hu := hm.unique (hA.const_sub 1)
  simp only [zero_smul, add_zero, Matrix.mul_one, cayley_zero, Matrix.one_mul] at hu
  obtain rfl := eq_sub_of_add_eq hu
  convert hd using 1
  rw [neg_smul, two_smul]; abel

theorem unitCayley_line_derivative (hk : Aᴴ = -A) :
    HasDerivAt (fun t : ℝ => unitCayley (t • A)) A 0 := by
  have hd := cayley_line_derivative _ (skew_smul (-1 / 2 : ℝ) hk)
  simp only [smul_smul, show (-2 : ℝ) * (-1 / 2) = 1 by norm_num, one_smul] at hd
  simpa only [unitCayley, smul_smul, mul_comm (-1 / 2 : ℝ)] using hd

end

theorem contDiff_val (S : Submodule ℝ 𝕄) : ContDiff ℝ ⊤ (Subtype.val : S → 𝕄) :=
  S.subtypeL.contDiff

/-! ## Frobenius geometry -/

/-- The real Frobenius pairing `Re tr (Aᴴ B)`. -/
def frob (A B : 𝕄) : ℝ := RCLike.re (trace (Aᴴ * B))

@[simp] theorem frob_zero_left (A : 𝕄) : frob 0 A = 0 := by simp [frob]

theorem frob_comm (A B : 𝕄) : frob A B = frob B A := by
  rw [frob, frob, ← RCLike.conj_re, ← RCLike.star_def, ← trace_conjTranspose]; simp

section
variable (A B C : 𝕄)
theorem frob_add_left : frob (A + B) C = frob A C + frob B C := by
  simp [frob, Matrix.add_mul]

theorem frob_sub_left : frob (A - B) C = frob A C - frob B C := by
  simp [frob, Matrix.sub_mul]

end

theorem frob_smul_left (a : ℝ) (A B : 𝕄) : frob (a • A) B = a * frob A B := by
  simp [frob, RCLike.smul_re]

section
variable (A : 𝕄)
theorem frob_self_nonneg : 0 ≤ frob A A :=
  (RCLike.nonneg_iff.1 (posSemidef_conjTranspose_mul_self A).trace_nonneg).1

theorem frob_self_eq_zero : frob A A = 0 ↔ A = 0 := by
  rw [← trace_conjTranspose_mul_self_eq_zero_iff, frob,
    ← RCLike.re_add_im (trace _), (RCLike.nonneg_iff.1 (posSemidef_conjTranspose_mul_self A).trace_nonneg).2]
  simp

end

theorem frob_unitary {U V : 𝕄} (hU : Uni U) (hV : Uni V)
    (X Y : 𝕄) : frob (U * X * Vᴴ) (U * Y * Vᴴ) = frob X Y := by
  simp only [frob, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ, hU.1, Matrix.one_mul, trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, hV.1, Matrix.mul_one]

/-- The matrix space with the Frobenius inner product (a separate type, so the
ambient sup norm on `𝕄` is untouched). -/
def W (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) := Matrix (Fin n) (Fin n) 𝕜

instance : AddCommGroup (W 𝕜 n) := inferInstanceAs (AddCommGroup 𝕄)
instance : Module ℝ (W 𝕜 n) := inferInstanceAs (Module ℝ 𝕄)
instance wCore : InnerProductSpace.Core ℝ (W 𝕜 n) where
  inner := frob (𝕜 := 𝕜)
  conj_inner_symm A B := frob_comm B A
  re_inner_nonneg := frob_self_nonneg
  add_left := frob_add_left
  smul_left A B r := frob_smul_left r A B
  definite A := (frob_self_eq_zero A).1
instance : NormedAddCommGroup (W 𝕜 n) := wCore.toNormedAddCommGroup
instance : InnerProductSpace ℝ (W 𝕜 n) := .ofCore wCore.toCore
instance : FiniteDimensional ℝ (W 𝕜 n) := inferInstanceAs (FiniteDimensional ℝ 𝕄)

section
variable (S : Submodule ℝ 𝕄)
/-- A real subspace of matrices, seen in the Frobenius space. -/
def toWS : Submodule ℝ (W 𝕜 n) := S

/-- Orthogonal Frobenius projection onto a real subspace. -/
def proj : 𝕄 →L[ℝ] 𝕄 :=
  LinearMap.toContinuousLinearMap (toWS S).starProjection.toLinearMap

theorem proj_mem (Z : 𝕄) : proj S Z ∈ S :=
  (toWS S).starProjection_apply_mem (Z : W 𝕜 n)

section
variable (Z Y : 𝕄)
theorem proj_normal (hY : Y ∈ S) : frob (Z - proj S Z) Y = 0 :=
  (toWS S).starProjection_inner_eq_zero (Z : W 𝕜 n) Y hY

theorem proj_unique_normal (hY : Y ∈ S)
    (hn : ∀ W ∈ S, frob (Z - Y) W = 0) : proj S Z = Y :=
  ((toWS S).eq_starProjection_of_mem_of_inner_eq_zero (u := (Z : W 𝕜 n)) hY hn)

end

@[simp] theorem proj_of_mem (Y : 𝕄) (hY : Y ∈ S) : proj S Y = Y :=
  proj_unique_normal S Y Y hY (by simp)

theorem proj_self_adjoint (A B : 𝕄) : frob (proj S A) B = frob A (proj S B) :=
  (toWS S).inner_starProjection_left_eq_right (A : W 𝕜 n) B

end

theorem frob_ext {G H : 𝕄} (h : ∀ A, frob G A = frob H A) : G = H :=
  sub_eq_zero.1 ((frob_self_eq_zero _).1 (by rw [frob_sub_left, h, sub_self]))

section
variable (D : 𝕄 →L[ℝ] ℝ)
/-- The Riesz representative of a real covector. -/
def dualMatrix : 𝕄 :=
  ((toDual ℝ (W 𝕜 n)).symm (LinearMap.toContinuousLinearMap (D : 𝕄 →ₗ[ℝ] ℝ)) : W 𝕜 n)

theorem dualMatrix_represents (A : 𝕄) : D A = frob (dualMatrix D) A :=
  (toDual_symm_apply (𝕜 := ℝ) (E := W 𝕜 n) (x := A) (y := LinearMap.toContinuousLinearMap (D : 𝕄 →ₗ[ℝ] ℝ))).symm

end

def dualCLM : (𝕄 →L[ℝ] ℝ) →L[ℝ] 𝕄 := LinearMap.toContinuousLinearMap
  { toFun := dualMatrix
    map_add' _ _ := frob_ext fun _ => by simp [frob_add_left, ← dualMatrix_represents]
    map_smul' _ _ := frob_ext fun _ => by simp [frob_smul_left, ← dualMatrix_represents] }

section
variable (f : 𝕄 → ℝ)
def ambientGradient (X : 𝕄) : 𝕄 := dualCLM (fderiv ℝ f X)

theorem ambientGradient_represents (X A : 𝕄) :
    fderiv ℝ f X A = frob (ambientGradient f X) A := dualMatrix_represents _ A

end

end GS.Shared
