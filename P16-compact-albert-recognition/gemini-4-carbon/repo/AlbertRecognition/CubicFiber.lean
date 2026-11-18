module
public import Glennie.Hilbert
public import Glennie.Automorphism
public import Glennie.Native.Triality
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Module

@[expose] public section
namespace AlbertRecognition
noncomputable section

open Glennie
open scoped BigOperators Quaternion
set_option maxHeartbeats 2000000
attribute [-instance] FloorSemiring.instCharZero RCLike.charZero_rclike

abbrev V := Glennie.traceLinear.ker

@[simp] theorem trace_V (x : V) : Glennie.trace (x : Albert) = 0 := x.property

def project : Albert →ₗ[ℝ] V where
  toFun x := ⟨Glennie.traceless x, Glennie.trace_traceless x⟩
  map_add' _ _ := Subtype.ext <| by simp [Glennie.traceless, add_div, add_smul]; abel
  map_smul' _ _ := Subtype.ext <| by simp [Glennie.traceless, smul_sub, smul_smul, mul_div_assoc]

@[simp] theorem project_coe (x : Albert) : (project x : Albert) = Glennie.traceless x := rfl
@[simp] theorem project_V (x : V) : project (x : Albert) = x := Subtype.ext <| by simp [Glennie.traceless]

def gA (x y : V) : ℝ := Glennie.inner (x : Albert) (y : Albert) / 3

theorem gA_comm (x y : V) : gA x y = gA y x := by simp [gA, Glennie.inner_comm]

def KA : V →ₗ[ℝ] V →ₗ[ℝ] V where
  toFun x :=
    { toFun y := project (Glennie.jordan (x : Albert) (y : Albert))
      map_add' y z := by change project (jordan (x : Albert) ((y : Albert) + z)) = _; rw [jordan_add_right, map_add]
      map_smul' r y := by change project (jordan (x : Albert) (r • (y : Albert))) = _; rw [jordan_smul_right, map_smul]; rfl }
  map_add' x y := LinearMap.ext fun z => by change project (jordan ((x : Albert) + y) z) = _; rw [jordan_add_left, map_add]; rfl
  map_smul' r x := LinearMap.ext fun y => by change project (jordan (r • (x : Albert)) y) = _; rw [jordan_smul_left, map_smul]; rfl

@[simp] theorem KA_apply (x y : V) : KA x y = project (Glennie.jordan (x : Albert) (y : Albert)) := rfl

theorem KA_comm (x y : V) : KA x y = KA y x := by simp [KA_apply, jordan_comm]

def CA (x y z : V) : ℝ := gA (KA x y) z

theorem CA_eq_native (x y z : V) :
    CA x y z = Glennie.inner (Glennie.jordan (x : Albert) (y : Albert)) (z : Albert) / 3 := by
  simp [CA, KA_apply, gA, Glennie.traceless, Glennie.inner_sub_left, Glennie.inner_smul_left, Glennie.inner_unit_left, trace_V]

structure SymmetricCubic where
  form : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  swap12 : ∀ x y z, form x y z = form y x z
  swap23 : ∀ x y z, form x y z = form x z y

def metricBilin : LinearMap.BilinForm ℝ V :=
  (1 / 3 : ℝ) • (_root_.innerₗ Albert).compl₁₂ V.subtype V.subtype

@[simp] theorem metricBilin_apply (x y : V) : metricBilin x y = gA x y := by
  change (1 / 3 : ℝ) * Glennie.inner (x : Albert) (y : Albert) = Glennie.inner (x : Albert) (y : Albert) / 3; ring

theorem metric_nondegenerate : metricBilin.Nondegenerate :=
  have h0 (x : V) (hx : metricBilin x x = 0) : x = 0 :=
    Subtype.ext ((Glennie.inner_self_eq_zero _).mp (by rw [metricBilin_apply, gA] at hx; linarith))
  ⟨fun x hx => h0 x (hx x), fun x hx => h0 x (hx x)⟩

def metricDual : V ≃ₗ[ℝ] Module.Dual ℝ V := metricBilin.toDual metric_nondegenerate

def KB (B : SymmetricCubic) : V →ₗ[ℝ] V →ₗ[ℝ] V := B.form.compr₂ metricDual.symm.toLinearMap

theorem KB_pairing (B : SymmetricCubic) (x y z : V) : gA (KB B x y) z = B.form x y z := by
  rw [← metricBilin_apply]
  change metricBilin ((metricBilin.toDual metric_nondegenerate).symm (B.form x y)) z = _
  exact LinearMap.BilinForm.apply_toDual_symm_apply _ _

theorem KB_comm (B : SymmetricCubic) (x y : V) : KB B x y = KB B y x :=
  metricDual.injective <| LinearMap.ext fun z => by
    change metricBilin (KB B x y) z = metricBilin (KB B y x) z
    rw [metricBilin_apply, metricBilin_apply, KB_pairing, KB_pairing, B.swap12]

theorem KB_selfadjoint (B : SymmetricCubic) (x y z : V) : gA (KB B x y) z = gA y (KB B x z) := by
  rw [gA_comm y, KB_pairing, KB_pairing, B.swap23]

def referenceCubic : SymmetricCubic where
  form := KA.compr₂ metricBilin
  swap12 x y z := by change metricBilin (KA x y) z = metricBilin (KA y x) z; rw [KA_comm]
  swap23 x y z := by
    simp only [LinearMap.compr₂_apply, metricBilin_apply]; change CA x y z = CA x z y
    rw [CA_eq_native, CA_eq_native, inner_jordan_associative, inner_jordan_associative, jordan_comm (y : Albert) z]

theorem KB_referenceCubic : KB referenceCubic = KA :=
  LinearMap.ext fun x => LinearMap.ext fun y => metricDual.injective <| LinearMap.ext fun z => by
    change metricBilin (KB referenceCubic x y) z = metricBilin (KA x y) z
    rw [metricBilin_apply, KB_pairing]; rfl

theorem KB_injective : Function.Injective KB := fun B C h => by
  have hf : B.form = C.form := LinearMap.ext fun x => LinearMap.ext fun y => LinearMap.ext fun z => by
    rw [← KB_pairing B x y z, ← KB_pairing C x y z, h]
  cases B; cases C; cases hf; rfl

def operatorComm (P Q : V →ₗ[ℝ] V) : V →ₗ[ℝ] V := P.comp Q - Q.comp P

def q (B : SymmetricCubic) (x y : V) : V →ₗ[ℝ] V := operatorComm (KB B x) (KB B y)

private def A (T : V → V → V →ₗ[ℝ] V) (B : SymmetricCubic) (x y z : V) : V →ₗ[ℝ] V :=
  operatorComm (KB B x) (T y z) + operatorComm (KB B y) (T z x) + operatorComm (KB B z) (T x y)

private def wedge (x y : V) : V →ₗ[ℝ] V := (metricBilin y).smulRight x - (metricBilin x).smulRight y

private def D (x y : V) : V →ₗ[ℝ] V := wedge x y + q referenceCubic x y

def scalarCubic (r : ℝ) (B : SymmetricCubic) : SymmetricCubic where
  form := r • B.form
  swap12 x y z := congrArg (r * ·) (B.swap12 x y z)
  swap23 x y z := congrArg (r * ·) (B.swap23 x y z)

private theorem KB_scalarCubic (r : ℝ) (B : SymmetricCubic) : KB (scalarCubic r B) = r • KB B :=
  LinearMap.ext fun x => LinearMap.ext fun y => map_smul metricDual.symm r (B.form x y)

private def automorphismV (g : CompactAutomorphism) : V ≃ₗ[ℝ] V where
  toFun x := ⟨g.equiv x, by change trace (g.equiv x) = 0; rw [g.map_trace]; exact trace_V x⟩
  invFun x := ⟨g.symm.equiv x, by change trace (g.symm.equiv x) = 0; rw [g.symm.map_trace]; exact trace_V x⟩
  left_inv _ := Subtype.ext (g.equiv.symm_apply_apply _)
  right_inv _ := Subtype.ext (g.equiv.apply_symm_apply _)
  map_add' _ _ := Subtype.ext (map_add g.equiv _ _)
  map_smul' r x := Subtype.ext (map_smul g.equiv r (x : Albert))

private theorem automorphismV_KA (g : CompactAutomorphism) (x y : V) :
    automorphismV g (KA x y) = KA (automorphismV g x) (automorphismV g y) :=
  Subtype.ext <| by change g.equiv (traceless (jordan x y)) = _; rw [g.map_traceless, g.map_jordan]; rfl

private def pullbackCubic (T : V ≃ₗ[ℝ] V) (B : SymmetricCubic) : SymmetricCubic where
  form :=
    { toFun x := (B.form (T x)).compl₁₂ T.toLinearMap T.toLinearMap
      map_add' _ _ := LinearMap.ext fun _ => LinearMap.ext fun _ => by simp
      map_smul' _ _ := LinearMap.ext fun _ => LinearMap.ext fun _ => by simp }
  swap12 x y z := B.swap12 (T x) (T y) (T z)
  swap23 x y z := B.swap23 (T x) (T y) (T z)

private theorem automorphismV_KB_pullback (g : CompactAutomorphism) (B : SymmetricCubic) (x y : V) :
    automorphismV g (KB (pullbackCubic (automorphismV g) B) x y) =
      KB B (automorphismV g x) (automorphismV g y) :=
  metricDual.injective <| LinearMap.ext fun z => by
    obtain ⟨w, rfl⟩ := (automorphismV g).surjective z
    change metricBilin (automorphismV g _) (automorphismV g w) = metricBilin _ (automorphismV g w)
    rw [metricBilin_apply, metricBilin_apply, show gA (automorphismV g _) (automorphismV g w) = gA _ w from
      congrArg (· / 3) (g.inner_map _ _), KB_pairing, KB_pairing]; rfl

attribute [local irreducible] KB

private theorem A_q_self (B : SymmetricCubic) : A (q B) B = 0 := by
  funext x y z; apply LinearMap.ext; intro v
  simp only [A, q, operatorComm, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, Pi.zero_apply, LinearMap.zero_apply]; abel

private theorem q_scalarCubic (r : ℝ) (B : SymmetricCubic) : q (scalarCubic r B) = r ^ 2 • q B := by
  funext x y; apply LinearMap.ext; intro z
  change operatorComm (KB (scalarCubic r B) x) (KB (scalarCubic r B) y) z = r ^ 2 • operatorComm (KB B x) (KB B y) z
  rw [KB_scalarCubic]; simp only [operatorComm, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_smul, sq]; module

private theorem A_D_zero_of_A_q_zero (B : SymmetricCubic) (hB : A (q referenceCubic) B = 0) : A D B = 0 := by
  have hw : A wedge B = 0 := by
    funext x y z; apply LinearMap.ext; intro v
    simp only [A, wedge, operatorComm, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smulRight_apply, metricBilin_apply, map_sub, map_smul, Pi.zero_apply, LinearMap.zero_apply,
      ← KB_selfadjoint B x z v, ← KB_selfadjoint B x y v, ← KB_selfadjoint B y x v,
      ← KB_selfadjoint B y z v, ← KB_selfadjoint B z y v, ← KB_selfadjoint B z x v,
      KB_comm B x y, KB_comm B x z, KB_comm B y z]; abel
  rw [show A D B = A wedge B + A (q referenceCubic) B by
    funext x y z; apply LinearMap.ext; intro v
    simp only [A, D, operatorComm, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add, Pi.add_apply]; abel,
    hw, hB, add_zero]

private theorem A_q_pullback_zero (g : CompactAutomorphism) (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    A (q referenceCubic) (pullbackCubic (automorphismV g) B) = 0 := by
  have hint {P Q R S : V →ₗ[ℝ] V} (hP : ∀ v, automorphismV g (P v) = R (automorphismV g v))
      (hQ : ∀ v, automorphismV g (Q v) = S (automorphismV g v)) (v : V) :
      automorphismV g (operatorComm P Q v) = operatorComm R S (automorphismV g v) := by
    simp only [operatorComm, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hP, hQ]
  have hq (w s v : V) : automorphismV g (q referenceCubic w s v) =
      q referenceCubic (automorphismV g w) (automorphismV g s) (automorphismV g v) := by
    simp only [q, KB_referenceCubic]; exact hint (automorphismV_KA g w) (automorphismV_KA g s) v
  funext x y z; apply LinearMap.ext; intro v; apply (automorphismV g).injective
  have ht (u w s : V) := hint (automorphismV_KB_pullback g B u) (hq w s) v
  simpa only [A, Pi.zero_apply, LinearMap.add_apply, map_add, map_zero, LinearMap.zero_apply, ht] using
    (show A (q referenceCubic) B (automorphismV g x) (automorphismV g y) (automorphismV g z) (automorphismV g v) = 0 by rw [hB]; rfl)

@[simp] private theorem albert_neg_d0 (x : Albert) : (-x).d0 = -x.d0 := rfl
@[simp] private theorem albert_neg_d1 (x : Albert) : (-x).d1 = -x.d1 := rfl
@[simp] private theorem albert_neg_d2 (x : Albert) : (-x).d2 = -x.d2 := rfl
@[simp] private theorem albert_neg_o01 (x : Albert) : (-x).o01 = -x.o01 := rfl
@[simp] private theorem albert_neg_o02 (x : Albert) : (-x).o02 = -x.o02 := rfl
@[simp] private theorem albert_neg_o12 (x : Albert) : (-x).o12 = -x.o12 := rfl

private def e : Fin 3 → Albert := ![⟨1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩]

private def h (i : Fin 3) : V :=
  ⟨(1 : Albert) - (3 : ℝ) • e i, by fin_cases i <;> norm_num [traceLinear_apply, trace, e, unit]⟩

private def X01 : Octonion →ₗ[ℝ] V :=
  { toFun a := ⟨⟨0, 0, 0, a, 0, 0⟩, by norm_num [traceLinear_apply, trace]⟩
    map_add' _ _ := Subtype.ext <| by apply Albert.ext <;> simp
    map_smul' _ _ := Subtype.ext <| by apply Albert.ext <;> simp }
private def X02 : Octonion →ₗ[ℝ] V :=
  { toFun a := ⟨⟨0, 0, 0, 0, a, 0⟩, by norm_num [traceLinear_apply, trace]⟩
    map_add' _ _ := Subtype.ext <| by apply Albert.ext <;> simp
    map_smul' _ _ := Subtype.ext <| by apply Albert.ext <;> simp }
private def X12 : Octonion →ₗ[ℝ] V :=
  { toFun a := ⟨⟨0, 0, 0, 0, 0, a⟩, by norm_num [traceLinear_apply, trace]⟩
    map_add' _ _ := Subtype.ext <| by apply Albert.ext <;> simp
    map_smul' _ _ := Subtype.ext <| by apply Albert.ext <;> simp }

private def frameD : V := ⟨⟨0, 1, -1, 0, 0, 0⟩, by norm_num [traceLinear_apply, trace]⟩

private theorem v_decompose (x : V) :
    x = (((x : Albert).d2 - (x : Albert).d0) / 3) • h 0 + (((x : Albert).d2 - (x : Albert).d1) / 3) • h 1 +
      X01 (x : Albert).o01 + X02 (x : Albert).o02 + X12 (x : Albert).o12 := by
  have ht : (x : Albert).d0 + (x : Albert).d1 + (x : Albert).d2 = 0 := trace_V x
  apply Subtype.ext; apply Albert.ext <;> simp [h, e, X01, X02, X12] <;> linarith

private theorem D_apply_native (x y z : V) :
    (D x y z : Albert) =
      jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
        jordan (y : Albert) (jordan (x : Albert) (z : Albert)) := by
  have htr : trace (jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
      jordan (y : Albert) (jordan (x : Albert) (z : Albert))) = 0 := by
    rw [trace_sub]; change inner (x : Albert) (jordan y z) - inner (y : Albert) (jordan x z) = 0
    rw [← inner_jordan_associative, ← inner_jordan_associative, jordan_comm (y : Albert) x, sub_self]
  have hcomp (a b c : V) : KA a (KA b c) = project (jordan (a : Albert) (jordan (b : Albert) (c : Albert))) - gA b c • a := by
    change project (jordan (a : Albert) (traceless (jordan b c))) = _
    rw [traceless, jordan_sub_right, jordan_smul_right, jordan_unit_right, map_sub, map_smul, project_V]; rfl
  have hp : D x y z = project (jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
      jordan (y : Albert) (jordan (x : Albert) (z : Albert))) := by
    unfold D q operatorComm; rw [KB_referenceCubic]
    simp only [wedge, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smulRight_apply, metricBilin_apply]
    rw [map_sub, hcomp, hcomp]; abel
  rw [hp, project_coe, traceless, htr]; simp

private theorem jordan_diag_left (r s t : ℝ) (y : Albert) : jordan ⟨r, s, t, 0, 0, 0⟩ y =
    ⟨r * y.d0, s * y.d1, t * y.d2, ((r + s) / 2) • y.o01, ((r + t) / 2) • y.o02, ((s + t) / 2) • y.o12⟩ := by
  apply Albert.ext <;> simp [jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octMul, octConj, show ((0, 0) : Octonion) = 0 from rfl, smul_smul, div_eq_mul_inv] <;> ring_nf

private theorem jordan_X12_left (a : Octonion) (y : Albert) : jordan (X12 a : Albert) y =
    ⟨0, octDot a y.o12, octDot a y.o12, (1 / 2 : ℝ) • octMul y.o02 (octConj a),
      (1 / 2 : ℝ) • octMul y.o01 a, ((y.d1 + y.d2) / 2) • a⟩ := by
  apply Albert.ext <;> simp [X12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octMul, octConj, show ((0, 0) : Octonion) = 0 from rfl, smul_smul, div_eq_mul_inv]
  ring

private theorem h0_coe : (h 0 : Albert) = ⟨-2, 1, 1, 0, 0, 0⟩ := by apply Albert.ext <;> norm_num [h, e, unit]
private theorem h1_coe : (h 1 : Albert) = ⟨1, -2, 1, 0, 0, 0⟩ := by apply Albert.ext <;> norm_num [h, e, unit]

private def frameAction (a : Octonion) : V →ₗ[ℝ] V := D (h 1) (X12 a)

private theorem frameAction_coords (a : Octonion) (x : V) :
    (frameAction a x : Albert) =
      ⟨0, -(3 / 2 : ℝ) * octDot a (x : Albert).o12, (3 / 2 : ℝ) * octDot a (x : Albert).o12,
        -(3 / 4 : ℝ) • octMul (x : Albert).o02 (octConj a),
        (3 / 4 : ℝ) • octMul (x : Albert).o01 a,
        ((3 / 4 : ℝ) * ((x : Albert).d1 - (x : Albert).d2)) • a⟩ := by
  rw [frameAction, D_apply_native, h1_coe, jordan_X12_left, jordan_diag_left, jordan_diag_left, jordan_X12_left]
  apply Albert.ext
  all_goals simp [octDot_comm a, octDot_smul_left, octMul_smul_left, smul_smul]
  all_goals try simp only [← sub_smul, ← neg_smul]
  all_goals congr 1; ring

private theorem h0_diag_actions (B : SymmetricCubic) (hB : A (q referenceCubic) B = 0) :
    ∃ a b : ℝ, KB B (h 0) (h 0) = a • h 0 ∧
      ∀ j : Fin 3, j ≠ 0 → KB B (h 0) (h j + (1 / 2 : ℝ) • h 0) = b • (h j + (1 / 2 : ℝ) • h 0) := by
  let G := KB B (h 0)
  have hAD := A_D_zero_of_A_q_zero B hB
  have hDh01 : D (h 0) (h 1) = 0 := LinearMap.ext fun x => Subtype.ext <| by
    rw [D_apply_native, h0_coe, h1_coe, jordan_diag_left, jordan_diag_left, jordan_diag_left, jordan_diag_left]
    apply Albert.ext <;> simp [smul_smul] <;> norm_num
  have hDh0x (a : Octonion) : D (X12 a) (h 0) = 0 := by
    have hz : D (h 0) (X12 a) = 0 := LinearMap.ext fun x => Subtype.ext <| by
      rw [D_apply_native, h0_coe, jordan_X12_left, jordan_diag_left, jordan_diag_left, jordan_X12_left]
      apply Albert.ext <;> simp [octMul_smul_left, smul_smul] <;> norm_num
    rw [show D (X12 a) (h 0) = -D (h 0) (X12 a) from LinearMap.ext fun x => by
      simp only [D, wedge, q, operatorComm, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smulRight_apply, LinearMap.neg_apply]; abel,
      hz, neg_zero]
  have hG (a : Octonion) (v : V) : G (frameAction a v) = frameAction a (G v) := by
    have hcyc : A D B (h 0) (h 1) (X12 a) v = 0 := by rw [hAD]; rfl
    exact sub_eq_zero.mp (by simpa only [A, frameAction, hDh0x a, hDh01, operatorComm, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.zero_apply, map_zero, sub_self, add_zero, zero_add] using hcyc)
  let y0 := G (h 0)
  have hy0_fa (a : Octonion) : (frameAction a y0 : Albert) = 0 := by
    rw [← hG a (h 0), show frameAction a (h 0) = 0 from Subtype.ext (by
      rw [frameAction_coords, h0_coe]; apply Albert.ext <;> simp [octDot_coordinates, octMul]), map_zero]; rfl
  have hy0 : y0 = (-(y0 : Albert).d0 / 2) • h 0 := by
    have h1 := hy0_fa (octScalar 1); rw [frameAction_coords] at h1
    have ho02 : (y0 : Albert).o02 = 0 := by
      have h := congrArg Albert.o01 h1; simp [octConj_scalar, octMul_scalar_right] at h; exact h
    have ho01 : (y0 : Albert).o01 = 0 := by
      have h := congrArg Albert.o02 h1; simp [octMul_scalar_right] at h; exact h
    have hd12 : (y0 : Albert).d1 = (y0 : Albert).d2 := by
      have h := congrArg (fun z : Albert => z.o12.1.re) h1; simp [octScalar] at h; linarith
    have ho12 : (y0 : Albert).o12 = 0 := by
      have h := congrArg Albert.d2 (hy0_fa (y0 : Albert).o12); rw [frameAction_coords] at h
      simp [octDot_self] at h; exact (octNormSq_eq_zero _).mp h
    have htr : (y0 : Albert).d0 + (y0 : Albert).d1 + (y0 : Albert).d2 = 0 := trace_V y0
    apply Subtype.ext; rw [Submodule.coe_smul, h0_coe]
    apply Albert.ext <;> simp [ho01, ho02, ho12] <;> linarith
  let yd := G frameD
  have hyd_sq (a : Octonion) (ha : octNormSq a = 1) : frameAction a (frameAction a yd) = (-9 / 4 : ℝ) • yd := by
    have hfd : frameAction a (frameAction a frameD) = (-9 / 4 : ℝ) • frameD := by
      have h1 : frameAction a frameD = (3 / 2 : ℝ) • X12 a := Subtype.ext <| by
        rw [frameAction_coords]; apply Albert.ext <;> simp [frameD, X12, octDot_coordinates, octMul] <;> norm_num
      have h2 : frameAction a (X12 a) = (-3 / 2 : ℝ) • frameD := Subtype.ext <| by
        rw [frameAction_coords]; apply Albert.ext <;> simp [frameD, X12, octMul, ha] <;> norm_num
      rw [h1, map_smul, h2, smul_smul]; norm_num
    rw [← hG, ← hG, hfd, map_smul]
  have hyd : yd = (yd : Albert).d1 • frameD := by
    have hu1 : octNormSq (octScalar 1) = 1 := by norm_num [octNormSq, octScalar, Quaternion.normSq_def']
    have hs1 := congrArg Subtype.val (hyd_sq (octScalar 1) hu1)
    rw [frameAction_coords, frameAction_coords] at hs1
    simp only [octConj_scalar, octMul_scalar_right, smul_neg, neg_smul, smul_smul,
      octDot_comm (octScalar 1) (_ • _), octDot_smul_left, octDot_self, hu1, mul_one, Submodule.coe_smul] at hs1
    have hd0 : (yd : Albert).d0 = 0 := by have h := congrArg Albert.d0 hs1; simp at h; exact h
    have ho01 : (yd : Albert).o01 = 0 := by
      have h := congrArg Albert.o01 hs1; dsimp only [Albert.smul_o01] at h
      have h' : ((27 / 16 : ℝ)) • (yd : Albert).o01 = 0 := by linear_combination (norm := module) h
      simpa [smul_smul] using congrArg ((16 / 27 : ℝ) • ·) h'
    have ho02 : (yd : Albert).o02 = 0 := by
      have h := congrArg Albert.o02 hs1; dsimp only [Albert.smul_o02] at h
      have h' : ((27 / 16 : ℝ)) • (yd : Albert).o02 = 0 := by linear_combination (norm := module) h
      simpa [smul_smul] using congrArg ((16 / 27 : ℝ) • ·) h'
    let r := octDot (octScalar 1) (yd : Albert).o12
    have ho12_sc : (yd : Albert).o12 = r • octScalar 1 := by
      have h := congrArg Albert.o12 hs1; dsimp only [Albert.smul_o12] at h
      have h' : (-9 / 4 : ℝ) • ((yd : Albert).o12 - r • octScalar 1) = 0 := by
        dsimp [r]; linear_combination (norm := module) -h
      exact sub_eq_zero.mp (by simpa [smul_smul] using congrArg ((-4 / 9 : ℝ) • ·) h')
    let uI : Octonion := (⟨0, 1, 0, 0⟩, 0)
    have hsi := congrArg (fun z : V => (z : Albert).o12) (hyd_sq uI (by norm_num [uI, octNormSq, Quaternion.normSq_def']))
    rw [frameAction_coords, frameAction_coords] at hsi
    have hdot0 : octDot uI (yd : Albert).o12 = 0 := by rw [ho12_sc]; simp [uI, octDot_coordinates, octScalar]
    simp only [hdot0, mul_zero, sub_self, zero_smul, Submodule.coe_smul, Albert.smul_o12] at hsi
    have ho12 : (yd : Albert).o12 = 0 := by simpa [smul_smul] using congrArg ((-4 / 9 : ℝ) • ·) hsi.symm
    have htr : (yd : Albert).d0 + (yd : Albert).d1 + (yd : Albert).d2 = 0 := trace_V yd
    apply Subtype.ext; rw [Submodule.coe_smul]
    apply Albert.ext <;> simp [frameD, hd0, ho01, ho02, ho12] <;> linarith
  refine ⟨-(y0 : Albert).d0 / 2, (yd : Albert).d1, hy0, fun j hj => ?_⟩
  fin_cases j <;> dsimp
  · exact absurd rfl hj
  · rw [show h 1 + (1 / 2 : ℝ) • h 0 = (-(3 / 2 : ℝ)) • frameD by apply Subtype.ext; apply Albert.ext <;> norm_num [h, e, unit, frameD]]
    change G _ = _; rw [map_smul, show G frameD = _ from hyd]; module
  · rw [show h 2 + (1 / 2 : ℝ) • h 0 = (3 / 2 : ℝ) • frameD by apply Subtype.ext; apply Albert.ext <;> norm_num [h, e, unit, frameD]]
    change G _ = _; rw [map_smul, show G frameD = _ from hyd]; module

private def cyclicAut : CompactAutomorphism := realSwap02Automorphism.comp realSwap01Automorphism
private def cyclicV : V ≃ₗ[ℝ] V := automorphismV cyclicAut

private theorem cyclicV_coords (x : V) :
    (cyclicV x : Albert) = ⟨(x : Albert).d2, (x : Albert).d0, (x : Albert).d1,
      octConj (x : Albert).o02, octConj (x : Albert).o12, (x : Albert).o01⟩ := by
  change realSwap02Automorphism.equiv (realSwap01Automorphism.equiv x) = _
  simp [realSwap01Automorphism, realSwap02Automorphism, octConj_conj]

private theorem cyclicV_h : cyclicV (h 0) = h 1 ∧ cyclicV (h 1) = h 2 ∧ cyclicV (h 2) = h 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Subtype.ext; rw [cyclicV_coords]; apply Albert.ext <;> norm_num [h, e, unit, octConj])

private theorem cyclicV_slots (u : Octonion) :
    cyclicV (X01 u) = X12 u ∧ cyclicV (X02 u) = X01 (octConj u) ∧ cyclicV (X12 u) = X02 (octConj u) := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Subtype.ext; rw [cyclicV_coords]; apply Albert.ext <;> simp [X01, X02, X12, octConj])

private theorem KA_h_self (i : Fin 3) : KA (h i) (h i) = (-1 : ℝ) • h i := by
  have hn : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  fin_cases i <;> apply Subtype.ext <;> apply Albert.ext <;>
    norm_num [KA, project_coe, traceless, trace, h, e, unit, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, hn]

private theorem KA_h_cross (i j : Fin 3) (hij : i ≠ j) : KA (h i) (h j) = h i + h j := by
  have hn : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  fin_cases i <;> fin_cases j <;> try exact absurd rfl hij
  all_goals apply Subtype.ext; apply Albert.ext <;>
    norm_num [KA, project_coe, traceless, trace, h, e, unit, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, hn]

private def cycPow : Fin 3 → CompactAutomorphism := ![.refl, cyclicAut, cyclicAut.comp cyclicAut]

private theorem cycPow_h (i k : Fin 3) : automorphismV (cycPow i) (h k) = h (i + k) := by
  obtain ⟨c0, c1, c2⟩ := cyclicV_h
  have hcomp (x : V) : automorphismV (cyclicAut.comp cyclicAut) x = cyclicV (cyclicV x) := rfl
  have hrefl (x : V) : automorphismV .refl x = x := rfl
  fin_cases i <;> fin_cases k <;> dsimp [cycPow, cyclicV] at * <;> simp [hrefl, hcomp, c0, c1, c2]

private theorem frame_diag_gate (B : SymmetricCubic) (hB : A (q referenceCubic) B = 0) :
    ∃ b : ℝ, ∀ i j : Fin 3, KB B (h i) (h j) = b • KA (h i) (h j) := by
  have hcoarse (i : Fin 3) : ∃ a b : ℝ, KB B (h i) (h i) = a • h i ∧
      ∀ j : Fin 3, j ≠ i → KB B (h i) (h j + (1 / 2 : ℝ) • h i) = b • (h j + (1 / 2 : ℝ) • h i) := by
    let g := cycPow i; let BT := pullbackCubic (automorphismV g) B
    obtain ⟨a, b, ha, hd⟩ := h0_diag_actions BT (A_q_pullback_zero g B hB)
    have tr {x y : V} {r : ℝ} (hh : KB BT x y = r • y) : KB B (automorphismV g x) (automorphismV g y) = r • automorphismV g y := by
      rw [← automorphismV_KB_pullback g B, hh, map_smul]
    have hi0 : automorphismV g (h 0) = h i := by simpa using cycPow_h i 0
    refine ⟨a, b, by simpa [hi0] using tr ha, fun j hj => ?_⟩
    simpa only [hi0, show automorphismV g (h (j - i) + (1 / 2 : ℝ) • h 0) = h j + (1 / 2 : ℝ) • h i by
      rw [map_add, map_smul, cycPow_h, hi0, add_sub_cancel]] using tr (hd (j - i) (sub_ne_zero.mpr hj))
  choose a b hself hcomp' using hcoarse
  have hcross (i j : Fin 3) (hij : i ≠ j) : KB B (h i) (h j) = b i • h j + ((b i - a i) / 2) • h i := by
    rw [show KB B (h i) (h j) = KB B (h i) (h j + (1 / 2 : ℝ) • h i) - (1 / 2 : ℝ) • KB B (h i) (h i) by rw [map_add, map_smul]; module,
      hcomp' i j hij.symm, hself i]; module
  have hab (i j : Fin 3) (hij : i ≠ j) : a i = b i - 2 * b j := by
    have heq : ((b i - a i) / 2) • h i + b i • h j = b j • h i + ((b j - a j) / 2) • h j := by
      rw [add_comm _ (b i • h j), ← hcross i j hij, KB_comm B, hcross j i hij.symm]
    have d0 := congrArg (fun x : V => (x : Albert).d0) heq
    have d1 := congrArg (fun x : V => (x : Albert).d1) heq
    have d2 := congrArg (fun x : V => (x : Albert).d2) heq
    fin_cases i <;> fin_cases j <;> try exact absurd rfl hij
    all_goals (norm_num [h, e, unit] at d0 d1 d2 ⊢; try linarith)
  have r01 := hab 0 1 (by decide); have r02 := hab 0 2 (by decide)
  have r10 := hab 1 0 (by decide); have r12 := hab 1 2 (by decide); have r20 := hab 2 0 (by decide)
  have hb_eq (i : Fin 3) : b i = b 0 := by fin_cases i <;> dsimp <;> linarith
  have ha_eq (i : Fin 3) : a i = -b 0 := by fin_cases i <;> dsimp <;> linarith
  refine ⟨b 0, fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij; rw [hself i, ha_eq i, KA_h_self, smul_smul]; congr 1; ring
  · rw [hcross i j hij, hb_eq i, ha_eq i, KA_h_cross i j hij, smul_add, show (b 0 - -b 0) / 2 = b 0 by ring, add_comm]

private def rotAut (s : ℝ) (hs : (3 / 5) ^ 2 + s ^ 2 = 1) (a : Octonion) (ha : octNormSq a = 1) : CompactAutomorphism :=
  (octMiddleTriple a ha).compactAutomorphism.comp (realRotation12Automorphism (3 / 5) s hs)

private theorem rotAut_h0 (s : ℝ) (hs : (3 / 5) ^ 2 + s ^ 2 = 1) (a : Octonion) (ha : octNormSq a = 1) :
    automorphismV (rotAut s hs a ha) (h 0) = h 0 := Subtype.ext <| by
  change (rotAut s hs a ha).equiv ((1 : Albert) - (3 : ℝ) • e 0) = (1 : Albert) - (3 : ℝ) • e 0
  rw [map_sub, map_smul, (rotAut s hs a ha).map_unit]; congr 2
  have hr : (realRotation12Automorphism (3 / 5) s hs).equiv (e 0) = e 0 := by
    change rot12Apply (3 / 5) s (e 0) = e 0; ext <;> simp [rot12Apply, e, octRe]
  simp only [rotAut, CompactAutomorphism.comp_apply, hr]
  change (octMiddleTriple a ha).albertEquiv (e 0) = e 0
  apply Albert.ext <;> simp [OctRelatedTriple.albertEquiv, e] <;> simp [octMul]

private theorem rotAut_h1 (s : ℝ) (hs : (3 / 5) ^ 2 + s ^ 2 = 1) (a : Octonion) (ha : octNormSq a = 1) :
    automorphismV (rotAut s hs a ha) (h 1) =
      (9 / 25 : ℝ) • h 1 + (s ^ 2) • h 2 + ((9 / 5 : ℝ) * s) • X12 a := Subtype.ext <| by
  change (rotAut s hs a ha).equiv ((1 : Albert) - (3 : ℝ) • e 1) = _
  rw [map_sub, map_smul, (rotAut s hs a ha).map_unit]
  have hr : (realRotation12Automorphism (3 / 5) s hs).equiv (e 1) =
      ⟨0, 9 / 25, s ^ 2, 0, 0, octScalar (-(3 / 5 * s))⟩ := by
    rw [show octScalar (-(3 / 5 * s)) = (⟨-(3 / 5 * s), 0, 0, 0⟩, 0) from rfl]
    change rot12Apply (3 / 5) s (e 1) = _
    ext <;> simp [rot12Apply, e, octRe] <;> ring
  have hm : (octMiddleTriple a ha).compactAutomorphism.equiv ⟨0, 9 / 25, s ^ 2, 0, 0, octScalar (-(3 / 5 * s))⟩ =
      ⟨0, 9 / 25, s ^ 2, 0, 0, (-(3 / 5 * s)) • a⟩ := by
    change (octMiddleTriple a ha).albertEquiv _ = _
    apply Albert.ext <;> simp [OctRelatedTriple.albertEquiv, OctRelatedTriple.middle_B, octMul_scalar_left] <;> simp [octMul]
  simp only [rotAut, CompactAutomorphism.comp_apply, hr, hm]
  have hs2 : s ^ 2 = 16 / 25 := by linarith
  apply Albert.ext <;> simp [h, e, X12, hs2, smul_smul] <;> ring

private theorem cycPow_slots (u : Octonion) :
    automorphismV (cycPow 0) (X12 u) = X12 u ∧
    automorphismV (cycPow 1) (X12 (octConj u)) = X02 u ∧
    automorphismV (cycPow 2) (X12 u) = X01 u :=
  ⟨rfl, by simpa [cycPow, show automorphismV cyclicAut = cyclicV from rfl, octConj_conj] using (cyclicV_slots (octConj u)).2.2,
    by change cyclicV (cyclicV (X12 u)) = X01 u; rw [(cyclicV_slots u).2.2, (cyclicV_slots (octConj u)).2.1, octConj_conj]⟩

private theorem KA_h_self_ne (m : Fin 3) : KA (h m) (h m) ≠ 0 := fun hz => by
  rw [KA_h_self] at hz; have hd := congrArg (fun x : V => (x : Albert).d0) hz
  fin_cases m <;> norm_num [h, e, unit] at hd

private theorem h_Slot_zero {L : V →ₗ[ℝ] V →ₗ[ℝ] V}
    (hL_symm : ∀ x y, L x y = L y x) (hL_hh : ∀ i j, L (h i) (h j) = 0)
    (hL_rot : ∀ (m : Fin 3) (s : ℝ) (hs : (3 / 5) ^ 2 + s ^ 2 = 1) (a : Octonion) (ha : octNormSq a = 1) (i j : Fin 3),
      L (automorphismV ((cycPow m).comp (rotAut s hs a ha)) (h i))
        (automorphismV ((cycPow m).comp (rotAut s hs a ha)) (h j)) = 0)
    (k : Fin 3) (u : Octonion) :
    L (h k) (X01 u) = 0 ∧ L (h k) (X02 u) = 0 ∧ L (h k) (X12 u) = 0 := by
  have hunit (m : Fin 3) (a : Octonion) (ha : octNormSq a = 1) :
      L (h k) (automorphismV (cycPow m) (X12 a)) = 0 := by
    let wm := (9 / 25 : ℝ) • h (m + 1) + (16 / 25 : ℝ) • h (m + 2)
    let zm := automorphismV (cycPow m) (X12 a)
    have hgm (s : ℝ) (hs : (3 / 5) ^ 2 + s ^ 2 = 1) :
        automorphismV ((cycPow m).comp (rotAut s hs a ha)) (h 0) = h m ∧
        automorphismV ((cycPow m).comp (rotAut s hs a ha)) (h 1) = wm + ((9 / 5 : ℝ) * s) • zm := by
      have hc {x : V} : automorphismV ((cycPow m).comp (rotAut s hs a ha)) x =
          automorphismV (cycPow m) (automorphismV (rotAut s hs a ha) x) := rfl
      refine ⟨by rw [hc, rotAut_h0, cycPow_h, add_zero], ?_⟩
      rw [hc, rotAut_h1, show s ^ 2 = 16 / 25 by linarith]; simp only [map_add, map_smul, cycPow_h]; rfl
    have h0p := hL_rot m (4 / 5) (by norm_num) a ha 0 1
    rw [(hgm (4 / 5) (by norm_num)).1, (hgm (4 / 5) (by norm_num)).2, map_add, map_smul,
      show L (h m) wm = 0 by simp [wm, map_add, map_smul, hL_hh], zero_add] at h0p
    have hm0 : L (h m) zm = 0 := by simpa [smul_smul] using congrArg ((25 / 36 : ℝ) • ·) h0p
    have h1p := hL_rot m (4 / 5) (by norm_num) a ha 1 1
    have h1n := hL_rot m (-4 / 5) (by norm_num) a ha 1 1
    rw [(hgm (4 / 5) (by norm_num)).2] at h1p
    rw [(hgm (-4 / 5) (by norm_num)).2] at h1n
    have hdiff : ((144 / 25 : ℝ)) • L wm zm = 0 := by
      have hp : L (wm + ((9 / 5 : ℝ) * (4 / 5)) • zm) (wm + ((9 / 5 : ℝ) * (4 / 5)) • zm) -
          L (wm + ((9 / 5 : ℝ) * (-4 / 5)) • zm) (wm + ((9 / 5 : ℝ) * (-4 / 5)) • zm) = 0 := by rw [h1p, h1n, sub_self]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hL_symm zm wm] at hp
      convert hp using 1; module
    have hwm : L wm zm = 0 := by simpa [smul_smul] using congrArg ((25 / 144 : ℝ) • ·) hdiff
    have hsum : L (h m) zm + L (h (m + 1)) zm + L (h (m + 2)) zm = 0 := by
      have hs : h m + h (m + 1) + h (m + 2) = 0 := by fin_cases m <;> (apply Subtype.ext; apply Albert.ext <;> norm_num [h, e, unit])
      simpa only [map_add, LinearMap.add_apply, map_zero, LinearMap.zero_apply] using congrArg (fun v => L v zm) hs
    have hm2 : L (h (m + 2)) zm = 0 := by
      have h7 : ((7 / 25 : ℝ)) • L (h (m + 2)) zm = 0 := by
        rw [show ((7 / 25 : ℝ)) • L (h (m + 2)) zm =
          L wm zm - (9 / 25 : ℝ) • (L (h m) zm + L (h (m + 1)) zm + L (h (m + 2)) zm) + (9 / 25 : ℝ) • L (h m) zm by
            dsimp [wm]; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]; module,
          hwm, hsum, hm0]; simp
      simpa [smul_smul] using congrArg ((25 / 7 : ℝ) • ·) h7
    have hm1 : L (h (m + 1)) zm = 0 := by linear_combination (norm := module) hsum - hm0 - hm2
    have hk_cases : k = m ∨ k = m + 1 ∨ k = m + 2 := by fin_cases m <;> fin_cases k <;> decide
    rcases hk_cases with rfl | rfl | rfl <;> assumption
  have hall (m : Fin 3) (v : Octonion) : L (h k) (automorphismV (cycPow m) (X12 v)) = 0 := by
    by_cases hv : v = 0
    · subst v; simp
    · obtain ⟨a, r, _, ha, rfl⟩ := octUnit_decomposition v hv
      rw [map_smul, map_smul, map_smul, hunit m a ha, smul_zero]
  obtain ⟨hc0, hc1, hc2⟩ := cycPow_slots u
  exact ⟨hc2 ▸ hall 2 u, hc1 ▸ hall 1 (octConj u), hc0 ▸ hall 0 u⟩

private theorem hk_gate (B : SymmetricCubic) (hB : A (q referenceCubic) B = 0) :
    ∃ b : ℝ, ∀ k : Fin 3, KB B (h k) = b • KA (h k) := by
  obtain ⟨b, hhh⟩ := frame_diag_gate B hB
  let L : V →ₗ[ℝ] V →ₗ[ℝ] V := KB B - b • KA
  have hL_hh (i j : Fin 3) : L (h i) (h j) = 0 := sub_eq_zero.mpr (hhh i j)
  have hL_rot (m : Fin 3) (s : ℝ) (hs : (3 / 5) ^ 2 + s ^ 2 = 1) (a : Octonion) (ha : octNormSq a = 1) (i j : Fin 3) :
      L (automorphismV ((cycPow m).comp (rotAut s hs a ha)) (h i))
        (automorphismV ((cycPow m).comp (rotAut s hs a ha)) (h j)) = 0 := by
    let g := (cycPow m).comp (rotAut s hs a ha)
    obtain ⟨c, hc⟩ := frame_diag_gate (pullbackCubic (automorphismV g) B) (A_q_pullback_zero g B hB)
    have htr (p q : Fin 3) : KB B (automorphismV g (h p)) (automorphismV g (h q)) =
        c • KA (automorphismV g (h p)) (automorphismV g (h q)) := by
      rw [← automorphismV_KB_pullback g B, hc, map_smul, automorphismV_KA]
    have hg0 : automorphismV g (h 0) = h m := by
      change automorphismV (cycPow m) (automorphismV (rotAut s hs a ha) (h 0)) = h m
      rw [rotAut_h0, cycPow_h, add_zero]
    have hcb : c = b := smul_left_injective ℝ (KA_h_self_ne m) (by
      have h00 := htr 0 0; rw [hg0, hhh m m] at h00; exact h00.symm)
    exact sub_eq_zero.mpr (hcb ▸ htr i j)
  have hslots := h_Slot_zero (fun x y => by simp [L, KB_comm, jordan_comm]) hL_hh hL_rot
  refine ⟨b, fun k => LinearMap.ext fun x => sub_eq_zero.mp ?_⟩
  change L (h k) x = 0; rw [v_decompose x]
  simp only [map_add, map_smul, hL_hh, (hslots k _).1, (hslots k _).2.1, (hslots k _).2.2, smul_zero, add_zero]

theorem q_fiber_reference (B : SymmetricCubic) (hq : q B = q referenceCubic) :
    B = referenceCubic ∨ B = scalarCubic (-1) referenceCubic := by
  have hB : A (q referenceCubic) B = 0 := by rw [← hq]; exact A_q_self B
  obtain ⟨b, hhk⟩ := hk_gate B hB
  let L : V →ₗ[ℝ] V →ₗ[ℝ] V := KB B - b • KA
  have hL_hk (k : Fin 3) : L (h k) = 0 := sub_eq_zero.mpr (hhk k)
  have hunit (m : Fin 3) (a : Octonion) (ha : octNormSq a = 1) :
      L (automorphismV (cycPow m) (X12 a)) = 0 := by
    let g := (cycPow m).comp (rotAut (4 / 5) (by norm_num) a ha)
    obtain ⟨c, hc⟩ := hk_gate (pullbackCubic (automorphismV g) B) (A_q_pullback_zero g B hB)
    have htr (k : Fin 3) : KB B (automorphismV g (h k)) = c • KA (automorphismV g (h k)) := LinearMap.ext fun z => by
      obtain ⟨w, rfl⟩ := (automorphismV g).surjective z
      rw [← automorphismV_KB_pullback g B, LinearMap.congr_fun (hc k) w]
      simp only [LinearMap.smul_apply, map_smul, automorphismV_KA]
    have hg0 : automorphismV g (h 0) = h m := by
      change automorphismV (cycPow m) (automorphismV (rotAut (4 / 5) _ a ha) (h 0)) = h m
      rw [rotAut_h0, cycPow_h, add_zero]
    have hcb : c = b := smul_left_injective ℝ (KA_h_self_ne m) (by
      have h00 := LinearMap.congr_fun (htr 0) (h m); rw [hg0, LinearMap.congr_fun (hhk m) (h m)] at h00; exact h00.symm)
    have h1 : L (automorphismV g (h 1)) = 0 := sub_eq_zero.mpr (hcb ▸ htr 1)
    have hg1 : automorphismV g (h 1) = (9 / 25 : ℝ) • h (m + 1) + (16 / 25 : ℝ) • h (m + 2) +
        (36 / 25 : ℝ) • automorphismV (cycPow m) (X12 a) := by
      change automorphismV (cycPow m) (automorphismV (rotAut (4 / 5) _ a ha) (h 1)) = _
      rw [rotAut_h1]; simp only [map_add, map_smul, cycPow_h]; norm_num
    rw [hg1, map_add, map_add, map_smul, map_smul, map_smul, hL_hk, hL_hk, smul_zero, smul_zero, add_zero, zero_add] at h1
    simpa [smul_smul] using congrArg ((25 / 36 : ℝ) • ·) h1
  have hall (m : Fin 3) (v : Octonion) : L (automorphismV (cycPow m) (X12 v)) = 0 := by
    by_cases hv : v = 0
    · subst v; simp
    · obtain ⟨a, r, _, ha, rfl⟩ := octUnit_decomposition v hv
      rw [map_smul, map_smul, map_smul, hunit m a ha, smul_zero]
  have hKB : KB B = b • KA := LinearMap.ext fun x => sub_eq_zero.mp <| by
    change L x = 0; rw [v_decompose x]
    simp only [map_add, map_smul, hL_hk, show L (X01 _) = 0 from (cycPow_slots _).2.2 ▸ hall 2 _,
      show L (X02 _) = 0 from (cycPow_slots _).2.1 ▸ hall 1 _, show L (X12 _) = 0 from hall 0 _, smul_zero, add_zero]
  have hBs : B = scalarCubic b referenceCubic := KB_injective (by rw [KB_scalarCubic, KB_referenceCubic, hKB])
  have hq_ne : q referenceCubic ≠ 0 := fun hz => by
    have hv := congrArg (fun T : V → V → Module.End ℝ V => T (h 0) (h 1) (h 0)) hz
    simp only [q, KB_referenceCubic, operatorComm, LinearMap.sub_apply, LinearMap.comp_apply,
      KA_h_cross 1 0 (by decide), KA_h_cross 0 1 (by decide), KA_h_self, map_add, map_smul] at hv
    have hv' : h 0 + (2 : ℝ) • h 1 = 0 := by convert hv using 1; module
    have hd := congrArg (fun x : V => (x : Albert).d1) hv'
    norm_num [h, e, unit] at hd
  have hb2 : b ^ 2 = 1 := smul_left_injective ℝ hq_ne <| by
    change b ^ 2 • q referenceCubic = (1 : ℝ) • q referenceCubic; rw [← q_scalarCubic, ← hBs, hq, one_smul]
  rcases sq_eq_one_iff.mp hb2 with rfl | rfl
  · left; rw [hBs]; cases referenceCubic; simp [scalarCubic]
  · exact Or.inr hBs

end
end AlbertRecognition
