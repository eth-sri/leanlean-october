module

public import Glennie.Native.AlgebraLaws
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Prod

@[expose] public section
namespace AlbertRecognition
noncomputable section

open Glennie
open scoped BigOperators Quaternion

def traceLinear : Albert →ₗ[ℝ] ℝ where
  toFun := Glennie.trace
  map_add' := Glennie.trace_add
  map_smul' r x := by
    simpa only [RingHom.id_apply, smul_eq_mul] using Glennie.trace_smul r x

@[simp] theorem traceLinear_apply (x : Albert) : traceLinear x = Glennie.trace x := rfl

def traceFreeSpace : Submodule ℝ Albert := traceLinear.ker
abbrev V := traceFreeSpace

@[simp] theorem trace_V (x : V) : Glennie.trace (x : Albert) = 0 := x.property

def project : Albert →ₗ[ℝ] V where
  toFun x := ⟨Glennie.traceless x, Glennie.trace_traceless x⟩
  map_add' x y := by
    apply Subtype.ext
    change Glennie.traceless (x + y) = Glennie.traceless x + Glennie.traceless y
    simp only [Glennie.traceless, Glennie.trace_add, add_div, add_smul]
    module
  map_smul' r x := by
    apply Subtype.ext
    change Glennie.traceless (r • x) = r • Glennie.traceless x
    simp only [Glennie.traceless, Glennie.trace_smul, smul_sub, smul_smul, mul_div_assoc]

@[simp] theorem project_coe (x : Albert) :
    (project x : Albert) = Glennie.traceless x := rfl

@[simp] theorem project_V (x : V) : project (x : Albert) = x := by
  apply Subtype.ext
  simp only [project_coe, Glennie.traceless, trace_V, zero_div, zero_smul, sub_zero]

def gA (x y : V) : ℝ := Glennie.inner (x : Albert) (y : Albert) / 3

theorem gA_comm (x y : V) : gA x y = gA y x :=
  congrArg (fun r : ℝ => r / 3) (Glennie.inner_comm _ _)

theorem gA_add_left (x y z : V) : gA (x + y) z = gA x z + gA y z := by
  change Glennie.inner ((x : Albert) + (y : Albert)) (z : Albert) / 3 = _
  rw [Glennie.inner_add_left, add_div]; rfl

theorem gA_add_right (x y z : V) : gA x (y + z) = gA x y + gA x z := by
  change Glennie.inner (x : Albert) ((y : Albert) + (z : Albert)) / 3 = _
  rw [Glennie.inner_add_right, add_div]; rfl

theorem gA_smul_left (r : ℝ) (x y : V) : gA (r • x) y = r * gA x y := by
  change Glennie.inner (r • (x : Albert)) (y : Albert) / 3 = _
  rw [Glennie.inner_smul_left, mul_div_assoc]; rfl

theorem gA_smul_right (r : ℝ) (x y : V) : gA x (r • y) = r * gA x y := by
  change Glennie.inner (x : Albert) (r • (y : Albert)) / 3 = _
  rw [Glennie.inner_smul_right, mul_div_assoc]; rfl

theorem gA_self_eq_zero (x : V) : gA x x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hinner : Glennie.inner (x : Albert) (x : Albert) = 0 := by
      change Glennie.inner (x : Albert) (x : Albert) / 3 = 0 at hx; linarith
    exact Subtype.ext ((Glennie.inner_self_eq_zero _).mp hinner)
  · rintro rfl
    change Glennie.inner (0 : Albert) 0 / 3 = 0
    simp only [Glennie.inner, Glennie.jordan_zero_left, Glennie.trace]; norm_num

theorem project_pairing (u : Albert) (z : V) :
    gA (project u) z = Glennie.inner u (z : Albert) / 3 := by
  change Glennie.inner (Glennie.traceless u) (z : Albert) / 3 = _
  rw [Glennie.traceless, Glennie.inner_sub_left, Glennie.inner_smul_left]
  have hunit : Glennie.inner (1 : Albert) (z : Albert) = 0 := by
    simp only [Glennie.inner, Glennie.jordan_unit_left, trace_V]
  rw [hunit, mul_zero, sub_zero]

def KA : V →ₗ[ℝ] (V →ₗ[ℝ] V) where
  toFun x :=
    { toFun := fun y => project (Glennie.jordan (x : Albert) (y : Albert))
      map_add' y z := by
        change project (Glennie.jordan (x : Albert) ((y : Albert) + (z : Albert))) = _
        rw [Glennie.jordan_add_right, map_add]
      map_smul' r y := by
        change project (Glennie.jordan (x : Albert) (r • (y : Albert))) =
          r • project (Glennie.jordan (x : Albert) (y : Albert))
        rw [Glennie.jordan_smul_right, map_smul] }
  map_add' x y := LinearMap.ext fun z => by
    change project (Glennie.jordan ((x : Albert) + (y : Albert)) (z : Albert)) =
      project (Glennie.jordan (x : Albert) (z : Albert)) +
        project (Glennie.jordan (y : Albert) (z : Albert))
    rw [Glennie.jordan_add_left, map_add]
  map_smul' r x := LinearMap.ext fun y => by
    change project (Glennie.jordan (r • (x : Albert)) (y : Albert)) =
      r • project (Glennie.jordan (x : Albert) (y : Albert))
    rw [Glennie.jordan_smul_left, map_smul]

@[simp] theorem KA_apply (x y : V) :
    KA x y = project (Glennie.jordan (x : Albert) (y : Albert)) := rfl

theorem KA_comm (x y : V) : KA x y = KA y x := by
  simp only [KA_apply, Glennie.jordan_comm]

def CA (x y z : V) : ℝ := gA (KA x y) z

theorem CA_eq_native (x y z : V) :
    CA x y z = Glennie.inner (Glennie.jordan (x : Albert) (y : Albert)) (z : Albert) / 3 :=
  project_pairing _ _

theorem CA_swap12 (x y z : V) : CA x y z = CA y x z := by
  unfold CA; rw [KA_comm]

theorem CA_swap23 (x y z : V) : CA x y z = CA x z y := by
  rw [CA_eq_native, CA_eq_native,
    Glennie.inner_jordan_associative, Glennie.inner_jordan_associative,
    Glennie.jordan_comm (y : Albert) (z : Albert)]

structure SymmetricCubic where
  form : V →ₗ[ℝ] (V →ₗ[ℝ] (V →ₗ[ℝ] ℝ))
  swap12 : ∀ x y z, form x y z = form y x z
  swap23 : ∀ x y z, form x y z = form x z y

def e : Fin 3 → Albert :=
  ![⟨1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩]

@[simp] theorem trace_e (i : Fin 3) : Glennie.trace (e i) = 1 := by
  fin_cases i <;> norm_num [e, Glennie.trace]

def h (i : Fin 3) : V :=
  ⟨(1 : Albert) - (3 : ℝ) • e i, by
    change Glennie.trace ((1 : Albert) - (3 : ℝ) • e i) = 0
    rw [Glennie.trace_sub, Glennie.trace_unit, Glennie.trace_smul, trace_e]; norm_num⟩

@[simp] theorem h_coe (i : Fin 3) :
    (h i : Albert) = (1 : Albert) - (3 : ℝ) • e i := rfl

theorem h_sum_zero : h 0 + h 1 + h 2 = 0 := by
  apply Subtype.ext; apply Albert.ext <;> norm_num [h, e, Glennie.unit]

def X01 : Octonion →ₗ[ℝ] V where
  toFun a := ⟨⟨0, 0, 0, a, 0, 0⟩, by change (0 : ℝ) + 0 + 0 = 0; norm_num⟩
  map_add' _ _ := by apply Subtype.ext; apply Albert.ext <;> simp
  map_smul' _ _ := by apply Subtype.ext; apply Albert.ext <;> simp

def X02 : Octonion →ₗ[ℝ] V where
  toFun a := ⟨⟨0, 0, 0, 0, a, 0⟩, by change (0 : ℝ) + 0 + 0 = 0; norm_num⟩
  map_add' _ _ := by apply Subtype.ext; apply Albert.ext <;> simp
  map_smul' _ _ := by apply Subtype.ext; apply Albert.ext <;> simp

def X12 : Octonion →ₗ[ℝ] V where
  toFun a := ⟨⟨0, 0, 0, 0, 0, a⟩, by change (0 : ℝ) + 0 + 0 = 0; norm_num⟩
  map_add' _ _ := by apply Subtype.ext; apply Albert.ext <;> simp
  map_smul' _ _ := by apply Subtype.ext; apply Albert.ext <;> simp

def albertLinearEquiv : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert.Coordinates :=
  { Glennie.Albert.coordinateAddEquiv with map_smul' _ _ := rfl }
instance : FiniteDimensional ℝ Glennie.Albert := albertLinearEquiv.symm.finiteDimensional

def metricBilin : LinearMap.BilinForm ℝ V where
  toFun x :=
    { toFun := gA x
      map_add' y z := gA_add_right x y z
      map_smul' r y := by simpa only [RingHom.id_apply, smul_eq_mul] using gA_smul_right r x y }
  map_add' x y := LinearMap.ext fun z => gA_add_left x y z
  map_smul' r x := LinearMap.ext fun y => gA_smul_left r x y

theorem metric_nondegenerate : metricBilin.Nondegenerate :=
  ⟨fun x hx => (gA_self_eq_zero x).mp (hx x), fun x hx => (gA_self_eq_zero x).mp (hx x)⟩

def metricDual : V ≃ₗ[ℝ] Module.Dual ℝ V := metricBilin.toDual metric_nondegenerate

def KB (B : SymmetricCubic) : V →ₗ[ℝ] (V →ₗ[ℝ] V) where
  toFun x := metricDual.symm.toLinearMap.comp (B.form x)
  map_add' x y := LinearMap.ext fun z => by
    change metricDual.symm (B.form (x + y) z) =
      metricDual.symm (B.form x z) + metricDual.symm (B.form y z)
    rw [map_add, LinearMap.add_apply, map_add]
  map_smul' r x := LinearMap.ext fun y => by
    change metricDual.symm (B.form (r • x) y) = r • metricDual.symm (B.form x y)
    rw [map_smul, LinearMap.smul_apply, map_smul]

theorem KB_pairing (B : SymmetricCubic) (x y z : V) :
    gA (KB B x y) z = B.form x y z := by
  change metricBilin ((metricBilin.toDual metric_nondegenerate).symm (B.form x y)) z = _
  exact LinearMap.BilinForm.apply_toDual_symm_apply _ _

theorem KB_comm (B : SymmetricCubic) (x y : V) : KB B x y = KB B y x := by
  apply metricDual.injective; apply LinearMap.ext; intro z
  change gA (KB B x y) z = gA (KB B y x) z
  rw [KB_pairing, KB_pairing, B.swap12]

theorem KB_selfadjoint (B : SymmetricCubic) (x y z : V) :
    gA (KB B x y) z = gA y (KB B x z) := by
  rw [gA_comm y (KB B x z), KB_pairing, KB_pairing, B.swap23]

def referenceForm : V →ₗ[ℝ] (V →ₗ[ℝ] (V →ₗ[ℝ] ℝ)) where
  toFun x := LinearMap.comp metricBilin (KA x)
  map_add' x y := LinearMap.ext fun z => LinearMap.ext fun w => by
    change gA (KA (x + y) z) w = gA (KA x z) w + gA (KA y z) w
    rw [map_add, LinearMap.add_apply, gA_add_left]
  map_smul' r x := LinearMap.ext fun y => LinearMap.ext fun z => by
    change gA (KA (r • x) y) z = r * gA (KA x y) z
    rw [map_smul, LinearMap.smul_apply, gA_smul_left]

def referenceCubic : SymmetricCubic where
  form := referenceForm
  swap12 := CA_swap12
  swap23 := CA_swap23

theorem KB_referenceCubic : KB referenceCubic = KA := by
  apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
  apply metricDual.injective; apply LinearMap.ext; intro z
  exact KB_pairing referenceCubic x y z

theorem KB_injective : Function.Injective KB := by
  intro B C h
  have hform : B.form = C.form := LinearMap.ext fun x => LinearMap.ext fun y =>
    LinearMap.ext fun z => by rw [← KB_pairing B x y z, ← KB_pairing C x y z, h]
  cases B; cases C; cases hform; rfl

def operatorComm (P Q : V →ₗ[ℝ] V) : V →ₗ[ℝ] V := P.comp Q - Q.comp P

def q (B : SymmetricCubic) (x y : V) : V →ₗ[ℝ] V :=
  operatorComm (KB B x) (KB B y)

def A (T : V → V → (V →ₗ[ℝ] V)) (B : SymmetricCubic)
    (x y z : V) : V →ₗ[ℝ] V :=
  operatorComm (KB B x) (T y z) + operatorComm (KB B y) (T z x) +
    operatorComm (KB B z) (T x y)

def wedge (x y : V) : V →ₗ[ℝ] V where
  toFun z := gA y z • x - gA x z • y
  map_add' z w := by simp only [gA_add_right, add_smul]; module
  map_smul' r z := by simp only [RingHom.id_apply, gA_smul_right, mul_smul, smul_sub]

def D (x y : V) : V →ₗ[ℝ] V := wedge x y + q referenceCubic x y

namespace FixedFrame

def qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
def qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩
def qk : Quaternion ℝ := ⟨0, 0, 0, 1⟩

@[simp] theorem star_qi : star qi = -qi := by apply Quaternion.ext <;> simp [qi]
@[simp] theorem star_qj : star qj = -qj := by apply Quaternion.ext <;> simp [qj]
@[simp] theorem star_qk : star qk = -qk := by apply Quaternion.ext <;> simp [qk]
@[simp] theorem qi_mul_qj : qi * qj = qk := by apply Quaternion.ext <;> norm_num [qi, qj, qk]
@[simp] theorem qj_mul_qi : qj * qi = -qk := by apply Quaternion.ext <;> norm_num [qi, qj, qk]
@[simp] theorem qk_mul_qk : qk * qk = -1 := by apply Quaternion.ext <;> norm_num [qk]

theorem quat_neg_eq_self_zero (p : Quaternion ℝ) (hp : -p = p) : p = 0 := by
  have hr := congrArg QuaternionAlgebra.re hp
  have hi := congrArg QuaternionAlgebra.imI hp
  have hj := congrArg QuaternionAlgebra.imJ hp
  have hk := congrArg QuaternionAlgebra.imK hp
  simp only [Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg] at hr hi hj hk
  apply Quaternion.ext <;> simp <;> linarith

theorem quat_right_k_zero (p : Quaternion ℝ) (hp : p * qk = 0) : p = 0 := by
  have hr := congrArg QuaternionAlgebra.re hp
  have hi := congrArg QuaternionAlgebra.imI hp
  have hj := congrArg QuaternionAlgebra.imJ hp
  have hk := congrArg QuaternionAlgebra.imK hp
  simp [qk] at hr hi hj hk
  apply Quaternion.ext <;> simp <;> linarith

theorem quat_comm_i_j_real (p : Quaternion ℝ)
    (hi : qi * p = p * qi) (hj : qj * p = p * qj) :
    p = (p.re : Quaternion ℝ) := by
  have hiJ := congrArg QuaternionAlgebra.imJ hi
  have hiK := congrArg QuaternionAlgebra.imK hi
  have hjK := congrArg QuaternionAlgebra.imK hj
  simp [qi, qj] at hiJ hiK hjK
  apply Quaternion.ext <;> simp <;> linarith

theorem quat_anticomm_i_j_k_zero (p : Quaternion ℝ)
    (hi : qi * p = -(p * qi)) (hj : qj * p = -(p * qj))
    (hk : qk * p = -(p * qk)) : p = 0 := by
  have hiR := congrArg QuaternionAlgebra.re hi
  have hiI := congrArg QuaternionAlgebra.imI hi
  have hjR := congrArg QuaternionAlgebra.re hj
  have hkR := congrArg QuaternionAlgebra.re hk
  simp [qi, qj, qk] at hiR hiI hjR hkR
  apply Quaternion.ext <;> simp <;> linarith

def octBasis : Fin 8 → Octonion :=
  ![octScalar 1, (qi, 0), (qj, 0), (qk, 0), (0, 1), (0, qi), (0, qj), (0, qk)]

@[simp] theorem octBasis_zero : octBasis 0 = octScalar 1 := rfl

theorem octBasis_conj_imag (t : Fin 8) (ht : t ≠ 0) :
    octConj (octBasis t) = -octBasis t := by
  fin_cases t <;> simp_all [octBasis, octConj]

theorem oct_decompose (x : Octonion) :
    x = x.1.re • octBasis 0 + x.1.imI • octBasis 1 +
      x.1.imJ • octBasis 2 + x.1.imK • octBasis 3 +
      x.2.re • octBasis 4 + x.2.imI • octBasis 5 +
      x.2.imJ • octBasis 6 + x.2.imK • octBasis 7 := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octBasis, octScalar, qi, qj, qk, smul_eq_mul]

theorem oct_linear_ext (f g : Octonion →ₗ[ℝ] Octonion)
    (h : ∀ t : Fin 8, f (octBasis t) = g (octBasis t)) : f = g := by
  apply LinearMap.ext; intro x; rw [oct_decompose x]; simp only [map_add, map_smul, h]

def octRight (a : Octonion) : Module.End ℝ Octonion where
  toFun x := octMul x a
  map_add' x y := octMul_add_left x y a
  map_smul' r x := by simpa only [RingHom.id_apply] using octMul_smul_left r x a

def octLeft (a : Octonion) : Module.End ℝ Octonion where
  toFun x := octMul a x
  map_add' x y := octMul_add_right a x y
  map_smul' r x := by simpa only [RingHom.id_apply] using octMul_smul_right r a x

def octConjLinear : Module.End ℝ Octonion where
  toFun := octConj
  map_add' := octConj_add
  map_smul' r x := by simpa only [RingHom.id_apply] using octConj_smul r x

@[simp] theorem octMul_zero_left (a : Octonion) : octMul 0 a = 0 := by simp [octMul]
@[simp] theorem octMul_zero_right (a : Octonion) : octMul a 0 = 0 := by simp [octMul]
@[simp] theorem octRight_apply (a x : Octonion) : octRight a x = octMul x a := rfl
@[simp] theorem octLeft_apply (a x : Octonion) : octLeft a x = octMul a x := rfl
@[simp] theorem octConjLinear_apply (x : Octonion) : octConjLinear x = octConj x := rfl

theorem oct_left_nucleus_scalar (c : Octonion)
    (hc : ∀ x a : Octonion, octMul c (octMul x a) = octMul (octMul c x) a) :
    ∃ b : ℝ, c = octScalar b := by
  rcases c with ⟨p, q⟩
  have hqk : -(q * qk) = q * qk := by
    simpa [octMul, mul_assoc] using congrArg Prod.snd (hc (qi, 0) (qj, 0))
  have hq0 : q = 0 := quat_right_k_zero q (quat_neg_eq_self_zero (q * qk) hqk)
  have hi : qi * p = p * qi := by
    simpa [octMul, neg_mul, mul_neg] using congrArg Neg.neg (congrArg Prod.snd (hc (0, 1) (qi, 0)))
  have hj : qj * p = p * qj := by
    simpa [octMul, neg_mul, mul_neg] using congrArg Neg.neg (congrArg Prod.snd (hc (0, 1) (qj, 0)))
  exact ⟨p.re, Prod.ext (quat_comm_i_j_real p hi hj) hq0⟩

theorem oct_reverse_identity_zero (d : Octonion)
    (hd : ∀ a x : Octonion, octMul d (octMul a x) = octMul (octMul d x) a) :
    d = 0 := by
  rcases d with ⟨p, q⟩
  have hpk : -(p * qk) = p * qk := by
    simpa [octMul, mul_assoc] using (congrArg Prod.fst (hd (qi, 0) (qj, 0))).symm
  have hp0 : p = 0 := quat_right_k_zero p (quat_neg_eq_self_zero (p * qk) hpk)
  have hi : qi * q = -(q * qi) := by
    simpa [octMul, neg_mul, mul_neg] using congrArg Neg.neg (congrArg Prod.fst (hd (0, 1) (qi, 0)))
  have hj : qj * q = -(q * qj) := by
    simpa [octMul, neg_mul, mul_neg] using congrArg Neg.neg (congrArg Prod.fst (hd (0, 1) (qj, 0)))
  have hk : qk * q = -(q * qk) := by
    simpa [octMul, neg_mul, mul_neg] using congrArg Neg.neg (congrArg Prod.fst (hd (0, 1) (qk, 0)))
  exact Prod.ext hp0 (quat_anticomm_i_j_k_zero q hi hj hk)

theorem oct_right_commutant_scalar (P : Module.End ℝ Octonion)
    (hP : ∀ t : Fin 8, ∀ x : Octonion,
      P (octMul x (octBasis t)) = octMul (P x) (octBasis t)) :
    ∃ b : ℝ, P = b • LinearMap.id := by
  have hall (x a : Octonion) : P (octMul x a) = octMul (P x) a := by
    have heq : P.comp (octLeft x) = octLeft (P x) :=
      oct_linear_ext _ _ (fun t => hP t x)
    exact LinearMap.congr_fun heq a
  let c := P (octScalar 1)
  have hx (x : Octonion) : P x = octMul c x := by simpa [c] using hall (octScalar 1) x
  obtain ⟨b, hb⟩ := oct_left_nucleus_scalar c fun x a => by rw [← hx, hall, hx]
  exact ⟨b, LinearMap.ext fun x => by simpa [hb] using hx x⟩

theorem oct_imaginary_right_anticommutant_zero (Q : Module.End ℝ Octonion)
    (hQ : ∀ t : Fin 8, t ≠ 0 → ∀ x : Octonion,
      Q (octMul x (octBasis t)) = -octMul (Q x) (octBasis t)) : Q = 0 := by
  have hall (x a : Octonion) : Q (octMul x a) = octMul (Q x) (octConj a) := by
    have heq : Q.comp (octLeft x) = (octLeft (Q x)).comp octConjLinear := by
      apply oct_linear_ext; intro t
      by_cases ht : t = 0
      · subst t
        change Q (octMul x (octScalar 1)) = octMul (Q x) (octConj (octScalar 1))
        simp only [octConj_scalar, octMul_scalar_right, one_smul]
      · change Q (octMul x (octBasis t)) = octMul (Q x) (octConj (octBasis t))
        rw [octBasis_conj_imag t ht, hQ t ht x]
        exact (map_neg (octLeft (Q x)) (octBasis t)).symm
    exact LinearMap.congr_fun heq a
  let d := Q (octScalar 1)
  have hx (x : Octonion) : Q x = octMul d (octConj x) := by simpa [d] using hall (octScalar 1) x
  have hd : ∀ a x : Octonion, octMul d (octMul a x) = octMul (octMul d x) a := fun a x => by
    have h := hall (octConj x) (octConj a)
    rw [hx (octMul (octConj x) (octConj a)), hx (octConj x)] at h
    simpa only [octConj_mul, octConj_conj] using h
  have hd0 : d = 0 := oct_reverse_identity_zero d hd
  apply LinearMap.ext; intro x
  change Q x = (0 : Octonion); rw [hx x, hd0, octMul_zero_left]

abbrev Spin := Octonion × Octonion

def spinJ (a : Octonion) : Module.End ℝ Spin where
  toFun x := (-octMul x.2 (octConj a), octMul x.1 a)
  map_add' x y := Prod.ext (map_add (-octRight (octConj a)) x.2 y.2) (octMul_add_left x.1 y.1 a)
  map_smul' _ _ := by apply Prod.ext <;> simp [octMul_smul_left, smul_neg]

@[simp] theorem spinJ_apply (a : Octonion) (u v : Octonion) :
    spinJ a (u, v) = (-octMul v (octConj a), octMul u a) := rfl

@[simp] theorem spinJ_unit_apply (u v : Octonion) :
    spinJ (octScalar 1) (u, v) = (-v, u) := by simp

theorem spinJ_imag_apply (a : Octonion) (ha : octConj a = -a) (u v : Octonion) :
    spinJ a (u, v) = (octMul v a, octMul u a) := by
  apply Prod.ext
  · change -octMul v (octConj a) = octMul v a
    rw [ha]; change -(octLeft v) (-a) = (octLeft v) a; rw [map_neg, neg_neg]
  · rfl

def spinP (F : Module.End ℝ Spin) : Module.End ℝ Octonion :=
  (LinearMap.fst ℝ Octonion Octonion).comp (F.comp (LinearMap.inl ℝ Octonion Octonion))
def spinQ (F : Module.End ℝ Spin) : Module.End ℝ Octonion :=
  (LinearMap.fst ℝ Octonion Octonion).comp (F.comp (LinearMap.inr ℝ Octonion Octonion))
def spinR (F : Module.End ℝ Spin) : Module.End ℝ Octonion :=
  (LinearMap.snd ℝ Octonion Octonion).comp (F.comp (LinearMap.inl ℝ Octonion Octonion))
def spinS (F : Module.End ℝ Spin) : Module.End ℝ Octonion :=
  (LinearMap.snd ℝ Octonion Octonion).comp (F.comp (LinearMap.inr ℝ Octonion Octonion))

theorem spin_four_blocks (F : Module.End ℝ Spin) (u v : Octonion) :
    F (u, v) = (spinP F u + spinQ F v, spinR F u + spinS F v) := by
  have hsplit : (u, v) = (u, 0) + (0, v) := by simp
  rw [hsplit, map_add]; rfl

theorem spin_blocks_of_unit (F : Module.End ℝ Spin)
    (hF : F.comp (spinJ (octScalar 1)) = (spinJ (octScalar 1)).comp F)
    (u v : Octonion) :
    F (u, v) = (spinP F u + spinQ F v, -spinQ F u + spinP F v) := by
  have hR (x : Octonion) : spinR F x = -spinQ F x := by
    have h := congrArg Prod.fst (LinearMap.congr_fun hF (x, 0))
    change (F (spinJ (octScalar 1) (x, 0))).1 = (spinJ (octScalar 1) (F (x, 0))).1 at h
    have hh : spinQ F x = -spinR F x := by simpa [spinJ, spinP, spinQ, spinR, spinS] using h
    simpa using congrArg Neg.neg hh.symm
  have hS (x : Octonion) : spinS F x = spinP F x := by
    have h := congrArg Prod.snd (LinearMap.congr_fun hF (x, 0))
    change (F (spinJ (octScalar 1) (x, 0))).2 = (spinJ (octScalar 1) (F (x, 0))).2 at h
    simpa [spinJ, spinP, spinQ, spinR, spinS] using h
  rw [spin_four_blocks F u v, hR u, hS v]

theorem spin_commutant_scalar (F : Module.End ℝ Spin)
    (hF : ∀ t : Fin 8, F.comp (spinJ (octBasis t)) = (spinJ (octBasis t)).comp F) :
    ∃ b : ℝ, F = b • LinearMap.id := by
  have hf := spin_blocks_of_unit F (hF 0)
  have himag (t : Fin 8) (ht : t ≠ 0) (x : Octonion) :
      spinQ F (octMul x (octBasis t)) = -octMul (spinQ F x) (octBasis t) ∧
      spinP F (octMul x (octBasis t)) = octMul (spinP F x) (octBasis t) := by
    have h := LinearMap.congr_fun (hF t) (x, 0)
    change F (spinJ (octBasis t) (x, 0)) = spinJ (octBasis t) (F (x, 0)) at h
    rw [spinJ_imag_apply _ (octBasis_conj_imag t ht), hf, hf] at h
    simp only [octMul_zero_left, map_zero, zero_add, add_zero, neg_zero] at h
    rw [spinJ_imag_apply _ (octBasis_conj_imag t ht)] at h
    refine ⟨?_, congrArg Prod.snd h⟩
    have hh := congrArg Prod.fst h
    change spinQ F (octMul x (octBasis t)) = octRight (octBasis t) (-spinQ F x) at hh
    rwa [map_neg] at hh
  have hP (t : Fin 8) (x : Octonion) :
      spinP F (octMul x (octBasis t)) = octMul (spinP F x) (octBasis t) := by
    by_cases ht : t = 0
    · subst t; simp
    · exact (himag t ht x).2
  obtain ⟨b, hb⟩ := oct_right_commutant_scalar (spinP F) hP
  have hq : spinQ F = 0 := oct_imaginary_right_anticommutant_zero (spinQ F) fun t ht x => (himag t ht x).1
  refine ⟨b, LinearMap.ext fun ⟨u, v⟩ => ?_⟩
  rw [hf u v, hb, hq]; simp

abbrev FrameCoordinates := ℝ × ℝ × Octonion × Spin

def frameD : V := ⟨⟨0, 1, -1, 0, 0, 0⟩, by change (0 : ℝ) + 1 + (-1) = 0; norm_num⟩

def frameSpin : Spin →ₗ[ℝ] V :=
  X01.comp (LinearMap.fst ℝ Octonion Octonion) + X02.comp (LinearMap.snd ℝ Octonion Octonion)

@[simp] theorem frameSpin_apply (u v : Octonion) :
    frameSpin (u, v) = X01 u + X02 v := rfl

def frameCoordinates : V ≃ₗ[ℝ] FrameCoordinates where
  toFun x :=
    (-(x : Albert).d0 / 2, ((x : Albert).d1 - (x : Albert).d2) / 2,
      (x : Albert).o12, ((x : Albert).o01, (x : Albert).o02))
  invFun c :=
    ⟨⟨-2*c.1, c.1+c.2.1, c.1-c.2.1, c.2.2.2.1, c.2.2.2.2, c.2.2.1⟩, by
      change -2*c.1 + (c.1+c.2.1) + (c.1-c.2.1) = 0; ring⟩
  left_inv x := by
    have ht : (x : Albert).d0 + (x : Albert).d1 + (x : Albert).d2 = 0 := trace_V x
    apply Subtype.ext; apply Albert.ext
    · change -2 * (-(x : Albert).d0 / 2) = (x : Albert).d0; ring
    · change -(x : Albert).d0 / 2 + ((x : Albert).d1 - (x : Albert).d2) / 2 = (x : Albert).d1; linarith
    · change -(x : Albert).d0 / 2 - ((x : Albert).d1 - (x : Albert).d2) / 2 = (x : Albert).d2; linarith
    · rfl
    · rfl
    · rfl
  right_inv := fun ⟨a, b, z, u, v⟩ => by
    change (-(-2*a)/2, ((a+b)-(a-b))/2, z, (u,v)) = (a,b,z,(u,v))
    rw [show -(-2*a)/2 = a by ring, show ((a+b)-(a-b))/2 = b by ring]
  map_add' x y := by
    change (-((x : Albert).d0+(y : Albert).d0)/2,
      ((x : Albert).d1+(y : Albert).d1-((x : Albert).d2+(y : Albert).d2))/2,
      (x : Albert).o12+(y : Albert).o12,
      ((x : Albert).o01+(y : Albert).o01,(x : Albert).o02+(y : Albert).o02)) =
      (-(x : Albert).d0/2 + -(y : Albert).d0/2,
      ((x : Albert).d1-(x : Albert).d2)/2 + ((y : Albert).d1-(y : Albert).d2)/2,
      (x : Albert).o12+(y : Albert).o12,
      ((x : Albert).o01+(y : Albert).o01,(x : Albert).o02+(y : Albert).o02))
    rw [show -((x : Albert).d0+(y : Albert).d0)/2 = -(x : Albert).d0/2 + -(y : Albert).d0/2 by ring,
      show ((x : Albert).d1+(y : Albert).d1-((x : Albert).d2+(y : Albert).d2))/2 =
        ((x : Albert).d1-(x : Albert).d2)/2 + ((y : Albert).d1-(y : Albert).d2)/2 by ring]
  map_smul' r x := by
    change (-(r*(x : Albert).d0)/2, (r*(x : Albert).d1-r*(x : Albert).d2)/2,
      r • (x : Albert).o12,(r • (x : Albert).o01,r • (x : Albert).o02)) =
      (r*(-(x : Albert).d0/2),r*(((x : Albert).d1-(x : Albert).d2)/2),
      r • (x : Albert).o12,(r • (x : Albert).o01,r • (x : Albert).o02))
    rw [show -(r*(x : Albert).d0)/2 = r*(-(x : Albert).d0/2) by ring,
      show (r*(x : Albert).d1-r*(x : Albert).d2)/2 = r*(((x : Albert).d1-(x : Albert).d2)/2) by ring]

def frameEmbed : FrameCoordinates →ₗ[ℝ] V := frameCoordinates.symm.toLinearMap

theorem frameEmbed_eq (a b : ℝ) (z : Octonion) (s : Spin) :
    frameEmbed (a,b,z,s) = a • h 0 + b • frameD + X12 z + frameSpin s := by
  rcases s with ⟨u,v⟩; apply Subtype.ext; apply Albert.ext <;>
    simp [frameEmbed, frameCoordinates, h, e, frameD, frameSpin, X01, X02, X12] <;> ring

theorem frame_decompose (x : V) :
    x = (frameCoordinates x).1 • h 0 + (frameCoordinates x).2.1 • frameD +
      X12 (frameCoordinates x).2.2.1 + frameSpin (frameCoordinates x).2.2.2 :=
  (frameCoordinates.symm_apply_apply x).symm.trans
    (frameEmbed_eq (frameCoordinates x).1 (frameCoordinates x).2.1
      (frameCoordinates x).2.2.1 (frameCoordinates x).2.2.2)

private theorem octDot_zero_left (a : Octonion) : octDot 0 a = 0 := by simp [octDot_coordinates]
private theorem octDot_zero_right (a : Octonion) : octDot a 0 = 0 := by simp [octDot_coordinates]
@[simp] private theorem octConj_zero_native : octConj (0 : Octonion) = 0 := by simp [octConj]
private theorem octDot_smul_right (r : ℝ) (a b : Octonion) :
    octDot a (r • b) = r * octDot a b := by
  rw [octDot_comm, octDot_smul_left, octDot_comm b a]

theorem trace_full_commutator (x y z : V) :
    Glennie.trace (jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
      jordan (y : Albert) (jordan (x : Albert) (z : Albert))) = 0 := by
  rw [trace_sub]
  change inner (x : Albert) (jordan (y : Albert) (z : Albert)) -
    inner (y : Albert) (jordan (x : Albert) (z : Albert)) = 0
  rw [← inner_jordan_associative, ← inner_jordan_associative,
    jordan_comm (y : Albert) (x : Albert), sub_self]

theorem KA_projected_composition (x y z : V) :
    KA x (KA y z) =
      project (jordan (x : Albert) (jordan (y : Albert) (z : Albert))) - gA y z • x := by
  change project (jordan (x : Albert) (traceless (jordan (y : Albert) (z : Albert)))) = _
  rw [traceless, jordan_sub_right, jordan_smul_right, jordan_unit_right, map_sub, map_smul, project_V]
  rfl

theorem D_apply_project_native (x y z : V) :
    D x y z = project
      (jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
        jordan (y : Albert) (jordan (x : Albert) (z : Albert))) := by
  unfold D q operatorComm
  rw [KB_referenceCubic]
  change gA y z • x - gA x z • y + (KA x (KA y z) - KA y (KA x z)) = _
  rw [map_sub, KA_projected_composition, KA_projected_composition]; module

theorem D_apply_native (x y z : V) :
    (D x y z : Albert) =
      jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
        jordan (y : Albert) (jordan (x : Albert) (z : Albert)) := by
  rw [D_apply_project_native]
  change traceless _ = _
  rw [traceless, trace_full_commutator]; simp

@[simp] private theorem albert_neg_d0 (x : Albert) : (-x).d0 = -x.d0 := rfl
@[simp] private theorem albert_neg_d1 (x : Albert) : (-x).d1 = -x.d1 := rfl
@[simp] private theorem albert_neg_d2 (x : Albert) : (-x).d2 = -x.d2 := rfl
@[simp] private theorem albert_neg_o01 (x : Albert) : (-x).o01 = -x.o01 := rfl
@[simp] private theorem albert_neg_o02 (x : Albert) : (-x).o02 = -x.o02 := rfl
@[simp] private theorem albert_neg_o12 (x : Albert) : (-x).o12 = -x.o12 := rfl

private def nativeDiagonal (r s t : ℝ) : Albert := ⟨r,s,t,0,0,0⟩

private theorem jordan_diagonal (r s t : ℝ) (x : Albert) :
    jordan (nativeDiagonal r s t) x =
      ⟨r*x.d0,s*x.d1,t*x.d2,((r+s)/2) • x.o01,
        ((r+t)/2) • x.o02,((s+t)/2) • x.o12⟩ := by
  apply Albert.ext
  all_goals simp [nativeDiagonal, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_zero_left, octMul_zero_left,
    octMul_zero_right, octConj_zero_native, smul_smul, div_eq_mul_inv]
  all_goals try ring

private theorem jordan_slot12 (a : Octonion) (x : Albert) :
    jordan (X12 a : Albert) x =
      ⟨0,octDot a x.o12,octDot a x.o12,
        (1/2 : ℝ) • octMul x.o02 (octConj a),
        (1/2 : ℝ) • octMul x.o01 a,((x.d1+x.d2)/2) • a⟩ := by
  apply Albert.ext
  all_goals simp [X12, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_zero_left, octMul_zero_left,
    octMul_zero_right, octConj_zero_native, smul_smul, div_eq_mul_inv]
  all_goals try ring

private theorem h1_nativeDiagonal : (h 1 : Albert) = nativeDiagonal 1 (-2) 1 := by
  apply Albert.ext <;> norm_num [h, e, unit, nativeDiagonal]

private theorem full_commutator_h1_slot12 (a : Octonion) (x : Albert) :
    jordan (nativeDiagonal 1 (-2) 1) (jordan (X12 a : Albert) x) -
      jordan (X12 a : Albert) (jordan (nativeDiagonal 1 (-2) 1) x) =
      ⟨0,-(3/2 : ℝ)*octDot a x.o12,(3/2 : ℝ)*octDot a x.o12,
        -(3/4 : ℝ) • octMul x.o02 (octConj a),
        (3/4 : ℝ) • octMul x.o01 a,
        ((3/4 : ℝ)*(x.d1-x.d2)) • a⟩ := by
  apply Albert.ext
  all_goals simp [jordan_diagonal, jordan_slot12, octDot_smul_right, octMul_smul_left, smul_smul]
  all_goals try simp only [← sub_smul, ← neg_smul]
  all_goals congr 1 <;> ring

def frameAction (a : Octonion) : V →ₗ[ℝ] V := D (h 1) (X12 a)

theorem frameAction_coordinates (a : Octonion) (x : V) :
    (frameAction a x : Albert) =
      ⟨0,-(3/2 : ℝ)*octDot a (x : Albert).o12,
        (3/2 : ℝ)*octDot a (x : Albert).o12,
        -(3/4 : ℝ) • octMul (x : Albert).o02 (octConj a),
        (3/4 : ℝ) • octMul (x : Albert).o01 a,
        ((3/4 : ℝ)*((x : Albert).d1-(x : Albert).d2)) • a⟩ := by
  rw [frameAction, D_apply_native, h1_nativeDiagonal]
  exact full_commutator_h1_slot12 a (x : Albert)

theorem frameAction_h0 (a : Octonion) : frameAction a (h 0) = 0 := by
  apply Subtype.ext; rw [frameAction_coordinates]
  apply Albert.ext <;> simp [h, e, octDot_zero_right, octMul_zero_left]

theorem frameAction_d (a : Octonion) :
    frameAction a frameD = (3/2 : ℝ) • X12 a := by
  apply Subtype.ext; rw [frameAction_coordinates]
  apply Albert.ext <;> (simp [frameD, X12, octDot_zero_right, octMul_zero_left]; try ring)

theorem frameAction_X12 (a z : Octonion) :
    frameAction a (X12 z) = (-(3/2 : ℝ)*octDot a z) • frameD := by
  apply Subtype.ext; rw [frameAction_coordinates]
  apply Albert.ext <;> simp [X12, frameD, octMul_zero_left]

theorem frameAction_X01 (a u : Octonion) :
    frameAction a (X01 u) = (3/4 : ℝ) • X02 (octMul u a) := by
  apply Subtype.ext; rw [frameAction_coordinates]
  apply Albert.ext <;> simp [X01, X02, octDot_zero_right, octMul_zero_left]

theorem frameAction_X02 (a v : Octonion) :
    frameAction a (X02 v) = -(3/4 : ℝ) • X01 (octMul v (octConj a)) := by
  apply Subtype.ext; rw [frameAction_coordinates]
  apply Albert.ext <;> simp [X01, X02, octDot_zero_right, octMul_zero_left]

theorem frameAction_spin (a : Octonion) (s : Spin) :
    frameAction a (frameSpin s) = (3/4 : ℝ) • frameSpin (spinJ a s) := by
  rcases s with ⟨u,v⟩
  rw [frameSpin_apply, map_add, frameAction_X01, frameAction_X02, spinJ_apply, frameSpin_apply]
  simp only [map_neg]; module

end FixedFrame
end
end AlbertRecognition
