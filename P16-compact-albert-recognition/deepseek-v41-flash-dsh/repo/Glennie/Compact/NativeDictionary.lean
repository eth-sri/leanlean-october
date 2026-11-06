/- Explicit real coordinate dictionary between the 27-coordinate model and the native
compact Albert carrier of `Glennie.Native`, in the Sector gauge (hidden columns
-o12, +o02, -o01; last imaginary octonion coordinate with sign i(j l) = -k l).

Full index 0 is the unit. Full index n+1 is traceless index n, in the order
  t s a01 b01 a02 b02 a12 b12 u00 v00 u01 v01 u02 v02 u10 v10 u11 v11 u12 v12
  u20 v20 u21 v21 u22 v22,
with H = [[t+s, a01+i b01, a02+i b02], [conj, -t+s, a12+i b12], [conj, conj, -2s]]
and the ROW-major hidden matrix M[r][c] = u_rc + i v_rc.

Raw native conventions: T(1)=3, halved Jordan product,
B(x,y) = T(x o y) = 3 g, hidden metric factor 2, no factor 4 anywhere. -/
module

public import Glennie.SectorModel

@[expose] public section

namespace Glennie.Compact.NativeDictionary

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
variable (a : Fin 26 → ℝ)
include a in

/-! ## Traceless decode -/

/-- The explicit traceless decode. It equals `sectorDecode (extH a) (extM a)`
(theorem `extDecode0_eq_sectorDecode`). -/
def extDecode0  : Albert :=
  ⟨a 0 + a 1, -a 0 + a 1, -2 * a 1,
    (⟨a 2, a 3, -a 12, -a 13⟩, ⟨-a 18, -a 19, -a 24, a 25⟩),
    (⟨a 4, a 5, a 10, a 11⟩, ⟨a 16, a 17, a 22, -a 23⟩),
    (⟨a 6, a 7, -a 8, -a 9⟩, ⟨-a 14, -a 15, -a 20, a 21⟩)⟩
include a in

@[simp] theorem extDecode0_d0  : (extDecode0 a).d0 = a 0 + a 1 := rfl
include a in
@[simp] theorem extDecode0_d1  : (extDecode0 a).d1 = -a 0 + a 1 := rfl
include a in
@[simp] theorem extDecode0_d2  : (extDecode0 a).d2 = -2 * a 1 := rfl
include a in
@[simp] theorem extDecode0_o01  :
    (extDecode0 a).o01 =
      ((⟨a 2, a 3, -a 12, -a 13⟩, ⟨-a 18, -a 19, -a 24, a 25⟩) : Octonion) := rfl
include a in
@[simp] theorem extDecode0_o02  :
    (extDecode0 a).o02 =
      ((⟨a 4, a 5, a 10, a 11⟩, ⟨a 16, a 17, a 22, -a 23⟩) : Octonion) := rfl
include a in
@[simp] theorem extDecode0_o12  :
    (extDecode0 a).o12 =
      ((⟨a 6, a 7, -a 8, -a 9⟩, ⟨-a 14, -a 15, -a 20, a 21⟩) : Octonion) := rfl
variable (a : Fin 27 → ℝ)
include a in

/-! ## Full 27-coordinate decode and encode -/

/-- Drop the unit coordinate: full index `i.succ` is traceless index `i`. -/
def extTail  : Fin 26 → ℝ := fun i => a i.succ
include a in

@[simp] theorem extTail_apply  (i : Fin 26) : extTail a i = a i.succ := rfl
include a in

/-- Full decode: coordinate 0 multiplies the native unit (raw trace 3). -/
def extDecode  : Albert := a 0 • (1 : Albert) + extDecode0 (extTail a)

/-- Traceless encode, the inverse of `extDecode0` on the traceless part. -/
def extEncode0 (x : Albert) : Fin 26 → ℝ :=
  ![(x.d0 - x.d1) / 2, (x.d0 + x.d1 - 2 * x.d2) / 6,
    x.o01.1.re, x.o01.1.imI, x.o02.1.re, x.o02.1.imI, x.o12.1.re, x.o12.1.imI,
    -x.o12.1.imJ, -x.o12.1.imK, x.o02.1.imJ, x.o02.1.imK,
    -x.o01.1.imJ, -x.o01.1.imK, -x.o12.2.re, -x.o12.2.imI,
    x.o02.2.re, x.o02.2.imI, -x.o01.2.re, -x.o01.2.imI,
    -x.o12.2.imJ, x.o12.2.imK, x.o02.2.imJ, -x.o02.2.imK,
    -x.o01.2.imJ, x.o01.2.imK]

/-- Full encode: unit coordinate T(x)/3, then the traceless coordinates. -/
def extEncode (x : Albert) : Fin 27 → ℝ := Matrix.vecCons (trace x / 3) (extEncode0 x)

theorem trace_extDecode0 (a : Fin 26 → ℝ) : trace (extDecode0 a) = 0 := by
  simp only [trace, extDecode0_d0, extDecode0_d1, extDecode0_d2]
  ring

theorem trace_extDecode (a : Fin 27 → ℝ) : trace (extDecode a) = 3 * a 0 := by
  simp only [extDecode, trace_add, trace_smul, trace_unit, trace_extDecode0]
  ring

theorem extDecode0_add (a b : Fin 26 → ℝ) :
    extDecode0 (a + b) = extDecode0 a + extDecode0 b := by
  ext <;> simp <;> ring

theorem extDecode0_smul (r : ℝ) (a : Fin 26 → ℝ) :
    extDecode0 (r • a) = r • extDecode0 a := by
  ext <;> simp <;> ring

/-- The traceless decode as a real-linear map. -/
def extDecode0L : (Fin 26 → ℝ) →ₗ[ℝ] Albert where
  toFun := extDecode0
  map_add' := extDecode0_add
  map_smul' r a := by
    try rw [RingHom.id_apply]
    exact extDecode0_smul r a

@[simp] theorem extDecode0L_apply (a : Fin 26 → ℝ) : extDecode0L a = extDecode0 a := rfl

theorem extDecode_add (a b : Fin 27 → ℝ) :
    extDecode (a + b) = extDecode a + extDecode b := by
  ext <;> simp [extDecode] <;> ring

theorem extDecode_smul (r : ℝ) (a : Fin 27 → ℝ) :
    extDecode (r • a) = r • extDecode a := by
  ext <;> simp [extDecode] <;> ring

theorem extEncode0_extDecode (a : Fin 27 → ℝ) : extEncode0 (extDecode a) = extTail a := by
  funext i
  fin_cases i <;> simp [extEncode0, extDecode] <;> ring

theorem extEncode_extDecode (a : Fin 27 → ℝ) : extEncode (extDecode a) = a := by
  funext m
  induction m using Fin.cases with
  | zero =>
    simp only [extEncode, Matrix.cons_val_zero, trace_extDecode]
    ring
  | succ k =>
    simp only [extEncode, Matrix.cons_val_succ, extEncode0_extDecode, extTail_apply]

theorem extDecode_extEncode (x : Albert) : extDecode (extEncode x) = x := by
  ext <;> simp [extDecode, extEncode, extEncode0, trace] <;> ring

/-- The coordinate equivalence, decode direction. -/
def extEquiv : (Fin 27 → ℝ) ≃ₗ[ℝ] Albert where
  toFun := extDecode
  invFun := extEncode
  map_add' := extDecode_add
  map_smul' r a := by
    try rw [RingHom.id_apply]
    exact extDecode_smul r a
  left_inv := extEncode_extDecode
  right_inv := extDecode_extEncode

/-! ## Metric: native B = 3 g -/

/-! ## Gauge bridge to the SectorModel -/

end
end Glennie.Compact.NativeDictionary
