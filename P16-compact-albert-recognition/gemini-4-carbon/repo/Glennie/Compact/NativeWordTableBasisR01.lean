module
public import Glennie.Hilbert
public import Glennie.Theorems.Frames
public import Glennie.BasicLaws
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.ToReal
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
open Module Glennie
open scoped BigOperators Matrix Quaternion
set_option autoImplicit false

def powModAux (p : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | k + 1, b, e, acc =>
    if e == 0 then acc
    else powModAux p k ((b * b) % p) (e / 2) (if e % 2 == 1 then (acc * b) % p else acc)

def invModNat (p x : ℕ) : ℕ := powModAux p 20 (x % p) (p - 2) 1

def pickPivot (col : ℕ) : List (List ℕ) → List ℕ × List (List ℕ)
  | [] => ([], [])
  | r :: rs =>
    if r.getD col 0 != 0 then (r, rs)
    else let (p, rest) := pickPivot col rs; (p, r :: rest)

def gjStep (p col : ℕ) (rows : List (List ℕ)) : List (List ℕ) :=
  let top := rows.take col
  let (piv0, bot) := pickPivot col (rows.drop col)
  let inv := invModNat p (piv0.getD col 0)
  let piv := piv0.map fun x => (x * inv) % p
  let elim (r : List ℕ) : List ℕ :=
    let f := r.getD col 0
    if f == 0 then r else List.zipWith (fun a b => (a + p - (f * b) % p) % p) r piv
  top.map elim ++ [piv] ++ bot.map elim

def intModNat (p : ℕ) (x : ℤ) : ℕ := (x % (p : ℤ)).toNat

def toIntModRows (p n : ℕ) (A : Fin n → Fin n → ℤ) : List (List ℕ) :=
  (List.finRange n).map fun i => (List.finRange n).map fun j => intModNat p (A i j)

def checkMatInvInt (p n : ℕ) (A : Fin n → Fin n → ℤ) : Bool :=
  let natRows := toIntModRows p n A
  let init := (List.range n).map fun i =>
    (natRows.getD i []) ++ ((List.range n).map fun j => if i == j then 1 else 0)
  let invRows := ((List.range n).foldl (fun rs col => gjStep p col rs) init).map (·.drop n)
  (List.finRange n).all fun i =>
    let ri := invRows.getD i.1 []
    (List.finRange n).all fun j =>
      (((List.finRange n).map fun k => ri.getD k.1 0 * (natRows.getD k.1 []).getD j.1 0).sum % p) ==
        if i.1 == j.1 then 1 else 0

theorem det_ne_zero_of_checkMatInvInt {p n : ℕ} [Fact (1 < p)] {R : Type*} [CommRing R]
    (φ : R →+* ZMod p) (M : Matrix (Fin n) (Fin n) R) (MZ : Fin n → Fin n → ℤ)
    (hMZ : ∀ i j, φ (M i j) = (MZ i j : ZMod p))
    (h : checkMatInvInt p n MZ = true) :
    M.det ≠ 0 := by
  have hp1 : 1 < p := Fact.out
  let natRows := toIntModRows p n MZ
  let init := (List.range n).map fun i =>
    (natRows.getD i []) ++ ((List.range n).map fun j => if i == j then 1 else 0)
  let invRows := ((List.range n).foldl (fun rs col => gjStep p col rs) init).map (·.drop n)
  let inv : Matrix (Fin n) (Fin n) (ZMod p) :=
    Matrix.of fun i k => ((invRows.getD i.1 []).getD k.1 0 : ZMod p)
  have hmul : inv * M.map φ = 1 := by
    ext i j; rw [Matrix.mul_apply, Matrix.one_apply]
    have h2 := beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j (List.mem_finRange j))
    have hcast : (((((List.finRange n).map fun k =>
        (invRows.getD i.1 []).getD k.1 0 * (natRows.getD k.1 []).getD j.1 0).sum % p : ℕ) : ZMod p)) =
        ((if i.1 == j.1 then 1 else 0 : ℕ) : ZMod p) := congrArg Nat.cast h2
    rw [ZMod.natCast_mod, Nat.cast_list_sum, List.map_map, ← Fin.sum_univ_def] at hcast
    have hsum : ∑ k : Fin n, (Nat.cast (R := ZMod p) ∘ fun k : Fin n =>
        (invRows.getD i.1 []).getD k.1 0 * (natRows.getD k.1 []).getD j.1 0) k =
        ∑ k : Fin n, inv i k * (M.map φ) k j :=
      Finset.sum_congr rfl fun k _ => by
        have hcm : ((intModNat p (MZ k j) : ℕ) : ZMod p) = (MZ k j : ZMod p) := by
          rw [← Int.cast_natCast, show ((intModNat p (MZ k j) : ℕ) : ℤ) = MZ k j % (p : ℤ) from
            Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), ZMod.intCast_mod]
        have hgd : ((natRows.getD k.1 []).getD j.1 0) = intModNat p (MZ k j) := by
          simp [natRows, toIntModRows, List.getD_eq_getElem?_getD, k.2, j.2]
        simp only [Function.comp_apply, Nat.cast_mul, inv, Matrix.of_apply, Matrix.map_apply, hgd, hcm, hMZ]
    rw [hsum] at hcast
    refine hcast.trans ?_
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, beq_false_of_ne (Fin.val_ne_of_ne hij)]
  intro h0
  have hd : (inv * M.map φ).det = (1 : ZMod p) := by rw [hmul, Matrix.det_one]
  rw [Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero] at hd
  exact zero_ne_one hd

abbrev OctG (R : Type*) [CommRing R] := ℍ[R] × ℍ[R]

@[ext] structure AlbertG (R : Type*) [CommRing R] where
  d0 : R
  d1 : R
  d2 : R
  o01 : OctG R
  o02 : OctG R
  o12 : OctG R

section RingOps
variable {R S : Type*} [CommRing R] [CommRing S]

def qZero : ℍ[R] := ⟨0, 0, 0, 0⟩
def qOne : ℍ[R] := ⟨1, 0, 0, 0⟩
def qAdd (a b : ℍ[R]) : ℍ[R] := ⟨a.re + b.re, a.imI + b.imI, a.imJ + b.imJ, a.imK + b.imK⟩
def qSub (a b : ℍ[R]) : ℍ[R] := ⟨a.re - b.re, a.imI - b.imI, a.imJ - b.imJ, a.imK - b.imK⟩
def qNeg (a : ℍ[R]) : ℍ[R] := ⟨-a.re, -a.imI, -a.imJ, -a.imK⟩
def qSmul (r : R) (a : ℍ[R]) : ℍ[R] := ⟨r * a.re, r * a.imI, r * a.imJ, r * a.imK⟩
def qConj (a : ℍ[R]) : ℍ[R] := ⟨a.re, -a.imI, -a.imJ, -a.imK⟩
def qMul (a b : ℍ[R]) : ℍ[R] :=
  ⟨a.re * b.re - a.imI * b.imI - a.imJ * b.imJ - a.imK * b.imK,
   a.re * b.imI + a.imI * b.re + a.imJ * b.imK - a.imK * b.imJ,
   a.re * b.imJ - a.imI * b.imK + a.imJ * b.re + a.imK * b.imI,
   a.re * b.imK + a.imI * b.imJ - a.imJ * b.imI + a.imK * b.re⟩

def oZero : OctG R := (qZero, qZero)
def oAdd (x y : OctG R) : OctG R := (qAdd x.1 y.1, qAdd x.2 y.2)
def oSub (x y : OctG R) : OctG R := (qSub x.1 y.1, qSub x.2 y.2)
def oSmul (r : R) (x : OctG R) : OctG R := (qSmul r x.1, qSmul r x.2)
def oConj (x : OctG R) : OctG R := (qConj x.1, qNeg x.2)
def oMul (x y : OctG R) : OctG R := (qSub (qMul x.1 y.1) (qMul (qConj y.2) x.2), qAdd (qMul y.2 x.1) (qMul x.2 (qConj y.1)))
def oDot (x y : OctG R) : R :=
  x.1.re * y.1.re + x.1.imI * y.1.imI + x.1.imJ * y.1.imJ + x.1.imK * y.1.imK +
  x.2.re * y.2.re + x.2.imI * y.2.imI + x.2.imJ * y.2.imJ + x.2.imK * y.2.imK

def zeroG : AlbertG R := ⟨0, 0, 0, oZero, oZero, oZero⟩
def unitG : AlbertG R := ⟨1, 1, 1, oZero, oZero, oZero⟩
def addG (x y : AlbertG R) : AlbertG R := ⟨x.d0 + y.d0, x.d1 + y.d1, x.d2 + y.d2, oAdd x.o01 y.o01, oAdd x.o02 y.o02, oAdd x.o12 y.o12⟩
def subG (x y : AlbertG R) : AlbertG R := ⟨x.d0 - y.d0, x.d1 - y.d1, x.d2 - y.d2, oSub x.o01 y.o01, oSub x.o02 y.o02, oSub x.o12 y.o12⟩
def smulG (r : R) (x : AlbertG R) : AlbertG R := ⟨r * x.d0, r * x.d1, r * x.d2, oSmul r x.o01, oSmul r x.o02, oSmul r x.o12⟩
def innerG (x y : AlbertG R) : R :=
  x.d0 * y.d0 + x.d1 * y.d1 + x.d2 * y.d2 + 2 * (oDot x.o01 y.o01 + oDot x.o02 y.o02 + oDot x.o12 y.o12)

def jordan2G (x y : AlbertG R) : AlbertG R :=
  ⟨2 * (x.d0 * y.d0 + oDot x.o01 y.o01 + oDot x.o02 y.o02),
   2 * (x.d1 * y.d1 + oDot x.o01 y.o01 + oDot x.o12 y.o12),
   2 * (x.d2 * y.d2 + oDot x.o02 y.o02 + oDot x.o12 y.o12),
   oAdd (oAdd (oSmul (x.d0 + x.d1) y.o01) (oSmul (y.d0 + y.d1) x.o01)) (oAdd (oMul x.o02 (oConj y.o12)) (oMul y.o02 (oConj x.o12))),
   oAdd (oAdd (oSmul (x.d0 + x.d2) y.o02) (oSmul (y.d0 + y.d2) x.o02)) (oAdd (oMul x.o01 y.o12) (oMul y.o01 x.o12)),
   oAdd (oAdd (oSmul (x.d1 + x.d2) y.o12) (oSmul (y.d1 + y.d2) x.o12)) (oAdd (oMul (oConj x.o01) y.o02) (oMul (oConj y.o01) x.o02))⟩

def mapQG (f : R →+* S) (q : ℍ[R]) : ℍ[S] := ⟨f q.re, f q.imI, f q.imJ, f q.imK⟩
def mapOG (f : R →+* S) (x : OctG R) : OctG S := (mapQG f x.1, mapQG f x.2)
def mapAG (f : R →+* S) (x : AlbertG R) : AlbertG S :=
  ⟨f x.d0, f x.d1, f x.d2, mapOG f x.o01, mapOG f x.o02, mapOG f x.o12⟩

private theorem mapOG_add (f : R →+* S) (x y : OctG R) : mapOG f (oAdd x y) = oAdd (mapOG f x) (mapOG f y) := by ext <;> simp [mapOG, mapQG, oAdd, qAdd]
private theorem mapOG_sub (f : R →+* S) (x y : OctG R) : mapOG f (oSub x y) = oSub (mapOG f x) (mapOG f y) := by ext <;> simp [mapOG, mapQG, oSub, qSub]
private theorem mapOG_smul (f : R →+* S) (r : R) (x : OctG R) : mapOG f (oSmul r x) = oSmul (f r) (mapOG f x) := by ext <;> simp [mapOG, mapQG, oSmul, qSmul]
private theorem mapOG_conj (f : R →+* S) (x : OctG R) : mapOG f (oConj x) = oConj (mapOG f x) := by ext <;> simp [mapOG, mapQG, oConj, qConj, qNeg]
private theorem mapOG_mul (f : R →+* S) (x y : OctG R) : mapOG f (oMul x y) = oMul (mapOG f x) (mapOG f y) := by
  ext <;> simp [mapOG, mapQG, oMul, qSub, qAdd, qMul, qConj]
private theorem map_oDot (f : R →+* S) (x y : OctG R) : f (oDot x y) = oDot (mapOG f x) (mapOG f y) := by
  simp [oDot, mapOG, mapQG]

theorem mapAG_unit (f : R →+* S) : mapAG f unitG = unitG := by ext <;> simp [mapAG, mapOG, mapQG, unitG, oZero, qZero]
theorem mapAG_add (f : R →+* S) (x y : AlbertG R) : mapAG f (addG x y) = addG (mapAG f x) (mapAG f y) := by ext <;> simp [mapAG, addG, mapOG_add]
theorem mapAG_sub (f : R →+* S) (x y : AlbertG R) : mapAG f (subG x y) = subG (mapAG f x) (mapAG f y) := by ext <;> simp [mapAG, subG, mapOG_sub]
theorem mapAG_smul (f : R →+* S) (r : R) (x : AlbertG R) : mapAG f (smulG r x) = smulG (f r) (mapAG f x) := by ext <;> simp [mapAG, smulG, mapOG_smul]
theorem mapAG_inner (f : R →+* S) (x y : AlbertG R) : f (innerG x y) = innerG (mapAG f x) (mapAG f y) := by simp [innerG, mapAG, map_oDot, map_ofNat]
theorem mapAG_jordan2 (f : R →+* S) (x y : AlbertG R) : mapAG f (jordan2G x y) = jordan2G (mapAG f x) (mapAG f y) := by
  ext <;> simp [mapAG, jordan2G, map_oDot, mapOG_add, mapOG_smul, mapOG_mul, mapOG_conj, map_ofNat]

def witnessXG : AlbertG R := ⟨-1, 0, 1, oZero, oZero, oZero⟩
def witnessYG : AlbertG R := ⟨0, 0, 0, (qOne, qZero), (⟨0, 1, 0, 0⟩, qZero), (qOne, qZero)⟩
def witnessZG : AlbertG R := ⟨0, 0, 0, (qZero, ⟨0, 0, 1, 0⟩), (qZero, ⟨-1, 0, 0, 0⟩), (⟨0, 0, 0, -1⟩, qZero)⟩

end RingOps

noncomputable section

def toRealAlbert (x : AlbertG ℝ) : Albert := ⟨x.d0, x.d1, x.d2, x.o01, x.o02, x.o12⟩

theorem toRealAlbert_unit : toRealAlbert unitG = 1 := rfl
theorem toRealAlbert_add (x y : AlbertG ℝ) : toRealAlbert (addG x y) = toRealAlbert x + toRealAlbert y := by apply Albert.ext <;> rfl
theorem toRealAlbert_sub (x y : AlbertG ℝ) : toRealAlbert (subG x y) = toRealAlbert x - toRealAlbert y := by apply Albert.ext <;> rfl
theorem toRealAlbert_smul (r : ℝ) (x : AlbertG ℝ) : toRealAlbert (smulG r x) = r • toRealAlbert x := by
  ext <;> simp [toRealAlbert, smulG, oSmul, qSmul, smul_eq_mul]
theorem toRealAlbert_inner (x y : AlbertG ℝ) : innerG x y = Glennie.inner (toRealAlbert x) (toRealAlbert y) := by
  simp [innerG, oDot, toRealAlbert, Glennie.inner_coordinates, octDot_coordinates]

theorem toRealAlbert_jordan2 (x y : AlbertG ℝ) :
    toRealAlbert (jordan2G x y) = (2 : ℝ) • jordan (toRealAlbert x) (toRealAlbert y) := by
  have ha (u v : Octonion) : oAdd u v = u + v := rfl
  have hs (r : ℝ) (u : Octonion) : oSmul r u = r • u := by ext <;> simp [oSmul, qSmul, smul_eq_mul]
  have hm (u v : Octonion) : oMul u v = octMul u v := by
    ext <;> simp [oMul, octMul, qSub, qAdd, qMul, qConj] <;> ring
  have hc (u : Octonion) : oConj u = octConj u := by ext <;> simp [oConj, octConj, qConj, qNeg]
  have hd (u v : Octonion) : oDot u v = octDot u v := by simp [oDot, octDot_coordinates]
  refine Albert.ext (by simp [toRealAlbert, jordan2G, jordan_d0, hd]) (by simp [toRealAlbert, jordan2G, jordan_d1, hd])
    (by simp [toRealAlbert, jordan2G, jordan_d2, hd]) ?_ ?_ ?_
  · simp only [toRealAlbert, jordan2G, Albert.smul_o01, jordan_o01, ha, hs, hm, hc]; module
  · simp only [toRealAlbert, jordan2G, Albert.smul_o02, jordan_o02, ha, hs, hm, hc]; module
  · simp only [toRealAlbert, jordan2G, Albert.smul_o12, jordan_o12, ha, hs, hm, hc]; module

end

inductive Word where
  | unit : Word
  | mark : Fin 3 → Word
  | mul : Word → Word → Word

def eval {E : Type*} (e : E) (a : Fin 3 → E) (j : E → E → E) : Word → E
  | .unit => e
  | .mark i => a i
  | .mul u v => j (eval e a j u) (eval e a j v)

def words : Fin 27 → Word :=
  let x : Word := .mark 0; let y : Word := .mark 1; let z : Word := .mark 2
  let xx := Word.mul x x; let xy := Word.mul x y; let xz := Word.mul x z
  let yy := Word.mul y y; let yz := Word.mul y z; let zz := Word.mul z z
  ![.unit, x, y, z, xx, xy, xz, yy, yz, zz,
    .mul x xy, .mul x xz, .mul x yy, .mul x yz, .mul x zz,
    .mul y xz, .mul y yz, .mul y zz,
    .mul xx yy, .mul xx yz, .mul xx zz, .mul xy yz, .mul xy zz, .mul yy zz,
    .mul x (.mul y xz), .mul x (.mul y yz), .mul x (.mul y zz)]

private def wordDepth : Word → ℕ
  | .unit => 0 | .mark _ => 0 | .mul u v => wordDepth u + wordDepth v + 1

private def marksG {R : Type*} [CommRing R] (i : Fin 3) : AlbertG R :=
  if i.1 = 0 then witnessXG else if i.1 = 1 then witnessYG else witnessZG

private def evalWG {R : Type*} [CommRing R] : Word → AlbertG R := eval unitG marksG jordan2G

private theorem mapAG_evalWG {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (w : Word) :
    mapAG f (evalWG w) = evalWG w := by
  induction w with
  | unit => exact mapAG_unit f
  | mark i => fin_cases i <;> (ext <;> simp [evalWG, eval, marksG, mapAG, mapOG, mapQG, witnessXG, witnessYG, witnessZG, oZero, qZero, qOne])
  | mul u v ihu ihv => simp only [evalWG, eval] at ihu ihv ⊢; rw [mapAG_jordan2, ihu, ihv]

private def toVecG {R : Type*} [CommRing R] (x : AlbertG R) (j : Fin 27) : R :=
  match j.1 with
  | 0 => x.d0 | 1 => x.d1 | 2 => x.d2
  | 3 => x.o01.1.re | 4 => x.o01.1.imI | 5 => x.o01.1.imJ | 6 => x.o01.1.imK
  | 7 => x.o01.2.re | 8 => x.o01.2.imI | 9 => x.o01.2.imJ | 10 => x.o01.2.imK
  | 11 => x.o02.1.re | 12 => x.o02.1.imI | 13 => x.o02.1.imJ | 14 => x.o02.1.imK
  | 15 => x.o02.2.re | 16 => x.o02.2.imI | 17 => x.o02.2.imJ | 18 => x.o02.2.imK
  | 19 => x.o12.1.re | 20 => x.o12.1.imI | 21 => x.o12.1.imJ | 22 => x.o12.1.imK
  | 23 => x.o12.2.re | 24 => x.o12.2.imI | 25 => x.o12.2.imJ | _ => x.o12.2.imK

private instance : Fact (1 < 5) := ⟨by decide⟩

private def wordMatZ : Matrix (Fin 27) (Fin 27) ℤ := Matrix.of fun j i => toVecG (evalWG (R := ℤ) (words i)) j
private def wordColsFast : List (AlbertG ℤ) := (List.finRange 27).map fun i => evalWG (R := ℤ) (words i)
private def wordMatFast (j i : Fin 27) : ℤ := toVecG (wordColsFast.getD i.1 zeroG) j

set_option maxHeartbeats 2000000 in
private theorem det_wordMatZ_ne_zero : wordMatZ.det ≠ 0 := by
  refine det_ne_zero_of_checkMatInvInt (Int.castRingHom (ZMod 5)) wordMatZ wordMatFast (fun j i => ?_) (by decide +kernel)
  simp [wordMatZ, wordMatFast, wordColsFast, List.getD_eq_getElem?_getD, i.2]

noncomputable section

def marks : Fin 3 → Albert := ![witnessX, witnessY, witnessZ]
def nativeEval : Word → Albert := eval 1 marks jordan
def nativeWords (i : Fin 27) : Albert := nativeEval (words i)

private def toVecReal : Albert →ₗ[ℝ] (Fin 27 → ℝ) where
  toFun x j := toVecG ⟨x.d0, x.d1, x.d2, x.o01, x.o02, x.o12⟩ j
  map_add' _ _ := by funext j; fin_cases j <;> rfl
  map_smul' _ _ := by funext j; fin_cases j <;> rfl

private theorem evalWG_real_eq (w : Word) :
    toRealAlbert (evalWG (R := ℝ) w) = ((2 : ℝ) ^ wordDepth w) • nativeEval w := by
  induction w with
  | unit => simp [evalWG, nativeEval, eval, wordDepth, toRealAlbert_unit]
  | mark i =>
    fin_cases i <;> (ext <;> simp [evalWG, nativeEval, eval, wordDepth, marksG, marks,
      toRealAlbert, witnessXG, witnessYG, witnessZG, witnessX, witnessY, witnessZ,
      oZero, qZero, qOne, octScalar, octI, octJL, octL, octK, quatI, quatJ, quatK])
  | mul u v ihu ihv =>
    simp only [evalWG, nativeEval, eval, wordDepth] at ihu ihv ⊢
    rw [toRealAlbert_jordan2, ihu, ihv, jordan_smul_left, jordan_smul_right, smul_smul, smul_smul]; congr 1; ring

theorem nativeWords_linearIndependent : LinearIndependent ℝ nativeWords := by
  rw [Fintype.linearIndependent_iff]; intro g hg i
  let c : Fin 27 → ℝ := fun k => g k / ((2 : ℝ) ^ wordDepth (words k))
  have hc_vec : (wordMatZ.map (Int.castRingHom ℝ)).mulVec c = 0 := by
    funext j; change ∑ k : Fin 27, ((wordMatZ j k : ℤ) : ℝ) * c k = 0
    have hj (k : Fin 27) : ((wordMatZ j k : ℤ) : ℝ) = ((2 : ℝ) ^ wordDepth (words k)) * toVecReal (nativeWords k) j := by
      have hm : (Int.castRingHom ℝ) (toVecG (evalWG (R := ℤ) (words k)) j) = toVecG (mapAG (Int.castRingHom ℝ) (evalWG (words k))) j := by
        fin_cases j <;> rfl
      rw [mapAG_evalWG] at hm
      have hr : toVecG (evalWG (R := ℝ) (words k)) j = toVecReal (toRealAlbert (evalWG (words k))) j := rfl
      rw [hr, evalWG_real_eq] at hm
      simpa [wordMatZ, nativeWords, LinearMap.map_smul] using hm
    have hsum : (∑ k : Fin 27, ((wordMatZ j k : ℤ) : ℝ) * c k) = toVecReal (∑ k : Fin 27, g k • nativeWords k) j := by
      rw [map_sum, Finset.sum_apply]; refine Finset.sum_congr rfl fun k _ => ?_
      have hp : (2 : ℝ) ^ wordDepth (words k) ≠ 0 := pow_ne_zero _ (by norm_num)
      simp only [hj, c, LinearMap.map_smul, Pi.smul_apply, smul_eq_mul]; field_simp
    rw [hsum, hg, map_zero, Pi.zero_apply]
  have hdet : (wordMatZ.map (Int.castRingHom ℝ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact Int.cast_ne_zero.mpr det_wordMatZ_ne_zero
  exact (div_eq_zero_iff.mp (congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hc_vec) i)).resolve_right (pow_ne_zero _ (by norm_num))

def wordBasis : Basis (Fin 27) ℝ Albert :=
  Basis.mk nativeWords_linearIndependent (nativeWords_linearIndependent.span_eq_top_of_card_eq_finrank (by simp [albert_finrank])).ge

theorem wordBasis_eq_nativeWords (i : Fin 27) : wordBasis i = nativeWords i := Basis.mk_apply _ _ i

end
end Glennie.Compact.NativeWordTableR01

namespace Glennie.Compact.FlatBase
open Glennie Glennie.Compact.NativeWordTableR01
open scoped Quaternion
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [-instance] FloorSemiring.instCharZero RCLike.charZero_rclike

abbrev Z3 := Zsqrtd 3

def flatXNG {R : Type*} [CommRing R] : AlbertG R := ⟨1, 0, -1, oZero, oZero, oZero⟩
def flatY1G {R : Type*} [CommRing R] : AlbertG R := ⟨0, 0, 0, (qOne, qZero), (⟨0, -1, 0, 0⟩, qZero), (qOne, qZero)⟩

def projFrame36 {R : Type*} [CommRing R] (Y : AlbertG R) (i : Fin 3) : AlbertG R :=
  let Y2 := jordan2G Y Y
  if i.1 = 0 then subG Y2 (smulG 6 Y)
  else if i.1 = 1 then subG (smulG 36 unitG) (smulG 2 Y2)
  else addG Y2 (smulG 6 Y)

def flatTriple36 {R : Type*} [CommRing R] (s3 : R) (a i : Fin 3) : AlbertG R :=
  if a.1 = 0 then projFrame36 (smulG 3 flatXNG) i
  else if a.1 = 1 then projFrame36 (smulG s3 flatY1G) i
  else projFrame36 (smulG s3 witnessZG) i

theorem mapAG_projFrame36 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (Y : AlbertG R) (i : Fin 3) :
    mapAG f (projFrame36 Y i) = projFrame36 (mapAG f Y) i := by
  unfold projFrame36; split_ifs <;> simp [mapAG_sub, mapAG_add, mapAG_smul, mapAG_jordan2, mapAG_unit, map_ofNat]

theorem mapAG_flatTriple36 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (s3 : R) (a i : Fin 3) :
    mapAG f (flatTriple36 s3 a i) = flatTriple36 (f s3) a i := by
  unfold flatTriple36; split_ifs <;> rw [mapAG_projFrame36] <;> congr 1 <;>
    (ext <;> simp [mapAG, mapOG, mapQG, smulG, oSmul, qSmul, oZero, qZero, qOne, flatXNG, flatY1G, witnessZG, map_ofNat])

private def U4G {R : Type*} [CommRing R] (a b : AlbertG R) : AlbertG R :=
  subG (smulG 2 (jordan2G a (jordan2G a b))) (jordan2G (jordan2G a a) b)

private def phi128G {R : Type*} [CommRing R] (x y z : AlbertG R) : R :=
  innerG (subG (U4G x (U4G y z)) (U4G y (U4G x z))) (U4G z (jordan2G x y))

private def frameEven {R : Type*} [CommRing R] (X : AlbertG R) (i : Fin 3) : AlbertG R :=
  let X2 := smulG 3 (jordan2G X X)
  if i.1 = 0 then X2 else if i.1 = 1 then subG (smulG 36 unitG) (smulG 2 X2) else X2

private def frameOdd {R : Type*} [CommRing R] (X : AlbertG R) (i : Fin 3) : AlbertG R :=
  if i.1 = 0 then smulG (-6) X else if i.1 = 1 then zeroG else smulG 6 X

private def flatPCache : List (AlbertG ℤ) := (List.finRange 3).map (projFrame36 (smulG 3 flatXNG))
private def flatQeCache : List (AlbertG ℤ) := (List.finRange 3).map (frameEven flatY1G)
private def flatQoCache : List (AlbertG ℤ) := (List.finRange 3).map (frameOdd flatY1G)
private def flatReCache : List (AlbertG ℤ) := (List.finRange 3).map (frameEven witnessZG)
private def flatRoCache : List (AlbertG ℤ) := (List.finRange 3).map (frameOdd witnessZG)
private def flatPQeCache : List (List (AlbertG ℤ)) :=
  (List.finRange 3).map fun i => (List.finRange 3).map fun j => jordan2G (flatPCache.getD i.1 zeroG) (flatQeCache.getD j.1 zeroG)
private def flatPQoCache : List (List (AlbertG ℤ)) :=
  (List.finRange 3).map fun i => (List.finRange 3).map fun j => jordan2G (flatPCache.getD i.1 zeroG) (flatQoCache.getD j.1 zeroG)

private def flatUniformCheck : Bool :=
  (List.finRange 3).all fun i => (List.finRange 3).all fun j =>
    let PQe := (flatPQeCache.getD i.1 []).getD j.1 zeroG
    let PQo := (flatPQoCache.getD i.1 []).getD j.1 zeroG
    (List.finRange 3).all fun k =>
      let Re := flatReCache.getD k.1 zeroG; let Ro := flatRoCache.getD k.1 zeroG
      (innerG PQe Re + 3 * innerG PQo Ro == 10368) && (innerG PQe Ro + innerG PQo Re == 0)

private theorem phi128G_check : phi128G (witnessXG : AlbertG ℤ) flatY1G witnessZG = 512 := by decide +kernel
private theorem flatUniformCheck_eq : flatUniformCheck = true := by decide +kernel

noncomputable section

def liftR : Z3 →+* ℝ := Zsqrtd.toReal (by decide : (0 : ℤ) ≤ 3)

theorem liftR_injective : Function.Injective liftR :=
  Zsqrtd.toReal_injective (by decide) fun n hn => by
    rcases le_or_gt n (-2) with h | h
    · nlinarith
    · rcases le_or_gt 2 n with h2 | h2
      · nlinarith
      · interval_cases n <;> omega

def flatScale : ℝ := 1 / Real.sqrt 3

theorem flatScale_sq : flatScale ^ 2 = 1 / 3 := by
  rw [flatScale, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num

def flatXN : Albert := ⟨1, 0, -1, 0, 0, 0⟩
def flatY1 : Albert := ⟨0, 0, 0, octScalar 1, -octI, octScalar 1⟩

theorem flatXN_eq : flatXN = (-1 : ℝ) • witnessX := by
  apply Albert.ext <;> simp only [flatXN, witnessX, Albert.smul_d0, Albert.smul_d1, Albert.smul_d2,
    Albert.smul_o01, Albert.smul_o02, Albert.smul_o12, smul_zero] <;> norm_num

private theorem flat_props :
    (trace flatXN = 0 ∧ trace witnessX = 0 ∧ trace flatY1 = 0 ∧ trace witnessZ = 0) ∧
    (inner flatXN flatXN = 2 ∧ inner witnessX witnessX = 2 ∧ inner flatY1 flatY1 = 6 ∧ inner witnessZ witnessZ = 6) ∧
    (newtonCubicNorm flatXN = 0 ∧ newtonCubicNorm witnessX = 0 ∧ newtonCubicNorm flatY1 = 0 ∧ newtonCubicNorm witnessZ = 0) := by
  refine ⟨by norm_num [trace, flatXN, witnessX, flatY1, witnessZ],
    by norm_num [inner_self_coordinates, flatXN, witnessX, flatY1, witnessZ, octNormSq, Quaternion.normSq_def', octScalar, octI, octJL, octL, octK, quatI, quatJ, quatK],
    by norm_num [newtonCubicNorm_coordinates, flatXN, witnessX, flatY1, witnessZ, octNormSq, Quaternion.normSq_def', octScalar, octI, octJL, octL, octK, quatI, quatJ, quatK, octMul, octConj, octRe, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]⟩

private theorem phi_witnessX_flatY1_witnessZ : phi witnessX flatY1 witnessZ = 4 := by
  have hZ := phi128G_check
  have hU {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a b : AlbertG R) :
      mapAG f (U4G a b) = U4G (mapAG f a) (mapAG f b) := by simp [U4G, mapAG_sub, mapAG_smul, mapAG_jordan2, map_ofNat]
  have hR := congrArg (Int.castRingHom ℝ) hZ.symm
  simp only [map_ofNat, phi128G, mapAG_inner, mapAG_sub, hU, mapAG_jordan2] at hR
  have hx : toRealAlbert (mapAG (Int.castRingHom ℝ) (witnessXG : AlbertG ℤ)) = witnessX := by ext <;> simp [toRealAlbert, mapAG, mapOG, mapQG, witnessXG, witnessX, oZero, qZero]
  have hy : toRealAlbert (mapAG (Int.castRingHom ℝ) (flatY1G : AlbertG ℤ)) = flatY1 := by ext <;> simp [toRealAlbert, mapAG, mapOG, mapQG, flatY1G, flatY1, oZero, qZero, qOne, octScalar, octI, quatI]
  have hz : toRealAlbert (mapAG (Int.castRingHom ℝ) (witnessZG : AlbertG ℤ)) = witnessZ := by ext <;> simp [toRealAlbert, mapAG, mapOG, mapQG, witnessZG, witnessZ, oZero, qZero, octJL, octL, octK, quatJ, quatK]
  have hUreal (a b : AlbertG ℝ) : toRealAlbert (U4G a b) = (4 : ℝ) • U (toRealAlbert a) (toRealAlbert b) := by
    simp only [U4G, U, toRealAlbert_sub, toRealAlbert_smul, toRealAlbert_jordan2, jordan_smul_left, jordan_smul_right, smul_sub, smul_smul]; module
  simp only [phi128G, Int.cast_ofNat, toRealAlbert_inner, toRealAlbert_sub, hUreal, toRealAlbert_jordan2,
    hx, hy, hz, U_smul_argument, smul_smul, ← smul_sub, Glennie.inner_smul_left, Glennie.inner_smul_right] at hR
  change (512 : ℝ) = 4 * 2 * (4 * 4 * phi witnessX flatY1 witnessZ) at hR; linarith

def flatFrameP : Fin 3 → Albert := projectorFrame flatXN
def flatFrameQ : Fin 3 → Albert := projectorFrame (flatScale • flatY1)
def flatFrameR : Fin 3 → Albert := projectorFrame (flatScale • witnessZ)

theorem flatFrameP_frame : Frame flatFrameP := projectorFrame_is_frame flatXN flat_props.1.1 flat_props.2.1.1 flat_props.2.2.1

theorem flatFrameQ_frame : Frame flatFrameQ :=
  projectorFrame_is_frame _ (by rw [trace_smul, flat_props.1.2.2.1, mul_zero])
    (by rw [inner_smul_left, inner_smul_right, flat_props.2.1.2.2.1]; linear_combination 6 * flatScale_sq)
    (by rw [newtonCubicNorm_smul, flat_props.2.2.2.2.1, mul_zero])

theorem flatFrameR_frame : Frame flatFrameR :=
  projectorFrame_is_frame _ (by rw [trace_smul, flat_props.1.2.2.2, mul_zero])
    (by rw [inner_smul_left, inner_smul_right, flat_props.2.1.2.2.2]; linear_combination 6 * flatScale_sq)
    (by rw [newtonCubicNorm_smul, flat_props.2.2.2.2.2, mul_zero])

theorem flatFrameP_encoder : encoder flatFrameP = flatXN := projectorFrame_encoder _
theorem flatFrameQ_encoder : encoder flatFrameQ = flatScale • flatY1 := projectorFrame_encoder _
theorem flatFrameR_encoder : encoder flatFrameR = flatScale • witnessZ := projectorFrame_encoder _

theorem flat_phi : phi (encoder flatFrameP) (encoder flatFrameQ) (encoder flatFrameR) = -4 / 27 := by
  rw [flatFrameP_encoder, flatFrameQ_encoder, flatFrameR_encoder, flatXN_eq,
    phi_smul_first, phi_smul_second, phi_smul_third, phi_witnessX_flatY1_witnessZ]
  linear_combination (-4 * (flatScale ^ 2 + 1 / 3) * (flatScale ^ 2) + -4 / 9) * flatScale_sq

theorem toRealAlbert_flatTriple36 (a i : Fin 3) :
    toRealAlbert (flatTriple36 (Real.sqrt 3) a i) = (36 : ℝ) • (![flatFrameP, flatFrameQ, flatFrameR] a i) := by
  have hs3 : (1 / 3 : ℝ) * Real.sqrt 3 = flatScale := by
    have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have hne : Real.sqrt 3 ≠ 0 := fun h => by rw [h] at hsq; norm_num at hsq
    rw [flatScale]; field_simp [hne]; linarith
  have hproj (Y : AlbertG ℝ) (l : Fin 3) :
      toRealAlbert (projFrame36 Y l) = (36 : ℝ) • projectorFrame ((1 / 3 : ℝ) • toRealAlbert Y) l := by
    fin_cases l <;> simp [projFrame36, projectorFrame, toRealAlbert_sub, toRealAlbert_add, toRealAlbert_smul,
      toRealAlbert_jordan2, toRealAlbert_unit, jordan_smul_left, jordan_smul_right, smul_sub, smul_add, smul_smul] <;> module
  have hY1 : toRealAlbert (flatY1G : AlbertG ℝ) = flatY1 := by ext <;> simp [toRealAlbert, flatY1G, flatY1, oZero, qZero, qOne, octScalar, octI, quatI]
  have hWZ : toRealAlbert (witnessZG : AlbertG ℝ) = witnessZ := by ext <;> simp [toRealAlbert, witnessZG, witnessZ, oZero, qZero, octJL, octL, octK, quatJ, quatK]
  fin_cases a
  · change toRealAlbert (projFrame36 (smulG 3 flatXNG) i) = (36 : ℝ) • flatFrameP i
    rw [hproj, toRealAlbert_smul, smul_smul]; norm_num; rfl
  · change toRealAlbert (projFrame36 (smulG (Real.sqrt 3) flatY1G) i) = (36 : ℝ) • flatFrameQ i
    rw [hproj, toRealAlbert_smul, hY1, smul_smul, hs3]; rfl
  · change toRealAlbert (projFrame36 (smulG (Real.sqrt 3) witnessZG) i) = (36 : ℝ) • flatFrameR i
    rw [hproj, toRealAlbert_smul, hWZ, smul_smul, hs3]; rfl

theorem flat_uniform : UniformLedger flatFrameP flatFrameQ flatFrameR := by
  have hb := flatUniformCheck_eq
  have hsplit (X : AlbertG ℝ) (l : Fin 3) :
      toRealAlbert (projFrame36 (smulG (Real.sqrt 3) X) l) =
        toRealAlbert (frameEven X l) + Real.sqrt 3 • toRealAlbert (frameOdd X l) := by
    have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    fin_cases l <;> simp only [projFrame36, frameEven, frameOdd,
      ↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, one_ne_zero,
      toRealAlbert_sub, toRealAlbert_add, toRealAlbert_smul, toRealAlbert_jordan2, toRealAlbert_unit,
      show toRealAlbert zeroG = 0 from rfl, jordan_smul_left, jordan_smul_right, smul_smul, hs] <;> module
  have hmE (X : AlbertG ℤ) (l : Fin 3) : mapAG (Int.castRingHom ℝ) (frameEven X l) = frameEven (mapAG (Int.castRingHom ℝ) X) l := by
    unfold frameEven; split_ifs <;> simp [mapAG_sub, mapAG_smul, mapAG_jordan2, mapAG_unit, map_ofNat]
  have hmO (X : AlbertG ℤ) (l : Fin 3) : mapAG (Int.castRingHom ℝ) (frameOdd X l) = frameOdd (mapAG (Int.castRingHom ℝ) X) l := by
    unfold frameOdd; split_ifs <;> try simp [mapAG_smul, map_ofNat]
    ext <;> simp [mapAG, mapOG, mapQG, zeroG, oZero, qZero]
  intro i j k
  have h3 := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hb i (List.mem_finRange i)) j (List.mem_finRange j)) k (List.mem_finRange k))
  have heven := beq_iff_eq.mp h3.1; have hodd := beq_iff_eq.mp h3.2
  have hget {α : Type} (f : Fin 3 → α) (d : α) (l : Fin 3) : ((List.finRange 3).map f).getD l.1 d = f l := by fin_cases l <;> rfl
  simp only [flatPQeCache, flatPQoCache, flatPCache, flatQeCache, flatQoCache, flatReCache, flatRoCache, hget] at heven hodd
  have hRe := congrArg (Int.castRingHom ℝ) heven; have hRo := congrArg (Int.castRingHom ℝ) hodd
  simp only [map_add, map_mul, map_ofNat, map_zero, mapAG_inner, mapAG_jordan2, mapAG_projFrame36, hmE, hmO, mapAG_smul, toRealAlbert_inner, toRealAlbert_jordan2] at hRe hRo
  have hXNR : mapAG (Int.castRingHom ℝ) (flatXNG : AlbertG ℤ) = flatXNG := by ext <;> simp [mapAG, mapOG, mapQG, flatXNG, oZero, qZero]
  have hY1R : mapAG (Int.castRingHom ℝ) (flatY1G : AlbertG ℤ) = flatY1G := by ext <;> simp [mapAG, mapOG, mapQG, flatY1G, oZero, qZero, qOne]
  have hWZR : mapAG (Int.castRingHom ℝ) (witnessZG : AlbertG ℤ) = witnessZG := by ext <;> simp [mapAG, mapOG, mapQG, witnessZG, oZero, qZero]
  rw [hXNR, hY1R, hWZR] at hRe hRo
  generalize hPg : toRealAlbert (projFrame36 (smulG 3 (flatXNG : AlbertG ℝ)) i) = P at hRe hRo
  generalize hQeg : toRealAlbert (frameEven (flatY1G : AlbertG ℝ) j) = Qe at hRe hRo
  generalize hQog : toRealAlbert (frameOdd (flatY1G : AlbertG ℝ) j) = Qo at hRe hRo
  generalize hReg : toRealAlbert (frameEven (witnessZG : AlbertG ℝ) k) = Re at hRe hRo
  generalize hRog : toRealAlbert (frameOdd (witnessZG : AlbertG ℝ) k) = Ro at hRe hRo
  have hP : P = (36 : ℝ) • flatFrameP i := hPg.symm.trans (toRealAlbert_flatTriple36 0 i)
  have hQ : Qe + Real.sqrt 3 • Qo = (36 : ℝ) • flatFrameQ j := by rw [← hQeg, ← hQog]; exact (hsplit flatY1G j).symm.trans (toRealAlbert_flatTriple36 1 j)
  have hR : Re + Real.sqrt 3 • Ro = (36 : ℝ) • flatFrameR k := by rw [← hReg, ← hRog]; exact (hsplit witnessZG k).symm.trans (toRealAlbert_flatTriple36 2 k)
  have htot : Glennie.inner ((2 : ℝ) • jordan ((36 : ℝ) • flatFrameP i) ((36 : ℝ) • flatFrameQ j)) ((36 : ℝ) • flatFrameR k) = 10368 := by
    rw [← hP, ← hQ, ← hR]
    simp only [jordan_add_right, jordan_smul_right, smul_add, smul_smul,
      Glennie.inner_add_left, Glennie.inner_add_right, Glennie.inner_smul_left, Glennie.inner_smul_right] at hRe hRo ⊢
    linear_combination hRe + Real.sqrt 3 * hRo + 2 * Glennie.inner (jordan P Qo) Ro * Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  simp only [jordan_smul_left, jordan_smul_right, smul_smul, Glennie.inner_smul_left, Glennie.inner_smul_right] at htot
  change Glennie.inner (jordan (flatFrameP i) (flatFrameQ j)) (flatFrameR k) = 1 / 9
  linarith

theorem uniform_pair_blocks (p q r : Fin 3 → Albert) (hp : Frame p) (hq : Frame q)
    (hr : Frame r) (hu : UniformLedger p q r) (i j : Fin 3) :
    inner (p i) (q j) = 1 / 3 ∧ inner (q i) (r j) = 1 / 3 ∧ inner (r i) (p j) = 1 / 3 :=
  ⟨uniformLedger_pair_overlap p q r hr hu i j,
    uniformLedger_pair_overlap q r p hp (uniformLedger_cyclic p q r hu) i j,
    uniformLedger_pair_overlap r p q hq (uniformLedger_cyclic q r p (uniformLedger_cyclic p q r hu)) i j⟩

end
end Glennie.Compact.FlatBase
