/- Unified independent native and admitted orbit-quotient statement surface. -/
module
public import AlbertRecognition.CubicFiber
public import Glennie.Diagonalization
public import Glennie.Theorems.Frames
public import Glennie.Compact.PairNormNearby
public import Glennie.Compact.NativeNormKernelR01
public import Glennie.Compact.NativeWordTableBasisR01
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Quaternion
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Glennie.SubmissionR03
noncomputable section
open Glennie
open Glennie.Compact.Affine20
open scoped BigOperators

def f0 : Fin 3 := ⟨0, Nat.zero_lt_succ 2⟩
def f1 : Fin 3 := ⟨1, Nat.lt_succ_of_le (Nat.le_succ 1)⟩
def f2 : Fin 3 := ⟨2, Nat.lt_succ_self 2⟩
def b0 : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩
def b1 : Fin 2 := ⟨1, Nat.lt_succ_self 1⟩

def fullLedger (T : Triple) : Ledger54 :=
  (ledger (T f0) (T f1) (T f2),
   fun i j => inner (T f0 i) (T f1 j),
   fun j k => inner (T f1 j) (T f2 k),
   fun k i => inner (T f2 k) (T f0 i))

def framePower (p : Fin 3 → Albert) (s : Fin 2) : Albert :=
  if s = b0 then encoder p else jordan (encoder p) (encoder p)
def qSingle (T : Triple) (v : Fin 3) (s : Fin 2) : ℝ :=
  inner (framePower (T v) b0) (framePower (T v) s)
def qPair (T : Triple) (v w : Fin 3) (s t : Fin 2) : ℝ :=
  inner (framePower (T v) s) (framePower (T w) t)
def qTriple (T : Triple) (s t u : Fin 2) : ℝ :=
  trace (jordan (jordan (framePower (T f0) s) (framePower (T f1) t))
    (framePower (T f2) u))
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

def phiOf (T : Triple) : ℝ :=
  phi (encoder (T f0)) (encoder (T f1)) (encoder (T f2))

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
def mapAtoms (g : CompactAutomorphism) (T : Triple) : Triple :=
  fun a i => g.equiv (T a i)

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

theorem phi_nonzero_generation_stabilizer
    (x y z : Albert) (hphi : phi x y z ≠ 0) :
    (∀ K : Submodule ℝ Albert, (1 : Albert) ∈ K →
      (∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) →
      x ∈ K → y ∈ K → z ∈ K → K = ⊤) ∧
    (∀ g : CompactAutomorphism,
      g.equiv x = x → g.equiv y = y → g.equiv z = z →
      g.equiv = LinearEquiv.refl ℝ Albert) ∧
    (∀ D : Albert →ₗ[ℝ] Albert,
      (∀ p q, D (jordan p q) = jordan (D p) q + jordan p (D q)) →
      D x = 0 → D y = 0 → D z = 0 → D = 0) := by
  have hgen := fun K h1 hJ hx hy hz =>
    Glennie.NativeGenerationEndpointR01.eq_top_of_phi_ne_zero K h1 hJ x y z hx hy hz hphi
  refine ⟨hgen, fun g hx hy hz => ?_, fun D hD hx hy hz => ?_⟩
  · have hF := hgen (g.equiv.toLinearMap - .id).ker (sub_eq_zero.mpr g.map_unit)
      (fun p hp q hq => sub_eq_zero.mpr (by
        change g.equiv (jordan p q) = jordan p q
        rw [g.map_jordan, show g.equiv p = p from sub_eq_zero.mp hp, show g.equiv q = q from sub_eq_zero.mp hq]))
      (sub_eq_zero.mpr hx) (sub_eq_zero.mpr hy) (sub_eq_zero.mpr hz)
    exact LinearEquiv.ext fun t => sub_eq_zero.mp (show t ∈ (g.equiv.toLinearMap - .id).ker by rw [hF]; trivial)
  · have h1 : D 1 = 0 := add_left_cancel
      (by simpa only [jordan_unit_left, jordan_unit_right, add_zero] using (hD 1 1).symm)
    have hK := hgen D.ker h1 (fun p hp q hq => by
      change D (jordan p q) = 0
      rw [hD, show D p = 0 from hp, show D q = 0 from hq, jordan_zero_left, jordan_zero_right, add_zero]) hx hy hz
    exact LinearMap.ker_eq_top.mp hK

private def momW : Fin 3 → Fin 3 → ℝ := ![![1, 1, 1], ![-1, 0, 1], ![1, 0, 1]]
private def frameMom (p : Fin 3 → Albert) : Fin 3 → Albert := ![1, framePower p b0, framePower p b1]

private theorem qSingle_on_frame (T : Triple) (hT : ∀ a, Frame (T a)) (v : Fin 3) (s : Fin 2) :
    qSingle T v s = if s = b0 then 2 else 0 := by
  fin_cases s <;> dsimp
  · simpa [qSingle, framePower, b0] using frame_encoder_norm (T v) (hT v)
  · simp only [qSingle, framePower, show (1 : Fin 2) ≠ b0 by decide, ↓reduceIte]
    change trace (jordan (encoder (T v)) (jordan (encoder (T v)) (encoder (T v)))) = 0
    rw [frame_encoder_cube (T v) (hT v)]; exact frame_encoder_trace (T v) (hT v)

theorem q26_eq_iff_fullLedger_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q26 T = q26 S ↔ fullLedger T = fullLedger S := by
  have hfM_sum (p : Fin 3 → Albert) (hp : Frame p) (r : Fin 3) :
      frameMom p r = ∑ i, momW r i • p i := by
    fin_cases r <;> dsimp
    · simp [frameMom, momW, Fin.sum_univ_three, ← hp.sum_unit]
    · simp [frameMom, framePower, momW, Fin.sum_univ_three, encoder]; abel
    · simp [frameMom, framePower, show b1 ≠ b0 by decide, momW, Fin.sum_univ_three, frame_encoder_square p hp]; abel
  have hfM_tr (p : Fin 3 → Albert) (hp : Frame p) (r : Fin 3) :
      trace (frameMom p r) = (![3, 0, 2] : Fin 3 → ℝ) r := by
    fin_cases r <;> dsimp
    · simp [frameMom]
    · simpa [frameMom, framePower] using frame_encoder_trace p hp
    · simpa [frameMom, framePower, show b1 ≠ b0 by decide, inner] using frame_encoder_norm p hp
  let mom3 (X : Triple) (r s t : Fin 3) : ℝ :=
    trace (jordan (jordan (frameMom (X f0) r) (frameMom (X f1) s)) (frameMom (X f2) t))
  have hmom3_w (X : Triple) (hX : ∀ a, Frame (X a)) (r s t : Fin 3) :
      mom3 X r s t = ∑ i, ∑ j, ∑ k, (momW r i * momW s j * momW t k) * (fullLedger X).1 i j k := by
    dsimp only [mom3]
    rw [hfM_sum (X f0) (hX f0) r, hfM_sum (X f1) (hX f1) s, hfM_sum (X f2) (hX f2) t]
    simp [fullLedger, ledger, Fin.sum_univ_three, jordan_add_left, jordan_add_right,
      jordan_smul_left, jordan_smul_right, trace_add, trace_smul]; ring
  have hpos (p : Fin 3 → Albert) (r : Fin 3) (hr : r ≠ 0) :
      frameMom p r = framePower p (if r = 1 then b0 else b1) := by
    fin_cases r <;> simp_all [frameMom]
  let ix (a : Fin 2) : Fin 3 := ⟨a.1 + 1, by omega⟩
  have hix (p : Fin 3 → Albert) (a : Fin 2) : frameMom p (ix a) = framePower p a := by fin_cases a <;> rfl
  constructor
  · intro h
    have hxy (a b : Fin 2) : qPair T f0 f1 a b = qPair S f0 f1 a b := by
      fin_cases a <;> fin_cases b <;> [exact congrFun h 6; exact congrFun h 7; exact congrFun h 8; exact congrFun h 9]
    have hyz (a b : Fin 2) : qPair T f1 f2 a b = qPair S f1 f2 a b := by
      fin_cases a <;> fin_cases b <;> [exact congrFun h 10; exact congrFun h 11; exact congrFun h 12; exact congrFun h 13]
    have hzx (a b : Fin 2) : qPair T f2 f0 a b = qPair S f2 f0 a b := by
      fin_cases a <;> fin_cases b <;> [exact congrFun h 14; exact congrFun h 15; exact congrFun h 16; exact congrFun h 17]
    have htr3 (a b c : Fin 2) : qTriple T a b c = qTriple S a b c := by
      fin_cases a <;> fin_cases b <;> fin_cases c <;> [
        exact congrFun h 18; exact congrFun h 19; exact congrFun h 20; exact congrFun h 21;
        exact congrFun h 22; exact congrFun h 23; exact congrFun h 24; exact congrFun h 25]
    have hm2 (u v : Fin 3) (hp : ∀ a b, qPair T u v a b = qPair S u v a b) (r s : Fin 3) :
        inner (frameMom (T u) r) (frameMom (T v) s) = inner (frameMom (S u) r) (frameMom (S v) s) := by
      have h10 (p : Fin 3 → Albert) : frameMom p 0 = 1 := rfl
      by_cases hr : r = 0
      · subst hr; rw [h10, h10, inner_unit_left, inner_unit_left, hfM_tr _ (hT v), hfM_tr _ (hS v)]
      · by_cases hs : s = 0
        · subst hs; rw [h10, h10, inner_unit_right, inner_unit_right, hfM_tr _ (hT u), hfM_tr _ (hS u)]
        · rw [hpos _ r hr, hpos _ s hs, hpos _ r hr, hpos _ s hs]; exact hp _ _
    have hm3 (r s t : Fin 3) : mom3 T r s t = mom3 S r s t := by
      by_cases hr : r = 0
      · subst hr; simpa [mom3, frameMom, inner, jordan_unit_left] using hm2 f1 f2 hyz s t
      · by_cases hs : s = 0
        · subst hs; dsimp only [mom3]
          have h10 (p : Fin 3 → Albert) : frameMom p 0 = 1 := rfl
          rw [h10, h10, jordan_unit_right, jordan_unit_right, jordan_comm (frameMom (T f0) r), jordan_comm (frameMom (S f0) r)]
          exact hm2 f2 f0 hzx t r
        · by_cases ht : t = 0
          · subst ht; simpa [mom3, frameMom, inner, jordan_unit_right] using hm2 f0 f1 hxy r s
          · dsimp only [mom3]; rw [hpos _ r hr, hpos _ s hs, hpos _ t ht, hpos _ r hr, hpos _ s hs, hpos _ t ht]; exact htr3 _ _ _
    have hw1 {f g : Fin 3 → ℝ} (hw : ∀ r, ∑ i, momW r i * f i = ∑ i, momW r i * g i) : f = g := by
      have h0 := hw 0; have h1 := hw 1; have h2 := hw 2
      simp only [momW, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2
      norm_num at h0 h1 h2
      funext i; fin_cases i <;> dsimp <;> linarith
    have hC : (fullLedger T).1 = (fullLedger S).1 := funext fun i => funext fun j =>
      hw1 (f := (fullLedger T).1 i j) (g := (fullLedger S).1 i j) fun t =>
        congrFun (hw1 (f := fun j => ∑ k, momW t k * (fullLedger T).1 i j k)
          (g := fun j => ∑ k, momW t k * (fullLedger S).1 i j k) fun s =>
          congrFun (hw1 (f := fun i => ∑ j, momW s j * ∑ k, momW t k * (fullLedger T).1 i j k)
            (g := fun i => ∑ j, momW s j * ∑ k, momW t k * (fullLedger S).1 i j k) fun r => by
            simpa only [Finset.mul_sum, mul_assoc] using (hmom3_w T hT r s t).symm.trans ((hm3 r s t).trans (hmom3_w S hS r s t))) i) j
    have hQ (X : Triple) (hX : ∀ a, Frame (X a)) (j k : Fin 3) :
        (fullLedger X).2.2.1 j k = ∑ i, (fullLedger X).1 i j k := by
      dsimp only [fullLedger]; rw [← ledger_last_marginal (X f1) (X f2) (X f0) (hX f0) j k]
      exact Finset.sum_congr rfl fun i _ => (ledger_cyclic _ _ _ i j k).symm
    have hR (X : Triple) (hX : ∀ a, Frame (X a)) (k i : Fin 3) :
        (fullLedger X).2.2.2 k i = ∑ j, (fullLedger X).1 i j k := by
      dsimp only [fullLedger]; rw [← ledger_last_marginal (X f2) (X f0) (X f1) (hX f1) k i]
      exact Finset.sum_congr rfl fun j _ => ledger_cyclic _ _ _ k i j
    have hP (X : Triple) (hX : ∀ a, Frame (X a)) (i j : Fin 3) :
        (fullLedger X).2.1 i j = ∑ k, (fullLedger X).1 i j k :=
      (ledger_last_marginal (X f0) (X f1) (X f2) (hX f2) i j).symm
    exact Prod.ext hC (Prod.ext (funext fun i => funext fun j => by rw [hP T hT, hP S hS, hC])
      (Prod.ext (funext fun j => funext fun k => by rw [hQ T hT, hQ S hS, hC])
        (funext fun k => funext fun i => by rw [hR T hT, hR S hS, hC])))
  · intro h
    have hs (v : Fin 3) (s : Fin 2) : qSingle T v s = qSingle S v s := by rw [qSingle_on_frame T hT, qSingle_on_frame S hS]
    have hm3 (r s t : Fin 3) : mom3 T r s t = mom3 S r s t := by rw [hmom3_w T hT, hmom3_w S hS, h]
    have hxy (a b : Fin 2) : qPair T f0 f1 a b = qPair S f0 f1 a b := by
      have h0 (X : Triple) : frameMom (X f2) 0 = 1 := rfl
      simpa only [mom3, h0, hix, qPair, inner, jordan_unit_right] using hm3 (ix a) (ix b) 0
    have hyz (a b : Fin 2) : qPair T f1 f2 a b = qPair S f1 f2 a b := by
      have h0 (X : Triple) : frameMom (X f0) 0 = 1 := rfl
      simpa only [mom3, h0, hix, qPair, inner, jordan_unit_left] using hm3 0 (ix a) (ix b)
    have hzx (a b : Fin 2) : qPair T f2 f0 a b = qPair S f2 f0 a b := by
      have hz0 (X : Triple) : mom3 X (ix b) 0 (ix a) = qPair X f2 f0 a b := by
        dsimp only [mom3, qPair, inner]; rw [show frameMom (X f1) 0 = 1 from rfl, jordan_unit_right, jordan_comm, hix, hix]
      rw [← hz0, ← hz0]; exact hm3 _ _ _
    have htr (a b c : Fin 2) : qTriple T a b c = qTriple S a b c := by
      simpa [mom3, hix, qTriple] using hm3 (ix a) (ix b) (ix c)
    funext n; fin_cases n <;> simp [q26, hs, hxy, hyz, hzx, htr]

def q20 (T : Triple) : Fin 20 → ℝ :=
  fun i => q26 T ⟨i.val + 6, Nat.add_lt_add_right i.2 6⟩

theorem q20_eq_iff_fullLedger_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q20 T = q20 S ↔ fullLedger T = fullLedger S :=
  ⟨fun h => (q26_eq_iff_fullLedger_eq T S hT hS).mp (funext fun n => by
    by_cases hn : n.1 < 6
    · fin_cases n <;> dsimp at hn <;> first | (simp [q26, qSingle_on_frame T hT, qSingle_on_frame S hS]; done) | omega
    · simpa [q20, Nat.sub_add_cancel (not_lt.mp hn)] using congrFun h ⟨n.1 - 6, by omega⟩),
   fun h => funext fun _ => congrFun ((q26_eq_iff_fullLedger_eq T S hT hS).mpr h) _⟩

theorem division_free (x y z : Albert) :
    4 * delta x y z (halfAmplitude x) y - delta x y z x y -
      delta x y z 1 y = 2 * phi x y z := by
  have hj (u a b : Albert) : inner a (jordan u b) = inner (jordan u a) b := by
    rw [← inner_jordan_associative, jordan_comm a u]
  have hU (u a b : Albert) : inner a (U u b) = inner (U u a) b := by
    simp only [U, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hj]
  have h4 : (4 : ℝ) • U (halfAmplitude x) y - U x y - U 1 y = (2 : ℝ) • jordan x y := by
    rw [show halfAmplitude x = (1 / 2 : ℝ) • ((1 : Albert) + x) by simp [halfAmplitude], U_smul_base, U_add_base]
    simp only [U, crossU, jordan_unit_left]; module
  have hc := congrArg (contrast x y z) h4
  have cs (u v : Albert) : contrast x y z (u - v) = contrast x y z u - contrast x y z v := by
    simp only [contrast, U_sub_argument, inner_sub_right]; ring
  have cm (r : ℝ) (v : Albert) : contrast x y z (r • v) = r * contrast x y z v := by
    simp only [contrast, U_smul_argument, inner_sub_right, inner_smul_right]; ring
  have hphi : contrast x y z (jordan x y) = phi x y z := by
    simp only [phi, contrast, inner_sub_left, inner_sub_right, ← hU]
  simpa only [delta, cs, cm, hphi] using hc

theorem score_eq_two_phi (T : Triple) : score T = 2 * phiOf T :=
  division_free (encoder (T f0)) (encoder (T f1)) (encoder (T f2))

theorem atoms_generate_of_score
    (T : Triple) (hT : ∀ a, Frame (T a)) (hs : score T ≠ 0)
    (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (hAtoms : ∀ a i, T a i ∈ K) : K = ⊤ := by
  have hphi : phiOf T ≠ 0 := fun hz => hs (by rw [score_eq_two_phi, hz, mul_zero])
  have hu : (1 : Albert) ∈ K := by
    rw [← (hT 0).sum_unit]; exact K.add_mem (K.add_mem (hAtoms 0 0) (hAtoms 0 1)) (hAtoms 0 2)
  exact (phi_nonzero_generation_stabilizer _ _ _ hphi).1 K hu hJ
    (K.sub_mem (hAtoms f0 2) (hAtoms f0 0))
    (K.sub_mem (hAtoms f1 2) (hAtoms f1 0))
    (K.sub_mem (hAtoms f2 2) (hAtoms f2 0))

private def LBox : Set Ledger54 := {L | ∀ i j : Fin 3, |L.2.1 i j - 1 / 3| < 1 / 50}

private theorem isOpen_LBox : IsOpen LBox := by
  rw [show LBox = ⋂ r : Fin 3 × Fin 3, {L : Ledger54 | |L.2.1 r.1 r.2 - 1 / 3| < 1 / 50} by ext; simp [LBox, Prod.forall]]
  refine isOpen_iInter_of_finite fun r => ?_
  have hc : Continuous (fun L : Ledger54 => L.2.1 r.1 r.2) :=
    (continuous_apply r.2).comp ((continuous_apply r.1).comp (continuous_fst.comp continuous_snd))
  exact isOpen_lt ((hc.sub continuous_const).abs) continuous_const

private theorem f_eq : f0 = 0 ∧ f1 = 1 ∧ f2 = 2 := ⟨rfl, rfl, rfl⟩

private theorem projFrame_eq (x : Albert) : projectorFrame x = Glennie.projectorFrame x := by
  funext i; fin_cases i <;> (apply Albert.ext <;> simp [projectorFrame, Glennie.projectorFrame])

private theorem flatBase_eq_frames :
    flatBase = ![Glennie.Compact.FlatBase.flatFrameP, Glennie.Compact.FlatBase.flatFrameQ, Glennie.Compact.FlatBase.flatFrameR] := by
  have hXN : flatXN = Glennie.Compact.FlatBase.flatXN := by apply Albert.ext <;> rfl
  have hY1 : flatY1 = Glennie.Compact.FlatBase.flatY1 := by apply Albert.ext <;> rfl
  have hWZ : witnessZ = Glennie.witnessZ := by apply Albert.ext <;> rfl
  have hsc : flatScale = Glennie.Compact.FlatBase.flatScale := rfl
  unfold flatBase; rw [projFrame_eq, projFrame_eq, projFrame_eq, hXN, hY1, hWZ, hsc]; rfl

private theorem flatBase_frames (a : Fin 3) : Frame (flatBase a) := by
  rw [flatBase_eq_frames]; fin_cases a <;> dsimp
  · exact Glennie.Compact.FlatBase.flatFrameP_frame
  · exact Glennie.Compact.FlatBase.flatFrameQ_frame
  · exact Glennie.Compact.FlatBase.flatFrameR_frame

private theorem fullLedger_flatBase :
    fullLedger flatBase = (fun _ _ _ => 1 / 9, fun _ _ => 1 / 3, fun _ _ => 1 / 3, fun _ _ => 1 / 3) := by
  have hu := Glennie.Compact.FlatBase.uniform_pair_blocks _ _ _
    Glennie.Compact.FlatBase.flatFrameP_frame Glennie.Compact.FlatBase.flatFrameQ_frame
    Glennie.Compact.FlatBase.flatFrameR_frame Glennie.Compact.FlatBase.flat_uniform
  have h0 : flatBase f0 = Glennie.Compact.FlatBase.flatFrameP := by rw [f_eq.1, flatBase_eq_frames]; rfl
  have h1 : flatBase f1 = Glennie.Compact.FlatBase.flatFrameQ := by rw [f_eq.2.1, flatBase_eq_frames]; rfl
  have h2 : flatBase f2 = Glennie.Compact.FlatBase.flatFrameR := by rw [f_eq.2.2, flatBase_eq_frames]; rfl
  unfold fullLedger; rw [h0, h1, h2]
  exact Prod.ext (funext fun i => funext fun j => funext fun k => Glennie.Compact.FlatBase.flat_uniform i j k)
    (Prod.ext (funext fun i => funext fun j => (hu i j).1)
      (Prod.ext (funext fun j => funext fun k => (hu j k).2.1)
        (funext fun k => funext fun i => (hu k i).2.2)))

private theorem flatBase_mem_LBox : fullLedger flatBase ∈ LBox := fun i j => by
  change |(fullLedger flatBase).2.1 i j - 1 / 3| < 1 / 50; rw [fullLedger_flatBase]; norm_num

private theorem phiT_eq (T : Triple) : Glennie.Compact.PairNormNearby.phiT T = phiOf T := by
  unfold Glennie.Compact.PairNormNearby.phiT phiOf; rw [f_eq.1, f_eq.2.1, f_eq.2.2]

private theorem led54_eq (T : Triple) : Glennie.Compact.PairNormNearby.led54 T = fullLedger T := by
  unfold Glennie.Compact.PairNormNearby.led54 fullLedger; rw [f_eq.1, f_eq.2.1, f_eq.2.2]

theorem nearby_sign_rigidity :
    ∃ V : Set Ledger54, IsOpen V ∧ fullLedger flatBase ∈ V ∧
      ∀ T S : Triple, (∀ a : Fin 3, Frame (T a)) →
        (∀ a : Fin 3, Frame (S a)) → fullLedger T ∈ V →
        fullLedger T = fullLedger S →
        ((phiOf T < 0 ∧ phiOf S < 0) ∨ (0 < phiOf T ∧ 0 < phiOf S)) →
        ∃ k : CompactAutomorphism, mapAtoms k S = T := by
  refine ⟨LBox, isOpen_LBox, flatBase_mem_LBox, fun T S hT hS hTV hTS hsign => ?_⟩
  have hTne : Glennie.Compact.PairNormNearby.phiT T ≠ 0 := by rw [phiT_eq]; rcases hsign with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have hbox : ∀ i j : Fin 3, |(Glennie.Compact.PairNormNearby.led54 T).2.1 i j - 1 / 3| < 1 / 50 := by rw [led54_eq]; exact hTV
  obtain ⟨hsq, himp⟩ := Glennie.Compact.PairNormNearby.nearby_core T S hT hS hbox (by rw [led54_eq, led54_eq, hTS]) hTne
  rw [phiT_eq, phiT_eq] at hsq himp
  refine himp ?_
  rcases mul_eq_zero.mp (by linear_combination hsq : (phiOf T - phiOf S) * (phiOf T + phiOf S) = 0) with h | h
  · linarith
  · rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

def centred (L : Ledger54) (i j k : Fin 3) : ℝ :=
  L.1 i j k - (L.2.1 i j + L.2.2.1 j k + L.2.2.2 k i) / (Nat.cast 3 : ℝ) + (Nat.cast 2 : ℝ) / (Nat.cast 9 : ℝ)
def encode20 (L : Ledger54) : Fin 20 → ℝ :=
  ![L.2.1 f0 f0 - 1 / (Nat.cast 3 : ℝ), L.2.1 f0 f1 - 1 / (Nat.cast 3 : ℝ), L.2.1 f1 f0 - 1 / (Nat.cast 3 : ℝ), L.2.1 f1 f1 - 1 / (Nat.cast 3 : ℝ),
    L.2.2.1 f0 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.1 f0 f1 - 1 / (Nat.cast 3 : ℝ), L.2.2.1 f1 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.1 f1 f1 - 1 / (Nat.cast 3 : ℝ),
    L.2.2.2 f0 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.2 f0 f1 - 1 / (Nat.cast 3 : ℝ), L.2.2.2 f1 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.2 f1 f1 - 1 / (Nat.cast 3 : ℝ),
    centred L f0 f0 f0, centred L f0 f0 f1, centred L f0 f1 f0, centred L f0 f1 f1,
    centred L f1 f0 f0, centred L f1 f0 f1, centred L f1 f1 f0, centred L f1 f1 f1]
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

def fibre54 (b : Fin 20 → ℝ) : Set Triple :=
  {T | (∀ a : Fin 3, Frame (T a)) ∧ fullLedger T = decode20 b}
def fibre20 (b : Fin 20 → ℝ) : Set Triple :=
  {T | (∀ a : Fin 3, Frame (T a)) ∧ encode20 (fullLedger T) = b}
def autOrbit (S : Triple) : Set Triple :=
  {T | ∃ g : CompactAutomorphism, mapAtoms g S = T}

section ChartAndSections
attribute [-instance] FloorSemiring.instCharZero RCLike.charZero_rclike
open Glennie.Compact.FlowFamily Glennie.Compact.FlatBase

private structure InDom (L : Ledger54) : Prop where
  pr : ∀ i, L.2.1 i 0 + L.2.1 i 1 + L.2.1 i 2 = 1
  pc : ∀ j, L.2.1 0 j + L.2.1 1 j + L.2.1 2 j = 1
  qr : ∀ j, L.2.2.1 j 0 + L.2.2.1 j 1 + L.2.2.1 j 2 = 1
  qc : ∀ k, L.2.2.1 0 k + L.2.2.1 1 k + L.2.2.1 2 k = 1
  rr : ∀ k, L.2.2.2 k 0 + L.2.2.2 k 1 + L.2.2.2 k 2 = 1
  rc : ∀ i, L.2.2.2 0 i + L.2.2.2 1 i + L.2.2.2 2 i = 1
  ck : ∀ i j, L.1 i j 0 + L.1 i j 1 + L.1 i j 2 = L.2.1 i j
  ci : ∀ j k, L.1 0 j k + L.1 1 j k + L.1 2 j k = L.2.2.1 j k
  cj : ∀ k i, L.1 i 0 k + L.1 i 1 k + L.1 i 2 k = L.2.2.2 k i

private theorem fullLedger_inDom (T : Triple) (hT : ∀ a, Frame (T a)) : InDom (fullLedger T) := by
  have pr (p q : Fin 3 → Albert) (hp : Frame p) (hq : Frame q) (i : Fin 3) :
      inner (p i) (q 0) + inner (p i) (q 1) + inner (p i) (q 2) = 1 := by
    rw [← inner_add_right, ← inner_add_right, hq.sum_unit, inner_unit_right, hp.trace_one]
  have pc (p q : Fin 3 → Albert) (hp : Frame p) (hq : Frame q) (j : Fin 3) :
      inner (p 0) (q j) + inner (p 1) (q j) + inner (p 2) (q j) = 1 := by
    rw [inner_comm (p 0), inner_comm (p 1), inner_comm (p 2)]; exact pr q p hq hp j
  have lm (p q r : Fin 3 → Albert) (hr : Frame r) (i j : Fin 3) :
      ledger p q r i j 0 + ledger p q r i j 1 + ledger p q r i j 2 = inner (p i) (q j) := by
    simp only [ledger]; rw [← trace_add, ← trace_add, ← jordan_add_right, ← jordan_add_right, hr.sum_unit, jordan_unit_right]; rfl
  refine ⟨pr _ _ (hT 0) (hT 1), pc _ _ (hT 0) (hT 1), pr _ _ (hT 1) (hT 2), pc _ _ (hT 1) (hT 2),
    pr _ _ (hT 2) (hT 0), pc _ _ (hT 2) (hT 0), lm _ _ _ (hT 2), fun j k => ?_, fun k i => ?_⟩
  · change ledger _ _ _ 0 j k + ledger _ _ _ 1 j k + ledger _ _ _ 2 j k = _
    rw [ledger_cyclic _ _ _ 0 j k, ledger_cyclic _ _ _ 1 j k, ledger_cyclic _ _ _ 2 j k]; exact lm _ _ _ (hT 0) j k
  · change ledger _ _ _ i 0 k + ledger _ _ _ i 1 k + ledger _ _ _ i 2 k = _
    rw [ledger_cyclic _ _ _ i 0 k, ledger_cyclic _ _ _ i 1 k, ledger_cyclic _ _ _ i 2 k,
      ledger_cyclic _ _ _ 0 k i, ledger_cyclic _ _ _ 1 k i, ledger_cyclic _ _ _ 2 k i]; exact lm _ _ _ (hT 1) k i

private theorem dec_enc (L : Ledger54) (h : InDom L) : decode20 (encode20 L) = L := by
  have he3 (v : Fin 3 → ℝ) (hv : v 0 + v 1 + v 2 = 0) (i : Fin 3) : ext3 (v 0) (v 1) i = v i := by
    fin_cases i <;> simp [ext3] <;> linarith
  have hl4 (M : Fin 3 → Fin 3 → ℝ) (hr : ∀ i, M i 0 + M i 1 + M i 2 = 0) (hc : ∀ j, M 0 j + M 1 j + M 2 j = 0) (i j : Fin 3) :
      lift4 (M 0 0) (M 0 1) (M 1 0) (M 1 1) i j = M i j := by
    unfold lift4; rw [he3 (M 0) (hr 0) j, he3 (M 1) (hr 1) j]; exact he3 (fun l => M l j) (hc j) i
  have hb (B : Fin 3 → Fin 3 → ℝ) (hr : ∀ i, B i 0 + B i 1 + B i 2 = 1) (hc : ∀ j, B 0 j + B 1 j + B 2 j = 1) (i j : Fin 3) :
      1 / (Nat.cast 3 : ℝ) + lift4 (B f0 f0 - 1 / (Nat.cast 3 : ℝ)) (B f0 f1 - 1 / (Nat.cast 3 : ℝ))
        (B f1 f0 - 1 / (Nat.cast 3 : ℝ)) (B f1 f1 - 1 / (Nat.cast 3 : ℝ)) i j = B i j := by
    dsimp [f0, f1]; norm_num; rw [hl4 (fun a b => B a b - 1 / 3) (fun a => by linarith [hr a]) (fun b => by linarith [hc b]) i j]; ring
  have hl8 (H : Fin 3 → Fin 3 → Fin 3 → ℝ)
      (hx : ∀ j k, H 0 j k + H 1 j k + H 2 j k = 0) (hy : ∀ i k, H i 0 k + H i 1 k + H i 2 k = 0)
      (hz : ∀ i j, H i j 0 + H i j 1 + H i j 2 = 0) (i j k : Fin 3) :
      lift8 (H 0 0 0) (H 0 0 1) (H 0 1 0) (H 0 1 1) (H 1 0 0) (H 1 0 1) (H 1 1 0) (H 1 1 1) i j k = H i j k := by
    unfold lift8
    rw [he3 (H 0 0) (hz 0 0) k, he3 (H 0 1) (hz 0 1) k, he3 (H 1 0) (hz 1 0) k, he3 (H 1 1) (hz 1 1) k,
      he3 (fun l => H 0 l k) (hy 0 k) j, he3 (fun l => H 1 l k) (hy 1 k) j]
    exact he3 (fun l => H l j k) (hx j k) i
  have hc (i j k : Fin 3) : decC (encode20 L) i j k = L.1 i j k := by
    have hH := hl8 (centred L)
      (fun j k => by simp only [centred]; norm_num; linarith [h.ci j k, h.pc j, h.rr k])
      (fun i k => by simp only [centred]; norm_num; linarith [h.cj k i, h.pr i, h.qc k])
      (fun i j => by simp only [centred]; norm_num; linarith [h.ck i j, h.qr j, h.rc i]) i j k
    have hP := hb L.2.1 h.pr h.pc i j; have hQ := hb L.2.2.1 h.qr h.qc j k; have hR := hb L.2.2.2 h.rr h.rc k i
    dsimp [decC, decP, decQ, decR, encode20, f0, f1] at hP hQ hR ⊢
    rw [hH, hP, hQ, hR]; simp only [centred]; norm_num; ring
  exact Prod.ext (funext fun i => funext fun j => funext fun k => hc i j k)
    (Prod.ext (funext fun i => funext fun j => hb L.2.1 h.pr h.pc i j)
      (Prod.ext (funext fun j => funext fun k => hb L.2.2.1 h.qr h.qc j k)
        (funext fun k => funext fun i => hb L.2.2.2 h.rr h.rc k i)))

private theorem dec20_inDom (v : Fin 20 → ℝ) : InDom (decode20 v) := by
  have h4r (a b c d : ℝ) (i : Fin 3) : lift4 a b c d i 0 + lift4 a b c d i 1 + lift4 a b c d i 2 = 0 := by fin_cases i <;> simp [lift4, ext3] <;> ring
  have h4c (a b c d : ℝ) (j : Fin 3) : lift4 a b c d 0 j + lift4 a b c d 1 j + lift4 a b c d 2 j = 0 := by fin_cases j <;> simp [lift4, ext3] <;> ring
  refine ⟨fun i => by dsimp [decode20, decP]; norm_num; linarith [h4r (v 0) (v 1) (v 2) (v 3) i],
    fun j => by dsimp [decode20, decP]; norm_num; linarith [h4c (v 0) (v 1) (v 2) (v 3) j],
    fun j => by dsimp [decode20, decQ]; norm_num; linarith [h4r (v 4) (v 5) (v 6) (v 7) j],
    fun k => by dsimp [decode20, decQ]; norm_num; linarith [h4c (v 4) (v 5) (v 6) (v 7) k],
    fun k => by dsimp [decode20, decR]; norm_num; linarith [h4r (v 8) (v 9) (v 10) (v 11) k],
    fun i => by dsimp [decode20, decR]; norm_num; linarith [h4c (v 8) (v 9) (v 10) (v 11) i],
    fun i j => by fin_cases i <;> fin_cases j <;> simp [decode20, decC, decP, decQ, decR, lift8, lift4, ext3] <;> ring,
    fun j k => by fin_cases j <;> fin_cases k <;> simp [decode20, decC, decP, decQ, decR, lift8, lift4, ext3] <;> ring,
    fun k i => by fin_cases k <;> fin_cases i <;> simp [decode20, decC, decP, decQ, decR, lift8, lift4, ext3] <;> ring⟩

private theorem enc20_dec20 (v : Fin 20 → ℝ) : encode20 (decode20 v) = v := by
  funext n; fin_cases n <;> simp [encode20, centred, decode20, decC, decP, decQ, decR, lift8, lift4, ext3, f0, f1] <;> ring

theorem continuous_encode20 : Continuous encode20 :=
  continuous_pi fun n => by fin_cases n <;> dsimp [encode20, centred] <;> fun_prop

private theorem continuous_decode20 : Continuous decode20 := by
  have he {a b : (Fin 20 → ℝ) → ℝ} (ha : Continuous a) (hb : Continuous b) (i : Fin 3) :
      Continuous (fun x => ext3 (a x) (b x) i) := by fin_cases i <;> dsimp [ext3] <;> fun_prop
  have hl4 (a b c d : Fin 20) (i j : Fin 3) : Continuous (fun v : Fin 20 → ℝ => lift4 (v a) (v b) (v c) (v d) i j) :=
    he (he (continuous_apply a) (continuous_apply b) j) (he (continuous_apply c) (continuous_apply d) j) i
  have hl8 (i j k : Fin 3) : Continuous (fun v : Fin 20 → ℝ => lift8 (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) i j k) :=
    he (he (he (continuous_apply 12) (continuous_apply 13) k) (he (continuous_apply 14) (continuous_apply 15) k) j)
      (he (he (continuous_apply 16) (continuous_apply 17) k) (he (continuous_apply 18) (continuous_apply 19) k) j) i
  have hdP : Continuous decP := continuous_pi fun i => continuous_pi fun j => continuous_const.add (hl4 0 1 2 3 i j)
  have hdQ : Continuous decQ := continuous_pi fun j => continuous_pi fun k => continuous_const.add (hl4 4 5 6 7 j k)
  have hdR : Continuous decR := continuous_pi fun k => continuous_pi fun i => continuous_const.add (hl4 8 9 10 11 k i)
  refine (continuous_pi fun i => continuous_pi fun j => continuous_pi fun k => ?_).prodMk (hdP.prodMk (hdQ.prodMk hdR))
  exact ((hl8 i j k).add (((((continuous_apply j).comp ((continuous_apply i).comp hdP)).add
    ((continuous_apply k).comp ((continuous_apply j).comp hdQ))).add
    ((continuous_apply i).comp ((continuous_apply k).comp hdR))).div_const _)).sub continuous_const

theorem fullLedger_mapAtoms (g : CompactAutomorphism) (T : Triple) : fullLedger (mapAtoms g T) = fullLedger T :=
  Prod.ext (funext fun i => funext fun j => funext fun k => g.ledger_map (T f0) (T f1) (T f2) i j k)
    (Prod.ext (funext fun _ => funext fun _ => g.inner_map _ _)
      (Prod.ext (funext fun _ => funext fun _ => g.inner_map _ _) (funext fun _ => funext fun _ => g.inner_map _ _)))

theorem continuous_fullLedger : Continuous fullLedger := by
  have hent (a i : Fin 3) : Continuous (fun T : Triple => T a i) := (continuous_apply i).comp (continuous_apply a)
  have hj {f g : Triple → Albert} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => jordan (f x) (g x)) := by
    simpa only [Function.comp_def] using continuous_jordan.comp (hf.prodMk hg)
  have hi {f g : Triple → Albert} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => inner (f x) (g x)) := by
    simpa only [Function.comp_def] using continuous_native_inner.comp (hf.prodMk hg)
  have htr : Continuous (fun x : Albert => trace x) := by
    simpa only [Function.comp_def, inner_unit_right] using
      continuous_native_inner.comp (continuous_id'.prodMk (continuous_const : Continuous fun _ : Albert => (1 : Albert)))
  exact (continuous_pi fun i => continuous_pi fun j => continuous_pi fun k =>
      htr.comp (hj (hj (hent f0 i) (hent f1 j)) (hent f2 k))).prodMk
    ((continuous_pi fun i => continuous_pi fun j => hi (hent f0 i) (hent f1 j)).prodMk
      ((continuous_pi fun j => continuous_pi fun k => hi (hent f1 j) (hent f2 k)).prodMk
        (continuous_pi fun k => continuous_pi fun i => hi (hent f2 k) (hent f0 i))))

theorem continuous_phiOf : Continuous phiOf := by
  have hj {f g : Triple → Albert} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => jordan (f x) (g x)) := by
    simpa only [Function.comp_def] using continuous_jordan.comp (hf.prodMk hg)
  have hU {f g : Triple → Albert} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => U (f x) (g x)) := by
    have h1 := hj hf (hj hf hg); simpa only [U, two_smul] using (h1.fun_add h1).fun_sub (hj (hj hf hf) hg)
  have he (a : Fin 3) : Continuous (fun T : Triple => encoder (T a)) :=
    ((continuous_apply 2).comp (continuous_apply a)).fun_sub ((continuous_apply 0).comp (continuous_apply a))
  unfold phiOf phi
  simpa only [Function.comp_def] using continuous_native_inner.comp
    (((hU (he f0) (hU (he f1) (he f2))).fun_sub (hU (he f1) (hU (he f0) (he f2)))).prodMk (hU (he f2) (hj (he f0) (he f1))))

private def revTriple (T : Triple) : Triple := ![fun i => T 0 (Equiv.swap (0 : Fin 3) 2 i), T 1, T 2]

private def revLedger (L : Ledger54) : Ledger54 :=
  (fun i j k => L.1 (Equiv.swap (0 : Fin 3) 2 i) j k, fun i j => L.2.1 (Equiv.swap (0 : Fin 3) 2 i) j,
    L.2.2.1, fun k i => L.2.2.2 k (Equiv.swap (0 : Fin 3) 2 i))

private theorem fullLedger_revTriple (T : Triple) : fullLedger (revTriple T) = revLedger (fullLedger T) := by
  unfold fullLedger revLedger; rw [f_eq.1, f_eq.2.1, f_eq.2.2]; rfl

private def tau (b : Fin 20 → ℝ) : Fin 20 → ℝ := encode20 (revLedger (decode20 b))

private theorem revLedger_inDom {L : Ledger54} (hL : InDom L) : InDom (revLedger L) := by
  have hs : Equiv.swap (0 : Fin 3) 2 0 = 2 ∧ Equiv.swap (0 : Fin 3) 2 1 = 1 ∧ Equiv.swap (0 : Fin 3) 2 2 = 0 := by decide
  exact ⟨fun i => hL.pr _, fun j => by dsimp [revLedger]; rw [hs.1, hs.2.1, hs.2.2]; linarith [hL.pc j],
    hL.qr, hL.qc, fun k => by dsimp [revLedger]; rw [hs.1, hs.2.1, hs.2.2]; linarith [hL.rr k],
    fun i => hL.rc _, fun i j => hL.ck _ j,
    fun j k => by dsimp [revLedger]; rw [hs.1, hs.2.1, hs.2.2]; linarith [hL.ci j k], fun k i => hL.cj k _⟩

private theorem rowsOf_chartVec :
    ∃ rowsOf chartVec : (Fin 20 → ℝ) → (Fin 20 → ℝ),
      (∀ v r, rowsOf v r = decC v (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2) ∧
      (∀ v, chartVec (rowsOf v) = v) ∧ Continuous rowsOf := by
  let rowsOf (v : Fin 20 → ℝ) (r : Fin 20) : ℝ := decC v (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2
  let chartVec (c : Fin 20 → ℝ) : Fin 20 → ℝ :=
    ![c 0 + c 1 + c 2 - 1 / 3, c 3 + c 4 + c 5 - 1 / 3, c 8 + c 9 + c 10 - 1 / 3, c 11 + c 12 + c 13 - 1 / 3,
      c 0 + c 8 + c 16 - 1 / 3, c 1 + c 9 + c 17 - 1 / 3, c 3 + c 11 + c 18 - 1 / 3, c 4 + c 12 + c 19 - 1 / 3,
      c 0 + c 3 + c 6 - 1 / 3, c 8 + c 11 + c 14 - 1 / 3, c 1 + c 4 + c 7 - 1 / 3, c 9 + c 12 + c 15 - 1 / 3,
      c 0 - ((c 0 + c 1 + c 2) + (c 0 + c 8 + c 16) + (c 0 + c 3 + c 6)) / 3 + 2 / 9,
      c 1 - ((c 0 + c 1 + c 2) + (c 1 + c 9 + c 17) + (c 1 + c 4 + c 7)) / 3 + 2 / 9,
      c 3 - ((c 3 + c 4 + c 5) + (c 3 + c 11 + c 18) + (c 0 + c 3 + c 6)) / 3 + 2 / 9,
      c 4 - ((c 3 + c 4 + c 5) + (c 4 + c 12 + c 19) + (c 1 + c 4 + c 7)) / 3 + 2 / 9,
      c 8 - ((c 8 + c 9 + c 10) + (c 0 + c 8 + c 16) + (c 8 + c 11 + c 14)) / 3 + 2 / 9,
      c 9 - ((c 8 + c 9 + c 10) + (c 1 + c 9 + c 17) + (c 9 + c 12 + c 15)) / 3 + 2 / 9,
      c 11 - ((c 11 + c 12 + c 13) + (c 3 + c 11 + c 18) + (c 8 + c 11 + c 14)) / 3 + 2 / 9,
      c 12 - ((c 11 + c 12 + c 13) + (c 4 + c 12 + c 19) + (c 9 + c 12 + c 15)) / 3 + 2 / 9]
  refine ⟨rowsOf, chartVec, fun _ _ => rfl, fun v => ?_, continuous_pi fun r =>
    (continuous_apply (rowIndex r).2.2).comp ((continuous_apply (rowIndex r).2.1).comp
      ((continuous_apply (rowIndex r).1).comp (continuous_fst.comp continuous_decode20)))⟩
  have hD := dec20_inDom v
  have hP (i j : Fin 3) : decC v i j 0 + decC v i j 1 + decC v i j 2 = decP v i j := hD.ck i j
  have hQ (j k : Fin 3) : decC v 0 j k + decC v 1 j k + decC v 2 j k = decQ v j k := hD.ci j k
  have hR (k i : Fin 3) : decC v i 0 k + decC v i 1 k + decC v i 2 k = decR v k i := hD.cj k i
  funext m; fin_cases m <;>
    (dsimp [chartVec, rowsOf, rowIndex]; repeat (first | rw [hP] | rw [hQ] | rw [hR])
     simp [decC, decP, decQ, decR, lift8, lift4, ext3]; try ring)

private theorem exists_signed_sec (T : Triple) (hT : ∀ a, Frame (T a))
    (e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ)) (he : (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T)
    (hneg : phiOf T < -1 / 27) :
    ∃ W : Set (Fin 20 → ℝ), IsOpen W ∧ encode20 (fullLedger T) ∈ W ∧
      ∃ sec : (Fin 20 → ℝ) → Triple, ContinuousOn sec W ∧
        (∀ b ∈ W, ∀ a : Fin 3, Frame (sec b a)) ∧
        (∀ b ∈ W, encode20 (fullLedger (sec b)) = b) ∧
        (∀ b ∈ W, phiOf (sec b) < -1 / 27) := by
  obtain ⟨rowsOf, chartVec, hrows, hcv, hc_rows⟩ := rowsOf_chartVec
  have hd : HasStrictFDerivAt (rowLedger T) (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) 0 := he ▸ hasStrictFDerivAt_rowLedger T
  let Psi := hd.toOpenPartialHomeomorph (rowLedger T)
  have hcoe : (Psi : (Fin 20 → ℝ) → (Fin 20 → ℝ)) = rowLedger T := hd.toOpenPartialHomeomorph_coe
  let movedT (s : Fin 20 → ℝ) : Triple :=
    fun a => movedFrame contextDirection contextDirection_isJordanDerivation contextDirection_traceFree T a s
  have hm0 : movedT 0 = T := funext fun a => movedFrame_zero _ _ _ T a
  have hm_rows (s : Fin 20 → ℝ) : rowsOf (encode20 (fullLedger (movedT s))) = rowLedger T s := by
    funext r; rw [hrows]
    have hdL := congrArg (fun L : Ledger54 => L.1 (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2)
      (dec_enc _ (fullLedger_inDom (movedT s) fun a => movedFrame_frame _ _ _ T a (hT a) s))
    dsimp only [decode20] at hdL; rw [hdL]; unfold fullLedger; rw [f_eq.1, f_eq.2.1, f_eq.2.2]; rfl
  have hb0 : rowsOf (encode20 (fullLedger T)) = rowLedger T 0 := by simpa only [hm0] using hm_rows 0
  let W0 : Set (Fin 20 → ℝ) := rowsOf ⁻¹' Psi.target
  let sec (b : Fin 20 → ℝ) : Triple := movedT (Psi.symm (rowsOf b))
  have hcont0 : ContinuousOn sec W0 := continuousOn_pi' fun a => continuousOn_pi' fun i =>
    (continuous_movedFrame _ _ _ T a i).comp_continuousOn' (Psi.continuousOn_symm.comp' hc_rows.continuousOn fun _ hb => hb)
  refine ⟨W0 ∩ (fun b => phiOf (sec b)) ⁻¹' Set.Iio (-1 / 27),
    (continuous_phiOf.comp_continuousOn' hcont0).isOpen_inter_preimage (Psi.open_target.preimage hc_rows) isOpen_Iio,
    ⟨by show rowsOf _ ∈ Psi.target; rw [hb0]; exact hd.image_mem_toOpenPartialHomeomorph_target,
     by show phiOf (movedT (Psi.symm (rowsOf _))) < -1 / 27
        rw [hb0, show Psi.symm (rowLedger T 0) = 0 by have h := Psi.left_inv hd.mem_toOpenPartialHomeomorph_source; rwa [hcoe] at h, hm0]
        exact hneg⟩,
    sec, hcont0.mono Set.inter_subset_left,
    fun b _ a => movedFrame_frame _ _ _ T a (hT a) _,
    fun b hb => by dsimp [sec]; rw [← hcv (encode20 _), hm_rows, show rowLedger T (Psi.symm (rowsOf b)) = rowsOf b by have h := Psi.right_inv hb.1; rwa [hcoe] at h, hcv],
    fun _ hb => hb.2⟩

private theorem tau_flat : tau (encode20 (fullLedger flatBase)) = encode20 (fullLedger flatBase) := by
  rw [tau, dec_enc _ (fullLedger_inDom flatBase flatBase_frames), fullLedger_flatBase]; rfl

private theorem continuous_tau : Continuous tau :=
  continuous_encode20.comp ((by unfold revLedger; fun_prop : Continuous revLedger).comp continuous_decode20)

private theorem frame_revTriple (T : Triple) (hT : ∀ a, Frame (T a)) (a : Fin 3) : Frame (revTriple T a) := by
  fin_cases a
  · refine ⟨fun i => (hT 0).trace_one _, fun i => (hT 0).idempotent _,
      fun i j hij => (hT 0).orthogonal _ _ ((Equiv.swap (0 : Fin 3) 2).injective.ne hij), ?_⟩
    show T 0 (Equiv.swap 0 2 0) + T 0 (Equiv.swap 0 2 1) + T 0 (Equiv.swap 0 2 2) = 1
    rw [show Equiv.swap (0 : Fin 3) 2 0 = 2 by decide, show Equiv.swap (0 : Fin 3) 2 1 = 1 by decide,
      show Equiv.swap (0 : Fin 3) 2 2 = 0 by decide, ← (hT 0).sum_unit]; abel
  · exact hT 1
  · exact hT 2

private theorem continuous_revTriple : Continuous revTriple :=
  continuous_pi fun a => continuous_pi fun i => by fin_cases a <;> dsimp only [revTriple] <;> fun_prop

private theorem phiOf_revTriple (T : Triple) : phiOf (revTriple T) = -phiOf T := by
  unfold phiOf; rw [f_eq.1, f_eq.2.1, f_eq.2.2]
  have h0 : encoder (revTriple T 0) = (-1 : ℝ) • encoder (T 0) := by
    change T 0 (Equiv.swap 0 2 2) - T 0 (Equiv.swap 0 2 0) = (-1 : ℝ) • (T 0 2 - T 0 0)
    rw [show Equiv.swap (0 : Fin 3) 2 2 = 0 by decide, show Equiv.swap (0 : Fin 3) 2 0 = 2 by decide, neg_one_smul]; abel
  simp only [h0, show revTriple T 1 = T 1 from rfl, show revTriple T 2 = T 2 from rfl, phi_smul_first]; ring

private theorem sections_core :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧ (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (fullLedger (secPos b)) = b) ∧ (∀ b ∈ V, encode20 (fullLedger (secNeg b)) = b) ∧
        (∀ b ∈ V, fullLedger (secPos b) = decode20 b) ∧ (∀ b ∈ V, fullLedger (secNeg b) = decode20 b) ∧
        (∀ b ∈ V, 1 / 27 < phiOf (secPos b)) ∧ (∀ b ∈ V, phiOf (secNeg b) < -1 / 27) := by
  obtain ⟨e, he⟩ := Glennie.Compact.PairNormNearby.native_rank20_strict_with_inverse
  have hv3 {α : Type} (x y z : α) : ![x, y, z] 0 = x ∧ ![x, y, z] 1 = y ∧ ![x, y, z] 2 = z := ⟨rfl, rfl, rfl⟩
  have hneg : phiOf flatBase < -1 / 27 := by
    rw [phiOf, f_eq.1, f_eq.2.1, f_eq.2.2, flatBase_eq_frames, (hv3 _ _ _).1, (hv3 _ _ _).2.1, (hv3 _ _ _).2.2, flat_phi]; norm_num
  obtain ⟨W, hWopen, hmemW, sec, hcont, hframes, hledger, hsign⟩ :=
    exists_signed_sec flatBase flatBase_frames e (he.trans (congrArg rowLedgerDeriv flatBase_eq_frames.symm)) hneg
  have htau_enc (L : Ledger54) (hL : InDom L) : tau (encode20 L) = encode20 (revLedger L) := by rw [tau, dec_enc L hL]
  have hrr (L : Ledger54) : revLedger (revLedger L) = L := by rcases L with ⟨_, _, _, _⟩; simp [revLedger]
  have htau_tau (b : Fin 20 → ℝ) : tau (tau b) = b := by
    conv_lhs => rw [tau, tau]
    rw [dec_enc _ (revLedger_inDom (dec20_inDom b)), hrr, enc20_dec20]
  let V := W ∩ tau ⁻¹' W
  let secPos (b : Fin 20 → ℝ) : Triple := revTriple (sec (tau b))
  have hcp (b : Fin 20 → ℝ) (hb : b ∈ V) : encode20 (fullLedger (secPos b)) = b := by
    dsimp only [secPos]; rw [fullLedger_revTriple, ← htau_enc _ (fullLedger_inDom _ (hframes (tau b) hb.2)), hledger (tau b) hb.2, htau_tau]
  have hmemV {L : Type} (f : L → L) (U : Set L) (x : L) (hx : x ∈ U) (hf : f x = x) : x ∈ U ∩ f ⁻¹' U :=
    ⟨hx, by show f x ∈ U; rwa [hf]⟩
  refine ⟨V, hWopen.inter (hWopen.preimage continuous_tau), hmemV tau W _ hmemW tau_flat,
    secPos, sec,
    continuous_revTriple.comp_continuousOn' (hcont.comp' continuous_tau.continuousOn fun _ hb => hb.2),
    hcont.mono Set.inter_subset_left,
    fun b hb => frame_revTriple _ (hframes (tau b) hb.2), fun b hb => hframes b hb.1,
    hcp, fun b hb => hledger b hb.1,
    fun b hb => (dec_enc _ (fullLedger_inDom _ (frame_revTriple _ (hframes (tau b) hb.2)))).symm.trans (congrArg decode20 (hcp b hb)),
    fun b hb => (dec_enc _ (fullLedger_inDom _ (hframes b hb.1))).symm.trans (congrArg decode20 (hledger b hb.1)),
    fun b hb => by show 1 / 27 < phiOf (revTriple (sec (tau b))); rw [phiOf_revTriple]; linarith [hsign (tau b) hb.2],
    fun b hb => hsign b hb.1⟩

end ChartAndSections

theorem phiOf_mapAtoms_sub (g : CompactAutomorphism) (T : Triple) :
    phiOf (mapAtoms g T) = phiOf T := by
  have hm (v : Fin 3) : mapAtoms g T v = fun i => g.equiv (T v i) := rfl
  simp only [phiOf, hm, g.encoder_map, g.phi_map]

theorem near_flat_scalar_margin :
    ∃ V : Set Ledger54, IsOpen V ∧ fullLedger flatBase ∈ V ∧
      ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) → fullLedger T ∈ V →
        1 / 27 < |phiOf T| := by
  obtain ⟨V0, hV0, hb0, _, secNeg, _, _, _, hfN, _, _, _, hlN, _, hpN⟩ := sections_core
  refine ⟨LBox ∩ encode20 ⁻¹' V0, isOpen_LBox.inter (hV0.preimage continuous_encode20),
    ⟨flatBase_mem_LBox, hb0⟩, fun T hT ⟨hTL, hbV⟩ => ?_⟩
  let b := encode20 (fullLedger T)
  have hSL : fullLedger (secNeg b) = fullLedger T := (hlN b hbV).trans (dec_enc _ (fullLedger_inDom T hT))
  have hSne : Glennie.Compact.PairNormNearby.phiT (secNeg b) ≠ 0 := by rw [phiT_eq]; linarith [hpN b hbV]
  have hbox : ∀ i j : Fin 3, |(Glennie.Compact.PairNormNearby.led54 (secNeg b)).2.1 i j - 1 / 3| < 1 / 50 := by
    rw [led54_eq, hSL]; exact hTL
  have hsq := (Glennie.Compact.PairNormNearby.nearby_core (secNeg b) T (hfN b hbV) hT hbox (by rw [led54_eq, led54_eq, hSL]) hSne).1
  rw [phiT_eq, phiT_eq] at hsq
  have habs : |phiOf (secNeg b)| = |phiOf T| := by rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]; exact congrArg Real.sqrt hsq
  rw [← habs, abs_of_neg (by linarith [hpN b hbV])]; linarith [hpN b hbV]

theorem nearby_fibres_two_orbits :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secPos b a i)) V ∧
        ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secNeg b a i)) V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (fullLedger (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (fullLedger (secNeg b)) = b) ∧
        (∀ b ∈ V, fullLedger (secPos b) = decode20 b) ∧
        (∀ b ∈ V, fullLedger (secNeg b) = decode20 b) ∧
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) ∧
        (∀ b ∈ V, fibre54 b = autOrbit (secNeg b) ∪ autOrbit (secPos b)) ∧
        (∀ b ∈ V, Disjoint (autOrbit (secNeg b)) (autOrbit (secPos b))) ∧
        (∀ b ∈ V, fibre20 b = fibre54 b) := by
  obtain ⟨V0, hV0, hb0, secPos, secNeg, hcP, hcN, hfP, hfN, heP, heN, hlP, hlN, hpP, hpN⟩ := sections_core
  obtain ⟨V1, hV1, hb1, hrig⟩ := nearby_sign_rigidity
  obtain ⟨V2, hV2, hb2, hmarg⟩ := near_flat_scalar_margin
  have hcoord : Continuous (fun T : Triple => fun a i => Albert.coordinateEquiv (T a i)) :=
    continuous_pi fun a => continuous_pi fun i =>
      Albert.coordinateLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp ((continuous_apply i).comp (continuous_apply a))
  have hbL : fullLedger (secNeg (encode20 (fullLedger flatBase))) = fullLedger flatBase :=
    (hlN _ hb0).trans (dec_enc _ (fullLedger_inDom flatBase flatBase_frames))
  let V := V0 ∩ (fun b => fullLedger (secNeg b)) ⁻¹' (V1 ∩ V2)
  refine ⟨V, (continuous_fullLedger.comp_continuousOn hcN).isOpen_inter_preimage hV0 (hV1.inter hV2),
    ⟨hb0, by show fullLedger (secNeg _) ∈ V1 ∩ V2; rw [hbL]; exact ⟨hb1, hb2⟩⟩,
    secPos, secNeg,
    hcoord.comp_continuousOn (hcP.mono Set.inter_subset_left),
    hcoord.comp_continuousOn (hcN.mono Set.inter_subset_left),
    fun b hb => hfP b hb.1, fun b hb => hfN b hb.1,
    fun b hb => heP b hb.1, fun b hb => heN b hb.1,
    fun b hb => hlP b hb.1, fun b hb => hlN b hb.1,
    fun b hb => by linarith [hpP b hb.1], fun b hb => by linarith [hpN b hb.1], ?_, ?_, ?_⟩
  · intro b hb; refine Set.Subset.antisymm ?_ ?_
    · rintro T ⟨hT, hTL⟩
      have hTeqN : fullLedger T = fullLedger (secNeg b) := hTL.trans (hlN b hb.1).symm
      have hTeqP : fullLedger T = fullLedger (secPos b) := hTL.trans (hlP b hb.1).symm
      have hnz := hmarg T hT (hTeqN.symm ▸ hb.2.2)
      rcases lt_trichotomy (phiOf T) 0 with hneg | hz | hpos
      · exact Or.inl (hrig T (secNeg b) hT (hfN b hb.1) (hTeqN.symm ▸ hb.2.1) hTeqN (Or.inl ⟨hneg, by linarith [hpN b hb.1]⟩))
      · exfalso; rw [hz, abs_zero] at hnz; norm_num at hnz
      · exact Or.inr (hrig T (secPos b) hT (hfP b hb.1) (hTeqN.symm ▸ hb.2.1) hTeqP (Or.inr ⟨hpos, by linarith [hpP b hb.1]⟩))
    · rintro T (⟨g, rfl⟩ | ⟨g, rfl⟩)
      · exact ⟨fun a => g.map_frame _ (hfN b hb.1 a), by rw [fullLedger_mapAtoms, hlN b hb.1]⟩
      · exact ⟨fun a => g.map_frame _ (hfP b hb.1 a), by rw [fullLedger_mapAtoms, hlP b hb.1]⟩
  · intro b hb; rw [Set.disjoint_left]; rintro T ⟨g, rfl⟩ ⟨k, hk⟩
    have := phiOf_mapAtoms_sub g (secNeg b); have := hk ▸ phiOf_mapAtoms_sub k (secPos b)
    linarith [hpN b hb.1, hpP b hb.1]
  · intro b hb; refine Set.Subset.antisymm (fun T ⟨hT, hTb⟩ => ⟨hT, hTb ▸ (dec_enc _ (fullLedger_inDom T hT)).symm⟩) ?_
    rintro T ⟨hT, hTb⟩; exact ⟨hT, by rw [hTb, ← hlN b hb.1, heN b hb.1]⟩

private theorem autOrbit_trans {A B C : Triple} (hBA : B ∈ autOrbit A) (hCA : C ∈ autOrbit A) :
    C ∈ autOrbit B := by
  obtain ⟨g, rfl⟩ := hBA; obtain ⟨h, rfl⟩ := hCA
  refine ⟨h.comp g.symm, funext fun a => funext fun i => ?_⟩
  change h.equiv (g.equiv.symm (g.equiv (A a i))) = h.equiv (A a i)
  rw [g.equiv.symm_apply_apply]

theorem local_q26_score_orbit_test :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∀ T S : Triple, (∀ a, Frame (T a)) → (∀ a, Frame (S a)) →
        encode20 (fullLedger T) ∈ V →
        score T ≠ 0 ∧
        ((∃ k : CompactAutomorphism, mapAtoms k S = T) ↔
          q26 T = q26 S ∧
          ((score T < 0 ∧ score S < 0) ∨ (0 < score T ∧ 0 < score S))) := by
  obtain ⟨V, ho, hb, secPos, secNeg, _, _, _, _, _, _, _, _, hpP, hpN, hcov, _, h20⟩ :=
    nearby_fibres_two_orbits
  refine ⟨V, ho, hb, fun T S hT hS hbT => ?_⟩
  let b := encode20 (fullLedger T)
  have hTorb : T ∈ autOrbit (secNeg b) ∨ T ∈ autOrbit (secPos b) := by
    change T ∈ autOrbit (secNeg b) ∪ autOrbit (secPos b)
    rw [← hcov b hbT, ← h20 b hbT]; exact ⟨hT, rfl⟩
  have hsN {X : Triple} : X ∈ autOrbit (secNeg b) → score X < 0 := fun ⟨g, hg⟩ => by
    rw [← hg, score_eq_two_phi, phiOf_mapAtoms_sub]; linarith [hpN b hbT]
  have hsP {X : Triple} : X ∈ autOrbit (secPos b) → 0 < score X := fun ⟨g, hg⟩ => by
    rw [← hg, score_eq_two_phi, phiOf_mapAtoms_sub]; linarith [hpP b hbT]
  have hsT : score T ≠ 0 := hTorb.elim (fun h => (hsN h).ne) (fun h => (hsP h).ne')
  refine ⟨hsT, ⟨?_, ?_⟩⟩
  · rintro ⟨k, hk⟩
    have hL : fullLedger T = fullLedger S := by rw [← hk, fullLedger_mapAtoms]
    have hsc : score T = score S := by rw [← hk, score_eq_two_phi, score_eq_two_phi, phiOf_mapAtoms_sub]
    refine ⟨(q26_eq_iff_fullLedger_eq T S hT hS).mpr hL, ?_⟩
    rcases lt_trichotomy (score T) 0 with hn | hz | hp
    · exact Or.inl ⟨hn, hsc ▸ hn⟩
    · exact absurd hz hsT
    · exact Or.inr ⟨hp, hsc ▸ hp⟩
  · rintro ⟨hq, hsign⟩
    have hL := (q26_eq_iff_fullLedger_eq T S hT hS).mp hq
    have hSorb : S ∈ autOrbit (secNeg b) ∨ S ∈ autOrbit (secPos b) := by
      change S ∈ autOrbit (secNeg b) ∪ autOrbit (secPos b)
      rw [← hcov b hbT, ← h20 b hbT]; exact ⟨hS, by rw [← hL]⟩
    rcases hTorb with hTN | hTP <;> rcases hSorb with hSN | hSP
    · exact autOrbit_trans hSN hTN
    · rcases hsign with h | h <;> linarith [hsN hTN, hsP hSP]
    · rcases hsign with h | h <;> linarith [hsP hTP, hsN hSN]
    · exact autOrbit_trans hSP hTP

private theorem contOn_of_coord {f : (Fin 20 → ℝ) → Triple} {V : Set (Fin 20 → ℝ)}
    (hf : ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (f b a i)) V) :
    ContinuousOn f V := by
  have hback : Continuous (fun c : Fin 3 → Fin 3 → Albert.Coordinates =>
      (fun a i => Albert.coordinateLinearEquiv.symm (c a i) : Triple)) :=
    continuous_pi fun a => continuous_pi fun i =>
      Albert.coordinateLinearEquiv.symm.toLinearMap.continuous_of_finiteDimensional.comp
        ((continuous_apply i).comp (continuous_apply a))
  exact hback.comp_continuousOn hf

theorem compact_local_phi_margin :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∀ K : Set V, IsCompact K →
        ∃ m > 0, ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) →
          ∀ hb : encode20 (fullLedger T) ∈ V,
            (⟨encode20 (fullLedger T), hb⟩ : V) ∈ K →
              m ≤ |phiOf T| := by
  obtain ⟨V, ho, hb, p, n, hcp, hcn, _, _, _, _, _, _, hpP, hpN, hcov, _, h20⟩ := nearby_fibres_two_orbits
  refine ⟨V, ho, hb, fun K hK => ?_⟩
  have hmin (s : (Fin 20 → ℝ) → Triple) (hs : ContinuousOn (fun b a i => Albert.coordinateEquiv (s b a i)) V)
      (hne : ∀ b : V, phiOf (s b.1) ≠ 0) : ∃ m > 0, ∀ b ∈ K, m ≤ |phiOf (s b.1)| :=
    hK.exists_forall_le' ((by simpa only [Function.comp_def, Set.domRestrict_apply] using
      (continuous_phiOf.comp (contOn_of_coord hs).domRestrict).abs : Continuous fun b : V => |phiOf (s b.1)|).continuousOn)
      fun b _ => abs_pos.mpr (hne b)
  obtain ⟨mp, hmp, hbp⟩ := hmin p hcp fun b => (hpP b.1 b.2).ne'
  obtain ⟨mn, hmn, hbn⟩ := hmin n hcn fun b => (hpN b.1 b.2).ne
  refine ⟨min mp mn, lt_min hmp hmn, fun T hT hbT hTK => ?_⟩
  have hTorb : T ∈ autOrbit (n (encode20 (fullLedger T))) ∨ T ∈ autOrbit (p (encode20 (fullLedger T))) := by
    change T ∈ autOrbit _ ∪ autOrbit _; rw [← hcov _ hbT, ← h20 _ hbT]; exact ⟨hT, rfl⟩
  rcases hTorb with ⟨g, hg⟩ | ⟨g, hg⟩
  · rw [← hg, phiOf_mapAtoms_sub]; exact (min_le_right mp mn).trans (hbn ⟨_, hbT⟩ hTK)
  · rw [← hg, phiOf_mapAtoms_sub]; exact (min_le_left mp mn).trans (hbp ⟨_, hbT⟩ hTK)

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

private theorem weightedScore_err {T : Triple} {noisy : Readouts} {ε : ℝ}
    (h : ErrorsAtMost noisy (exactReadouts T) ε) :
    |weightedScore noisy - 2 * phiOf T| ≤ 12 * ε := by
  have hex : weightedScore (exactReadouts T) = 2 * phiOf T := by
    rw [← score_eq_two_phi]
    simp only [weightedScore, exactReadouts, score, delta, contrast, inner_sub_right, rawPlus, rawMinus]
    ring
  rw [← hex]
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  rw [abs_le] at h0 h1 h2 h3 h4 h5 ⊢
  dsimp only [weightedScore]; constructor <;> linarith

theorem signed_readout_margin (T : Triple) (noisy : Readouts) (ε : ℝ)
    (_hε : 0 ≤ ε) (h : ErrorsAtMost noisy (exactReadouts T) ε)
    (hm : 12 * ε < |weightedScore noisy|) :
    (weightedScore noisy < 0 ∧ phiOf T < 0) ∨
    (0 < weightedScore noisy ∧ 0 < phiOf T) := by
  obtain ⟨hl, hu⟩ := abs_le.mp (weightedScore_err h)
  rcases le_total 0 (weightedScore noisy) with hp | hn
  · rw [abs_of_nonneg hp] at hm; exact Or.inr ⟨by linarith, by linarith⟩
  · rw [abs_of_nonpos hn] at hm; exact Or.inl ⟨by linarith, by linarith⟩

def nA (x : Albert) : ℝ := Real.sqrt (inner x x)

private theorem nA_eq_norm (x : Albert) : nA x = ‖x‖ := by
  rw [nA, ← Glennie.native_norm_sq, Real.sqrt_sq (norm_nonneg x)]

theorem compact_feasible_element_recovery :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secPos b a i)) V ∧
        ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secNeg b a i)) V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (fullLedger (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (fullLedger (secNeg b)) = b) ∧
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) ∧
        (∀ K : Set V, IsCompact K → ∀ ζ : ℝ, 0 < ζ →
          ∃ η > 0, ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) →
            ∀ hb : encode20 (fullLedger T) ∈ V,
              (⟨encode20 (fullLedger T), hb⟩ : V) ∈ K →
              ∀ b : V, b ∈ K →
                dist (⟨encode20 (fullLedger T), hb⟩ : V) b < η →
                  ∃ g : CompactAutomorphism, ∀ a i : Fin 3,
                    nA (T a i - g.equiv
                      ((if 0 < phiOf T then secPos b.1 else secNeg b.1) a i)) < ζ) := by
  obtain ⟨V, ho, hb, p, n, hcp, hcn, hfp, hfn, hep, hen, _, _, hpp, hnn, hcov, _, h20⟩ :=
    nearby_fibres_two_orbits
  refine ⟨V, ho, hb, p, n, hcp, hcn, hfp, hfn, hep, hen, hpp, hnn, fun K hK ζ hζ => ?_⟩
  obtain ⟨ηp, hηp, hup⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous (contOn_of_coord hcp).domRestrict.continuousOn) ζ hζ
  obtain ⟨ηn, hηn, hun⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous (contOn_of_coord hcn).domRestrict.continuousOn) ζ hζ
  refine ⟨min ηp ηn, lt_min hηp hηn, fun T hT hbT hTK b hbK hdist => ?_⟩
  let b0 : V := ⟨encode20 (fullLedger T), hbT⟩
  have hTorb : T ∈ autOrbit (n b0.1) ∨ T ∈ autOrbit (p b0.1) := by
    change T ∈ autOrbit _ ∪ autOrbit _
    rw [← hcov _ hbT, ← h20 _ hbT]; exact ⟨hT, rfl⟩
  have hnorm_aut (g : CompactAutomorphism) (X Y : Triple) (a i : Fin 3) :
      nA (g.equiv (X a i) - g.equiv (Y a i)) ≤ dist X Y := by
    rw [← map_sub, nA, g.inner_map, ← nA, nA_eq_norm, dist_eq_norm]
    exact (norm_le_pi_norm ((X - Y) a) i).trans (norm_le_pi_norm (X - Y) a)
  by_cases hp : 0 < phiOf T
  · rcases hTorb with ⟨g, hg⟩ | ⟨g, hg⟩
    · exfalso; rw [← hg, phiOf_mapAtoms_sub] at hp; linarith [hnn b0.1 hbT]
    · refine ⟨g, fun a i => ?_⟩
      simp only [hp, ↓reduceIte]; rw [← hg]
      exact (hnorm_aut g (p b0.1) (p b.1) a i).trans_lt
        (hup b0 hTK b hbK (hdist.trans_le (min_le_left _ _)))
  · rcases hTorb with ⟨g, hg⟩ | ⟨g, hg⟩
    · refine ⟨g, fun a i => ?_⟩
      simp only [hp, ↓reduceIte]; rw [← hg]
      exact (hnorm_aut g (n b0.1) (n b.1) a i).trans_lt
        (hun b0 hTK b hbK (hdist.trans_le (min_le_right _ _)))
    · exfalso; rw [← hg, phiOf_mapAtoms_sub] at hp; exact hp (hpp b0.1 hbT)

theorem compact_noisy_feasible_element_recovery :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secPos b a i)) V ∧
        ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secNeg b a i)) V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (fullLedger (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (fullLedger (secNeg b)) = b) ∧
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) ∧
        (∀ K : Set V, IsCompact K → ∀ ζ : ℝ, 0 < ζ →
          ∃ η > 0, ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) →
            ∀ hb : encode20 (fullLedger T) ∈ V,
              (⟨encode20 (fullLedger T), hb⟩ : V) ∈ K →
              ∀ b : V, b ∈ K →
                dist (⟨encode20 (fullLedger T), hb⟩ : V) b < η →
                  ∀ noisy : Readouts, ∀ ε : ℝ, 0 ≤ ε →
                    ErrorsAtMost noisy (exactReadouts T) ε →
                    12 * ε < |weightedScore noisy| →
                    ∃ g : CompactAutomorphism, ∀ a i : Fin 3,
                      nA (T a i - g.equiv
                        ((if 0 < weightedScore noisy then secPos b.1
                          else secNeg b.1) a i)) < ζ) := by
  obtain ⟨V, ho, hb, p, n, hcp, hcn, hfp, hfn, hep, hen, hpp, hpn, hrec⟩ :=
    compact_feasible_element_recovery
  refine ⟨V, ho, hb, p, n, hcp, hcn, hfp, hfn, hep, hen, hpp, hpn, fun K hK ζ hζ => ?_⟩
  obtain ⟨η, hη, hrecover⟩ := hrec K hK ζ hζ
  refine ⟨η, hη, fun T hT hbT hTK b hbK hdist noisy ε hε herr hm => ?_⟩
  obtain ⟨g, hg⟩ := hrecover T hT hbT hTK b hbK hdist
  refine ⟨g, ?_⟩
  rcases signed_readout_margin T noisy ε hε herr hm with hn | hp
  · simpa only [ite_eq_right_iff.mpr fun h => absurd h (not_lt_of_ge hn.1.le),
      ite_eq_right_iff.mpr fun h => absurd h (not_lt_of_ge hn.2.le)] using hg
  · simpa only [ite_eq_left_iff.mpr fun h => absurd hp.1 h,
      ite_eq_left_iff.mpr fun h => absurd hp.2 h] using hg

def noisyPhi (r : Readouts) : ℝ := weightedScore r / (Nat.cast 2 : ℝ)

theorem six_readout_displaced_generation
    (T : Triple) (noisy : Readouts) (x' y' z' : Albert)
    (ε ξ R δ : ℝ) (_hξ : 0 ≤ ξ) (hR : 0 ≤ R)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hallowance : 6 * ε ≤ ξ)
    (hx : nA (encoder (T f0)) ≤ R) (hy : nA (encoder (T f1)) ≤ R)
    (hz : nA (encoder (T f2)) ≤ R)
    (hx' : nA x' ≤ R) (hy' : nA y' ≤ R) (hz' : nA z' ≤ R)
    (hdx : nA (encoder (T f0) - x') ≤ δ)
    (hdy : nA (encoder (T f1) - y') ≤ δ)
    (hdz : nA (encoder (T f2) - z') ≤ δ)
    (hmargin : 18 * R^8 * δ < |noisyPhi noisy| - ξ) :
    ((noisyPhi noisy < 0 ∧ phi x' y' z' < 0) ∨
      (0 < noisyPhi noisy ∧ 0 < phi x' y' z')) ∧
    (∀ K : Submodule ℝ Albert, (1 : Albert) ∈ K →
      (∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) →
      x' ∈ K → y' ∈ K → z' ∈ K → K = ⊤) ∧
    (∀ g : CompactAutomorphism,
      g.equiv x' = x' → g.equiv y' = y' → g.equiv z' = z' →
      g.equiv = LinearEquiv.refl ℝ Albert) := by
  simp only [nA_eq_norm] at hx hy hz hx' hy' hz' hdx hdy hdz
  have herr : |noisyPhi noisy - phiOf T| ≤ ξ := by
    obtain ⟨hl, hu⟩ := abs_le.mp (weightedScore_err hreadout)
    rw [abs_le]; dsimp [noisyPhi]; constructor <;> linarith
  have hdisp := Glennie.Compact.NativeNormKernel.phi_displacement_18
    (encoder (T f0)) (encoder (T f1)) (encoder (T f2)) x' y' z' R δ hR
    hx hy hz hx' hy' hz' hdx hdy hdz
  obtain ⟨el, eu⟩ := abs_le.mp herr
  obtain ⟨dl, du⟩ := abs_le.mp hdisp
  have hsign : (noisyPhi noisy < 0 ∧ phi x' y' z' < 0) ∨ (0 < noisyPhi noisy ∧ 0 < phi x' y' z') := by
    rcases le_total 0 (noisyPhi noisy) with hp | hn
    · rw [abs_of_nonneg hp] at hmargin; exact Or.inr ⟨by linarith, by dsimp [phiOf] at eu; linarith⟩
    · rw [abs_of_nonpos hn] at hmargin; exact Or.inl ⟨by linarith, by dsimp [phiOf] at el; linarith⟩
  have hne : phi x' y' z' ≠ 0 := hsign.elim (fun h => h.2.ne) (fun h => h.2.ne')
  obtain ⟨hgen, hstab, _⟩ := phi_nonzero_generation_stabilizer x' y' z' hne
  exact ⟨hsign, hgen, hstab⟩

def diagonalNProduct {n : ℕ} (a b : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp (Nat.cast 2 : ENNReal) (fun i => a i * b i)

theorem diagonalN_defect_response_radius {n : ℕ}
    (f : Albert →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : ∀ x : Albert, ‖f x‖ = nA x)
    (μ R : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤
        μ * nA a * nA b)
    (x y z : Albert) (hx : nA x ≤ R) (hy : nA y ≤ R)
    (hz : nA z ≤ R) :
    |phi x y z| ≤ 38 * μ * R^9 := by
  simp only [nA_eq_norm] at hf hdef hx hy hz
  let jE : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toFun a := { toFun := diagonalNProduct a
                   map_add' b c := by ext i; exact mul_add (a i) (b i) (c i)
                   map_smul' r b := by ext i; exact mul_left_comm (a i) r (b i) }
      map_add' a b := LinearMap.ext fun c => by ext i; exact add_mul (a i) (b i) (c i)
      map_smul' r a := LinearMap.ext fun c => by ext i; exact mul_assoc r (a i) (c i) }
  have hE (a b : EuclideanSpace ℝ (Fin n)) : ‖jE a b‖ ≤ ‖a‖ * ‖b‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq b, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have ha : (a i) ^ 2 ≤ ‖a‖ ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        (sq_le_sq₀ (norm_nonneg (a i)) (norm_nonneg a)).mpr (PiLp.norm_apply_le a i)
    change (a i * b i) ^ 2 ≤ ‖a‖ ^ 2 * (b i) ^ 2
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right ha (sq_nonneg _)
  have hUE (a b : EuclideanSpace ℝ (Fin n)) : ‖Glennie.Compact.NativeNormKernel.QOp jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖ := by
    have hsand : Glennie.Compact.NativeNormKernel.QOp jE a b = jE a (jE a b) := by
      ext i; change 2 * (a i * (a i * b i)) - (a i * a i) * b i = a i * (a i * b i); ring
    rw [hsand]
    exact (hE a _).trans ((mul_le_mul_of_nonneg_left (hE a b) (norm_nonneg a)).trans_eq (by ring))
  let ρ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun a i := a i, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  let τ : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun a := ∑ i, a i, map_add' _ _ := Finset.sum_add_distrib, map_smul' _ _ := by simp [Finset.mul_sum] }
  exact Glennie.Compact.NativeNormKernel.native_compatible_defect_response jE ⟨f, hf⟩ hE hUE ρ τ
    (fun a b => funext fun i => by change a i * b i = (1 / 2 : ℝ) * (a i * b i + b i * a i); ring)
    (fun a b => Finset.sum_congr rfl fun i _ => mul_comm (b i) (a i))
    (fun a b => congrArg τ (mul_comm a b))
    μ R hμ hR hdef x y z hx hy hz

private theorem defect_lower_of_phi_bound {T : Triple} (_hT : ∀ a : Fin 3, Frame (T a))
    {noisy : Readouts} {ε μ : ℝ} (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hphi : |phiOf T| ≤ 38 * μ * (Real.sqrt 2) ^ 9) :
    (|weightedScore noisy| - 12 * ε) / (1216 * Real.sqrt 2) ≤ μ := by
  have hpow : (Real.sqrt (2 : ℝ)) ^ 9 = 16 * Real.sqrt 2 := by
    calc (Real.sqrt (2 : ℝ)) ^ 9 = ((Real.sqrt (2 : ℝ)) ^ 2) ^ 4 * Real.sqrt 2 := by ring
      _ = 16 * Real.sqrt 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
  rw [hpow] at hphi
  have hws : |weightedScore noisy| - 12 * ε ≤ 2 * |phiOf T| := by
    have he := weightedScore_err hreadout
    have htri := abs_add_le (weightedScore noisy - 2 * phiOf T) (2 * phiOf T)
    rw [sub_add_cancel, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
    linarith
  have hr : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

private theorem frame_encoder_nA (p : Fin 3 → Albert) (hp : Frame p) :
    nA (encoder p) ≤ Real.sqrt 2 := by
  rw [nA, frame_encoder_norm p hp]

theorem frame_noisy_diagonalN_defect_lower {n : ℕ}
    (f : Albert →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : ∀ x : Albert, ‖f x‖ = nA x)
    (T : Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤
        μ * nA a * nA b) :
    (|weightedScore noisy| - 12 * ε) / (1216 * Real.sqrt 2) ≤ μ :=
  defect_lower_of_phi_bound hT hreadout
    (diagonalN_defect_response_radius f hf μ (Real.sqrt 2) hμ (Real.sqrt_nonneg 2) hdef
      _ _ _ (frame_encoder_nA _ (hT f0)) (frame_encoder_nA _ (hT f1)) (frame_encoder_nA _ (hT f2)))

theorem frame_noisy_represented_defect_lower
    {E N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedRing N] [NormedAlgebra ℝ N]
    (jE : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (f : Albert →ₗ[ℝ] E) (hf : ∀ x : Albert, ‖f x‖ = nA x)
    (ρ : E →ₗᵢ[ℝ] N) (τ : N →ₗ[ℝ] ℝ)
    (hj : ∀ a b : E, ρ (jE a b) =
      (1 / 2 : ℝ) • (ρ a * ρ b + ρ b * ρ a))
    (hB : ∀ a b : E, Inner.inner ℝ a b = τ (ρ a * ρ b))
    (hcyclic : ∀ a b : N, τ (a * b) = τ (b * a))
    (T : Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - jE (f a) (f b)‖ ≤ μ * nA a * nA b) :
    (|weightedScore noisy| - 12 * ε) / (1216 * Real.sqrt 2) ≤ μ := by
  obtain ⟨hE, hUE⟩ := Glennie.Compact.NativeNormKernel.represented_norms jE ρ hj
  have hf' (x : Albert) : ‖f x‖ = ‖x‖ := (hf x).trans (nA_eq_norm x)
  have hdef' (a b : Albert) : ‖f (jordan a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖ := by
    simpa only [nA_eq_norm] using hdef a b
  have hfn (v : Fin 3) : ‖encoder (T v)‖ ≤ Real.sqrt 2 := by
    rw [← nA_eq_norm]; exact frame_encoder_nA _ (hT v)
  exact defect_lower_of_phi_bound hT hreadout
    (Glennie.Compact.NativeNormKernel.native_compatible_defect_response jE ⟨f, hf'⟩ hE hUE
      ρ.toLinearMap τ hj hB hcyclic μ (Real.sqrt 2) hμ (Real.sqrt_nonneg 2) hdef'
      _ _ _ (hfn f0) (hfn f1) (hfn f2))

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
def generated {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Submodule ℝ E :=
  sInf {K : Submodule ℝ E | e ∈ K ∧ (∀ i, a i ∈ K) ∧
    (∀ x ∈ K, ∀ y ∈ K, j x y ∈ K)}
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

private theorem wordValues_eq_source {E : Type*} (e : E) (a : Fin 3 → E) (j : E → E → E) (i : Fin 27) :
    wordValues e a j i = Glennie.Compact.NativeWordTableR01.eval e a j (Glennie.Compact.NativeWordTableR01.words i) := by
  fin_cases i <;> rfl

theorem finite_word_marked_recognition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (h : Match27 e a j) :
    ∃! L : Albert →ₗ[ℝ] E,
      L 1 = e ∧
      (∀ i : Fin 3, L (nativeMarks i) = a i) ∧
      (∀ x y : Albert, L (jordan x y) = j (L x) (L y)) ∧
      (∀ x y : Albert, Inner.inner ℝ (L x) (L y) = inner x y) ∧
      Function.Injective L ∧ LinearMap.range L = generated e a j := by
  let wb := Glennie.Compact.NativeWordTableR01.wordBasis
  let v := candidateWordValues e a j
  have hns (i : Fin 27) : nativeWordValues i = Glennie.Compact.NativeWordTableR01.nativeWords i := by
    change wordValues 1 nativeMarks jordan i = _
    rw [show nativeMarks = Glennie.Compact.NativeWordTableR01.marks from funext fun k => by fin_cases k <;> rfl]
    exact wordValues_eq_source 1 _ jordan i
  have hwb (i : Fin 27) : wb i = nativeWordValues i :=
    (Glennie.Compact.NativeWordTableR01.wordBasis_eq_nativeWords i).trans (hns i).symm
  let L : Albert →ₗ[ℝ] E := wb.constr ℝ v
  have hL (i : Fin 27) : L (nativeWordValues i) = v i := by rw [← hwb]; exact wb.constr_basis ℝ v i
  have hunit : L 1 = e := hL 0
  have hmarks (i : Fin 3) : L (nativeMarks i) = a i := by fin_cases i <;> [exact hL 1; exact hL 2; exact hL 3]
  have hmetric (x y : Albert) : Inner.inner ℝ (L x) (L y) = inner x y := by
    change Inner.inner ℝ (L x) (L y) = Inner.inner ℝ x y
    conv_lhs => rw [← wb.sum_repr x, ← wb.sum_repr y]
    conv_rhs => rw [← wb.sum_repr x, ← wb.sum_repr y]
    simp only [map_sum, map_smul, _root_.sum_inner, _root_.inner_sum,
      real_inner_smul_left, real_inner_smul_right, hwb, hL]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    dsimp only [v]; rw [h.gram k i]; rfl
  have hinj : Function.Injective L := fun x y hxy => sub_eq_zero.mp <|
    (inner_self_eq_zero (x - y)).mp (by rw [← hmetric, map_sub, hxy, sub_self, _root_.inner_zero_left])
  have hprod_wb (i k : Fin 27) : L (jordan (wb i) (wb k)) = j (L (wb i)) (L (wb k)) := by
    rw [hwb, hwb, hL, hL]
    set w := jordan (nativeWordValues i) (nativeWordValues k)
    have h1 : Inner.inner ℝ (j (v i) (v k)) (L w) = inner w w := by
      conv_lhs => rw [← wb.sum_repr w]
      simp only [map_sum, map_smul, hwb, hL, _root_.inner_sum, real_inner_smul_right]
      dsimp only [v]; simp only [h.mixed i k]
      have hs : ∑ l : Fin 27, wb.repr w l * inner w (nativeWordValues l) = Inner.inner ℝ w (∑ l : Fin 27, wb.repr w l • wb l) := by
        rw [_root_.inner_sum]; exact Finset.sum_congr rfl fun l _ => by rw [real_inner_smul_right, hwb]; rfl
      rw [hs, wb.sum_repr]; rfl
    refine (sub_eq_zero.mp ((_root_.inner_self_eq_zero (𝕜 := ℝ)).mp ?_)).symm
    rw [_root_.inner_sub_left (𝕜 := ℝ), _root_.inner_sub_right (𝕜 := ℝ), _root_.inner_sub_right (𝕜 := ℝ),
      real_inner_comm (j (v i) (v k)) (L w), h1, hmetric w w]
    dsimp only [v]; rw [h.product_sq i k]
    change inner w w - inner w w - (inner w w - inner w w) = 0; ring
  have hprod (x y : Albert) : L (jordan x y) = j (L x) (L y) := by
    let JB : Albert →ₗ[ℝ] Albert →ₗ[ℝ] Albert :=
      LinearMap.mk₂ ℝ jordan jordan_add_left jordan_smul_left jordan_add_right jordan_smul_right
    conv_lhs => rw [← wb.sum_repr x, ← wb.sum_repr y]; change L (JB _ _)
    conv_rhs => rw [← wb.sum_repr x, ← wb.sum_repr y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, JB, LinearMap.mk₂_apply, hprod_wb]
  have hrange : LinearMap.range L = generated e a j := le_antisymm
    (by rw [LinearMap.range_eq_map, ← wb.span_eq, Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩; rw [hwb, hL]; change v i ∈ generated e a j; rw [generated, Submodule.mem_sInf]
        rintro K ⟨heK, haK, hjK⟩; change wordValues e a (fun p q => j p q) i ∈ K; rw [wordValues_eq_source]
        induction (Glennie.Compact.NativeWordTableR01.words i) with
        | unit => exact heK | mark m => exact haK m | mul _ _ ih1 ih2 => exact hjK _ ih1 _ ih2)
    (sInf_le ⟨⟨1, hunit⟩, fun i => ⟨nativeMarks i, hmarks i⟩, by rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩; exact ⟨jordan p q, hprod p q⟩⟩)
  refine ⟨L, ⟨hunit, hmarks, hprod, hmetric, hinj, hrange⟩, fun J ⟨hJu, hJm, hJp, _, _, _⟩ => wb.ext fun i => ?_⟩
  have heval (M : Albert →ₗ[ℝ] E) (hu : M 1 = e) (hm : ∀ m, M (nativeMarks m) = a m)
      (hp : ∀ x y, M (jordan x y) = j (M x) (M y)) (w : Glennie.Compact.NativeWordTableR01.Word) :
      M (Glennie.Compact.NativeWordTableR01.nativeEval w) =
        Glennie.Compact.NativeWordTableR01.eval e a (fun x y => j x y) w := by
    induction w with
    | unit => exact hu | mark m => exact hm m
    | mul u1 u2 ih1 ih2 =>
      change M (jordan (Glennie.Compact.NativeWordTableR01.nativeEval u1) (Glennie.Compact.NativeWordTableR01.nativeEval u2)) = _
      rw [hp, ih1, ih2]; rfl
  rw [hwb, hns]; exact (heval J hJu hJm hJp _).trans (heval L hunit hmarks hprod _).symm

end
end Glennie.SubmissionR03

@[expose] public section
namespace Glennie.SubmissionR04Quotient
noncomputable section
open Glennie Glennie.Compact.Affine20 Glennie.SubmissionR03
set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev ChartPoint := Fin 20 → ℝ
abbrev TripleCoordinates := Fin 3 → Fin 3 → Albert.Coordinates

def tripleCoordinates (T : Triple) : TripleCoordinates :=
  fun a i => Albert.coordinateEquiv (T a i)

def tripleCoordinateTopology : TopologicalSpace Triple :=
  TopologicalSpace.induced tripleCoordinates inferInstance

def tripleTopologicalSpace : TopologicalSpace Triple := tripleCoordinateTopology
attribute [local instance] tripleTopologicalSpace

abbrev Admitted (V : Set ChartPoint) :=
  {T : Triple // (∀ a : Fin 3, Frame (T a)) ∧
    Glennie.SubmissionR03.encode20 (fullLedger T) ∈ V}

def invariant (V : Set ChartPoint) (T : Admitted V) : V × Bool :=
  (⟨Glennie.SubmissionR03.encode20 (fullLedger T.1), T.2.2⟩,
    decide (0 < phiOf T.1))

namespace NativeAction
def refl : CompactAutomorphism where
  equiv := LinearEquiv.refl ℝ Albert
  map_jordan x y := by simp only [LinearEquiv.refl_apply]
  map_trace x := by simp only [LinearEquiv.refl_apply]

def comp (g h : CompactAutomorphism) : CompactAutomorphism where
  equiv := h.equiv.trans g.equiv
  map_jordan x y := by simp only [LinearEquiv.trans_apply, h.map_jordan, g.map_jordan]
  map_trace x := by simp only [LinearEquiv.trans_apply, g.map_trace, h.map_trace]

def symm (g : CompactAutomorphism) : CompactAutomorphism where
  equiv := g.equiv.symm
  map_jordan x y := by
    apply g.equiv.injective
    simp only [LinearEquiv.apply_symm_apply, g.map_jordan]
  map_trace x := by
    simpa only [LinearEquiv.apply_symm_apply] using (g.map_trace (g.equiv.symm x)).symm
end NativeAction

def orbitSetoid (V : Set ChartPoint) : Setoid (Admitted V) where
  r T S := ∃ g : CompactAutomorphism, Glennie.SubmissionR03.mapAtoms g T.1 = S.1
  iseqv := by
    constructor
    · intro T
      exact ⟨NativeAction.refl, by funext a i; rfl⟩
    · intro T S h
      obtain ⟨g, hg⟩ := h
      refine ⟨NativeAction.symm g, ?_⟩
      rw [← hg]
      funext a i
      exact g.equiv.symm_apply_apply (T.1 a i)
    · intro T S R hTS hSR
      obtain ⟨g, hg⟩ := hTS
      obtain ⟨h, hh⟩ := hSR
      refine ⟨NativeAction.comp h g, ?_⟩
      rw [← hh, ← hg]
      rfl

abbrev OrbitQuotient (V : Set ChartPoint) := Quotient (orbitSetoid V)
local instance (V : Set ChartPoint) : Setoid (Admitted V) := orbitSetoid V

theorem admitted_orbit_quotient_homeomorph :
    ∃ V : Set ChartPoint, IsOpen V ∧
      Glennie.SubmissionR03.encode20 (fullLedger flatBase) ∈ V ∧
      ∃ H : OrbitQuotient V ≃ₜ V × Bool,
        (∀ T : Admitted V, H (Quotient.mk' T) = invariant V T) ∧
        (∀ T S : Admitted V,
          (orbitSetoid V).r T S ↔ invariant V T = invariant V S) := by
  obtain ⟨V, ho, hb, secPos, secNeg, hcp, hcn, hfp, hfn, hep, hen, _, _, hpp, hpn, hcov, _, h20⟩ :=
    Glennie.SubmissionR03.nearby_fibres_two_orbits
  refine ⟨V, ho, hb, ?_⟩
  have hcatom (a i : Fin 3) : Continuous (fun T : Triple => T a i) :=
    Albert.coordinateLinearEquiv.symm.toLinearMap.continuous_of_finiteDimensional.comp
      ((continuous_apply i).comp ((continuous_apply a).comp (continuous_induced_dom : Continuous tripleCoordinates)))
  have hj {f g : Triple → Albert} (hf : Continuous f) (hg : Continuous g) : Continuous (fun T => jordan (f T) (g T)) := by
    simpa only [Function.comp_def] using continuous_jordan.comp (hf.prodMk hg)
  have hi {f g : Triple → Albert} (hf : Continuous f) (hg : Continuous g) : Continuous (fun T => inner (f T) (g T)) := by
    simpa only [Function.comp_def] using continuous_native_inner.comp (hf.prodMk hg)
  have htr {f : Triple → Albert} (hf : Continuous f) : Continuous (fun T => trace (f T)) := by
    simpa only [inner_unit_right] using hi hf (continuous_const : Continuous fun _ : Triple => (1 : Albert))
  have hcontLed : Continuous fullLedger :=
    (continuous_pi fun i => continuous_pi fun j => continuous_pi fun k => htr (hj (hj (hcatom f0 i) (hcatom f1 j)) (hcatom f2 k))).prodMk
      ((continuous_pi fun i => continuous_pi fun j => hi (hcatom f0 i) (hcatom f1 j)).prodMk
        ((continuous_pi fun j => continuous_pi fun k => hi (hcatom f1 j) (hcatom f2 k)).prodMk
          (continuous_pi fun k => continuous_pi fun i => hi (hcatom f2 k) (hcatom f0 i))))
  have hcontPhi : Continuous phiOf := by
    have hU {f g : Triple → Albert} (hf : Continuous f) (hg : Continuous g) : Continuous (fun T => U (f T) (g T)) := by
      have h1 := hj hf (hj hf hg); simpa only [U, two_smul] using (h1.fun_add h1).fun_sub (hj (hj hf hf) hg)
    have he (a : Fin 3) : Continuous (fun T : Triple => encoder (T a)) := (hcatom a 2).fun_sub (hcatom a 0)
    exact hi ((hU (he f0) (hU (he f1) (he f2))).fun_sub (hU (he f1) (hU (he f0) (he f2)))) (hU (he f2) (hj (he f0) (he f1)))
  have horb (T : Admitted V) :
      T.1 ∈ autOrbit (secNeg (Glennie.SubmissionR03.encode20 (fullLedger T.1))) ∨
      T.1 ∈ autOrbit (secPos (Glennie.SubmissionR03.encode20 (fullLedger T.1))) := by
    change T.1 ∈ autOrbit _ ∪ autOrbit _
    rw [← hcov _ T.2.2, ← h20 _ T.2.2]; exact ⟨T.2.1, rfl⟩
  have hphi_map {X Y : Triple} : (∃ g : CompactAutomorphism, Glennie.SubmissionR03.mapAtoms g X = Y) →
      phiOf Y = phiOf X := fun ⟨g, hg⟩ => by rw [← hg, phiOf_mapAtoms_sub]
  have hphi_ne (T : Admitted V) : phiOf T.1 ≠ 0 :=
    (horb T).elim (fun hN => by rw [hphi_map hN]; exact (hpn _ T.2.2).ne) (fun hP => by rw [hphi_map hP]; exact (hpp _ T.2.2).ne')
  have hrel_iff (T S : Admitted V) : (orbitSetoid V).r T S ↔ invariant V T = invariant V S := by
    constructor
    · rintro ⟨g, hg⟩
      exact Prod.ext (Subtype.ext (by change encode20 (fullLedger T.1) = encode20 (fullLedger S.1); rw [← hg, fullLedger_mapAtoms]))
        (by simp only [invariant, hphi_map ⟨g, hg⟩])
    · intro hinv
      have hc : encode20 (fullLedger T.1) = encode20 (fullLedger S.1) := congrArg (fun p : V × Bool => p.1.1) hinv
      have hs : decide (0 < phiOf T.1) = decide (0 < phiOf S.1) := congrArg Prod.snd hinv
      have htr_orb {A B C : Triple} : B ∈ autOrbit A → C ∈ autOrbit A → (∃ g : CompactAutomorphism, mapAtoms g B = C) := by
        rintro ⟨g, rfl⟩ ⟨h, rfl⟩
        exact ⟨h.comp g.symm, funext fun a => funext fun i => by show h.equiv (g.equiv.symm (g.equiv _)) = _; rw [g.equiv.symm_apply_apply]; rfl⟩
      rcases horb T with hTN | hTP <;> rcases horb S with hSN | hSP
      · exact htr_orb hTN (hc ▸ hSN)
      · exfalso; have := hphi_map hTN; have := hphi_map hSP
        exact Bool.false_ne_true ((decide_eq_false (not_lt.mpr (by linarith [hpn _ T.2.2]))).symm.trans (hs.trans (decide_eq_true (by linarith [hpp _ S.2.2]))))
      · exfalso; have := hphi_map hTP; have := hphi_map hSN
        exact Bool.false_ne_true ((decide_eq_false (not_lt.mpr (by linarith [hpn _ S.2.2]))).symm.trans (hs.symm.trans (decide_eq_true (by linarith [hpp _ T.2.2]))))
      · exact htr_orb hTP (hc ▸ hSP)
  let secP (b : V) : Admitted V := ⟨secPos b.1, hfp b.1 b.2, by change encode20 _ ∈ V; rw [hep b.1 b.2]; exact b.2⟩
  let secN (b : V) : Admitted V := ⟨secNeg b.1, hfn b.1 b.2, by change encode20 _ ∈ V; rw [hen b.1 b.2]; exact b.2⟩
  let fwd : OrbitQuotient V → V × Bool := Quotient.lift (invariant V) fun T S h => (hrel_iff T S).mp h
  let inv : V × Bool → OrbitQuotient V := fun z => if z.2 then Quotient.mk' (secP z.1) else Quotient.mk' (secN z.1)
  have hcont_inv_map : Continuous (invariant V) := by
    have hc1 : Continuous (fun T : Admitted V => (⟨encode20 (fullLedger T.1), T.2.2⟩ : V)) :=
      ((continuous_encode20.comp hcontLed).comp continuous_subtype_val).subtype_mk _
    have hc2 : Continuous (fun T : Admitted V => decide (0 < phiOf T.1)) := by
      rw [continuous_bool_rng true]
      have hcP := hcontPhi.comp (continuous_subtype_val : Continuous (Subtype.val : Admitted V → Triple))
      rw [show (fun T : Admitted V => decide (0 < phiOf T.1)) ⁻¹' {true} = {T | 0 < phiOf T.1} by ext; simp]
      have hcompl : ({T : Admitted V | 0 < phiOf T.1})ᶜ = {T | phiOf T.1 < 0} := by
        ext T; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]; exact ⟨fun h => lt_of_le_of_ne h (hphi_ne T), le_of_lt⟩
      exact ⟨isOpen_compl_iff.mp (hcompl ▸ isOpen_lt hcP continuous_const), isOpen_lt continuous_const hcP⟩
    exact hc1.prodMk hc2
  have hcont_inv : Continuous inv := continuous_prod_of_discrete_right.mpr fun s => by
    cases s
    · exact continuous_quotient_mk'.comp ((continuous_induced_rng.mpr
        (show Continuous (tripleCoordinates ∘ fun b : V => secNeg b.1) from hcn.comp_continuous continuous_subtype_val fun b => b.2)).subtype_mk _)
    · exact continuous_quotient_mk'.comp ((continuous_induced_rng.mpr
        (show Continuous (tripleCoordinates ∘ fun b : V => secPos b.1) from hcp.comp_continuous continuous_subtype_val fun b => b.2)).subtype_mk _)
  have hfm (X : Admitted V) : fwd (Quotient.mk' X) = invariant V X := rfl
  have hright (z : V × Bool) : fwd (inv z) = z := by
    rcases z with ⟨b, s⟩; cases s <;> dsimp only [inv] <;> simp only [Bool.false_eq_true, ↓reduceIte, hfm]
    · exact Prod.ext (Subtype.ext (hen b.1 b.2)) (decide_eq_false (not_lt.mpr (hpn b.1 b.2).le))
    · exact Prod.ext (Subtype.ext (hep b.1 b.2)) (decide_eq_true (hpp b.1 b.2))
  have hleft (q : OrbitQuotient V) : inv (fwd q) = q := Quotient.inductionOn q fun T => by
    let sT : Admitted V := if decide (0 < phiOf T.1) then secP ⟨_, T.2.2⟩ else secN ⟨_, T.2.2⟩
    have hi : inv (invariant V T) = Quotient.mk' sT := by dsimp only [inv, invariant, sT]; split_ifs <;> rfl
    have hr : fwd (inv (invariant V T)) = invariant V T := hright (invariant V T)
    change inv (invariant V T) = Quotient.mk' T
    rw [hi, hfm] at hr; rw [hi]; exact Quotient.sound ((hrel_iff _ T).mpr hr)
  exact ⟨{ toFun := fwd, invFun := inv, left_inv := hleft, right_inv := hright,
           continuous_toFun := hcont_inv_map.quotient_lift _, continuous_invFun := hcont_inv },
    fun _ => rfl, hrel_iff⟩

end
end Glennie.SubmissionR04Quotient

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

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
set_option autoImplicit false
open Glennie AlbertRecognition Filter
open scoped BigOperators ContDiff Topology

section Helpers
attribute [-instance] FloorSemiring.instCharZero RCLike.charZero_rclike
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance]
  taskAmbientDualNorm taskAmbientDualSpace
  taskAmbientBilinearNorm taskAmbientBilinearSpace
  taskAmbientTrilinearNorm taskAmbientTrilinearSpace
  taskAmbientEndNorm taskAmbientEndSpace
  taskAmbientVectorBilinearNorm taskAmbientVectorBilinearSpace
  taskAmbientInverseNorm taskAmbientInverseSpace
  tangentDualNormedAddCommGroup tangentDualNormedSpace
  tangentBilinearNormedAddCommGroup tangentBilinearNormedSpace
  tangentTrilinearNormedAddCommGroup tangentTrilinearNormedSpace
  tangentEndNormedAddCommGroup tangentEndNormedSpace
  tangentVectorBilinearNormedAddCommGroup tangentVectorBilinearNormedSpace
  tangentInverseNormedAddCommGroup tangentInverseNormedSpace

private def nativeAdjoint (x : Albert) : Albert :=
  jordan x x - Glennie.trace x • x + ((Glennie.trace x ^ 2 - Glennie.inner x x) / 2) • (1 : Albert)

private theorem nativeCubic_line (x y : Albert) (t : ℝ) :
    nativeCubic (x + t • y) = nativeCubic x +
      t * Glennie.inner (nativeAdjoint x) y +
      t ^ 2 * Glennie.inner (nativeAdjoint y) x + t ^ 3 * nativeCubic y := by
  simp only [nativeCubic, nativeAdjoint, trace_add, trace_smul,
    jordan_add_left, jordan_add_right, jordan_smul_left, jordan_smul_right,
    Glennie.inner_add_left, Glennie.inner_add_right, Glennie.inner_sub_left,
    Glennie.inner_smul_left, Glennie.inner_smul_right, inner_unit_left,
    jordan_comm y x, inner_comm y x, inner_comm y (jordan x x), inner_comm x (jordan y y),
    inner_jordan_associative x x y, inner_jordan_associative y y x]
  ring

private theorem nativeAdjoint_cross (x y : Albert) :
    nativeAdjoint (x + y) - nativeAdjoint x - nativeAdjoint y =
      (2 : ℝ) • jordan x y - Glennie.trace y • x - Glennie.trace x • y +
        (Glennie.trace x * Glennie.trace y - Glennie.inner x y) • (1 : Albert) := by
  simp only [nativeAdjoint, trace_add, jordan_add_left, jordan_add_right,
    Glennie.inner_add_left, Glennie.inner_add_right, jordan_comm y x, inner_comm y x]
  module

private def curry3 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X) ℝ) : X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ :=
  letI : NormedAddCommGroup (X →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (X →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  (((continuousMultilinearCurryFin1 ℝ X (X →L[ℝ] ℝ)).toContinuousLinearEquiv).toContinuousLinearMap).comp
    f.curryRight.curryLeft

@[simp] private theorem curry3_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X) ℝ) (x y z : X) :
    curry3 f x y z = f ![x, y, z] := by
  letI : NormedAddCommGroup (X →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (X →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  change continuousMultilinearCurryFin1 ℝ X (X →L[ℝ] ℝ) (f.curryRight.curryLeft x) y z = f ![x, y, z]
  rw [continuousMultilinearCurryFin1_apply, ContinuousMultilinearMap.curryLeft_apply,
    show Fin.cons x (Fin.snoc (0 : Fin 0 → X) y) = ![x, y] by ext i; fin_cases i <;> simp]
  change f (Fin.snoc ![x, y] z) = f ![x, y, z]; congr 1; ext i; fin_cases i <;> simp

private theorem cubic_eq_curry3 (P : BasedCubic E) (z : E) : cubic P z = curry3 P.form z z z := by
  rw [curry3_apply]; change P.form (fun _ => z) = P.form ![z, z, z]; congr 1; ext i; fin_cases i <;> rfl

private theorem contDiff_cubic (P : BasedCubic E) : ContDiff ℝ ⊤ (cubic P) := by
  rw [funext (cubic_eq_curry3 P)]
  exact ((curry3 P.form).contDiff.clm_apply contDiff_id).clm_apply contDiff_id

private theorem fderiv_cubic_apply (P : BasedCubic E) (x y : E) :
    fderiv ℝ (cubic P) x y = 3 * P.form ![x, x, y] := by
  let L := curry3 P.form
  have h1 := (L.hasFDerivAt (x := x)).clm_apply (hasFDerivAt_id x)
  have h2 := h1.clm_apply (hasFDerivAt_id x)
  simp only [id_eq] at h2
  rw [show cubic P = fun z => L z z z from funext (cubic_eq_curry3 P), h2.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, id_eq, L, curry3_apply, P.swap12 y x x, P.swap23 x y x]
  ring

private theorem traceAt_self (P : BasedCubic E) (e : E) (he : cubic P e = 1) : traceAt P e e = 3 := by
  rw [traceAt, fderiv_cubic_apply, ← curry3_apply, ← cubic_eq_curry3, he]; ring

private abbrev hessian (P : BasedCubic E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun z : E => fderiv ℝ (cubic P) z) x

private theorem hasFDerivAt_traceAt (P : BasedCubic E) (x : E) :
    HasFDerivAt (fun z => fderiv ℝ (cubic P) z) ((6 : ℝ) • curry3 P.form x) x := by
  let L := curry3 P.form
  have hf : (fun z => fderiv ℝ (cubic P) z) = fun z => (3 : ℝ) • L z z :=
    funext fun z => by ext y; rw [fderiv_cubic_apply]; simp [L]
  have hd := (((L.hasFDerivAt (x := x)).clm_apply (hasFDerivAt_id x)).const_smul (3 : ℝ))
  simp only [id_eq] at hd
  rw [hf]; refine hd.congr_fderiv ?_
  ext u v; simp [L, P.swap12 u x v]; ring

private theorem hessian_eq (P : BasedCubic E) (x : E) : hessian P x = (6 : ℝ) • curry3 P.form x :=
  (hasFDerivAt_traceAt P x).fderiv

private theorem hessian_apply (P : BasedCubic E) (x u v : E) : hessian P x u v = 6 * P.form ![x, u, v] := by
  rw [hessian_eq]; simp

private theorem hasFDerivAt_hessian (P : BasedCubic E) (x : E) :
    HasFDerivAt (hessian P) ((6 : ℝ) • curry3 P.form) x :=
  (((6 : ℝ) • curry3 P.form).hasFDerivAt (x := x)).congr_of_eventuallyEq
    (Eventually.of_forall fun z => (hessian_eq P z).symm ▸ rfl)

private theorem eventually_pos (P : BasedCubic E) {x : E} (hx : 0 < cubic P x) :
    ∀ᶠ z in 𝓝 x, 0 < cubic P z :=
  (isOpen_lt continuous_const (contDiff_cubic P).continuous).mem_nhds hx

private theorem hasFDerivAt_invCubic (P : BasedCubic E) {x : E} (hx : 0 < cubic P x) :
    HasFDerivAt (fun z => (cubic P z)⁻¹) ((-(cubic P x ^ 2)⁻¹) • traceAt P x) x :=
  (hasDerivAt_inv hx.ne').comp_hasFDerivAt x ((contDiff_cubic P).contDiffAt.differentiableAt (by simp)).hasFDerivAt

private theorem metric_apply (P : BasedCubic E) {x : E} (hx : 0 < cubic P x) (u v : E) :
    metric P x u v = -hessian P x u v / (3 * cubic P x) +
      traceAt P x u * traceAt P x v / (3 * cubic P x ^ 2) := by
  have hlog (z : E) (hz : 0 < cubic P z) :
      fderiv ℝ (fun w => Real.log (cubic P w)) z = (cubic P z)⁻¹ • fderiv ℝ (cubic P) z :=
    ((((contDiff_cubic P).contDiffAt (x := z)).differentiableAt (by simp)).hasFDerivAt.log hz.ne').fderiv
  have hd : HasFDerivAt (fun z => fderiv ℝ (fun w => Real.log (cubic P w)) z)
      ((cubic P x)⁻¹ • hessian P x + ((-(cubic P x ^ 2)⁻¹) • traceAt P x).smulRight (traceAt P x)) x :=
    ((hasFDerivAt_invCubic P hx).smul
      ((hasFDerivAt_traceAt P x).congr_fderiv (hessian_eq P x).symm)).congr_of_eventuallyEq
      ((eventually_pos P hx).mono fun z hz => hlog z hz)
  simp only [metric, hd.fderiv, traceAt, smul_apply, add_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem metric_symm (P : BasedCubic E) {x : E} (hx : 0 < cubic P x) (u v : E) :
    metric P x u v = metric P x v u := by
  rw [metric_apply P hx, metric_apply P hx, hessian_apply, hessian_apply, P.swap23]; ring

private theorem rawPair_apply (P : BasedCubic E) (e u v : E) :
    rawPair P e u v = traceAt P e u * traceAt P e v - hessian P e u v := by
  simp [rawPair, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

private theorem rawPair_eq_three_metric (P : BasedCubic E) (e : E) (he : cubic P e = 1) (u v : E) :
    rawPair P e u v = 3 * metric P e u v := by
  rw [rawPair_apply, metric_apply P (by linarith : 0 < cubic P e), he]; ring

private theorem eval_const_hasFDerivAt {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup (Y →L[ℝ] Z)] [NormedSpace ℝ (Y →L[ℝ] Z)]
    {f : X → Y →L[ℝ] Z} {f' : X →L[ℝ] Y →L[ℝ] Z} {x : X}
    (hf : HasFDerivAt f f' x) (u : Y) : HasFDerivAt (fun y => f y u) (f'.flip u) x :=
  (hf.clm_apply (hasFDerivAt_const u x)).congr_fderiv (by ext w; simp)

private theorem contDiffAt_metric (P : BasedCubic E) {x : E} (hx : 0 < cubic P x) :
    ContDiffAt ℝ ⊤ (metric P) x := by
  have hd : ContDiffAt ℝ ⊤ (fun y => fderiv ℝ (fun z => Real.log (cubic P z)) y) x :=
    ((contDiff_cubic P).contDiffAt.log hx.ne').fderiv_right (by simp)
  have hh : ContDiffAt ℝ ⊤ (fderiv ℝ (fun y => fderiv ℝ (fun z => Real.log (cubic P z)) y)) x :=
    hd.fderiv_right (by simp)
  exact hh.const_smul (-1 / 3 : ℝ)

private theorem ambientKoszulTensor_eq_half (P : BasedCubic E) {x : E} (hx : 0 < cubic P x) :
    ambientKoszulTensor P x = (1 / 2 : ℝ) • ambientMetricD1 P x := by
  have hs12 (u v w : E) : ambientMetricD1 P x u v w = ambientMetricD1 P x v u w := by
    have hd : ContDiffAt ℝ ⊤ (fun y => fderiv ℝ (fun z => Real.log (cubic P z)) y) x :=
      ((contDiff_cubic P).contDiffAt.log hx.ne').fderiv_right (by simp)
    have hh0 : ContDiffAt ℝ ⊤ (fderiv ℝ (fun y => fderiv ℝ (fun z => Real.log (cubic P z)) y)) x :=
      hd.fderiv_right (by simp)
    have hh := (hh0.differentiableAt (by simp)).hasFDerivAt.const_smul (-1 / 3 : ℝ)
    have hm : fderiv ℝ (metric P) x = (-1 / 3 : ℝ) • fderiv ℝ (fderiv ℝ fun y => fderiv ℝ (fun z => Real.log (cubic P z)) y) x :=
      hh.fderiv
    change fderiv ℝ (metric P) x u v w = fderiv ℝ (metric P) x v u w
    rw [hm]; simp only [smul_apply, smul_eq_mul]
    exact congrArg ((-1 / 3 : ℝ) * ·) (congrArg (fun L : E →L[ℝ] ℝ => L w) ((hd.isSymmSndFDerivAt le_top).eq u v))
  have hs23 (u v w : E) : ambientMetricD1 P x u v w = ambientMetricD1 P x u w v := by
    have hG : HasFDerivAt (metric P) (ambientMetricD1 P x) x :=
      ((contDiffAt_metric P hx).differentiableAt (by simp)).hasFDerivAt
    have h1 := eval_const_hasFDerivAt (eval_const_hasFDerivAt hG v) w
    have h2 := eval_const_hasFDerivAt (eval_const_hasFDerivAt hG w) v
    have hc : (fun y => metric P y v w) =ᶠ[𝓝 x] (fun y => metric P y w v) :=
      (eventually_pos P hx).mono fun y hy => metric_symm P hy v w
    simpa only [ContinuousLinearMap.flip_apply] using
      congrArg (fun L : E →L[ℝ] ℝ => L u) (h1.unique (h2.congr_of_eventuallyEq hc))
  ext u v w
  have hf : ((((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv).toContinuousLinearMap :
      (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ).comp (ambientMetricD1 P x).flip) u v w =
      ambientMetricD1 P x w u v := rfl
  simp only [ambientKoszulTensor, smul_apply, add_apply, sub_apply]
  rw [hf]; simp only [ContinuousLinearMap.flip_apply, smul_eq_mul, hs12 v u w, hs12 w u v, hs23 u w v]; ring

private theorem cubic_expand_add (P : BasedCubic E) (x y : E) (t : ℝ) :
    cubic P (x + t • y) =
      cubic P x + 3 * t * P.form ![x, x, y] +
        3 * t ^ 2 * P.form ![x, y, y] + t ^ 3 * cubic P y := by
  rw [cubic_eq_curry3 P (x + t • y), cubic_eq_curry3 P x, cubic_eq_curry3 P y]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, curry3_apply,
    P.swap23 x y x, (P.swap12 y x x).trans (P.swap23 x y x),
    P.swap12 y x y, (P.swap23 y y x).trans (P.swap12 y x y)]
  ring

private theorem nativeCubic_split (t : ℝ) (u : V) :
    nativeCubic (t • (1 : Albert) + (u : Albert)) =
      t ^ 3 - (3 / 2 : ℝ) * t * gA u u + CA u u u := by
  rw [CA_eq_native, gA]
  simp only [nativeCubic, trace_add, trace_smul, trace_unit, trace_V,
    jordan_add_left, jordan_add_right, jordan_smul_left, jordan_smul_right,
    jordan_unit_left, jordan_unit_right, Glennie.inner_add_left, Glennie.inner_add_right,
    Glennie.inner_smul_left, Glennie.inner_smul_right, inner_unit_left, inner_unit_right,
    show ∀ a b : Albert, Glennie.trace (jordan a b) = Glennie.inner a b from fun _ _ => rfl,
    inner_comm (u : Albert) (jordan (u : Albert) (u : Albert))]
  ring

private theorem cubic_split_E (P : BasedCubic E) (e : E) (he : cubic P e = 1)
    (t : ℝ) (u : tangent P e) :
    cubic P (t • e + (u : E)) =
      t ^ 3 - (3 / 2 : ℝ) * t * metric P e (u : E) (u : E) +
        P.form ![(u : E), (u : E), (u : E)] := by
  have hu : fderiv ℝ (cubic P) e (u : E) = 0 := u.property
  have h1 : P.form ![e, e, (u : E)] = 0 := by linarith [fderiv_cubic_apply P e (u : E)]
  have h2 : P.form ![e, (u : E), (u : E)] = -(1 / 2 : ℝ) * metric P e (u : E) (u : E) := by
    have hm := metric_apply P (by linarith : 0 < cubic P e) (u : E) (u : E)
    rw [he, traceAt, hu, hessian_apply] at hm; linarith
  have h3 := cubic_expand_add P (t • e) (u : E) 1; rw [one_smul] at h3
  rw [h3, cubic_eq_curry3 P (t • e), cubic_eq_curry3 P (u : E)]
  simp only [← curry3_apply, map_smul, smul_apply, smul_eq_mul]
  simp only [curry3_apply, h1, h2,
    show P.form ![e, e, e] = 1 from (congrArg P.form (funext fun i => by fin_cases i <;> rfl)).trans he]; ring

private theorem fderiv_from_norm_iso (P : BasedCubic E) (A : E ≃ₗ[ℝ] Albert)
    (hnorm : ∀ x : E, nativeCubic (A x) = cubic P x) (x y : E) :
    fderiv ℝ (cubic P) x y = Glennie.inner (nativeAdjoint (A x)) (A y) := by
  have he1 := cubic_expand_add P x y 1
  have he2 := cubic_expand_add P x y (-1)
  have hn1 := nativeCubic_line (A x) (A y) 1
  have hn2 := nativeCubic_line (A x) (A y) (-1)
  rw [← map_smul, ← map_add, hnorm, hnorm, hnorm] at hn1 hn2
  linarith [fderiv_cubic_apply P x y]

private theorem hessian_at_unit_from_norm_iso (P : BasedCubic E) (e : E)
    (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
    (hnorm : ∀ x : E, nativeCubic (A x) = cubic P x) (x y : E) :
    hessian P e x y = Glennie.trace (A x) * Glennie.trace (A y) - Glennie.inner (A x) (A y) := by
  have h1 : fderiv ℝ (cubic P) (e + x) y - fderiv ℝ (cubic P) e y - fderiv ℝ (cubic P) x y =
      hessian P e x y := by
    rw [fderiv_cubic_apply, fderiv_cubic_apply, fderiv_cubic_apply, hessian_apply]
    simp only [← curry3_apply, map_add, add_apply]; simp only [curry3_apply, P.swap12 x e y]; ring
  rw [← h1, fderiv_from_norm_iso P A hnorm, fderiv_from_norm_iso P A hnorm,
    fderiv_from_norm_iso P A hnorm, map_add, hunit,
    ← Glennie.inner_sub_left, ← Glennie.inner_sub_left, nativeAdjoint_cross]
  simp only [trace_unit, jordan_unit_left, inner_unit_left, Glennie.inner_add_left,
    Glennie.inner_sub_left, Glennie.inner_smul_left]
  ring

private def nativeToSource : NativeTangent ≃ₗ[ℝ] V :=
  LinearEquiv.ofEq _ _ (by congr 1)

private theorem nativeToSource_K (u v : NativeTangent) :
    nativeToSource (nativeK u v) = KA (nativeToSource u) (nativeToSource v) := Subtype.ext rfl

private theorem nativeToSource_metric (u v : NativeTangent) :
    nativeMetric u v = gA (nativeToSource u) (nativeToSource v) := rfl

private theorem tangentCubicForm_vec (P : BasedCubic E) (e : E) (a b c : tangent P e) :
    tangentCubicForm P e ![a, b, c] = P.form ![(a : E), (b : E), (c : E)] := by
  rw [tangentCubicForm, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1; ext i; fin_cases i <;> rfl

variable [FiniteDimensional ℝ E]

private theorem pos_injective {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup (X →L[ℝ] ℝ)] [NormedSpace ℝ (X →L[ℝ] ℝ)]
    (g : X →L[ℝ] X →L[ℝ] ℝ) (hp : ∀ u : X, u ≠ 0 → 0 < g u u) : Function.Injective g :=
  fun u v huv => by
    by_contra hne
    have hz0 : g (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have h0 : g (u - v) (u - v) = 0 := by rw [hz0]; rfl
    exact (hp _ (sub_ne_zero.mpr hne)).ne' h0

private theorem pos_isInvertible {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup (X →L[ℝ] ℝ)] [NormedSpace ℝ (X →L[ℝ] ℝ)]
    (g : X →L[ℝ] X →L[ℝ] ℝ) (hp : ∀ u : X, u ≠ 0 → 0 < g u u) : g.IsInvertible := by
  let d : Module.Dual ℝ X ≃ₗ[ℝ] (X →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
  have : FiniteDimensional ℝ (X →L[ℝ] ℝ) := d.finiteDimensional
  exact ⟨(LinearEquiv.ofInjectiveOfFinrankEq g.toLinearMap (pos_injective g hp)
    ((Subspace.dual_finrank_eq (K := ℝ) (V := X)).symm.trans d.finrank_eq)).toContinuousLinearEquiv, rfl⟩

private theorem rawPair_isInvertible (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) :
    (rawPair P e).IsInvertible :=
  pos_isInvertible (rawPair P e) fun x hx => by
    rw [rawPair_eq_three_metric P e he]; linarith [hp x hx]

private theorem adjoint_pairing (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) (x y : E) :
    rawPair P e (adjoint P e x) y = fderiv ℝ (cubic P) x y :=
  congrArg (fun L : E →L[ℝ] ℝ => L y)
    ((rawPair_isInvertible P e he hp).self_apply_inverse (fderiv ℝ (cubic P) x))

omit [FiniteDimensional ℝ E] in
private theorem ambientConnection_koszul (P : BasedCubic E) (x : E)
    (hi : (metric P x).IsInvertible) (u v w : E) :
    metric P x (ambientConnection P x u v) w = ambientKoszulTensor P x u v w :=
  congrArg (fun L : E →L[ℝ] ℝ => L w) (hi.self_apply_inverse (ambientKoszulTensor P x u v))

private theorem ambientConnection_at_one (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (hp : ∀ u : E, u ≠ 0 → 0 < metric P e u u) (u v : E) :
    ambientConnection P e u v = -product P e u v := by
  have hN : 0 < cubic P e := by linarith
  apply pos_injective (metric P e) hp; ext w
  rw [ambientConnection_koszul P e (pos_isInvertible (metric P e) hp), ambientKoszulTensor_eq_half P hN]
  simp only [smul_apply, map_neg, neg_apply, smul_eq_mul]
  have hD1 : ambientMetricD1 P e u v w = (-1 / 3 : ℝ) *
      (6 * P.form ![u, v, w] - traceAt P e u * hessian P e v w -
        hessian P e u v * traceAt P e w - traceAt P e v * hessian P e u w +
        2 * traceAt P e u * traceAt P e v * traceAt P e w) := by
    have hG := eval_const_hasFDerivAt (eval_const_hasFDerivAt
      (((contDiffAt_metric P hN).differentiableAt (by simp)).hasFDerivAt) v) w
    have hH := eval_const_hasFDerivAt (eval_const_hasFDerivAt (hasFDerivAt_hessian P e) v) w
    have hT (z : E) : HasFDerivAt (fun y => traceAt P y z) (((6 : ℝ) • curry3 P.form e).flip z) e :=
      eval_const_hasFDerivAt (hasFDerivAt_traceAt P e) z
    have hR := hasFDerivAt_invCubic P hN
    have hs := ((hH.mul hR).const_smul (-1 / 3 : ℝ)).add ((((hT v).mul (hT w)).mul hR).mul hR |>.const_smul (1 / 3 : ℝ))
    have hc : (fun y => metric P y v w) =ᶠ[𝓝 e]
        (fun y => (-1 / 3 : ℝ) * (hessian P y v w * (cubic P y)⁻¹) +
          (1 / 3 : ℝ) * (traceAt P y v * traceAt P y w * (cubic P y)⁻¹ * (cubic P y)⁻¹)) :=
      (eventually_pos P hN).mono fun y hy => by
        change metric P y v w = _; rw [metric_apply P hy]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
    have hd := congrArg (fun L : E →L[ℝ] ℝ => L u) (hG.unique (hs.congr_of_eventuallyEq hc))
    change fderiv ℝ (metric P) e u v w = _
    simp only [ContinuousLinearMap.flip_apply, add_apply, smul_apply, curry3_apply,
      smul_eq_mul, Pi.mul_apply, he, one_pow, inv_one, ← hessian_apply] at hd
    rw [hd, hessian_apply P u v w]; ring
  have hru : rawPair P e e w = traceAt P e w := by
    rw [rawPair_apply, traceAt_self P e he, hessian_apply, traceAt, fderiv_cubic_apply]; ring
  have hg := rawPair_eq_three_metric P e he (product P e u v) w
  have hl : rawPair P e (product P e u v) w = -3 * ((1 / 2 : ℝ) * ambientMetricD1 P e u v w) := by
    rw [hD1, product]
    simp only [map_smul, map_add, map_sub, smul_apply, add_apply, sub_apply, smul_eq_mul,
      adjoint_pairing P e he hp, hru]
    rw [rawPair_apply P e v w, rawPair_apply P e u w, rawPair_apply P e u v,
      fderiv_cubic_apply, fderiv_cubic_apply, fderiv_cubic_apply]
    simp only [← curry3_apply, map_add, add_apply]; simp only [curry3_apply, P.swap12 v u w]; ring
  linarith

private theorem ambientCurvature_at_one [CompleteSpace E] (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (hp : ∀ u : E, u ≠ 0 → 0 < metric P e u u) (u v w : E) :
    ambientCurvature P e u v w = -(product P e u (product P e v w) - product P e v (product P e u w)) := by
  have hx : 0 < cubic P e := by linarith
  have hInv := pos_isInvertible (metric P e) hp
  have hcG : ContDiffAt ℝ ⊤ (ambientConnection P) e := by
    have hG := contDiffAt_metric P hx
    have hi : ContDiffAt ℝ ⊤ (fun y => (metric P y).inverse) e := hInv.contDiffAt_map_inverse.fun_comp e hG
    have hDG : ContDiffAt ℝ ⊤ (ambientMetricD1 P) e := hG.fderiv_right (by simp)
    have hK : ContDiffAt ℝ ⊤ (ambientKoszulTensor P) e :=
      (hDG.const_smul (1 / 2 : ℝ)).congr_of_eventuallyEq
        ((eventually_pos P hx).mono fun y hy => ambientKoszulTensor_eq_half P hy)
    exact ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E).contDiff.contDiffAt.fun_comp e hi).clm_comp hK
  have hΓ : HasFDerivAt (ambientConnection P) (fderiv ℝ (ambientConnection P) e) e :=
    (hcG.differentiableAt (by simp)).hasFDerivAt
  have hconst (a : E) : ambientCovariantDerivative P a (fun _ : E => w) = fun y => ambientConnection P y a w :=
    funext fun y => by simp [ambientCovariantDerivative]
  have happ : ambientCurvature P e u v w =
      fderiv ℝ (ambientConnection P) e u v w - fderiv ℝ (ambientConnection P) e v u w +
        ambientConnection P e u (ambientConnection P e v w) - ambientConnection P e v (ambientConnection P e u w) := by
    rw [ambientCurvature, hconst v, hconst u]
    have hv := eval_const_hasFDerivAt (eval_const_hasFDerivAt hΓ v) w
    have hu := eval_const_hasFDerivAt (eval_const_hasFDerivAt hΓ u) w
    simp only [ambientCovariantDerivative, hv.fderiv, hu.fderiv, ContinuousLinearMap.flip_apply]; abel
  obtain ⟨M, hM⟩ := hInv
  have hevInv : ∀ᶠ y in 𝓝 e, (metric P y).IsInvertible :=
    (contDiffAt_metric P hx).continuousAt.eventually (hM ▸ M.nhds)
  have hD1_pair (a b z : E) :
      metric P e (fderiv ℝ (ambientConnection P) e a b w) z =
        (1 / 2 : ℝ) * fderiv ℝ (ambientMetricD1 P) e a b w z -
          ambientMetricD1 P e a (ambientConnection P e b w) z := by
    have hG : HasFDerivAt (metric P) (ambientMetricD1 P e) e :=
      ((contDiffAt_metric P hx).differentiableAt (by simp)).hasFDerivAt
    have hpair := eval_const_hasFDerivAt (hG.clm_apply (eval_const_hasFDerivAt (eval_const_hasFDerivAt hΓ b) w)) z
    have hD1c : ContDiffAt ℝ ⊤ (ambientMetricD1 P) e := (contDiffAt_metric P hx).fderiv_right (by simp)
    have hD1 := (hD1c.differentiableAt (by simp)).hasFDerivAt
    have hjet := eval_const_hasFDerivAt (eval_const_hasFDerivAt (eval_const_hasFDerivAt hD1 b) w) z
    have hc : (fun y => metric P y (ambientConnection P y b w) z) =ᶠ[𝓝 e]
        (fun y => (1 / 2 : ℝ) * ambientMetricD1 P y b w z) :=
      ((eventually_pos P hx).and hevInv).mono fun y ⟨hy1, hy2⟩ => by
        change metric P y (ambientConnection P y b w) z = _
        rw [ambientConnection_koszul P y hy2, ambientKoszulTensor_eq_half P hy1]; simp [smul_eq_mul]
    have hd := congrArg (fun L : E →L[ℝ] ℝ => L a) (hpair.unique ((hjet.const_smul (1 / 2 : ℝ)).congr_of_eventuallyEq hc))
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply, add_apply, smul_apply, smul_eq_mul] at hd
    linarith
  have hswapD2 (z : E) : fderiv ℝ (ambientMetricD1 P) e u v w z = fderiv ℝ (ambientMetricD1 P) e v u w z :=
    congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L w z) (((contDiffAt_metric P hx).isSymmSndFDerivAt le_top).eq u v)
  have h2G (a b z : E) : ambientMetricD1 P e a b z = 2 * metric P e (ambientConnection P e a b) z := by
    have h := ambientConnection_koszul P e ⟨M, hM⟩ a b z
    rw [ambientKoszulTensor_eq_half P hx] at h; simp only [smul_apply, smul_eq_mul] at h; linarith
  have hcomm : ambientCurvature P e u v w =
      -(ambientConnection P e u (ambientConnection P e v w) - ambientConnection P e v (ambientConnection P e u w)) := by
    apply pos_injective (metric P e) hp; ext z
    rw [happ]; simp only [map_sub, map_add, map_neg, sub_apply, add_apply, neg_apply]
    rw [hD1_pair u v z, hD1_pair v u z, hswapD2 z, h2G u (ambientConnection P e v w) z, h2G v (ambientConnection P e u w) z]
    ring
  rw [hcomm, ambientConnection_at_one P e he hp v w, ambientConnection_at_one P e he hp u w,
    map_neg, map_neg, ambientConnection_at_one P e he hp, ambientConnection_at_one P e he hp, neg_neg, neg_neg]

private theorem tangentMetricDual_isInvertible (P : BasedCubic E) (e : E)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) :
    (tangentMetricDual P e).IsInvertible :=
  pos_isInvertible (tangentMetricDual P e) fun u hu => hp u (Subtype.coe_ne_coe.mpr hu)

private theorem raised_pairing (P : BasedCubic E) (e : E)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) (u v w : tangent P e) :
    tangentMetricDual P e (independentRaisedCubic P e u v) w =
      P.form ![(u : E), (v : E), (w : E)] := by
  have hi := congrArg (fun L : tangent P e →L[ℝ] ℝ => L w)
    ((tangentMetricDual_isInvertible P e hp).self_apply_inverse (tangentCubicCurried P e u v))
  exact hi.trans ((curry3_apply (tangentCubicForm P e) u v w).trans (tangentCubicForm_vec P e u v w))

private def pullbackSymmetricCubic (P : BasedCubic E) (e : E) (F : V ≃ₗ[ℝ] tangent P e) : SymmetricCubic :=
  let f : V →ₗ[ℝ] E := (tangent P e).subtype.comp F.toLinearMap
  { form := LinearMap.mk₂ ℝ (fun x y => (curry3 P.form (f x) (f y)).toLinearMap.comp f)
      (fun _ _ _ => by ext; simp) (fun _ _ _ => by ext; simp)
      (fun _ _ _ => by ext; simp) (fun _ _ _ => by ext; simp)
    swap12 _ _ _ := by simp only [LinearMap.mk₂_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, curry3_apply]; exact P.swap12 _ _ _
    swap23 _ _ _ := by simp only [LinearMap.mk₂_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, curry3_apply]; exact P.swap23 _ _ _ }

private theorem exists_norm_unit_equiv (P : BasedCubic E) (e : E) (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x)
    (hMatch : ∃ F : NativeTangent ≃ₗ[ℝ] tangent P e,
      (∀ x y : NativeTangent, metric P e (F x : E) (F y : E) = nativeMetric x y) ∧
      (∀ x y z : NativeTangent,
        independentCurvature P e (F x) (F y) (F z) = F (nativeCurvature x y z))) :
    ∃ A : E ≃ₗ[ℝ] Albert, A e = 1 ∧ ∀ x : E, nativeCubic (A x) = cubic P x := by
  obtain ⟨F, hmet0, hcurv0⟩ := hMatch
  let F₀ : V ≃ₗ[ℝ] tangent P e := nativeToSource.symm.trans F
  have hmet (x y : V) : tangentMetricDual P e (F₀ x) (F₀ y) = gA x y := by
    change metric P e (F (nativeToSource.symm x) : E) (F (nativeToSource.symm y) : E) = gA x y
    rw [hmet0, nativeToSource_metric]; simp
  let B := pullbackSymmetricCubic P e F₀
  obtain ⟨eDual, heDual⟩ := tangentMetricDual_isInvertible P e hp
  have hraised (x y : V) : independentRaisedCubic P e (F₀ x) (F₀ y) = F₀ (KB B x y) := by
    apply eDual.injective; ext w
    obtain ⟨z, rfl⟩ := F₀.surjective w
    have h1 := congrArg (fun (L : tangent P e →L[ℝ] tangent P e →L[ℝ] ℝ) => L (independentRaisedCubic P e (F₀ x) (F₀ y)) (F₀ z)) heDual
    have h2 := congrArg (fun (L : tangent P e →L[ℝ] tangent P e →L[ℝ] ℝ) => L (F₀ (KB B x y)) (F₀ z)) heDual
    have hb : B.form x y z = P.form ![(F₀ x : E), (F₀ y : E), (F₀ z : E)] := curry3_apply P.form _ _ _
    exact (h1.trans (raised_pairing P e hp _ _ _)).trans
      (hb.symm.trans ((KB_pairing B x y z).symm.trans ((hmet _ _).symm.trans h2.symm)))
  have hq : q B = q referenceCubic := by
    funext x y; apply LinearMap.ext; intro z
    have hc := hcurv0 (nativeToSource.symm x) (nativeToSource.symm y) (nativeToSource.symm z)
    change independentCurvature P e (F₀ x) (F₀ y) (F₀ z) = F₀ (nativeToSource (nativeCurvature _ _ _)) at hc
    simp only [nativeCurvature, map_add, map_sub, map_smul, map_neg, nativeToSource_K,
      nativeToSource_metric, LinearEquiv.apply_symm_apply] at hc
    simp only [independentCurvature, hmet, hraised, ← KB_referenceCubic, neg_smul,
      ← map_smul, ← map_sub, ← map_add] at hc
    have hinj := F₀.injective hc
    simp only [q, operatorComm, LinearMap.sub_apply, LinearMap.comp_apply]
    linear_combination (norm := module) -hinj
  have hF₁ : ∃ F₁ : V ≃ₗ[ℝ] tangent P e,
      (∀ u : V, metric P e (F₁ u : E) (F₁ u : E) = gA u u) ∧
      (∀ u : V, P.form ![(F₁ u : E), (F₁ u : E), (F₁ u : E)] = CA u u u) := by
    rcases q_fiber_reference B hq with hB | hB
    · refine ⟨F₀, fun u => hmet u u, fun u => (curry3_apply P.form _ _ _).symm.trans ?_⟩
      change B.form u u u = CA u u u
      have hb := congrArg (fun C : SymmetricCubic => C.form u u u) hB
      unfold CA; simpa only [referenceCubic, LinearMap.compr₂_apply, metricBilin_apply] using hb
    · refine ⟨(LinearEquiv.neg ℝ).trans F₀, fun u => ?_, fun u => ?_⟩
      · change tangentMetricDual P e (F₀ (-u)) (F₀ (-u)) = gA u u
        simp only [map_neg, neg_apply, neg_neg]; exact hmet u u
      · have hb := congrArg (fun C : SymmetricCubic => C.form u u u) hB
        simp only [scalarCubic, referenceCubic, LinearMap.smul_apply, LinearMap.compr₂_apply, metricBilin_apply, smul_eq_mul] at hb
        have hb' : curry3 P.form (F₀ u : E) (F₀ u : E) (F₀ u : E) = (-1 : ℝ) * CA u u u := hb
        change P.form ![(F₀ (-u) : E), (F₀ (-u) : E), (F₀ (-u) : E)] = CA u u u
        rw [← curry3_apply, map_neg, Submodule.coe_neg]
        simp only [map_neg, neg_apply, neg_neg]; linarith
  obtain ⟨F₁, hm₁, hc₁⟩ := hF₁
  have hte : traceAt P e e = 3 := traceAt_self P e he
  let projE : E →ₗ[ℝ] tangent P e :=
    (LinearMap.id - ((1 / 3 : ℝ) • (traceAt P e).toLinearMap).smulRight e).codRestrict
      (tangent P e) (fun x => by
        change traceAt P e (x - ((1 / 3 : ℝ) * traceAt P e x) • e) = 0
        rw [map_sub, map_smul, hte, smul_eq_mul]; ring)
  let A : E ≃ₗ[ℝ] Albert :=
    { toFun x := (traceAt P e x / 3) • (1 : Albert) + (F₁.symm (projE x) : Albert)
      invFun y := (Glennie.trace y / 3) • e + (F₁ (project y) : E)
      left_inv x := by
        dsimp only
        have ht : Glennie.trace ((traceAt P e x / 3) • (1 : Albert) + (F₁.symm (projE x) : Albert)) = traceAt P e x := by
          rw [trace_add, trace_smul, trace_unit, trace_V]; ring
        have hp' : project ((traceAt P e x / 3) • (1 : Albert) + (F₁.symm (projE x) : Albert)) = F₁.symm (projE x) := by
          rw [map_add, map_smul, project_V, show project (1 : Albert) = 0 by apply Subtype.ext; simp [Glennie.traceless, trace_unit], smul_zero, zero_add]
        rw [ht, hp', F₁.apply_symm_apply]
        change (traceAt P e x / 3) • e + (x - ((1 / 3 : ℝ) * traceAt P e x) • e) = x; module
      right_inv y := by
        dsimp only
        have hv : traceAt P e (F₁ (project y) : E) = 0 := (F₁ (project y)).property
        have ht : traceAt P e ((Glennie.trace y / 3) • e + (F₁ (project y) : E)) = Glennie.trace y := by
          rw [map_add, map_smul, hte, hv, smul_eq_mul]; ring
        have hp' : projE ((Glennie.trace y / 3) • e + (F₁ (project y) : E)) = F₁ (project y) :=
          Subtype.ext (by change ((Glennie.trace y / 3) • e + (F₁ (project y) : E)) - ((1 / 3 : ℝ) * traceAt P e _) • e = _; rw [ht]; module)
        rw [ht, hp', F₁.symm_apply_apply]
        change (Glennie.trace y / 3) • (1 : Albert) + (y - (Glennie.trace y / 3) • (1 : Albert)) = y; module
      map_add' _ _ := by simp only [map_add, add_div, add_smul, Submodule.coe_add]; abel
      map_smul' _ _ := by simp only [map_smul, smul_eq_mul, mul_div_assoc, mul_smul, Submodule.coe_smul, RingHom.id_apply, smul_add] }
  refine ⟨A, ?_, fun x => ?_⟩
  · have hp0 : projE e = 0 := Subtype.ext (by change e - ((1 / 3 : ℝ) * traceAt P e e) • e = 0; rw [hte]; module)
    change (traceAt P e e / 3) • (1 : Albert) + (F₁.symm (projE e) : Albert) = 1
    rw [hte, hp0, map_zero, ZeroMemClass.coe_zero]; norm_num
  · let t := traceAt P e x / 3; let u := F₁.symm (projE x)
    have hx : x = t • e + (F₁ u : E) := by
      rw [F₁.apply_symm_apply]; change x = (traceAt P e x / 3) • e + (x - ((1 / 3 : ℝ) * traceAt P e x) • e); module
    change nativeCubic (t • (1 : Albert) + (u : Albert)) = cubic P x
    rw [nativeCubic_split, hx, cubic_split_E P e he t (F₁ u), hm₁ u, hc₁ u]

end Helpers

theorem intrinsic_local_reconstruction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (P : BasedCubic E) (e : E) (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x)
    (hMatch : ∃ F : NativeTangent ≃ₗ[ℝ] tangent P e,
      (∀ x y : NativeTangent,
        metric P e (F x : E) (F y : E) = nativeMetric x y) ∧
      (∀ x y z : NativeTangent,
        independentCurvature P e (F x) (F y) (F z) =
          F (nativeCurvature x y z))) :
    Nonempty (ReconstructionResult P e) := by
  obtain ⟨A, hunit, hnorm⟩ := exists_norm_unit_equiv P e he hp hMatch
  have ht0 (x : E) : traceAt P e x = Glennie.trace (A x) := by
    rw [traceAt, fderiv_from_norm_iso P A hnorm e x, hunit]
    simp only [nativeAdjoint, jordan_unit_left, trace_unit, inner_unit_left]; norm_num
  have hraw (x y : E) : rawPair P e x y = Glennie.inner (A x) (A y) := by
    rw [rawPair_apply, ht0, ht0, hessian_at_unit_from_norm_iso P e A hunit hnorm]; ring
  have hmet (x y : E) : metric P e x y = Glennie.inner (A x) (A y) / 3 := by
    linarith [rawPair_eq_three_metric P e he x y, hraw x y]
  have hadj (x : E) : A (adjoint P e x) = nativeAdjoint (A x) := by
    obtain ⟨y, hy⟩ := A.surjective (A (adjoint P e x) - nativeAdjoint (A x))
    refine sub_eq_zero.mp ((Glennie.inner_self_eq_zero _).mp ?_)
    rw [Glennie.inner_sub_left, ← hy, ← hraw, adjoint_pairing P e he hp x y,
      fderiv_from_norm_iso P A hnorm, sub_self]
  have hj0 (x y : E) : A (product P e x y) = jordan (A x) (A y) := by
    simp only [product, map_smul, map_sub, map_add, hadj, ht0, hraw, hunit]
    rw [nativeAdjoint_cross]; module
  have hG (x y : E) : A (ambientConnection P e x y) = -jordan (A x) (A y) := by
    rw [ambientConnection_at_one P e he hp, map_neg, hj0]
  have hR (u v w : E) : A (ambientCurvature P e u v w) =
      -(jordan (A u) (jordan (A v) (A w)) - jordan (A v) (jordan (A u) (A w))) := by
    rw [ambientCurvature_at_one P e he hp, map_neg, map_sub, hj0, hj0, hj0, hj0]
  let t : E → ℝ := fun x => traceAt P e x
  let j : E → E → E := product P e
  have ht : ∀ x, t x = Glennie.trace (A x) := ht0
  have hj : ∀ x y, A (j x y) = jordan (A x) (A y) := hj0
  let mapT (T : Local.Triple E) : Glennie.Compact.Affine20.Triple := fun f i => A (T f i)
  let pullT (T : Glennie.Compact.Affine20.Triple) : Local.Triple E := fun f i => A.symm (T f i)
  have hmp (T : Glennie.Compact.Affine20.Triple) : mapT (pullT T) = T := funext fun f => funext fun i => A.apply_symm_apply _
  have hframe (p : Fin 3 → E) : Local.Frame e t j p ↔ Glennie.Frame (fun i => A (p i)) :=
    ⟨fun h => ⟨fun i => (ht _).symm.trans (h.trace_one i), fun i => (hj _ _).symm.trans (congrArg A (h.idempotent i)),
      fun i k hik => (hj _ _).symm.trans ((congrArg A (h.orthogonal i k hik)).trans (map_zero A)),
      by simpa only [map_add, hunit] using congrArg A h.sum_unit⟩,
     fun h => ⟨fun i => (ht _).trans (h.trace_one i), fun i => A.injective ((hj _ _).trans (h.idempotent i)),
      fun i k hik => A.injective ((hj _ _).trans ((h.orthogonal i k hik).trans (map_zero A).symm)),
      A.injective (by simpa only [map_add, hunit] using h.sum_unit)⟩⟩
  have hpair (x y : E) : Local.pairing t j x y = Glennie.inner (A x) (A y) := by rw [Local.pairing, ht, hj]; rfl
  have hquad (x z : E) : A (Local.quad j x z) = U (A x) (A z) := by simp only [Local.quad, U, map_sub, map_smul, hj]
  have henc (p : Fin 3 → E) : A (Local.encoder p) = Glennie.encoder (fun i => A (p i)) := by simp only [Local.encoder, Glennie.encoder, map_sub]
  have hpow (p : Fin 3 → E) (s : Fin 2) : A (Local.power j p s) = Glennie.SubmissionR03.framePower (fun i => A (p i)) s := by
    fin_cases s <;> simp [Local.power, Glennie.SubmissionR03.framePower, Glennie.SubmissionR03.b0, henc, hj]
  have hled (T : Local.Triple E) : Local.ledger t j T = Glennie.SubmissionR03.fullLedger (mapT T) :=
    Prod.ext (funext fun i => funext fun k => funext fun l => by change t (j (j _ _) _) = _; rw [ht, hj, hj]; rfl)
      (Prod.ext (funext fun _ => funext fun _ => hpair _ _)
        (Prod.ext (funext fun _ => funext fun _ => hpair _ _) (funext fun _ => funext fun _ => hpair _ _)))
  have hq26 (T : Local.Triple E) : Local.q26 t j T = Glennie.SubmissionR03.q26 (mapT T) := by
    have h1 (v : Fin 3) (s : Fin 2) : Local.qSingle t j T v s = Glennie.SubmissionR03.qSingle (mapT T) v s := by simp only [Local.qSingle, Glennie.SubmissionR03.qSingle, hpair, hpow]; rfl
    have h2 (v w : Fin 3) (s r : Fin 2) : Local.qPair t j T v w s r = Glennie.SubmissionR03.qPair (mapT T) v w s r := by simp only [Local.qPair, Glennie.SubmissionR03.qPair, hpair, hpow]; rfl
    have h3 (s r u : Fin 2) : Local.qTriple t j T s r u = Glennie.SubmissionR03.qTriple (mapT T) s r u := by change t (j (j _ _) _) = _; rw [ht, hj, hj, hpow, hpow, hpow]; rfl
    funext n; fin_cases n <;> simp [Local.q26, Glennie.SubmissionR03.q26, Glennie.SubmissionR03.f0, Glennie.SubmissionR03.f1, Glennie.SubmissionR03.f2, Glennie.SubmissionR03.b0, Glennie.SubmissionR03.b1, h1, h2, h3]
  have hscore (T : Local.Triple E) : Local.score e t j T = Glennie.SubmissionR03.score (mapT T) := by
    have hhalf (x : E) : A (Local.half e x) = Glennie.SubmissionR03.halfAmplitude (A x) := by simp only [Local.half, Glennie.SubmissionR03.halfAmplitude, map_smul, map_add, hunit]; norm_num
    have hdelta (x y z w rho : E) : Local.delta t j x y z w rho = Glennie.SubmissionR03.delta (A x) (A y) (A z) (A w) (A rho) := by
      simp only [Local.delta, Local.contrast, Glennie.SubmissionR03.delta, Glennie.SubmissionR03.contrast, hpair, map_sub, hquad]
    simp only [Local.score, Glennie.SubmissionR03.score, hdelta, hhalf, hunit, henc]; rfl
  let autToNative (g : Local.Automorphism t j) : CompactAutomorphism :=
    { equiv := A.symm.trans (g.equiv.trans A)
      map_jordan x y := by
        change A (g.equiv (A.symm (jordan x y))) = _
        rw [show A.symm (jordan x y) = j (A.symm x) (A.symm y) from A.injective (by simp [hj]), g.map_product, hj]; rfl
      map_trace x := by change Glennie.trace (A (g.equiv (A.symm x))) = _; rw [← ht, g.map_trace, ht, A.apply_symm_apply] }
  have horb (S T : Local.Triple E) :
      T ∈ Local.orbit t j S ↔ ∃ k : CompactAutomorphism, Glennie.SubmissionR03.mapAtoms k (mapT S) = mapT T :=
    ⟨fun ⟨g, hg⟩ => ⟨autToNative g, funext fun f => funext fun i => by change A (g.equiv (A.symm (A (S f i)))) = _; rw [A.symm_apply_apply, ← hg]; rfl⟩,
     fun ⟨k, hk⟩ => ⟨{ equiv := A.trans (k.equiv.trans A.symm), map_product := fun _ _ => A.injective (by simp [hj, k.map_jordan]), map_trace := fun _ => by simp [ht, k.map_trace] },
      funext fun f => funext fun i => A.injective (by change A (A.symm (k.equiv (A (S f i)))) = _; rw [A.apply_symm_apply]; exact congrFun (congrFun hk f) i)⟩⟩
  obtain ⟨V1, hV1, hb1, secPos, secNeg, hcP, hcN, hfP, hfN, _, _, hlP, hlN, hpP, hpN, hcov, hdisj, h20⟩ := Glennie.SubmissionR03.nearby_fibres_two_orbits
  obtain ⟨V2, hV2, hb2, htest⟩ := Glennie.SubmissionR03.local_q26_score_orbit_test
  have hcontBack : Continuous (fun c : Fin 3 → Fin 3 → Albert.Coordinates => (fun f i => A.symm (Albert.coordinateLinearEquiv.symm (c f i)) : Local.Triple E)) :=
    continuous_pi fun f => continuous_pi fun i => ((Albert.coordinateLinearEquiv.symm.trans A.symm).toLinearMap.continuous_of_finiteDimensional).comp ((continuous_apply i).comp (continuous_apply f))
  let V := V1 ∩ V2
  have hphi_adm (T : Local.Triple E) (hT : Local.Admitted e t j V T) :
      Glennie.phi (A (Local.encoder (T 0))) (A (Local.encoder (T 1))) (A (Local.encoder (T 2))) ≠ 0 := by
    have hs := (htest (mapT T) (mapT T) (fun f => (hframe _).mp (hT.1 f)) (fun f => (hframe _).mp (hT.1 f)) (hled T ▸ hT.2.2)).1
    rw [Glennie.SubmissionR03.score_eq_two_phi] at hs
    intro hz; apply hs; dsimp [Glennie.SubmissionR03.phiOf, Glennie.SubmissionR03.f0, Glennie.SubmissionR03.f1, Glennie.SubmissionR03.f2]
    rw [← henc, ← henc, ← henc, hz, mul_zero]
  refine ⟨{
    A := A, map_unit := hunit, map_norm := hnorm, map_metric := hmet, map_raw_pairing := hraw,
    map_trace := ht, map_product := hj, map_connection := hG, map_curvature := hR,
    V := V, V_open := hV1.inter hV2, flat_mem := by show Glennie.SubmissionR03.encode20 (Local.ledger t j (pullT _)) ∈ V; rw [hled, hmp]; exact ⟨hb1, hb2⟩,
    two_orbits := ?_, score_complete := ?_,
    q26_iff_ledger := fun T S hT hS => by
      change Local.q26 t j T = Local.q26 t j S ↔ Local.ledger t j T = Local.ledger t j S
      rw [hq26, hq26, hled, hled]; exact Glennie.SubmissionR03.q26_eq_iff_fullLedger_eq _ _ (fun f => (hframe _).mp (hT f)) (fun f => (hframe _).mp (hS f)),
    score_eq_two_phi := fun T => by
      change Local.score e t j T = 2 * Local.phi t j (Local.encoder (T 0)) (Local.encoder (T 1)) (Local.encoder (T 2))
      have hphi_eq : Local.phi t j (Local.encoder (T 0)) (Local.encoder (T 1)) (Local.encoder (T 2)) =
          Glennie.phi (A (Local.encoder (T 0))) (A (Local.encoder (T 1))) (A (Local.encoder (T 2))) := by
        simp only [Local.phi, Glennie.phi, hpair, map_sub, hquad, hj]
      rw [hscore, hphi_eq, henc, henc, henc]; exact Glennie.SubmissionR03.score_eq_two_phi _,
    atoms_generate := ?_, atom_stabilizer := ?_, atom_derivation := ?_ }⟩
  · refine ⟨fun b => pullT (secPos b), fun b => pullT (secNeg b),
      (hcontBack.comp_continuousOn hcP).mono Set.inter_subset_left, (hcontBack.comp_continuousOn hcN).mono Set.inter_subset_left,
      fun b hb f => (hframe _).mpr (by simpa [pullT] using hfP b hb.1 f),
      fun b hb f => (hframe _).mpr (by simpa [pullT] using hfN b hb.1 f),
      fun b hb => by show Local.ledger t j _ = _; rw [hled, hmp]; exact hlP b hb.1,
      fun b hb => by show Local.ledger t j _ = _; rw [hled, hmp]; exact hlN b hb.1,
      fun b hb => by show 0 < Local.score e t j _; rw [hscore, hmp, Glennie.SubmissionR03.score_eq_two_phi]; linarith [hpP b hb.1],
      fun b hb => by show Local.score e t j _ < 0; rw [hscore, hmp, Glennie.SubmissionR03.score_eq_two_phi]; linarith [hpN b hb.1],
      fun b hb => ?_, fun b hb => ?_, fun b hb => ?_⟩
    · ext T; change T ∈ Local.fibre54 e t j b ↔ T ∈ Local.orbit t j _ ∪ Local.orbit t j _
      simp only [Local.fibre54, Set.mem_union, Set.mem_ofPred_eq, horb, hmp, hled, hframe]
      exact Set.ext_iff.mp (hcov b hb.1) (mapT T)
    · rw [Set.disjoint_left]; intro T hN hP
      change T ∈ Local.orbit t j _ at hN hP; rw [horb, hmp] at hN hP
      exact Set.disjoint_left.mp (hdisj b hb.1) hN hP
    · ext T; change T ∈ Local.fibre20 e t j b ↔ T ∈ Local.fibre54 e t j b
      simp only [Local.fibre20, Local.fibre54, Set.mem_ofPred_eq, hframe, hled]
      exact Set.ext_iff.mp (h20 b hb.1) (mapT T)
  · intro T S hT hS hb
    obtain ⟨hs, hiff⟩ := htest (mapT T) (mapT S) (fun f => (hframe _).mp (hT f)) (fun f => (hframe _).mp (hS f)) (hled T ▸ hb.2)
    change Local.score e t j T ≠ 0 ∧ (T ∈ Local.orbit t j S ↔ Local.q26 t j T = Local.q26 t j S ∧ Local.SameSign e t j T S)
    exact ⟨by rwa [hscore], by rwa [horb, hq26, hq26, Local.SameSign, hscore, hscore]⟩
  · intro T hT K hK hAtoms
    let L : Submodule ℝ Albert := K.map A.toLinearMap
    have hu : e ∈ K := by rw [← (hT.1 0).sum_unit]; exact K.add_mem (K.add_mem (hAtoms 0 0) (hAtoms 0 1)) (hAtoms 0 2)
    have hL : L = ⊤ := (Glennie.SubmissionR03.phi_nonzero_generation_stabilizer _ _ _ (hphi_adm T hT)).1 L ⟨e, hu, hunit⟩
      (by rintro _ ⟨p, hpK, rfl⟩ _ ⟨q, hqK, rfl⟩; exact ⟨j p q, hK p hpK q hqK, hj p q⟩)
      ⟨Local.encoder (T 0), K.sub_mem (hAtoms 0 2) (hAtoms 0 0), rfl⟩
      ⟨Local.encoder (T 1), K.sub_mem (hAtoms 1 2) (hAtoms 1 0), rfl⟩
      ⟨Local.encoder (T 2), K.sub_mem (hAtoms 2 2) (hAtoms 2 0), rfl⟩
    apply top_unique; intro x _; obtain ⟨y, hy, hyx⟩ := (by rw [hL]; trivial : A x ∈ L); exact A.injective hyx ▸ hy
  · intro T hT g hfix
    have hf (f i : Fin 3) : g.equiv (T f i) = T f i := congrFun (congrFun hfix f) i
    have hk := (Glennie.SubmissionR03.phi_nonzero_generation_stabilizer _ _ _ (hphi_adm T hT)).2.1 (autToNative g)
      (by simp [autToNative, Local.encoder, hf]) (by simp [autToNative, Local.encoder, hf]) (by simp [autToNative, Local.encoder, hf])
    ext x; apply A.injective; simpa [autToNative] using congrArg (fun f : Albert ≃ₗ[ℝ] Albert => f (A x)) hk
  · intro T hT D hD hkill
    let D' : Albert →ₗ[ℝ] Albert := A.toLinearMap.comp (D.comp A.symm.toLinearMap)
    have hD' := (Glennie.SubmissionR03.phi_nonzero_generation_stabilizer _ _ _ (hphi_adm T hT)).2.2 D'
      (fun p q => by
        change A (D (A.symm (jordan p q))) = _
        rw [show A.symm (jordan p q) = j (A.symm p) (A.symm q) from A.injective (by simp [hj]), hD, map_add, hj, hj, A.apply_symm_apply, A.apply_symm_apply]; rfl)
      (by simp [D', Local.encoder, hkill]) (by simp [D', Local.encoder, hkill]) (by simp [D', Local.encoder, hkill])
    ext x; apply A.injective; simpa [D'] using congrArg (fun L : Albert →ₗ[ℝ] Albert => L (A x)) hD'

end
end Glennie.SubmissionR04Intrinsic
