/- Unified independent native and admitted orbit-quotient statement surface. -/
module
public import Glennie.Compact.LocalOrbitQuotientR01
public import Glennie.Compact.NearbyOrbitsClosed
public import Glennie.Compact.ReadoutRobustnessR01
public import Glennie.Diagonalization
public import Glennie.NativeGenerationEndpointR01
public import Mathlib.Analysis.Quaternion
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Basic
public import AlbertGeometry.BasedNormAdjointTransport
public import AlbertGeometry.RecognitionFromCurvature
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace Glennie.SubmissionR03
noncomputable section
open Glennie
open Glennie.Compact.Affine20

/-- Named Fin indices avoid compiler-generated numeral witnesses in the statement. -/
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

/-- Nonzero Phi for arbitrary native elements forces full unital generation
and fixes the pointwise simultaneous automorphism stabilizer. -/
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
  have hgen (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
      (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) : K = ⊤ :=
    Glennie.NativeGenerationEndpointR01.eq_top_of_phi_ne_zero K h1 hJ x y z hx hy hz hphi
  refine ⟨hgen, fun g hx hy hz => LinearEquiv.ext fun t => ?_,
    fun D hD hx hy hz => LinearMap.ext fun t => ?_⟩
  · have hK := hgen (LinearMap.eqLocus g.equiv.toLinearMap LinearMap.id) g.map_unit
      (fun p hp q hq => (g.map_jordan p q).trans (congrArg₂ jordan hp hq)) hx hy hz
    exact (hK ▸ trivial : t ∈ LinearMap.eqLocus g.equiv.toLinearMap LinearMap.id)
  · have h1 : D 1 = 0 := by
      have h := hD 1 1
      rw [jordan_unit_left, jordan_unit_right, jordan_unit_left] at h
      exact (add_sub_cancel_left (D 1) (D 1)).symm.trans (by rw [← h, sub_self])
    have hK := hgen (LinearMap.ker D) h1 (fun p hp q hq => by
      change D _ = 0; rw [hD, LinearMap.mem_ker.mp hp, LinearMap.mem_ker.mp hq]; simp) hx hy hz
    exact LinearMap.mem_ker.mp (hK ▸ trivial : t ∈ LinearMap.ker D)

theorem q26_eq_iff_fullLedger_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q26 T = q26 S ↔ fullLedger T = fullLedger S := by
  change Glennie.Compact.NativeQFamilyLedger.q26 T =
      Glennie.Compact.NativeQFamilyLedger.q26 S ↔
      Glennie.Compact.Affine20.ledger54 T = Glennie.Compact.Affine20.ledger54 S
  exact Glennie.Compact.NativeQFamilyLedger.q26_eq_iff_ledger54_eq T S hT hS

/-- Q20 is the final twenty Q26 readings; the first six are fixed on actual frames. -/
def q20 (T : Triple) : Fin 20 → ℝ :=
  fun i => q26 T ⟨i.val + 6, Nat.add_lt_add_right i.2 6⟩

/-- On actual ordered frames, Q20 still determines the complete 54-trace ledger. -/
theorem q20_eq_iff_fullLedger_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q20 T = q20 S ↔ fullLedger T = fullLedger S := by
  rw [← q26_eq_iff_fullLedger_eq T S hT hS]
  refine ⟨fun h => funext fun n => ?_, fun h => funext fun i => congrFun h _⟩
  have hs (v : Fin 3) (s : Fin 2) : qSingle T v s = qSingle S v s := by
    change Glennie.Compact.NativeQFamilyLedger.qSingle T v s =
      Glennie.Compact.NativeQFamilyLedger.qSingle S v s
    rw [Glennie.Compact.NativeQFamilyLedger.qSingle_frame T hT,
      Glennie.Compact.NativeQFamilyLedger.qSingle_frame S hS]
  by_cases hn : n.val < 6
  · obtain ⟨m, rfl⟩ : ∃ m : Fin 6, n = ⟨m.val, m.2.trans (by decide)⟩ := ⟨⟨n.val, hn⟩, rfl⟩
    fin_cases m <;> simp [q26, hs]
  · have h6 : (⟨(⟨n.val - 6, by omega⟩ : Fin 20).val + 6,
        Nat.add_lt_add_right (by omega) 6⟩ : Fin 26) = n := by ext; dsimp; omega
    simpa [q20, h6] using congrFun h ⟨n.val - 6, by omega⟩

private theorem q26_eq_source (T : Triple) :
    q26 T = Glennie.Compact.NativeQFamilyLedger.q26 T := by rfl
private theorem f0_eq : f0 = (0 : Fin 3) := rfl
private theorem f1_eq : f1 = (1 : Fin 3) := rfl
private theorem f2_eq : f2 = (2 : Fin 3) := rfl
private theorem delta_eq (x y z a rho : Albert) :
    delta x y z a rho = Glennie.Compact.OperationalPhi.delta x y z a rho := rfl
private theorem halfAmplitude_eq (x : Albert) :
    halfAmplitude x = Glennie.Compact.OperationalPhi.halfAmplitude x := rfl
private theorem phiOf_eq (T : Triple) :
    phiOf T = Glennie.Compact.Sections.phiOf T := by
  simp only [phiOf, Glennie.Compact.Sections.phiOf, f0_eq, f1_eq, f2_eq]
theorem score_eq_source (T : Triple) :
    score T = Glennie.Compact.LocalContrast.score T := by
  simp only [score, Glennie.Compact.LocalContrast.score,
    f0_eq, f1_eq, f2_eq, delta_eq, halfAmplitude_eq]

theorem division_free (x y z : Albert) :
    4 * delta x y z (halfAmplitude x) y - delta x y z x y -
      delta x y z 1 y = 2 * phi x y z := by
  rw [delta_eq, halfAmplitude_eq, delta_eq, delta_eq]
  exact Glennie.Compact.OperationalPhi.phi_division_free x y z

theorem score_eq_two_phi (T : Triple) : score T = 2 * phiOf T := by
  rw [score_eq_source, phiOf_eq]
  exact Glennie.Compact.LocalContrast.score_eq_two_phi T

theorem atoms_generate_of_score
    (T : Triple) (hT : ∀ a, Frame (T a)) (hs : score T ≠ 0)
    (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (hAtoms : ∀ a i, T a i ∈ K) : K = ⊤ := by
  have hphi : phiOf T ≠ 0 := fun h0 => hs (by rw [score_eq_two_phi, h0, mul_zero])
  have hu : (1 : Albert) ∈ K := by
    rw [← (hT 0).sum_unit]
    exact K.add_mem (K.add_mem (hAtoms 0 0) (hAtoms 0 1)) (hAtoms 0 2)
  exact Glennie.NativeGenerationEndpointR01.eq_top_of_phi_ne_zero K hu hJ
    (encoder (T f0)) (encoder (T f1)) (encoder (T f2))
    (K.sub_mem (hAtoms f0 2) (hAtoms f0 0))
    (K.sub_mem (hAtoms f1 2) (hAtoms f1 0))
    (K.sub_mem (hAtoms f2 2) (hAtoms f2 0)) hphi

private theorem flatBase_eq_source : flatBase = Glennie.Compact.FrameTopology.flatBaseTriple := rfl
theorem flatBase_eq_sections : flatBase = Glennie.Compact.Sections.flatBase := rfl
theorem fullLedger_eq_fn : fullLedger = Glennie.Compact.Affine20.ledger54 := rfl
private theorem mapAtoms_eq_fn : mapAtoms = Glennie.Compact.Affine20.mapAtoms := rfl
private theorem q26_eq_fn : q26 = Glennie.Compact.NativeQFamilyLedger.q26 := rfl
private theorem phiOf_eq_fn : phiOf = Glennie.Compact.Sections.phiOf := funext phiOf_eq
private theorem score_eq_fn : score = Glennie.Compact.LocalContrast.score := funext score_eq_source

theorem nearby_sign_rigidity :
    ∃ V : Set Ledger54, IsOpen V ∧ fullLedger flatBase ∈ V ∧
      ∀ T S : Triple, (∀ a : Fin 3, Frame (T a)) →
        (∀ a : Fin 3, Frame (S a)) → fullLedger T ∈ V →
        fullLedger T = fullLedger S →
        ((phiOf T < 0 ∧ phiOf S < 0) ∨ (0 < phiOf T ∧ 0 < phiOf S)) →
        ∃ k : CompactAutomorphism, mapAtoms k S = T := by
  rw [flatBase_eq_source, fullLedger_eq_fn, phiOf_eq_fn, mapAtoms_eq_fn]
  exact Glennie.Compact.NearbyOrbitsClosed.nearby_sign_rigidity_unconditional

/-- A specific native near-flat full-fiber margin in a supplied open ledger neighborhood. -/
theorem near_flat_scalar_margin :
    ∃ V : Set Ledger54, IsOpen V ∧ fullLedger flatBase ∈ V ∧
      ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) → fullLedger T ∈ V →
        1 / 27 < |phiOf T| := by
  rw [flatBase_eq_source, fullLedger_eq_fn, phiOf_eq_fn]
  exact Glennie.Compact.NearbyOrbitsClosed.phi_bounded_away_near_flat

/-- The fixed twenty-coordinate affine chart of complete overlap ledgers. -/
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

theorem encode20_eq_fn : encode20 = Glennie.Compact.Affine20.encode20 := rfl
private theorem decode20_eq_fn : decode20 = Glennie.Compact.Affine20.decode20 := rfl
private theorem fibre54_eq_fn : fibre54 = Glennie.Compact.NearbyOrbits.fibre54 := by
  ext b T; simp only [fibre54, Glennie.Compact.NearbyOrbits.fibre54, fullLedger_eq_fn, decode20_eq_fn]
private theorem fibre20_eq_fn : fibre20 = Glennie.Compact.NearbyOrbits.fibre20 := by
  ext b T; simp only [fibre20, Glennie.Compact.NearbyOrbits.fibre20, fullLedger_eq_fn, encode20_eq_fn]
private theorem autOrbit_eq_fn : autOrbit = Glennie.Compact.FlatOrbit.autOrbit := by
  ext S T; simp only [autOrbit, Glennie.Compact.FlatOrbit.autOrbit, mapAtoms_eq_fn]

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
  rw [flatBase_eq_sections, fullLedger_eq_fn, encode20_eq_fn, decode20_eq_fn,
    phiOf_eq_fn, fibre54_eq_fn, fibre20_eq_fn, autOrbit_eq_fn]
  obtain ⟨V, ho, hb, p, n, hcp, hcn, hfp, hfn, hep, hen,
    hlp, hln, hpp, hnn, hcover, hdisj, heq⟩ :=
    Glennie.Compact.NearbyOrbitsClosed.nearby_fibres_two_orbits_unconditional
  have hcoord : Continuous (fun T : Triple => fun a i => Albert.coordinateEquiv (T a i)) :=
    continuous_pi fun a => continuous_pi fun i =>
      Albert.coordinateLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp
        ((continuous_apply i).comp (continuous_apply a))
  exact ⟨V, ho, hb, p, n, hcoord.comp_continuousOn hcp, hcoord.comp_continuousOn hcn,
    hfp, hfn, hep, hen, hlp, hln, hpp, hnn, hcover, hdisj, heq⟩

/-- On the admitted local chart, Q26 plus the nonzero score sign classifies
all actual ordered-frame triples under one simultaneous product-and-trace action. -/
theorem local_q26_score_orbit_test :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∀ T S : Triple, (∀ a, Frame (T a)) → (∀ a, Frame (S a)) →
        encode20 (fullLedger T) ∈ V →
        score T ≠ 0 ∧
        ((∃ k : CompactAutomorphism, mapAtoms k S = T) ↔
          q26 T = q26 S ∧
          ((score T < 0 ∧ score S < 0) ∨ (0 < score T ∧ 0 < score S))) := by
  rw [flatBase_eq_sections, fullLedger_eq_fn, encode20_eq_fn, score_eq_fn, mapAtoms_eq_fn, q26_eq_fn]
  exact Glennie.Compact.NearbyOrbitsClosed.nearby_q26_score_complete

/-- Every compact region of the established admitted chart has a positive
uniform Phi margin for its entire actual ordered-frame fiber. -/
theorem compact_local_phi_margin :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∀ K : Set V, IsCompact K →
        ∃ m > 0, ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) →
          ∀ hb : encode20 (fullLedger T) ∈ V,
            (⟨encode20 (fullLedger T), hb⟩ : V) ∈ K →
              m ≤ |phiOf T| := by
  rw [flatBase_eq_sections, fullLedger_eq_fn, encode20_eq_fn, phiOf_eq_fn]
  let d := Glennie.Compact.LocalOrbitQuotientR01.localData
  refine ⟨d.V, d.openV, d.base, fun K hK => ?_⟩
  obtain ⟨m, hm, hbound⟩ :=
    Glennie.Compact.LocalOrbitQuotientR01.compact_response_margin d K hK
  exact ⟨m, hm, fun T hT hb hmem => hbound ⟨T, hT, hb⟩ hmem⟩

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

private theorem weightedScore_exact (T : Triple) :
    weightedScore (exactReadouts T) = score T := by
  simp only [weightedScore, exactReadouts, score, delta, contrast,
    inner_sub_right, rawPlus, rawMinus]
  ring

private theorem weightedScore_error (noisy exact : Readouts) (ε : ℝ)
    (h : ErrorsAtMost noisy exact ε) :
    |weightedScore noisy - weightedScore exact| ≤ 12 * ε := by
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
  rcases abs_le.mp h₀ with ⟨_, _⟩; rcases abs_le.mp h₁ with ⟨_, _⟩
  rcases abs_le.mp h₂ with ⟨_, _⟩; rcases abs_le.mp h₃ with ⟨_, _⟩
  rcases abs_le.mp h₄ with ⟨_, _⟩; rcases abs_le.mp h₅ with ⟨_, _⟩
  exact abs_le.mpr ⟨by dsimp [weightedScore]; linarith, by dsimp [weightedScore]; linarith⟩

/-- Six absolute-error bounds and a strict observed margin certify the
    native scalar sign; no probability or measurement semantics is assumed. -/
theorem signed_readout_margin (T : Triple) (noisy : Readouts) (ε : ℝ)
    (hε : 0 ≤ ε) (h : ErrorsAtMost noisy (exactReadouts T) ε)
    (hm : 12 * ε < |weightedScore noisy|) :
    (weightedScore noisy < 0 ∧ phiOf T < 0) ∨
    (0 < weightedScore noisy ∧ 0 < phiOf T) := by
  have hb := weightedScore_error noisy (exactReadouts T) ε h
  rw [weightedScore_exact, score_eq_two_phi] at hb
  rcases abs_le.mp hb with ⟨hl, hu⟩
  rcases le_total 0 (weightedScore noisy) with hp | hn
  · rw [abs_of_nonneg hp] at hm
    exact Or.inr ⟨by linarith, by linarith⟩
  · rw [abs_of_nonpos hn] at hm
    exact Or.inl ⟨by linarith, by linarith⟩

/-- The native raw trace norm, used to state perturbation radii independently. -/
def nA (x : Albert) : ℝ := Real.sqrt (inner x x)

private theorem nA_eq_norm (x : Albert) : nA x = ‖x‖ := by
  unfold nA
  rw [← Glennie.native_norm_sq]
  exact Real.sqrt_sq (norm_nonneg x)

/-- On a compact feasible chart region, nearby feasible coordinates recover
an actual frame triple up to one simultaneous automorphism, atom by atom.
Both the true and proposed coordinates must belong to the compact region. -/
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
  rw [flatBase_eq_sections, fullLedger_eq_fn, encode20_eq_fn, phiOf_eq_fn]
  let d := Glennie.Compact.LocalOrbitQuotientR01.localData
  have hcoord : Continuous (fun T : Triple => fun a i => Albert.coordinateEquiv (T a i)) :=
    continuous_pi fun a => continuous_pi fun i =>
      Albert.coordinateLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp
        ((continuous_apply i).comp (continuous_apply a))
  refine ⟨d.V, d.openV, d.base, d.pos, d.neg, hcoord.comp_continuousOn d.contPos,
    hcoord.comp_continuousOn d.contNeg, d.framePos, d.frameNeg, d.chartPos, d.chartNeg,
    d.phiPos, d.phiNeg, fun K hK ζ hζ => ?_⟩
  obtain ⟨η, hη, hrec⟩ :=
    Glennie.Compact.LocalOrbitQuotientR01.compact_feasible_recovery d K hK ζ hζ
  refine ⟨η, hη, fun T hT hb hTK b hbK hdist => ?_⟩
  obtain ⟨g, hg⟩ := hrec ⟨T, hT, hb⟩ hTK b hbK hdist
  refine ⟨g, fun a i => ?_⟩
  have hsection :
      Glennie.Compact.LocalOrbitQuotientR01.branchSection d b
        (Glennie.Compact.LocalOrbitQuotientR01.sheet d ⟨T, hT, hb⟩) =
        (if 0 < Glennie.Compact.Sections.phiOf T then d.pos b.1 else d.neg b.1) := by
    by_cases hp : 0 < Glennie.Compact.Sections.phiOf T <;>
      simp [Glennie.Compact.LocalOrbitQuotientR01.branchSection,
        Glennie.Compact.LocalOrbitQuotientR01.sheet, hp]
  rw [hsection] at hg
  have hbound :
      ‖(T - Glennie.Compact.Affine20.mapAtoms g
        (if 0 < Glennie.Compact.Sections.phiOf T then d.pos b.1 else d.neg b.1)) a i‖ ≤
      ‖T - Glennie.Compact.Affine20.mapAtoms g
        (if 0 < Glennie.Compact.Sections.phiOf T then d.pos b.1 else d.neg b.1)‖ :=
    (norm_le_pi_norm _ i).trans (norm_le_pi_norm _ a)
  simpa only [nA_eq_norm, Pi.sub_apply, Glennie.Compact.Affine20.mapAtoms] using
    hbound.trans_lt hg

/-- A strict six-reading margin selects the correct continuous branch for
compact feasible-coordinate recovery. The proposed chart remains feasible. -/
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
  refine ⟨V, ho, hb, p, n, hcp, hcn, hfp, hfn, hep, hen, hpp, hpn, ?_⟩
  intro K hK ζ hζ
  obtain ⟨η, hη, hrecover⟩ := hrec K hK ζ hζ
  refine ⟨η, hη, ?_⟩
  intro T hT hbT hTK b hbK hdist noisy ε hε herr hm
  obtain ⟨g, hg⟩ := hrecover T hT hbT hTK b hbK hdist
  refine ⟨g, ?_⟩
  rcases signed_readout_margin T noisy ε hε herr hm with hn | hp
  · have hns : ¬ 0 < weightedScore noisy := not_lt_of_ge hn.1.le
    have hnp : ¬ 0 < phiOf T := not_lt_of_ge hn.2.le
    simpa only [if_neg hns, if_neg hnp] using hg
  · simpa only [if_pos hp.1, if_pos hp.2] using hg

def noisyPhi (r : Readouts) : ℝ := weightedScore r / (Nat.cast 2 : ℝ)

/-- Raw six-readout errors and three bounded input displacements certify the
sign, full unital generation, and pointwise stabilizer at the displaced inputs. -/
theorem six_readout_displaced_generation
    (T : Triple) (noisy : Readouts) (x' y' z' : Albert)
    (ε ξ R δ : ℝ) (hξ : 0 ≤ ξ) (hR : 0 ≤ R)
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
  have hb := weightedScore_error noisy (exactReadouts T) ε hreadout
  rw [weightedScore_exact, score_eq_two_phi, phiOf] at hb
  rcases abs_le.mp hb with ⟨hl1, hu1⟩
  have hdisp := Glennie.Compact.ReadoutRobustnessR01.phi_displacement_18
    (encoder (T f0)) (encoder (T f1)) (encoder (T f2))
    x' y' z' R δ hR hx hy hz hx' hy' hz' hdx hdy hdz
  rcases abs_le.mp hdisp with ⟨hl2, hu2⟩
  have hnp : noisyPhi noisy = weightedScore noisy / 2 := by
    change weightedScore noisy / (Nat.cast 2 : ℝ) = _
    norm_num
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hdx
  have hR8 : 0 ≤ R ^ 8 := by positivity
  have hsign : (noisyPhi noisy < 0 ∧ phi x' y' z' < 0) ∨
      (0 < noisyPhi noisy ∧ 0 < phi x' y' z') := by
    rcases le_total 0 (noisyPhi noisy) with hp | hn
    · rw [abs_of_nonneg hp] at hmargin
      exact Or.inr ⟨by nlinarith, by nlinarith⟩
    · rw [abs_of_nonpos hn] at hmargin
      exact Or.inl ⟨by nlinarith, by nlinarith⟩
  have hnz : phi x' y' z' ≠ 0 := by rcases hsign with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
  obtain ⟨hgen, hstab, _⟩ := phi_nonzero_generation_stabilizer x' y' z' hnz
  exact ⟨hsign, hgen, hstab⟩

/-- The coordinatewise special Jordan product in arbitrary Euclidean dimension. -/
def diagonalNProduct {n : ℕ} (a b : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp (Nat.cast 2 : ENNReal) (fun i => a i * b i)

/-- A uniform all-input defect bounds the degree-nine scalar on any
radius-bounded triple for every finite coordinatewise Euclidean target. -/
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
  exact Glennie.Compact.ReadoutRobustnessR01.null_defect_response_radius
    Glennie.Compact.ReadoutRobustnessR01.diagonalNProduct f hf
    (fun a b c => by ext i; exact sub_mul (a i) (b i) (c i))
    (fun a b c => by ext i; exact mul_sub (a i) (b i) (c i))
    Glennie.Compact.ReadoutRobustnessR01.diagonalN_product_norm
    Glennie.Compact.ReadoutRobustnessR01.diagonalN_quadratic_norm
    Glennie.Compact.ReadoutRobustnessR01.diagonalN_phi_zero
    μ R hμ hR hdef x y z hx hy hz

private theorem frame_radius (p : Fin 3 → Albert) (hp : Frame p) :
    nA (encoder p) ≤ Real.sqrt 2 := by
  rw [nA_eq_norm]
  have hs : ‖encoder p‖ ^ 2 = 2 := (native_norm_sq _).trans (frame_encoder_norm p hp)
  have hr : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [norm_nonneg (encoder p), Real.sqrt_nonneg (2 : ℝ)]

private theorem frame_noisy_defect_lower_of_response
    (T : Triple) (noisy : Readouts) (ε μ : ℝ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hresp : |phiOf T| ≤ 38 * μ * (Real.sqrt 2) ^ 9) :
    (|weightedScore noisy| - 12 * ε) / (1216 * Real.sqrt 2) ≤ μ := by
  have hb := weightedScore_error noisy (exactReadouts T) ε hreadout
  rw [weightedScore_exact, score_eq_two_phi] at hb
  have htri : |weightedScore noisy| - 12 * ε ≤ 2 * |phiOf T| := by
    have := (abs_sub_abs_le_abs_sub (weightedScore noisy) (2 * phiOf T)).trans hb
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
    linarith
  have hr9 : (Real.sqrt (2 : ℝ)) ^ 9 = 16 * Real.sqrt 2 := by
    calc (Real.sqrt (2 : ℝ)) ^ 9 = ((Real.sqrt (2 : ℝ)) ^ 2) ^ 4 * Real.sqrt 2 := by ring
      _ = 16 * Real.sqrt 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
  rw [hr9] at hresp
  have hr : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- An actual-frame noisy score forces a uniform multiplication defect for
any norm-preserving linear map into a coordinatewise Euclidean target. -/
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
  frame_noisy_defect_lower_of_response T noisy ε μ hreadout
    (diagonalN_defect_response_radius f hf μ (Real.sqrt 2) hμ (Real.sqrt_nonneg 2) hdef
      (encoder (T f0)) (encoder (T f1)) (encoder (T f2))
      (frame_radius _ (hT f0)) (frame_radius _ (hT f1)) (frame_radius _ (hT f2)))

/-- A noisy actual-frame score also forces a defect for an associative
cyclic-trace represented target with its exact product and metric adapters. -/
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
  have hf' (x : Albert) : ‖f x‖ = ‖x‖ := (hf x).trans (nA_eq_norm x)
  have hdef' (a b : Albert) : ‖f (jordan a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖ := by
    simpa only [nA_eq_norm] using hdef a b
  exact frame_noisy_defect_lower_of_response T noisy ε μ hreadout
    (Glennie.Compact.ReadoutRobustnessR01.null_defect_response_radius
      (fun a b => jE a b) f hf'
      (fun a b c => by simp) (fun a b c => by simp)
      (Glennie.Compact.ReadoutRobustnessR01.represented_product_norm (fun a b => jE a b) ρ hj)
      (Glennie.Compact.ReadoutRobustnessR01.represented_quadratic_norm (fun a b => jE a b) ρ hj)
      (Glennie.Compact.ReadoutRobustnessR01.phiWith_eq_zero_of_compatible_trace
        (fun a b => jE a b) (Inner.inner ℝ) ρ.toLinearMap τ hj hB hcyclic)
      μ (Real.sqrt 2) hμ (Real.sqrt_nonneg 2) hdef'
      (encoder (T f0)) (encoder (T f1)) (encoder (T f2))
      ((nA_eq_norm _).symm.trans_le (frame_radius _ (hT f0)))
      ((nA_eq_norm _).symm.trans_le (frame_radius _ (hT f1)))
      ((nA_eq_norm _).symm.trans_le (frame_radius _ (hT f2))))

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

open scoped BigOperators

private abbrev w0 : Albert := ⟨1, 1, 1, 0, 0, 0⟩
private abbrev w1 : Albert := ⟨-1, 0, 1, 0, 0, 0⟩
private abbrev w2 : Albert := ⟨0, 0, 0, (1, 0), (⟨0, 1, 0, 0⟩, 0), (1, 0)⟩
private abbrev w3 : Albert := ⟨0, 0, 0, (0, ⟨0, 0, 1, 0⟩), (0, -1), (⟨0, 0, 0, -1⟩, 0)⟩
private abbrev w4 : Albert := ⟨1, 0, 1, 0, 0, 0⟩
private abbrev w5 : Albert := ⟨0, 0, 0, (⟨-1/2, 0, 0, 0⟩, 0), 0, (⟨1/2, 0, 0, 0⟩, 0)⟩
private abbrev w6 : Albert := ⟨0, 0, 0, (0, ⟨0, 0, -1/2, 0⟩), 0, (⟨0, 0, 0, -1/2⟩, 0)⟩
private abbrev w7 : Albert := ⟨2, 2, 2, (⟨0, 1, 0, 0⟩, 0), (1, 0), (⟨0, 1, 0, 0⟩, 0)⟩
private abbrev w8 : Albert := ⟨0, 0, 0, (⟨0, 0, -1/2, 0⟩, ⟨-1/2, 0, 0, 0⟩), (⟨0, 0, 0, -1/2⟩, ⟨0, 0, 1/2, 0⟩), (0, ⟨-1/2, 0, 0, -1/2⟩)⟩
private abbrev w9 : Albert := ⟨2, 2, 2, (0, ⟨0, 0, 0, 1⟩), (0, ⟨0, 1, 0, 0⟩), (⟨0, 0, -1, 0⟩, 0)⟩
private abbrev w10 : Albert := ⟨0, 0, 0, (⟨1/4, 0, 0, 0⟩, 0), 0, (⟨1/4, 0, 0, 0⟩, 0)⟩
private abbrev w11 : Albert := ⟨0, 0, 0, (0, ⟨0, 0, 1/4, 0⟩), 0, (⟨0, 0, 0, -1/4⟩, 0)⟩
private abbrev w12 : Albert := ⟨-2, 0, 2, (⟨0, -1/2, 0, 0⟩, 0), 0, (⟨0, 1/2, 0, 0⟩, 0)⟩
private abbrev w13 : Albert := ⟨0, 0, 0, (⟨0, 0, 1/4, 0⟩, ⟨1/4, 0, 0, 0⟩), 0, (0, ⟨-1/4, 0, 0, -1/4⟩)⟩
private abbrev w14 : Albert := ⟨-2, 0, 2, (0, ⟨0, 0, 0, -1/2⟩), 0, (⟨0, 0, -1/2, 0⟩, 0)⟩
private abbrev w15 : Albert := ⟨0, 0, 0, (⟨0, 0, -1/4, 0⟩, 0), (⟨0, 0, 0, -1/4⟩, ⟨0, 0, -1/4, 0⟩), (0, ⟨0, 0, 0, 1/4⟩)⟩
private abbrev w16 : Albert := ⟨0, 0, 0, (⟨0, 0, 0, -1/4⟩, ⟨0, 1/4, 1/2, 0⟩), (⟨0, 0, -1/4, 0⟩, ⟨-1/2, 0, 0, -1/4⟩), (⟨0, 0, 0, -1/2⟩, ⟨0, -1/4, 1/4, 0⟩)⟩
private abbrev w17 : Albert := ⟨0, 0, 0, (⟨2, 0, 0, 1/2⟩, ⟨0, 1/2, 0, 0⟩), (⟨0, 2, -1/2, 0⟩, ⟨0, 0, 0, 1/2⟩), (⟨2, 0, 0, 0⟩, ⟨0, 1/2, 1/2, 0⟩)⟩
private abbrev w18 : Albert := ⟨2, 0, 2, (⟨0, 1/2, 0, 0⟩, 0), (1, 0), (⟨0, 1/2, 0, 0⟩, 0)⟩
private abbrev w19 : Albert := ⟨0, 0, 0, (⟨0, 0, -1/4, 0⟩, ⟨-1/4, 0, 0, 0⟩), (⟨0, 0, 0, -1/2⟩, ⟨0, 0, 1/2, 0⟩), (0, ⟨-1/4, 0, 0, -1/4⟩)⟩
private abbrev w20 : Albert := ⟨2, 0, 2, (0, ⟨0, 0, 0, 1/2⟩), (0, ⟨0, 1, 0, 0⟩), (⟨0, 0, -1/2, 0⟩, 0)⟩
private abbrev w21 : Albert := ⟨0, 0, 0, (⟨0, 0, 0, -1/8⟩, ⟨0, 0, 1/8, 0⟩), (⟨0, 0, -1/8, 0⟩, ⟨0, 0, 0, 1/8⟩), (⟨0, 0, 0, 1/8⟩, ⟨0, 0, -1/8, 0⟩)⟩
private abbrev w22 : Albert := ⟨0, 0, 0, (-1, ⟨0, 1/4, 0, 0⟩), (⟨0, 0, 1/4, 0⟩, ⟨0, 0, 0, 1/4⟩), (1, ⟨0, -1/4, 0, 0⟩)⟩
private abbrev w23 : Albert := ⟨4, 4, 4, (⟨0, 2, 1/2, 0⟩, ⟨-1/2, 0, 0, 2⟩), (⟨2, 0, 0, -1/2⟩, ⟨0, 2, -1/2, 0⟩), (⟨0, 2, -2, 0⟩, ⟨1/2, 0, 0, -1/2⟩)⟩
private abbrev w24 : Albert := ⟨0, 0, 0, (⟨0, 0, 1/8, 0⟩, 0), 0, (0, ⟨0, 0, 0, 1/8⟩)⟩
private abbrev w25 : Albert := ⟨0, 0, 0, (⟨0, 0, 0, 1/8⟩, ⟨0, -1/8, -1/4, 0⟩), 0, (⟨0, 0, 0, -1/4⟩, ⟨0, -1/8, 1/8, 0⟩)⟩
private abbrev w26 : Albert := ⟨0, 0, 0, (⟨-1, 0, 0, -1/4⟩, ⟨0, -1/4, 0, 0⟩), 0, (1, ⟨0, 1/4, 1/4, 0⟩)⟩
private def wVal : Fin 27 → Albert := ![w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26]

private def wordRepr (v : Albert) : Fin 27 → ℝ :=
  let a := v.o01.1; let b := v.o01.2; let c := v.o02.1; let d := v.o02.2; let e := v.o12.1; let f := v.o12.2
  ![
  (3 * v.d1 + 4 * (a.imJ + f.re - b.re - c.imK - d.imJ - f.imK) + 6 * (c.re + d.imI + e.imJ - a.imI - b.imK - e.imI)) / 3,
  (v.d2 - v.d0 + 4 * (a.imI + b.imK + e.imJ - e.imI)) / 2,
  (2 * (c.imJ - a.imK - b.imI - d.imK - f.imI - f.imJ) + 3 * c.imI) / 3,
  (a.imK + c.imJ + d.imK + f.imI - b.imI - f.imJ - 3 * d.re) / 3,
  (v.d0 + v.d2 - 2 * v.d1 + 4 * (a.imI + b.imK + e.imI - e.imJ) - 8 * (c.re + d.imI)) / 2,
  e.re - a.re + 4 * (a.imK - c.imJ - d.imK - f.imJ),
  b.imI + f.imI - a.imK - b.imJ - e.imK - f.imJ,
  (2 * (b.re + c.imK + d.imJ + f.imK - a.imJ - f.re) + 3 * (a.imI + e.imI - c.re)) / 3,
  c.imK - d.imJ - 2 * (b.re + f.re),
  (2 * (b.re + c.imK + d.imJ + f.imK - a.imJ - f.re) + 3 * (b.imK - d.imI - e.imJ)) / 3,
  2 * (a.re + e.re) - 4 * c.imI,
  2 * (b.imJ - e.imK) + 4 * d.re,
  e.imI - a.imI,
  (2 * (a.imJ - c.imK - d.imJ - f.imK) + 4 * (b.re - f.re)) / 3,
  -(b.imK + e.imJ),
  (2 * (b.re + f.imK - a.imJ - f.re) - 4 * (c.imK + d.imJ)) / 3,
  (2 * (b.imI + f.imJ - a.imK - c.imJ - d.imK - f.imI)) / 3,
  (a.imK + b.imI + d.imK + f.imI + f.imJ - c.imJ) / 3,
  -(a.imI + e.imI) + 2 * c.re,
  2 * (b.re + d.imJ + f.re - c.imK),
  e.imJ - b.imK + 2 * d.imI,
  (-4 * (a.imK + b.imI + f.imI + f.imJ) + 8 * (d.imK - c.imJ)) / 3,
  (2 * (b.imI + f.imJ - a.imK - f.imI) + 4 * (c.imJ + d.imK)) / 3,
  (a.imJ + f.re - b.re - c.imK - d.imJ - f.imK) / 3,
  4 * (a.imJ + f.imK - b.re - f.re),
  (4 * (a.imK + d.imK + f.imJ - c.imJ) - 8 * (b.imI + f.imI)) / 3,
  (2 * (c.imJ + d.imK + f.imI - b.imI) + 4 * (f.imJ - a.imK)) / 3
]

set_option maxHeartbeats 4000000 in
private theorem wordRepr_sum (v : Albert) : ∑ i : Fin 27, wordRepr v i • wVal i = v := by
  ext <;> simp [Fin.sum_univ_succ, wordRepr, wVal] <;> ring

local macro "jw" : tactic => `(tactic| (ext <;> simp only [witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, octNormSq, Quaternion.normSq_def', Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat, Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add, Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero, Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero, Albert.smul_o01, Albert.smul_o02, Albert.smul_o12] <;> norm_num))

private theorem h1 : nativeMarks f0 = w1 := rfl
private theorem h2 : nativeMarks f1 = w2 := rfl
private theorem h3 : nativeMarks f2 = w3 := by dsimp [nativeMarks, f2]; jw
private theorem h4 : jordan w1 w1 = w4 := by jw
private theorem h5 : jordan w1 w2 = w5 := by jw
private theorem h6 : jordan w1 w3 = w6 := by jw
private theorem h7 : jordan w2 w2 = w7 := by jw
private theorem h8 : jordan w2 w3 = w8 := by jw
private theorem h9 : jordan w3 w3 = w9 := by jw
private theorem h10 : jordan w1 w5 = w10 := by jw
private theorem h11 : jordan w1 w6 = w11 := by jw
private theorem h12 : jordan w1 w7 = w12 := by jw
private theorem h13 : jordan w1 w8 = w13 := by jw
private theorem h14 : jordan w1 w9 = w14 := by jw
private theorem h15 : jordan w2 w6 = w15 := by jw
private theorem h16 : jordan w2 w8 = w16 := by jw
private theorem h17 : jordan w2 w9 = w17 := by jw
private theorem h18 : jordan w4 w7 = w18 := by jw
private theorem h19 : jordan w4 w8 = w19 := by jw
private theorem h20 : jordan w4 w9 = w20 := by jw
private theorem h21 : jordan w5 w8 = w21 := by jw
private theorem h22 : jordan w5 w9 = w22 := by jw
private theorem h23 : jordan w7 w9 = w23 := by jw
private theorem h24 : jordan w1 w15 = w24 := by jw
private theorem h25 : jordan w1 w16 = w25 := by jw
private theorem h26 : jordan w1 w17 = w26 := by jw

private theorem nativeWordValues_eq_wVal : nativeWordValues = wVal := by
  unfold nativeWordValues wordValues wVal
  dsimp only
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
  rfl

private theorem nativeWordValues_sum (v : Albert) : ∑ i : Fin 27, wordRepr v i • nativeWordValues i = v := by
  rw [nativeWordValues_eq_wVal]
  exact wordRepr_sum v

private def wordReprLin (i : Fin 27) : Albert →ₗ[ℝ] ℝ where
  toFun v := wordRepr v i
  map_add' x y := by fin_cases i <;> dsimp [wordRepr] <;> ring
  map_smul' r x := by fin_cases i <;> dsimp [wordRepr] <;> ring

private theorem residual_norm_sq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (v : Fin 27 → F) (p : F) (c : Fin 27 → ℝ) :
    ‖p - ∑ k, c k • v k‖^2 =
      Inner.inner ℝ p p - 2 * (∑ k, c k * Inner.inner ℝ p (v k)) +
        ∑ k, ∑ l, c k * c l * Inner.inner ℝ (v k) (v l) := by
  have hp : Inner.inner ℝ p (∑ k, c k • v k) = ∑ k, c k * Inner.inner ℝ p (v k) := by
    simp only [inner_sum, real_inner_smul_right]
  have hs : ‖∑ k, c k • v k‖^2 = ∑ k, ∑ l, c k * c l * Inner.inner ℝ (v k) (v l) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [real_inner_comm (v l) (v k)]; ring
  rw [norm_sub_sq_real, hp, hs, ← real_inner_self_eq_norm_sq p]

private theorem recognition_core
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (nw : Fin 27 → Albert)
    (hsum : ∀ v : Albert, ∑ i : Fin 27, wordReprLin i v • nw i = v)
    (hnw : nw = nativeWordValues)
    (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (h : Match27 e a j) :
    ∃! L : Albert →ₗ[ℝ] E,
      L 1 = e ∧
      (∀ i : Fin 3, L (nativeMarks i) = a i) ∧
      (∀ x y : Albert, L (jordan x y) = j (L x) (L y)) ∧
      (∀ x y : Albert, Inner.inner ℝ (L x) (L y) = inner x y) ∧
      Function.Injective L ∧ LinearMap.range L = generated e a j := by
  let cw := candidateWordValues e a j
  let L : Albert →ₗ[ℝ] E := ∑ i : Fin 27, (wordReprLin i).smulRight (cw i)
  have hL (v : Albert) : L v = ∑ i : Fin 27, wordReprLin i v • cw i := by
    simp [L, LinearMap.sum_apply]
  have hgram (i k : Fin 27) : Inner.inner ℝ (cw i) (cw k) = inner (nw i) (nw k) := by
    rw [hnw]; exact h.gram i k
  have hmixed (i k l : Fin 27) : Inner.inner ℝ (j (cw i) (cw k)) (cw l) =
      inner (jordan (nw i) (nw k)) (nw l) := by
    rw [hnw]; exact h.mixed i k l
  have hprod_sq (i k : Fin 27) : Inner.inner ℝ (j (cw i) (cw k)) (j (cw i) (cw k)) =
      inner (jordan (nw i) (nw k)) (jordan (nw i) (nw k)) := by
    rw [hnw]; exact h.product_sq i k
  have hinner (x y : Albert) : Inner.inner ℝ x y = inner x y := rfl
  have hmom (p : E) (u : Albert) (hpp : Inner.inner ℝ p p = inner u u)
      (hpu : ∀ k, Inner.inner ℝ p (cw k) = inner u (nw k)) : p = L u := by
    have h0 : ‖u - ∑ k, wordReprLin k u • nw k‖^2 = 0 := by
      rw [hsum u, sub_self, norm_zero, sq, zero_mul]
    rw [residual_norm_sq] at h0
    simp only [hinner] at h0
    have h1 : ‖p - L u‖^2 = 0 := by
      rw [hL, residual_norm_sq]
      simpa only [hpp, hpu, hgram] using h0
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp h1))
  have hLw (k : Fin 27) : L (nw k) = cw k :=
    (hmom (cw k) (nw k) (hgram k k) (hgram k)).symm
  have hLj (k l : Fin 27) : L (jordan (nw k) (nw l)) = j (cw k) (cw l) :=
    (hmom (j (cw k) (cw l)) (jordan (nw k) (nw l)) (hprod_sq k l) (hmixed k l)).symm
  have hunit : L 1 = e := by
    have h0 : nw 0 = 1 := by rw [hnw]; rfl
    rw [← h0, hLw 0]; rfl
  have hmarks (i : Fin 3) : L (nativeMarks i) = a i := by
    fin_cases i <;> dsimp
    · have h1 : nw 1 = nativeMarks 0 := by rw [hnw]; rfl
      rw [← h1, hLw 1]; rfl
    · have h2 : nw 2 = nativeMarks 1 := by rw [hnw]; rfl
      rw [← h2, hLw 2]; rfl
    · have h3 : nw 3 = nativeMarks 2 := by rw [hnw]; rfl
      rw [← h3, hLw 3]; rfl
  have hprod (x y : Albert) : L (jordan x y) = j (L x) (L y) := by
    have hx := (hsum x).symm
    have hy := (hsum y).symm
    calc L (jordan x y)
      _ = L (jordanLinear (∑ k, wordReprLin k x • nw k) (∑ l, wordReprLin l y • nw l)) := by
        rw [← hx, ← hy]; rfl
      _ = ∑ l, wordReprLin l y • ∑ k, wordReprLin k x • L (jordan (nw k) (nw l)) := by
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
        rfl
      _ = ∑ l, wordReprLin l y • ∑ k, wordReprLin k x • j (cw k) (cw l) := by
        simp only [hLj]
      _ = j (L x) (L y) := by
        rw [hL x, hL y]
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  have hmetric (x y : Albert) : Inner.inner ℝ (L x) (L y) = inner x y := by
    have hx := (hsum x).symm
    have hy := (hsum y).symm
    calc Inner.inner ℝ (L x) (L y)
      _ = ∑ l, ∑ k, wordReprLin l y * (wordReprLin k x * Inner.inner ℝ (cw k) (cw l)) := by
        rw [hL x, hL y]
        simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      _ = ∑ l, ∑ k, wordReprLin l y * (wordReprLin k x * Inner.inner ℝ (nw k) (nw l)) := by
        simp only [hgram, hinner]
      _ = Inner.inner ℝ (∑ k, wordReprLin k x • nw k) (∑ l, wordReprLin l y • nw l) := by
        simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      _ = inner x y := by rw [← hx, ← hy, hinner]
  have hinj : Function.Injective L := fun x y hxy => by
    have h0 : inner (x - y) (x - y) = 0 := by simp [← hmetric, hxy]
    exact sub_eq_zero.mp ((inner_self_eq_zero _).mp h0)
  have hrange : LinearMap.range L = generated e a j := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [generated, Submodule.mem_sInf]
      rintro K ⟨heK, haK, hjK⟩
      have hcw (k : Fin 27) : cw k ∈ K := by
        have hx : a f0 ∈ K := haK f0
        have hy : a f1 ∈ K := haK f1
        have hz : a f2 ∈ K := haK f2
        have hxx := hjK _ hx _ hx; have hxy := hjK _ hx _ hy; have hxz := hjK _ hx _ hz
        have hyy := hjK _ hy _ hy; have hyz := hjK _ hy _ hz; have hzz := hjK _ hz _ hz
        have h10 := hjK _ hx _ hxy; have h11 := hjK _ hx _ hxz; have h12 := hjK _ hx _ hyy
        have h13 := hjK _ hx _ hyz; have h14 := hjK _ hx _ hzz; have h15 := hjK _ hy _ hxz
        have h16 := hjK _ hy _ hyz; have h17 := hjK _ hy _ hzz; have h18 := hjK _ hxx _ hyy
        have h19 := hjK _ hxx _ hyz; have h20 := hjK _ hxx _ hzz; have h21 := hjK _ hxy _ hyz
        have h22 := hjK _ hxy _ hzz; have h23 := hjK _ hyy _ hzz; have h24 := hjK _ hx _ h15
        have h25 := hjK _ hx _ h16; have h26 := hjK _ hx _ h17
        fin_cases k <;> (dsimp [cw, candidateWordValues, wordValues]; assumption)
      rw [hL]
      exact K.sum_mem fun k _ => K.smul_mem _ (hcw k)
    · refine sInf_le ⟨⟨1, hunit⟩, fun i => ⟨nativeMarks i, hmarks i⟩, ?_⟩
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact ⟨jordan x y, hprod x y⟩
  refine ⟨L, ⟨hunit, hmarks, hprod, hmetric, hinj, hrange⟩, ?_⟩
  rintro J ⟨hJu, hJm, hJp, _, _, _⟩
  have hJw (k : Fin 27) : J (nw k) = cw k := by
    rw [hnw]
    have hx := hJm f0; have hy := hJm f1; have hz := hJm f2
    fin_cases k <;>
      (dsimp [cw, nativeWordValues, candidateWordValues, wordValues]
       simp only [hJu, hx, hy, hz, hJp])
  ext x
  conv_lhs => rw [← hsum x]
  rw [map_sum, hL]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smul, hJw k]

theorem finite_word_marked_recognition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (h : Match27 e a j) :
    ∃! L : Albert →ₗ[ℝ] E,
      L 1 = e ∧
      (∀ i : Fin 3, L (nativeMarks i) = a i) ∧
      (∀ x y : Albert, L (jordan x y) = j (L x) (L y)) ∧
      (∀ x y : Albert, Inner.inner ℝ (L x) (L y) = inner x y) ∧
      Function.Injective L ∧ LinearMap.range L = generated e a j :=
  recognition_core nativeWordValues nativeWordValues_sum rfl e a j h

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

/-- The honest topology from all nine native coordinate vectors. -/
def tripleCoordinateTopology : TopologicalSpace Triple :=
  TopologicalSpace.induced tripleCoordinates inferInstance

private def tripleCoordinateHomeomorph : Triple ≃ₜ TripleCoordinates :=
  Homeomorph.piCongrRight (fun _ : Fin 3 =>
    Homeomorph.piCongrRight (fun _ : Fin 3 =>
      Albert.coordinateLinearEquiv.toContinuousLinearEquiv.toHomeomorph))

private theorem tripleCoordinateTopology_eq_native :
    tripleCoordinateTopology = (inferInstance : TopologicalSpace Triple) := by
  change TopologicalSpace.induced
    (tripleCoordinateHomeomorph : Triple → TripleCoordinates) inferInstance = _
  exact tripleCoordinateHomeomorph.isInducing.eq_induced.symm

def tripleTopologicalSpace : TopologicalSpace Triple := tripleCoordinateTopology
attribute [local instance] tripleTopologicalSpace

/-- Admission requires actual ordered frames and the exact centered chart. -/
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

/-- One actual simultaneous product-and-trace automorphism, on fixed labels. -/
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

private def quotientCoordinateTopology
    (d : Glennie.Compact.LocalOrbitQuotientR01.LocalData) :
    TopologicalSpace (OrbitQuotient d.V) :=
  @instTopologicalSpaceQuotient (Admitted d.V) (orbitSetoid d.V)
    (@instTopologicalSpaceSubtype Triple _ tripleCoordinateTopology)

private def quotientNativeTopology
    (d : Glennie.Compact.LocalOrbitQuotientR01.LocalData) :
    TopologicalSpace (Glennie.Compact.LocalOrbitQuotientR01.OrbitQuotient d) :=
  @instTopologicalSpaceQuotient
    (Glennie.Compact.LocalOrbitQuotientR01.Admitted d)
    (Glennie.Compact.LocalOrbitQuotientR01.orbitSetoid d)
    (@instTopologicalSpaceSubtype Triple _ Pi.topologicalSpace)

private theorem quotientTopology_eq_source
    (d : Glennie.Compact.LocalOrbitQuotientR01.LocalData) :
    quotientCoordinateTopology d = quotientNativeTopology d := by
  unfold quotientCoordinateTopology quotientNativeTopology
  rw [tripleCoordinateTopology_eq_native]
  rfl

private theorem continuous_forward_induced
    (d : Glennie.Compact.LocalOrbitQuotientR01.LocalData) :
    Continuous (Glennie.Compact.LocalOrbitQuotientR01.forward d :
      OrbitQuotient d.V → d.V × Bool) := by
  let Q := Glennie.Compact.LocalOrbitQuotientR01.OrbitQuotient d
  let P : TopologicalSpace Q → Prop := fun τ =>
    @Continuous Q (d.V × Bool) τ inferInstance
      (Glennie.Compact.LocalOrbitQuotientR01.forward d)
  have hs : P (quotientNativeTopology d) := by
    with_unfolding_all exact Glennie.Compact.LocalOrbitQuotientR01.continuous_forward d
  with_unfolding_all change P (quotientCoordinateTopology d)
  exact (quotientTopology_eq_source d).symm ▸ hs

private theorem continuous_inverse_induced
    (d : Glennie.Compact.LocalOrbitQuotientR01.LocalData) :
    Continuous (Glennie.Compact.LocalOrbitQuotientR01.inverse d :
      d.V × Bool → OrbitQuotient d.V) := by
  let Q := Glennie.Compact.LocalOrbitQuotientR01.OrbitQuotient d
  let P : TopologicalSpace Q → Prop := fun τ =>
    @Continuous (d.V × Bool) Q inferInstance τ
      (Glennie.Compact.LocalOrbitQuotientR01.inverse d)
  have hs : P (quotientNativeTopology d) := by
    with_unfolding_all exact Glennie.Compact.LocalOrbitQuotientR01.continuous_inverse d
  with_unfolding_all change P (quotientCoordinateTopology d)
  exact (quotientTopology_eq_source d).symm ▸ hs

/-- The actual automorphism quotient of all admitted ordered frames is
homeomorphic to the centered feasible chart and its two algebraic sign sheets. -/
theorem admitted_orbit_quotient_homeomorph :
    ∃ V : Set ChartPoint, IsOpen V ∧
      Glennie.SubmissionR03.encode20 (fullLedger flatBase) ∈ V ∧
      ∃ H : OrbitQuotient V ≃ₜ V × Bool,
        (∀ T : Admitted V, H (Quotient.mk' T) = invariant V T) ∧
        (∀ T S : Admitted V,
          (orbitSetoid V).r T S ↔ invariant V T = invariant V S) := by
  let d := Glennie.Compact.LocalOrbitQuotientR01.localData
  refine ⟨d.V, d.openV, by rw [flatBase_eq_sections, fullLedger_eq_fn, encode20_eq_fn]; exact d.base, ?_⟩
  let H : OrbitQuotient d.V ≃ₜ d.V × Bool := {
    toFun := Glennie.Compact.LocalOrbitQuotientR01.forward d
    invFun := Glennie.Compact.LocalOrbitQuotientR01.inverse d
    left_inv := Glennie.Compact.LocalOrbitQuotientR01.inverse_forward d
    right_inv := Glennie.Compact.LocalOrbitQuotientR01.forward_inverse d
    continuous_toFun := continuous_forward_induced d
    continuous_invFun := continuous_inverse_induced d }
  refine ⟨H, fun _ => rfl, fun T S => ?_⟩
  change (Glennie.Compact.LocalOrbitQuotientR01.orbitSetoid d).r T S ↔
    Glennie.Compact.LocalOrbitQuotientR01.invariant d T =
      Glennie.Compact.LocalOrbitQuotientR01.invariant d S
  simpa only [Glennie.Compact.LocalOrbitQuotientR01.invariant, Prod.mk.injEq] using
    Glennie.Compact.LocalOrbitQuotientR01.rel_iff_chart_sheet_eq d T S

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
local instance tangentBilinearNormedSpace : NormedSpace ℝ (W →L[ℝ] W →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := W →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentEndNormedSpace : NormedSpace ℝ (W →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := W) (σ₁₂ := RingHom.id ℝ)
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
local instance taskAmbientEndSpace : NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := E) (F := E) (σ₁₂ := RingHom.id ℝ)
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
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def toSource (P : BasedCubic E) : SymmetricTrilinearForm E where
  form := P.form
  swap12 := P.swap12
  swap23 := P.swap23

theorem traceAt_eq_source (P : BasedCubic E) (e : E) :
    traceAt P e = normTrace (toSource P) e := rfl

theorem rawPair_eq_source (P : BasedCubic E) (e : E) :
    rawPair P e = rawTraceForm (toSource P) e := rfl

theorem rawPair_eq_three_metric (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (x y : E) :
    rawPair P e x y = 3 * metric P e x y :=
  rawTraceForm_eq_three_logMetric (toSource P) e he x y

theorem traceAt_eq_three_metric_unit (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (x : E) :
    traceAt P e x = 3 * metric P e x e := by
  have hepos : 0 < diagonalCubic (toSource P).form e := by
    change 0 < cubic P e; rw [he]; norm_num
  change fderiv ℝ (diagonalCubic (toSource P).form) e x =
    3 * logHessianForm (toSource P) e x e
  rw [logHessianForm_symm (toSource P) hepos x e,
    logHessianForm_radial_at_one (toSource P) e x he]
  ring

variable [FiniteDimensional ℝ E]

theorem rawPair_isInvertible (P : BasedCubic E) (e : E)
    (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) :
    (rawPair P e).IsInvertible :=
  ⟨(((rawBilinearForm (toSource P) e).toDual
    (rawBilinearForm_nondegenerate (toSource P) e he hp)).trans
    LinearMap.toContinuousLinearMap).toContinuousLinearEquiv, by ext x y; rfl⟩

theorem adjoint_eq_source (P : BasedCubic E) (e : E)
    (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x)
    (hB : (rawBilinearForm (toSource P) e).Nondegenerate) (x : E) :
    adjoint P e x = intrinsicAdjoint (toSource P) e hB x := by
  apply intrinsicAdjoint_unique (toSource P) e hB x
  intro y
  exact congrArg (fun L : E →L[ℝ] ℝ => L y)
    ((rawPair_isInvertible P e he hp).self_apply_inverse (fderiv ℝ (cubic P) x))

theorem product_eq_source (P : BasedCubic E) (e : E)
    (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x)
    (hB : (rawBilinearForm (toSource P) e).Nondegenerate) (x y : E) :
    product P e x y = intrinsicProduct (toSource P) e hB x y := by
  simp only [product, intrinsicProduct, intrinsicCross, intrinsicS,
    adjoint_eq_source P e he hp hB, traceAt_eq_source, rawPair_eq_source]

end
end Glennie.SubmissionR04Intrinsic

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
set_option autoImplicit false
open Glennie
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem nativeTraceLinear_eq_source :
    nativeTraceLinear = AlbertRecognition.traceLinear := by ext x; rfl

theorem nativeTangent_eq_source : NativeTangent = AlbertRecognition.V := by
  change nativeTraceLinear.ker = AlbertRecognition.traceLinear.ker
  rw [nativeTraceLinear_eq_source]

def nativeToSource : NativeTangent ≃ₗ[ℝ] AlbertRecognition.V :=
  LinearEquiv.ofEq _ _ nativeTangent_eq_source

theorem nativeToSource_K (u v : NativeTangent) :
    nativeToSource (nativeK u v) =
      AlbertRecognition.KA (nativeToSource u) (nativeToSource v) := by
  apply Subtype.ext; rfl

theorem nativeToSource_metric (u v : NativeTangent) :
    nativeMetric u v = AlbertRecognition.gA (nativeToSource u) (nativeToSource v) := rfl

private theorem gA_neg_left_local (x y : AlbertRecognition.V) :
    AlbertRecognition.gA (-x) y = -AlbertRecognition.gA x y := by
  change Glennie.inner (-(x : Albert)) (y : Albert) / 3 =
    -(Glennie.inner (x : Albert) (y : Albert) / 3)
  rw [Glennie.inner_neg_left, neg_div]

private theorem gA_sub_left_local (x y z : AlbertRecognition.V) :
    AlbertRecognition.gA (x - y) z =
      AlbertRecognition.gA x z - AlbertRecognition.gA y z := by
  rw [sub_eq_add_neg, AlbertRecognition.gA_add_left, gA_neg_left_local]; ring

theorem nativeCurvature_reference (u v w : NativeTangent) :
    nativeToSource (nativeCurvature u v w) =
      -(AlbertRecognition.D (nativeToSource u) (nativeToSource v)
        (nativeToSource w)) := by
  simp only [nativeCurvature, map_add, map_sub, map_smul,
    nativeToSource_K, nativeToSource_metric,
    AlbertRecognition.D, AlbertRecognition.wedge,
    AlbertRecognition.q, AlbertRecognition.operatorComm,
    AlbertRecognition.KB_referenceCubic,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  change _ =
    -(AlbertRecognition.gA (nativeToSource v) (nativeToSource w) • nativeToSource u -
      AlbertRecognition.gA (nativeToSource u) (nativeToSource w) • nativeToSource v +
      (AlbertRecognition.KA (nativeToSource u)
        (AlbertRecognition.KA (nativeToSource v) (nativeToSource w)) -
       AlbertRecognition.KA (nativeToSource v)
        (AlbertRecognition.KA (nativeToSource u) (nativeToSource w))))
  module

end
end Glennie.SubmissionR04Intrinsic

namespace Glennie.SubmissionR04Intrinsic.Local
noncomputable section
open Glennie Glennie.Compact.Affine20
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (A : E ≃ₗ[ℝ] Albert)

local notation "eA" => A.symm (1 : Albert)
local notation "tA" => (fun x : E => trace (A x))
local notation "jA" => (fun x y : E => A.symm (jordan (A x) (A y)))

private abbrev mT (T : Triple E) : Glennie.Compact.Affine20.Triple := fun a i => A (T a i)
private abbrev pT (T : Glennie.Compact.Affine20.Triple) : Triple E := fun a i => A.symm (T a i)

omit [FiniteDimensional ℝ E] in
private theorem pow_map (p : Fin 3 → E) (s : Fin 2) :
    A (power jA p s) = Glennie.Compact.NativeQFamilyLedger.framePower (fun i => A (p i)) s := by
  by_cases hs : s = 0 <;> simp [power, Glennie.Compact.NativeQFamilyLedger.framePower, hs, encoder, Glennie.encoder]

omit [FiniteDimensional ℝ E] in
private theorem quad_map (x z : E) : A (quad jA x z) = U (A x) (A z) := by
  simp [quad, U]

omit [FiniteDimensional ℝ E] in
private theorem phi_eq (x y z : E) : phi tA jA x y z = Glennie.phi (A x) (A y) (A z) := by
  simp [phi, Glennie.phi, pairing, Glennie.inner, quad_map A]

omit [FiniteDimensional ℝ E] in
private theorem frame_iff (p : Fin 3 → E) : Frame eA tA jA p ↔ Glennie.Frame (fun i => A (p i)) := by
  refine ⟨fun h => ⟨h.1, fun i => by simpa using congrArg A (h.2 i),
    fun i k hik => by simpa using congrArg A (h.3 i k hik),
    by simpa using congrArg A h.4⟩,
    fun h => ⟨h.1, fun i => A.injective (by simpa using h.2 i),
    fun i k hik => A.injective (by simpa using h.3 i k hik),
    A.injective (by simpa using h.4)⟩⟩

omit [FiniteDimensional ℝ E] in
private theorem ledger_eq (T : Triple E) : ledger tA jA T = ledger54 (mT A T) := by
  ext <;> simp [ledger, ledger54, Glennie.ledger, pairing, Glennie.inner]

omit [FiniteDimensional ℝ E] in
private theorem q26_eq (T : Triple E) :
    q26 tA jA T = Glennie.Compact.NativeQFamilyLedger.q26 (mT A T) := by
  funext k; fin_cases k <;>
    simp [q26, Glennie.Compact.NativeQFamilyLedger.q26, qSingle, qPair, qTriple,
      Glennie.Compact.NativeQFamilyLedger.qSingle, Glennie.Compact.NativeQFamilyLedger.qPair,
      Glennie.Compact.NativeQFamilyLedger.qTriple, pairing, Glennie.inner, pow_map A]

omit [FiniteDimensional ℝ E] in
private theorem score_eq (T : Triple E) :
    score eA tA jA T = Glennie.Compact.LocalContrast.score (mT A T) := by
  have henc (a : Fin 3) : A (encoder (T a)) = Glennie.encoder (mT A T a) := map_sub A _ _
  simp only [score, Glennie.Compact.LocalContrast.score, delta, contrast,
    Glennie.Compact.OperationalPhi.delta, Glennie.Compact.OperationalPhi.contrast,
    half, Glennie.Compact.OperationalPhi.halfAmplitude, pairing, Glennie.inner,
    quad_map A, henc, map_sub, map_add, map_smul, LinearEquiv.apply_symm_apply]

omit [FiniteDimensional ℝ E] in
private theorem orbit_iff (T S : Triple E) :
    S ∈ orbit tA jA T ↔ mT A S ∈ Glennie.Compact.FlatOrbit.autOrbit (mT A T) := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨⟨(A.symm.trans g.equiv).trans A, fun x y => ?_, fun x => ?_⟩,
      funext fun a => funext fun i => by simp [Glennie.Compact.Affine20.mapAtoms, mapAtoms]⟩
    · simpa using congrArg A (g.map_product (A.symm x) (A.symm y))
    · simpa using g.map_trace (A.symm x)
  · rintro ⟨k, hk⟩
    refine ⟨⟨(A.trans k.equiv).trans A.symm, fun x y => ?_, fun x => ?_⟩,
      funext fun a => funext fun i => A.injective (by
        simpa [mapAtoms, Glennie.Compact.Affine20.mapAtoms] using congrFun (congrFun hk a) i)⟩
    · simp [k.map_jordan]
    · simp [k.map_trace]

omit [FiniteDimensional ℝ E] in
private theorem fibre54_iff (b : Chart) (T : Triple E) :
    T ∈ fibre54 eA tA jA b ↔ mT A T ∈ Glennie.Compact.NearbyOrbits.fibre54 b := by
  change ((∀ a, Frame eA tA jA (T a)) ∧ ledger tA jA T = Glennie.Compact.Affine20.decode20 b) ↔ _
  simp only [Glennie.Compact.NearbyOrbits.fibre54, Set.mem_ofPred_eq, ledger_eq A, frame_iff A]

omit [FiniteDimensional ℝ E] in
private theorem fibre20_iff (b : Chart) (T : Triple E) :
    T ∈ fibre20 eA tA jA b ↔ mT A T ∈ Glennie.Compact.NearbyOrbits.fibre20 b := by
  change ((∀ a, Frame eA tA jA (T a)) ∧ Glennie.Compact.Affine20.encode20 (ledger tA jA T) = b) ↔ _
  simp only [Glennie.Compact.NearbyOrbits.fibre20, Set.mem_ofPred_eq, ledger_eq A, frame_iff A]

theorem exists_result (N : E → ℝ) (a B : E → E → ℝ)
    (Gamma : E → E → E) (R : E → E → E → E) (nativeN : Albert → ℝ)
    (hnorm : ∀ x, nativeN (A x) = N x)
    (hmetric : ∀ x y, a x y = Glennie.inner (A x) (A y) / 3)
    (hraw : ∀ x y, B x y = Glennie.inner (A x) (A y))
    (hconn : ∀ x y, A (Gamma x y) = -jordan (A x) (A y))
    (hcurv : ∀ u v w, A (R u v w) = -(jordan (A u) (jordan (A v) (A w)) - jordan (A v) (jordan (A u) (A w)))) :
    Nonempty (Result eA N tA a B jA Gamma R nativeN) := by
  obtain ⟨V1, hV1, hb1, pos, neg, hcP, hcN, hfP, hfN, _, _, hlP, hlN, hpP, hpN, hcov, hdisj, h20⟩ :=
    Glennie.Compact.NearbyOrbitsClosed.nearby_fibres_two_orbits_unconditional
  obtain ⟨V2, hV2, hb2, hclass⟩ := Glennie.Compact.NearbyOrbitsClosed.nearby_q26_score_complete
  let V := V1 ∩ V2
  have hpT_cont : Continuous (pT A) :=
    continuous_pi fun f => continuous_pi fun i =>
      A.symm.toLinearMap.continuous_of_finiteDimensional.comp
        (Glennie.Compact.FrameTopology.continuous_entry f i)
  have hmT_pT (T : Glennie.Compact.Affine20.Triple) : mT A (pT A T) = T := by
    funext f i; exact A.apply_symm_apply _
  have hdec (b : Chart) : Glennie.SubmissionR03.decode20 b = decode20 b := rfl
  have henc (L : Ledger54) : Glennie.SubmissionR03.encode20 L = encode20 L := rfl
  have htwo : TwoOrbitSections eA tA jA V := by
    refine ⟨fun b => pT A (pos b), fun b => pT A (neg b),
      hpT_cont.comp_continuousOn (hcP.mono Set.inter_subset_left),
      hpT_cont.comp_continuousOn (hcN.mono Set.inter_subset_left),
      fun b hb f => (frame_iff A _).mpr (by simpa [hmT_pT] using hfP b hb.1 f),
      fun b hb f => (frame_iff A _).mpr (by simpa [hmT_pT] using hfN b hb.1 f),
      fun b hb => by rw [ledger_eq A, hmT_pT, hdec]; exact hlP b hb.1,
      fun b hb => by rw [ledger_eq A, hmT_pT, hdec]; exact hlN b hb.1,
      fun b hb => by
        rw [score_eq A, hmT_pT, Glennie.Compact.LocalContrast.score_eq_two_phi]
        linarith [hpP b hb.1],
      fun b hb => by
        rw [score_eq A, hmT_pT, Glennie.Compact.LocalContrast.score_eq_two_phi]
        linarith [hpN b hb.1],
      fun b hb => Set.ext fun T => by
        change T ∈ fibre54 eA tA jA b ↔ T ∈ orbit tA jA _ ∨ T ∈ orbit tA jA _
        rw [fibre54_iff A, orbit_iff A, orbit_iff A, hmT_pT, hmT_pT, hcov b hb.1]; rfl,
      fun b hb => Set.disjoint_left.mpr fun T hN hP =>
        Set.disjoint_left.mp (hdisj b hb.1)
          (by simpa [hmT_pT] using (orbit_iff A _ T).mp hN)
          (by simpa [hmT_pT] using (orbit_iff A _ T).mp hP),
      fun b hb => Set.ext fun T => by rw [fibre20_iff A, fibre54_iff A, h20 b hb.1]⟩
  have hsc : ScoreComplete eA tA jA V := fun T S hT hS hb => by
    rw [henc, ledger_eq A] at hb
    obtain ⟨hnz, hiff⟩ := hclass (mT A T) (mT A S)
      (fun f => (frame_iff A _).mp (hT f)) (fun f => (frame_iff A _).mp (hS f)) hb.2
    refine ⟨by rwa [score_eq A], ?_⟩
    simpa only [orbit_iff A, Glennie.Compact.FlatOrbit.autOrbit, Set.mem_ofPred_eq,
      q26_eq A, SameSign, Glennie.Compact.NearbyOrbitsClosed.SameScoreSign, score_eq A] using hiff
  have hgen (T : Triple E) (hT : Admitted eA tA jA V T)
      (K : Submodule ℝ E) (hK : ∀ p ∈ K, ∀ q ∈ K, jA p q ∈ K)
      (hAtoms : ∀ f i, T f i ∈ K) : K = ⊤ := by
    have htop : K.map A.toLinearMap = ⊤ :=
      Glennie.SubmissionR03.atoms_generate_of_score (mT A T)
        (fun f => (frame_iff A _).mp (hT.1 f))
        (by rw [Glennie.SubmissionR03.score_eq_source, ← score_eq A]; exact (hsc T T hT.1 hT.1 hT.2).1)
        (K.map A.toLinearMap)
        (by rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩; exact ⟨jA p q, hK p hp q hq, A.apply_symm_apply _⟩)
        (fun f i => ⟨T f i, hAtoms f i, rfl⟩)
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (htop.symm ▸ trivial : A x ∈ K.map A.toLinearMap)
    exact A.injective hyx ▸ hy
  refine ⟨⟨A, A.apply_symm_apply 1, hnorm, hmetric, hraw, fun _ => rfl,
    fun x y => A.apply_symm_apply _, hconn, hcurv, V, hV1.inter hV2,
    by rw [henc, ledger_eq A, show mT A (fun f i => A.symm (Glennie.SubmissionR03.flatBase f i)) =
      Glennie.Compact.Sections.flatBase from hmT_pT _]; exact ⟨hb1, hb2⟩, htwo, hsc,
    fun T S hT hS => by
      rw [q26_eq A, q26_eq A, ledger_eq A, ledger_eq A]
      exact Glennie.Compact.NativeQFamilyLedger.q26_eq_iff_ledger54_eq _ _
        (fun f => (frame_iff A _).mp (hT f)) (fun f => (frame_iff A _).mp (hS f)),
    fun T => by
      rw [score_eq A, Glennie.Compact.LocalContrast.score_eq_two_phi, phi_eq A]
      simp [Glennie.Compact.Sections.phiOf, encoder, Glennie.encoder, mT],
    hgen,
    fun T hT g hfix => LinearEquiv.ext fun x => by
      have htop := hgen T hT (LinearMap.eqLocus g.equiv.toLinearMap LinearMap.id)
        (fun p hp q hq => (g.map_product p q).trans (congrArg₂ jA hp hq))
        (fun f i => congrFun (congrFun hfix f) i)
      exact (htop.symm ▸ trivial : x ∈ LinearMap.eqLocus g.equiv.toLinearMap LinearMap.id),
    fun T hT D hD hkill => LinearMap.ext fun x => by
      have htop := hgen T hT (LinearMap.ker D)
        (fun p hp q hq => by
          change D _ = 0
          rw [hD, LinearMap.mem_ker.mp hp, LinearMap.mem_ker.mp hq]
          simp [Glennie.jordan_zero_left, Glennie.jordan_zero_right])
        hkill
      exact LinearMap.mem_ker.mp (htop.symm ▸ trivial : x ∈ LinearMap.ker D)⟩⟩

end
end Glennie.SubmissionR04Intrinsic.Local

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
set_option autoImplicit false
open Glennie
attribute [local instance] tangentDualNormedAddCommGroup tangentDualNormedSpace

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
  obtain ⟨F, hmetric, hcurvature⟩ := hMatch
  let FSource : AlbertRecognition.V ≃ₗ[ℝ]
      AlbertGeometry.RecognitionFromCurvature.tangentSpace (toSource P) e :=
    nativeToSource.symm.trans F
  have hMD : AlbertGeometry.RecognitionFromCurvature.baseChartMetric (toSource P) e =
      tangentMetricDual P e := by ext u v; rfl
  have hRC : AlbertGeometry.RecognitionFromCurvature.raisedTangentCubic (toSource P) e =
      independentRaisedCubic P e := by
    unfold AlbertGeometry.RecognitionFromCurvature.raisedTangentCubic
      independentRaisedCubic tangentMetricRaise
    rw [hMD]; rfl
  obtain ⟨A, hunit, hnorm, hm, hprod, hconn, hcurv⟩ :=
    AlbertGeometry.RecognitionFromCurvature.exists_native_norm_unit_actual_geometry
      (toSource P) e he hp FSource
      (fun x y => by
        change metric P e (F (nativeToSource.symm x) : E) (F (nativeToSource.symm y) : E) = _
        rw [hmetric, nativeToSource_metric, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
      (fun x y z => by
        dsimp only [AlbertGeometry.RecognitionFromCurvature.sourceCurvature]
        rw [hMD, hRC]
        change independentCurvature P e (F (nativeToSource.symm x))
          (F (nativeToSource.symm y)) (F (nativeToSource.symm z)) =
          F (nativeToSource.symm (-(AlbertRecognition.D x y z)))
        rw [hcurvature]
        congr 1
        apply nativeToSource.injective
        rw [nativeCurvature_reference]
        simp only [LinearEquiv.apply_symm_apply])
  have he_eq : e = A.symm 1 := A.injective (hunit.trans (A.apply_symm_apply _).symm)
  have ht_eq : (fun x : E => traceAt P e x) = (fun x => trace (A x)) := by
    funext x
    rw [traceAt_eq_three_metric_unit P e he x]
    change 3 * AlbertGeometry.Cubic.logHessianForm (toSource P) e x e = trace (A x)
    rw [hm x e, hunit, jordan_unit_right]
    ring
  have hj_eq : product P e = (fun x y : E => A.symm (jordan (A x) (A y))) := by
    funext x y
    apply A.injective
    rw [A.apply_symm_apply, product_eq_source P e he hp
      (AlbertGeometry.BasedNormAdjointTransport.rawBilinearForm_nondegenerate (toSource P) e he hp)]
    exact hprod x y
  change Nonempty (Local.Result e (cubic P) (fun x => traceAt P e x)
    (fun x y => metric P e x y) (fun x y => rawPair P e x y) (product P e)
    (fun x y => ambientConnection P e x y) (ambientCurvature P e) nativeCubic)
  rw [ht_eq, hj_eq]
  exact he_eq.symm ▸ Local.exists_result A (cubic P) (fun x y => metric P e x y)
    (fun x y => rawPair P e x y) (fun x y => ambientConnection P e x y)
    (ambientCurvature P e) nativeCubic hnorm hm
    (fun x y => by
      rw [rawPair_eq_three_metric P e he x y]
      change 3 * AlbertGeometry.Cubic.logHessianForm (toSource P) e x y = trace (jordan (A x) (A y))
      rw [hm x y]; ring)
    hconn hcurv

end
end Glennie.SubmissionR04Intrinsic
