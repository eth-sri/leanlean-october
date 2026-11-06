/- Unified independent native and admitted orbit-quotient statement surface. -/
module
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Aesop
public import Glennie.Compact.ObservationTransport
public import Glennie.Compact.ObservationScript
public import Glennie.Compact.ReadoutRobustnessR01
public import Glennie.Compact.LocalOrbitQuotientR01
public import Glennie.NativeQuadraticPositiveR01
public import Glennie.Theorems.Frames
public import Glennie.Compact.OperationalPhi
public import Mathlib.Tactic.LinearCombination
public import Glennie.Compact.NearbyOrbitsClosed

public import Glennie.NativeGenerationComplexSectorR01
public import Glennie.NativeGenerationCoordinatesR01
public import Glennie.NativeGenerationEndpointR01
public import Glennie.NativeGenerationHiddenActionsR01
public import Glennie.NativeGenerationHiddenCompletionR01
public import Glennie.NativeGenerationHiddenSpanR01
public import Glennie.NativeGenerationPeirceTriangleR01
public import Glennie.NativeGenerationStabilizersR01
public import Glennie.Diagonalization
public import Glennie.Compact.NativeQ20AdapterR01
public import Glennie.Compact.NativeDefectReadoutR01
public import Glennie.Compact.NativeWordTableCoordinatesR01
public import Glennie.Compact.NativeWordTableBasisR01
public import Glennie.Compact.VariableDiagonalNullTargetR01

public import Mathlib.Analysis.Quaternion
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Basic
public import AlbertGeometry.BasedNormAdjointTransport
public import AlbertGeometry.UnitTangentNormReconstruction
public import AlbertGeometry.NativeIntrinsicProductBinding
public import AlbertGeometry.AmbientCurvatureProduct
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
  refine ⟨?_, ?_, ?_⟩
  · intro K h1 hJ hx hy hz
    exact Glennie.NativeGenerationEndpointR01.eq_top_of_phi_ne_zero
      K h1 hJ x y z hx hy hz hphi
  · intro g hx hy hz
    have hg := Glennie.NativeGenerationStabilizersR01.automorphism_eq_refl_of_phi_ne_zero
      g x y z hphi hx hy hz
    rw [hg]
    rfl
  · intro D hD hx hy hz
    exact Glennie.NativeGenerationStabilizersR01.derivation_eq_zero_of_phi_ne_zero
      D hD x y z hphi hx hy hz

theorem q26_eq_iff_fullLedger_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q26 T = q26 S ↔ fullLedger T = fullLedger S := Glennie.Compact.NativeQFamilyLedger.q26_eq_iff_ledger54_eq T S hT hS

/-- Q20 is the final twenty Q26 readings; the first six are fixed on actual frames. -/
def q20 (T : Triple) : Fin 20 → ℝ :=
  fun i => q26 T ⟨i.val + 6, Nat.add_lt_add_right i.2 6⟩

/-- On actual ordered frames, Q20 still determines the complete 54-trace ledger. -/
theorem q20_eq_iff_fullLedger_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q20 T = q20 S ↔ fullLedger T = fullLedger S := Glennie.Compact.NativeQ20AdapterR01.q20_eq_iff_ledger54_eq T S hT hS

private theorem q26_eq_source (T : Triple) :
    q26 T = Glennie.Compact.NativeQFamilyLedger.q26 T := rfl
private theorem phiOf_eq (T : Triple) :
    phiOf T = Glennie.Compact.Sections.phiOf T := rfl
private theorem score_eq_source (T : Triple) :
    score T = Glennie.Compact.LocalContrast.score T := rfl
theorem division_free (x y z : Albert) :
    4 * delta x y z (halfAmplitude x) y - delta x y z x y -
      delta x y z 1 y = 2 * phi x y z := Glennie.Compact.OperationalPhi.phi_division_free x y z

theorem score_eq_two_phi (T : Triple) : score T = 2 * phiOf T := Glennie.Compact.LocalContrast.score_eq_two_phi T

theorem atoms_generate_of_score
    (T : Triple) (hT : ∀ a, Frame (T a)) (hs : score T ≠ 0)
    (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (hAtoms : ∀ a i, T a i ∈ K) : K = ⊤ := by
  have hu : (1 : Albert) ∈ K := by
    rw [← (hT 0).sum_unit]
    exact K.add_mem (K.add_mem (hAtoms 0 0) (hAtoms 0 1)) (hAtoms 0 2)
  have he (a : Fin 3) : encoder (T a) ∈ K := K.sub_mem (hAtoms a 2) (hAtoms a 0)
  apply Glennie.NativeGenerationEndpointR01.eq_top_of_phi_ne_zero K hu hJ
    (encoder (T f0)) (encoder (T f1)) (encoder (T f2)) (he f0) (he f1) (he f2)
  intro hz
  apply hs
  simp only [score_eq_two_phi, phiOf, hz, mul_zero]

private theorem flatBase_eq_source :
    flatBase = Glennie.Compact.FrameTopology.flatBaseTriple := rfl
private theorem fullLedger_eq_source (T : Triple) :
    fullLedger T = Glennie.Compact.Affine20.ledger54 T := rfl
private theorem mapAtoms_eq_source (g : CompactAutomorphism) (T : Triple) :
    mapAtoms g T = Glennie.Compact.Affine20.mapAtoms g T := rfl

theorem nearby_sign_rigidity :
    ∃ V : Set Ledger54, IsOpen V ∧ fullLedger flatBase ∈ V ∧
      ∀ T S : Triple, (∀ a : Fin 3, Frame (T a)) →
        (∀ a : Fin 3, Frame (S a)) → fullLedger T ∈ V →
        fullLedger T = fullLedger S →
        ((phiOf T < 0 ∧ phiOf S < 0) ∨ (0 < phiOf T ∧ 0 < phiOf S)) →
        ∃ k : CompactAutomorphism, mapAtoms k S = T := by
  simp only [flatBase_eq_source, fullLedger_eq_source, phiOf_eq, mapAtoms_eq_source]
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun T S hT hS _ =>
    Glennie.Compact.NearbyOrbitsClosed.same_sign_rigidity T S hT hS⟩

/- A specific native near-flat full-fiber margin in a supplied open ledger neighborhood. -/
open Glennie.Compact Glennie.Compact.FrameTopology Glennie.Compact.Sections
  Glennie.Compact.NearbyOrbits Glennie.Compact.FlatBase in
theorem near_flat_scalar_margin :
    ∃ V : Set Ledger54, IsOpen V ∧ fullLedger flatBase ∈ V ∧
      ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) → fullLedger T ∈ V →
        1 / 27 < |phiOf T| := by
  simp only [flatBase_eq_source, fullLedger_eq_source, phiOf_eq]
  obtain ⟨d⟩ := Sections.flat_two_sections
  have hl := d.ledgerNeg
  rcases d with ⟨W, hW, hb, _, sec, _, hc, _, hf, _, _, _, hp⟩
  let b0 := Glennie.Compact.Affine20.encode20 (ledger54 flatBaseTriple)
  have hbL : ledger54 (sec b0) = ledger54 flatBaseTriple := by
    rw [hl b0 (show b0 ∈ W from hb)]
    exact decode_encode_frames flatBaseTriple flatBaseTriple_frames
  have hphi : Glennie.Compact.Sections.phiOf flatBaseTriple = -4 / 27 := flat_phi
  have hs : 1 / 27 < |Glennie.Compact.Sections.phiOf (sec b0)| := by
    rw [← abs_phi_eq flatBaseTriple (sec b0) flatBaseTriple_frames (hf _ hb)
      hbL.symm (by rw [hphi]; norm_num)]
    norm_num [hphi]
  let U := W ∩ (fun b => Glennie.Compact.Sections.phiOf (sec b)) ⁻¹' {r : ℝ | 1 / 27 < |r|}
  have hu : IsOpen U := (continuous_phiOf.comp_continuousOn hc).isOpen_inter_preimage hW
    (isOpen_lt continuous_const continuous_abs)
  refine ⟨Glennie.Compact.Affine20.encode20 ⁻¹' U, hu.preimage continuous_encode20, ⟨hb, hs⟩, ?_⟩
  intro T hT hTV
  have heq : ledger54 (sec (Glennie.Compact.Affine20.encode20 (ledger54 T))) = ledger54 T := by
    rw [hl _ hTV.1]
    exact decode_encode_frames T hT
  rw [← abs_phi_eq (sec (Glennie.Compact.Affine20.encode20 (ledger54 T))) T (hf _ hTV.1) hT heq
    (ne_of_lt (hp _ hTV.1))]
  exact hTV.2

/-- Full admitted fibers and the simultaneous product-and-trace automorphism orbit. -/
def fibre54 (b : Fin 20 → ℝ) : Set Triple :=
  {T | (∀ a : Fin 3, Frame (T a)) ∧ fullLedger T = decode20 b}
def fibre20 (b : Fin 20 → ℝ) : Set Triple :=
  {T | (∀ a : Fin 3, Frame (T a)) ∧ encode20 (fullLedger T) = b}
def autOrbit (S : Triple) : Set Triple :=
  {T | ∃ g : CompactAutomorphism, mapAtoms g S = T}

/-- Every admitted nearby full fiber is exactly two disjoint simultaneous
    automorphism orbits, with continuous signed sections and exact chart fibers. -/
private theorem continuous_coordinates :
    Continuous (fun T : Triple => fun a i => Albert.coordinateEquiv (T a i)) := by
  have hc : Continuous Albert.coordinateEquiv :=
    Albert.coordinateLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  fun_prop

private theorem flatBase_eq_sections :
    flatBase = Glennie.Compact.Sections.flatBase := rfl
private theorem encode20_eq_source (L : Ledger54) :
    encode20 L = Glennie.Compact.Affine20.encode20 L := rfl
private theorem fibre54_eq_source (b : Fin 20 → ℝ) :
    fibre54 b = Glennie.Compact.NearbyOrbits.fibre54 b := by
  simp only [fibre54, Glennie.Compact.NearbyOrbits.fibre54,
    fullLedger_eq_source]
private theorem fibre20_eq_source (b : Fin 20 → ℝ) :
    fibre20 b = Glennie.Compact.NearbyOrbits.fibre20 b := by
  simp only [fibre20, Glennie.Compact.NearbyOrbits.fibre20,
    fullLedger_eq_source]
private theorem autOrbit_eq_source (T : Triple) :
    autOrbit T = Glennie.Compact.FlatOrbit.autOrbit T := by
  simp only [autOrbit, Glennie.Compact.FlatOrbit.autOrbit, mapAtoms_eq_source]

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
  obtain ⟨d⟩ :=
    Glennie.Compact.NearbyOrbitsClosed.nearby_fibres_two_orbits_unconditional
  have hlp := d.toSignedSections.ledgerPos
  have hln := d.toSignedSections.ledgerNeg
  have hdisj := d.toSignedSections.disj
  have heq := fun b (_ : b ∈ d.V) => Glennie.Compact.NearbyOrbits.fibre20_eq_fibre54 b
  rcases d with ⟨⟨V, ho, hb, p, n, hcp, hcn, hfp, hfn, hep, hen, hpp, hnn⟩, hcover⟩
  refine ⟨V, ho, ?_, p, n, continuous_coordinates.comp_continuousOn hcp,
    continuous_coordinates.comp_continuousOn hcn, hfp, hfn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp_all [flatBase_eq_sections, fullLedger_eq_source, phiOf_eq, fibre54_eq_source, fibre20_eq_source, autOrbit_eq_source,
    Glennie.Compact.ChartTransfer.encode20_decode20]

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
  let d := Glennie.Compact.LocalOrbitQuotientR01.localData
  refine ⟨d.V, d.openV, ?_, ?_⟩
  · simpa only [flatBase_eq_sections, fullLedger_eq_source, encode20_eq_source] using d.base
  · simpa only [fullLedger_eq_source, encode20_eq_source, score_eq_source,
      mapAtoms_eq_source, q26_eq_source, Glennie.Compact.LocalReconstruction.SameScoreSign] using
      Glennie.Compact.LocalReconstruction.nearby_q26_score_complete d

/-- Every compact region of the established admitted chart has a positive
uniform Phi margin for its entire actual ordered-frame fiber. -/
theorem compact_local_phi_margin :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∀ K : Set V, IsCompact K →
        ∃ m > 0, ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) →
          ∀ hb : encode20 (fullLedger T) ∈ V,
            (⟨encode20 (fullLedger T), hb⟩ : V) ∈ K →
              m ≤ |phiOf T| := by
  let d := Glennie.Compact.LocalOrbitQuotientR01.localData
  refine ⟨d.V, d.openV, ?_, ?_⟩
  · rw [flatBase_eq_sections, fullLedger_eq_source, encode20_eq_source]
    exact d.base
  · intro K hK
    obtain ⟨m, hm, hbound⟩ :=
      Glennie.Compact.NativeQ20AdapterR01.compact_response_margin d K hK
    refine ⟨m, hm, ?_⟩
    intro T hT hb hmem
    exact hbound ⟨T, hT, hb⟩ hmem

/-- Six absolute-error bounds and a strict observed margin certify the
    native scalar sign; no probability or measurement semantics is assumed. -/
theorem signed_readout_margin (T : Triple) (noisy : Readouts) (ε : ℝ)
    (hε : 0 ≤ ε) (h : ErrorsAtMost noisy (exactReadouts T) ε)
    (hm : 12 * ε < |weightedScore noisy|) :
    (weightedScore noisy < 0 ∧ phiOf T < 0) ∨
    (0 < weightedScore noisy ∧ 0 < phiOf T) := by
  have he := Glennie.Compact.ReadoutRobustnessR01.weightedScore_error noisy (exactReadouts T) ε h
  rw [Glennie.Compact.ReadoutRobustnessR01.weightedScore_eq_two_phi, ← phiOf_eq] at he
  grind

/-- The native raw trace norm, used to state perturbation radii independently. -/
def nA (x : Albert) : ℝ := Real.sqrt (inner x x)

theorem nA_eq_norm (x : Albert) : nA x = ‖x‖ := by
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
  let d := Glennie.Compact.LocalOrbitQuotientR01.localData
  refine ⟨d.V, d.openV, ?_, d.pos, d.neg, ?_, ?_,
    d.framePos, d.frameNeg, ?_, ?_, ?_, ?_, ?_⟩
  · rw [flatBase_eq_sections, fullLedger_eq_source, encode20_eq_source]
    exact d.base
  · exact continuous_coordinates.comp_continuousOn d.contPos
  · exact continuous_coordinates.comp_continuousOn d.contNeg
  · intro b hb
    rw [fullLedger_eq_source, encode20_eq_source]
    exact d.chartPos b hb
  · intro b hb
    rw [fullLedger_eq_source, encode20_eq_source]
    exact d.chartNeg b hb
  · intro b hb
    rw [phiOf_eq]
    exact d.phiPos b hb
  · intro b hb
    rw [phiOf_eq]
    exact d.phiNeg b hb
  · intro K hK ζ hζ
    obtain ⟨η, hη, hrec⟩ :=
      Glennie.Compact.NativeQ20AdapterR01.compact_feasible_recovery d K hK ζ hζ
    refine ⟨η, hη, ?_⟩
    intro T hT hb hTK b hbK hdist
    let Td : Glennie.Compact.LocalOrbitQuotientR01.Admitted d :=
      ⟨T, hT, hb⟩
    obtain ⟨g, hg⟩ := hrec Td hTK b hbK hdist
    refine ⟨g, ?_⟩
    have hsection :
        Glennie.Compact.NativeQ20AdapterR01.branchSection d b
          (Glennie.Compact.LocalOrbitQuotientR01.sheet d Td) =
          (if 0 < phiOf T then d.pos b.1 else d.neg b.1) := by
      simp [Glennie.Compact.NativeQ20AdapterR01.branchSection,
        Glennie.Compact.LocalOrbitQuotientR01.sectionPoint,
        Glennie.Compact.LocalOrbitQuotientR01.sheet, phiOf_eq, Td]
      exact apply_ite (fun X : Glennie.Compact.LocalOrbitQuotientR01.Admitted d => X.1) _ _ _
    rw [hsection] at hg
    intro a i
    rw [nA_eq_norm]
    exact ((norm_le_pi_norm
      ((T - Glennie.Compact.Affine20.mapAtoms g
        (if 0 < phiOf T then d.pos b.1 else d.neg b.1)) a) i).trans
      (norm_le_pi_norm _ a)).trans_lt hg

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
  · have hns                             := not_lt_of_ge hn.1.le
    have hnp                 := not_lt_of_ge hn.2.le
    simpa only [if_neg hns, if_neg hnp] using hg
  · simpa only [if_pos hp.1, if_pos hp.2] using hg


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
  have hp := Glennie.Compact.NativeNormKernel.phi_displacement_18
    (encoder (T 0)) (encoder (T 1)) (encoder (T 2))
    x' y' z' R δ hR hx hy hz hx' hy' hz' hdx hdy hdz
  have he : |noisyPhi noisy - phi x' y' z'| ≤ ξ + 18 * R^8 * δ :=
    (abs_sub_le _ _ _).trans (add_le_add
      (Glennie.Compact.MeasuredMarginR01.six_readout_scalar_error
        T noisy ε ξ hreadout hallowance) hp)
  have hn : phi x' y' z' ≠ 0 := by grind
  refine ⟨by grind, ?_, ?_⟩
  · exact fun K h1 hJ hx hy hz =>
      Glennie.NativeGenerationEndpointR01.eq_top_of_phi_ne_zero K h1 hJ x' y' z' hx hy hz hn
  · intro g hx hy hz
    rw [Glennie.NativeGenerationStabilizersR01.automorphism_eq_refl_of_phi_ne_zero
      g x' y' z' hn hx hy hz]
    rfl

/-- The coordinatewise special Jordan product in arbitrary Euclidean dimension. -/
def diagonalNProduct {n : ℕ} (a b : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp (Nat.cast 2 : ENNReal) (fun i => a i * b i)

/- A uniform all-input defect bounds the degree-nine scalar on any
radius-bounded triple for every finite coordinatewise Euclidean target. -/
open Glennie.Compact.MultiplicationDefectR01 Glennie.Compact.NativeDefectReadoutR01
  Glennie.Compact.VariableDiagonalNullTargetR01 Glennie.Compact.NativeNormKernel
  Glennie.Compact.NormCompatibleNullTargetR01 Glennie.Compact.CyclicTraceNullR01

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
  have h := response_discrepancy_radius jordanLinear (diagonalNProductLinear n)
    ⟨f, fun x => (hf x).trans (nA_eq_norm x)⟩ jordan_norm diagonalN_product_norm
    U_norm diagonalN_quadratic_norm μ hμ (by bound) R hR x y z hx hy hz
  simpa only [native_response_eq, diagonalN_phi_zero, sub_zero] using h

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
    (|weightedScore noisy| - 12 * ε) / (1216 * Real.sqrt 2) ≤ μ := by
  exact frame_defect_lower (diagonalNProductLinear n)
    ⟨f, fun x => (hf x).trans (nA_eq_norm x)⟩ diagonalN_product_norm
    diagonalN_quadratic_norm diagonalN_phi_zero T hT noisy ε μ hμ hreadout (by bound)

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
  exact frame_defect_lower jE ⟨f, fun x => (hf x).trans (nA_eq_norm x)⟩
    (represented_product_norm (fun a b => jE a b) ρ hj)
    (represented_quadratic_norm (fun a b => jE a b) ρ hj)
    (phiWith_eq_zero_of_compatible_trace (fun a b => jE a b) (Inner.inner ℝ)
      ρ.toLinearMap τ hj hB hcyclic) T hT noisy ε μ hμ hreadout (by bound)

/-- The same 27 fixed bracketed words evaluated in any marked product. -/
def witnessX : Albert := ⟨-1,0,1,0,0,0⟩
def witnessY : Albert := ⟨0,0,0,octScalar 1,octI,octScalar 1⟩
def nativeMarks : Fin 3 → Albert := ![witnessX,witnessY,witnessZ]
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

set_option maxHeartbeats 3000000 in
/-- The native word certificate supplies a unique unit-, mark-, product- and
metric-preserving embedding into the ambient carrier. -/
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
  let b := Glennie.Compact.NativeWordTableR01.wordBasis
  let v := candidateWordValues e a j
  let L : Albert →ₗ[ℝ] E := b.constr ℝ v
  have hb (i : Fin 27) : b i = nativeWordValues i :=
    Glennie.Compact.NativeWordTableR01.wordBasis_eq_nativeWords i
  have hn (i : Fin 27) : L (nativeWordValues i) = v i := by simp [← hb, L]
  have hu : L 1 = e := hn 0
  have hm (i : Fin 3) : L (nativeMarks i) = a i := by
    have h := hn (i.castAdd 23).succ
    fin_cases i <;> exact h
  have hmetric : ∀ x y, Inner.inner ℝ (L x) (L y) = inner x y := by
    suffices he : (_root_.innerₗ E).compl₁₂ L L = _root_.innerₗ Albert from
      fun x y => LinearMap.congr_fun (LinearMap.congr_fun he x) y
    refine LinearMap.ext_basis b b fun i k => ?_
    change Inner.inner ℝ (L (b i)) (L (b k)) = inner (b i) (b k)
    simpa only [hb, hn] using h.gram i k
  have hprod : ∀ x y, L (jordan x y) = j (L x) (L y) := by
    suffices he : jordanLinear.compr₂ L = j.compl₁₂ L L from
      fun x y => LinearMap.congr_fun (LinearMap.congr_fun he x) y
    refine LinearMap.ext_basis b b fun i k => ?_
    change L (jordan (b i) (b k)) = j (L (b i)) (L (b k))
    simp only [L, Module.Basis.constr_basis]
    let p := j (v i) (v k)
    let w := jordan (b i) (b k)
    have hpair : ∀ z, Inner.inner ℝ p (L z) = inner w z := by
      suffices he : (_root_.innerₗ E p).comp L = _root_.innerₗ Albert w from
        fun z => LinearMap.congr_fun he z
      apply b.ext
      intro l
      change Inner.inner ℝ p (L (b l)) = inner w (b l)
      simpa only [p, w, hb, hn] using h.mixed i k l
    have hs : Inner.inner ℝ p p = inner w w := by
      simpa only [p, w, hb] using h.product_sq i k
    have hz : ‖p - L w‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        hmetric, hs, hpair]
      ring
    exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))).symm
  have hwords (i : Fin 27) : v i ∈ generated e a j := by
    apply Submodule.mem_sInf.mpr
    intro K hK
    rcases hK with ⟨he, ha, hj⟩
    fin_cases i <;> simp only [v, candidateWordValues, wordValues] <;> aesop
  have hrange : LinearMap.range L = generated e a j := by
    apply le_antisymm
    · change LinearMap.range (b.constr ℝ v) ≤ _
      rw [b.constr_range]
      exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hwords)
    · apply sInf_le
      refine ⟨⟨1, hu⟩, fun i => ⟨nativeMarks i, hm i⟩, ?_⟩
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact ⟨jordan x y, hprod x y⟩
  refine ⟨L, ⟨hu, hm, hprod, hmetric, (L.isometryOfInner hmetric).injective, hrange⟩, ?_⟩
  rintro J ⟨hJu, hJm, hJp, _⟩
  apply b.ext
  intro i
  rw [hb]
  fin_cases i <;> simp [nativeWordValues, wordValues, hJp, hprod, hJm, hm, hJu, hu]
end
end Glennie.SubmissionR03

@[expose] public section
namespace Glennie.SubmissionR04Quotient
noncomputable section
open Glennie Glennie.Compact.Affine20 Glennie.SubmissionR03
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

private theorem flatBase_eq_source :
    flatBase = Glennie.Compact.Sections.flatBase := rfl

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
  with_unfolding_all change @Continuous _ _ (quotientCoordinateTopology d) _ _
  rw [quotientTopology_eq_source d]
  with_unfolding_all exact Glennie.Compact.LocalOrbitQuotientR01.continuous_forward d


private theorem continuous_inverse_induced
    (d : Glennie.Compact.LocalOrbitQuotientR01.LocalData) :
    Continuous (Glennie.Compact.LocalOrbitQuotientR01.inverse d :
      d.V × Bool → OrbitQuotient d.V) := by
  with_unfolding_all change @Continuous _ _ _ (quotientCoordinateTopology d) _
  rw [quotientTopology_eq_source d]
  with_unfolding_all exact Glennie.Compact.LocalOrbitQuotientR01.continuous_inverse d


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
  refine ⟨d.V, d.openV, ?_, ?_⟩
  · simpa only [flatBase_eq_source, fullLedger_eq_source,
      encode20_eq_source] using d.base
  · let H : OrbitQuotient d.V ≃ₜ d.V × Bool := {
      toFun := Glennie.Compact.LocalOrbitQuotientR01.forward d
      invFun := Glennie.Compact.LocalOrbitQuotientR01.inverse d
      left_inv := Glennie.Compact.LocalOrbitQuotientR01.inverse_forward d
      right_inv := Glennie.Compact.LocalOrbitQuotientR01.forward_inverse d
      continuous_toFun := continuous_forward_induced d
      continuous_invFun := continuous_inverse_induced d }
    refine ⟨H, ?_, ?_⟩
    · intro T
      rfl
    · intro T S
      change (Glennie.Compact.LocalOrbitQuotientR01.orbitSetoid d).r T S ↔
        Glennie.Compact.LocalOrbitQuotientR01.invariant d T =
          Glennie.Compact.LocalOrbitQuotientR01.invariant d S
      exact Glennie.Compact.LocalOrbitQuotientR01.rel_iff_invariant_eq d T S

end
end Glennie.SubmissionR04Quotient

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
structure BasedCubic (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  form : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ
  swap12 : ∀ x y z : E, form ![x, y, z] = form ![y, x, z]
  swap23 : ∀ x y z : E, form ![x, y, z] = form ![x, z, y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (P : BasedCubic E) (e : E)
def cubic  (x : E) : ℝ := P.form (fun _ : Fin 3 => x)
def metric  (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (-1 / 3 : ℝ) • fderiv ℝ
    (fun y : E => fderiv ℝ (fun z : E => Real.log (cubic P z)) y) x
def tangent   : Submodule ℝ E :=
  (fderiv ℝ (cubic P) e).ker
def traceAt   : E →L[ℝ] ℝ := fderiv ℝ (cubic P) e
def rawPair   : E →L[ℝ] E →L[ℝ] ℝ :=
  (traceAt P e).smulRight (traceAt P e) -
    fderiv ℝ (fun z : E => fderiv ℝ (cubic P) z) e
def adjoint  (x : E) : E :=
  (rawPair P e).inverse (fderiv ℝ (cubic P) x)
def product  (x y : E) : E :=
  (1 / 2 : ℝ) • ((adjoint P e (x + y) - adjoint P e x - adjoint P e y) +
    traceAt P e x • y + traceAt P e y • x -
    (traceAt P e x * traceAt P e y - rawPair P e x y) • e)
section TangentOperators
variable (P : BasedCubic E) (e : E)
local notation "W" => tangent P e
real_operator_norms tangentDualNormedAddCommGroup tangentDualNormedSpace W ℝ
real_operator_norms tangentBilinearNormedAddCommGroup tangentBilinearNormedSpace W (W →L[ℝ] ℝ)
real_operator_norms tangentTrilinearNormedAddCommGroup tangentTrilinearNormedSpace W (W →L[ℝ] W →L[ℝ] ℝ)
real_operator_norms tangentEndNormedAddCommGroup tangentEndNormedSpace W W
real_operator_norms tangentVectorBilinearNormedAddCommGroup tangentVectorBilinearNormedSpace W (W →L[ℝ] W)
real_operator_norms tangentInverseNormedAddCommGroup tangentInverseNormedSpace (W →L[ℝ] ℝ) W
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
real_operator_norms taskAmbientDualNorm taskAmbientDualSpace E ℝ
real_operator_norms taskAmbientBilinearNorm taskAmbientBilinearSpace E (E →L[ℝ] ℝ)
real_operator_norms taskAmbientTrilinearNorm taskAmbientTrilinearSpace E (E →L[ℝ] E →L[ℝ] ℝ)
real_operator_norms taskAmbientEndNorm taskAmbientEndSpace E E
real_operator_norms taskAmbientVectorBilinearNorm taskAmbientVectorBilinearSpace E (E →L[ℝ] E)
real_operator_norms taskAmbientInverseNorm taskAmbientInverseSpace (E →L[ℝ] ℝ) E
/-- Literal derivative of the varying normalized log-Hessian metric. -/
def ambientMetricD1  (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (metric P) x
/-- Three-term affine Koszul covector, before any Hessian-symmetry shortcut. -/
def ambientKoszulTensor  (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (ambientMetricD1 P x + (ambientMetricD1 P x).flip -
    ((((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv).toContinuousLinearMap :
      (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ).comp
      (ambientMetricD1 P x).flip))
/-- Actual ambient affine connection coefficient. Positivity later proves that
the total metric inverse is the genuine inverse near the normalized base. -/
def ambientConnection  (x : E) : E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)
    (metric P x).inverse).comp (ambientKoszulTensor P x)
/-- Actual covariant derivative in a constant affine direction. -/
def ambientCovariantDerivative  (u : E)
    (Y : E → E) (x : E) : E :=
  fderiv ℝ Y x u + ambientConnection P x u (Y x)
/-- Actual curvature on all ambient vectors. The constant direction fields
commute, so their Lie bracket vanishes. This is not a product definition. -/
def ambientCurvature  (x u v w : E) : E :=
  ambientCovariantDerivative P u (ambientCovariantDerivative P v (fun _ : E => w)) x -
    ambientCovariantDerivative P v (ambientCovariantDerivative P u (fun _ : E => w)) x
end
end Glennie.SubmissionR04Intrinsic
namespace Glennie.SubmissionR04Intrinsic.Local
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (P : BasedCubic E) (e : E)
def toSource  : SymmetricTrilinearForm E where
  form := P.form
  swap12 := P.swap12
  swap23 := P.swap23




/- The function and both derivatives are literal, not desired formulas. -/
theorem traceAt_eq_source   :
    traceAt P e = normTrace (toSource P) e := rfl

theorem rawPair_eq_source   :
    rawPair P e = rawTraceForm (toSource P) e := rfl

/- The factor 3 is a theorem requiring N(e)=1; it is not definitional. -/
theorem rawPair_eq_three_metric
    (he : cubic P e = 1) (x y : E) :
    rawPair P e x y = 3 * metric P e x y := rawTraceForm_eq_three_logMetric (toSource P) e he x y

theorem traceAt_eq_three_metric_unit
    (he : cubic P e = 1) (x : E) :
    traceAt P e x = 3 * metric P e x e := by
  have hepos : 0 < diagonalCubic (toSource P).form e := by
    change 0 < cubic P e
    rw [he]
    norm_num
  change fderiv ℝ (diagonalCubic (toSource P).form) e x =
    3 * logHessianForm (toSource P) e x e
  rw [logHessianForm_symm (toSource P) hepos x e,
    logHessianForm_radial_at_one (toSource P) e x he]
  ring

variable [FiniteDimensional ℝ E]

/- Build the continuous raw-pairing equivalence from the EXISTING algebraic
nondegeneracy producer. This does not build the tangent metric dual or K. -/
theorem rawPair_isInvertible
    (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) :
    (rawPair P e).IsInvertible := by
  refine ⟨positiveDualEquiv (rawPair P e) ?_, rfl⟩
  intro x hx
  rw [rawPair_eq_three_metric P e he]
  exact mul_pos (by norm_num) (hp x hx)

/- Under the unchanged entrance hypotheses, inverse's zero fallback is excluded. -/
theorem adjoint_pairing
    (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) (x y : E) :
    rawPair P e (adjoint P e x) y = fderiv ℝ (cubic P) x y := congrArg (fun L : E →L[ℝ] ℝ => L y)
    ((rawPair_isInvertible P e he hp).self_apply_inverse (fderiv ℝ (cubic P) x))

/- hB is any proof for the source representation: proof identity is immaterial. -/
theorem adjoint_eq_source
    (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x)
    (hB : (rawBilinearForm (toSource P) e).Nondegenerate) (x : E) :
    adjoint P e x = intrinsicAdjoint (toSource P) e hB x := by
  apply intrinsicAdjoint_unique (toSource P) e hB x
  intro y
  exact adjoint_pairing P e he hp x y

theorem product_eq_source
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
open Glennie
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem nativeTraceLinear_eq_source :
    nativeTraceLinear = AlbertRecognition.traceLinear := by
  ext x
  rfl

theorem nativeTangent_eq_source : NativeTangent = AlbertRecognition.V := by
  change nativeTraceLinear.ker = AlbertRecognition.traceLinear.ker
  rw [nativeTraceLinear_eq_source]

def nativeToSource : NativeTangent ≃ₗ[ℝ] AlbertRecognition.V :=
  LinearEquiv.ofEq _ _ nativeTangent_eq_source

theorem nativeToSource_K (u v : NativeTangent) :
    nativeToSource (nativeK u v) =
      AlbertRecognition.KA (nativeToSource u) (nativeToSource v) := by
  rw [AlbertRecognition.KA_apply_apply]
  apply Subtype.ext
  simp only [nativeToSource, LinearEquiv.coe_ofEq_apply]
  rfl

theorem nativeToSource_metric (u v : NativeTangent) :
    nativeMetric u v = AlbertRecognition.gA (nativeToSource u) (nativeToSource v) := by
  simp only [nativeToSource, nativeMetric, AlbertRecognition.gA,
    LinearEquiv.coe_ofEq_apply]

def nativeCurvatureOnV (u v w : AlbertRecognition.V) : AlbertRecognition.V :=
  nativeToSource (nativeCurvature
    (nativeToSource.symm u) (nativeToSource.symm v) (nativeToSource.symm w))

open AlbertRecognition

theorem nativeCurvatureOnV_formula (u v w : V) :
    nativeCurvatureOnV u v w =
      -(gA v w) • u + (gA u w) • v - KA u (KA v w) + KA v (KA u w) := by
  simp only [nativeCurvatureOnV, nativeCurvature, map_add, map_sub, map_smul,
    nativeToSource_K, nativeToSource_metric, LinearEquiv.apply_symm_apply]

end
end Glennie.SubmissionR04Intrinsic

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
open Glennie
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (P : BasedCubic E) (e : E)

variable [CompleteSpace E]
variable [FiniteDimensional ℝ E]

attribute [local instance] tangentDualNormedAddCommGroup tangentDualNormedSpace
  tangentBilinearNormedAddCommGroup tangentBilinearNormedSpace
  tangentTrilinearNormedAddCommGroup tangentTrilinearNormedSpace
  tangentEndNormedAddCommGroup tangentEndNormedSpace
  tangentVectorBilinearNormedAddCommGroup tangentVectorBilinearNormedSpace
  tangentInverseNormedAddCommGroup tangentInverseNormedSpace

open AlbertRecognition AlbertGeometry.Cubic AlbertGeometry.NativeCurvatureDictionary

theorem independentRaisedCubic_frame
    (F : V ≃ₗ[ℝ] tangent P e)
    (hp : ∀ u : E, u ≠ 0 → 0 < metric P e u u)
    (hm : ∀ x y, metric P e (F x : E) (F y : E) = gA x y) (x y : V) :
    independentRaisedCubic P e (F x) (F y) = F (KB (frameCubic (toSource P) e F) x y) := by
  let A := positiveDualEquiv (tangentMetricDual P e)
    (fun u hu => hp u (fun h => hu (Subtype.ext h)))
  apply A.injective
  apply ContinuousLinearMap.ext
  intro w
  obtain ⟨w,rfl⟩ := F.surjective w
  change metric P e (independentRaisedCubic P e (F x) (F y) : E) (F w : E) =
    metric P e (F (KB (frameCubic (toSource P) e F) x y) : E) (F w : E)
  rw [hm, KB_pairing]
  erw [frameCubic_apply]
  have hi : (tangentMetricDual P e).IsInvertible := ⟨A, rfl⟩
  change tangentMetricDual P e
    ((tangentMetricDual P e).inverse (tangentCubicCurried P e (F x) (F y))) (F w) = _
  rw [hi.self_apply_inverse]
  change fullyCurried (tangentCubicForm P e) (F x) (F y) (F w) = _
  rw [fullyCurried_apply]
  simp only [tangentCubicForm, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Submodule.subtypeL_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem frameCubic_q_of_curvature
    (F : V ≃ₗ[ℝ] tangent P e)
    (hp : ∀ u : E, u ≠ 0 → 0 < metric P e u u)
    (hm : ∀ x y, metric P e (F x : E) (F y : E) = gA x y)
    (hr : ∀ x y z, independentCurvature P e (F x) (F y) (F z) =
      F (nativeCurvatureOnV x y z)) :
    q (frameCubic (toSource P) e F) = q referenceCubic := by
  funext x y
  apply LinearMap.ext
  intro z
  apply F.injective
  have h := hr x y z
  simp only [independentCurvature, tangentMetricDual, ContinuousLinearMap.bilinearComp_apply, Submodule.subtypeL_apply, hm,
    independentRaisedCubic_frame P e F hp hm, nativeCurvatureOnV_formula, map_add, map_sub, map_smul] at h
  simp only [q, operatorComm_apply, KB_referenceCubic, map_sub]
  linear_combination (norm := module) -h
end
end Glennie.SubmissionR04Intrinsic

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section

open AlbertGeometry.Cubic AlbertGeometry.NativeCurvatureDictionary
  AlbertGeometry.NativeEuclideanNormBinding

attribute [local instance] tangentDualNormedAddCommGroup tangentDualNormedSpace
  tangentBilinearNormedAddCommGroup tangentBilinearNormedSpace
  tangentTrilinearNormedAddCommGroup tangentTrilinearNormedSpace
  tangentEndNormedAddCommGroup tangentEndNormedSpace
  tangentVectorBilinearNormedAddCommGroup tangentVectorBilinearNormedSpace
  tangentInverseNormedAddCommGroup tangentInverseNormedSpace

open AlbertRecognition AlbertGeometry.UnitTangentNormReconstruction AlbertGeometry.BasedNormDerivativeTransport
  AlbertGeometry.BasedNormAdjointTransport AlbertGeometry.NativeCoordinateDerivatives
  AlbertGeometry.NativeIntrinsicProductBinding AlbertGeometry.AmbientLeviCivitaProduct
  AlbertGeometry.AmbientCurvatureProduct

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
  let FSource : AlbertRecognition.V ≃ₗ[ℝ] tangentSpace (toSource P) e :=
    nativeToSource.symm.trans F
  have hmetricSource : ∀ x y : AlbertRecognition.V,
      logHessianForm (toSource P) e (FSource x : E) (FSource y : E) = AlbertRecognition.gA x y := by bound
  have hcurvatureSource : ∀ x y z : AlbertRecognition.V,
      independentCurvature P e (FSource x) (FSource y) (FSource z) =
        FSource (nativeCurvatureOnV x y z) := by
    intro x y z
    change independentCurvature P e (F (nativeToSource.symm x))
      (F (nativeToSource.symm y)) (F (nativeToSource.symm z)) =
        F (nativeToSource.symm (nativeCurvatureOnV x y z))
    rw [hcurvature]
    simp only [nativeCurvatureOnV, LinearEquiv.symm_apply_apply]
  have hs := AlbertRecognition.q_fiber_reference (frameCubic (toSource P) e FSource)
    (frameCubic_q_of_curvature P e FSource hp hmetricSource hcurvatureSource)
  obtain ⟨I⟩ : Nonempty (BasedNormIso (toSource P) e nativeEuclideanRepresentation nativeCoordinateUnit) := by
    let D := FSource.symm.trans nativeMetricFrame
    have hmetricD : ∀ u v : tangentSpace (toSource P) e,
        logHessianForm nativeEuclideanRepresentation nativeCoordinateUnit (D u) (D v) =
          logHessianForm (toSource P) e u v := by
      intro u v
      dsimp only [D, LinearEquiv.trans_apply]
      rw [nativeMetricFrame_metric, ← hmetricSource, FSource.apply_symm_apply, FSource.apply_symm_apply]
    rcases hs with hp | hn
    · refine ⟨basedNormIsoOfTangent (toSource P) e he nativeEuclideanRepresentation
        nativeCoordinateUnit nativeNormalization D hmetricD ?_⟩
      intro u
      obtain ⟨x,rfl⟩ := FSource.surjective u
      simp only [D, LinearEquiv.trans_apply, FSource.symm_apply_apply]
      rw [nativeMetricFrame_cubic]
      have h := congrArg (fun B : SymmetricCubic => B.form x x x) hp
      simpa only [frameCubic_apply] using h.symm
    · refine ⟨basedNormIsoOfTangent (toSource P) e he nativeEuclideanRepresentation
        nativeCoordinateUnit nativeNormalization (D.trans (LinearEquiv.neg ℝ)) ?_ ?_⟩
      · intro u v
        simp only [LinearEquiv.trans_apply, LinearEquiv.neg_apply, Submodule.coe_neg, map_neg,
          ContinuousLinearMap.neg_apply, neg_neg]
        exact hmetricD u v
      · intro u
        obtain ⟨x,rfl⟩ := FSource.surjective u
        simp only [D, LinearEquiv.trans_apply, FSource.symm_apply_apply, LinearEquiv.neg_apply,
          Submodule.coe_neg]
        rw [cubic_three_neg, nativeMetricFrame_cubic]
        have h := congrArg (fun B : SymmetricCubic => B.form x x x) hn
        simpa only [frameCubic_apply, scalarCubic_form, neg_mul, one_mul] using h.symm
  let A : E ≃ₗ[ℝ] Albert := I.equiv.toLinearEquiv.trans delta
  have hprod (x y : E) :
      A (intrinsicProduct (toSource P) e (rawBilinearForm_nondegenerate (toSource P) e he hp) x y) =
        jordan (A x) (A y) := by
    have h := intrinsicProduct_pull I (rawBilinearForm_nondegenerate (toSource P) e he hp)
      nativeRawBilinear_nondegenerate x y
    change I.equiv (intrinsicProduct (toSource P) e
      (rawBilinearForm_nondegenerate (toSource P) e he hp) x y) =
        nativeIntrinsicProduct (I.equiv x) (I.equiv y) at h
    exact (congrArg delta h).trans (delta_nativeIntrinsicProduct (I.equiv x) (I.equiv y))
  have hu : A e = 1 := by
    change delta (I.equiv e) = 1
    rw [I.map_unit, delta_nativeCoordinateUnit]
  have hm' : ∀ x y, metric P e x y = inner (A x) (A y) / 3 := by
    intro x y
    have h := I.rawTraceForm_pull x y
    rw [AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso.rawTraceForm_eq_three_logMetric
      (toSource P) e he, native_rawTraceForm] at h
    change logHessianForm (toSource P) e x y = inner (delta (I.equiv x)) (delta (I.equiv y)) / 3
    linarith
  have ht : ∀ x, traceAt P e x = trace (A x) := by
    intro x
    rw [traceAt_eq_three_metric_unit P e he, hm', hu, inner_unit_right]
    ring
  have hj' : ∀ x y, A (product P e x y) = jordan (A x) (A y) := by
    intro x y
    rw [product_eq_source P e he hp
      (AlbertGeometry.BasedNormAdjointTransport.rawBilinearForm_nondegenerate
        (toSource P) e he hp)]
    exact hprod x y
  obtain ⟨V, hV, hb, htwo, hc⟩ :=
    Glennie.Compact.ObservationTransport.local_reconstruction A hu ht hj'
  refine ⟨{
    A := A
    map_unit := hu
    map_norm := ?_
    map_metric := hm'
    map_raw_pairing := ?_
    map_trace := ht
    map_product := hj'
    map_connection := by
      intro x y
      change A (ambientGamma (toSource P) e x y) = _
      rw [ambientGamma_at_one_eq_neg_product (toSource P) e he hp, map_neg, hprod]
    map_curvature := by
      intro u v w
      change A (AlbertGeometry.AmbientCurvatureProduct.ambientCurvature (toSource P) e u v w) = _
      rw [ambientCurvature_at_one_eq_neg_product_commutator (toSource P) e he hp]
      simp only [map_neg, map_sub, hprod]
    V := V
    V_open := hV
    flat_mem := hb
    two_orbits := htwo
    score_complete := hc
    q26_iff_ledger := Glennie.Compact.ObservationTransport.q26_iff_ledger A hu ht hj'
    score_eq_two_phi := Glennie.Compact.ObservationTransport.score_eq_two_phi A hu ht hj'
    atoms_generate := Glennie.Compact.ObservationTransport.atoms_generate A hu ht hj' hc
    atom_stabilizer := Glennie.Compact.ObservationTransport.atom_stabilizer A hu ht hj' hc
    atom_derivation := Glennie.Compact.ObservationTransport.atom_derivation A hu ht hj' hc }⟩
  · intro x
    change newtonCubicNorm (delta (I.equiv x)) = _
    rw [← diagonal_nativeEuclideanRepresentation]
    exact I.map_norm x
  · intro x y
    rw [rawPair_eq_three_metric P e he, hm']
    ring

end
end Glennie.SubmissionR04Intrinsic
