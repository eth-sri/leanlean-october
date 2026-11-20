/- Unified independent native and admitted orbit-quotient statement surface. -/
module
public import Glennie.Compact.LocalOrbitQuotientR01
public import Glennie.Diagonalization
public import Glennie.Compact.OperationalPhi
public import Glennie.Theorems.Frames
public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Glennie.Compact.NearbyOrbitsClosed
public import Glennie.NativeOrderedFrameGenerationR01
public import Glennie.Compact.ReadoutRobustnessR01
public import Glennie.NativeGenerationEndpointR01
public import Glennie.NativeGenerationStabilizersR01
public import Glennie.Compact.NativeWordTableBasisR01
public import Glennie.Compact.VariableDiagonalDefectReadoutR01
public import Glennie.Compact.NormCompatibleNullTargetR01
public import Glennie.Compact.InputDisplacementR01
public import Glennie.Compact.NativeQ20AdapterR01
public import Mathlib.Analysis.Quaternion
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Basic
public import AlbertGeometry.BasedNormAdjointTransport
public import AlbertGeometry.TangentRecognition
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

theorem phi_nonzero_generation_stabilizer
    (x y z : Albert) (hphi : phi x y z ≠ 0) :
    (∀ K : Submodule ℝ Albert, (1 : Albert) ∈ K →
      (JordanClosed K) →
      x ∈ K → y ∈ K → z ∈ K → K = ⊤) ∧
    (∀ g : CompactAutomorphism,
      g.equiv x = x → g.equiv y = y → g.equiv z = z →
      g.equiv = LinearEquiv.refl ℝ Albert) ∧
    (∀ D : Albert →ₗ[ℝ] Albert,
      (∀ p q, D (jordan p q) = jordan (D p) q + jordan p (D q)) →
      D x = 0 → D y = 0 → D z = 0 → D = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun K h1 hJ hx hy hz =>
      NativeGenerationEndpointR01.eq_top_of_phi_ne_zero K h1 hJ x y z hx hy hz hphi
  · exact fun g => NativeGenerationStabilizersR01.automorphism_eq_refl_of_phi_ne_zero g x y z hphi
  · exact fun D hD => NativeGenerationStabilizersR01.derivation_eq_zero_of_phi_ne_zero D hD x y z hphi

theorem nearby_sign_rigidity :
    ∃ V : Set Ledger54, IsOpen V ∧ fullLedger flatBase ∈ V ∧
      ∀ T S : Triple, (IsFrameTriple T) →
        (IsFrameTriple S) → fullLedger T ∈ V →
        fullLedger T = fullLedger S →
        ((phiOf T < 0 ∧ phiOf S < 0) ∨ (0 < phiOf T ∧ 0 < phiOf S)) →
        ∃ k : CompactAutomorphism, mapAtoms k S = T :=
  ⟨Set.univ, isOpen_univ, trivial, fun T S hT hS _ =>
    Glennie.Compact.PairNormNearby.orbit_of_same_sign T S hT hS⟩

/-- A specific native near-flat full-fiber margin in a supplied open ledger neighborhood. -/
theorem near_flat_scalar_margin :
    ∃ V : Set Ledger54, IsOpen V ∧ fullLedger flatBase ∈ V ∧
      ∀ T : Triple, (IsFrameTriple T) → fullLedger T ∈ V →
        1 / 27 < |phiOf T| := by
  let d := Glennie.Compact.NearbyOrbitsClosed.localData
  exact ⟨encode20 ⁻¹' d.V, d.openV.preimage Glennie.Compact.FrameTopology.continuous_encode20,
    d.base, fun _ hT hb => d.margin hT hb⟩

private theorem continuous_coordinateTriple : Continuous
    (fun T : Triple => fun a i => Albert.coordinateEquiv (T a i)) :=
  continuous_pi fun a => continuous_pi fun i =>
    Albert.coordinateLinearEquiv.continuous_of_finiteDimensional.comp
      ((continuous_apply i).comp (continuous_apply a))

-- Keep the common local-chart contract literally expanded in the public statements.
local macro "NearFlat " v:ident ", " conclusion:term : term =>
  `(∃ ($v:ident : Set (Fin 20 → ℝ)), IsOpen $v ∧ encode20 (fullLedger flatBase) ∈ $v ∧ $conclusion)

local macro "WithSections " v:ident p:ident n:ident ", " conclusion:term : term =>
  `(∃ ($p:ident $n:ident : (Fin 20 → ℝ) → Triple),
    ContinuousOn (fun b => fun a i => Albert.coordinateEquiv ($p b a i)) $v ∧
    ContinuousOn (fun b => fun a i => Albert.coordinateEquiv ($n b a i)) $v ∧
    (∀ b ∈ $v, IsFrameTriple ($p b)) ∧ (∀ b ∈ $v, IsFrameTriple ($n b)) ∧
    (∀ b ∈ $v, encode20 (fullLedger ($p b)) = b) ∧
    (∀ b ∈ $v, encode20 (fullLedger ($n b)) = b) ∧ $conclusion)

theorem nearby_fibres_two_orbits :
    NearFlat V,
      WithSections V secPos secNeg,
        (∀ b ∈ V, fullLedger (secPos b) = decode20 b) ∧
        (∀ b ∈ V, fullLedger (secNeg b) = decode20 b) ∧
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) ∧
        (∀ b ∈ V, fibre54 b = autOrbit (secNeg b) ∪ autOrbit (secPos b)) ∧
        (∀ b ∈ V, Disjoint (autOrbit (secNeg b)) (autOrbit (secPos b))) ∧
        (∀ b ∈ V, fibre20 b = fibre54 b) := by
  let d := Glennie.Compact.NearbyOrbitsClosed.localData
  refine ⟨d.V, d.openV, d.base, d.pos, d.neg,
    continuous_coordinateTriple.comp_continuousOn d.contPos,
    continuous_coordinateTriple.comp_continuousOn d.contNeg,
    d.framePos, d.frameNeg, d.chartPos, d.chartNeg, fun _ hb => d.ledgerPos hb,
    fun _ hb => d.ledgerNeg hb, d.phiPos, d.phiNeg, d.cover, fun _ hb => d.disjoint hb,
    fun b _ => Glennie.Compact.NearbyOrbits.fibre20_eq_fibre54 b⟩

private theorem local_q26_on (d : Glennie.Compact.NearbyOrbitsClosed.LocalData)
    (T S : Triple) (hT : IsFrameTriple T) (hS : IsFrameTriple S)
    (hb : encode20 (fullLedger T) ∈ d.V) :
    score T ≠ 0 ∧ ((∃ k : CompactAutomorphism, mapAtoms k S = T) ↔
      q26 T = q26 S ∧
      ((score T < 0 ∧ score S < 0) ∨ (0 < score T ∧ 0 < score S))) := by
  have hn : phiOf T ≠ 0 := abs_pos.mp (lt_trans (by norm_num) (d.margin hT hb))
  have hneg (u : ℝ) : 2*u < 0 ↔ u < 0 := by constructor <;> intro h <;> linarith
  simp only [score_eq_two_phi, q26_eq_iff_fullLedger_eq T S hT hS,
    mul_pos_iff_of_pos_left (zero_lt_two : (0:ℝ) < 2), hneg]
  refine ⟨mul_ne_zero (by norm_num) hn, ?_, fun ⟨hL, h⟩ =>
    Glennie.Compact.PairNormNearby.orbit_of_same_sign T S hT hS hL h⟩
  rintro ⟨g, rfl⟩
  rw [Glennie.Compact.NearbyOrbits.phiOf_mapAtoms] at hn
  rw [Glennie.Compact.NearbyOrbits.phiOf_mapAtoms]
  exact ⟨ledger54_map g S, (lt_or_gt_of_ne hn).imp (fun h => ⟨h,h⟩) (fun h => ⟨h,h⟩)⟩

theorem local_q26_score_orbit_test :
    NearFlat V,
      ∀ T S : Triple, (IsFrameTriple T) → (IsFrameTriple S) →
        encode20 (fullLedger T) ∈ V →
        score T ≠ 0 ∧
        ((∃ k : CompactAutomorphism, mapAtoms k S = T) ↔
          q26 T = q26 S ∧
          ((score T < 0 ∧ score S < 0) ∨ (0 < score T ∧ 0 < score S))) :=
  let d := Glennie.Compact.NearbyOrbitsClosed.localData
  ⟨d.V, d.openV, d.base, local_q26_on d⟩

/-- Every compact region of the established admitted chart has a positive
uniform Phi margin for its entire actual ordered-frame fiber. -/
theorem compact_local_phi_margin :
    NearFlat V,
      ∀ K : Set V, IsCompact K →
        ∃ m > 0, ∀ T : Triple, (IsFrameTriple T) →
          ∀ hb : encode20 (fullLedger T) ∈ V,
            (⟨encode20 (fullLedger T), hb⟩ : V) ∈ K →
              m ≤ |phiOf T| := by
  let d := Glennie.Compact.NearbyOrbitsClosed.localData
  exact ⟨d.V, d.openV, d.base, fun _ _ =>
    ⟨1 / 27, by norm_num, fun T hT hb _ => (d.margin hT hb).le⟩⟩

/-- The native raw trace norm, used to state perturbation radii independently. -/
def nA (x : Albert) : ℝ := Real.sqrt (inner x x)

private theorem nA_eq_norm (x : Albert) : nA x = ‖x‖ :=
  (congrArg Real.sqrt (native_norm_sq x).symm).trans (Real.sqrt_sq (norm_nonneg x))

private def asIsometry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Albert →ₗ[ℝ] E) (hf : ∀ x, ‖f x‖ = nA x) : Albert →ₗᵢ[ℝ] E :=
  ⟨f, fun x => (hf x).trans (nA_eq_norm x)⟩

open Compact.LocalOrbitQuotientR01 Compact.NativeQ20AdapterR01 in
/-- On a compact feasible chart region, nearby feasible coordinates recover
an actual frame triple up to one simultaneous automorphism, atom by atom.
Both the true and proposed coordinates must belong to the compact region. -/
theorem compact_feasible_element_recovery :
    NearFlat V,
      WithSections V secPos secNeg,
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) ∧
        (∀ K : Set V, IsCompact K → ∀ ζ : ℝ, 0 < ζ →
          ∃ η > 0, ∀ T : Triple, (IsFrameTriple T) →
            ∀ hb : encode20 (fullLedger T) ∈ V,
              (⟨encode20 (fullLedger T), hb⟩ : V) ∈ K →
              ∀ b : V, b ∈ K →
                dist (⟨encode20 (fullLedger T), hb⟩ : V) b < η →
                  ∃ g : CompactAutomorphism, ∀ a i : Fin 3,
                    nA (T a i - g.equiv
                      ((if 0 < phiOf T then secPos b.1 else secNeg b.1) a i)) < ζ) := by
  let d := Glennie.Compact.NearbyOrbitsClosed.localData
  refine ⟨d.V, d.openV, d.base, d.pos, d.neg,
    continuous_coordinateTriple.comp_continuousOn d.contPos,
    continuous_coordinateTriple.comp_continuousOn d.contNeg,
    d.framePos, d.frameNeg, d.chartPos, d.chartNeg, d.phiPos, d.phiNeg, ?_⟩
  intro K hK ζ hζ
  obtain ⟨η, hη, hrec⟩ := compact_feasible_recovery d K hK ζ hζ
  refine ⟨η, hη, fun T hT hb hTK b hbK hdist => ?_⟩
  let Td : Admitted d := ⟨T, hT, hb⟩
  obtain ⟨g, hg⟩ := hrec Td hTK b hbK hdist
  refine ⟨g, fun a i => ?_⟩
  have h := (norm_le_pi_norm _ i).trans_lt ((norm_le_pi_norm _ a).trans_lt hg)
  simpa [nA_eq_norm, branchSection, sheet, Td, mapAtoms] using h

/-- A strict six-reading margin selects the correct continuous branch for
compact feasible-coordinate recovery. The proposed chart remains feasible. -/
theorem compact_noisy_feasible_element_recovery :
    NearFlat V,
      WithSections V secPos secNeg,
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) ∧
        (∀ K : Set V, IsCompact K → ∀ ζ : ℝ, 0 < ζ →
          ∃ η > 0, ∀ T : Triple, (IsFrameTriple T) →
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
  have h : (0 < weightedScore noisy) = (0 < phiOf T) := by
    rcases signed_readout_margin T noisy ε hε herr hm with hn | hp <;> simp [*, LT.lt.not_gt]
  simpa only [h] using hrecover T hT hbT hTK b hbK hdist

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
      (JordanClosed K) →
      x' ∈ K → y' ∈ K → z' ∈ K → K = ⊤) ∧
    (∀ g : CompactAutomorphism,
      g.equiv x' = x' → g.equiv y' = y' → g.equiv z' = z' →
      g.equiv = LinearEquiv.refl ℝ Albert) := by
  simp only [nA_eq_norm, f0_eq, f1_eq, f2_eq] at hx hy hz hx' hy' hz' hdx hdy hdz
  have hd := Compact.NativeNormKernel.phi_displacement_18
    (encoder (T 0)) (encoder (T 1)) (encoder (T 2)) x' y' z' R δ hR
    hx hy hz hx' hy' hz' hdx hdy hdz
  have he := (Compact.ReadoutRobustnessR01.phi_error T noisy ε hreadout).trans hallowance
  have h : |noisyPhi noisy - phi x' y' z'| ≤ ξ + 18 * R^8 * δ :=
    (abs_sub_le _ (phiOf T) _).trans (add_le_add he hd)
  have hs := Compact.ReadoutRobustnessR01.scalar_sign_certificate h (by linarith)
  obtain ⟨hg, hk, -⟩ := phi_nonzero_generation_stabilizer _ _ _ (hs.elim (fun h => h.2.ne) (fun h => h.2.ne'))
  exact ⟨hs, hg, hk⟩

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
  simp only [nA_eq_norm] at hdef hx hy hz
  exact Glennie.Compact.VariableDiagonalDefectReadoutR01.native_diagonalN_defect_response
    (asIsometry f hf) μ R hμ hR hdef x y z hx hy hz

/-- An actual-frame noisy score forces a uniform multiplication defect for
any norm-preserving linear map into a coordinatewise Euclidean target. -/
theorem frame_noisy_diagonalN_defect_lower {n : ℕ}
    (f : Albert →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : ∀ x : Albert, ‖f x‖ = nA x)
    (T : Triple) (hT : IsFrameTriple T)
    (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤
        μ * nA a * nA b) :
    (|weightedScore noisy| - 12 * ε) / (1216 * Real.sqrt 2) ≤ μ := by
  simp only [nA_eq_norm] at hdef
  exact Compact.NativeDefectReadoutR01.frame_noisy_defect_lower T hT noisy ε μ hreadout
    (Compact.VariableDiagonalDefectReadoutR01.native_diagonalN_defect_response
      (asIsometry f hf) μ _ hμ (Real.sqrt_nonneg _) hdef)

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
    (T : Triple) (hT : IsFrameTriple T)
    (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - jE (f a) (f b)‖ ≤ μ * nA a * nA b) :
    (|weightedScore noisy| - 12 * ε) / (1216 * Real.sqrt 2) ≤ μ := by
  simp only [nA_eq_norm] at hdef
  open Compact.NativeDefectReadoutR01 Compact.NormCompatibleNullTargetR01 Compact.CyclicTraceNullR01 in
  refine frame_noisy_defect_lower T hT noisy ε μ hreadout fun x y z hx hy hz => ?_
  exact native_defect_response jE (asIsometry f hf) (represented_product_norm _ ρ hj)
    (represented_quadratic_norm _ ρ hj) μ _ hμ (Real.sqrt_nonneg _) hdef x y z hx hy hz
    (phiWith_eq_zero_of_compatible_trace _ _ ρ.toLinearMap τ hj hB hcyclic (f x) (f y) (f z))

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

set_option maxHeartbeats 800000 in
open Glennie.Compact.NativeWordTableR01 in
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
  classical
  let b := wordBasis
  let v := candidateWordValues e a j
  let L := b.constr ℝ v
  have hb i : b i = nativeWordValues i := wordBasis_eq_nativeWordValues i
  have hbL (i) : L (b i) = v i := b.constr_basis ℝ v i
  have hL (i) : L (nativeWordValues i) = v i := hb i ▸ hbL i
  have metricEq : (innerₗ E).compl₁₂ L L = nativeInnerLinear := LinearMap.ext_basis b b fun i k => by
    change Inner.inner ℝ (L (b i)) (L (b k)) = inner (b i) (b k)
    simpa only [hb, hL] using h.gram i k
  have hmetric (x y : Albert) : Inner.inner ℝ (L x) (L y) = inner x y :=
    DFunLike.congr_fun (DFunLike.congr_fun metricEq x) y
  have hJ : jordanLinear.compr₂ L = j.compl₁₂ L L := LinearMap.ext_basis b b fun i k => by
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, jordanLinear_apply, hb, hL]
    let p := j (v i) (v k)
    let q := jordan (nativeWordValues i) (nativeWordValues k)
    change L q = p
    have hmix : (innerₗ E p).comp L = nativeInnerLinear q := b.ext fun l => by
      change Inner.inner ℝ p (L (b l)) = inner q (b l)
      simpa only [hb, hL] using h.mixed i k l
    have hz : Inner.inner ℝ p (L q) = inner q q := DFunLike.congr_fun hmix q
    have hp : Inner.inner ℝ p p = inner q q := h.product_sq i k
    apply sub_eq_zero.mp ∘ (_root_.inner_self_eq_zero (𝕜 := ℝ)).mp
    simp only [_root_.inner_sub_left, _root_.inner_sub_right, real_inner_comm p (L q),
      hp, hmetric, hz, sub_self]
  have hprod (x y : Albert) : L (jordan x y) = j (L x) (L y) :=
    DFunLike.congr_fun (DFunLike.congr_fun hJ x) y
  have hu : L 1 = e := hL 0
  have hm (i : Fin 3) : L (nativeMarks i) = a i := by
    fin_cases i
    · exact hL 1
    · exact hL 2
    · exact hL 3
  have hinj : Function.Injective L := (L.isometryOfInner hmetric).injective
  have hrange : LinearMap.range L = generated e a j := by
    apply le_antisymm
    · rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      rw [Function.comp_apply, hbL]
      refine Submodule.mem_sInf.mpr fun K ⟨he, ha, hk⟩ => ?_
      fin_cases i <;> simp (config := { maxDischargeDepth := 5 }) [v, candidateWordValues, wordValues, he, ha, hk]
    · refine sInf_le ⟨⟨1, hu⟩, fun i => ⟨nativeMarks i, hm i⟩, ?_⟩
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact ⟨jordan x y, hprod x y⟩
  refine ⟨L, ⟨hu, hm, hprod, hmetric, hinj, hrange⟩, ?_⟩
  rintro M ⟨hMu, hMm, hMp, -⟩
  refine b.ext fun i => ?_
  rw [hbL, hb, nativeWordValues, map_wordValues M jordan (fun x y => j x y) hMp, hMu]
  simp [v, candidateWordValues, hMm]

end
end Glennie.SubmissionR03

@[expose] public section
namespace Glennie.SubmissionR04Quotient
noncomputable section
open Glennie Glennie.Compact.Affine20 Glennie.SubmissionR03
set_option autoImplicit false
set_option maxHeartbeats 1000000

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
local instance (V : Set ChartPoint) : Setoid (Admitted V) := orbitSetoid V

open Glennie.Compact.LocalOrbitQuotientR01 in
private theorem quotient_continuous (d : Glennie.Compact.NearbyOrbitsClosed.LocalData) :
    Continuous (forward d : OrbitQuotient d.V → d.V × Bool) ∧
      Continuous (inverse d : d.V × Bool → OrbitQuotient d.V) := by
  let top (τ : TopologicalSpace Triple) :=
    @instTopologicalSpaceQuotient (Admitted d.V) (orbitSetoid d.V)
      (@instTopologicalSpaceSubtype Triple _ τ)
  with_unfolding_all change (@Continuous _ _ (top tripleCoordinateTopology) _ (forward d)) ∧
    (@Continuous _ _ _ (top tripleCoordinateTopology) (inverse d))
  rw [tripleCoordinateTopology_eq_native]
  exact ⟨continuous_forward d, continuous_inverse d⟩

open Glennie.Compact.LocalOrbitQuotientR01 in
/-- The actual automorphism quotient of all admitted ordered frames is
homeomorphic to the centered feasible chart and its two algebraic sign sheets. -/
theorem admitted_orbit_quotient_homeomorph :
    ∃ V : Set ChartPoint, IsOpen V ∧
      Glennie.SubmissionR03.encode20 (fullLedger flatBase) ∈ V ∧
      ∃ H : OrbitQuotient V ≃ₜ V × Bool,
        (∀ T : Admitted V, H (Quotient.mk' T) = invariant V T) ∧
        (∀ T S : Admitted V,
          (orbitSetoid V).r T S ↔ invariant V T = invariant V S) := by
  let d := Glennie.Compact.NearbyOrbitsClosed.localData
  refine ⟨d.V, d.openV, d.base,
    ⟨⟨forward d, inverse d, inverse_forward d, forward_inverse d⟩,
      (quotient_continuous d).1, (quotient_continuous d).2⟩, fun _ => rfl, ?_⟩
  exact rel_iff_invariant d

end
end Glennie.SubmissionR04Quotient


@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
set_option autoImplicit false
open Glennie
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [CompleteSpace E]
variable [FiniteDimensional ℝ E]

attribute [local instance] tangentDualNormedAddCommGroup tangentDualNormedSpace
  tangentBilinearNormedAddCommGroup tangentBilinearNormedSpace
  tangentTrilinearNormedAddCommGroup tangentTrilinearNormedSpace
  tangentEndNormedAddCommGroup tangentEndNormedSpace
  tangentVectorBilinearNormedAddCommGroup tangentVectorBilinearNormedSpace
  tangentInverseNormedAddCommGroup tangentInverseNormedSpace

open AlbertRecognition AlbertGeometry.Cubic AlbertGeometry.TangentRecognition

private theorem nativeCurvature_reference (u v w : V) : nativeCurvature u v w = -(D u v w) := by
  have hK (x y : V) : nativeK x y = KA x y := by
    apply Subtype.ext
    rw [KA_apply, project_coe]
    rfl
  have hg (x y : V) : nativeMetric x y = gA x y := rfl
  simp only [nativeCurvature, hg, hK, D, wedge_apply, q, operatorComm, KB_referenceCubic,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  change (-(gA v w) • u + gA u w • v - KA u (KA v w) + KA v (KA u w) : V) = _
  rw [neg_smul]
  abel

private theorem frame_q (P : BasedCubic E) (e : E)
    (F : V ≃ₗ[ℝ] tangent P e)
    (hm : ∀ x y : V, metric P e (F x : E) (F y : E) = gA x y)
    (hc : ∀ x y z : V, independentCurvature P e (F x) (F y) (F z) = F (-(D x y z))) :
    q (frameCubic P e F) = q referenceCubic := by
  have hg (x y : V) : tangentMetricDual P e (F x) (F y) = gA x y := hm x y
  have hinv : (tangentMetricDual P e).IsInvertible := by
    apply AlbertGeometry.BasedNormAdjointTransport.dual_isInvertible
    intro u hu
    obtain ⟨x, rfl⟩ := F.surjective u
    rw [hg] at hu
    rw [(gA_self_eq_zero x).mp hu, map_zero]
  let C := frameCubic P e F
  have hK (x y : V) : independentRaisedCubic P e (F x) (F y) = F (KB C x y) := by
    change (tangentMetricDual P e).inverse (tangentCubicCurried P e (F x) (F y)) = _
    apply hinv.inverse_apply_eq.mpr
    ext u
    obtain ⟨z, rfl⟩ := F.surjective u
    change tangentCubicCurried P e (F x) (F y) (F z) = tangentMetricDual P e (F (KB C x y)) (F z)
    rw [hg, KB_pairing]
    change fullyCurried (tangentCubicForm P e) (F x) (F y) (F z) = _
    rw [fullyCurried_apply, frameCubic_apply]
    change P.form _ = P.form _
    congr 1
    funext i
    fin_cases i <;> rfl
  funext x y
  apply LinearMap.ext
  intro z
  have h := congrArg F.symm (hc x y z)
  simp only [independentCurvature, hg, hK, map_add, map_sub, map_smul,
    LinearEquiv.symm_apply_apply, D, wedge_apply, LinearMap.add_apply, q, operatorComm,
    LinearMap.sub_apply, LinearMap.comp_apply] at h
  simp only [q, operatorComm, LinearMap.sub_apply, LinearMap.comp_apply]
  change KB C x (KB C y z) - KB C y (KB C x z) = _
  linear_combination (norm := module) -h

end
end Glennie.SubmissionR04Intrinsic

end
end
end

namespace Glennie.SubmissionR04Intrinsic.Local
noncomputable section

open Glennie.Compact
open SubmissionR03 (fullLedger autOrbit)
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Transport the local observations using only the unit, product and trace of the model. -/
private structure Model (e : E) (t : E → ℝ) (j : E → E → E) where
  A : E ≃ₗ[ℝ] Albert
  unit : A e = 1
  trace : ∀ x, t x = Glennie.trace (A x)
  mul : ∀ x y, A (j x y) = jordan (A x) (A y)

namespace Model
variable {e : E} {t : E → ℝ} {j : E → E → E} (I : Model e t j)
include I

private def triples : Triple E ≃ₜ Triple Albert :=
  Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ =>
    I.A.toContinuousLinearEquiv.toHomeomorph

@[simp] private theorem triples_apply (T : Triple E) (a i : Fin 3) :
    I.triples T a i = I.A (T a i) := rfl

private theorem frames_iff (T : Triple E) :
    (∀ a, Frame e t j (T a)) ↔ IsFrameTriple (I.triples T) := by
  apply forall_congr'
  intro a
  constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;> constructor <;>
    simp_all only [triples_apply, ← I.trace, ← I.mul, ← I.A.map_zero, ← map_add, ← I.unit,
      I.A.injective.eq_iff, forall_const] <;> assumption

@[simp] private theorem ledger_eq (T : Triple E) :
    ledger t j T = fullLedger (I.triples T) := by
  simp only [ledger, fullLedger, pairing, inner, I.trace, I.mul, triples_apply]
  rfl

@[simp] private theorem encoder_map (p : Fin 3 → E) :
    I.A (encoder p) = Glennie.encoder (fun i => I.A (p i)) := map_sub _ _ _

private theorem power_map (p : Fin 3 → E) (s : Fin 2) :
    I.A (power j p s) = SubmissionR03.framePower (fun i => I.A (p i)) s := by
  by_cases h : s = 0 <;> simp [power, SubmissionR03.framePower, SubmissionR03.b0, h, I.mul]

@[simp] private theorem q26_eq (T : Triple E) :
    q26 t j T = SubmissionR03.q26 (I.triples T) := by
  simp only [q26, SubmissionR03.q26, qSingle, qPair, qTriple,
    SubmissionR03.qSingle, SubmissionR03.qPair, SubmissionR03.qTriple,
    pairing, inner, I.trace, I.mul, I.power_map] <;> rfl

@[simp] private theorem quad_map (x y : E) : I.A (quad j x y) = U (I.A x) (I.A y) := by
  simp only [quad, U, I.mul, map_smul, map_sub]

@[simp] private theorem phi_eq (x y z : E) :
    phi t j x y z = Glennie.phi (I.A x) (I.A y) (I.A z) := by
  simp only [phi, Glennie.phi, pairing, inner, I.trace, I.mul, I.quad_map, map_sub]

@[simp] private theorem score_eq (T : Triple E) :
    score e t j T = SubmissionR03.score (I.triples T) := by
  simp only [score, SubmissionR03.score, delta, SubmissionR03.delta, contrast,
    SubmissionR03.contrast, pairing, inner, I.trace, I.mul, I.quad_map, I.encoder_map,
    map_sub, map_smul, map_add, I.unit, half, SubmissionR03.halfAmplitude, Nat.cast_ofNat,
    SubmissionR03.f0_eq, SubmissionR03.f1_eq, SubmissionR03.f2_eq, Glennie.encoder, triples_apply]

private def pushAut (g : Automorphism t j) : CompactAutomorphism where
  equiv := (I.A.symm.trans g.equiv).trans I.A
  map_jordan x y := by
    obtain ⟨x, rfl⟩ := I.A.surjective x
    obtain ⟨y, rfl⟩ := I.A.surjective y
    simp [← I.mul, g.map_product]
  map_trace x := by
    change Glennie.trace (I.A (g.equiv (I.A.symm x))) = Glennie.trace x
    rw [← I.trace, g.map_trace, I.trace, I.A.apply_symm_apply]

private def pullAut (g : CompactAutomorphism) : Automorphism t j where
  equiv := (I.A.trans g.equiv).trans I.A.symm
  map_product x y := I.A.injective (by simp [I.mul, g.map_jordan])
  map_trace x := by simp [I.trace, g.map_trace]

@[simp] private theorem orbit_iff (T S : Triple E) :
    T ∈ orbit t j S ↔ I.triples T ∈ autOrbit (I.triples S) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨I.pushAut g, by funext a i; simp [pushAut, SubmissionR03.mapAtoms, mapAtoms]⟩
  · rintro ⟨g, hg⟩
    refine ⟨I.pullAut g, I.triples.injective ?_⟩
    funext a i
    simpa [pullAut, SubmissionR03.mapAtoms, mapAtoms] using congrFun (congrFun hg a) i

@[simp] private theorem fibre54_iff (b : Chart) (T : Triple E) :
    T ∈ fibre54 e t j b ↔ I.triples T ∈ SubmissionR03.fibre54 b := by
  simp only [fibre54, SubmissionR03.fibre54, Set.mem_ofPred_eq, I.frames_iff, I.ledger_eq]

@[simp] private theorem fibre20_iff (b : Chart) (T : Triple E) :
    T ∈ fibre20 e t j b ↔ I.triples T ∈ SubmissionR03.fibre20 b := by
  simp only [fibre20, SubmissionR03.fibre20, Set.mem_ofPred_eq, I.frames_iff, I.ledger_eq]

private theorem generate (T : Triple E) (hT : ∀ a, Frame e t j (T a))
    (hs : score e t j T ≠ 0) (K : Submodule ℝ E)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, j p q ∈ K) (hAtoms : ∀ a i, T a i ∈ K) : K = ⊤ := by
  apply (Submodule.map_eq_top_iff (e := I.A)).mp
  apply SubmissionR03.atoms_generate_of_score (I.triples T) ((I.frames_iff T).mp hT)
    (I.score_eq T ▸ hs)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨j x y, hJ x hx y hy, I.mul x y⟩
  · exact fun a i => ⟨T a i, hAtoms a i, rfl⟩

private theorem score_two_phi (T : Triple E) :
    score e t j T = 2 * phi t j (encoder (T 0)) (encoder (T 1)) (encoder (T 2)) := by
  simp only [I.score_eq, SubmissionR03.score_eq_two_phi, I.phi_eq, I.encoder_map] <;> rfl

private theorem local_sections (d : Glennie.Compact.NearbyOrbitsClosed.LocalData) :
    TwoOrbitSections e t j d.V := by
  open Glennie.Compact in
  have h54 b : fibre54 e t j b = I.triples ⁻¹' NearbyOrbits.fibre54 b :=
    Set.ext (I.fibre54_iff b)
  have h20 b : fibre20 e t j b = I.triples ⁻¹' NearbyOrbits.fibre54 b := by
    ext T
    simp [NearbyOrbits.fibre20_eq_fibre54, I.fibre20_iff]
  have hor S : orbit t j (I.triples.symm S) = I.triples ⁻¹' FlatOrbit.autOrbit S := by
    ext T
    simp only [Set.mem_preimage, I.orbit_iff, Homeomorph.apply_symm_apply]
  refine ⟨I.triples.symm ∘ d.pos, I.triples.symm ∘ d.neg,
    I.triples.symm.continuous.comp_continuousOn d.contPos,
    I.triples.symm.continuous.comp_continuousOn d.contNeg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Function.comp_apply, I.frames_iff, I.ledger_eq, I.score_eq, Homeomorph.apply_symm_apply,
      SubmissionR03.score_eq_two_phi, h54, h20, hor, ← Set.preimage_union]
  · exact d.framePos
  · exact d.frameNeg
  · exact fun _ hb => d.ledgerPos hb
  · exact fun _ hb => d.ledgerNeg hb
  · exact fun b hb => mul_pos zero_lt_two (d.phiPos b hb)
  · exact fun b hb => mul_neg_of_pos_of_neg zero_lt_two (d.phiNeg b hb)
  · exact fun b hb => congrArg (I.triples ⁻¹' ·) (d.cover b hb)
  · exact fun _ hb => (d.disjoint hb).preimage I.triples
  · exact fun _ _ => trivial

private theorem result {N : E → ℝ} {a B : E → E → ℝ}
    {Γ : E → E → E} {R : E → E → E → E} {nativeN : Albert → ℝ}
    (hN : ∀ x, nativeN (I.A x) = N x)
    (ha : ∀ x y, a x y = inner (I.A x) (I.A y) / 3)
    (hB : ∀ x y, B x y = inner (I.A x) (I.A y))
    (hΓ : ∀ x y, I.A (Γ x y) = -jordan (I.A x) (I.A y))
    (hR : ∀ x y z, I.A (R x y z) =
      -(jordan (I.A x) (jordan (I.A y) (I.A z)) - jordan (I.A y) (jordan (I.A x) (I.A z)))) :
    Nonempty (Result e N t a B j Γ R nativeN) := by
  let d := Glennie.Compact.NearbyOrbitsClosed.localData
  have hScore : ScoreComplete e t j d.V := by
    intro T S hT hS hb
    rw [I.ledger_eq] at hb
    simpa only [I.score_eq, I.orbit_iff, I.q26_eq, SameSign, autOrbit, Set.mem_ofPred_eq] using
      SubmissionR03.local_q26_on d (I.triples T) (I.triples S)
        ((I.frames_iff T).mp hT) ((I.frames_iff S).mp hS) hb
  have hgen (T : Triple E) (hT : Admitted e t j d.V T) :=
    I.generate T hT.1 (hScore T T hT.1 hT.1 hT.2).1
  refine ⟨⟨I.A, I.unit, hN, ha, hB, I.trace, I.mul, hΓ, hR, d.V, d.openV,
    ?_, I.local_sections d, hScore, ?_, I.score_two_phi, hgen, ?_, ?_⟩⟩
  · change SubmissionR03.encode20 (ledger t j (I.triples.symm SubmissionR03.flatBase)) ∈ _
    rw [I.ledger_eq, Homeomorph.apply_symm_apply]
    exact d.base
  · intro T S hT hS
    simpa only [I.q26_eq, I.ledger_eq] using SubmissionR03.q26_eq_iff_fullLedger_eq
      (I.triples T) (I.triples S) ((I.frames_iff T).mp hT) ((I.frames_iff S).mp hS)
  · intro T hT g hg
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.eqLocus_eq_top.mp
    exact hgen T hT _ (NativeGenerationStabilizersR01.eqLocus_closed j g.equiv.toLinearMap LinearMap.id g.map_product (by simp))
      (fun f i => congrFun (congrFun hg f) i)
  · intro T hT D hD hfix
    exact LinearMap.ker_eq_top.mp (hgen T hT _
      (NativeGenerationStabilizersR01.derivation_ker_closed j D hD
        (fun x => I.A.injective (by simp [I.mul])) (fun x => I.A.injective (by simp [I.mul]))) hfix)

end Model
end
end Glennie.SubmissionR04Intrinsic.Local

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
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
  change AlbertRecognition.V ≃ₗ[ℝ] tangent P e at F
  have hc (x y z : AlbertRecognition.V) :
      independentCurvature P e (F x) (F y) (F z) = F (-(AlbertRecognition.D x y z)) := by
    rw [← nativeCurvature_reference]
    exact hcurvature x y z
  obtain ⟨A, hu, hN⟩ :=
    AlbertGeometry.TangentRecognition.norm_unit_of_q P e he F hmetric (frame_q P e F hmetric hc)
  obtain ⟨ht, hb, hJ, hΓ, hR⟩ :=
    AlbertGeometry.TangentRecognition.actual_geometry_of_norm P e he hp A hu hN
  let I : Local.Model e (traceAt P e) (product P e) := ⟨A, hu, ht, hJ⟩
  refine I.result (N := cubic P) (a := fun x y => metric P e x y) (B := fun x y => rawPair P e x y)
    (Γ := fun x y => ambientConnection P e x y) (R := ambientCurvature P e) (nativeN := nativeCubic)
    hN (fun x y => ?_) ?_ ?_ ?_
  · linarith [AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso.rawTraceForm_eq_three_logMetric
      P e he x y, hb x y]
  all_goals dsimp only [I]; assumption

end
end Glennie.SubmissionR04Intrinsic
