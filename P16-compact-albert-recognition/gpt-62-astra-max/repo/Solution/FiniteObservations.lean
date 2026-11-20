/- Unified independent native and admitted orbit-quotient statement surface. -/
module
public import Glennie.ObservationData
public import Glennie.Compact.LocalOrbitQuotientR01

public import Glennie.Compact.LocalReconstruction

public import Solution.Defect

public import Glennie.Compact.InputDisplacementR01

public import Glennie.NativeOrderedFrameGenerationR01

public import Glennie.Compact.NativeQ20AdapterR01
public import Glennie.Compact.ReadoutRobustnessR01
public import Glennie.NativeGenerationStabilizersR01

public import Glennie.Compact.GeneratedRecognitionR01

public import Mathlib.Analysis.Quaternion

public import Mathlib.Topology.Homeomorph.Lemmas

public import Mathlib.Topology.Maps.Basic

public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public import Mathlib.Data.Fin.VecNotation

public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace Glennie.SubmissionR03
noncomputable section
open Glennie
open Glennie.Compact.Affine20

open Glennie.Compact

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
    q26 T = q26 S ↔ fullLedger T = fullLedger S := NativeQFamilyLedger.q26_eq_iff_ledger54_eq T S hT hS

/-- On actual ordered frames, Q20 still determines the complete 54-trace ledger. -/
theorem q20_eq_iff_fullLedger_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q20 T = q20 S ↔ fullLedger T = fullLedger S := NativeQ20AdapterR01.q20_eq_iff_ledger54_eq T S hT hS

theorem division_free (x y z : Albert) :
    4 * delta x y z (halfAmplitude x) y - delta x y z x y -
      delta x y z 1 y = 2 * phi x y z := by
  exact OperationalPhi.phi_division_free ..

theorem score_eq_two_phi (T : Triple) : score T = 2 * phiOf T := by
  exact LocalContrast.score_eq_two_phi T

theorem atoms_generate_of_score
    (T : Triple) (hT : ∀ a, Frame (T a)) (hs : score T ≠ 0)
    (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (hAtoms : ∀ a i, T a i ∈ K) : K = ⊤ := by
  exact NativeOrderedFrameGenerationR01.ordered_frame_atoms_generate_of_score T hT hs K hJ hAtoms

theorem nearby_sign_rigidity :
    ∃ V : Set Ledger54, IsOpen V ∧ fullLedger flatBase ∈ V ∧
      ∀ T S : Triple, (∀ a : Fin 3, Frame (T a)) →
        (∀ a : Fin 3, Frame (S a)) → fullLedger T ∈ V →
        fullLedger T = fullLedger S →
        ((phiOf T < 0 ∧ phiOf S < 0) ∨ (0 < phiOf T ∧ 0 < phiOf S)) →
        ∃ k : CompactAutomorphism, mapAtoms k S = T := by
  exact ⟨Set.univ,isOpen_univ,Set.mem_univ _,fun _ _ ht hs _ => PairNormNearby.rigid ht hs⟩

/-- A specific native near-flat full-fiber margin in a supplied open ledger neighborhood. -/
theorem near_flat_scalar_margin :
    ∃ V : Set Ledger54, IsOpen V ∧ fullLedger flatBase ∈ V ∧
      ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) → fullLedger T ∈ V →
        1 / 27 < |phiOf T| := by
  let d := LocalOrbitQuotientR01.localData
  exact ⟨encode20 ⁻¹' d.V,d.openV.preimage Affine20.continuous_encode20,d.base,
    fun T hf hb => d.margin _ hb ⟨hf, NearbyOrbits.ledger54_eq_decode20 hf rfl⟩⟩

/-- Every admitted nearby full fiber is exactly two disjoint simultaneous
    automorphism orbits, with continuous signed sections and exact chart fibers. -/
private theorem coordContinuous : Continuous (fun T : Triple => fun a i => Albert.coordinateEquiv (T a i)) :=
  continuous_pi fun a => continuous_pi fun i =>
    Albert.coordinateLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp ((continuous_apply i).comp (continuous_apply a))

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
  let d := LocalOrbitQuotientR01.localData
  exact ⟨d.V,d.openV,d.base,d.pos,d.neg, coordContinuous.comp_continuousOn d.contPos,
    coordContinuous.comp_continuousOn d.contNeg, d.framePos,d.frameNeg,d.chartPos,d.chartNeg,
    d.posL,d.negL,d.phiPos,d.phiNeg,d.cover,d.disjoint,fun b _ => NearbyOrbits.fibre_eq b⟩

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
  let d := LocalOrbitQuotientR01.localData
  exact ⟨d.V,d.openV,d.base,LocalReconstruction.complete d⟩

/-- Every compact region of the established admitted chart has a positive
uniform Phi margin for its entire actual ordered-frame fiber. -/
theorem compact_local_phi_margin :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∀ K : Set V, IsCompact K →
        ∃ m > 0, ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) →
          ∀ hb : encode20 (fullLedger T) ∈ V,
            (⟨encode20 (fullLedger T), hb⟩ : V) ∈ K →
              m ≤ |phiOf T| := by
  let d := LocalOrbitQuotientR01.localData
  refine ⟨d.V,d.openV,d.base,?_⟩
  exact fun _ _ => ⟨1/27,by norm_num,fun T hf hb _ =>
    (d.margin _ hb ⟨hf,NearbyOrbits.ledger54_eq_decode20 hf rfl⟩).le⟩

/-- Six absolute-error bounds and a strict observed margin certify the
    native scalar sign; no probability or measurement semantics is assumed. -/
theorem signed_readout_margin (T : Triple) (noisy : Readouts) (ε : ℝ)
    (hε : 0 ≤ ε) (h : ErrorsAtMost noisy (exactReadouts T) ε)
    (hm : 12 * ε < |weightedScore noisy|) :
    (weightedScore noisy < 0 ∧ phiOf T < 0) ∨
    (0 < weightedScore noisy ∧ 0 < phiOf T) := ReadoutRobustnessR01.sign_certificate T noisy ε hε h hm



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
  let d := LocalOrbitQuotientR01.localData
  refine ⟨d.V, d.openV, d.base, d.pos, d.neg, coordContinuous.comp_continuousOn d.contPos,
    coordContinuous.comp_continuousOn d.contNeg, d.framePos, d.frameNeg, d.chartPos, d.chartNeg, d.phiPos, d.phiNeg, ?_⟩
  intro K hK ζ hζ
  obtain ⟨η,hη,h⟩ := NativeQ20AdapterR01.compact_feasible_recovery d K hK ζ hζ
  refine ⟨η,hη,?_⟩; intro T hf hb hk b hbK hd
  obtain ⟨g,hg⟩ := h ⟨T,hf,hb⟩ hk b hbK hd
  refine ⟨g,fun a i => ?_⟩
  have bound (Z : Triple) : ‖Z a i‖ ≤ ‖Z‖ := (norm_le_pi_norm (Z a) i).trans (norm_le_pi_norm Z a)
  have h := (bound _).trans_lt hg
  by_cases hp : 0 < Sections.phiOf T <;> simpa [NativeQ20AdapterR01.branchSection, LocalOrbitQuotientR01.select, LocalOrbitQuotientR01.sheet, nA_eq, Affine20.mapAtoms, hp] using h

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
  simp only [nA_eq] at *
  have e : |noisyPhi noisy - phi (encoder (T f0)) (encoder (T f1)) (encoder (T f2))| ≤ ξ :=
    (ReadoutRobustnessR01.phi_error T noisy ε hreadout).trans hallowance
  have d := NativeNormKernel.phi_displacement_18 _ _ _ _ _ _ R δ hR hx hy hz hx' hy' hz' hdx hdy hdz
  obtain ⟨hg,ha,_⟩ := phi_nonzero_generation_stabilizer x' y' z' (by grind)
  exact ⟨by grind,hg,ha⟩

end
end Glennie.SubmissionR03
