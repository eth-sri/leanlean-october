module
public import Solution.FiniteObservations

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

open Compact.LocalOrbitQuotientR01

/-- The actual automorphism quotient of all admitted ordered frames is
homeomorphic to the centered feasible chart and its two algebraic sign sheets. -/
theorem admitted_orbit_quotient_homeomorph :
    ∃ V : Set ChartPoint, IsOpen V ∧
      Glennie.SubmissionR03.encode20 (fullLedger flatBase) ∈ V ∧
      ∃ H : OrbitQuotient V ≃ₜ V × Bool,
        (∀ T : Admitted V, H (Quotient.mk' T) = invariant V T) ∧
        (∀ T S : Admitted V,
          (orbitSetoid V).r T S ↔ invariant V T = invariant V S) := by
  let d := Compact.LocalOrbitQuotientR01.localData
  let H : OrbitQuotient d.V ≃ₜ d.V × Bool := {
    toFun := forward d
    invFun := inverse d
    left_inv := inverse_forward d
    right_inv := forward_inverse d
    continuous_toFun := by with_unfolding_all change @Continuous _ _ (quotientCoordinateTopology d) _ _
                           rw [quotientTopology_eq_source]; with_unfolding_all exact continuous_forward d
    continuous_invFun := by with_unfolding_all change @Continuous _ _ _ (quotientCoordinateTopology d) _
                            rw [quotientTopology_eq_source]; with_unfolding_all exact continuous_inverse d }
  exact ⟨d.V,d.openV,d.base,H,fun _ => rfl,fun T S => (rel_iff_chart_sheet_eq d T S).trans ⟨fun h => Prod.ext h.1 h.2,fun h => ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩⟩⟩

end
end Glennie.SubmissionR04Quotient

