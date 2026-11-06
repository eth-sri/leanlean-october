module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevExtensionality
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Countable actual-test Galerkin spaces

This module chooses a countable family of genuine smooth compactly supported
zero-trace tests with dense image in the Hilbert realization of spatial
`H¹₀`.  Its finite initial spans supply the approximation spaces used by the
later finite-dimensional Galerkin ODE; no spectral theorem is assumed.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter Set Module
open scoped ENNReal RealInnerProductSpace Topology

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

/-- The H10 Hilbert carrier inherits a second countable topology from spatial L2. -/
def h10HilbertGraphSecondCountableTopology
    (hΩ : IsOpen Ω) : SecondCountableTopology (H10HilbertGraph hΩ) := by
  letI : MeasureTheory.SFinite (PDE.volumeOn Ω) := inferInstance
  letI : MeasurableSpace.CountablyGenerated (PDE.Vec d) := inferInstance
  letI : MeasureTheory.IsSeparable (PDE.volumeOn Ω) := inferInstance
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  letI : SecondCountableTopology (PDE.ScalarLp Ω (2 )) :=
    MeasureTheory.Lp.SecondCountableTopology
  letI : SecondCountableTopology (PDE.HilbertVectorLp Ω (2 )) :=
    MeasureTheory.Lp.SecondCountableTopology
  letI : SecondCountableTopology (PDE.H1HilbertAmbient Ω) :=
    WithLp.secondCountableTopology 2 _ _
  letI : SecondCountableTopology (PDE.H1HilbertGraph Ω) := inferInstance
  exact inferInstance

/-- The H10 Hilbert carrier is separable. -/
instance instSeparableSpaceH10HilbertGraph
    (hΩ : IsOpen Ω) : TopologicalSpace.SeparableSpace (H10HilbertGraph hΩ) := by
  letI : SecondCountableTopology (H10HilbertGraph hΩ) :=
    h10HilbertGraphSecondCountableTopology hΩ
  exact TopologicalSpace.SecondCountableTopology.to_separableSpace

variable (hΩ : IsOpen Ω)

/-- The actual-test map, codomain-restricted to the H10 closure. -/
def smoothCompactlySupportedH1HilbertGraphToH10LinearMap
     :
    PDE.WeakTestFunction Ω →ₗ[ℝ] H10HilbertGraph hΩ :=
  (smoothCompactlySupportedH1HilbertGraphLinearMap hΩ).codRestrict
    (h10HilbertGraphClosedSubmodule hΩ).toSubmodule
    fun φ => subset_closure
      (LinearMap.mem_range_self (smoothCompactlySupportedH1HilbertGraphLinearMap hΩ) φ)

@[simp] theorem coe_smoothCompactlySupportedH1HilbertGraphToH10LinearMap_apply
     (φ : PDE.WeakTestFunction Ω) :
    ((smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ ) : PDE.H1HilbertGraph Ω) =
      smoothCompactlySupportedH1HilbertGraphLinearMap hΩ φ :=
  rfl

variable (m : ℕ)

/-- Smooth approximations to the selected dense sequence in the H10 Hilbert carrier. -/
def smoothApproximation
      : ℕ → PDE.WeakTestFunction Ω :=
  Classical.choose (exists_tendsto_smooth hΩ (TopologicalSpace.denseSeq (H10HilbertGraph hΩ) m))

private theorem tendsto_smoothApproximation
      :
    Tendsto
      (fun k => smoothCompactlySupportedH1HilbertGraphLinearMap hΩ
        (smoothApproximation hΩ m k))
      atTop (𝓝 ((TopologicalSpace.denseSeq (H10HilbertGraph hΩ) m ) : PDE.H1HilbertGraph Ω)) :=
  Classical.choose_spec
    (exists_tendsto_smooth hΩ (TopologicalSpace.denseSeq (H10HilbertGraph hΩ) m))

/-- A countable sequence of genuine zero-trace smooth tests. -/
def galerkinTestSequence
     : ℕ → PDE.WeakTestFunction Ω :=
  fun n => smoothApproximation hΩ n.unpair.1 n.unpair.2

/-- Its images in the internally constructed H10 Hilbert carrier. -/
def galerkinVector
     : ℕ → H10HilbertGraph hΩ :=
  smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ∘
    galerkinTestSequence hΩ

theorem denseRange_galerkinVector
     : DenseRange (galerkinVector hΩ) := by
  let q : ℕ → H10HilbertGraph hΩ := TopologicalSpace.denseSeq (H10HilbertGraph hΩ)


  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro u

  have hclosure : closure (Set.range q) ⊆ closure (Set.range (galerkinVector hΩ)) := by
    simpa only [closure_closure] using closure_mono (show Set.range q ⊆ closure (Set.range (galerkinVector hΩ)) by
        rintro _ ⟨m, rfl⟩

        apply mem_closure_of_tendsto (show Tendsto (fun k  => galerkinVector hΩ (Nat.pair m k)) atTop (𝓝 (q m)) by
            apply tendsto_subtype_rng.mpr
            simpa only [q, galerkinVector, Function.comp_apply, galerkinTestSequence,
              Nat.unpair_pair,
              coe_smoothCompactlySupportedH1HilbertGraphToH10LinearMap_apply] using
              (tendsto_smoothApproximation hΩ m))
        filter_upwards with k
        exact ⟨Nat.pair m k, rfl⟩)
  exact hclosure (by
      rw [(TopologicalSpace.denseRange_denseSeq (H10HilbertGraph hΩ)).closure_range]
      exact Set.mem_univ u)

/-- The span of the first `N` actual-test images; in particular `E 0 = ⊥`. -/
def galerkinSpace
     (N : ℕ) :
    Submodule ℝ (H10HilbertGraph hΩ) :=
  Submodule.span ℝ (Set.range fun i : Fin N => galerkinVector hΩ i)



theorem galerkinSpace_mono
     {N M : ℕ} (hNM : N ≤ M) :
    galerkinSpace hΩ N ≤ galerkinSpace hΩ M := by
  rw [galerkinSpace, galerkinSpace]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  exact ⟨⟨i, lt_of_lt_of_le i.isLt hNM⟩, rfl⟩

instance galerkinSpace_finiteDimensional
    (hΩ : IsOpen Ω) (N : ℕ) :
    FiniteDimensional ℝ (galerkinSpace hΩ N) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- A coordinate basis for the finite ODE on `E N`; no global basis is chosen. -/
def galerkinSpaceBasis
    (hΩ : IsOpen Ω) (N : ℕ)  :=
  Module.finBasis ℝ (galerkinSpace hΩ N)

end HypoellipticAleksandrov.Parabolic.Dirichlet
