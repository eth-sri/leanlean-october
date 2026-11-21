module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.CubicRootChartGeometry

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

section CompactZeroExtension
variable {X Y G : Type*} [TopologicalSpace X] [CompactSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [T2Space Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [Group G] [Fintype G] [MulAction G X]
variable (Q : X → Y) (hQ : Continuous Q)
  (horbit : ∀ x y, Q x = Q y ↔ ∃ g : G, g • x = y)
  (hact : ∀ g : G, Continuous (fun x : X => g • x))
  (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]









end CompactZeroExtension

section FiniteAverage
variable {X B G : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
  [TopologicalSpace B] [T2Space B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B] [Group G] [Fintype G] [MulAction G X]
variable (Q : X → B) (hQ : Continuous Q) (hsurj : Function.Surjective Q)
  (horbit : ∀ x y, Q x = Q y ↔ ∃ g : G, g • x = y)
  (hact : ∀ g : G, Continuous (fun x : X => g • x))

variable (μ : Measure B) [IsFiniteMeasure μ]

end FiniteAverage

open KPContSectorSmoothFramesSupport KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}


local instance : TopologicalSpace (rootsOfUnity 3 F) := ⊥
local instance : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
local instance : MeasurableSpace (rootsOfUnity 3 F) := ⊤
local instance : BorelSpace (rootsOfUnity 3 F) := ⟨(borel_eq_top_of_discrete).symm⟩

@[instance_reducible]  def rootAction (a : ActualChart (U := U) (H := H))
    (C : Set (M F)) (hI : ∀ g : Gamma a, (isotropyArrow a g).psi '' C = C) :
    MulAction (Gamma a) (rootsOfUnity 3 F × C) where
  smul g p := (p.1 * g.val.2⁻¹, ⟨(isotropyArrow a g).psi p.2.val, by
    have hh := Set.mem_image_of_mem (isotropyArrow a g).psi p.2.property
    exact (congrArg (fun D : Set (M F) => (isotropyArrow a g).psi p.2.val ∈ D) (hI g)).mp hh⟩)
  one_smul p := by
    apply Prod.ext
    · change p.1 * (1 : rootsOfUnity 3 F)⁻¹ = p.1
      simp
    · apply Subtype.ext
      exact (gammaMulAction a).one_smul p.2.val
  mul_smul g h p := by
    apply Prod.ext
    · change p.1 * (g.val.2 * h.val.2)⁻¹ = (p.1*h.val.2⁻¹)*g.val.2⁻¹
      group
    · apply Subtype.ext
      exact (gammaMulAction a).mul_smul g h p.2.val







end DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

end
