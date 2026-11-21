module

public import DedekindZetaZeroFree.Adeles.Quotients.FiniteCuspAtlas
public import DedekindZetaZeroFree.Analysis.QuadraticForms.TestDifferentialFriedrichsLaplacian

@[expose] public section

set_option maxHeartbeats 400000
noncomputable section
open scoped Classical NumberField
open MeasureTheory Filter
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
  (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

abbrev Fiber := KPCuspGenuineMonodromy.scalarFiber F ζ hζ U
abbrev Coordinates := HyperbolicChart.Space (KPCuspLogShape.dimension F)
abbrev Arch := KPFiniteCuspAtlas.SymmetricSpace F

def toArch (p : Coordinates F) : Arch F :=
  fun i => (⟨p (i,0), p (i,1)⟩, p (i,2))

def fromArch (x : Arch F) : Coordinates F :=
  WithLp.toLp 2 (fun ik => ![(x ik.1).1.re, (x ik.1).1.im, (x ik.1).2] ik.2)

abbrev Cotangent := PiLp 2 (fun _ : Fin (KPCuspLogShape.dimension F) × Fin 3 =>
  Fiber F ζ hζ U)

variable (a : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

def basePoint (i : Fin a.componentCount) (x : Arch F) : KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i)
    (KPCuspSiegel.projection F _ x)

def highEnds (T : ℝ) : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  ⋃ i : Fin a.componentCount, ⋃ c : Fin (a.cuspAtlas i).cuspCount,
    KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i) ''
      KPFiniteCuspAtlas.endSet F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative i))
        ((a.cuspAtlas i).representative c) T

def closedHighEnds (T : ℝ) : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  ⋃ i : Fin a.componentCount, ⋃ c : Fin (a.cuspAtlas i).cuspCount,
    KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i) ''
      (KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative i)) ''
        (KPCuspSiegel.action F ((a.cuspAtlas i).representative c) ''
          {x | T ≤ KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) x}))

def core : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  Set.univ \ highEnds F ζ hζ hF U a a.threshold

def scalarLift (r : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ) (i : Fin a.componentCount) :
    Coordinates F → ℂ :=
  fun p => (r (basePoint F ζ hζ hF U a i (toArch F p)) : ℂ)

def scalarGradientNorm (r : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (i : Fin a.componentCount) (x : Arch F) : ℝ :=
  Real.sqrt (∑ j : Fin (KPCuspLogShape.dimension F), ∑ k : Fin 3,
    ‖HyperbolicChart.differential (KPCuspLogShape.dimension F)
      (scalarLift F ζ hζ hF U a r i) (fromArch F x) j k‖ ^ 2)

def scalarLaplacian (r : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (i : Fin a.componentCount) (x : Arch F) : ℂ :=
  HyperbolicChart.laplacian (KPCuspLogShape.dimension F)
    (scalarLift F ζ hζ hF U a r i) (fromArch F x)

end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

end
