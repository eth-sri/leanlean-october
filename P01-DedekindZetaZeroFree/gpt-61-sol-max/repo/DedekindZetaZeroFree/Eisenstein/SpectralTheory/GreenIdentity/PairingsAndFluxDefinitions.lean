module

public import DedekindZetaZeroFree.Adeles.Characters.CompactAbelianAndAdelicUniqueness
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.IncomingCasimirEigenfunctions
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Topology BigOperators
open MeasureTheory

namespace DedekindZetaZeroFree.KPMsGreenFlux
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev Cover := KPMsFixedHaarDisintegration.Cover F ζ hζ
abbrev X := KPMsFixedHaarDisintegration.X F ζ hζ
abbrev K := NumberField.InfinitePlace F → KPCplxPrincipalSeriesCharts.compactSubgroup

instance : MeasurableSpace (K F) := borel _
instance : BorelSpace (K F) := ⟨rfl⟩

def compactInsertion (k : K F) : Cover F ζ hζ :=
  KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (fun w => (k w).val)

def rightDerivative (w : NumberField.InfinitePlace F) (j : Fin 6)
    (f : Cover F ζ hζ → ℂ) (g : Cover F ζ hζ) : ℂ :=
  deriv (fun t : ℝ => f (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPSmoothActualFlowData.flow F (w,j) t))) 0

def casimir (f : Cover F ζ hζ → ℂ) (g : Cover F ζ hζ) : ℂ :=
  ∑ w : NumberField.InfinitePlace F, -((1 : ℂ) / 4) *
    (rightDerivative F ζ hζ w 0 (rightDerivative F ζ hζ w 0 f) g -
     rightDerivative F ζ hζ w 1 (rightDerivative F ζ hζ w 1 f) g +
     2 * (rightDerivative F ζ hζ w 2 (rightDerivative F ζ hζ w 4 f) g +
          rightDerivative F ζ hζ w 4 (rightDerivative F ζ hζ w 2 f) g -
          rightDerivative F ζ hζ w 3 (rightDerivative F ζ hζ w 5 f) g -
          rightDerivative F ζ hζ w 5 (rightDerivative F ζ hζ w 3 f) g))

def Smooth (f : Cover F ζ hζ → ℂ) : Prop :=
  Continuous f ∧ ∀ g, ContDiff ℝ (⊤ : ℕ∞)
    (fun a : KPSmoothActualFlowData.LieCoordinates F =>
      f (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.exponential F a)))

def KFinite (f : Cover F ζ hζ → ℂ) : Prop :=
  Module.Finite ℂ (Submodule.span ℂ
    (Set.range (fun k : K F => fun g => f (g * compactInsertion F ζ hζ k))))

section Atlas
variable {F ζ hζ} {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

abbrev Cusps := KPMsFixedHaarDisintegration.CuspIndex A

structure AutomorphicAtLevel (f : Cover F ζ hζ → ℂ) : Prop where
  rational_left : ∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ∀ g,
    f (γ.val * g) = f g
  right_level : ∀ u : U.toOpenSubgroup, ∀ g, f (g * u.val.val) = f g
  ordinary_genuine : ∀ ε : rootsOfUnity 3 F, ∀ g,
    f (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g) =
      (KPSmoothLocalQuotientCharts.ordinaryGenuine F ζ hζ ε : ℂ) * f g

def cuspRepresentative (j : Cusps A) : Cover F ζ hζ :=
  KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
    (KPRationalAdelicSplitting.rationalPGLQuotient F
      ((A.cuspAtlas j.1).representative j.2).out)

def constantTerm (dn : Measure (KPCompactFourier.AdditiveQuotient F))
    (j : Cusps A) (f : Cover F ζ hζ → ℂ) (g : Cover F ζ hζ) : ℂ :=
  ∫ q, f (cuspRepresentative A j *
    KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F q) *
    (cuspRepresentative A j)⁻¹ * g) ∂dn

def balancedArch (p : KPCuspCharts.Cross F) (k : K F) (r : ℝ) :
    KPSmoothActualFlowData.GInfinity F := fun w =>
  let i := (Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex})
    ⟨w, KPHilbert.infinite_isComplex F ζ hζ w⟩
  Matrix.ProjGenLinGroup.mk
    (KPCplxCharacterHaar.upperUnipotent (p.1 i) *
      KPCplxCharacterHaar.diagonal (Units.mk0
        (Real.exp (KPMsFixedHaarDisintegration.logHeight (F := F) r + p.2.val i) : ℂ)
        (by exact_mod_cast Real.exp_ne_zero _))) * (k w).val

def cuspLift (j : Cusps A) (p : KPCuspCharts.Cross F) (k : K F) (r : ℝ) :
    Cover F ζ hζ :=
  cuspRepresentative A j *
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (balancedArch (ζ := ζ) (hζ := hζ) p k r) *
    (A.representative j.1).val

def endSet (j : Cusps A) (Y : ℝ) :
    Set (KPMsFixedHaarDisintegration.Spherical F ζ hζ U) :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) ''
    KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).representative j.2)
      (KPMsFixedHaarDisintegration.logHeight (F := F) Y)

def quotientCore (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (T : ℝ) : Set (X F ζ hζ) :=
  {x | ∀ j : Cusps A, P.projection U x ∉ endSet A j T}

end Atlas
end DedekindZetaZeroFree.KPMsGreenFlux

end
