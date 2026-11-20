module

public import DedekindZetaZeroFree.Metaplectic.Kubota.PGL.LocalCover
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RankOne.NormalizedInduction
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalCompactHolomorphicModel
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.CompactRootCharacterAverages

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPLocalSmoothRepresentation

open scoped NumberField NNReal
open NumberField IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)

abbrev FiniteCover := KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr w)

@[instance_reducible] def finiteCoverTopology : TopologicalSpace (FiniteCover F ζ hζ w) :=
  KPPGLLocalCover.finiteTopology F ζ hζ w m

local instance : (KPPGLLocalCover.scalarSubgroup F (Sum.inr w)).Normal :=
  KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)

def ordinaryPGLMap : KPPGLLocalCover.LocalPGL2 F (Sum.inr w) →*
    KPRankOneInduction.PGL2 F w :=
  QuotientGroup.lift (KPPGLLocalCover.scalarSubgroup F (Sum.inr w))
    Matrix.ProjGenLinGroup.mk (by
      intro g hg
      rw [Matrix.ProjGenLinGroup.ker_mk]
      exact KPPGLLocalCover.scalarSubgroup_le_center F (Sum.inr w) hg)

def projection : FiniteCover F ζ hζ w →* KPRankOneInduction.PGL2 F w :=
  (ordinaryPGLMap F w).comp (KPPGLLocalCover.projection F ζ hζ (Sum.inr w))

abbrev Borel := KPRankOneInduction.coveredBorel F w (projection F ζ hζ w)
abbrev Torus := KPRankOneInduction.coveredTorus F w (projection F ζ hζ w)
abbrev deltaB := KPRankOneInduction.deltaB F w (projection F ζ hζ w)
abbrev dB := KPRankOneInduction.dB F w (projection F ζ hζ w)

abbrev compactOpenLevel :=
  letI := finiteCoverTopology F ζ hζ w m
  CompactOpenLevel (FiniteCover F ζ hζ w)

abbrev Induced {E : Type*} [AddCommGroup E] [Module ℂ E]
    (τ : Representation ℂ (Borel F ζ hζ w) E) :=
  letI := finiteCoverTopology F ζ hζ w m
  SmoothInd (Borel F ζ hζ w) τ (dB F ζ hζ w)

abbrev inflatedRepresentation {E : Type*} [AddCommGroup E] [Module ℂ E]
    (q : Borel F ζ hζ w →* Torus F ζ hζ w)
    (τ : Representation ℂ (Torus F ζ hζ w) E) :=
  KPRankOneInduction.inflatedTorusRepresentation F w (projection F ζ hζ w) q τ

abbrev PrincipalSeries {E : Type*} [AddCommGroup E] [Module ℂ E]
    (q : Borel F ζ hζ w →* Torus F ζ hζ w)
    (τ : Representation ℂ (Torus F ζ hζ w) E) :=
  Induced F ζ hζ w m (inflatedRepresentation F ζ hζ w q τ)

def upperRoot : Multiplicative (KPRankOneInduction.LocalField F w) →*
    FiniteCover F ζ hζ w where
  toFun t := KPPGLLocalCover.N F ζ hζ (Sum.inr w) (Multiplicative.toAdd t)
  map_one' := by
    change KPPGLLocalCover.N F ζ hζ (Sum.inr w)
      (0 : KPHilbert.Completion F (Sum.inr w)) = 1
    have h := KPPGLLocalCover.N_add F ζ hζ (Sum.inr w) 0 0
    simpa only [add_zero, mul_eq_left] using h.symm
  map_mul' t u := KPPGLLocalCover.N_add F ζ hζ (Sum.inr w) _ _

def lowerRoot : Multiplicative (KPRankOneInduction.LocalField F w) →*
    FiniteCover F ζ hζ w where
  toFun t := KPPGLLocalCover.LowerN F ζ hζ (Sum.inr w) (Multiplicative.toAdd t)
  map_one' := by
    change KPPGLLocalCover.LowerN F ζ hζ (Sum.inr w)
      (0 : KPHilbert.Completion F (Sum.inr w)) = 1
    have h := KPPGLLocalCover.LowerN_add F ζ hζ (Sum.inr w) 0 0
    simpa only [add_zero, mul_eq_left] using h.symm
  map_mul' t u := KPPGLLocalCover.LowerN_add F ζ hζ (Sum.inr w) _ _

abbrev OrdinaryCoinvariants {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (FiniteCover F ζ hζ w) V) :=
  RootCoinvariants ρ (upperRoot F ζ hζ w) 1

abbrev TwistedCoinvariants {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (FiniteCover F ζ hζ w) V)
    (ψ : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ) :=
  RootCoinvariants ρ (upperRoot F ζ hζ w) ψ

def continuousUpperRoot (hm : KPLocalChartTopology.MatrixChartDepth F w m) :
    letI := finiteCoverTopology F ζ hζ w m
    ContinuousMonoidHom (Multiplicative (KPRankOneInduction.LocalField F w))
      (FiniteCover F ζ hζ w) := by
  letI := finiteCoverTopology F ζ hζ w m
  exact ⟨upperRoot F ζ hζ w,
    (KPPGLLocalCover.finite_lifts_continuous F ζ hζ w m hm).1⟩

end DedekindZetaZeroFree.KPLocalSmoothRepresentation

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPLocalSmoothRepresentation

open scoped NumberField NNReal
open NumberField IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)

local instance : (KPPGLLocalCover.scalarSubgroup F (Sum.inr w)).Normal :=
  KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)

def genericGenuine {V : Type*} [AddCommGroup V] [Module ℂ V]
    (χ : rootsOfUnity 3 F →* ℂˣ)
    (ρ : Representation ℂ (FiniteCover F ζ hζ w) V) : Prop :=
  ∀ z v, ρ (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) z) v =
    (χ z : ℂ) • v

def genuine {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (FiniteCover F ζ hζ w) V) : Prop :=
  genericGenuine F ζ hζ w
    ((KPLocalCover.coefficientEmbedding F ζ hζ).comp (KPLocalCover.threeToSix F)) ρ

def smoothGenuine {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (FiniteCover F ζ hζ w) V) : Prop :=
  letI := finiteCoverTopology F ζ hζ w m
  SmoothRepresentation ρ ∧ genuine F ζ hζ w ρ

def scalarRepresentation {H : Type*} [Group H] (χ : H →* ℂˣ) :
    Representation ℂ H ℂ where
  toFun h := (χ h : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' h k := by ext; simp [mul_smul, mul_comm]

abbrev ScalarInduced (χ : Borel F ζ hζ w →* ℂˣ) :=
  Induced F ζ hζ w m (scalarRepresentation χ)

def scalarInducedRepresentation
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (χ : Borel F ζ hζ w →* ℂˣ) :
    Representation ℂ (FiniteCover F ζ hζ w) (ScalarInduced F ζ hζ w m χ) := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  exact smoothIndRepresentation (Borel F ζ hζ w) (scalarRepresentation χ) (dB F ζ hζ w)

def scalarValue (χ : Borel F ζ hζ w →* ℂˣ)
    (f : ScalarInduced F ζ hζ w m χ) (g : FiniteCover F ζ hζ w) : ℂ :=
  f.val.val g

@[simp] theorem scalarInducedRepresentation_apply
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (χ : Borel F ζ hζ w →* ℂˣ) (a g : FiniteCover F ζ hζ w)
    (f : ScalarInduced F ζ hζ w m χ) :
    scalarValue F ζ hζ w m χ
      (scalarInducedRepresentation F ζ hζ w m hm χ a f) g =
      scalarValue F ζ hζ w m χ f (g * a) := rfl

end DedekindZetaZeroFree.KPLocalSmoothRepresentation

end
end
