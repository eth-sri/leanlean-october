module

public import DedekindZetaZeroFree.Adeles.Quotients.ProperDoubleQuotientTopology
public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCompactLevels
public import DedekindZetaZeroFree.Adeles.Lattices.RationalMatrices

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ActualQuotient
open Topology
open scoped NumberField Classical

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G]

abbrev DoubleQuotient (Γ K : Subgroup G) := DoubleCoset.Quotient (Γ : Set G) (K : Set G)

instance (Γ K : Subgroup G) : TopologicalSpace (DoubleQuotient Γ K) :=
  inferInstanceAs (TopologicalSpace (_root_.Quotient _))

end Generic

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev actualCover := KPAdelicCoverRestrictedProduct.CubicPGL2Adelic F ζ hζ
abbrev rationalSplit := KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
abbrev rationalSubgroup : Subgroup (actualCover F ζ hζ) := (rationalSplit F ζ hζ).range

def finiteTuples : Subgroup (KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) where
  carrier := {g | ∀ w : NumberField.InfinitePlace F, g (Sum.inl w) = 1}
  one_mem' := by simp
  mul_mem' := by simp_all
  inv_mem' := by simp

def finiteSubgroup : Subgroup (actualCover F ζ hζ) :=
  (finiteTuples F ζ hζ).map
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))

theorem actual_cover_lc_t2_group :
    T2Space (actualCover F ζ hζ) ∧ LocallyCompactSpace (actualCover F ζ hζ) ∧
      IsTopologicalGroup (actualCover F ζ hζ) := 
  ⟨(KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1,
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.1,
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1⟩

theorem actual_cover_secondCountable : SecondCountableTopology (actualCover F ζ hζ) := 
  ActualQuotientTopology.Cover.rawCover_secondCountable F ζ hζ

abbrev ArchGroup := NumberField.InfinitePlace F → Matrix.ProjGenLinGroup (Fin 2) ℂ

def glArchProjection : KPAdelicCoverRestrictedProduct.AdelicGL2 F →* ArchGroup F where
  toFun g w := Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map
      ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
        (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w))) g)
  map_one' := by ext w; simp
  map_mul' := by intro g h; ext w; simp

 theorem scalars_le_arch_kernel : KPAdelicCoverRestrictedProduct.scalarSubgroup F ≤
    (glArchProjection F ζ hζ).ker := by
  rintro g ⟨u, rfl⟩
  ext w
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
    (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) = 1
  rw [Matrix.GeneralLinearGroup.map_scalar, Matrix.ProjGenLinGroup.mk_scalar]

def archProjection : actualCover F ζ hζ →* ArchGroup F :=
  (QuotientGroup.lift (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
    (glArchProjection F ζ hζ) (scalars_le_arch_kernel F ζ hζ)).comp
      (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ)

end DedekindZetaZeroFree.ActualQuotient

end

section

noncomputable section
namespace DedekindZetaZeroFree.ActualQuotient
open Topology
open scoped NumberField Classical

section Generic
variable {G : Type*} [Group G] [TopologicalSpace G]

abbrev doubleQuotientMap (Γ K : Subgroup G) : G → DoubleQuotient Γ K :=
  DoubleCoset.mk Γ K

def actionCorrespondence (Γ K : Subgroup G) : (Γ × K) × G → G × G :=
  fun p => ((p.1.1 : G) * p.2 * (p.1.2 : G)⁻¹, p.2)

theorem proper_actionCorrespondence [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (Γ K : Subgroup G)
    (hΓ : IsClosed (Γ : Set G)) (dΓ : IsDiscrete (Γ : Set G))
    (hK : IsCompact (K : Set G)) : IsProperMap (actionCorrespondence Γ K) := 
  ActualQuotientTopology.Generic.proper_rawActionCorrespondence Γ K hΓ dΓ hK

theorem lcsc_polish (Y : Type*) [TopologicalSpace Y] [T2Space Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] : PolishSpace Y := 
  ActualQuotientTopology.Generic.locallyCompact_secondCountable_polish Y

structure TopologyCertificate (Γ K : Subgroup G) : Prop where
  proper : IsProperMap (actionCorrespondence Γ K)
  locallyCompact : LocallyCompactSpace (DoubleQuotient Γ K)
  hausdorff : T2Space (DoubleQuotient Γ K)
  secondCountable : SecondCountableTopology (DoubleQuotient Γ K)
  polish : PolishSpace (DoubleQuotient Γ K)
  continuous : Continuous (doubleQuotientMap Γ K)
  openMap : IsOpenMap (doubleQuotientMap Γ K)
  quotientMap : IsQuotientMap (doubleQuotientMap Γ K)

theorem proper_doubleQuotient_certificate [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (Γ K : Subgroup G)
    (hp : IsProperMap (actionCorrespondence Γ K)) : TopologyCertificate Γ K := by
  obtain ⟨hlc, ht2, hsc, hc, ho, hq⟩ :=
    ActualQuotientTopology.Generic.proper_rawDoubleQuotient_topology Γ K hp
  letI : LocallyCompactSpace (DoubleQuotient Γ K) := hlc
  letI : T2Space (DoubleQuotient Γ K) := ht2
  letI : SecondCountableTopology (DoubleQuotient Γ K) := hsc
  exact ⟨hp, hlc, ht2, hsc, lcsc_polish (DoubleQuotient Γ K), hc, ho, hq⟩
end Generic

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem actual_rational_closed_discrete :
    IsClosed (rationalSubgroup F ζ hζ : Set (actualCover F ζ hζ)) ∧
      IsDiscrete (rationalSubgroup F ζ hζ : Set (actualCover F ζ hζ)) := by
  have h := ActualQuotientTopology.Arithmetic.rawRational_arithmetic_certificate F ζ hζ
  exact ⟨h.1, h.2.1⟩

theorem actual_rational_arch_injective :
    Function.Injective ((archProjection F ζ hζ).comp (rationalSubgroup F ζ hζ).subtype) := 
  (ActualQuotientTopology.Arithmetic.rawRational_arithmetic_certificate F ζ hζ).2.2
