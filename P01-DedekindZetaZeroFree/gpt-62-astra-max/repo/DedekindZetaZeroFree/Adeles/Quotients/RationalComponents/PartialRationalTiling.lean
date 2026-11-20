module
public import DedekindZetaZeroFree.Adeles.Quotients.SphericalProjection

public import DedekindZetaZeroFree.Adeles.Quotients.RationalComponents.Defs

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Pointwise
open MeasureTheory Function

namespace DedekindZetaZeroFree.KPActualComponentHaarSources

open KPMsFixedHaar

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private alias actual_archProjection_compare := DedekindZetaZeroFree.KPMsFixedHaar.archProjection_compare

private theorem actual_finiteSubgroup_eq :
    PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ =
      KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
  obtain ⟨e, he, hi, hs, hker, hrest⟩ :=
    PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  rw [← hker]
  ext g
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hg
    funext w
    let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)
    have hw := congrFun hg w
    rw [actual_archProjection_compare] at hw
    have hw' := congrArg (Matrix.ProjGenLinGroup.map e.symm.toRingHom) hw
    simp only [← MonoidHom.comp_apply, ← Matrix.ProjGenLinGroup.map_comp] at hw'
    simpa [e] using hw'
  · intro hg
    funext w
    rw [actual_archProjection_compare, hg]
    exact map_one _

alias PartialRationalTiling.actual_finiteSubgroup_eq := actual_finiteSubgroup_eq

 theorem actual_product_splitting :
    ∃ e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ*
      KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ,
      ∀ a c, e (a, c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by
  obtain ⟨e, he, hrest⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  rw [← (actual_finiteSubgroup_eq F ζ hζ)]
  exact ⟨e, he⟩

open KPAdelicCoverRestrictedProduct

private alias finiteProjection_local_infinite := DedekindZetaZeroFree.KPMsFixedHaar.SphericalProjection.finiteProjection_local_infinite

private alias finiteProjection_archimedeanInsertion := DedekindZetaZeroFree.KPMsFixedHaar.SphericalProjection.finiteProjection_archimedeanInsertion

 def tilingLift : KPCuspArithmetic.PGL2 F →* Cover F ζ hζ :=
  (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ).comp (rationalEquiv F).toMonoidHom

 def tilingArch : KPCuspArithmetic.PGL2 F →* KPSmoothActualFlowData.GInfinity F :=
  (KPSmoothLocalQuotientCharts.archProjection F ζ hζ).comp (tilingLift F ζ hζ)

 theorem tilingLift_finite (γ : KPCuspArithmetic.PGL2 F) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ (tilingLift F ζ hζ γ) =
      KPFiniteComponents.diagonal F γ := by apply @DedekindZetaZeroFree.KPMsFixedHaar.rationalLift_finite <;> assumption

 theorem tilingArch_injective : Function.Injective (tilingArch F ζ hζ) := by
  intro x y hxy
  apply (KPRationalAdelicSplitting.rationalPGL_splitting F ζ hζ).1.comp (rationalEquiv F).injective
  exact congrArg Subtype.val (ActualQuotient.actual_rational_arch_injective F ζ hζ
    (a₁ := ⟨tilingLift F ζ hζ x, (⟨rationalEquiv F x, rfl⟩)⟩) (a₂ := ⟨tilingLift F ζ hζ y, (⟨rationalEquiv F y, rfl⟩)⟩) hxy)

 theorem tiling_arch_m (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    KPSmoothLocalQuotientCharts.archProjection F ζ hζ (m F ζ hζ (a,c)) = a := by
  have hc : KPSmoothLocalQuotientCharts.archProjection F ζ hζ c.val = 1 := by
    change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ c.val = 1
    funext w
    rw [actual_archProjection_compare]
    have hh := c.property
    change KPCuspGenuineMonodromy.archProjection F ζ hζ c.val = 1 at hh
    rw [hh]
    exact map_one _
  change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
    (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a * c.val) = a
  change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ c.val = 1 at hc
  rw [map_mul, PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion, hc, mul_one]

 theorem tiling_finite_m (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ (m F ζ hζ (a,c)) =
      KPCuspGenuineMonodromy.finiteBase F ζ hζ c := by
  simp only [m, map_mul, finiteProjection_archimedeanInsertion, one_mul]
  rfl

 theorem tiling_central_base (ε : rootsOfUnity 3 F) :
    KPCuspGenuineMonodromy.finiteBase F ζ hζ (KPCuspGenuineMonodromy.central F ζ hζ ε) = 1 := by
  have hm : KPCuspGenuineMonodromy.central F ζ hζ ε ∈
      (KPCuspGenuineMonodromy.finiteBase F ζ hζ).ker := by
    rw [← (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).1]
    exact ⟨ε, rfl⟩
  exact hm

 theorem tiling_orbit_base (U : Level F ζ hζ)
    (g c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    c ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g ↔
      ∃ u : U.toOpenSubgroup,
        KPCuspGenuineMonodromy.finiteBase F ζ hζ c =
          KPCuspGenuineMonodromy.finiteBase F ζ hζ g *
            KPCuspGenuineMonodromy.finiteBase F ζ hζ u := by
  constructor
  · rintro ⟨ε,u,rfl⟩
    exact ⟨u, by simp only [map_mul, tiling_central_base, one_mul]⟩
  · rintro ⟨u, hu⟩
    have hk : c * (g * u)⁻¹ ∈ (KPCuspGenuineMonodromy.central F ζ hζ).range := by
      rw [(KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).1,
        MonoidHom.mem_ker, map_mul, map_inv, map_mul, hu, mul_inv_cancel]
    obtain ⟨ε, hε⟩ := hk
    refine ⟨ε, u, ?_⟩
    rw [hε]
    group

 theorem tiling_overlap_primitive (U : Level F ζ hζ)
    (g b c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (δ : KPCuspArithmetic.PGL2 F)
    (hb : b ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g)
    (hc : c ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g)
    (he : KPFiniteComponents.diagonal F δ * KPCuspGenuineMonodromy.finiteBase F ζ hζ b =
      KPCuspGenuineMonodromy.finiteBase F ζ hζ c) :
    δ ∈ KPCuspGenuineMonodromy.Component F ζ hζ U g := by
  obtain ⟨u,hu⟩ := (tiling_orbit_base F ζ hζ U g b).mp hb
  obtain ⟨v,hv⟩ := (tiling_orbit_base F ζ hζ U g c).mp hc
  refine ⟨KPCuspGenuineMonodromy.finiteBase F ζ hζ (v * u⁻¹),
    ⟨v * u⁻¹, (v * u⁻¹).property, rfl⟩, ?_⟩
  rw [hu,hv] at he
  simp only [MulAut.conj_apply, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  simpa [mul_assoc] using (congrArg (fun x => x * (KPCuspGenuineMonodromy.finiteBase F ζ hζ u)⁻¹ *
    (KPCuspGenuineMonodromy.finiteBase F ζ hζ g)⁻¹) he).symm

 theorem tiling_preserve_base (U : Level F ζ hζ)
    (g b c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (δ : KPCuspGenuineMonodromy.Component F ζ hζ U g)
    (hb : b ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g)
    (he : KPCuspGenuineMonodromy.finiteBase F ζ hζ c =
      KPFiniteComponents.diagonal F δ * KPCuspGenuineMonodromy.finiteBase F ζ hζ b) :
    c ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g := by
  obtain ⟨u,hu⟩ := (tiling_orbit_base F ζ hζ U g b).mp hb
  obtain ⟨ε,v,hv⟩ := KPCuspGenuineMonodromy.finiteComparison_exists F ζ hζ U g δ
  have hh := congrArg (KPCuspGenuineMonodromy.finiteBase F ζ hζ) hv
  simp only [map_mul, tiling_central_base, one_mul] at hh
  rw [← MonoidHom.comp_apply,
    (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.2] at hh
  apply (tiling_orbit_base F ζ hζ U g c).mpr
  refine ⟨v*u, ?_⟩
  rw [he,hu,← mul_assoc,hh]
  change _ = KPCuspGenuineMonodromy.finiteBase F ζ hζ g *
    KPCuspGenuineMonodromy.finiteBase F ζ hζ (v.val*u.val)
  simp only [map_mul,mul_assoc]

 def tilingRational (δ : KPCuspArithmetic.PGL2 F) :
    KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ :=
  ⟨tilingLift F ζ hζ δ, ⟨rationalEquiv F δ, rfl⟩⟩

 theorem tilingRational_surjective : Function.Surjective (tilingRational F ζ hζ) := by
  rintro ⟨x,δ,hδ⟩
  exact ⟨(rationalEquiv F).symm δ, Subtype.ext (by simpa [tilingRational,tilingLift] using hδ)⟩

 theorem tiling_quotient_invariant
    (δ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) (x : Cover F ζ hζ) :
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (δ.val*x) =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ x := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simpa [mul_inv_rev, mul_assoc] using
    (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ).inv_mem δ.property

 theorem tiling_projection_mem (U : Level F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (g b : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (a : KPSmoothActualFlowData.GInfinity F)
    (hb : b ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g) :
    P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (m F ζ hζ (a,b))) ∈
      Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U g) := by
  obtain ⟨ε,u,rfl⟩ := hb
  refine ⟨Quotient.mk _ (archBasepoint F a), ?_⟩
  simp only [m, P.formula]
  apply Quotient.sound
  exact ⟨1,ε,u,by simp,by simp⟩

 theorem tiling_projection_cover (U : Level F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (g c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (a : KPSmoothActualFlowData.GInfinity F)
    (hc : P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (m F ζ hζ (a,c))) ∈
      Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U g)) :
    ∃ δ : KPCuspArithmetic.PGL2 F, ∃ u : U.toOpenSubgroup,
      KPFiniteComponents.diagonal F δ * KPCuspGenuineMonodromy.finiteBase F ζ hζ c =
        KPCuspGenuineMonodromy.finiteBase F ζ hζ g *
          KPCuspGenuineMonodromy.finiteBase F ζ hζ u := by
  obtain ⟨y,hy⟩ := hc
  obtain ⟨y,rfl⟩ := Quotient.mk_surjective y
  simp only [m, P.formula] at hy
  change Quotient.mk _ (y,g) = Quotient.mk _ (archBasepoint F a,c) at hy
  obtain ⟨δ,ε,u,hx,he⟩ := Quotient.exact hy.symm
  refine ⟨δ,u⁻¹,?_⟩
  have hh := congrArg (KPCuspGenuineMonodromy.finiteBase F ζ hζ) he
  simp only [map_mul,tiling_central_base, mul_one] at hh
  rw [← MonoidHom.comp_apply,
    (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.2] at hh
  have hh' := congrArg (fun x => x * (KPCuspGenuineMonodromy.finiteBase F ζ hζ u.val)⁻¹) hh
  simpa [mul_assoc] using hh'.symm

end DedekindZetaZeroFree.KPActualComponentHaarSources

end
