module

public import DedekindZetaZeroFree.Adeles.Quotients.FiniteCuspAtlas

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff
open Topology

namespace DedekindZetaZeroFree.KPActualCollarBuffer

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
  {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
  {U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ)}
  (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

abbrev CuspIndex := Σ i : Fin A.componentCount, Fin (A.cuspAtlas i).cuspCount

abbrev Stabilizer (a : CuspIndex A) := KPCuspArithmetic.conjugatedStabilizer F
  (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
  ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2)

def chartLift (a : CuspIndex A) (z : KPCuspCharts.Coordinates F) :
    KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
    (((A.cuspAtlas a.1).representative a.2 • KPCuspCharts.toArch F z), A.representative a.1)

def endSet (τ : ℝ) (a : CuspIndex A) : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1) ''
    KPFiniteCuspAtlas.endSet F (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
      ((A.cuspAtlas a.1).representative a.2) τ

def endChart (τ : ℝ) (a : CuspIndex A) :
    KPCuspCharts.HighQuotient F (Stabilizer A a) τ → KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1) ∘ KPFiniteCuspAtlas.endMap F
    (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
    ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2) τ

def height (τ : ℝ) (a : CuspIndex A) (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) : ℝ :=
  if h : ∃ z, τ < z.2 ∧ chartLift A a z = x then (Classical.choose h).2 else 0

abbrev RadialDomain (τ : ℝ) (a : CuspIndex A) :=
  KPCuspCharts.CrossQuotient F (Stabilizer A a) × Set.Ioi τ

def radialChart (τ : ℝ) (a : CuspIndex A) : RadialDomain A τ a → KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  endChart A τ a ∘ ((A.cuspAtlas a.1).geometry a.2).highPresentation τ

@[simp] theorem radialChart_mk (τ : ℝ) (a : CuspIndex A) (z : KPCuspCharts.Coordinates F)
    (hz : τ < z.2) : radialChart A τ a (Quotient.mk _ z.1, ⟨z.2, hz⟩) = chartLift A a z := by
  rw [radialChart, Function.comp_apply, KPCuspCharts.ChartOutput.highPresentation_formula]
  rfl

theorem end_open (τ : ℝ) (a : CuspIndex A) : IsOpen (endSet A τ a) := by
  have hop : IsOpenMap (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1)) := by
    simpa only [Function.comp_def, A.components_formula] using
      A.components.isOpenMap.comp (isOpenMap_sigmaMk (i := a.1))
  exact hop _ (KPFiniteAdelicCuspEnds.component_open_end F _ _ τ)

theorem radialChart_embedding {τ : ℝ} (hτ : A.threshold ≤ τ) (a : CuspIndex A) :
    Topology.IsEmbedding (radialChart A τ a) := by
  let C := A.cuspAtlas a.1
  let e := A.components ∘ Sigma.mk a.1
  let inc : Set.Ioi τ → Set.Ioi C.threshold := fun t =>
    ⟨t.val, (show C.threshold ≤ τ from (A.common_threshold a.1).symm ▸ hτ).trans_lt t.property⟩
  have hi : Topology.IsEmbedding inc := Topology.IsEmbedding.of_comp
    (continuous_subtype_val.subtype_mk _) continuous_subtype_val Topology.IsEmbedding.subtypeVal
  have he : radialChart A τ a = radialChart A C.threshold a ∘ Prod.map id inc := by
    funext p
    obtain ⟨q,t⟩ := p
    obtain ⟨z, rfl⟩ := Quotient.mk_surjective q
    simp only [Function.comp_apply, Prod.map_apply, id_eq]
    rw [radialChart_mk A τ a (z,t.val) t.property,
      radialChart_mk A C.threshold a (z,t.val) (inc t).property]
  have hc : KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1) = e :=
    funext fun v => (A.components_formula a.1 v).symm
  rw [he, radialChart, endChart, hc]
  exact ((A.components.isEmbedding.comp Topology.IsEmbedding.sigmaMk).comp
    ((C.end_embedding a.2).comp (((C.geometry a.2).highPresentation C.threshold).isEmbedding))).comp
    (Topology.IsEmbedding.id.prodMap hi)

theorem radialChart_range (τ : ℝ) (a : CuspIndex A) : Set.range (radialChart A τ a) = endSet A τ a := by
  rw [radialChart, endChart, Function.comp_assoc, Set.range_comp, Set.range_comp,
    Set.range_eq_univ.mpr (((A.cuspAtlas a.1).geometry a.2).highPresentation τ).surjective,
    Set.image_univ, KPFiniteCuspAtlas.endMap_range F ((A.cuspAtlas a.1).geometry a.2).positive_dimension]
  rfl

theorem chartLift_range (τ : ℝ) (a : CuspIndex A) :
    chartLift A a '' {z | τ < z.2} = endSet A τ a := by
  rw [← radialChart_range A τ a]
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(Quotient.mk _ z.1, ⟨z.2,hz⟩), radialChart_mk A τ a z hz⟩
  · rintro ⟨⟨q,t⟩, rfl⟩
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
    exact ⟨(p,t.val), t.property, (radialChart_mk A τ a (p,t.val) t.property).symm⟩

theorem height_coordinates {τ : ℝ} (hτ : A.threshold ≤ τ) (a : CuspIndex A)
    (z : KPCuspCharts.Coordinates F) (hz : τ < z.2) : height A τ a (chartLift A a z) = z.2 := by
  have h : ∃ w, τ < w.2 ∧ chartLift A a w = chartLift A a z := ⟨z,hz,rfl⟩
  obtain ⟨hw, he⟩ := Classical.choose_spec h
  rw [height, dite_eq_left h]
  exact congrArg (fun p : RadialDomain A τ a => p.2.val)
    ((radialChart_embedding A hτ a).injective
      ((radialChart_mk A τ a _ hw).trans (he.trans (radialChart_mk A τ a z hz).symm)))

theorem height_continuous {τ : ℝ} (hτ : A.threshold ≤ τ) (a : CuspIndex A) :
    ContinuousOn (height A τ a) (endSet A τ a) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let e := (radialChart_embedding A hτ a).toHomeomorph.trans
    (Homeomorph.setCongr (radialChart_range A τ a))
  refine ((continuous_subtype_val.comp continuous_snd).comp e.symm.continuous).congr ?_
  intro x
  have he : radialChart A τ a (e.symm x) = x.val := congrArg Subtype.val (e.apply_symm_apply x)
  have hk (p : RadialDomain A τ a) : height A τ a (radialChart A τ a p) = p.2.val := by
    obtain ⟨q,t⟩ := p
    obtain ⟨v, rfl⟩ := Quotient.mk_surjective q
    rw [radialChart_mk A τ a (v,t.val) t.property]
    exact height_coordinates A hτ a (v,t.val) t.property
  exact (hk (e.symm x)).symm.trans (congrArg (height A τ a) he)

theorem actual_height_descent
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (τ : ℝ) (hτ : A.threshold ≤ τ) :
    (∀ a, chartLift A a '' {z | τ < z.2} = endSet A τ a) ∧
    (∀ a z, τ < z.2 → height A τ a (chartLift A a z) = z.2) ∧
    ∀ a, ContinuousOn (height A τ a) (endSet A τ a) :=
  ⟨chartLift_range A τ, height_coordinates A hτ, height_continuous A hτ⟩

end DedekindZetaZeroFree.KPActualCollarBuffer

end
