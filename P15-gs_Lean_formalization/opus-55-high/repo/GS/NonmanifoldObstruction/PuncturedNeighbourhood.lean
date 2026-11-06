module

public import GS.Topology.SectionPair
public import GS.NonmanifoldObstruction.ProductSphere

@[expose] public section


/-!
# An actual sphere retract of EVERY punctured open neighbourhood

Compactness puts one sufficiently small spherical section entirely inside a
specified open neighbourhood. The sphere projection is defined on the whole
punctured cone product, so its restriction gives an exact continuous retraction.

No claim is made here that a homology functor has been implemented or applied.
-/
noncomputable section
namespace GS.NonmanifoldObstruction

variable {ι : Type*} [Fintype ι]

/-- The explicit auxiliary sphere is compact in the usual product topology. -/
theorem isCompact_planeSphere : IsCompact {p : PlaneSpace ι | planeEnergy p = 1} := by
  refine (isCompact_Icc (a := ((-1, -1) : PlaneSpace ι)) (b := (1, 1))).of_isClosed_subset
    (isClosed_eq continuous_planeEnergy continuous_const) fun p (hp : vectorSq p.1 + (p.2 0^2 + p.2 1^2) = 1) => ?_
  have := vectorSq_nonneg p.1
  have h1 (i) : |p.1 i| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    have := Finset.single_le_sum (fun j _ => sq_nonneg (p.1 j)) (Finset.mem_univ i)
    unfold vectorSq at *
    nlinarith [sq_nonneg (p.2 0), sq_nonneg (p.2 1)]
  have h2 (i : Fin 2) : |p.2 i| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    fin_cases i <;> dsimp <;> nlinarith [sq_nonneg (p.2 0), sq_nonneg (p.2 1)]
  refine ⟨⟨fun i => ?_, fun i => ?_⟩, fun i => ?_, fun i => ?_⟩ <;> simp only [Pi.neg_apply, Pi.one_apply] <;> grind

instance planeSphere_compactSpace : CompactSpace (PlaneSphere ι) :=
  isCompact_iff_compactSpace.mp isCompact_planeSphere

/-- A compact-parameter tube lemma proved by closedness of projection.
Unlike pointwise continuity, this gives a SINGLE parameter neighbourhood
working for every point of K. -/
theorem uniform_neighbourhood_of_compact_parameter
    {A K X : Type*} [TopologicalSpace A] [TopologicalSpace K]
    [TopologicalSpace X] [CompactSpace K]
    (F : A × K → X) (hF : Continuous F) (a : A) (U : Set X)
    (hU : IsOpen U) (ha : ∀ k, F (a,k) ∈ U) :
    ∃ V : Set A, IsOpen V ∧ a ∈ V ∧ ∀ t ∈ V, ∀ k, F (t,k) ∈ U := by
  refine ⟨(Prod.fst '' (F ⁻¹' Uᶜ))ᶜ, (isClosedMap_fst_of_compactSpace _ (hU.isClosed_compl.preimage hF)).isOpen_compl, ?_, ?_⟩ <;> aesop

/-- Jointly continuous even at scale zero. -/
def scaledSectionFamily (d : ℕ) (p : ℝ × PlaneSphere ι) : ConeSpace ι (Fin (d+2)) :=
  productSection d (p.1 • p.2.val)

theorem continuous_scaledSectionFamily (d : ℕ) :
    Continuous (@scaledSectionFamily ι _ d) :=
  (continuous_productSection d).comp
    (by fun_prop)

@[simp] theorem scaledSectionFamily_zero (d : ℕ) (v : PlaneSphere ι) :
    scaledSectionFamily d (0,v) = productZero := by
  simp [scaledSectionFamily]

/-- Uniform smallness in an ARBITRARY open neighbourhood, not only a round ball. -/
theorem exists_small_sphere_in_open (d : ℕ)
    (U : Set (ConeSpace ι (Fin (d+2)))) (hU : IsOpen U) (hzero : productZero ∈ U) :
    ∃ t : ℝ, 0<t ∧ ∀ v : PlaneSphere ι, productSection d (t • v.val) ∈ U := by
  obtain ⟨V,hV,h0,hsub⟩ := uniform_neighbourhood_of_compact_parameter
    (scaledSectionFamily d) (continuous_scaledSectionFamily d) 0 U hU
    (by simp_all)
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hV 0 h0
  refine ⟨δ/2, by positivity, fun v => hsub (δ/2) (hball ?_) v⟩
  simp [abs_of_pos hδ]
  linarith

/-- Explicit continuous maps with a proved left-inverse law, not a homology
or nonmanifold assumption. -/
-- ContinuousSectionPair is imported from GS.Topology.SectionPair.

abbrev PuncturedOpen (d : ℕ) (U : Set (ConeSpace ι (Fin (d+2)))) :=
  {p : ConeSpace ι (Fin (d+2)) // p ∈ U ∧ p ≠ productZero}

/-- The central topological construction. It includes all Euclidean factors
and works for every neighbourhood before assuming any putative manifold chart. -/
theorem punctured_open_has_sphere_retract (d : ℕ)
    (U : Set (ConeSpace ι (Fin (d+2)))) (hU : IsOpen U) (hzero : productZero ∈ U) :
    Nonempty (ContinuousSectionPair (PlaneSphere ι) (PuncturedOpen d U)) := by
  obtain ⟨t,ht,hsmall⟩ := exists_small_sphere_in_open d U hU hzero
  exact ⟨{
    sectionMap := fun v => ⟨(smallSphereSection d t ht v).val, hsmall v, by grind⟩
    retractionMap := fun p => sphereProjection ⟨p.val, p.2.2⟩
    section_continuous := (continuous_subtype_val.comp (continuous_smallSphereSection d t ht)).subtype_mk _
    retraction_continuous := continuous_sphereProjection.comp (continuous_subtype_val.subtype_mk _)
    retraction_section := sphereProjection_smallSphereSection d t ht }⟩

end GS.NonmanifoldObstruction
