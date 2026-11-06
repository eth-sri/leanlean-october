
import GS.UnitaryTopology.LocalTransport
import GS.UnitaryLocalModel.TopologyNeighbourhood
import GS.UnitaryLocalModel.TopologyFeasibility
import GS.UnitaryLocalModel.FullCoverage
import GS.Results.Nonmanifold
import GS.Unitary.RealEmbedding




/-!
# Topological singularities of the original unitary three-factor family

The local model is proved for the complete scalar-indexed matrix family with
its inherited topology. The dephased chart, the compact quotient, feasibility,
and coverage of every nearby matrix are all instantiated. The topological
obstruction proved here applies to every odd q >= 3.
-/
section
open GS.UnitaryManifold GS.UnitaryLocalModel
open GS.NonmanifoldCompletion
open scoped Topology
namespace GS.UnitaryTopology

variable (Q : FullUnitary q)

/-- The distinguished point, viewed inside the actual scalar-indexed family. -/
def unitaryFamilyBase  (o : Fin q) :
    GS.UnitaryNonmanifold.localFamily q :=
  ⟨scalarBlockBase Q.val,scalarBlockBase_mem_localFamily Q.val Q.property.2 o⟩



/-- An actual neighbourhood homeomorphism for the whole original matrix family.
Neither a local-model assumption nor a restricted central slice appears here. -/
theorem unitary_matrix_pointed_neighbourhood_model  (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    Nonempty (PointedNeighbourhoodModel (GS.UnitaryNonmanifold.localFamily q)
      (OuterFactors q o × ConeCoordinates ((q-1)^2))
      (unitaryFamilyBase Q o) (identityOuter q o,coneCoordinatesZero ((q-1)^2))) := by
  let d := (q-1)^2
  let ψ := euclideanDephasedParametrization Q o hQ
  let U := euclideanDephasedDomain Q o hQ
  obtain ⟨r,hr,hargs⟩ := exists_parameterBox_in_chart U
    (euclideanDephasedDomain_open Q o hQ) (zero_mem_euclideanDephasedDomain Q o hQ)
  have hunit : ∀ y ∈ U, GS.Unitary (ψ y) := by
    intro y _
    exact dephasedParametrization_unitary Q o hQ _
  have hsub : FullCompactImage ψ o r ⊆ GS.UnitaryNonmanifold.localFamily q := by
    rintro _ ⟨p,rfl⟩
    exact fullBlockImage_mem_localFamily ψ p.1 p.2.val
      (hunit _ (hargs _ p.2.property).1) (hunit _ (hargs _ p.2.property).2) p.2.property.2.2
  have hn := (continuous_smallFactorValue q).isClosedMap.eventually_nhds_fiber
    (p := fun p => p ∈ smallFullFactors Q o hQ r) (scalarBlockBase Q.val)
    (fun p he => (smallFullFactors_open Q o hQ r).mem_nhds
      (base_fibre_mem_smallFullFactors Q o hQ r hr p he))
  have hcover : fullCompactSource (GS.UnitaryNonmanifold.localFamily q) ψ o r ∈
      𝓝 (unitaryFamilyBase Q o) := by
    filter_upwards [(continuous_subtype_val.tendsto (unitaryFamilyBase Q o)).eventually hn] with M hM
    have hi : M.val ∈ Set.range (smallFactorValue q) := by
      rw [range_smallFactorValue]
      exact M.property
    obtain ⟨p,hp⟩ := hi
    change M.val ∈ FullCompactImage ψ o r
    rw [← hp]
    exact smallFullFactors_map_mem Q o hQ r p (hM p hp)
  let F := GS.UnitaryNonmanifold.localFamily q
  let x := unitaryFamilyBase Q o
  let p₀ := fullParameterZero q d o r
  have hψ := euclideanDephasedParametrization_continuousOn Q o hQ
  have hcf : Continuous (fullCompactMiddle ψ o r) := by
    have hp : Continuous (fun p : FullCompactParameters q o d r => ψ (p.2.val.1+p.2.val.2.1)) :=
      hψ.comp_continuous (by fun_prop) (fun p => (hargs p.2.val p.2.property).1)
    have hm : Continuous (fun p : FullCompactParameters q o d r => ψ (p.2.val.1-p.2.val.2.1)) :=
      hψ.comp_continuous (by fun_prop) (fun p => (hargs p.2.val p.2.property).2)
    apply (continuous_flattenBlockFamily q).comp
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    apply continuous_matrix_product
    · apply continuous_matrix_product
      · exact ((continuous_apply i).comp (continuous_outerLeft q o)).comp continuous_fst
      · have hpi := ((continuous_apply j).comp ((continuous_apply i).comp hp))
        have hmi := ((continuous_apply j).comp ((continuous_apply i).comp hm))
        exact ((hpi.add hmi).div_const 2).smul continuous_const |>.add
          (((hpi.sub hmi).div_const 2).smul (continuous_pauli.comp (by fun_prop)))
    · exact ((continuous_apply j).comp (continuous_outerRight q o)).comp continuous_fst
  obtain ⟨h,hh⟩ := exists_homeomorph_ranges_of_same_fibres
    (fullCompactMiddle ψ o r) (@fullCompactCone q d o r)
    hcf (by
      apply Continuous.prodMk continuous_fst
      apply Continuous.subtype_mk
      exact (continuous_parameterCone d).comp (continuous_subtype_val.comp continuous_snd)) (by
      intro p p'
      rw [fullCompactMiddle_fibres Q.val o ψ U
        (euclideanDephasedParametrization_injectiveOn Q o hQ)
        (fun y hy => (dephased_constraints_iff Q.val _ o).mp
          (dephasedParametrization_constraints Q o hQ _ hy)) r hargs p p']
      simp only [fullCompactCone, Prod.mk.injEq, Subtype.mk.injEq])
  let e := (Homeomorph.setCongr (fullCompactCone_surjective q d o r).range_eq).trans
    (Homeomorph.Set.univ _)
  refine ⟨{
    source := fullCompactSource F ψ o r
    target := outerConeRegion q d o r
    source_nhds := hcover
    target_nhds := continuous_snd.continuousAt.preimage_mem_nhds (boundedConeCoordinates_mem_nhds d hr)
    chart := ((fullCompactSourceHomeomorph F ψ o r hsub).trans (h.trans e)).trans
      (outerBoundedHomeomorph q d o r)
    map_point := ?_ }⟩
  intro hx
  have he : fullCompactSourceHomeomorph F ψ o r hsub ⟨x,hx⟩ =
      ⟨fullCompactMiddle ψ o r p₀,⟨p₀,rfl⟩⟩ := Subtype.ext (by simp [d,p₀,x,ψ,unitaryFamilyBase,fullCompactSourceHomeomorph] <;> rfl)
  change ((outerBoundedHomeomorph q d o r)
    (e (h (fullCompactSourceHomeomorph F ψ o r hsub ⟨x,hx⟩)))).val = _
  rw [he,hh p₀]
  change (p₀.1,parameterCone p₀.2.val) = (p₀.1,coneCoordinatesZero d)
  simp [d,p₀,fullParameterZero]

end GS.UnitaryTopology
