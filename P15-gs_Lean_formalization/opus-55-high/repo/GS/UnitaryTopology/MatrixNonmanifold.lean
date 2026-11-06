module

public import GS.UnitaryTopology.LocalTransport
public import GS.UnitaryLocalModel.TopologyNeighbourhood
public import GS.UnitaryLocalModel.TopologyFeasibility
public import GS.UnitaryLocalModel.FullCoverage
public import GS.Results.Nonmanifold
public import GS.Unitary.RealEmbedding

@[expose] public section


/-!
# Topological singularities of the original unitary three-factor family

The local model is proved for the complete scalar-indexed matrix family with
its inherited topology. The dephased chart, the compact quotient, feasibility,
and coverage of every nearby matrix are all instantiated. The topological
obstruction proved here applies to every odd q >= 3.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS GS.UnitaryManifold GS.UnitaryLocalModel GS.UnitaryGeometry
open GS.NonmanifoldFinal GS.NonmanifoldCompletion GS.NonmanifoldClosure GS.NonmanifoldObstruction
open scoped Topology
namespace GS.UnitaryTopology

/-- A genuine topological obstruction for the full complex matrix family, at
the real Householder matrix viewed as a unitary matrix. -/
theorem exists_unitary_nonEuclidean_point (q : ℕ) (hq : 3≤q) (hodd : Odd q) :
    ∃ M : CMat (q*2), M ∈ sFamily ℂ q ∧
      ¬ EuclideanAtSubset (sFamily ℂ q) M := by
  let Q : FullUnitary q := fullUnitary (ofRealMatrix (GS.Results.reflectionBase q))
    (ofRealMatrix_unitary (GS.Results.reflectionBase_orthogonal q (by omega)))
  let o : Fin q := ⟨0,by omega⟩
  have h (i j : Fin q) : Q.val i j ≠ 0 := by
    change (GS.Results.reflectionBase q i j : ℂ) ≠ 0
    exact_mod_cast GS.Results.reflectionBase_entries_ne_zero q hq i j
  have hQ : AnchorNonzero Q.val Q.val o := ⟨fun i => ⟨h i _, h i _⟩, fun j => ⟨h _ j, h _ j⟩⟩
  let B : sFamily ℂ q := ⟨scalarBlockBase Q.val, by
    have h := fullBlockImage_mem_localFamily (d := 0) (fun _ => Q.val)
      (identityOuter q o) (parameterZero 0) Q.2.2 Q.2.2 (by simp [parameterZero,OnSphere])
    have he := fullCompactMiddle_zero (d := 0) (fun _ => Q.val) o 0
    change fullBlockImage (fun _ => Q.val) (identityOuter q o) (parameterZero 0) = _ at he
    grind⟩
  let ψ := euclideanDephasedParametrization Q o hQ
  obtain ⟨r,hr,hargs⟩ := exists_parameterBox_in_chart _
    (euclideanDephasedDomain_open Q o hQ) (zero_mem_euclideanDephasedDomain Q o hQ)
  obtain ⟨W,hW,hbaseW,hcoverW⟩ := GS.Continuation.compact_full_fibre_neighbourhood
    (smallFactorValue q) ((continuous_smallFactorMap q).comp continuous_subtype_val) Set.univ isCompact_univ
    (smallFullFactors Q o hQ r) (smallFullFactors_open Q o hQ r) (scalarBlockBase Q.val)
    fun p _ he => by
      have hh := congrArg (@extractBlockFamily q) he
      rw [scalarBlockBase,extract_flattenBlockFamily] at hh
      have hm := base_fibre_dephased_middle p.val.1 p.val.2.2.2 Q.val p.val.2.1 p.val.2.2.1 o p.property.1
        p.property.2.2.2 (fun i => (hQ.1 i).1) (fun j => (hQ.2 j).1)
        fun i j => Matrix.ext fun a b => (smallFactorMap_block p.val i j a b).symm.trans (congrFun₂ (congrFun₂ hh i j) a b)
      refine ⟨⟨p, hm.1⟩, ?_, rfl⟩
      constructor <;> convert base_mem_smallDephasedSource Q o hQ r hr using 1 <;> ext1 <;> ext1
      exacts [hm.2.1, hm.2.2]
  obtain ⟨h,hh⟩ := exists_full_compact_homeomorphism Q.val o ψ _
    (euclideanDephasedParametrization_continuousOn Q o hQ)
    (euclideanDephasedParametrization_injectiveOn Q o hQ)
    (fun y hy => (dephased_constraints_iff Q.val _ o).mp (dephasedParametrization_constraints Q o hQ _ hy)) r hargs
  have hsub : FullCompactImage ψ o r ⊆ sFamily ℂ q := by
    rintro _ ⟨p,rfl⟩
    exact fullBlockImage_mem_localFamily ψ p.1 p.2.val (dephasedParametrization_unitary Q o hQ _) (dephasedParametrization_unitary Q o hQ _) p.2.2.2.2
  let m : PointedNeighbourhoodModel (sFamily ℂ q) (OuterFactors q o × ConeCoordinates ((q-1)^2)) B
      (identityOuter q o, coneCoordinatesZero _) := {
    source := {M | M.val ∈ FullCompactImage ψ o r}
    target := {p | p.2 ∈ boundedConeCoordinates _ r}
    source_nhds := Filter.mem_of_superset ((hW.preimage continuous_subtype_val).mem_nhds hbaseW) fun M hM => by
      obtain ⟨p,hp,hpM⟩ := hcoverW M.val hM (by rw [Set.image_univ,range_smallFactorValue]; grind [M.2])
      simpa [← hpM] using smallFullFactors_map_mem Q o hQ r p hp.2
    target_nhds := continuous_snd.continuousAt.preimage_mem_nhds (boundedConeCoordinates_mem_nhds _ hr)
    chart := (({ toFun x := ⟨x.val.val,x.property⟩, invFun y := ⟨⟨y.val,hsub y.property⟩,y.property⟩
                 left_inv := by grind, right_inv := by grind } : {M : sFamily ℂ q | M.val ∈ FullCompactImage ψ o r} ≃ₜ _).trans h).trans
      { toFun p := ⟨(p.1,p.2.val),p.2.property⟩, invFun p := (p.val.1,⟨p.val.2,p.property⟩)
        left_inv := by grind, right_inv := by grind }
    map_point := fun hx => by
      have he : ∀ hy, (⟨B.val, hy⟩ : FullCompactImage ψ o r) = ⟨fullCompactMiddle ψ o r (fullParameterZero q ((q-1)^2) o r),_,rfl⟩ :=
        fun _ => Subtype.ext (by simp [ψ,B])
      simp
      rw [he, hh]
      simp [fullCompactCone, fullParameterZero] }
  refine ⟨_, B.property, fun he => mt (euclideanAt_pointedOpenModel (pointedOpenModel m)).mp (fun he => ?_)
    ((euclideanAtSubset_iff _ _ he.1).mp he)⟩
  let a := identityOuter q o
  let p := ((OpenPartialHomeomorph.pi fun i => blockPartialChart (a.1 i)).prod
    (OpenPartialHomeomorph.pi fun i => blockPartialChart (a.2 i))).trans (ContinuousLinearEquiv.ofFinrankEq
      (F := Eucl (Module.finrank ℝ _)) finrank_euclideanSpace_fin.symm).toHomeomorph.toOpenPartialHomeomorph
  obtain ⟨n,c,hc⟩ := (euclideanAt_iff_chart a).mp ⟨p.source,p.open_source,by simp [p]; exact ⟨fun _ => base_mem_chartSource _, fun _ _ => base_mem_chartSource _⟩,_,p.target,p.open_target,⟨p.toHomeomorphSourceTarget⟩⟩
  obtain ⟨b,_⟩ := exists_centeredChart c a hc
  refine rankThreeProduct_not_euclidean_of_four_dvd (n+(q-1)^2) _ (pow_pos (by omega : 0 < q-1) 2) ?_ ?_
  · obtain ⟨k,rfl⟩ := hodd
    exact ⟨k^2, by simp; ring⟩
  simpa using euclideanAt_of_homeomorph (euclideanConeCoordinates n _) _
    ((euclideanAt_pointedOpenModel (x := (a, coneCoordinatesZero _)) (y := (0, coneCoordinatesZero _)) ⟨b.source ×ˢ Set.univ, {z : Eucl n | ‖z‖ < b.radius} ×ˢ Set.univ,
      b.source_open.prod isOpen_univ, (isOpen_lt continuous_norm continuous_const).prod isOpen_univ,
      ⟨b.source_point, trivial⟩, ⟨by simpa using b.radius_pos, trivial⟩,
      (Homeomorph.Set.prod _ _).trans ((b.chart.prodCongr (.refl _)).trans (Homeomorph.Set.prod _ _).symm),
      fun hx => Prod.ext (b.map_point hx.1) rfl⟩).mp he)


end GS.UnitaryTopology
