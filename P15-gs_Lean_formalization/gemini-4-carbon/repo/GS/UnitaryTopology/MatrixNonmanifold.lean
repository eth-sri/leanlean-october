module

public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import GS.UnitaryTopology.Nonmanifold
public import GS.UnitaryLocalModel.FullCoverage
public import GS.UnitaryManifold.CayleyCharts
public import GS.Results.Nonmanifold
public import GS.Unitary.RealEmbedding

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS GS.NonmanifoldFinal GS.NonmanifoldClosure GS.NonmanifoldObstruction GS.NonmanifoldCompletion
open GS.UnitaryManifold GS.UnitaryLocalModel GS.UnitaryGeometry
open scoped Topology

namespace GS.UnitaryTopology

def pointedOpenModel_prodRight {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {x : X} {y : Y} (g : PointedOpenModel X Y x y) (z : Z) :
    PointedOpenModel (X × Z) (Y × Z) (x, z) (y, z) where
  source := g.source ×ˢ Set.univ
  target := g.target ×ˢ Set.univ
  source_open := g.source_open.prod isOpen_univ
  target_open := g.target_open.prod isOpen_univ
  source_point := ⟨g.source_point, Set.mem_univ z⟩
  target_point := ⟨g.target_point, Set.mem_univ z⟩
  chart := (Homeomorph.Set.prod g.source Set.univ).trans
    ((g.chart.prodCongr (Homeomorph.refl _)).trans (Homeomorph.Set.prod g.target Set.univ).symm)
  map_point hx := Prod.ext (g.map_point hx.1) rfl

private theorem fd_eucl {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (c : OpenPartialHomeomorph X E) (x : X) (hx : x ∈ c.source) : EuclideanAt x := by
  let n := Module.finrank ℝ E
  let e : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  let p := c.trans (e.toHomeomorph.trans (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph).toOpenPartialHomeomorph
  exact ⟨p.source, p.open_source, ⟨hx, Set.mem_univ _⟩, n, p.target, p.open_target, ⟨p.toHomeomorphSourceTarget⟩⟩

theorem outerFactors_euclideanAt {q : ℕ} {o : Fin q} (a : OuterFactors q o) : EuclideanAt a :=
  fd_eucl ((OpenPartialHomeomorph.pi fun i => blockPartialChart (a.1 i)).prod
    (OpenPartialHomeomorph.pi fun j => blockPartialChart (a.2 j))) a
    ⟨fun i _ => base_mem_chartSource (a.1 i), fun j _ => base_mem_chartSource (a.2 j)⟩

def euclideanConeCoordinates (n d : ℕ) :
    (Eucl n × ConeCoordinates d) ≃ₜ ((Fin (n + d) → ℝ) × RankThreeCone (Fin d)) :=
  (((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.prodCongr (Homeomorph.refl (ConeCoordinates d))).trans
    (Homeomorph.prodAssoc _ _ _).symm).trans
    ((sumCoordinates.trans (reindexReal finSumFinEquiv)).prodCongr (Homeomorph.refl _))

theorem not_euclidean_of_unitary_cone_neighbourhoodModel_odd
    {F : Type} [TopologicalSpace F] {f : F} {q : ℕ} (o : Fin q) (a : OuterFactors q o)
    (hq : 3 ≤ q) (hodd : Odd q)
    (g : PointedNeighbourhoodModel F (OuterFactors q o × ConeCoordinates ((q - 1) ^ 2))
      f (a, coneCoordinatesZero ((q - 1) ^ 2))) :
    ¬ EuclideanAt f := by
  let d := (q - 1) ^ 2
  have hd : 0 < d := Nat.pow_pos (by omega)
  have hdiv : 4 ∣ d := by
    obtain ⟨k, hk⟩ := hodd; refine ⟨k ^ 2, ?_⟩
    have he : q - 1 = 2 * k := by omega
    dsimp [d]; rw [he]; ring
  refine not_euclideanAt_of_pointedOpenModel (pointedOpenModel g) ?_
  obtain ⟨n, c, hc⟩ := (euclideanAt_iff_chart a).mp (outerFactors_euclideanAt a)
  obtain ⟨b, _⟩ := exists_centeredChart c a hc
  let ga : PointedOpenModel (OuterFactors q o) (Eucl n) a 0 :=
    { source := b.source, target := {z | ‖z‖ < b.radius}
      source_open := b.source_open, target_open := isOpen_lt continuous_norm continuous_const
      source_point := b.source_point, target_point := by simpa using b.radius_pos
      chart := b.chart, map_point := b.map_point }
  intro he
  have hflat := euclideanAt_of_homeomorph (euclideanConeCoordinates n d) (0, coneCoordinatesZero d)
    ((euclideanAt_pointedOpenModel (pointedOpenModel_prodRight ga (coneCoordinatesZero d))).mp he)
  have hz0 : euclideanConeCoordinates n d (0, coneCoordinatesZero d) = (0, rankThreeZero) :=
    Prod.ext (funext fun i => by change Sum.elim (0 : Fin n → ℝ) (0 : Fin d → ℝ) (finSumFinEquiv.symm i) = 0; cases finSumFinEquiv.symm i <;> rfl) rfl
  exact rankThreeProduct_not_euclidean_of_four_dvd (n + d) d hd hdiv (hz0 ▸ hflat)

def unitaryFamilyBase {q : ℕ} (Q : FullUnitary q) (o : Fin q) : GS.UnitaryNonmanifold.localFamily q :=
  ⟨scalarBlockBase Q.val, scalarBlockBase_mem_localFamily Q.val Q.property.2 o⟩

theorem unitary_gs_not_euclidean_at {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q)
    (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    ¬ EuclideanAtSubset (GS.UnitaryNonmanifold.localFamily q) (scalarBlockBase Q.val) := by
  let ψ := euclideanDephasedParametrization Q o hQ
  let U := euclideanDephasedDomain Q o hQ
  obtain ⟨r, hr, hargs⟩ := exists_parameterBox_in_chart U
    (euclideanDephasedDomain_open Q o hQ) (zero_mem_euclideanDephasedDomain Q o hQ)
  obtain ⟨W, hW, hbaseW, hcoverW⟩ := exists_open_full_compact_coverage Q o hQ r hr
  have hcover : fullCompactSource (GS.UnitaryNonmanifold.localFamily q) ψ o r ∈ 𝓝 (unitaryFamilyBase Q o) :=
    Filter.mem_of_superset ((hW.preimage continuous_subtype_val).mem_nhds hbaseW) fun M hM => hcoverW M.val M.property hM
  obtain ⟨g⟩ := full_compact_pointed_neighbourhood_model
    (GS.UnitaryNonmanifold.localFamily q) (unitaryFamilyBase Q o) Q.val o ψ U
    (euclideanDephasedParametrization_continuousOn Q o hQ)
    (euclideanDephasedParametrization_injectiveOn Q o hQ)
    (fun y hy => (dephased_constraints_iff Q.val _ o).mp (dephasedParametrization_constraints Q o hQ _ hy))
    r hr hargs
    (fullCompactImage_subset_localFamily ψ o U (fun y _ => dephasedParametrization_unitary Q o hQ _) r hargs)
    hcover (fullParameterZero q ((q - 1) ^ 2) o r) (by simp [ψ, unitaryFamilyBase]) (parameterCone_zero ((q - 1) ^ 2))
  intro he
  exact not_euclidean_of_unitary_cone_neighbourhoodModel_odd o (identityOuter q o) hq hodd g
    ((euclideanAtSubset_iff (GS.UnitaryNonmanifold.localFamily q) (scalarBlockBase Q.val) (unitaryFamilyBase Q o).property).mp he)

def unitaryReflection (q : ℕ) (hq : 3 ≤ q) : FullUnitary q :=
  fullUnitary (ofRealMatrix (GS.Results.reflectionBase q))
    (ofRealMatrix_unitary (GS.Results.reflectionBase_orthogonal q (by omega)))

theorem exists_unitary_nonEuclidean_point (q : ℕ) (hq : 3 ≤ q) (hodd : Odd q) :
    ∃ M : CMat (q * 2), M ∈ GS.UnitaryNonmanifold.localFamily q ∧
      ¬ EuclideanAtSubset (GS.UnitaryNonmanifold.localFamily q) M := by
  let o : Fin q := ⟨0, by omega⟩
  have hne (i j : Fin q) : (unitaryReflection q hq).val i j ≠ 0 := by
    change (GS.Results.reflectionBase q i j : ℂ) ≠ 0
    exact_mod_cast GS.Results.reflectionBase_entries_ne_zero q hq i j
  exact ⟨scalarBlockBase (unitaryReflection q hq).val, (unitaryFamilyBase (unitaryReflection q hq) o).property,
    unitary_gs_not_euclidean_at hq hodd (unitaryReflection q hq) o ⟨fun i => ⟨hne i o, hne i o⟩, fun j => ⟨hne o j, hne o j⟩⟩⟩

end GS.UnitaryTopology
