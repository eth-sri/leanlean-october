
import GS.UnitaryLocalModel.FullCoverageCoordinates
import GS.UnitaryLocalModel.TopologyFeasibility
import GS.Continuation.CompactCoverageTools



/-!
# Coverage of an actual neighbourhood in the complete unitary family

Every representative of the full compact scalar-block fibre lies in the
normalization maps this open set into the compact local model. Compactness
then provides an ambient open neighbourhood whose intersection with the
original matrix family is covered. No chosen-branch coverage is assumed.
-/
open GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel

/-- The open coordinate set contains every representative of the complete base fibre. -/
theorem base_fibre_mem_smallFullFactors (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) (hr : 0<r)
    (p : SmallFactorSpace q) (he : smallFactorValue q p = scalarBlockBase Q.val) :
    p ∈ smallFullFactors Q o hQ r := by
  have hv : extractBlockFamily (smallFactorValue q p) = fun i j =>
      p.val.1 i * diagTwo (p.val.2.1 i j) (p.val.2.2.1 i j) * p.val.2.2.2 j := by
    funext i j a b
    exact smallFactorMap_block p.val i j a b
  have hb := congrArg (@extractBlockFamily q) he
  rw [hv,scalarBlockBase,extract_flattenBlockFamily] at hb
  have hb := fun i j => congrFun (congrFun hb i) j
  have hn i j (hij : Q.val i j ≠ 0) : p.val.2.1 i j ≠ 0 ∧ p.val.2.2.1 i j ≠ 0 := by
    have hd := congrArg Matrix.det (hb i j)
    simp only [Matrix.det_mul,diagTwo,Matrix.det_diagonal,Fin.prod_univ_two,
      Matrix.det_smul,Fintype.card_fin,Matrix.det_one,mul_one] at hd
    have hh : p.val.2.1 i j * p.val.2.2.1 i j ≠ 0 := by
      intro h
      exact (pow_ne_zero 2 hij) (by aesop)
    exact mul_ne_zero_iff.mp hh
  have ha : AnchorNonzero Q.val p.val.2.1 o ∧ AnchorNonzero Q.val p.val.2.2.1 o :=
    ⟨⟨fun i => ⟨(hQ.1 i).1,(hn i o (hQ.1 i).1).1⟩,
       fun j => ⟨(hQ.2 j).1,(hn o j (hQ.2 j).1).1⟩⟩,
     ⟨fun i => ⟨(hQ.1 i).1,(hn i o (hQ.1 i).1).2⟩,
       fun j => ⟨(hQ.2 j).1,(hn o j (hQ.2 j).1).2⟩⟩⟩
  refine ⟨⟨p,ha⟩,?_,rfl⟩
  have hm := base_fibre_dephased_middle p.val.1 p.val.2.2.2 Q.val p.val.2.1 p.val.2.2.1 o
    p.property.1 p.property.2.2.2 (fun i => (hQ.1 i).1) (fun j => (hQ.2 j).1) hb
  simpa only [smallAnchorFactors,Set.mem_ofPred_eq,dephasedFirst,dephasedSecond,hm.1,hm.2,dephasedBase,fullUnitary] using
    And.intro (base_mem_smallDephasedSource Q o hQ r hr) (base_mem_smallDephasedSource Q o hQ r hr)



end GS.UnitaryLocalModel
