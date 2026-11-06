module

public import PottsDiscontinuity.Torus.DiamondIntersectionLocality
public import PottsDiscontinuity.TorusTopology.IndexedWalk

/-! An integer winding divisor gives a modular vertex phase, constant on
seam-closed components. The construction integrates indexed walks, so parallel
edges and their seam crossings are retained. -/

public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus
variable {N M : ℕ}
noncomputable section

/-- An integral cycle-flux divisor in one primal cluster gives an actual
modular potential for the seam cocycle on all edges of that cluster. -/
theorem exists_winding_phase_of_integral_divisor
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (b : ℕ)
    (hdiv : ∀ f : diamondCycleSpace hN hM A,
      SupportedOnDiamondCluster hN hM A c f →
      (∀ e : OpenDiamondEdge A, ∃ z : ℤ, f.val e = z) →
      ∃ z : ℤ, diamondWindingY A f.val = (((b : ℤ)*z : ℤ) : ℚ)) :
    ∃ g : FaceVertex N M true → ZMod b,
      ∀ e : OpenDiamondEdge A, diamondEdgeCluster hN hM A e = c →
        g (faceEndpoint hN hM true e.val true) - g (faceEndpoint hN hM true e.val false) =
          if e.val.2.val=0 then -1 else 0 := by
  classical
  obtain ⟨u₀,hu₀⟩ : ∃ u : FaceVertex N M true,
      (diamondOpenGraph hN hM true A).connectedComponentMk u = c := by
    induction c using Quot.inductionOn with
    | h u => tauto
  let V := {u : FaceVertex N M true // (diamondOpenGraph hN hM true A).connectedComponentMk u = c}
  have hpaths (u : V) :=
    exists_indexedWalk_of_reachable hN hM A
      (SimpleGraph.ConnectedComponent.eq.1 (hu₀.trans u.property.symm))
  let p (u : V) := Classical.choice (hpaths u)
  let g : FaceVertex N M true → ZMod b := fun u =>
    if hu : (diamondOpenGraph hN hM true A).connectedComponentMk u = c
      then ((p ⟨u,hu⟩).winding : ℤ) else 0
  refine ⟨g,?_⟩
  intro e hec
  have ht :=
    (SimpleGraph.ConnectedComponent.sound
      (diamond_endpoints_reachable hN hM A e.val e.property)).symm.trans hec
  let pu := p ⟨faceEndpoint hN hM true e.val false,hec⟩
  let pv := p ⟨faceEndpoint hN hM true e.val true,ht⟩
  let F := pu.chain + Pi.single e 1 - pv.chain
  have hF : F ∈ diamondCycleSpace hN hM A := by
    change diamondBoundary hN hM A F = 0
    rw [map_sub,map_add,pu.boundary_chain,pv.boundary_chain,diamondBoundary_single]
    simp
  let f : diamondCycleSpace hN hM A := ⟨F,hF⟩
  have hs : SupportedOnDiamondCluster hN hM A c f := by
    intro d hd
    have hd₀ : diamondEdgeCluster hN hM A d ≠
        (diamondOpenGraph hN hM true A).connectedComponentMk u₀ := by rwa [hu₀]
    have hde : d ≠ e := by aesop
    change pu.chain d + (Pi.single e (1 : ℚ) : OpenDiamondEdge A → ℚ) d - pv.chain d = 0
    rw [pu.chain_supported d hd₀,pv.chain_supported d hd₀]
    simp [hde]
  have hint : ∀ d : OpenDiamondEdge A, ∃ z : ℤ, f.val d = z := by
    intro d
    obtain ⟨zu,hzu⟩ := pu.chain_integral d
    obtain ⟨zv,hzv⟩ := pv.chain_integral d
    refine ⟨zu+(if d=e then 1 else 0)-zv,?_⟩
    change pu.chain d + (Pi.single e (1 : ℚ) : OpenDiamondEdge A → ℚ) d - pv.chain d = _
    simp only [hzu,hzv,Pi.single_apply]
    simp
  let s := if e.val.2.val=0 then -1 else 0
  have hw : diamondWindingY A f.val = ((pu.winding+s-pv.winding : ℤ) : ℚ) := by
    change diamondWindingY A (pu.chain + Pi.single e 1 - pv.chain) = _
    unfold diamondWindingY
    simp only [Pi.sub_apply,Pi.add_apply,mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    change diamondWindingY A pu.chain +
      (∑ d, diamondSeamCrossY d.val * (Pi.single e (1 : ℚ) : OpenDiamondEdge A → ℚ) d) -
      diamondWindingY A pv.chain = _
    rw [pu.winding_chain,pv.winding_chain]
    simp [Pi.single_apply,mul_ite,diamondSeamCrossY,s]
  obtain ⟨z,hz⟩ := hdiv f hs hint
  have hcast := congrArg (fun z : ℤ => (z : ZMod b)) (by exact_mod_cast (hw.symm.trans hz))
  simp at hcast
  have hg : g (faceEndpoint hN hM true e.val true) -
      g (faceEndpoint hN hM true e.val false) = (s : ZMod b) := by
    have hf₀ : (diamondOpenGraph hN hM true A).connectedComponentMk
        (faceEndpoint hN hM true e.val false) = c := hec
    dsimp only [g]
    rw [dite_eq_left ht,dite_eq_left hf₀]
    linear_combination -hcast
  rw [hg]
  dsimp [s]
  split_ifs <;> simp

end
end PottsDiscontinuity.TorusTopology
