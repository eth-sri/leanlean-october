import Mathlib.Tactic

import RequestProject.RoseCoverGeneratorChain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

  (c : StrictOrdEdge P →₀ ℤ)
variable (hc : ∀ v, f v ≠ Rose.base → FiniteChains.Comb.bdry1 (strictOrderCx P) c v = 0)
include hc in
/-- Selected coordinates detect finite chains whose boundary is supported on the base fibre. -/
theorem roseCover_chain_eq_zero_of_boundary_off_base 
    
    (hz : ∀ (e : StrictOrdEdge P) (i : α),
      (strictOrderCxMap f hf.strictMono).onE e = roseMidEdge i true → c e = 0) : c = 0 := by
  have hm : ∀ (e : StrictOrdEdge P) (i : α) (b : Bool),
      (strictOrderCxMap f hf.strictMono).onE e = roseMidEdge i b → c e = 0 := by
    intro e i b he
    cases b with
    | true => exact hz e i he
    | false =>
      have hv : f e.1.1 = Rose.mid i :=
        congrArg (fun r : StrictOrdEdge (Rose α) => r.1.1) he
      have hl := hf.strictEdgeLiftFrom_unique (roseMidEdge i false) e.1.1 hv e he rfl
      have hr := hz (hf.strictEdgeLiftFrom (roseMidEdge i true) e.1.1 hv) i
        (hf.strictEdgeLiftFrom_projection _ _ _)
      have hb := roseCover_boundary_mid f hf e.1.1 i hv c
      grind
  ext e
  obtain ⟨i, b, he⟩ := rose_strict_edge_cases ((strictOrderCxMap f hf.strictMono).onE e)
  rcases he with he | he
  · have hq : f e.1.2 = Rose.edg i b :=
      congrArg (fun r : StrictOrdEdge (Rose α) => r.1.2) he
    have hl := hf.strictEdgeLiftTo_unique (roseBaseEdge i b) e.1.2 hq e he rfl
    have hr := hm (hf.strictEdgeLiftTo (roseMidEdge i b) e.1.2 hq) i b
      (hf.strictEdgeLiftTo_projection _ _ _)
    have hb := roseCover_boundary_end f hf e.1.2 i b hq c
    grind
  · exact hm e i b he

/-- Realize arbitrary finite selected coefficients by genuine generator chains. -/
noncomputable def roseCoverRealizeGeneratorCoordinates  :=
  Finsupp.linearCombination ℤ (fun e =>
    roseCoverGeneratorChain f hf ((roseCoverMidpointEdgeEquiv f hf).symm e))

/-- Realization recovers exactly the prescribed actual selected coefficients. -/
theorem roseCoverRealizeGeneratorCoordinates_coordinates
    (c : roseCoverGeneratorEdges f hf →₀ ℤ) :
    roseCoverGeneratorCoordinates f hf (roseCoverRealizeGeneratorCoordinates f hf c) = c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single e n =>
    rw [roseCoverRealizeGeneratorCoordinates, Finsupp.linearCombination_single, map_smul,
      roseCoverGeneratorChain_coordinates]
    change n • Finsupp.single ((roseCoverMidpointEdgeEquiv f hf)
      ((roseCoverMidpointEdgeEquiv f hf).symm e)) (1 : ℤ) = _
    rw [Equiv.apply_symm_apply, Finsupp.smul_single]
    simp

/-- Every realized finite generator chain has zero boundary outside the actual base fibre. -/
theorem roseCoverRealizeGeneratorCoordinates_boundary_off_base
    (c : roseCoverGeneratorEdges f hf →₀ ℤ) (v : P) (hv : f v ≠ Rose.base) :
    FiniteChains.Comb.bdry1 (strictOrderCx P) (roseCoverRealizeGeneratorCoordinates f hf c) v = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
    rw [roseCoverRealizeGeneratorCoordinates, Finsupp.linearCombination_single, map_smul,
      roseCoverGeneratorChain_boundary]
    let p := (roseCoverMidpointEdgeEquiv f hf).symm e
    have hn : ∀ b, v ≠ (roseCoverMidpointBaseEdge f hf p b).val.1 := by
      intro b he
      apply hv
      have hp := hf.strictEdgeLiftTo_projection (roseBaseEdge p.val.2 b)
        (roseCoverMidpointEndEdge f hf p b).val.2
        (congrArg (fun r : StrictOrdEdge (Rose α) => r.val.2)
          (hf.strictEdgeLiftFrom_projection (roseMidEdge p.val.2 b) p.val.1 p.property))
      exact (congrArg f he).trans (congrArg (fun r : StrictOrdEdge (Rose α) => r.val.1) hp)
    aesop

include hc in
/-- Every finite chain with boundary supported on the base fibre is reconstructed from its actual coordinates. -/
theorem roseCover_chain_reconstruct 
     :
    roseCoverRealizeGeneratorCoordinates f hf (roseCoverGeneratorCoordinates f hf c) = c := by
  apply sub_eq_zero.mp
  apply roseCover_chain_eq_zero_of_boundary_off_base f hf
  · simp_all [roseCoverRealizeGeneratorCoordinates_boundary_off_base]
  · intro e i he
    have h := congrArg (fun z : roseCoverGeneratorEdges f hf →₀ ℤ => z ⟨e, i, he⟩)
      (roseCoverRealizeGeneratorCoordinates_coordinates f hf (roseCoverGeneratorCoordinates f hf c))
    rw [Finsupp.sub_apply]
    exact sub_eq_zero.mpr h

/-- Genuine finite one-cycles are reconstructed from their actual selected incidence coefficients. -/
theorem roseCover_cycle_reconstruct 
    (hc : FiniteChains.Comb.bdry1 (strictOrderCx P) c = 0) :
    roseCoverRealizeGeneratorCoordinates f hf (roseCoverGeneratorCoordinates f hf c) = c := by
  simp_all [roseCover_chain_reconstruct]

/-- For genuine cycles the actual selected coordinate equation is equivalent to chain vanishing. -/
theorem roseCover_cycle_eq_zero_iff_coordinates 
    (hc : FiniteChains.Comb.bdry1 (strictOrderCx P) c = 0) :
    c = 0 ↔ roseCoverGeneratorCoordinates f hf c = 0 := by
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    have hr := roseCover_cycle_reconstruct f hf c hc
    rw [h, map_zero] at hr
    exact hr.symm

end FiniteChains.PresModel
