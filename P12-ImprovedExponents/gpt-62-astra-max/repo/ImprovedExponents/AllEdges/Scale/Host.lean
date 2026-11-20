module

public import ImprovedExponents.AllEdges.Scale.Run

@[expose] public section
namespace ImprovedExponents.AllEdges.Scale
open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec3

theorem Ctx.body_spec {P S p T r lim d x μ fr} (C : Ctx P S p T r lim d x μ fr) :
    Ends lim (P++S) d (body p) ⟨frame [x.n,x.U,x.a,x.b,x.c,fr],μ⟩ (time T x.n x.U)
      fun σ' => Seg σ'.mem x.c (minPlusList x.n x.A x.B) ∧ KeptBut μ σ'.mem fr x.c (area x) := by
  have places := C.places
  have budget : init.blockCost + (20*aeLevels x.U+10) + 170*(area x+1) +
      (aeLevels x.U * (rTime T x + 8) + 6) + (20*area x+30) ≤ time T x.n x.U := by
    simp [init,time,rTime,qTime,area]; ring_nf; omega
  refine Ends.mono ?_ budget (fun _ => id)
  unfold body
  refine Ends.pieceThen (init_spec C) ?_ (by omega); rintro _ rfl
  refine Ends.pieceThen (powers_spec C) ?_ (by omega); rintro _ rfl
  refine Ends.pieceThen C.prep_spec ?_ (by omega); rintro _ ⟨_,_,rfl,hm⟩
  refine Ends.pieceThen (C.rounds_spec hm) ?_ (by omega); rintro _ ⟨v,ν,rfl,_,_,⟨L,a,ls⟩,keep⟩
  have len := a.len
  refine Ends.callTo (C.map ls (a.bounded C.pre) 1 (-(2*(x.U:ℤ))) x.c) ?_
    (ha := by light_side [len]) (hT := by simp only [Expr.cost,List.map_cons,
      List.map_nil,List.sum_cons,List.sum_nil]; omega)
  rintro _ _ ⟨ds,out⟩
  exact ⟨finish C.pre a ▸ ds,by light_keep⟩

/-- Prefix refinement is a uniform host: append four array passes and the loop to any solver. -/
theorem host : IsHost aeTask mpTask time need := by
  constructor
  · intro P ae T r sol
    let p : Procs := ⟨ae,P.length,P.length+1,P.length+2,P.length+3⟩
    refine ⟨[affineBody,transposeBody,prefDownBody,bumpBody,body p],P.length+4,body p,by simp,
      fun S lim d x μ fr pre ok => ?_⟩
    rw [List.append_assoc]
    exact Ctx.body_spec (p:=p) ⟨sol,by simp [p],by simp [p],by simp [p],by simp [p],pre,ok⟩
  · intro r h; unfold need; poly_need [h.word,h.cells,h.depth]

end ImprovedExponents.AllEdges.Scale
