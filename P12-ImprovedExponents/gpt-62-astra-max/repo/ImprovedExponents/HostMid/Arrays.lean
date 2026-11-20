module

public import ImprovedExponents.HostMid.PrimeStage

@[expose] public section

/-!
# The variant host: the arrays and the call of the loop

The third part of the host (the table of doubles, the residues, the classes, the chunks, and the
loop over the instances) has upstream's text `et17Tables`.  This file proves its specification for
the data `hostData'` of the variant, whose inner dimension is `midSize D g`: upstream's facts about
the third part are generic in the data, so only the two places that name the data of a run are
proved again (`ready_of'`, `et17Tables_spec'`).
-/

namespace ImprovedExponents.HostMid

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- What the third part needs holds for the data of a run of the variant. -/
theorem ready_of' {lim} {d} {x} {μ} {fr}
    {need} {D g a b} (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt' a b need x.n x.U D g).Ok lim fr d) :
    Et17.Ready lim d x (hostData' x D g) μ fr := by
  have hok0 : (hostNeedAt a b (fun ps => need (midArgs (fun _ => g) ps)) x.n x.U D g).Ok lim fr d :=
    hok
  have hr := Et17.ready_of hpre hbig hok0
  have htop := aFr_le' (x := x) (g := g) hbig.sixteen_le fr
  have hcells := hok.cells
  simp [hostNeedAt'] at hcells
  exact { hr with top := by omega }

end ImprovedExponents.HostMid
