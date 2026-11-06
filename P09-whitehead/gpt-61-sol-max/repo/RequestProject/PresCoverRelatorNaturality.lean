import Mathlib.Tactic

import RequestProject.PresCoverConeCircleProjection
import RequestProject.PosetCoverTopTriangle

namespace FiniteChains.Comb
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
theorem strictOrderCxMap_onF_injective (k : P → Q) (hm : StrictMono k)
    (hi : Function.Injective k) : Function.Injective (strictOrderCxMap k hm).onF := by
  intro t s he
  apply Subtype.ext
  apply Prod.ext
  · exact hi (congrArg (fun r : StrictOrdTri Q => r.1.1) he)
  · apply Prod.ext
    · exact hi (congrArg (fun r : StrictOrdTri Q => r.1.2.1) he)
    · exact hi (congrArg (fun r : StrictOrdTri Q => r.1.2.2) he)
end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb
variable {α J P Q : Type u} [PartialOrder P] [PartialOrder Q]
  (w : J → List (α × Bool)) (f : P → PresPos w) (hf : IsPosetCover f)
  (hpos : ∀ j, 0 < (w j).length)

/-- The distinguished coordinate triangle is the unique triangle over its actual
first incidence with its actual apex. -/
theorem presCoverRelatorTriangle_unique (p : PresCoverRelator w f) (t : StrictOrdTri P)
    (ht : (strictOrderCxMap f hf.strictMono).onF t = presRelatorFirstTriangle w hpos p.1.2)
    (hv : t.1.2.2 = p.1.1) : t = presCoverRelatorTriangle w f hf hpos p := by
  let r := presCoverRelatorTriangle w f hf hpos p
  have he  :=
    ht.trans (presCoverRelatorTriangle_projection w f hf hpos p).symm
  have hfa := congrArg (fun s : StrictOrdTri (PresPos w) => s.1.1) he
  have hfb := congrArg (fun s : StrictOrdTri (PresPos w) => s.1.2.1) he
  have ha  := hf.down_inj (a := p.1.1)
    (hv ▸ (t.2.1.le.trans t.2.2.le)) (r.2.1.le.trans r.2.2.le) hfa
  have hb  := hf.down_inj (a := p.1.1) (hv ▸ t.2.2.le) r.2.2.le hfb
  exact Subtype.ext (Prod.ext ha (Prod.ext hb hv))

end FiniteChains.PresModel
