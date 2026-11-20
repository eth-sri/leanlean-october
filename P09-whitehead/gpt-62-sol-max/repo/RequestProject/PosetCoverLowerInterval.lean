module

public import RequestProject.PosetCoverUpTransform
public import RequestProject.StrictTopLinkChains

@[expose] public section

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
section Above
variable {R : Type u} [PartialOrder R]

def StrictAbove (v : R) := {p : R // v < p}

instance (v : R) : PartialOrder (StrictAbove v) := Subtype.partialOrder _

end Above

def strictBelowCongr {a b : P} (h : a = b) : StrictBelow a ≃o StrictBelow b := by
  cases h
  exact OrderIso.refl _

namespace IsPosetCover
variable (hf : IsPosetCover f)
include hf

noncomputable def upperIntervalLift (v : P) (q : StrictAbove (f v)) :
    StrictAbove v := ⟨(hf.liftUp v q.1 q.2.le).1, hf.liftUp_strict v q.1 q.2⟩

theorem upperIntervalLift_projection (v : P) (q : StrictAbove (f v)) :
    f (hf.upperIntervalLift v q).1 = q.1 := (hf.liftUp v q.1 q.2.le).2.2

/-- An actual cover identifies each upper link with the actual upper link in
the base.  Distinct pole lifts are not identified by this construction. -/
noncomputable def upperIntervalOrderIso (v : P) :
    StrictAbove v ≃o StrictAbove (f v) where
  toFun p := ⟨f p.1, hf.strictMono p.2⟩
  invFun := hf.upperIntervalLift v
  left_inv p := Subtype.ext (hf.up_inj (hf.upperIntervalLift v _).2.le p.2.le
    (hf.upperIntervalLift_projection v _))
  right_inv q := Subtype.ext (hf.upperIntervalLift_projection v q)
  map_rel_iff' {a b} := ⟨fun h => hf.le_of_le_above a.2.le b.2.le h,
    fun h => hf.mono h⟩

/-- Lower links are the upper links of the dual orders. -/
noncomputable def lowerIntervalOrderIso (v : P) : StrictBelow v ≃o StrictBelow (f v) := by
  let e : StrictAbove (R := Pᵒᵈ) (OrderDual.toDual v) ≃o
      StrictAbove (R := Qᵒᵈ) (OrderDual.toDual (f v)) := hf.dual.upperIntervalOrderIso v
  exact e.dual

noncomputable def lowerIntervalLift (v : P) (q : StrictBelow (f v)) : StrictBelow v :=
  hf.dual.upperIntervalLift v q

theorem lowerIntervalLift_projection (v : P) (q : StrictBelow (f v)) :
    f (hf.lowerIntervalLift v q).1 = q.1 := hf.dual.upperIntervalLift_projection v q

end IsPosetCover
end FiniteChains.Comb
