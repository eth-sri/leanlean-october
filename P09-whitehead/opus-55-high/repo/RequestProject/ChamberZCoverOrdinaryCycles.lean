module

public import RequestProject.ChamberZCoverRetraction
public import RequestProject.PosetCoverConeCycles

@[expose] public section

/-! Genuine finite fillings in actual lifted ordinary chambers. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}

/-- All strict two-cycles of the actual preimage of an ordinary chamber bound there,
even if that preimage has more than one connected component. -/
theorem strict_twoCycle_cover_unmarked_chamber (hf : IsPosetCover f)
    (w : CayGroup A) (hw : ¬ M w)
    (c : StrictOrdTri {p : P // InZChamber w (f p)} →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx {p : P // InZChamber w (f p)}) c = 0) :
    ∃ y : StrictOrdTet {p : P // InZChamber w (f p)} →₀ ℤ,
      strictOrdBoundary3 y = c := by
  let S : Set (Zpos A X M att) := {z | InZChamber w z}
  have hfc := IsPosetCover.restriction f S hf
  let b : S := ⟨zApex (X := X) (att := att) hw,
    inZChamber_zApex (X := X) (att := att) hw⟩
  have hb : ∀ q : S, b ≤ q := fun q => zApex_le hw q.2
  exact strict_twoCycle_cover_lower_cone hfc b hb c hc

end FiniteChains.Davis
