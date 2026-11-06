import RequestProject.ChamberZCellular
import RequestProject.PosetCoverDownTransform
import RequestProject.PosetCoverRestriction
import RequestProject.OrderUniversalPosetCover


/-! The actual marked-chamber retraction on covering posets. -/
namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}

/-- The actual preimage of a marked chamber in a poset covering is acyclic relative
to the actual preimage of the inserted base. The retraction is constructed by unique
downward interval lifts of the geometric chamber retraction. -/
theorem acyclicRelIn_cover_marked_chamber [Nonempty X] (hf : IsPosetCover f)
    w (hw : M w) :
    AcyclicRelIn (fun p => InZChamber w (f p)) (fun p => InZBase (f p)) := by
  let S : Set (Zpos A X M att) := {z | InZChamber w z}
  let fc := posetCoverRestriction f S
  have hfc := IsPosetCover.restriction f S hf
  let g := zChamberRetr (att := att) hw
  have hgle : ∀ q, g q ≤ q := zChamberRetr_le hw
  let ρ := hfc.downTransform g hgle
  have hmono := hfc.downTransform_monotone g (zChamberRetr_monotone hw) hgle
  have hρle := hfc.downTransform_le g hgle
  have hbase : ∀ q, InZBase (f (ρ q).1) := by
    intro q
    have he := congrArg Subtype.val (hfc.downTransform_spec g hgle q).2
    cases' zChamberRetr_mem hw (fc q) with x hx
    have hb : InZBase (g (fc q)).1 := by
      rw [hx]
      trivial
    change f (ρ q).1 = (g (fc q)).1 at he
    simp_all
  have hne : ∃ p : P, InZChamber w (f p) := by
    let x : X := Classical.choice inferInstance
    cases' hf.surj (zNew (att := att) ⟨w, hw⟩ x) with p hp
    refine ⟨p, ?_⟩
    aesop
  exact acyclicRelIn_of_retraction hne ρ hmono hρle hbase
