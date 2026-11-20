module

public import RequestProject.ChamberZCoverIntersectionCycles
public import RequestProject.OrderNervePositiveFillings
public import RequestProject.NerveDegreeTransfer

@[expose] public section

/-! Local degree-two generation and degree-one intersection fillings on actual covers. -/
namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}

section

variable (hf : IsPosetCover f) (w : CayGroup A)
include hf

omit [Fintype V] in
theorem fillsDegreeIn_cover_unmarked_chamber (hw : ¬ M w) :
    FillsDegreeIn (fun p : P => InZChamber w (f p)) 3 := by
  have hne : ∃ p : P, InZChamber w (f p) := by
    obtain ⟨p, hp⟩ := hf.surj (zApex (X := X) (att := att) hw)
    grind [inZChamber_zApex]
  apply fillsDegreeIn_of_subtype hne
  simp_all [nerve_twoCycle_filling_of_strict, strict_twoCycle_cover_unmarked_chamber]

theorem fillsDegreeIn_cover_attaching_intersection (hw : w ≠ 1) :
    FillsDegreeIn (fun p : P => ZJSet w (f p)) 2 := by
  have hne : ∃ p : P, ZJSet w (f p) := by
    obtain ⟨p, hp⟩ := hf.surj ((zJSetOrderIso (A := A) (X := X) (M := M) (att := att) w).symm (interTop hw)).1
    grind
  apply fillsDegreeIn_of_subtype hne
  simp_all [nerve_oneCycle_filling_of_strict, strict_oneCycle_cover_attaching_intersection]

end

omit [Fintype V] in
theorem generatesDegreeIn_cover_chamber [Nonempty X] (hf : IsPosetCover f)
    (w : CayGroup A) :
    GeneratesDegreeIn (fun p : P => InZChamber w (f p))
      (fun p => InZBase (f p)) 3 := by
  classical
  by_cases hw : M w
  · solve_by_elim [generatesDegreeIn_of_acyclicRelIn, acyclicRelIn_cover_marked_chamber]
  · solve_by_elim [generatesDegreeIn_of_fillsDegreeIn, fillsDegreeIn_cover_unmarked_chamber]

end FiniteChains.Davis
