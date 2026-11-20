module

public import PottsDiscontinuity.TorusCrossing.Planar

/-!
# Exploration of the dual cluster of a boundary row

For a board `R`, an open edge set `A ⊆ R.inner`, and a row `p₁` of faces, let `D₁` be the set of
odd cells reachable from the row `p₁` through dual-open edges.  Let `U` be the set of odd cells
outside `D₁` which are joined to the opposite row `p₂` through odd cells outside `D₁` (any
adjacency, open or closed).  The *explored* region is the complement `X` of `U`, the explored
edges are those having a dual end in `X`, and the *boundary* consists of the edges separating `U`
from `X`.  The boundary edges are open, and the exploration is a stopping set: it is determined by
the states of the explored edges alone.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

theorem stepRel_mono {ends : Cell → Cell × Cell} {A B : Finset Cell} (h : A ⊆ B) {x y : Cell}
    (hxy : StepRel ends A x y) : StepRel ends B x y := by
  obtain ⟨m, hm, hmx⟩ := hxy
  exact ⟨m, h hm, hmx⟩

namespace Rect

variable (R : Rect)

/-- Odd cells of the board lying in a given row. -/
noncomputable def faceRow (r : ℤ) : Finset Cell := R.dcells.filter (fun z => z.2 = r)

/-- Odd cells reachable from the row `p₁` by dual-open edges (those inner medial vertices not
in `A`). -/
noncomputable def expD (p₁ : ℤ) (A : Finset Cell) : Finset Cell :=
  R.dcells.filter (fun z => ∃ p ∈ R.faceRow p₁,
    Relation.ReflTransGen (StepRel dualEnds (R.inner \ A)) p z)

/-- Adjacency of odd cells (through any inner medial vertex) avoiding a set `E`. -/
def AvoidStep (R : Rect) (E : Finset Cell) (x y : Cell) : Prop :=
  x ∉ E ∧ y ∉ E ∧ StepRel dualEnds R.inner x y

section

variable (p₁ p₂ : ℤ) (A : Finset Cell)

/-- Odd cells outside `D₁` joined to the row `p₂` outside `D₁`. -/
noncomputable def expU : Finset Cell :=
  R.dcells.filter (fun z => z ∉ R.expD p₁ A ∧ ∃ t ∈ R.faceRow p₂,
    t ∉ R.expD p₁ A ∧ Relation.ReflTransGen (R.AvoidStep (R.expD p₁ A)) t z)

/-- The explored region of odd cells. -/
noncomputable def expX : Finset Cell := R.dcells \ R.expU p₁ p₂ A

/-- Explored edges: those with a dual end in the explored region. -/
noncomputable def expRm : Finset Cell :=
  R.inner.filter (fun m => (dualEnds m).1 ∈ R.expX p₁ p₂ A ∨ (dualEnds m).2 ∈ R.expX p₁ p₂ A)

/-- Boundary edges: exactly one dual end in `U`. -/
noncomputable def expBd : Finset Cell :=
  R.inner.filter (fun m => ((dualEnds m).1 ∈ R.expU p₁ p₂ A) ≠ ((dualEnds m).2 ∈ R.expU p₁ p₂ A))

end

variable {R}

theorem stepRel_mem_dcells {y w : Cell} (h : StepRel dualEnds R.inner w y) : y ∈ R.dcells := by
  obtain ⟨e, he, h | h⟩ := h
  · simpa [h] using (R.dData.mem e he).2
  · simpa [h] using (R.dData.mem e he).1

theorem mem_expD {p₁ : ℤ} {B : Finset Cell} {z : Cell} :
    z ∈ R.expD p₁ B ↔ z ∈ R.dcells ∧ ∃ p ∈ R.faceRow p₁,
      Relation.ReflTransGen (StepRel dualEnds (R.inner \ B)) p z := by
  unfold expD; exact Finset.mem_filter

theorem mem_expU {p₁ p₂ : ℤ} {A : Finset Cell} {z : Cell} :
    z ∈ R.expU p₁ p₂ A ↔ z ∈ R.dcells ∧ z ∉ R.expD p₁ A ∧ ∃ t ∈ R.faceRow p₂,
      t ∉ R.expD p₁ A ∧ Relation.ReflTransGen (R.AvoidStep (R.expD p₁ A)) t z := by
  unfold expU; exact Finset.mem_filter

theorem expD_step {p₁ : ℤ} {A : Finset Cell} {x y : Cell} (hx : x ∈ R.expD p₁ A)
    (h : StepRel dualEnds (R.inner \ A) x y) : y ∈ R.expD p₁ A := by
  obtain ⟨_, p, hp, hr⟩ := R.mem_expD.mp hx
  exact R.mem_expD.mpr ⟨R.stepRel_mem_dcells (stepRel_mono Finset.sdiff_subset h), p, hp, hr.tail h⟩

theorem expU_step {p₁ p₂ : ℤ} {A : Finset Cell} {x y : Cell} (hx : x ∈ R.expU p₁ p₂ A)
    (h : R.AvoidStep (R.expD p₁ A) x y) : y ∈ R.expU p₁ p₂ A := by
  obtain ⟨_, _, p, hp, hpD, hr⟩ := R.mem_expU.mp hx
  exact R.mem_expU.mpr ⟨R.stepRel_mem_dcells h.2.2, h.2.1, p, hp, hpD, hr.tail h⟩

theorem expU_subset_not_expD {p₁ p₂ : ℤ} {A : Finset Cell} {z : Cell} (hz : z ∈ R.expU p₁ p₂ A) :
    z ∉ R.expD p₁ A := (R.mem_expU.mp hz).2.1

theorem expBd_subset_expRm (p₁ p₂ : ℤ) (A : Finset Cell) : R.expBd p₁ p₂ A ⊆ R.expRm p₁ p₂ A := by
  intro m hm
  obtain ⟨hmi, hd⟩ := Finset.mem_filter.mp hm
  obtain ⟨h₁, h₂⟩ := R.dData.mem m hmi
  rw [expRm, Finset.mem_filter, expX]
  exact ⟨hmi, by grind⟩

/-- Boundary edges are open. -/
theorem expBd_subset (p₁ p₂ : ℤ) (A : Finset Cell) : R.expBd p₁ p₂ A ⊆ A := by
  intro m hm
  obtain ⟨hmi, hd⟩ := Finset.mem_filter.mp hm
  by_contra hA
  have hm' : m ∈ R.inner \ A := Finset.mem_sdiff.mpr ⟨hmi, hA⟩
  have step {x y : Cell} (hs : StepRel dualEnds (R.inner \ A) x y) (hx : x ∈ R.expU p₁ p₂ A) :
      y ∈ R.expU p₁ p₂ A :=
    R.expU_step hx ⟨expU_subset_not_expD hx,
      fun hy => expU_subset_not_expD hx (R.expD_step hy (stepRel_symm hs)),
      stepRel_mono Finset.sdiff_subset hs⟩
  exact hd (propext ⟨step ⟨m, hm', Or.inl rfl⟩, step ⟨m, hm', Or.inr rfl⟩⟩)

theorem expD_subset_expX (p₁ p₂ : ℤ) (A : Finset Cell) : R.expD p₁ A ⊆ R.expX p₁ p₂ A :=
  fun _ hz => Finset.mem_sdiff.mpr ⟨(R.mem_expD.mp hz).1, fun hU => expU_subset_not_expD hU hz⟩

theorem expU_congr {p₁ p₂ : ℤ} {A A' : Finset Cell} (h : R.expD p₁ A = R.expD p₁ A') :
    R.expU p₁ p₂ A = R.expU p₁ p₂ A' := by
  unfold expU; rw [h]

theorem expX_congr {p₁ p₂ : ℤ} {A A' : Finset Cell} (h : R.expD p₁ A = R.expD p₁ A') :
    R.expX p₁ p₂ A = R.expX p₁ p₂ A' := by
  unfold expX; rw [R.expU_congr h]

theorem expRm_congr {p₁ p₂ : ℤ} {A A' : Finset Cell} (h : R.expD p₁ A = R.expD p₁ A') :
    R.expRm p₁ p₂ A = R.expRm p₁ p₂ A' := by
  unfold expRm; rw [R.expX_congr h]

theorem rtg_mem_dcells {B : Finset Cell} {p z : Cell} (hp : p ∈ R.dcells)
    (hr : Relation.ReflTransGen (StepRel dualEnds (R.inner \ B)) p z) : z ∈ R.dcells := by
  induction hr with
  | refl => exact hp
  | tail _ h _ => exact R.stepRel_mem_dcells (stepRel_mono Finset.sdiff_subset h)

/-- **Stopping property.**  The explored dual cluster is determined by the states of the explored
edges: two configurations agreeing on the explored edges have the same exploration. -/
theorem expD_stop (p₁ p₂ : ℤ) {A A' : Finset Cell}
    (h : A' ∩ R.expRm p₁ p₂ A = A ∩ R.expRm p₁ p₂ A) :
    R.expD p₁ A' = R.expD p₁ A := by
  have hagree : ∀ m ∈ R.expRm p₁ p₂ A, m ∈ A' ↔ m ∈ A := by
    intro m hm
    have := congrArg (fun S => m ∈ S) h
    grind
  have hRm : ∀ y m : Cell, y ∈ R.expD p₁ A → m ∈ R.inner →
      ((dualEnds m).1 = y ∨ (dualEnds m).2 = y) → m ∈ R.expRm p₁ p₂ A := by
    intro y m hy hm hend
    have hx := expD_subset_expX p₁ p₂ A hy
    rw [expRm, Finset.mem_filter]
    exact ⟨hm, by grind⟩
  have transport {B C : Finset Cell} (hBC : A = B ∨ A = C)
      (hagree' : ∀ e ∈ R.expRm p₁ p₂ A, e ∈ B ↔ e ∈ C) {p z : Cell}
      (hp : p ∈ R.faceRow p₁) (hr : Relation.ReflTransGen (StepRel dualEnds (R.inner \ B)) p z) :
      Relation.ReflTransGen (StepRel dualEnds (R.inner \ C)) p z := by
    induction hr with
    | refl => rfl
    | @tail b c hpre hstep ih =>
      have hpre' : Relation.ReflTransGen (StepRel dualEnds (R.inner \ A)) p b := by
        rcases hBC with rfl | rfl <;> assumption
      have hbD := R.mem_expD.mpr ⟨R.rtg_mem_dcells (Finset.mem_filter.mp hp).1 hpre', p, hp, hpre'⟩
      obtain ⟨m, hm, hmz⟩ := hstep
      obtain ⟨hmi, hmB⟩ := Finset.mem_sdiff.mp hm
      exact ih.tail ⟨m, Finset.mem_sdiff.mpr ⟨hmi, mt (hagree' m (hRm b m hbD hmi (by grind))).mpr hmB⟩, hmz⟩
  ext z
  simp only [mem_expD]
  constructor <;> rintro ⟨hzc, p, hp, hr⟩
  · exact ⟨hzc, p, hp, transport (Or.inr rfl) hagree hp hr⟩
  · exact ⟨hzc, p, hp, transport (Or.inl rfl) (fun e he => (hagree e he).symm) hp hr⟩

end Rect

end PottsDiscontinuity.TorusCrossing
