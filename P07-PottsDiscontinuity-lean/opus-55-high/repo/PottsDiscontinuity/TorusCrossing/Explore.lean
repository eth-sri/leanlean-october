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

@[expose] public noncomputable section

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
def faceRow (r : ℤ) : Finset Cell := R.dcells.filter (fun z => z.2 = r)

/-- Odd cells reachable from the row `p₁` by dual-open edges (those inner medial vertices not
in `A`). -/
def expD (p₁ : ℤ) (A : Finset Cell) : Finset Cell :=
  R.dcells.filter (fun z => ∃ p ∈ R.faceRow p₁,
    Relation.ReflTransGen (StepRel dualEnds (R.inner \ A)) p z)

/-- Adjacency of odd cells (through any inner medial vertex) avoiding a set `E`. -/
def AvoidStep (R : Rect) (E : Finset Cell) (x y : Cell) : Prop :=
  x ∉ E ∧ y ∉ E ∧ StepRel dualEnds R.inner x y

section
variable (p₁ p₂ : ℤ) (A : Finset Cell)
/-- Odd cells outside `D₁` joined to the row `p₂` outside `D₁`. -/
def expU  : Finset Cell :=
  R.dcells.filter (fun z => z ∉ R.expD p₁ A ∧ ∃ t ∈ R.faceRow p₂,
    t ∉ R.expD p₁ A ∧ Relation.ReflTransGen (R.AvoidStep (R.expD p₁ A)) t z)

/-- The explored region of odd cells. -/
def expX  : Finset Cell := R.dcells \ R.expU p₁ p₂ A

/-- Explored edges: those with a dual end in the explored region. -/
def expRm  : Finset Cell :=
  R.inner.filter (fun m => (dualEnds m).1 ∈ R.expX p₁ p₂ A ∨ (dualEnds m).2 ∈ R.expX p₁ p₂ A)

/-- Boundary edges: exactly one dual end in `U`. -/
def expBd  : Finset Cell :=
  R.inner.filter (fun m => ((dualEnds m).1 ∈ R.expU p₁ p₂ A) ≠ ((dualEnds m).2 ∈ R.expU p₁ p₂ A))
end

variable {R}

theorem expBd_subset_expRm (p₁ p₂ : ℤ) (A : Finset Cell) : R.expBd p₁ p₂ A ⊆ R.expRm p₁ p₂ A := by
  intro m hm
  unfold expBd at hm
  unfold expRm
  simp_all
  have hmem := R.dData.mem m hm.1
  by_cases h1 : (dualEnds m).1 ∈ R.expU p₁ p₂ A <;> simp_all [expX]

theorem expU_subset_not_expD {p₁ p₂ : ℤ} {A : Finset Cell} {z : Cell} (hz : z ∈ R.expU p₁ p₂ A) :
    z ∉ R.expD p₁ A := by
  simp_all [expU]

section
variable (p₁ p₂ : ℤ) (A : Finset Cell)
/-- Boundary edges are open. -/
theorem expBd_subset  : R.expBd p₁ p₂ A ⊆ A := by
  intro m hm
  by_contra hmA
  obtain ⟨hmi, hdiff⟩ := Finset.mem_filter.1 hm
  have hdual : m ∈ R.inner \ A := by simp_all
  have hmem := R.dData.mem m hmi
  set z₁ := (dualEnds m).1 with hz₁
  set z₂ := (dualEnds m).2 with hz₂
  -- one end is in U, the other in X
  have key : ∀ a b : Cell, (a = z₁ ∧ b = z₂ ∨ a = z₂ ∧ b = z₁) → a ∈ R.expU p₁ p₂ A →
      b ∉ R.expU p₁ p₂ A → b ∈ R.dcells → False := by
    intro a b hab ha hb hbc
    have hstep : StepRel dualEnds (R.inner \ A) a b ∨ StepRel dualEnds (R.inner \ A) b a := by
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨m, hdual, Or.inl rfl⟩
      · exact Or.inl ⟨m, hdual, Or.inr rfl⟩
    by_cases hbD : b ∈ R.expD p₁ A
    · -- b ∈ D₁ forces a ∈ D₁ through the dual-open edge
      apply (expU_subset_not_expD ha)
      obtain ⟨hbc', p, hp, hr⟩ := Finset.mem_filter.1 hbD
      have hac : a ∈ R.dcells := by
        grind
      refine Finset.mem_filter.2 ⟨hac, p, hp, hr.tail ?_⟩
      rcases hstep with h | h
      · exact stepRel_symm h
      omega
    · -- otherwise b is joined to the same row p₂ outside D₁, so b ∈ U
      apply hb
      obtain ⟨hac, haD', t, ht, htD, hr⟩ := Finset.mem_filter.1 ha
      refine Finset.mem_filter.2 ⟨hbc, hbD, t, ht, htD, hr.tail ?_⟩
      refine ⟨haD', hbD, ?_⟩
      rcases hstep with h | h
      · exact stepRel_mono Finset.sdiff_subset h
      · exact stepRel_symm (stepRel_mono Finset.sdiff_subset h)
  by_cases h1 : z₁ ∈ R.expU p₁ p₂ A
  · exact key z₁ z₂ (Or.inl ⟨rfl, rfl⟩) h1 (by simp_all) hmem.2
  grind


theorem expD_subset_expX  : R.expD p₁ A ⊆ R.expX p₁ p₂ A := by
  intro z hz
  have hzc := (Finset.mem_filter.1 hz).1
  grind [expX, expU_subset_not_expD]
end

section
variable {p₁ p₂ : ℤ} {A A' : Finset Cell} (h : R.expD p₁ A = R.expD p₁ A')
include h
theorem expU_congr  :
    R.expU p₁ p₂ A = R.expU p₁ p₂ A' := by
  simp [expU, h]

theorem expX_congr  :
    R.expX p₁ p₂ A = R.expX p₁ p₂ A' := by
  unfold expX; rw [R.expU_congr h]

theorem expRm_congr  :
    R.expRm p₁ p₂ A = R.expRm p₁ p₂ A' := by
  unfold expRm; rw [R.expX_congr h]

theorem expBd_congr  :
    R.expBd p₁ p₂ A = R.expBd p₁ p₂ A' := by
  unfold expBd; rw [R.expU_congr h]
end

theorem rtg_mem_dcells {B : Finset Cell} {p z : Cell} (hp : p ∈ R.dcells)
    (hr : Relation.ReflTransGen (StepRel dualEnds (R.inner \ B)) p z) : z ∈ R.dcells := by
  induction hr with
  | refl => omega
  | @tail b c _ hstep ih =>
    obtain ⟨m, hm, hmz⟩ := hstep
    have hmem := R.dData.mem m ((Finset.mem_sdiff.1 hm).1)
    grind

theorem mem_expD {p₁ : ℤ} {B : Finset Cell} {z : Cell} :
    z ∈ R.expD p₁ B ↔ z ∈ R.dcells ∧ ∃ p ∈ R.faceRow p₁,
      Relation.ReflTransGen (StepRel dualEnds (R.inner \ B)) p z := by
  simp [expD]

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
    grind [expRm, expD_subset_expX]
  have hends : ∀ {m b c : Cell}, (dualEnds m = (b, c) ∨ dualEnds m = (c, b)) →
      ((dualEnds m).1 = b ∨ (dualEnds m).2 = b) := by
    grind
  -- transfer of reachability in both directions
  have hT1 : ∀ p ∈ R.faceRow p₁, ∀ z, Relation.ReflTransGen (StepRel dualEnds (R.inner \ A')) p z →
      Relation.ReflTransGen (StepRel dualEnds (R.inner \ A)) p z := by
    intro p hp z hr
    induction hr with
    | refl => rfl
    | @tail b c _ hstep ih =>
      obtain ⟨m, hm, hmz⟩ := hstep
      obtain ⟨hmi, hmA'⟩ := Finset.mem_sdiff.1 hm
      have hmRm := hRm b m (R.mem_expD.2 ⟨R.rtg_mem_dcells (Finset.mem_filter.1 hp).1 ih, p, hp, ih⟩) hmi (hends hmz)
      exact ih.tail ⟨m, Finset.mem_sdiff.2 ⟨hmi, (by simp_all)⟩, hmz⟩
  have hT2 : ∀ p ∈ R.faceRow p₁, ∀ z, Relation.ReflTransGen (StepRel dualEnds (R.inner \ A)) p z →
      Relation.ReflTransGen (StepRel dualEnds (R.inner \ A')) p z := by
    intro p hp z hr
    induction hr with
    | refl => rfl
    | @tail b c hbc hstep ih =>
      obtain ⟨m, hm, hmz⟩ := hstep
      obtain ⟨hmi, hmA⟩ := Finset.mem_sdiff.1 hm
      have hmRm := hRm b m (R.mem_expD.2 ⟨R.rtg_mem_dcells (Finset.mem_filter.1 hp).1 hbc, p, hp, hbc⟩) hmi (hends hmz)
      exact ih.tail ⟨m, Finset.mem_sdiff.2 ⟨hmi, (by simp_all)⟩, hmz⟩
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨hzc, p, hp, hr⟩ := R.mem_expD.1 hz
    exact R.mem_expD.2 ⟨hzc, p, hp, hT1 p hp z hr⟩
  · intro z hz
    obtain ⟨hzc, p, hp, hr⟩ := R.mem_expD.1 hz
    exact R.mem_expD.2 ⟨hzc, p, hp, hT2 p hp z hr⟩

end Rect

end PottsDiscontinuity.TorusCrossing
