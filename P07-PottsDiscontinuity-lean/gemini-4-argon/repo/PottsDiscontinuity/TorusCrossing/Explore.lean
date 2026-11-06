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

/-- Odd cells outside `D₁` joined to the row `p₂` outside `D₁`. -/
noncomputable def expU (p₁ p₂ : ℤ) (A : Finset Cell) : Finset Cell :=
  R.dcells.filter (fun z => z ∉ R.expD p₁ A ∧ ∃ t ∈ R.faceRow p₂,
    t ∉ R.expD p₁ A ∧ Relation.ReflTransGen (R.AvoidStep (R.expD p₁ A)) t z)

/-- The explored region of odd cells. -/
noncomputable def expX (p₁ p₂ : ℤ) (A : Finset Cell) : Finset Cell := R.dcells \ R.expU p₁ p₂ A

/-- Explored edges: those with a dual end in the explored region. -/
noncomputable def expRm (p₁ p₂ : ℤ) (A : Finset Cell) : Finset Cell :=
  R.inner.filter (fun m => (dualEnds m).1 ∈ R.expX p₁ p₂ A ∨ (dualEnds m).2 ∈ R.expX p₁ p₂ A)

/-- Boundary edges: exactly one dual end in `U`. -/
noncomputable def expBd (p₁ p₂ : ℤ) (A : Finset Cell) : Finset Cell :=
  R.inner.filter (fun m => ((dualEnds m).1 ∈ R.expU p₁ p₂ A) ≠ ((dualEnds m).2 ∈ R.expU p₁ p₂ A))

variable {R}

theorem expBd_subset_expRm (p₁ p₂ : ℤ) (A : Finset Cell) : R.expBd p₁ p₂ A ⊆ R.expRm p₁ p₂ A := by
  intro m hm
  rw [expBd, Finset.mem_filter] at hm
  rw [expRm, Finset.mem_filter]
  have hmem := R.dData.mem m hm.1
  by_cases h1 : (dualEnds m).1 ∈ R.expU p₁ p₂ A
  · exact ⟨hm.1, Or.inr (Finset.mem_sdiff.2 ⟨hmem.2, fun h => hm.2 (by simp [h1, h])⟩)⟩
  · exact ⟨hm.1, Or.inl (Finset.mem_sdiff.2 ⟨hmem.1, h1⟩)⟩

theorem expU_subset_not_expD {p₁ p₂ : ℤ} {A : Finset Cell} {z : Cell} (hz : z ∈ R.expU p₁ p₂ A) :
    z ∉ R.expD p₁ A :=
  (Finset.mem_filter.1 hz).2.1

theorem expBd_subset (p₁ p₂ : ℤ) (A : Finset Cell) : R.expBd p₁ p₂ A ⊆ A := by
  intro m hm
  by_contra hmA
  obtain ⟨hmi, hdiff⟩ := Finset.mem_filter.1 hm
  have hdual : m ∈ R.inner \ A := Finset.mem_sdiff.2 ⟨hmi, hmA⟩
  have hmem := R.dData.mem m hmi
  set z₁ := (dualEnds m).1
  set z₂ := (dualEnds m).2
  have key (a b : Cell) (hab : a = z₁ ∧ b = z₂ ∨ a = z₂ ∧ b = z₁) (ha : a ∈ R.expU p₁ p₂ A)
      (hb : b ∉ R.expU p₁ p₂ A) (hbc : b ∈ R.dcells) : False := by
    have hstep : StepRel dualEnds (R.inner \ A) a b :=
      ⟨m, hdual, hab.imp (fun ⟨h1, h2⟩ => Prod.ext h1.symm h2.symm)
        (fun ⟨h1, h2⟩ => Prod.ext h2.symm h1.symm)⟩
    by_cases hbD : b ∈ R.expD p₁ A
    · obtain ⟨_, p, hp, hr⟩ := Finset.mem_filter.1 hbD
      have hac : a ∈ R.dcells := by rcases hab with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> [exact hmem.1; exact hmem.2]
      exact expU_subset_not_expD ha (Finset.mem_filter.2 ⟨hac, p, hp, hr.tail (stepRel_symm hstep)⟩)
    · obtain ⟨_, haD', t, ht, htD, hr⟩ := Finset.mem_filter.1 ha
      exact hb (Finset.mem_filter.2 ⟨hbc, hbD, t, ht, htD,
        hr.tail ⟨haD', hbD, stepRel_mono Finset.sdiff_subset hstep⟩⟩)
  by_cases h1 : z₁ ∈ R.expU p₁ p₂ A
  · exact key z₁ z₂ (Or.inl ⟨rfl, rfl⟩) h1 (fun h => hdiff (by simp [h1, h])) hmem.2
  · exact key z₂ z₁ (Or.inr ⟨rfl, rfl⟩) (by by_contra h2; exact hdiff (by simp [h1, h2])) h1 hmem.1

theorem expD_subset_expX (p₁ p₂ : ℤ) (A : Finset Cell) : R.expD p₁ A ⊆ R.expX p₁ p₂ A :=
  fun _ hz => Finset.mem_sdiff.2 ⟨(Finset.mem_filter.1 hz).1, fun hU => expU_subset_not_expD hU hz⟩

theorem expU_congr {p₁ p₂ : ℤ} {A A' : Finset Cell} (h : R.expD p₁ A = R.expD p₁ A') :
    R.expU p₁ p₂ A = R.expU p₁ p₂ A' := by
  unfold expU; rw [h]

theorem expX_congr {p₁ p₂ : ℤ} {A A' : Finset Cell} (h : R.expD p₁ A = R.expD p₁ A') :
    R.expX p₁ p₂ A = R.expX p₁ p₂ A' := by
  unfold expX; rw [R.expU_congr h]

theorem expRm_congr {p₁ p₂ : ℤ} {A A' : Finset Cell} (h : R.expD p₁ A = R.expD p₁ A') :
    R.expRm p₁ p₂ A = R.expRm p₁ p₂ A' := by
  unfold expRm; rw [R.expX_congr h]

theorem expBd_congr {p₁ p₂ : ℤ} {A A' : Finset Cell} (h : R.expD p₁ A = R.expD p₁ A') :
    R.expBd p₁ p₂ A = R.expBd p₁ p₂ A' := by
  unfold expBd; rw [R.expU_congr h]

theorem rtg_mem_dcells {B : Finset Cell} {p z : Cell} (hp : p ∈ R.dcells)
    (hr : Relation.ReflTransGen (StepRel dualEnds (R.inner \ B)) p z) : z ∈ R.dcells := by
  induction hr with
  | refl => exact hp
  | @tail b c _ hstep _ =>
    obtain ⟨m, hm, e | e⟩ := hstep <;> have hmem := R.dData.mem m (Finset.mem_sdiff.1 hm).1
    · simpa [e] using hmem.2
    · simpa [e] using hmem.1

theorem mem_expD {p₁ : ℤ} {B : Finset Cell} {z : Cell} :
    z ∈ R.expD p₁ B ↔ z ∈ R.dcells ∧ ∃ p ∈ R.faceRow p₁,
      Relation.ReflTransGen (StepRel dualEnds (R.inner \ B)) p z :=
  Finset.mem_filter

theorem expD_stop (p₁ p₂ : ℤ) {A A' : Finset Cell}
    (h : A' ∩ R.expRm p₁ p₂ A = A ∩ R.expRm p₁ p₂ A) :
    R.expD p₁ A' = R.expD p₁ A := by
  have hagree (m : Cell) (hm : m ∈ R.expRm p₁ p₂ A) : m ∈ A' ↔ m ∈ A := by
    simpa [hm] using congrArg (m ∈ ·) h
  have hRm {b c m : Cell} (hbD : b ∈ R.expD p₁ A) (hm : m ∈ R.inner)
      (hmz : dualEnds m = (b, c) ∨ dualEnds m = (c, b)) : m ∈ R.expRm p₁ p₂ A :=
    Finset.mem_filter.2 ⟨hm, hmz.imp
      (fun e => by rw [congrArg Prod.fst e]; exact expD_subset_expX p₁ p₂ A hbD)
      (fun e => by rw [congrArg Prod.snd e]; exact expD_subset_expX p₁ p₂ A hbD)⟩
  have hT1 (p : Cell) (hp : p ∈ R.faceRow p₁) :
      ∀ z, Relation.ReflTransGen (StepRel dualEnds (R.inner \ A')) p z →
        Relation.ReflTransGen (StepRel dualEnds (R.inner \ A)) p z := by
    intro z hr
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hstep ih =>
      have hbD : b ∈ R.expD p₁ A :=
        R.mem_expD.2 ⟨R.rtg_mem_dcells (Finset.mem_filter.1 hp).1 ih, p, hp, ih⟩
      obtain ⟨m, hm, hmz⟩ := hstep
      obtain ⟨hmi, hmA'⟩ := Finset.mem_sdiff.1 hm
      exact ih.tail ⟨m, Finset.mem_sdiff.2 ⟨hmi, fun hmA => hmA' ((hagree m (hRm hbD hmi hmz)).2 hmA)⟩, hmz⟩
  have hT2 (p : Cell) (hp : p ∈ R.faceRow p₁) :
      ∀ z, Relation.ReflTransGen (StepRel dualEnds (R.inner \ A)) p z →
        Relation.ReflTransGen (StepRel dualEnds (R.inner \ A')) p z := by
    intro z hr
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hbc hstep ih =>
      have hbD : b ∈ R.expD p₁ A :=
        R.mem_expD.2 ⟨R.rtg_mem_dcells (Finset.mem_filter.1 hp).1 hbc, p, hp, hbc⟩
      obtain ⟨m, hm, hmz⟩ := hstep
      obtain ⟨hmi, hmA⟩ := Finset.mem_sdiff.1 hm
      exact ih.tail ⟨m, Finset.mem_sdiff.2 ⟨hmi, fun hmA' => hmA ((hagree m (hRm hbD hmi hmz)).1 hmA')⟩, hmz⟩
  exact Finset.Subset.antisymm
    (fun z hz => by obtain ⟨hzc, p, hp, hr⟩ := R.mem_expD.1 hz; exact R.mem_expD.2 ⟨hzc, p, hp, hT1 p hp z hr⟩)
    (fun z hz => by obtain ⟨hzc, p, hp, hr⟩ := R.mem_expD.1 hz; exact R.mem_expD.2 ⟨hzc, p, hp, hT2 p hp z hr⟩)

end Rect

end PottsDiscontinuity.TorusCrossing
