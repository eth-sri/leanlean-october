module

public import Chazelle.Core.SpecMerge
public import Chazelle.RewriteTactics

/-!
# WP-F fusion assembly, part 2: the fused family as a set of shots

The fused family `J.fusion S₁ S₂ ∪ glueChords J` is the set of chords of `C` shot from a set of
query points with directions (`fused_eq_shots`):

* the ends of the chords of `S₁ ∪ S₂` along the chords (`endQ`);
* the shared vertex, both directions (`vtxQ J.m₁`);
* the tops of `C₁` and `C₂`, both directions (`vtxQ` at `topIdxs`);
* the cap origin in the cap direction, when the shared vertex is a local extremum (`capQ`).

A query contributes its shot exactly when the direction is free for `C` at the point
(`Merge.FreeAt`), which is what the sweep reports (`SeesInWhole`).
-/

namespace Chazelle.Core

namespace FuseAsm

@[expose] public section

open Chazelle.Merge (lend rend FreeAt shoot freeAt_vertex shoot_vertex)

theorem getD_lt {α : Type*} {l : List α} {i : ℕ} (h : i < l.length) (d : α) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

variable (J : Merge.Junction)

/-- The chords of `C` shot from the queries `Z` whose direction is free. -/
def shots (Z : Set (Point × ℝ)) : Set (Set Point) :=
  {d | ∃ x ∈ Z, FreeAt J.whole x.1 x.2 ∧ d = shoot J.whole x.1 x.2}

theorem shots_union (Z Z' : Set (Point × ℝ)) : shots J (Z ∪ Z') = shots J Z ∪ shots J Z' := by
  ext d
  simp only [shots, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx | hx, h⟩
    · exact Or.inl ⟨x, hx, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    · exact ⟨x, Or.inl hx, h⟩
    · exact ⟨x, Or.inr hx, h⟩

/-- Queries whose direction is not free contribute nothing: dropping them keeps the shots. -/
theorem shots_eq_of {Z Z' : Set (Point × ℝ)} (hsub : Z ⊆ Z')
    (hfree : ∀ x ∈ Z', FreeAt J.whole x.1 x.2 → x ∈ Z) : shots J Z = shots J Z' := by
  ext d
  constructor
  · rintro ⟨x, hx, hf, rfl⟩; exact ⟨x, hsub hx, hf, rfl⟩
  · rintro ⟨x, hx, hf, rfl⟩; exact ⟨x, hfree x hx hf, hf, rfl⟩

/-- The chord-end queries of a family. -/
def endQ (S : Set (Set Point)) : Set (Point × ℝ) :=
  {x | ∃ c ∈ S, x = (lend c, 1)} ∪ {x | ∃ c ∈ S, x = (rend c, -1)}

/-- The vertex queries at vertex `k` of `C`. -/
def vtxQ (k : ℕ) : Set (Point × ℝ) := {(J.whole.vertex k, 1), (J.whole.vertex k, -1)}

/-- The vertex queries at the tops of `C₁` and `C₂`. -/
def topQ : Set (Point × ℝ) := vtxQ J J.left.topIdx ∪ vtxQ J (J.m₁ + J.right.topIdx)

/-- The cap query. -/
def capQ : Set (Point × ℝ) := {x | SharedExtremum J ∧ x = (capOrigin J, capDir J)}

theorem shots_vtxQ (k : ℕ) :
    shots J (vtxQ J k) = {d | ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ J.whole.DirFree k σ ∧
      d = J.whole.chordSet k σ} := by
  ext d
  simp only [shots, vtxQ, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, hf, rfl⟩
    rcases hx with rfl | rfl
    · exact ⟨1, Or.inl rfl, (freeAt_vertex _ _ _).1 hf, (shoot_vertex _ _ _)⟩
    · exact ⟨-1, Or.inr rfl, (freeAt_vertex _ _ _).1 hf, (shoot_vertex _ _ _)⟩
  · rintro ⟨σ, hσ | hσ, hf, rfl⟩ <;> subst hσ
    · exact ⟨_, Or.inl rfl, (freeAt_vertex _ _ _).2 hf, (shoot_vertex _ _ _).symm⟩
    · exact ⟨_, Or.inr rfl, (freeAt_vertex _ _ _).2 hf, (shoot_vertex _ _ _).symm⟩

theorem shared_eq_shots : J.sharedChords = shots J (vtxQ J J.m₁) := by
  rwr [shots_vtxQ]

theorem top_eq_shots : topChords J = shots J (topQ J) := by
  rw [topQ, shots_union, shots_vtxQ, shots_vtxQ]
  ext d
  simp only [topChords, topIdxs, Finset.mem_insert, Finset.mem_singleton, Set.mem_union,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk | hk, h⟩ <;> subst hk
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩

theorem cap_eq_shots : capChords J = shots J (capQ J) := by
  ext d
  simp only [capChords, shots, capQ, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨he, hf, rfl⟩; exact ⟨_, ⟨he, rfl⟩, hf, rfl⟩
  · rintro ⟨x, ⟨he, rfl⟩, hf, rfl⟩; exact ⟨he, hf, rfl⟩

theorem fusion_eq_shots (S₁ S₂ : Set (Set Point)) :
    J.fusion S₁ S₂ = shots J (endQ (S₁ ∪ S₂)) ∪ shots J (vtxQ J J.m₁) := by
  rw [← shared_eq_shots, endQ, shots_union]
  ext d
  simp only [Merge.Junction.fusion, shots, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ((⟨c, hc, hf, rfl⟩ | ⟨c, hc, hf, rfl⟩) | h)
    · exact Or.inl (Or.inl ⟨_, ⟨c, hc, rfl⟩, hf, rfl⟩)
    · exact Or.inl (Or.inr ⟨_, ⟨c, hc, rfl⟩, hf, rfl⟩)
    · exact Or.inr h
  · rintro ((⟨x, ⟨c, hc, rfl⟩, hf, rfl⟩ | ⟨x, ⟨c, hc, rfl⟩, hf, rfl⟩) | h)
    · exact Or.inl (Or.inl ⟨c, hc, hf, rfl⟩)
    · exact Or.inl (Or.inr ⟨c, hc, hf, rfl⟩)
    · exact Or.inr h

/-- **The fused family as a set of shots.** -/
theorem fused_eq_shots (S₁ S₂ : Set (Set Point)) :
    J.fusion S₁ S₂ ∪ glueChords J =
      shots J (endQ (S₁ ∪ S₂) ∪ vtxQ J J.m₁ ∪ topQ J ∪ capQ J) := by
  rw [fusion_eq_shots, glueChords, top_eq_shots, cap_eq_shots, shots_union, shots_union,
    shots_union]
  ac_rfl

/-! ## The answers of the sweep -/

/-- The triples of the answers with flag `1`. -/
def collect (R : List (ℕ × ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  (R.filter (fun r => r.1 == 1)).map (fun r => r.2)

/-- The geometric queries of a query list of side `i`. -/
def geoQ (Q : Polygon) (i : ℕ) (L : List (ℕ × ℕ × ℕ)) : Set (Point × ℝ) :=
  {x | ∃ q ∈ L, x = ((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩, dirOf q.2.2)}

end

end FuseAsm

end Chazelle.Core
