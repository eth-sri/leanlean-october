module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SpecMerge

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

open Chazelle.Merge (lend rend FreeAt shoot freeAt_vertex             )

theorem getD_lt {α : Type*} {l : List α} {i : ℕ} (h : i < l.length) (d : α) :
    l.getD i d = l[i] := by
  simp_all

variable (J : Merge.Junction)

/-- The chords of `C` shot from the queries `Z` whose direction is free. -/
def shots (Z : Set (Point × ℝ)) : Set (Set Point) :=
  {d | ∃ x ∈ Z, FreeAt J.whole x.1 x.2 ∧ d = shoot J.whole x.1 x.2}

theorem shots_union (Z Z' : Set (Point × ℝ)) : shots J (Z ∪ Z') = shots J Z ∪ shots J Z' := by
  ext d
  simp only [shots, Set.mem_union, Set.mem_ofPred_eq]
  ram_grind

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
  aesop (add simp [shots, vtxQ, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]) (add safe (by omega))

theorem shared_eq_shots : J.sharedChords = shots J (vtxQ J J.m₁) := by
  rw [shots_vtxQ]; rfl

theorem top_eq_shots : topChords J = shots J (topQ J) := by
  aesop (add simp [topQ, shots_union, shots_vtxQ, topChords, topIdxs, Finset.mem_insert, Finset.mem_singleton, Set.mem_union, Set.mem_ofPred_eq]) (add safe (by omega))

theorem cap_eq_shots : capChords J = shots J (capQ J) := by
  ext d
  simp only [capChords, shots, capQ, Set.mem_ofPred_eq]
  simp_all

section
variable (S₁ S₂ : Set (Set Point))
theorem fusion_eq_shots :
    J.fusion S₁ S₂ = shots J (endQ (S₁ ∪ S₂)) ∪ shots J (vtxQ J J.m₁) := by
  rw [← shared_eq_shots, endQ, shots_union]
  ext d
  simp only [Merge.Junction.fusion, shots, Set.mem_union, Set.mem_ofPred_eq]
  simp_all

/-- **The fused family as a set of shots.** -/
theorem fused_eq_shots :
    J.fusion S₁ S₂ ∪ glueChords J =
      shots J (endQ (S₁ ∪ S₂) ∪ vtxQ J J.m₁ ∪ topQ J ∪ capQ J) := by
  grind [fusion_eq_shots, glueChords, top_eq_shots, cap_eq_shots, shots_union]

/-! ## The answers of the sweep -/


end


/-- The geometric queries of a query list of side `i`. -/
def geoQ (Q : Polygon) (i : ℕ) (L : List (ℕ × ℕ × ℕ)) : Set (Point × ℝ) :=
  {x | ∃ q ∈ L, x = ((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩, dirOf q.2.2)}

end

end FuseAsm

end Chazelle.Core
