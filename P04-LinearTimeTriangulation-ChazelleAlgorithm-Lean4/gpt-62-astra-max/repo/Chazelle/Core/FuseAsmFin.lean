module

public import Chazelle.Core.FuseAsmHt
public import Chazelle.Core.FuseDeg
public import Chazelle.Core.FuseMath
public import Chazelle.Core.OracleQFacts

/-!
# WP-F fusion assembly, part 13: the chord list of the fusion

From the two sweeps (query lists `L₀`, `L₁`, answers `R₀`, `R₁`) and a list `D` with the
elements of `collectQ L₀ R₀ ++ collectQ L₁ R₁` and no repetition:

* the chords of `D` are `J.fusion S₁ S₂ ∪ glueChords J` (`fuseList_set`), provided the geometric
  queries are among the queries of `fused_eq_shots` and contain all of those with a free
  direction (`Cover`);
* `D` is a valid input of `BuildNF` (`fuseList_ok`).
-/

namespace Chazelle.Core

namespace FuseAsm

@[expose] public section

open Chazelle.Merge (FreeAt shoot)

variable (J : Merge.Junction) (Q : Polygon)

/-- The query set of the fused family. -/
def fuseZ (S₁ S₂ : Set (Set Point)) : Set (Point × ℝ) :=
  endQ (S₁ ∪ S₂) ∪ vtxQ J J.m₁ ∪ topQ J ∪ capQ J

/-- The geometric queries of the two sweeps cover the query set of the fused family. -/
def Cover (S₁ S₂ : Set (Set Point)) (L₀ L₁ : List (ℕ × ℕ × ℕ)) : Prop :=
  geoQ J Q 0 L₀ ∪ geoQ J Q 1 L₁ ⊆ fuseZ J S₁ S₂ ∧
    ∀ x ∈ fuseZ J S₁ S₂, FreeAt J.whole x.1 x.2 → x ∈ geoQ J Q 0 L₀ ∪ geoQ J Q 1 L₁

/-- The answers of the two sweeps. -/
structure Answers (L₀ L₁ : List (ℕ × ℕ × ℕ)) (R₀ R₁ : List (ℕ × ℕ × ℕ × ℕ)) : Prop where
  len₀ : R₀.length = L₀.length
  len₁ : R₁.length = L₁.length
  sees₀ : ∀ j, j < L₀.length →
    SeesInWhole J Q 0 (L₀.getD j (0, 0, 0)) (R₀.getD j (0, 0, 0, 0))
  sees₁ : ∀ j, j < L₁.length →
    SeesInWhole J Q 1 (L₁.getD j (0, 0, 0)) (R₁.getD j (0, 0, 0, 0))
  ok₀ : ∀ q ∈ L₀, QueryOK J Q 0 q ∧ HeightOK J Q 0 q
  ok₁ : ∀ q ∈ L₁, QueryOK J Q 1 q ∧ HeightOK J Q 1 q

theorem fuseList_set {S₁ S₂ : Set (Set Point)} {L₀ L₁ : List (ℕ × ℕ × ℕ)}
    {R₀ R₁ : List (ℕ × ℕ × ℕ × ℕ)} (hA : Answers J Q L₀ L₁ R₀ R₁) (hC : Cover J Q S₁ S₂ L₀ L₁)
    {D : List (ℕ × ℕ × ℕ)} (hD : ∀ x, x ∈ D ↔ x ∈ collectQ L₀ R₀ ++ collectQ L₁ R₁) :
    {c | ∃ x ∈ D, c = (recOf x).toSet (chainModel J.whole) Q} =
        J.fusion S₁ S₂ ∪ glueChords J ∧
      ∀ x ∈ D, (recOf x).Attached (chainModel J.whole) Q ∧ x.1 < Q.n := by
  obtain ⟨e₀, a₀⟩ := collectQ_spec J Q 0 L₀ R₀ hA.len₀ hA.sees₀ hA.ok₀
  obtain ⟨e₁, a₁⟩ := collectQ_spec J Q 1 L₁ R₁ hA.len₁ hA.sees₁ hA.ok₁
  refine ⟨?_, fun x hx => ?_⟩
  · rw [fused_eq_shots, show endQ (S₁ ∪ S₂) ∪ vtxQ J J.m₁ ∪ topQ J ∪ capQ J = fuseZ J S₁ S₂ from rfl,
      ← shots_eq_of J hC.1 hC.2, shots_union, ← e₀, ← e₁]
    ext c
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases List.mem_append.1 ((hD x).1 hx) with h | h
      · exact Or.inl ⟨x, h, rfl⟩
      · exact Or.inr ⟨x, h, rfl⟩
    · rintro (⟨x, h, rfl⟩ | ⟨x, h, rfl⟩)
      · exact ⟨x, (hD x).2 (List.mem_append_left _ h), rfl⟩
      · exact ⟨x, (hD x).2 (List.mem_append_right _ h), rfl⟩
  · rcases List.mem_append.1 ((hD x).1 hx) with h | h
    · exact a₀ x h
    · exact a₁ x h

/-- **The chord list of the fusion is a valid input of `BuildNF`.** -/
theorem fuseList_ok (hP : J.P.Simple) (hQ : DistinctHeights Q) (hgen : SharedGeneric J)
    {S₁ S₂ : Set (Set Point)} (hS₁ : (chainModel J.left).ChordFamily Q S₁)
    (hS₂ : (chainModel J.right).ChordFamily Q S₂) {L₀ L₁ : List (ℕ × ℕ × ℕ)}
    {R₀ R₁ : List (ℕ × ℕ × ℕ × ℕ)} (hA : Answers J Q L₀ L₁ R₀ R₁) (hC : Cover J Q S₁ S₂ L₀ L₁)
    {D : List (ℕ × ℕ × ℕ)} (hD : ∀ x, x ∈ D ↔ x ∈ collectQ L₀ R₀ ++ collectQ L₁ R₁)
    (hnd : D.Nodup) :
    ChordTriplesOK (chainModel J.whole) Q D ∧
      {c | ∃ x ∈ D, c = (recOf x).toSet (chainModel J.whole) Q} =
        J.fusion S₁ S₂ ∪ glueChords J ∧
      D.length ≤ L₀.length + L₁.length := by
  obtain ⟨hset, hatt⟩ := fuseList_set J Q hA hC hD
  have hadm := FuseDeg.fuse_adm J hgen hS₁.2.1 hS₂.2.1
  have hmemF : ∀ x ∈ D, (recOf x).toSet (chainModel J.whole) Q ∈ (chainModel J.whole).Adm :=
    fun x hx => hadm (by rw [← hset]; exact ⟨x, hx, rfl⟩)
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, fun x hx => (hatt x hx).1, fun x hx => (hatt x hx).2⟩, hset, ?_⟩
  · have : {c | ∃ x ∈ D, c = (recOf x).toSet (chainModel J.whole) Q} =
        (fun x => (recOf x).toSet (chainModel J.whole) Q) '' {x | x ∈ D} := by
      ext c; simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    rw [this]; exact (D.finite_toSet).image _
  · rintro c ⟨x, hx, rfl⟩; exact hmemF x hx
  · rintro c ⟨x, hx, rfl⟩
    exact ⟨x.1, (hatt x hx).2, _, _, rfl⟩
  · refine hnd.map_on fun x hx y hy he => ?_
    have hM := walkAx_chainModel (C := J.whole) hP
    obtain ⟨e1, e2, e3⟩ := rec_eq_of_toSet hM hQ (hatt x hx).1 (hatt y hy).1 (hmemF x hx)
      (hatt x hx).2 (hatt y hy).2 he
    obtain ⟨a, b, d⟩ := x
    obtain ⟨a', b', d'⟩ := y
    simp only [recOf] at e1 e2 e3
    rw [e1, e2, e3]
  · have hsub : D ⊆ collectQ L₀ R₀ ++ collectQ L₁ R₁ := fun x hx => (hD x).1 hx
    have := (hnd.subperm hsub).length_le
    rw [List.length_append] at this
    have h0 := collectQ_length_le L₀ R₀
    have h1 := collectQ_length_le L₁ R₁
    omega

end

end FuseAsm

end Chazelle.Core
