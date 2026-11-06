module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.FuseAsmPt
public import Chazelle.Core.SweepMachine8
public import Chazelle.Core.FuseAsmSet

/-!
# WP-F fusion assembly, part 11: records with the height index of their query

`SeesInWhole` does not bound the height index of a reported record (an index `≥ n` names the
height `0`).  The fusion therefore takes the height index of a reported chord from its query:
a record depends on its height index only through the height (`toSet_congr`, `attached_congr`),
and the query point lies on the chord it sees (`Sweep.origin_mem`), so the chord is at the
height of the query.  `collectQ L R` is the list of the triples `(code - 1, lp, rp)` of the
answers with flag `1` (`collectQ_spec`).
-/

namespace Chazelle.Core

namespace FuseAsm

@[expose] public section

open Chazelle.Merge (FreeAt shoot)

section
variable (M : Model) (Q : Polygon) (e : ℕ) {h h' : ℕ} (hh : (Q.vtx h).2 = (Q.vtx h').2)
include hh
theorem param_congr : M.param Q ⟨e, h + 1⟩ = M.param Q ⟨e, h' + 1⟩ := by
  simp_all [Model.param] <;> omega_nf

theorem pos_congr : M.pos Q ⟨e, h + 1⟩ = M.pos Q ⟨e, h' + 1⟩ := by
  unfold Model.pos; rw [param_congr M Q e hh]


end

section
variable (M : Model) (Q : Polygon) {r r' : CRec} (hh : (Q.vtx r.h).2 = (Q.vtx r'.h).2) (hl : r.lp = r'.lp) (hr : r.rp = r'.rp)
include hh hl hr
theorem toSet_congr : r.toSet M Q = r'.toSet M Q := by
  unfold CRec.toSet CRec.lpos CRec.rpos
  rw [hh, pos_congr M Q r.lp hh, pos_congr M Q r.rp hh, hl, hr]

theorem attached_congr
    (hA : r.Attached M Q) : r'.Attached M Q := by
  core_grind [Chazelle.Core.FuseAsm.param_congr, Chazelle.Core.FuseAsm.toSet_congr, CRec.lpos, CRec.rpos]


end

/-- The height of a query agrees with its height code. -/
def HeightOK (J : Merge.Junction) (Q : Polygon) (i : ℕ) (q : ℕ × ℕ × ℕ) : Prop :=
  ((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩).2 = (Q.vtx (q.2.1 - 1)).2

/-- The triple of an answer, with the height index of its query. -/
def qtrip (p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) : ℕ × ℕ × ℕ :=
  (p.1.2.1 - 1, p.2.2.2.1, p.2.2.2.2)

/-- The triples of the answers with flag `1`, with the height indices of their queries. -/
def collectQ (L : List (ℕ × ℕ × ℕ)) (R : List (ℕ × ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  ((L.zip R).filter (fun p => p.2.1 == 1)).map qtrip

theorem collectQ_append {L : List (ℕ × ℕ × ℕ)} {R : List (ℕ × ℕ × ℕ × ℕ)}
    (hlen : L.length = R.length) (q : ℕ × ℕ × ℕ) (r : ℕ × ℕ × ℕ × ℕ) :
    collectQ (L ++ [q]) (R ++ [r]) =
      collectQ L R ++ (if r.1 = 1 then [(q.2.1 - 1, r.2.2.1, r.2.2.2)] else []) := by
  grind [collectQ, List.filter_append, List.map_append, qtrip]

theorem collectQ_length_le (L : List (ℕ × ℕ × ℕ)) (R : List (ℕ × ℕ × ℕ × ℕ)) :
    (collectQ L R).length ≤ L.length := by
  grind [collectQ, List.length_map, List.length_zip]

section
variable (J : Merge.Junction) (Q : Polygon) (i : ℕ)
/-- The chord seen from a query of a reported answer is at the height of the query. -/
theorem qtrip_eq {q : ℕ × ℕ × ℕ}
    {r : ℕ × ℕ × ℕ × ℕ} (hs : SeesInWhole J Q i q r) (hH : HeightOK J Q i q) (h1 : r.1 = 1) :
    (recOf (qtrip (q, r))).toSet (chainModel J.whole) Q = (recOf r.2).toSet (chainModel J.whole) Q ∧
      (recOf (qtrip (q, r))).Attached (chainModel J.whole) Q := by
  obtain ⟨-, hrec⟩ := hs
  obtain ⟨hset, hatt⟩ := hrec h1
  have hz := Sweep.origin_mem J (a := (chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩)
    (σ := dirOf q.2.2)
  rw [← hset] at hz
  have hy : ((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩).2 = (Q.vtx (recOf r.2).h).2 := hz.1
  have hh : (Q.vtx (recOf r.2).h).2 = (Q.vtx (recOf (qtrip (q, r))).h).2 := by
    rw [← hy]; exact hH
  exact ⟨(toSet_congr _ Q hh rfl rfl).symm, attached_congr _ Q hh rfl rfl hatt⟩

/-- **The chords reported by the sweep**, with the height indices of the queries. -/
theorem collectQ_spec (L : List (ℕ × ℕ × ℕ))
    (R : List (ℕ × ℕ × ℕ × ℕ)) (hlen : R.length = L.length)
    (hs : ∀ j, j < L.length → SeesInWhole J Q i (L.getD j (0, 0, 0)) (R.getD j (0, 0, 0, 0)))
    (hq : ∀ q ∈ L, QueryOK J Q i q ∧ HeightOK J Q i q) :
    {d | ∃ t ∈ collectQ L R, d = (recOf t).toSet (chainModel J.whole) Q} =
        shots J (geoQ J Q i L) ∧
      ∀ t ∈ collectQ L R, (recOf t).Attached (chainModel J.whole) Q ∧ t.1 < Q.n := by
  have key : ∀ t ∈ collectQ L R, ∃ j, j < L.length ∧ (R.getD j (0, 0, 0, 0)).1 = 1 ∧
      t = qtrip (L.getD j (0, 0, 0), R.getD j (0, 0, 0, 0)) := by
    intro t ht
    simp only [collectQ, List.mem_map, List.mem_filter, beq_iff_eq] at ht
    obtain ⟨p, ⟨hp, h1⟩, rfl⟩ := ht
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    ram_grind
  have memk : ∀ j, j < L.length → (R.getD j (0, 0, 0, 0)).1 = 1 →
      qtrip (L.getD j (0, 0, 0), R.getD j (0, 0, 0, 0)) ∈ collectQ L R := by
    intro j hj h1
    have hjR : j < R.length := by omega
    simp only [collectQ, List.mem_map, List.mem_filter, beq_iff_eq]
    refine ⟨(L[j], R[j]), ⟨?_, ?_⟩, ?_⟩
    · have : (L.zip R)[j]'(by grind) = (L[j], R[j]) := by simp
      grind
    all_goals grind
  refine ⟨?_, fun t ht => ?_⟩
  · ext d
    simp only [shots, geoQ, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨j, hj, h1, rfl⟩ := key t ht
      have hmem : L.getD j (0, 0, 0) ∈ L := by grind
      obtain ⟨e1, -⟩ := qtrip_eq J Q i (hs j hj) (hq _ hmem).2 h1
      ram_grind
    · rintro ⟨x, ⟨q, hq', rfl⟩, hf, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq'
      have hs' := hs j hj
      rw [getD_lt hj] at hs'
      have h1 := hs'.1.2 hf
      refine ⟨_, memk j hj h1, ?_⟩
      obtain ⟨e1, -⟩ := qtrip_eq J Q i hs' (hq _ (List.getElem_mem hj)).2 h1
      rw [getD_lt hj, e1, (hs'.2 h1).1]
  · obtain ⟨j, hj, h1, rfl⟩ := key t ht
    have hmem : L.getD j (0, 0, 0) ∈ L := by grind
    obtain ⟨hQ, hH⟩ := hq _ hmem
    refine ⟨(qtrip_eq J Q i (hs j hj) hH h1).2, ?_⟩
    obtain ⟨-, h1', h2', -⟩ := hQ
    grind [qtrip]


end

end

end FuseAsm

end Chazelle.Core
