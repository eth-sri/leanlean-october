module

public import Chazelle.Core.DownPhaseDrvBCtx

/-!
# Down-phase base (D9): the chords emitted by one region

For a region with shooting polygon `polyOf Q l` (`RegOK`; `l` the walk-order list of its symbolic
points), the base case emits, for every point `l[k]` that is a vertex `i` of `Q` (`qvx`: one
abscissa comparison decides it for an edge point) and every direction code `d ∈ {0, 1}` passing
the corner test `emitAt` (`emitG` on the corner `l[k-1], l[k], l[k+1]`), the record
`vtrip li n i d (farW li Q i d)` of the vertex chord of `i` in direction `sgnD d`.

* `regList li Q l`: these records, in the order of `k`, then `d` (`emIdx`: the emitted indices);
* `regList_sound`: every record is that of a vertex chord of `Q` not in `S`, with its domain part
  in the region, attached, with proper ends;
* `regList_complete`: every vertex chord of `Q` not in `S` whose domain part lies in the region
  is emitted;
* `regList_nodup`: the emitted chords are distinct;
* `regList_length`: at most two records per point.
-/

namespace Chazelle.Core

namespace DrvB

@[expose] public section

open Set
open Chazelle.Visibility (DirInterior chordEnd chordSet chords OpenEdgePt)
open DrvR (ivB qE)

variable {Q : Polygon}

/-! ## Vertices among the symbolic points -/

open Classical in
/-- **The vertex of `Q` that a symbolic point is** (an edge point `.onEdge e h` is the vertex `h`
iff its abscissa is that of `v_h`). -/
noncomputable def qvx (Q : Polygon) : SymPt → Option ℕ
  | .vtx i => some i
  | .onEdge e h => if edgeXAt Q e h = (Q.vtx h).1 then some h else none

theorem qvx_eval {s : SymPt} {i : ℕ} (h : qvx Q s = some i) : s.eval Q = Q.vtx i := by
  cases s with
  | vtx j => simp only [qvx, Option.some.injEq] at h; subst h; rfl
  | onEdge e h' =>
    simp only [qvx] at h
    split_ifs at h with hx
    simp only [Option.some.injEq] at h
    subst h
    exact Prod.ext hx rfl

theorem qvx_lt {s : SymPt} {i : ℕ} (hs : s.Lt Q.n) (h : qvx Q s = some i) : i < Q.n := by
  cases s with
  | vtx j => simp only [qvx, Option.some.injEq] at h; subst h; exact hs
  | onEdge e h' =>
    simp only [qvx] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact hs.2

theorem qvx_of_eval (hQ : Q.Simple) (hDH : DistinctHeights Q) {s : SymPt} (hs : s.Lt Q.n) {i : ℕ}
    (hi : i < Q.n) (h : s.eval Q = Q.vtx i) : qvx Q s = some i := by
  cases s with
  | vtx j =>
    simp only [qvx]
    exact congrArg some (hQ.2.1 _ _ hs hi h)
  | onEdge e h' =>
    have hy : (Q.vtx h').2 = (Q.vtx i).2 := by
      have := congrArg Prod.snd h; simpa [SymPt.eval] using this
    have hh : h' = i := by
      by_contra hne; exact hDH _ _ hs.2 hi hne hy
    subst hh
    have hx : edgeXAt Q e h' = (Q.vtx h').1 := by
      have := congrArg Prod.fst h; simpa [SymPt.eval] using this
    simp only [qvx]
    rw [ite_eq_left hx]

/-! ## The corner test on the walk-order list -/

/-- The corner test at point `k` of the walk-order list `l`, direction code `d`. -/
def emitAt (Q : Polygon) (l : List SymPt) (k d : ℕ) : Prop :=
  emitG ((l.getD ((k + l.length - 1) % l.length) (.vtx 0)).eval Q)
    ((l.getD k (.vtx 0)).eval Q) ((l.getD ((k + 1) % l.length) (.vtx 0)).eval Q) (sgnD d)

/-- **The corner test is the interior direction** in the shooting polygon. -/
theorem emitAt_iff {l : List SymPt} (hW : (polyOf Q l).Simple)
    (hL : Mountain.orient (polyOf Q l) = 1) {k : ℕ} (hk : k < l.length) (d : ℕ) :
    emitAt Q l k d ↔ DirInterior (polyOf Q l) k (sgnD d) := by
  have hn := Chazelle.Jordan.simple_three_le hW
  rw [polyOf_n] at hn
  rw [dirInterior_iff_emitG hW hL (by rw [polyOf_n]; exact hk) (sgnD_cases d)]
  unfold emitAt
  have hp : Chazelle.Jordan.prevIdx (polyOf Q l) k = (k + l.length - 1) % l.length := by
    unfold Chazelle.Jordan.prevIdx; rw [polyOf_n]
  rw [hp, polyOf_vtx Q (Nat.mod_lt _ (by omega)), polyOf_vtx Q hk, polyOf_n,
    polyOf_vtx Q (Nat.mod_lt _ (by omega))]

/-! ## The far walk edge -/

open Classical in
/-- **The walk edge carrying the far end** of the vertex chord of `i` in direction `sgnD d`. -/
noncomputable def farW (li : Bool) (Q : Polygon) (i d : ℕ) : ℕ :=
  if h : ∃ w, w < Q.n ∧ OpenEdgePt Q (qE li Q.n w) (chordEnd Q i (sgnD d)) then Classical.choose h
  else 0

theorem farW_spec (hQ : Q.Simple) (hDH : DistinctHeights Q) (li : Bool) {i d : ℕ} (hi : i < Q.n)
    (hdir : DirInterior Q i (sgnD d)) :
    farW li Q i d < Q.n ∧ OpenEdgePt Q (qE li Q.n (farW li Q i d)) (chordEnd Q i (sgnD d)) := by
  have hn := Chazelle.Jordan.simple_three_le hQ
  have hex : ∃ w, w < Q.n ∧ OpenEdgePt Q (qE li Q.n w) (chordEnd Q i (sgnD d)) := by
    obtain ⟨q, hc, -, ho⟩ := far_cand hQ hDH hi (sgnD_cases d) hdir
    exact ⟨qEi li Q.n q, qEi_lt li hc.1, by rw [qE_qEi li (by omega) hc.1]; exact ho⟩
  unfold farW
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex

/-- **Any walk edge whose edge of `Q` carries the far end is `farW`.** -/
theorem farW_eq (hQ : Q.Simple) (hDH : DistinctHeights Q) (li : Bool) {i d w : ℕ} (hi : i < Q.n)
    (hdir : DirInterior Q i (sgnD d)) (hw : w < Q.n)
    (h : OpenEdgePt Q (qE li Q.n w) (chordEnd Q i (sgnD d))) : w = farW li Q i d := by
  obtain ⟨hf, hfo⟩ := farW_spec hQ hDH li hi hdir
  exact qE_inj hw hf (openEdge_unique hQ (DownMath.qE_lt li hw) (DownMath.qE_lt li hf) h hfo)

/-! ## The emitted records -/

open Classical in
/-- The emitted indices `(k, d)`: point `k` is a vertex of `Q` and passes the corner test in
direction `d`. -/
noncomputable def emIdx (Q : Polygon) (l : List SymPt) : List (ℕ × ℕ) :=
  (List.range l.length).flatMap fun k => (List.range 2).filterMap fun d =>
    if (qvx Q (l.getD k (.vtx 0))).isSome ∧ emitAt Q l k d then some (k, d) else none

/-- The record of an emitted index. -/
noncomputable def recAt (li : Bool) (Q : Polygon) (l : List SymPt) (kd : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  vtrip li Q.n ((qvx Q (l.getD kd.1 (.vtx 0))).getD 0) kd.2
    (farW li Q ((qvx Q (l.getD kd.1 (.vtx 0))).getD 0) kd.2)

/-- **The records emitted by a region.** -/
noncomputable def regList (li : Bool) (Q : Polygon) (l : List SymPt) : List (ℕ × ℕ × ℕ) :=
  (emIdx Q l).map (recAt li Q l)

theorem mem_emIdx {l : List SymPt} {kd : ℕ × ℕ} :
    kd ∈ emIdx Q l ↔ kd.1 < l.length ∧ kd.2 < 2 ∧ (qvx Q (l.getD kd.1 (.vtx 0))).isSome ∧
      emitAt Q l kd.1 kd.2 := by
  classical
  unfold emIdx
  simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, d, hd, h⟩
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hk, hd, hc.1, hc.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨kd.1, h1, kd.2, h2, by rw [ite_eq_left ⟨h3, h4⟩]⟩

theorem emIdx_nodup (l : List SymPt) : (emIdx Q l).Nodup := by
  classical
  unfold emIdx
  rw [List.nodup_flatMap]
  refine ⟨fun k _ => ?_, ?_⟩
  · apply List.Nodup.filterMap _ List.nodup_range
    intro d d' x hx hx'
    split_ifs at hx hx' <;> simp only [Option.mem_def, Option.some.injEq, reduceCtorEq] at hx hx'
    rw [← hx] at hx'
    exact (Prod.ext_iff.1 hx').2.symm
  · refine List.nodup_range.pairwise_of_forall_ne fun a _ b _ hab => ?_
    refine List.disjoint_left.2 fun x hx hx' => hab ?_
    simp only [List.mem_filterMap, List.mem_range] at hx hx'
    obtain ⟨d, -, hd⟩ := hx
    obtain ⟨d', -, hd'⟩ := hx'
    split_ifs at hd hd'
    simp only [Option.some.injEq] at hd hd'
    rw [← hd] at hd'
    exact (Prod.ext_iff.1 hd').1.symm

theorem emIdx_length_le (l : List SymPt) : (emIdx Q l).length ≤ 2 * l.length := by
  classical
  unfold emIdx
  rw [List.length_flatMap]
  calc ((List.range l.length).map fun k => ((List.range 2).filterMap fun d =>
        if (qvx Q (l.getD k (.vtx 0))).isSome ∧ emitAt Q l k d then some (k, d) else none).length).sum
      ≤ ((List.range l.length).map fun _ => 2).sum := by
        apply List.sum_le_sum
        intro k _
        exact (List.length_filterMap_le _ _).trans (by simp)
    _ = 2 * l.length := by simp [mul_comm]

theorem regList_length_le (li : Bool) (l : List SymPt) : (regList li Q l).length ≤ 2 * l.length := by
  unfold regList; rw [List.length_map]; exact emIdx_length_le l

/-! ## Soundness, completeness, distinctness -/

section

variable {S : Set (Set Point)} {R : Set Point} {l : List SymPt} {li : Bool}

/-- The facts of an emitted index. -/
theorem emIdx_facts (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hR : RegOK Q S R (polyOf Q l)) (hl : ∀ s ∈ l, s.Lt Q.n) {kd : ℕ × ℕ} (hkd : kd ∈ emIdx Q l) :
    ∃ i, qvx Q (l.getD kd.1 (.vtx 0)) = some i ∧ i < Q.n ∧ kd.1 < l.length ∧ kd.2 ≤ 1 ∧
      (polyOf Q l).vtx kd.1 = Q.vtx i ∧ DirInterior (polyOf Q l) kd.1 (sgnD kd.2) ∧
      DirInterior Q i (sgnD kd.2) ∧ chordSet Q i (sgnD kd.2) ∈ chords Q ∧
      chordSet Q i (sgnD kd.2) ∉ S ∧ chordSet Q i (sgnD kd.2) ∩ (interiorModel Q).D ⊆ R := by
  obtain ⟨hk, hd, hsome, hem⟩ := mem_emIdx.1 hkd
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hsome
  have hmem : l.getD kd.1 (.vtx 0) ∈ l := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact List.getElem_mem hk
  have hin : i < Q.n := qvx_lt (hl _ hmem) hi
  have hv : (polyOf Q l).vtx kd.1 = Q.vtx i := by rw [polyOf_vtx Q hk]; exact qvx_eval hi
  have hdirW := (emitAt_iff hR.simple hR.orient hk kd.2).1 hem
  obtain ⟨hdir, -, hc, hcS, hcR⟩ := hR.sound hQ hFam hin hv (sgnD_cases _) hdirW
  exact ⟨i, hi, hin, hk, by omega, hv, hdirW, hdir, hc, hcS, hcR⟩

/-- **Soundness**: every emitted record is that of a vertex chord of `Q` missing from `S`, with its
domain part in the region, attached, with proper ends. -/
theorem regList_sound (hQ : Q.Simple) (hDH : DistinctHeights Q)
    (hli : li = true ↔ Mountain.LeftInside Q) (hFam : (interiorModel Q).ChordFamily Q S)
    (hR : RegOK Q S R (polyOf Q l)) (hl : ∀ s ∈ l, s.Lt Q.n) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ regList li Q l) :
    (recOf x).toSet (interiorModel Q) Q ∈ chords Q ∧
      (recOf x).toSet (interiorModel Q) Q ∉ S ∧
      (recOf x).toSet (interiorModel Q) Q ∩ (interiorModel Q).D ⊆ R ∧
      (recOf x).Attached (interiorModel Q) Q ∧
      ProperPos (interiorModel Q) Q Q.n (recOf x).lpos ∧
      ProperPos (interiorModel Q) Q Q.n (recOf x).rpos ∧ x.1 < Q.n := by
  unfold regList at hx
  obtain ⟨kd, hkd, rfl⟩ := List.mem_map.1 hx
  obtain ⟨i, hi, hin, -, hd, -, -, hdir, hc, hcS, hcR⟩ := emIdx_facts hQ hFam hR hl hkd
  obtain ⟨hf, hfo⟩ := farW_spec hQ hDH li hin hdir
  have hrec : recAt li Q l kd = vtrip li Q.n i kd.2 (farW li Q i kd.2) := by
    unfold recAt; rw [hi]; rfl
  rw [hrec]
  obtain ⟨hset, hatt, hpl, hpr, hlt⟩ := vtrip_ok hQ hDH hli hin hd hdir hf hfo
  rw [hset]
  exact ⟨hc, hcS, hcR, hatt, hpl, hpr, hlt⟩

/-- **Completeness**: every vertex chord of `Q` missing from `S` with its domain part in the
region is emitted. -/
theorem regList_complete (hQ : Q.Simple) (hDH : DistinctHeights Q)
    (hli : li = true ↔ Mountain.LeftInside Q) (hR : RegOK Q S R (polyOf Q l))
    (hl : ∀ s ∈ l, s.Lt Q.n) {c : Set Point} (hc : c ∈ chords Q) (hcS : c ∉ S)
    (hcR : c ∩ (interiorModel Q).D ⊆ R) :
    ∃ x ∈ regList li Q l, (recOf x).toSet (interiorModel Q) Q = c := by
  obtain ⟨i, σ, hi, hσ, hdir, rfl⟩ := hc
  obtain ⟨k, hk, hv, hdirW⟩ := hR.complete i σ hi hσ hdir hcS hcR
  rw [polyOf_n] at hk
  obtain ⟨d, hd, hσd⟩ : ∃ d, d ≤ 1 ∧ sgnD d = σ := by
    rcases hσ with rfl | rfl
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, le_rfl, rfl⟩
  subst hσd
  have hmem : l.getD k (.vtx 0) ∈ l := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact List.getElem_mem hk
  have hq : qvx Q (l.getD k (.vtx 0)) = some i :=
    qvx_of_eval hQ hDH (hl _ hmem) hi (by rw [← polyOf_vtx Q hk]; exact hv)
  have hkd : (k, d) ∈ emIdx Q l :=
    mem_emIdx.2 ⟨hk, by omega, by rw [hq]; rfl, (emitAt_iff hR.simple hR.orient hk d).2 hdirW⟩
  refine ⟨recAt li Q l (k, d), List.mem_map.2 ⟨(k, d), hkd, rfl⟩, ?_⟩
  have hrec : recAt li Q l (k, d) = vtrip li Q.n i d (farW li Q i d) := by
    unfold recAt; rw [hq]; rfl
  obtain ⟨hf, hfo⟩ := farW_spec hQ hDH li hi hdir
  rw [hrec]
  exact (vtrip_ok hQ hDH hli hi hd hdir hf hfo).1

/-- **Distinctness**: the emitted chords are pairwise distinct. -/
theorem regList_nodup (hQ : Q.Simple) (hDH : DistinctHeights Q)
    (hli : li = true ↔ Mountain.LeftInside Q) (hFam : (interiorModel Q).ChordFamily Q S)
    (hR : RegOK Q S R (polyOf Q l)) (hl : ∀ s ∈ l, s.Lt Q.n) :
    ((regList li Q l).map fun x => (recOf x).toSet (interiorModel Q) Q).Nodup := by
  unfold regList
  rw [List.map_map]
  refine (emIdx_nodup l).map_on ?_
  intro a ha b hb hab
  obtain ⟨i, hi, hin, hak, had, hva, -, hdir, -⟩ := emIdx_facts hQ hFam hR hl ha
  obtain ⟨i', hi', hin', hbk, hbd, hvb, -, hdir', -⟩ := emIdx_facts hQ hFam hR hl hb
  obtain ⟨hf, hfo⟩ := farW_spec hQ hDH li hin hdir
  obtain ⟨hf', hfo'⟩ := farW_spec hQ hDH li hin' hdir'
  have ha' : recAt li Q l a = vtrip li Q.n i a.2 (farW li Q i a.2) := by
    unfold recAt; rw [hi]; rfl
  have hb' : recAt li Q l b = vtrip li Q.n i' b.2 (farW li Q i' b.2) := by
    unfold recAt; rw [hi']; rfl
  simp only [Function.comp] at hab
  rw [ha', hb', (vtrip_ok hQ hDH hli hin had hdir hf hfo).1,
    (vtrip_ok hQ hDH hli hin' hbd hdir' hf' hfo').1] at hab
  obtain ⟨rfl, hσ⟩ := DownDrv.chordSet_inj hQ hDH hin hin' (sgnD_cases _) (sgnD_cases _) hdir
    hdir' hab
  have hd : a.2 = b.2 := by
    unfold sgnD at hσ
    split_ifs at hσ with h1 h2 h2 <;> first | omega | norm_num at hσ
  have hk : a.1 = b.1 := by
    have := hva.trans hvb.symm
    exact hR.simple.2.1 _ _ (by rw [polyOf_n]; exact hak) (by rw [polyOf_n]; exact hbk) this
  exact Prod.ext hk hd

end

end

end DrvB

end Chazelle.Core
