module

public import Chazelle.Core.FactsFullDegInt
public import Chazelle.Core.SpecKernels
public import Chazelle.Merge.Augmented
public import Chazelle.MiscTactics

/-!
# Down phase, A1 (math, part 1): which interior chord records are vertex chords

The interior walk of `Q` is `Q` itself (if `LeftInside Q`) or `Q` reversed; its edge `p` starts at
the input vertex `wStart li n p`.  A chord triple `x = (h, lp, rp)` is **kept** (`keepX`) when one
of its walk edges starts at the vertex `h`.

**`mem_full_iff`**: for `Q` simple with distinct heights and an attached admissible record of the
interior model, the chord is a vertex chord (`∈ (interiorModel Q).Full = chords Q`) iff the triple
is kept:
* kept: the end is the vertex `h` (parameter `0`), so the chord is the vertex chord of `h` in its
  direction (`FullDegInt.eq_of_common`);
* vertex chord `chordSet Q i σ`: `i = h` (distinct heights), `Q.vtx h` is a boundary point of the
  chord, hence one of its ends `pos ⟨p, h + 1⟩`; a parameter `t ∈ (0, 1)` would put `Q.vtx h` on
  a non-incident edge (simplicity) or at the end of the edge (`t = 1`), so `t = 0` and the edge
  starts at `h` (`start_of_pos`).

Design: `docs/design-downphase-nf.md` §3.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (IsHChordIn)
open Chazelle.Visibility (hseg chords chordSet rayPt)
open Chazelle.Geometry (lerp point_ext)

namespace DownBase

/-- The input vertex at the start of interior walk edge `p` (`li`: the `LeftInside` bit). -/
def wStart (li : Bool) (n p : ℕ) : ℕ := if li then p else n - 1 - p

/-- The input vertex at the end of interior walk edge `p`. -/
def wEnd (li : Bool) (n p : ℕ) : ℕ := wStart li n ((p + 1) % n)

/-- **A kept triple**: one of its walk edges starts at the height vertex. -/
def keepX (li : Bool) (n : ℕ) (x : ℕ × ℕ × ℕ) : Bool :=
  decide (x.1 = wStart li n x.2.1) || decide (x.1 = wStart li n x.2.2)

theorem keepX_iff (li : Bool) (n : ℕ) (x : ℕ × ℕ × ℕ) :
    keepX li n x = true ↔ x.1 = wStart li n x.2.1 ∨ x.1 = wStart li n x.2.2 := by
  simp [keepX]

variable {Q : Polygon} {li : Bool}

theorem interiorWalk_n (Q : Polygon) : (interiorWalk Q).n = Q.n := by
  unfold interiorWalk
  split_ifs
  · rfl
  · simp [Polygon.n]

theorem rev_vtx (Q : Polygon) {p : ℕ} (hp : p < Q.n) :
    Polygon.vtx ⟨Q.vertices.reverse⟩ p = Q.vtx (Q.n - 1 - p) := by
  simp only [Polygon.vtx, List.getD_eq_getElem?_getD]
  rw [List.getElem?_reverse hp]
  rfl

theorem walk_vtx (hli : li = true ↔ Mountain.LeftInside Q) {p : ℕ} (hp : p < Q.n) :
    (interiorWalk Q).vtx p = Q.vtx (wStart li Q.n p) := by
  unfold interiorWalk wStart
  by_cases h : Mountain.LeftInside Q
  · rw [ite_eq_left h, hli.2 h]
    rfl
  · have : li = false := by
      cases hb : li
      · rfl
      · exact absurd (hli.1 hb) h
    rw [ite_eq_right h, this]
    exact rev_vtx Q hp

theorem mod_lt' {p n : ℕ} (hp : p < n) : (p + 1) % n < n := Nat.mod_lt _ (by omega)

theorem walk_vtx_succ (hli : li = true ↔ Mountain.LeftInside Q) {p : ℕ} (hp : p < Q.n) :
    (interiorWalk Q).vtx ((p + 1) % (interiorWalk Q).n) = Q.vtx (wEnd li Q.n p) := by
  rw [interiorWalk_n]
  exact walk_vtx hli (mod_lt' hp)

theorem wStart_lt {n p : ℕ} (hp : p < n) : wStart li n p < n := by
  unfold wStart; splao

theorem wEnd_lt {n p : ℕ} (hp : p < n) : wEnd li n p < n := wStart_lt (mod_lt' hp)

theorem wStart_ne_wEnd {n p : ℕ} (hn : 2 ≤ n) (hp : p < n) : wStart li n p ≠ wEnd li n p := by
  unfold wEnd wStart
  have : (p + 1) % n = if p + 1 < n then p + 1 else 0 := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [show p + 1 = n by omega, Nat.mod_self]
  rw [this]
  splao

/-! ## Positions on the interior walk -/

variable (hQ : Q.Simple) (hDH : DistinctHeights Q) (hli : li = true ↔ Mountain.LeftInside Q)
include hQ hDH hli

omit hQ hDH hli in
theorem wa_eq (_hQ : Q.Simple) (_hDH : DistinctHeights Q) (hli : li = true ↔ Mountain.LeftInside Q)
    {p : ℕ} (hp : p < Q.n) : (interiorModel Q).wa p = Q.vtx (wStart li Q.n p) :=
  walk_vtx hli hp

omit hQ hDH hli in
theorem wb_eq (_hQ : Q.Simple) (_hDH : DistinctHeights Q) (hli : li = true ↔ Mountain.LeftInside Q)
    {p : ℕ} (hp : p < Q.n) : (interiorModel Q).wb p = Q.vtx (wEnd li Q.n p) :=
  walk_vtx_succ hli hp

theorem wa_wb_snd_ne {p : ℕ} (hp : p < Q.n) :
    ((interiorModel Q).wa p).2 ≠ ((interiorModel Q).wb p).2 := by
  rw [wa_eq hQ hDH hli hp, wb_eq hQ hDH hli hp]
  exact hDH _ _ (wStart_lt hp) (wEnd_lt hp) (wStart_ne_wEnd (by have := hQ.1; omega) hp)

theorem param_eq {p h : ℕ} (hp : p < Q.n) :
    (interiorModel Q).param Q ⟨p, h + 1⟩ =
      ((Q.vtx h).2 - ((interiorModel Q).wa p).2) /
        (((interiorModel Q).wb p).2 - ((interiorModel Q).wa p).2) := by
  simp only [Model.param]
  rw [ite_eq_right (wa_wb_snd_ne hQ hDH hli hp)]

/-- The point of a position lies at the height of its vertex. -/
theorem pos_snd {p h : ℕ} (hp : p < Q.n) :
    ((interiorModel Q).pos Q ⟨p, h + 1⟩).2 = (Q.vtx h).2 := by
  have hne := wa_wb_snd_ne hQ hDH hli hp
  have hd  := sub_ne_zero.2 hne.symm
  simp only [Model.pos, Geometry.lerp_snd]
  rw [param_eq hQ hDH hli hp]
  field_simp
  ring

/-- A position whose edge starts at its vertex is that vertex. -/
theorem pos_start {p h : ℕ} (hp : p < Q.n) (hh : h = wStart li Q.n p) :
    (interiorModel Q).pos Q ⟨p, h + 1⟩ = Q.vtx h := by
  have hpar : (interiorModel Q).param Q ⟨p, h + 1⟩ = 0 := by
    rw [param_eq hQ hDH hli hp, wa_eq hQ hDH hli hp, ← hh, sub_self, zero_div]
  simp only [Model.pos]
  rw [hpar, Geometry.lerp_zero, wa_eq hQ hDH hli hp, ← hh]

/-- **A position at a vertex, with parameter in `[0, 1)`, is on an edge starting there.** -/
theorem start_of_pos {p h : ℕ} (hp : p < Q.n) (hh : h < Q.n)
    (ht0 : 0 ≤ (interiorModel Q).param Q ⟨p, h + 1⟩)
    (ht1 : (interiorModel Q).param Q ⟨p, h + 1⟩ < 1)
    (hpos : (interiorModel Q).pos Q ⟨p, h + 1⟩ = Q.vtx h) : h = wStart li Q.n p := by
  set t := (interiorModel Q).param Q ⟨p, h + 1⟩ with ht
  set j := wStart li Q.n p with hj
  set j' := wEnd li Q.n p with hj'
  have hjn : j < Q.n := wStart_lt hp
  have hj'n : j' < Q.n := wEnd_lt hp
  have hjj' : j ≠ j' := wStart_ne_wEnd (by have := hQ.1; omega) hp
  have hpos' : lerp (Q.vtx j) (Q.vtx j') t = Q.vtx h := by
    rw [← hpos]; simp only [Model.pos]; rw [wa_eq hQ hDH hli hp, wb_eq hQ hDH hli hp]
  by_contra hne
  have inj : ∀ a b, a < Q.n → b < Q.n → Q.vtx a = Q.vtx b → a = b := hQ.2.1
  -- `t ≠ 0`
  have ht0' : t ≠ 0 := by
    intro e
    rw [e, Geometry.lerp_zero] at hpos'
    exact hne (inj _ _ hh hjn hpos'.symm)
  -- `h ≠ j'`
  have hj'h : h ≠ j' := by
    intro e
    have hy := congrArg Prod.snd hpos'
    rw [e] at hy
    simp only [Geometry.lerp_snd] at hy
    have hne' : (Q.vtx j).2 ≠ (Q.vtx j').2 := hDH _ _ hjn hj'n hjj'
    have : (1 - t) * ((Q.vtx j').2 - (Q.vtx j).2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact hne' (by linarith)
  -- the `Q` edge carrying the position
  obtain ⟨e, hen, hee, hmem⟩ : ∃ e, e < Q.n ∧ (e = j ∧ (e + 1) % Q.n = j' ∨
      e = j' ∧ (e + 1) % Q.n = j) ∧ Q.vtx h ∈ Q.edge e := by
    have hmod : ∀ q, q < Q.n → (q + 1) % Q.n = if q + 1 < Q.n then q + 1 else 0 := fun q hq => by
      split_ifs with h1
      · exact Nat.mod_eq_of_lt h1
      · rw [show q + 1 = Q.n by omega, Nat.mod_self]
    cases hb : li
    · -- reversed walk: edge `j'` runs from `j'` to `j`
      have hj1 : j = Q.n - 1 - p := by rw [hj]; simp [wStart, hb]
      have hj'1 : j' = Q.n - 1 - (p + 1) % Q.n := by rw [hj']; simp [wEnd, wStart, hb]
      refine ⟨j', hj'n, Or.inr ⟨rfl, ?_⟩, ?_⟩
      · rw [hj1, hj'1, hmod p hp, hmod _ (by splao)]
        splao
      · have hjs : (j' + 1) % Q.n = j := by
          rw [hj1, hj'1, hmod p hp, hmod _ (by splao)]
          splao
        refine ⟨1 - t, by linarith, by linarith, ?_⟩
        rw [hjs, ← hpos']
        simp only [lerp]
        refine Prod.ext ?_ ?_ <;> simp only <;> ring
    · have hj1 : j = p := by rw [hj]; simp [wStart, hb]
      have hj'1 : j' = (p + 1) % Q.n := by rw [hj']; simp [wEnd, wStart, hb]
      refine ⟨j, hjn, Or.inl ⟨rfl, by rw [hj1, hj'1]⟩, ?_⟩
      refine ⟨t, ht0, ht1.le, ?_⟩
      have hs : (j + 1) % Q.n = j' := by rw [hj1, hj'1]
      rw [hs, ← hpos']
      rfl
  have heh : e ≠ h := by
    rintro rfl
    rcases hee with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hne rfl
    · exact hj'h rfl
  have hmh : Q.vtx h ∈ Q.edge h := ⟨0, le_rfl, zero_le_one, by simp⟩
  have hcap := hQ.2.2 h e hh hen heh.symm
  have hin : Q.vtx h ∈ Q.edge h ∩ Q.edge e := ⟨hmh, hmem⟩
  rw [hcap] at hin
  obtain ⟨-, h2 | h2⟩ := hin
  · have := inj _ _ hh hen h2
    exact heh this.symm
  · have := inj _ _ hh (Nat.mod_lt _ (by omega)) h2
    rcases hee with ⟨rfl, h3⟩ | ⟨rfl, h3⟩
    · exact hj'h (this.trans h3)
    · exact hne (this.trans h3)

omit hQ hDH hli in
theorem vtx_not_mem_dom {h : ℕ} (hh : h < Q.n) : Q.vtx h ∉ Q.filled \ Q.boundary := fun hm =>
  hm.2 ⟨h, hh, 0, le_rfl, zero_le_one, by simp⟩

/-! ## Vertex chords among the records -/

/-- **A record of the interior model is a vertex chord iff its triple is kept.** -/
theorem mem_full_iff {x : ℕ × ℕ × ℕ} (hx : (recOf x).Attached (interiorModel Q) Q)
    (hadm : (recOf x).toSet (interiorModel Q) Q ∈ (interiorModel Q).Adm) (hh : x.1 < Q.n) :
    (recOf x).toSet (interiorModel Q) Q ∈ (interiorModel Q).Full ↔ keepX li Q.n x = true := by
  obtain ⟨h, lp, rp⟩ := x
  simp only at hh
  set I := interiorModel Q with hI
  set y := (Q.vtx h).2 with hy
  set a := (I.pos Q ⟨lp, h + 1⟩).1 with ha
  set b := (I.pos Q ⟨rp, h + 1⟩).1 with hb
  have hset : (recOf (h, lp, rp)).toSet I Q = hseg y a b := rfl
  rw [hset] at hadm ⊢
  rw [keepX_iff]
  simp only
  obtain ⟨hA1, hA2⟩ := hx
  obtain ⟨hlp, hl0, hl1, -⟩ := hA1
  obtain ⟨hrp, hr0, hr1, -⟩ := hA2
  have hWn : I.W.n = Q.n := interiorWalk_n Q
  rw [hWn] at hlp hrp
  -- the chord of the domain
  obtain ⟨y', a', b', hch, heq⟩ := hadm
  have hab : a ≤ b := by
    have : ((a', y') : Point) ∈ hseg y a b := heq ▸ (⟨rfl, le_rfl, hch.lt.le⟩ :
      ((a', y') : Point) ∈ hseg y' a' b')
    exact this.2.1.trans this.2.2
  obtain ⟨rfl, rfl, rfl⟩ := Merge.hseg_inj hab heq
  have hL : I.pos Q ⟨lp, h + 1⟩ = (a, y) := point_ext rfl (pos_snd hQ hDH hli hlp)
  have hR : I.pos Q ⟨rp, h + 1⟩ = (b, y) := point_ext rfl (pos_snd hQ hDH hli hrp)
  have hHC : FullDegInt.HC Q (hseg y a b) := ⟨y, a, b, hch, rfl⟩
  constructor
  · -- a vertex chord: the vertex is an end
    intro hmem
    obtain ⟨i, σ, hi, hσ, hdir, hcs, -⟩ := Visibility.chords_spec hQ hmem
    have hvi : Q.vtx i ∈ hseg y a b := by
      rw [hcs, Visibility.chordSet_eq_openChordSet_union hQ hi hdir]
      exact Or.inr (Or.inl rfl)
    have hih : i = h := by
      by_contra hne
      exact hDH _ _ hi hh hne hvi.1
    subst hih
    have hvD := vtx_not_mem_dom (Q := Q) hi
    obtain ⟨-, h1, h2⟩ := hvi
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · exact absurd (by
          have := hch.open_mem _ h1 h2
          rwa [show (((Q.vtx i).1, y) : Point) = Q.vtx i from point_ext rfl rfl] at this) hvD
      · right
        exact start_of_pos hQ hDH hli hrp hi hr0 hr1 (by rw [hR]; exact point_ext h2.symm rfl)
    · left
      exact start_of_pos hQ hDH hli hlp hi hl0 hl1 (by rw [hL]; exact point_ext h1 rfl)
  · -- a kept triple: the chord is the vertex chord of `h`
    have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
        (∀ t, 0 < t → t < b - a → rayPt (Q.vtx h) σ t ∈ Q.filled \ Q.boundary) →
        (∀ t, 0 < t → t < b - a → rayPt (Q.vtx h) σ t ∈ hseg y a b) →
        hseg y a b ∈ chords Q := by
      intro σ hσ hin hon
      have hba : 0 < b - a := sub_pos.2 hch.lt
      have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (b - a) := Ioo_mem_nhdsGT hba
      have hdir : Visibility.DirInterior Q h σ := e1.mono fun t ht => hin t ht.1 ht.2
      have hmem : chordSet Q h σ ∈ chords Q := ⟨h, σ, hh, hσ, hdir, rfl⟩
      have hpar := Visibility.chordParam_pos hQ hh hdir
      set s := min (Visibility.chordParam Q h σ / 2) ((b - a) / 2) with hs
      have hs0 : 0 < s := lt_min (by linarith) (by linarith)
      have hs1 : s < Visibility.chordParam Q h σ := (min_le_left _ _).trans_lt (by linarith)
      have hs2 : s < b - a := (min_le_right _ _).trans_lt (by linarith)
      have hzC : rayPt (Q.vtx h) σ s ∈ chordSet Q h σ := by
        rw [Visibility.chordSet_eq_openChordSet_union hQ hh hdir]
        exact Or.inl ⟨s, ⟨hs0, hs1⟩, rfl⟩
      have heq := FullDegInt.eq_of_common (FullDegInt.hc_full hQ hmem) hHC hzC
        (hon s hs0 hs2) (hin s hs0 hs2)
      rw [← heq]
      exact hmem
    rintro (e | e)
    · -- left end at the vertex
      have hv : Q.vtx h = (a, y) := by rw [← hL]; exact (pos_start hQ hDH hli hlp e).symm
      refine key 1 (Or.inl rfl) (fun t ht1 ht2 => ?_) (fun t ht1 ht2 => ?_)
      · have := hch.open_mem (a + t) (by linarith) (by linarith)
        convert this using 1
        rw [hv]; simp [rayPt]
      · rw [hv]; refine ⟨rfl, ?_, ?_⟩ <;> simp [rayPt] <;> linarith
    · -- right end at the vertex
      have hv : Q.vtx h = (b, y) := by rw [← hR]; exact (pos_start hQ hDH hli hrp e).symm
      refine key (-1) (Or.inr rfl) (fun t ht1 ht2 => ?_) (fun t ht1 ht2 => ?_)
      · have := hch.open_mem (b - t) (by linarith) (by linarith)
        convert this using 1
        rw [hv]; simp [rayPt, sub_eq_add_neg]
      · rw [hv]; refine ⟨rfl, ?_, ?_⟩ <;> simp [rayPt] <;> linarith

end DownBase

end

end Chazelle.Core
