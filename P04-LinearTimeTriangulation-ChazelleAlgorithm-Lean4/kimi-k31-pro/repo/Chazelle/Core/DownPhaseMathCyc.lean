module

public import Chazelle.Core.DownPhaseMathHost
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# Down phase, math (H-R1): the cyclic structure of the host keys of a region

Around a region `R` of the interior family `S` (walk order of the host keys `hk 0 < … < hk (N-1)`):

* `exit_chord_side`: an exit chord of `R` attached at the host key `hk i` is attached at a
  neighbouring host key, through a chord gap;
* `end_chord`: after the end of an arc of `R` comes a chord gap, along every exit chord attached
  at the end;
* `two_chords_vertex`: two distinct chords attached at one walk position meet at a walk vertex;
* `junction` (distinct heights): a host key between two chord gaps is a walk vertex, and the key
  after the second chord gap starts an arc gap — so between two arcs there is at most one
  junction point;
* `arc_run`: the inner host keys of an arc `(l, r)` are the walk vertices `⌊l⌋ + 1, …` in order,
  the end `r` lies on the walk edge of the last of them or is the next walk vertex, and an arc has
  at most `n - 1` inner vertices.
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn sideLeft IsHChordIn)
open DownHost

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **Two distinct chords attached at one position meet at a walk vertex.** -/
theorem two_chords_vertex (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    {c c' : Set Point} (hc : c ∈ S) (hc' : c' ∈ S) (hcc : c ≠ c') {p : ℕ} {t : ℝ}
    (hA : SideAttach (interiorModel Q).W c p t) (hA' : SideAttach (interiorModel Q).W c' p t) :
    t = 0 := by
  set I := interiorModel Q with hI
  have hM : WalkAx I := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  by_contra ht0
  have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hA.2.1 (Ne.symm ht0), hA.2.2.1⟩
  have hWs : I.W.Simple := (FactsInterior.interiorWalk_spec hQ).1
  have hn3 : 3 ≤ I.W.n := Chazelle.Jordan.simple_three_le hWs
  have hp : p < I.W.n := hA.1
  have hne : I.W.vtx p ≠ I.W.vtx ((p + 1) % I.W.n) := by
    intro h
    have := Chazelle.Jordan.simple_vtx_inj hWs hp (Nat.mod_lt _ (by omega)) h
    by_cases h1 : p + 1 < I.W.n
    · rwo [Nat.mod_eq_of_lt h1] at this
    · rwo [show p + 1 = I.W.n by omega, Nat.mod_self] at this
  set y := sidePt I.W p t with hy
  have hyD : y ∉ I.D := hM.trace p hp t hA.2.1 hA.2.2.1.le
  obtain ⟨Y, a, b, hch, rfl⟩ := hF hc
  obtain ⟨Y', a', b', hch', rfl⟩ := hF hc'
  have hyc : y ∈ Visibility.hseg Y a b := hA.2.2.2.1
  have hyc' : y ∈ Visibility.hseg Y' a' b' := hA'.2.2.2.1
  -- `y` is an endpoint of both chords
  have hend : ∀ {Y a b : ℝ}, IsHChordIn I.D Y a b → y ∈ Visibility.hseg Y a b →
      y.1 = a ∨ y.1 = b := by
    intro Y a b hch hyc
    by_contra h
    push Not at h
    apply hyD
    have := hch.open_mem y.1 (lt_of_le_of_ne hyc.2.1 (Ne.symm h.1))
      (lt_of_le_of_ne hyc.2.2 h.2)
    rwa [show ((y.1, Y) : Point) = y from Prod.ext rfl hyc.1.symm] at this
  have hYY : Y = Y' := hyc.1.symm.trans hyc'.1
  subst hYY
  obtain ⟨r, hr, hsec⟩ := hA.2.2.2.2
  obtain ⟨r', hr', hsec'⟩ := hA'.2.2.2.2
  set ε := min (min r r') (min (b - a) (b' - a')) / 2 with hε
  have hba := hch.lt
  have hba' := hch'.lt
  have hε0 : 0 < ε := by
    have : 0 < min (min r r') (min (b - a) (b' - a')) :=
      lt_min (lt_min hr hr') (lt_min (by linarith) (by linarith))
    linarith
  have hεr : ε < r := by
    have := min_le_left (min r r') (min (b - a) (b' - a'))
    have := min_le_left r r'; linarith
  have hεr' : ε < r' := by
    have := min_le_left (min r r') (min (b - a) (b' - a'))
    have := min_le_right r r'; linarith
  have hεb : ε < b - a := by
    have := min_le_right (min r r') (min (b - a) (b' - a'))
    have := min_le_left (b - a) (b' - a'); linarith
  have hεb' : ε < b' - a' := by
    have := min_le_right (min r r') (min (b - a) (b' - a'))
    have := min_le_right (b - a) (b' - a'); linarith
  have hyY : y = (y.1, Y) := Prod.ext rfl hyc.1
  set zp : Point := (y.1 + ε, Y) with hzp
  set zm : Point := (y.1 - ε, Y) with hzm
  have hdp : dist zp y = ε := by
    rw [Prod.dist_eq]
    simp [hzp, hyc.1, abs_of_pos hε0, hε0.le]
  have hdm : dist zm y = ε := by
    rw [Prod.dist_eq]
    simp [hzm, hyc.1, abs_of_pos hε0, hε0.le]
  have hzpy : zp ≠ y := by
    intro h; have := congrArg Prod.fst h; sil [hzp] at this
  have hzmy : zm ≠ y := by
    intro h; have := congrArg Prod.fst h; sil [hzm] at this
  -- the determinant of the edge at `y ± ε`
  have hdet0 : det (I.W.vtx p) (I.W.vtx ((p + 1) % I.W.n)) y = 0 := by
    rw [hy]; unfold sidePt det Geometry.lerp; sir only
  have hsum : det (I.W.vtx p) (I.W.vtx ((p + 1) % I.W.n)) zp +
      det (I.W.vtx p) (I.W.vtx ((p + 1) % I.W.n)) zm =
        2 * det (I.W.vtx p) (I.W.vtx ((p + 1) % I.W.n)) y := by
    rw [hyY]; unfold det; sir only [hzp, hzm]
  rw [hdet0] at hsum
  have hleft : ∀ {z : Point}, sideLeft I.W p t z → 0 < det (I.W.vtx p) (I.W.vtx ((p + 1) % I.W.n)) z :=
    fun h => (Chazelle.Chain.sideLeft_edge hne ht _).1 h
  have hcommon : ∀ z, z ∈ Visibility.hseg Y a b → z ∈ Visibility.hseg Y a' b' → z ∈ I.D → False :=
    fun z hz hz' hzD => chord_disj hM hF hfin hc hc' hcc hz hz' hzD
  rcases hend hch hyc with e1 | e1 <;> rcases hend hch' hyc' with e2 | e2
  · -- both to the right
    apply hcommon zp ⟨rfl, by linarith, by linarith⟩ ⟨rfl, by linarith, by linarith⟩
    exact hch.open_mem _ (by linarith) (by linarith)
  · -- `c` to the right, `c'` to the left
    have h1 := hleft (hsec zp ⟨rfl, by linarith, by linarith⟩ hzpy (by rw [hdp]; exact hεr))
    have h2 := hleft (hsec' zm ⟨rfl, by linarith, by linarith⟩ hzmy (by rw [hdm]; exact hεr'))
    linarith
  · -- `c` to the left, `c'` to the right
    have h1 := hleft (hsec zm ⟨rfl, by linarith, by linarith⟩ hzmy (by rw [hdm]; exact hεr))
    have h2 := hleft (hsec' zp ⟨rfl, by linarith, by linarith⟩ hzpy (by rw [hdp]; exact hεr'))
    linarith
  · -- both to the left
    apply hcommon zm ⟨rfl, by linarith, by linarith⟩ ⟨rfl, by linarith, by linarith⟩
    exact hch.open_mem _ (by linarith) (by linarith)

/-- Attachment points of a chord of `S` are at the height of the chord. -/
theorem attach_height (hFam : (interiorModel Q).ChordFamily Q S) {c : Set Point} (hc : c ∈ S)
    {p p' : ℕ} {t t' : ℝ} (hA : SideAttach (interiorModel Q).W c p t)
    (hA' : SideAttach (interiorModel Q).W c p' t') :
    (sidePt (interiorModel Q).W p t).2 = (sidePt (interiorModel Q).W p' t').2 := by
  obtain ⟨h0, -, a, b, rfl⟩ := hFam.2.2 c hc
  exact hA.2.2.2.1.1.trans hA'.2.2.2.1.1.symm

/-- Distinct heights pass to the interior walk. -/
theorem walk_distinct (hdh : DistinctHeights Q) {k k' : ℕ} (hk : k < Q.n) (hk' : k' < Q.n)
    (h : ((interiorWalk Q).vtx k).2 = ((interiorWalk Q).vtx k').2) : k = k' := by
  classical
  have hli : decide (Mountain.LeftInside Q) = true ↔ Mountain.LeftInside Q := decide_eq_true_iff
  rw [walk_vtx hli hk, walk_vtx hli hk'] at h
  by_contra hne
  exact hdh _ _ (ivB_lt _ hk) (ivB_lt _ hk') (fun e => hne (ivB_inj _ hk hk' e)) h

/-- **Two attachment keys of one chord are on different walk edges.** -/
theorem attach_floor_ne (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hdh : DistinctHeights Q) {c : Set Point} (hc : c ∈ S) {p p' : ℕ} {t t' : ℝ}
    (hA : SideAttach (interiorModel Q).W c p t) (hA' : SideAttach (interiorModel Q).W c p' t')
    (hne : (p : ℝ) + t ≠ p' + t') : p ≠ p' := by
  rintro rfl
  have hy := attach_height hFam hc hA hA'
  have hp := hA.1
  have hWn : (interiorModel Q).W.n = Q.n := walk_n Q
  rw [hWn] at hp
  have hn3 : 3 ≤ Q.n := Chazelle.Jordan.simple_three_le hQ
  have hp1 : (p + 1) % Q.n < Q.n := Nat.mod_lt _ (by omega)
  have hd : ((interiorWalk Q).vtx p).2 ≠ ((interiorWalk Q).vtx ((p + 1) % Q.n)).2 := by
    intro h
    have := walk_distinct hdh hp hp1 h
    by_cases h1 : p + 1 < Q.n
    · rwo [Nat.mod_eq_of_lt h1] at this
    · rwo [show p + 1 = Q.n by omega, Nat.mod_self] at this
  unfold sidePt at hy
  change (Geometry.lerp ((interiorWalk Q).vtx p) ((interiorWalk Q).vtx ((p + 1) % (interiorWalk Q).n)) t).2 =
    (Geometry.lerp ((interiorWalk Q).vtx p) ((interiorWalk Q).vtx ((p + 1) % (interiorWalk Q).n)) t').2 at hy
  rw [walk_n] at hy
  simp only [Geometry.lerp_snd] at hy
  apply hne
  have : (t - t') * (((interiorWalk Q).vtx ((p + 1) % Q.n)).2 - ((interiorWalk Q).vtx p).2) = 0 := by
    linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact absurd (by linarith) hd

section

variable (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
  (hR : R ∈ (interiorModel Q).regions S)
include hQ hFam hne hR

/-- **An exit chord attached at a host key is attached at a neighbouring host key**, through a
chord gap. -/
theorem exit_chord_side {i : ℕ} (hi : i < nk (interiorModel Q) S R) {c : Set Point} (hc : c ∈ S)
    (ht : TouchesIn (interiorModel Q).D c R) {p : ℕ} {t : ℝ}
    (hA : SideAttach (interiorModel Q).W c p t) (hx : hk (interiorModel Q) S R i = p + t) :
    (ChordGap (interiorModel Q) S R i ∧ ∃ (p' : ℕ) (t' : ℝ), SideAttach (interiorModel Q).W c p' t' ∧
        hk (interiorModel Q) S R ((i + 1) % nk (interiorModel Q) S R) = p' + t') ∨
      (ChordGap (interiorModel Q) S R (prevIdx (nk (interiorModel Q) S R) i) ∧
        ∃ (p' : ℕ) (t' : ℝ), SideAttach (interiorModel Q).W c p' t' ∧
          hk (interiorModel Q) S R (prevIdx (nk (interiorModel Q) S R) i) = p' + t') := by
  set I := interiorModel Q
  set N := nk I S R
  have hM : WalkAx I := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have h3 : 3 ≤ N := three_le_nk hQ hFam hne hR
  obtain ⟨j, hj, pa, pb, ta, tb, hAa, hAb, ea, eb, hne', -⟩ :=
    exit_chordGap hM hF hfin hR (by omega) hc ht
  have hgap : ChordGap I S R j := ⟨c, hc, pa, pb, ta, tb, hAa, hAb, ea, eb, hne'⟩
  obtain ⟨k₁, k₂, hsub⟩ := DownDrv.attachKeys_sub hM (hF hc)
  have hsj : (j + 1) % N < N := Nat.mod_lt _ (by omega)
  have hkne := hk_succ_ne hM hF hfin (by omega : 2 ≤ N) hj
  have hxa : hk I S R i ∈ DownDrv.attachKeys I c := ⟨p, t, hA, hx⟩
  have h1 : hk I S R j ∈ DownDrv.attachKeys I c := ⟨pa, ta, hAa, ea⟩
  have h2 : hk I S R ((j + 1) % N) ∈ DownDrv.attachKeys I c := ⟨pb, tb, hAb, eb⟩
  have hcases : hk I S R i = hk I S R j ∨ hk I S R i = hk I S R ((j + 1) % N) := by
    have m0 := hsub hxa
    have m1 := hsub h1
    have m2 := hsub h2
    simp only [mem_insert_iff, mem_singleton_iff] at m0 m1 m2
    rcases m0 with e0 | e0 <;> rcases m1 with e1 | e1 <;> rcases m2 with e2 | e2
    all_goals first
      | exact Or.inl (e0.trans e1.symm)
      | exact Or.inr (e0.trans e2.symm)
      | exact absurd (e1.trans e2.symm) hkne
  rcases hcases with e | e
  · have := hk_inj hM hF hfin hi hj e
    subst this
    exact Or.inl ⟨hgap, pb, tb, hAb, eb⟩
  · have := hk_inj hM hF hfin hi hsj e
    subst this
    rw [prevIdx_succ hj]
    exact Or.inr ⟨hgap, pa, ta, hAa, ea⟩

/-- **After the end of an arc comes a chord gap**, along every exit chord attached at the end. -/
theorem end_chord {i : ℕ} (hi : i < nk (interiorModel Q) S R)
    (hx : hk (interiorModel Q) S R i ∈ exitKeys (interiorModel Q) S R)
    (hA : ArcGap (interiorModel Q) S R (prevIdx (nk (interiorModel Q) S R) i)) :
    ChordGap (interiorModel Q) S R i ∧
      ∀ c ∈ S, TouchesIn (interiorModel Q).D c R → ∀ (p : ℕ) (t : ℝ),
        SideAttach (interiorModel Q).W c p t → hk (interiorModel Q) S R i = p + t →
        ∃ (p' : ℕ) (t' : ℝ), SideAttach (interiorModel Q).W c p' t' ∧
          hk (interiorModel Q) S R ((i + 1) % nk (interiorModel Q) S R) = p' + t' := by
  have hM  := walkAx_interiorModel hQ
  have h3 := three_le_nk hQ hFam hne hR
  have hpl := prevIdx_lt (N := nk (interiorModel Q) S R) (i := i) (by omega)
  have key : ∀ c ∈ S, TouchesIn (interiorModel Q).D c R → ∀ (p : ℕ) (t : ℝ),
      SideAttach (interiorModel Q).W c p t → hk (interiorModel Q) S R i = p + t →
      ChordGap (interiorModel Q) S R i ∧ ∃ (p' : ℕ) (t' : ℝ), SideAttach (interiorModel Q).W c p' t' ∧
        hk (interiorModel Q) S R ((i + 1) % nk (interiorModel Q) S R) = p' + t' := by
    intro c hc ht p t hAt hxt
    rcases exit_chord_side hQ hFam hne hR hi hc ht hAt hxt with h | ⟨hC, -⟩
    · exact h
    · exact absurd hC fun hC => not_arc_and_chord hM hFam.2.1 hFam.1 (by omega) hpl hA hC
  obtain ⟨c, hc, ht, p, t, hAt, hxt⟩ := hx
  exact ⟨(key c hc ht p t hAt hxt).1, fun c hc ht p t hAt hxt => (key c hc ht p t hAt hxt).2⟩

/-- **A host key between two chord gaps is a walk vertex.** -/
theorem vertex_of_two_gaps {j : ℕ} (hj : j < nk (interiorModel Q) S R)
    (hC1 : ChordGap (interiorModel Q) S R (prevIdx (nk (interiorModel Q) S R) j))
    (hC2 : ChordGap (interiorModel Q) S R j) :
    hk (interiorModel Q) S R j = ⌊hk (interiorModel Q) S R j⌋₊ := by
  set I := interiorModel Q
  set N := nk I S R
  have hM : WalkAx I := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have h3 : 3 ≤ N := three_le_nk hQ hFam hne hR
  have hpl : prevIdx N j < N := prevIdx_lt (by omega)
  have hsj : (j + 1) % N < N := Nat.mod_lt _ (by omega)
  obtain ⟨c', hc', p1, p2, t1, t2, hA1, hA2, e1, e2, -⟩ := hC1
  rw [succ_prevIdx hj] at e2
  obtain ⟨c'', hc'', q1, q2, s1, s2, hB1, hB2, f1, f2, -⟩ := hC2
  -- the two chords are distinct
  have hcc : c' ≠ c'' := by
    rintro rfl
    obtain ⟨k₁, k₂, hsub⟩ := DownDrv.attachKeys_sub hM (hF hc')
    have m0 := hsub (show hk I S R (prevIdx N j) ∈ DownDrv.attachKeys I c' from ⟨p1, t1, hA1, e1⟩)
    have m1 := hsub (show hk I S R j ∈ DownDrv.attachKeys I c' from ⟨p2, t2, hA2, e2⟩)
    have m2 := hsub (show hk I S R ((j + 1) % N) ∈ DownDrv.attachKeys I c' from ⟨q2, s2, hB2, f2⟩)
    have d01 : hk I S R (prevIdx N j) ≠ hk I S R j := by
      have := hk_succ_ne hM hF hfin (by omega : 2 ≤ N) hpl
      rwa [succ_prevIdx hj] at this
    have d12 : hk I S R j ≠ hk I S R ((j + 1) % N) := hk_succ_ne hM hF hfin (by omega) hj
    have d02 : hk I S R (prevIdx N j) ≠ hk I S R ((j + 1) % N) := by
      intro h
      have := hk_inj hM hF hfin hpl hsj h
      have e := succ_prevIdx (N := N) hj
      unfold prevIdx at this e
      by_cases h1 : j + 1 < N
      · rw [Nat.mod_eq_of_lt h1] at this
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0; rw [show 0 + N - 1 = N - 1 by omega, Nat.mod_eq_of_lt (by omega)] at this
          omega
        · rw [show j + N - 1 = (j - 1) + N by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)] at this
          omega
      · rw [show j + 1 = N by omega, Nat.mod_self, show j + N - 1 = (j - 1) + N by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at this
        omega
    simp only [mem_insert_iff, mem_singleton_iff] at m0 m1 m2
    rcases m0 with e0 | e0 <;> rcases m1 with e1' | e1' <;> rcases m2 with e2' | e2'
    all_goals first
      | exact d01 (e0.trans e1'.symm)
      | exact d12 (e1'.trans e2'.symm)
      | exact d02 (e0.trans e2'.symm)
  -- both are attached at `hk j`
  obtain ⟨rfl, rfl⟩ := DownHost.key_inj hA2.2.1 hA2.2.2.1 hB1.2.1 hB1.2.2.1 (e2.symm.trans f1)
  have ht := two_chords_vertex hQ hFam hc' hc'' hcc hA2 hB1
  rw [e2, ht, add_zero, Nat.floor_natCast]

/-- **Junctions** (distinct heights): a host key after a chord gap that does not start an arc
gap is a walk vertex, and the key after it starts an arc gap. -/
theorem junction (hdh : DistinctHeights Q) {i : ℕ} (hi : i < nk (interiorModel Q) S R)
    (hC : ChordGap (interiorModel Q) S R (prevIdx (nk (interiorModel Q) S R) i))
    (hnA : ¬ ArcGap (interiorModel Q) S R i) :
    hk (interiorModel Q) S R i = ⌊hk (interiorModel Q) S R i⌋₊ ∧
      ArcGap (interiorModel Q) S R ((i + 1) % nk (interiorModel Q) S R) := by
  set I := interiorModel Q
  set N := nk I S R
  have hM : WalkAx I := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have h3 : 3 ≤ N := three_le_nk hQ hFam hne hR
  have hsi : (i + 1) % N < N := Nat.mod_lt _ (by omega)
  have hCi : ChordGap I S R i :=
    (gap_cases hM hF hfin hne hR (by omega) hi).resolve_left hnA
  have hv := vertex_of_two_gaps hQ hFam hne hR hi hC hCi
  refine ⟨hv, ?_⟩
  by_contra hnA2
  have hCi2 : ChordGap I S R ((i + 1) % N) :=
    (gap_cases hM hF hfin hne hR (by omega) hsi).resolve_left hnA2
  have hv2 := vertex_of_two_gaps hQ hFam hne hR hsi (by rwx [prevIdx_succ hi]) hCi2
  obtain ⟨c, hc, q1, q2, s1, s2, hB1, hB2, f1, f2, -⟩ := hCi
  have hs1 : s1 = 0 := by
    have h1 := floor_add (p := q1) hB1.2.1 hB1.2.2.1
    rw [← f1] at h1
    have : hk I S R i = q1 := by rw [hv, h1]
    linarith
  have hs2 : s2 = 0 := by
    have h1 := floor_add (p := q2) hB2.2.1 hB2.2.2.1
    rw [← f2] at h1
    have : hk I S R ((i + 1) % N) = q2 := by rw [hv2, h1]
    linarith
  subst hs1 hs2
  have hy := attach_height hFam hc hB1 hB2
  simp only [Chazelle.Chain.sidePt_zero] at hy
  have hWn : I.W.n = Q.n := walk_n Q
  have hq1 : q1 < Q.n := hWn ▸ hB1.1
  have hq2 : q2 < Q.n := hWn ▸ hB2.1
  have := walk_distinct hdh hq1 hq2 hy
  subst this
  exact hk_succ_ne hM hF hfin (by omega) hi (by rw [f1, f2])

/-- **One step along an arc gap**: the next key is the next walk vertex or on the same walk
edge. -/
theorem arcGap_step {i : ℕ} (hi : i < nk (interiorModel Q) S R)
    (hA : ArcGap (interiorModel Q) S R i) :
    (hk (interiorModel Q) S R ((i + 1) % nk (interiorModel Q) S R) =
        ⌊hk (interiorModel Q) S R ((i + 1) % nk (interiorModel Q) S R)⌋₊ →
      hk (interiorModel Q) S R ((i + 1) % nk (interiorModel Q) S R) =
        (((⌊hk (interiorModel Q) S R i⌋₊ + 1) % Q.n : ℕ) : ℝ)) ∧
    (hk (interiorModel Q) S R ((i + 1) % nk (interiorModel Q) S R) ≠
        ⌊hk (interiorModel Q) S R ((i + 1) % nk (interiorModel Q) S R)⌋₊ →
      ⌊hk (interiorModel Q) S R ((i + 1) % nk (interiorModel Q) S R)⌋₊ =
        ⌊hk (interiorModel Q) S R i⌋₊) := by
  set I := interiorModel Q
  set N := nk I S R
  have hM : WalkAx I := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have h3 : 3 ≤ N := three_le_nk hQ hFam hne hR
  have hsi : (i + 1) % N < N := Nat.mod_lt _ (by omega)
  have hWn : I.W.n = Q.n := walk_n Q
  have hbx := hostKeys_bounds (hk_mem hM hF hfin hi)
  have hby := hostKeys_bounds (hk_mem hM hF hfin hsi)
  rw [hWn] at hbx hby
  have hnoint : ∀ k : ℕ, k < Q.n → ¬ sideInArc (hk I S R i) (hk I S R ((i + 1) % N)) k :=
    fun k hk => arcGap_noInt hQ hFam hne hR hi hA k (by rwx [hWn])
  rcases noInt_cases hbx.1 hbx.2 hby.1 hby.2 (hk_succ_ne hM hF hfin (by omega) hi) hnoint with
    ⟨hlt, hfl⟩ | hyv
  · refine ⟨fun hint => ?_, fun _ => hfl⟩
    exfalso
    have : (⌊hk I S R i⌋₊ : ℝ) ≤ hk I S R i := Nat.floor_le hbx.1
    rw [hint, hfl] at hlt
    linarith
  · exact ⟨fun _ => hyv, fun hni => absurd (by rw [hyv, Nat.floor_natCast]) hni⟩

omit hQ hFam hne hR in
/-- The gaps of an arc are arc gaps. -/
theorem arcData_gap (_hQ : Q.Simple) (_hFam : (interiorModel Q).ChordFamily Q S) (_hne : S.Nonempty)
    (_hR : R ∈ (interiorModel Q).regions S) {l r : ℝ} {i_l d : ℕ}
    (harc : (interiorModel Q).IsArc S R l r)
    (hD : ArcData (interiorModel Q) S R l r i_l d) {j : ℕ} (hj : j < d) :
    ArcGap (interiorModel Q) S R ((i_l + j) % nk (interiorModel Q) S R) := by
  refine ⟨l, r, harc, fun x hx0 hxn hin => hD.gaps j hj x hx0 hxn ?_⟩
  rwa [Existence.mod_add_one_mod] at hin

/-- **The run of an arc**: the inner host keys of an arc `(l, r)` are the walk vertices
`⌊l⌋ + j` (mod `n`), `0 < j < d`; the end `r` is the walk vertex `⌊l⌋ + d` or lies on the walk
edge `⌊l⌋ + d - 1`; and `d ≤ n`. -/
theorem arc_run (hdh : DistinctHeights Q) {l r : ℝ} {i_l d : ℕ}
    (harc : (interiorModel Q).IsArc S R l r) (hD : ArcData (interiorModel Q) S R l r i_l d) :
    (∀ j, 0 < j → j < d →
      hk (interiorModel Q) S R ((i_l + j) % nk (interiorModel Q) S R) =
        (((⌊l⌋₊ + j) % Q.n : ℕ) : ℝ)) ∧
    ((r = ⌊r⌋₊ ∧ ⌊r⌋₊ = (⌊l⌋₊ + d) % Q.n) ∨ (r ≠ ⌊r⌋₊ ∧ ⌊r⌋₊ = (⌊l⌋₊ + (d - 1)) % Q.n)) ∧
    d ≤ Q.n := by
  set I := interiorModel Q
  set N := nk I S R
  have hM : WalkAx I := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have h3 : 3 ≤ N := three_le_nk hQ hFam hne hR
  have hWn : I.W.n = Q.n := walk_n Q
  have hn3 : 3 ≤ Q.n := Chazelle.Jordan.simple_three_le hQ
  have hil := hD.hil
  have hdN := hD.hdN
  have hd0 := hD.hd0
  have hlb : 0 ≤ l ∧ l < Q.n := by
    have := hostKeys_bounds (hk_mem hM hF hfin hil); rw [hD.hl, hWn] at this; exact this
  have hfl : ⌊l⌋₊ < Q.n := by
    have : (⌊l⌋₊ : ℝ) < Q.n := lt_of_le_of_lt (Nat.floor_le hlb.1) hlb.2
    exact_mod_cast this
  have hmod : ∀ j, (i_l + j) % N < N := fun j => Nat.mod_lt _ (by omega)
  have hsucc : ∀ j, ((i_l + j) % N + 1) % N = (i_l + (j + 1)) % N :=
    fun j => Existence.mod_add_one_mod _ _ _
  -- the inner keys
  have hinner : ∀ j, 0 < j → j < d → hk I S R ((i_l + j) % N) = (((⌊l⌋₊ + j) % Q.n : ℕ) : ℝ) := by
    intro j hj0 hjd
    induction j with
    | zero => omega
    | succ j ih =>
      have hA := arcData_gap hQ hFam hne hR harc hD (show j < d by omega)
      obtain ⟨hint, -⟩ := arcGap_step hQ hFam hne hR (hmod j) hA
      rw [hsucc j] at hint
      obtain ⟨k, hkk⟩ := (hD.inner (j + 1) hj0 hjd).1
      have hkI : hk I S R ((i_l + (j + 1)) % N) = ⌊hk I S R ((i_l + (j + 1)) % N)⌋₊ := by
        rw [hkk, Nat.floor_natCast]
      rw [hint hkI]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [add_zero, Nat.mod_eq_of_lt hil, hD.hl]
      · rw [ih hj (by omega), Nat.floor_natCast, Existence.mod_add_one_mod]
  -- the floor of the key before the end
  have hlast : ⌊hk I S R ((i_l + (d - 1)) % N)⌋₊ = (⌊l⌋₊ + (d - 1)) % Q.n := by
    rcases Nat.eq_zero_or_pos (d - 1) with h0 | h0
    · rw [h0, add_zero, add_zero, Nat.mod_eq_of_lt hil, hD.hl, Nat.mod_eq_of_lt hfl]
    · rw [hinner (d - 1) h0 (by omega), Nat.floor_natCast]
  have hend : (r = ⌊r⌋₊ ∧ ⌊r⌋₊ = (⌊l⌋₊ + d) % Q.n) ∨
      (r ≠ ⌊r⌋₊ ∧ ⌊r⌋₊ = (⌊l⌋₊ + (d - 1)) % Q.n) := by
    have hA := arcData_gap hQ hFam hne hR harc hD (show d - 1 < d by omega)
    obtain ⟨hint, hni⟩ := arcGap_step hQ hFam hne hR (hmod (d - 1)) hA
    rw [hsucc, show d - 1 + 1 = d by omega, hD.hr, hlast] at hint hni
    by_cases hr : r = ⌊r⌋₊
    · left
      refine ⟨hr, ?_⟩
      have := hint hr
      rw [this, Nat.floor_natCast, Existence.mod_add_one_mod, Nat.sub_add_cancel (by omega : 1 ≤ d)]
    · exact Or.inr ⟨hr, hni hr⟩
  refine ⟨hinner, hend, ?_⟩
  -- at most `n` gaps
  by_contra hdn
  push Not at hdn
  have hinj : ∀ j j', j < N → j' < N → hk I S R ((i_l + j) % N) = hk I S R ((i_l + j') % N) →
      j = j' := by
    intro j j' hj hj' h
    have := hk_inj hM hF hfin (hmod j) (hmod j') h
    exact Existence.rot_index_inj hj hj' this
  -- two inner keys coincide if `d > n + 1`
  have hd1 : d = Q.n + 1 := by
    by_contra hne1
    have h1 := hinner 1 one_pos (by omega)
    have h2 := hinner (Q.n + 1) (by omega) (by omega)
    rw [show ⌊l⌋₊ + (Q.n + 1) = (⌊l⌋₊ + 1) + Q.n * 1 by ring, Nat.add_mul_mod_self_left] at h2
    have := hinj 1 (Q.n + 1) (by omega) (by omega) (h1.trans h2.symm)
    omega
  subst hd1
  -- the vertex `⌊l⌋` is the inner key `n`
  have hvn := hinner Q.n (by omega) (by omega)
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt hfl] at hvn
  have hlni : l ≠ ⌊l⌋₊ := by
    intro h
    have e : hk I S R ((i_l + 0) % N) = hk I S R ((i_l + Q.n) % N) := by
      rwx [add_zero, Nat.mod_eq_of_lt hil, hD.hl, hvn]
    have := hinj 0 Q.n (by omega) (by omega) e
    omega
  rcases hend with ⟨hr, hrv⟩ | ⟨hrni, hrfl⟩
  · -- `r` would be the inner key `1`
    rw [show ⌊l⌋₊ + (Q.n + 1) = (⌊l⌋₊ + 1) + Q.n * 1 by ring, Nat.add_mul_mod_self_left] at hrv
    have h1 := hinner 1 one_pos (by omega)
    have e : hk I S R ((i_l + 1) % N) = hk I S R ((i_l + (Q.n + 1)) % N) := by
      rw [h1, hD.hr, hr, hrv]
    have := hinj 1 (Q.n + 1) (by omega) (by omega) e
    omega
  · -- `l` and `r` are on one walk edge: the chord after `r` returns to that edge
    rw [Nat.add_sub_cancel, Nat.add_mod_right, Nat.mod_eq_of_lt hfl] at hrfl
    set p := ⌊l⌋₊ with hp
    have hrb : 0 ≤ r ∧ r < Q.n := by
      have := hostKeys_bounds (hk_mem hM hF hfin (hmod (Q.n + 1)))
      rw [hD.hr, hWn] at this; exact this
    have hlp : (p : ℝ) < l := lt_of_le_of_ne (Nat.floor_le hlb.1) (Ne.symm hlni)
    have hlp1 : l < p + 1 := Nat.lt_floor_add_one l
    have hrp : (p : ℝ) < r := by
      rw [← hrfl]; exact lt_of_le_of_ne (Nat.floor_le hrb.1) (Ne.symm hrni)
    have hrp1 : r < p + 1 := by rw [← hrfl]; exact Nat.lt_floor_add_one r
    -- the arc wraps: `r < l`
    have hrl : r < l := by
      by_contra h
      push Not at h
      obtain ⟨k, hkk⟩ := (hD.inner 1 one_pos (by omega)).1
      have hin := (hD.inner 1 one_pos (by omega)).2
      rw [hkk] at hin
      have hlr : l < r := lt_of_le_of_ne h (fun e => (WalkAx.arc_cuts hne harc).2.2 e)
      unfold sideInArc at hin
      rw [ite_eq_left hlr] at hin
      have h1 : (p : ℝ) < k := lt_trans hlp hin.1
      have h2 : (k : ℝ) < p + 1 := lt_trans hin.2 hrp1
      have h1' : p < k := by exact_mod_cast h1
      have h2' : k < p + 1 := by exact_mod_cast h2
      omega
    -- the exit chord at `r`
    have hiN : (i_l + (Q.n + 1)) % N < N := hmod _
    have hx : hk I S R ((i_l + (Q.n + 1)) % N) ∈ exitKeys I S R := by
      obtain ⟨c, ⟨hc, ht⟩, p', t', hA', he⟩ := hM.exists_exit_at_end hF hfin hne hR harc
      exact ⟨c, hc, ht, p', t', hA', by rwx [hD.hr]⟩
    have hprev : prevIdx N ((i_l + (Q.n + 1)) % N) = (i_l + Q.n) % N := by
      rw [← hsucc Q.n, prevIdx_succ (hmod Q.n)]
    have hAprev : ArcGap I S R (prevIdx N ((i_l + (Q.n + 1)) % N)) := by
      rw [hprev]; exact arcData_gap hQ hFam hne hR harc hD (by omega)
    obtain ⟨-, hnext⟩ := end_chord hQ hFam hne hR hiN hx hAprev
    obtain ⟨c, ⟨hc, ht⟩, pr, tr, hAr, her⟩ := hM.exists_exit_at_end hF hfin hne hR harc
    obtain ⟨pz, tz, hAz, hez⟩ := hnext c hc ht pr tr hAr (by rwx [hD.hr])
    set z := hk I S R (((i_l + (Q.n + 1)) % N + 1) % N) with hz
    have hzr : r ≠ z := by
      rw [← hD.hr]; exact hk_succ_ne hM hF hfin (by omega) hiN
    -- `z` is a cut, so not inside the arc: `r < z ≤ l`
    have hzcut : I.IsCut S z := ⟨c, hc, pz, tz, hAz, hez⟩
    have hzin : ¬ sideInArc l r z := fun h => harc.2.2.2.2.2.1 _ h hzcut
    unfold sideInArc at hzin
    rw [ite_eq_right (not_lt.2 hrl.le)] at hzin
    push Not at hzin
    have hrz : r < z := lt_of_le_of_ne hzin.2 hzr
    have hzfl : ⌊z⌋₊ = p := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by linarith, by linarith⟩
    have hpz : pz = p := by rw [← hzfl, hez, floor_add hAz.2.1 hAz.2.2.1]
    have hpr : pr = p := by rw [← hrfl, her, floor_add hAr.2.1 hAr.2.2.1]
    exact attach_floor_ne hQ hFam hdh hc hAr hAz (by rwx [← her, ← hez])
      (by rw [hpr, hpz])

end

end

end DownMath

end Chazelle.Core
