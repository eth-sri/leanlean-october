module

public import Chazelle.Core.SweepEvTasks4
public import Chazelle.Core.SweepEvStartM
public import Chazelle.Core.SweepEvCount
set_option maxHeartbeats 4000000

/-!
# The sweep (WP-D), stage 3: the start of the event loop (task L0, mathematics)

* `chordFamily_pair`: one polygon carries the heights of the chords of `S₂` and of `F₂⁺` (the
  polygon of the family facts is only a height table).
* `stops_sorted`, `stops_two`, `stops_ge`: the stop records of stage 2 are sorted by offset, at
  most two share an offset (`tie_third`), all offsets are at least `Lst`.
* `evInv_start`: **the invariant at the start key** from the labels of the anchored stops at the
  start key (`evInv_anchor`, or `evInv_pocket`), or, when no stop at the start key is anchored, the
  region faced before the end of the right stretch (`startTask`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (hseg)

@[expose] public section

/-! ## A height table for two families -/

/-- A polygon whose vertices carry the heights of the chords of a finite family. -/
noncomputable def hPolyS (F : Set (Set Point)) (hfin : F.Finite) : Polygon :=
  ⟨hfin.toFinset.toList.map fun c => ((0 : ℝ), (Merge.lend c).2)⟩

theorem hPolyS_vtx {F : Set (Set Point)} (hfin : F.Finite) {C : Chain} {c : Set Point}
    (hc : c ∈ F) (hcC : c ∈ Merge.augChords C) :
    ∃ h, h < (hPolyS F hfin).n ∧ ∃ a b : ℝ, c = hseg ((hPolyS F hfin).vtx h).2 a b := by
  have hmem : ((0 : ℝ), (Merge.lend c).2) ∈ (hPolyS F hfin).vertices := by
    simp only [hPolyS]
    exact List.mem_map.2 ⟨c, by simp [hc], rfl⟩
  obtain ⟨h, hh, he⟩ := List.mem_iff_getElem.1 hmem
  obtain ⟨y, a, b, -, -, hcd, hl, -⟩ := Merge.augChords_spec hcC
  refine ⟨h, hh, a, b, ?_⟩
  have hv : (hPolyS F hfin).vtx h = ((0 : ℝ), (Merge.lend c).2) := by
    unfold Polygon.vtx
    rw [List.getD_eq_getElem _ _ hh, he]
  rw [hv, hl, hcd]

/-- **One polygon for the families `S₂` and `F₂⁺`.** -/
theorem chordFamily_pair (J : Merge.Junction) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) :
    ∃ Q : Polygon, (chainModel J.right).ChordFamily Q S₂ ∧
      (chainModel J.whole).ChordFamily Q (F₂plus J S₂) := by
  have hfin  := hS₂f.union (F₂plus_finite J hS₂f)
  refine ⟨hPolyS _ hfin, ⟨hS₂f, hS₂, fun c hc => hPolyS_vtx hfin (Or.inl hc) (hS₂ hc)⟩,
    ⟨F₂plus_finite J hS₂f, F₂plus_subset J hS₂, fun c hc =>
      hPolyS_vtx hfin (Or.inr hc) (F₂plus_subset J hS₂ hc)⟩⟩

/-! ## The stop records -/

section Stops

variable {P : Polygon} {J : Merge.Junction} {N₂ : NF}

/-- The offset of a stop record. -/
noncomputable def soff (P : Polygon) (J : Merge.Junction) (r : ℕ × ℕ × ℕ × ℕ × ℕ) : ℝ :=
  oW J (r.1 + (chainModel J.whole).param (Qof P) ⟨r.1, r.2.1⟩)

theorem stopsOf_getElem {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)} {i : ℕ} (hi : i < rs.length) :
    (stopsOf J (Qof P) N₂ rs)[i]'(by simp [stopsOf, hi]) =
      ((rs[i]).1, (chainModel J.whole).param (Qof P) ⟨(rs[i]).1, (rs[i]).2.1⟩,
        stopSet J (Qof P) N₂ (rs[i]).2.2.1 (rs[i]).2.2.2.1 (rs[i]).2.2.2.2) := by
  simp [stopsOf]

/-- The facts of the stop `i`: its chord, attached at its position, on the `C₁` part. -/
theorem stop_facts {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hst : StopsOK J (N₂.F (chainModel J.right) (Qof P)) (stopsOf J (Qof P) N₂ rs)) {i : ℕ}
    (hi : i < rs.length) :
    stopSet J (Qof P) N₂ (rs[i]).2.2.1 (rs[i]).2.2.2.1 (rs[i]).2.2.2.2 ∈
        F₂plus J (N₂.F (chainModel J.right) (Qof P)) ∧
      StopChord2 J (N₂.F (chainModel J.right) (Qof P))
        (stopSet J (Qof P) N₂ (rs[i]).2.2.1 (rs[i]).2.2.2.1 (rs[i]).2.2.2.2) ∧
      SideAttach (chainModel J.whole).W
        (stopSet J (Qof P) N₂ (rs[i]).2.2.1 (rs[i]).2.2.2.1 (rs[i]).2.2.2.2) (rs[i]).1
        ((chainModel J.whole).param (Qof P) ⟨(rs[i]).1, (rs[i]).2.1⟩) ∧
      (Lst J : ℝ) ≤ soff P J rs[i] := by
  have hi' : i < (stopsOf J (Qof P) N₂ rs).length := by simp [stopsOf, hi]
  have h := hst.1 _ (List.getElem_mem hi')
  rw [stopsOf_getElem hi] at h
  exact h

/-- **The stops are sorted by offset.** -/
theorem stops_sorted {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hst : StopsOK J (N₂.F (chainModel J.right) (Qof P)) (stopsOf J (Qof P) N₂ rs)) {i i' : ℕ}
    (hii : i ≤ i') (hi' : i' < rs.length) :
    soff P J (rs[i]'(by omega)) ≤ soff P J rs[i'] := by
  rcases hii.lt_or_eq with h | rfl
  · have hl : (stopsOf J (Qof P) N₂ rs).length = rs.length := by simp [stopsOf]
    have := List.pairwise_iff_getElem.1 hst.2.2.1 i i' (by omega) (by omega) h
    rw [stopsOf_getElem, stopsOf_getElem] at this
    exact this
  · exact le_rfl

/-- **At most two stops share an offset.** -/
theorem stops_two (hP : J.P.Simple) (hN : IsNF (chainModel J.right) (Qof P) N₂)
    {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hst : StopsOK J (N₂.F (chainModel J.right) (Qof P)) (stopsOf J (Qof P) N₂ rs)) {i : ℕ}
    (hi : i + 2 < rs.length) :
    soff P J (rs[i]'(by omega)) < soff P J rs[i + 2] := by
  set S₂ := N₂.F (chainModel J.right) (Qof P) with hS₂d
  have hS₂  := hN.1.2.1
  have hS₂f  := hN.1.1
  have hC := corr_right0 J hP hS₂ hS₂f
  have h01 := stops_sorted hst (i := i) (i' := i + 1) (by omega) (by omega)
  have h12 := stops_sorted hst (i := i + 1) (i' := i + 2) (by omega) (by omega)
  by_contra hlt
  push Not at hlt
  have e01 : soff P J (rs[i]'(by omega)) = soff P J (rs[i + 1]'(by omega)) := by linarith
  have e02 : soff P J (rs[i]'(by omega)) = soff P J rs[i + 2] := by linarith
  obtain ⟨f0, -, a0, -⟩ := stop_facts hst (i := i) (by omega)
  obtain ⟨f1, -, a1, -⟩ := stop_facts hst (i := i + 1) (by omega)
  obtain ⟨f2, -, a2, -⟩ := stop_facts hst (i := i + 2) (by omega)
  obtain ⟨p01, t01⟩ := pos_eq_of_oW hP hS₂ hS₂f a0.1 a1.1 a0.2.1 a0.2.2.1 a1.2.1 a1.2.2.1 e01
  obtain ⟨p02, t02⟩ := pos_eq_of_oW hP hS₂ hS₂f a0.1 a2.1 a0.2.1 a0.2.2.1 a2.2.1 a2.2.2.1 e02
  -- the chords are pairwise distinct (no duplicate stops)
  have hl : (stopsOf J (Qof P) N₂ rs).length = rs.length := by simp [stopsOf]
  have hnd := hst.2.2.2
  have dist : ∀ a b (ha : a < rs.length) (hb : b < rs.length), a ≠ b →
      (rs[a]).1 = (rs[b]).1 →
      (chainModel J.whole).param (Qof P) ⟨(rs[a]).1, (rs[a]).2.1⟩ =
        (chainModel J.whole).param (Qof P) ⟨(rs[b]).1, (rs[b]).2.1⟩ →
      stopSet J (Qof P) N₂ (rs[a]).2.2.1 (rs[a]).2.2.2.1 (rs[a]).2.2.2.2 ≠
        stopSet J (Qof P) N₂ (rs[b]).2.2.1 (rs[b]).2.2.2.1 (rs[b]).2.2.2.2 := by
    intro a b ha hb hab h1 h2 h3
    apply hab
    have := (List.Nodup.getElem_inj_iff hnd (hi := by rw [hl]; exact ha) (hj := by rw [hl]; exact hb)).1 (by
      rw [stopsOf_getElem ha, stopsOf_getElem hb, h2, h1, h3])
    exact this
  have d01 := dist i (i + 1) (by omega) (by omega) (by omega) p01 t01
  have d02 := dist i (i + 2) (by omega) (by omega) (by omega) p02 t02
  have d12 := dist (i + 1) (i + 2) (by omega) (by omega) (by omega) (p01.symm.trans p02)
    (t01.symm.trans t02)
  rw [← t01, ← p01] at a1
  rw [← t02, ← p02] at a2
  rcases tie_third hC.hM hC.hF f0 f1 f2 d01 a0 a1 a2 with h | h
  · exact d02 h.symm
  · exact d12 h.symm

end Stops

/-! ## Labels -/

theorem evSideLab_mono {J : Merge.Junction} {S₂ : Set (Set Point)} {Λ Λ' : Set (Set Point)}
    {Z : Set Point} (h : Λ ⊆ Λ') (hl : EvSideLab J S₂ Λ Z) : EvSideLab J S₂ Λ' Z :=
  fun G hG ρ hρ hS => by
    obtain ⟨L, hL, h2, h3⟩ := hl G hG ρ hρ hS
    exact ⟨L, hL.imp (fun x => h x) id, h2, h3⟩

/-- The walk edge of the vertex at the end of the right stretch in the walk of `C₂`. -/
noncomputable def vEnd (J : Merge.Junction) : ℕ :=
  (6 + tpos J.right 0 + (dq (rL1 J) (rδ J) (rL1 J + rL2 J - 1) + 1)) %
    (chainModel J.right).W.n

/-- The start key. -/
noncomputable def pK0 (J : Merge.Junction) : ℕ := (gW J + Lst J) % (chainModel J.whole).W.n

/-! ## The invariant at the start -/

/-- **The invariant at the start key.**  The label set contains the labels of every anchored stop
at the start key; if there is none, it is `{V}` for the region `V` faced before the end of the
right stretch. -/
theorem evInv_start {P : Polygon} {J : Merge.Junction} {N₂ : NF} (hP : J.P.Simple)
    (hN : IsNF (chainModel J.right) (Qof P) N₂) {rs ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hlen : ax.length = rs.length)
    (hst : StopsOK J (N₂.F (chainModel J.right) (Qof P)) (stopsOf J (Qof P) N₂ rs))
    (haux : ∀ i (hi : i < rs.length), AuxOK P J N₂
      (stopSet J (Qof P) N₂ (rs[i]).2.2.1 (rs[i]).2.2.2.1 (rs[i]).2.2.2.2) (ax[i]'(by omega)))
    {Λ : Set (Set Point)}
    (hΛ : ∀ i (hi : i < rs.length), soff P J rs[i] = Lst J → (ax[i]'(by omega)).1 = 1 →
      labSet J (Qof P) N₂ (ax[i]'(by omega)).2.1 (ax[i]'(by omega)).2.2.1
        (ax[i]'(by omega)).2.2.2.1 0 0 ⊆ Λ)
    (hB : (∀ i (hi : i < rs.length), soff P J rs[i] = Lst J → (ax[i]'(by omega)).1 ≠ 1) →
      ∃ V ∈ (chainModel J.right).regions (N₂.F (chainModel J.right) (Qof P)),
        BeforeFaces (chainModel J.right) (vEnd J) 0 V ∧ Λ = {V}) :
    EvInv J (N₂.F (chainModel J.right) (Qof P)) (Lst J) Λ := by
  set S₂ := N₂.F (chainModel J.right) (Qof P) with hS₂d
  have hS₂  := hN.1.2.1
  have hS₂f  := hN.1.1
  have hC := corr_right0 J hP hS₂ hS₂f
  obtain ⟨Q', hQ₂, hQF⟩ := chordFamily_pair J hS₂ hS₂f
  obtain ⟨⟨hpKn, -, -⟩, hoK, hstop⟩ := startMathTask P J N₂ hP hN
  set pK := (gW J + Lst J) % (chainModel J.whole).W.n with hpKd
  have hoK' : oW J ((pK : ℝ) + 0) = Lst J := by exact_mod_cast hoK
  have hL0 := Lst_pos J
  -- every chord at the start key is a stop at the start key
  have atKey : ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK 0 →
      ∃ i, ∃ hi : i < rs.length, soff P J rs[i] = Lst J ∧
        stopSet J (Qof P) N₂ (rs[i]).2.2.1 (rs[i]).2.2.2.1 (rs[i]).2.2.2.2 = e := by
    intro e he hA
    have hmem := hst.2.1 e he (hstop e he hA) pK 0 hA (by rw [hoK'])
    obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.1 hmem
    have hk' : k < rs.length := by simpa [stopsOf] using hk
    rw [stopsOf_getElem hk'] at hkx
    simp only [Prod.mk.injEq] at hkx
    obtain ⟨h1, h2, h3⟩ := hkx
    refine ⟨k, hk', ?_, h3⟩
    unfold soff
    rw [h2, h1]
    exact hoK'
  -- a stop at the start key is attached at the start key
  have stopAt : ∀ i (hi : i < rs.length), soff P J rs[i] = Lst J →
      SideAttach (chainModel J.whole).W
        (stopSet J (Qof P) N₂ (rs[i]).2.2.1 (rs[i]).2.2.2.1 (rs[i]).2.2.2.2) pK 0 := by
    intro i hi ho
    obtain ⟨-, -, hA, -⟩ := stop_facts hst hi
    have e : soff P J rs[i] = oW J ((pK : ℝ) + 0) := by rw [ho, hoK']
    obtain ⟨h1, h2⟩ := pos_eq_of_oW hP hS₂ hS₂f hA.1 hpKn hA.2.1 hA.2.2.1 le_rfl one_pos e
    rw [h2, h1] at hA
    exact hA
  by_cases hanc : ∃ i, ∃ hi : i < rs.length, soff P J rs[i] = Lst J ∧ (ax[i]'(by omega)).1 = 1
  · obtain ⟨i₀, hi₀, ho₀, ha₀⟩ := hanc
    have hZ := (stop_facts hst hi₀).1
    have hZK := stopAt i₀ hi₀ ho₀
    have hZb : ¬ EvBrk J (stopSet J (Qof P) N₂ (rs[i₀]).2.2.1 (rs[i₀]).2.2.2.1
        (rs[i₀]).2.2.2.2) := ((haux i₀ hi₀).2.1).1 ha₀
    rw [← hoK']
    by_cases hpock : ∃ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK 0 ∧
        ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s ∧ oW J (q + s) = 0
    · obtain ⟨e, he, heK, q, s, hQ, hQ0⟩ := hpock
      have hne : sidePt (chainModel J.whole).W pK 0 ≠ sidePt (chainModel J.whole).W q s := by
        intro h
        obtain ⟨rfl, rfl⟩ := hC.hM.attach_unique (hC.hF he) heK hQ h
        rw [hoK'] at hQ0
        linarith
      exact evInv_pocket he heK hQ hne (by rw [hoK']) hQ0 Λ
    push Not at hpock
    unfold EvBrk at hZb
    push Not at hZb
    obtain ⟨pz, tz, hZz, hzL⟩ := hZb
    exact evInv_anchor hP hQ₂ hQF (noTieV hP hS₂) hpKn le_rfl one_pos (by rw [hoK']) hZ hZK hZz
      hzL (fun e he heK q s hQ => hpock e he heK q s hQ) (fun e he heK hnb _ => by
        obtain ⟨j, hj, hoj, rfl⟩ := atKey e he heK
        have haj  := ((haux j hj).2.1).2 hnb
        exact evSideLab_mono (hΛ j hj hoj haj)
          ((haux j hj).2.2.2.2.2.1 haj (fun q s hQ => hpock _ he heK q s hQ)))
  · push Not at hanc
    obtain ⟨V, hV, hW, rfl⟩ := hB hanc
    refine startTask J Q' S₂ hP hQ₂ hQF (fun e he hA => ?_) V hV hW
    obtain ⟨j, hj, hoj, rfl⟩ := atKey e he hA
    by_contra hb
    exact hanc j hj hoj (((haux j hj).2.1).2 hb)

end

end SweepEv

end Chazelle.Core
