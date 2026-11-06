module

public import Chazelle.Core.SweepEvStepL4

/-!
# The sweep (WP-D), stage 3: the chords at the next key (Task L1)

`SCtx`: the context of one iteration that does not finish (the environment, the invariant at
`c`, the iteration, a set `A` of accepted triples of the batch, their valid origins, the stop
records `rs`, `ax` of `c`).  At the next key `K' = (pK, tK)` (offset `o'`):

* `SCtx.stop_idx`: a stop chord at `K'` is a stop skipped by the next-key step;
* `SCtx.skip_at`: a skipped stop is attached at `K'`;
* `SCtx.nonstop_acc`: a non-stop chord at `K'` is the chord of an accepted triple at `o'`, and the
  best candidate is at `o'`;
* `SCtx.triple_at`: the chord of an accepted triple at `o'` is attached at `K'`, is not a stop
  chord and is anchored.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- **The context of one iteration that does not finish.** -/
structure SCtx (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction)
    (N₁ N₂ : NF) (c cw cs co c' : Config) (A : Set (ℕ × ℕ × ℕ))
    (rs ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : Prop where
  E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂
  L : LoopInv P J N₁ N₂ c₀ c
  hI : IterRel P J N₁ N₂ c cw cs co c'
  hd : c'.nreg dF = 0
  hBA : BatchA P J N₂ cs
    (ShotList.loSet (chainModel J.left) (Qof P) cs.nmem (cs.nreg wGB) (cs.nreg wGK) [])
    (iterO N₂ cs) co A
  hval : ∀ t ∈ A, ValidJ J (Qof P) N₂ t.1
  hD : StopData P J N₂ c rs ax

namespace SCtx

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config} {A : Set (ℕ × ℕ × ℕ)} {rs ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
  (S : SCtx sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' A rs ax)
include S

/-- The parameter of the next key. -/
theorem posK : c'.nreg kE < (chainModel J.whole).W.n ∧
    0 ≤ (chainModel J.whole).param (Qof P) ⟨c'.nreg kE, c'.nreg kH⟩ ∧
    (chainModel J.whole).param (Qof P) ⟨c'.nreg kE, c'.nreg kH⟩ < 1 :=
  let h := (stp_next_key S.E S.L S.hI S.hd).2.1
  ⟨h.1, h.2.1.1, h.2.1.2.1⟩

/-- No cut strictly between the key and the next key. -/
theorem gapK : ∀ e ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P)), ∀ (q : ℕ) (s : ℝ),
    SideAttach (chainModel J.whole).W e q s →
      ¬ (keyOff P J c < oW J (q + s) ∧ oW J (q + s) < keyOff P J c') := by
  intro e he q s hA
  exact no_cut_iter S.E S.L S.hI (q + s) ⟨e, he, q, s, hA, rfl⟩ (by have := hA.2.1; positivity)
    (by have := hA.2.2.1; have : ((q : ℕ) : ℝ) + 1 ≤ (chainModel J.whole).W.n := by
          exact_mod_cast hA.1
        linarith)

/-- A position at the offset of the next key is the next key. -/
theorem posEq {q : ℕ} {s : ℝ} (hq : q < (chainModel J.whole).W.n) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (h : oW J (q + s) = keyOff P J c') :
    q = c'.nreg kE ∧ s = (chainModel J.whole).param (Qof P) ⟨c'.nreg kE, c'.nreg kH⟩ := by
  obtain ⟨h1, h2, h3⟩ := S.posK
  exact pos_eq_of_oW S.E.hP S.E.hNF₂.1.2.1 S.E.hNF₂.1.1 hq h1 hs0 hs1 h2 h3 h

/-- The stop offsets read from the records. -/
theorem stopOff_rs {i : ℕ} (hi : i < rs.length) :
    stopOff P J c i = soff P J rs[i] := by
  obtain ⟨-, -, hrec, -⟩ := S.hD
  obtain ⟨e0, e1, -⟩ := hrec i hi
  rw [List.getD_eq_getElem _ _ hi] at e0 e1
  show offK P J (c.nmem (c.nreg sB + 5 * i)) (c.nmem (c.nreg sB + 5 * i + 1)) = _
  aesop

/-- **A skipped stop is attached at the next key.** -/
theorem skip_at {i : ℕ} (h1 : c.nreg sP ≤ i) (h2 : i < c'.nreg sP) :
    ∃ hi : i < rs.length,
      stopSet J (Qof P) N₂ rs[i].2.2.1 rs[i].2.2.2.1 rs[i].2.2.2.2 ∈
        F₂plus J (N₂.F (chainModel J.right) (Qof P)) ∧
      StopChord2 J (N₂.F (chainModel J.right) (Qof P))
        (stopSet J (Qof P) N₂ rs[i].2.2.1 rs[i].2.2.2.1 rs[i].2.2.2.2) ∧
      SideAttach (chainModel J.whole).W
        (stopSet J (Qof P) N₂ rs[i].2.2.1 rs[i].2.2.2.1 rs[i].2.2.2.2) (c'.nreg kE)
        ((chainModel J.whole).param (Qof P) ⟨c'.nreg kE, c'.nreg kH⟩) ∧
      rs[i].1 = c'.nreg kE ∧ (chainModel J.whole).param (Qof P) ⟨rs[i].1, rs[i].2.1⟩ =
        (chainModel J.whole).param (Qof P) ⟨c'.nreg kE, c'.nreg kH⟩ := by
  obtain ⟨-, hle, -, hk3⟩ := stp_ptr_c' S.E S.L S.hI S.hd
  obtain ⟨-, -, esC', -, -⟩ := stp_arrays_c' S.E S.L S.hI S.hd
  have hlen := S.hD.1
  have hi : i < rs.length := by omega
  refine ⟨hi, ?_⟩
  obtain ⟨f0, f1, a0, -⟩ := stop_facts S.hD.2.2.2.2.1 hi
  have ho := hk3 i h1 h2
  rw [S.stopOff_rs hi] at ho
  obtain ⟨e1, e2⟩ := S.posEq a0.1 a0.2.1 a0.2.2.1 ho
  simp_all

section
variable {e : Set Point} (he : e ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P))) (hA : SideAttach (chainModel J.whole).W e (c'.nreg kE)
      ((chainModel J.whole).param (Qof P) ⟨c'.nreg kE, c'.nreg kH⟩))
include he hA
/-- **A stop chord at the next key is a skipped stop.** -/
theorem stop_idx
    (hs : StopChord2 J (N₂.F (chainModel J.right) (Qof P)) e) :
    ∃ i, ∃ hi : i < rs.length, c.nreg sP ≤ i ∧ i < c'.nreg sP ∧
      stopSet J (Qof P) N₂ rs[i].2.2.1 rs[i].2.2.2.1 rs[i].2.2.2.2 = e := by
  obtain ⟨hlt, -, -⟩ := stp_next_key S.E S.L S.hI S.hd
  obtain ⟨hlen, -, -, -, hok, -⟩ := S.hD
  have hL : (Lst J : ℝ) ≤ oW J (c'.nreg kE +
      (chainModel J.whole).param (Qof P) ⟨c'.nreg kE, c'.nreg kH⟩) := by
    have := S.L.keyL
    show (Lst J : ℝ) ≤ keyOff P J c'
    linarith
  have hmem := hok.2.1 e he hs _ _ hA hL
  obtain ⟨r, hr, hreq⟩ := List.mem_map.1 hmem
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  simp only [Prod.mk.injEq] at hreq
  obtain ⟨h1, h2, h3⟩ := hreq
  have ho : stopOff P J c i = keyOff P J c' := by
    rw [S.stopOff_rs hi]
    unfold soff
    rw [h2, h1]
    rfl
  have hic : i < c.nreg sC := hlen ▸ hi
  obtain ⟨-, -, hptr, -⟩ := stp_ptr_c' S.E S.L S.hI S.hd
  obtain ⟨-, -, esC', -, -⟩ := stp_arrays_c' S.E S.L S.hI S.hd
  have hso := (stp_stops_c' S.E S.L S.hI S.hd).2 i hic
  refine ⟨i, hi, ?_, ?_, h3⟩
  · by_contra h
    have := (S.L.ptrL i hic).1 (by omega)
    linarith
  simp_all

/-- **A non-stop chord at the next key** is the chord of an accepted triple at its offset, and
the best candidate is there. -/
theorem nonstop_acc
    (hs : ¬ StopChord2 J (N₂.F (chainModel J.right) (Qof P)) e) :
    ∃ t ∈ A, offT P J t = keyOff P J c' ∧
      Merge.shoot J.whole (endOrigin J (Qof P) N₂ t.1) (endDir t.1) = e ∧
      co.nreg bF = 1 ∧ offK P J (co.nreg bE) (co.nreg bH) = keyOff P J c' := by
  obtain ⟨hlt, -, -⟩ := stp_next_key S.E S.L S.hI S.hd
  obtain ⟨-, -, -, ewX, ewE, ewH⟩ := iter_stops S.L S.hI
  have hsome := stp_key_some S.hI S.hd
  obtain ⟨hW, -, hR, -, hK⟩ := S.hI
  obtain ⟨hkp, -, -, -⟩ := stp_pre_frame hW hR
  have ekE : cs.nreg kE = c.nreg kE := hkp 2400 (by omega)
  have ekH : cs.nreg kH = c.nreg kH := hkp 2401 (by omega)
  obtain ⟨-, -, hKb, -, hKw, -⟩ := hK.2.2.2 hsome
  obtain ⟨k, hk, a, σ, ha, haR, hav, hat, hfree, rfl, hlt', j, hj, hjk, hjO, hjD, h, hh, hmA⟩ :=
    stp_accepted_of_found S.E S.L hW hR S.hBA he hA hlt S.gapK hs (fun h0 => by
      have := hKw (by omega)
      rw [ewE, ewH] at this
      exact this)
  have hoT : offT P J (j, c'.nreg kE, h) = keyOff P J c' := by
    show oW J (_ + (chainModel J.whole).param (Qof P) ⟨_, h⟩) = _
    rw [hh]
    rfl
  obtain ⟨hbF, hle⟩ := S.hBA.bMin _ hmA (by rw [hoT, ekE, ekH]; exact hlt)
  have hge := hKb hbF
  exact ⟨_, hmA, hoT, by simp_all, hbF, le_antisymm (hle.trans hoT.le) hge⟩


end

/-- **The chord of an accepted triple at the offset of the next key** is attached there, is not
a stop chord and is anchored. -/
theorem triple_at {t : ℕ × ℕ × ℕ} (ht : t ∈ A) (hto : offT P J t = keyOff P J c') :
    Merge.shoot J.whole (endOrigin J (Qof P) N₂ t.1) (endDir t.1) ∈
        F₂plus J (N₂.F (chainModel J.right) (Qof P)) ∧
      SideAttach (chainModel J.whole).W
        (Merge.shoot J.whole (endOrigin J (Qof P) N₂ t.1) (endDir t.1)) (c'.nreg kE)
        ((chainModel J.whole).param (Qof P) ⟨c'.nreg kE, c'.nreg kH⟩) ∧
      ¬ StopChord2 J (N₂.F (chainModel J.right) (Qof P))
        (Merge.shoot J.whole (endOrigin J (Qof P) N₂ t.1) (endDir t.1)) ∧
      ¬ EvBrk J (Merge.shoot J.whole (endOrigin J (Qof P) N₂ t.1) (endDir t.1)) := by
  have hP := S.E.hP
  obtain ⟨-, hj, hfree, hmemF, hAt, -, -, hpw, hlt'⟩ := S.hBA.acc t ht
  obtain ⟨haR, hav, hat⟩ := S.hval t ht
  obtain ⟨hc, ha⟩ := query_chord (J := J) (Q := Qof P) hj
  have hS₂a : N₂.F (chainModel J.right) (Qof P) ⊆ Merge.augChords J.right := S.E.hNF₂.1.2.1
  obtain ⟨e1, e2⟩ := S.posEq hpw.1 hpw.2.1.1 hpw.2.1.2.1 hto
  refine ⟨hmemF, by simp_all,
    origin_not_stop hP hS₂a (hS₂a hc) ha haR hav hat hlt', fun hbr => ?_⟩
  have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
  have haD : endOrigin J (Qof P) N₂ t.1 ∉ J.whole.dom := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd (J.right_set_subset haR)
  obtain ⟨q, s, hq, hqpt⟩ := endpoint_attach hM (F₂plus_subset J hS₂a hmemF) (origin_mem J) haD
  have := off_right_pt J hP (S₂ := ∅) (empty_subset _) finite_empty hq.1 hq.2.1 hq.2.2.1
    (by simp_all) (by simp_all)
  rw [← oW_eq, ← Lst_eq] at this
  have := hbr q s hq
  linarith

end SCtx

end

end SweepEv

end Chazelle.Core
