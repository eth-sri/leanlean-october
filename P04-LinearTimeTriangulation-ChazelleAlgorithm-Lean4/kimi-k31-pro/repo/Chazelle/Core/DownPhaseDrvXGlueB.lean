module

public import Chazelle.Core.DownPhaseDrvXContracts
public import Chazelle.Core.DownPhaseDrvXPos2
public import Chazelle.Core.DownPhaseDrvXKept
public import Chazelle.Rwx
public import Chazelle.UnfoldTactics

/-!
# Down phase, extraction (D6): glue B (`PostMath`)

For the hypotheses `XHyp` of a region and values `v` agreeing with the chain, the bit `li` and the
host, the triple list `xL P v NR #chords` (the triples `xT` of the kept records `kl`) describes the
kept chords exactly (`XCtx.kept_iff`, `XCtx.kept_pos`), without repetition (the records of `NR`
have distinct chords), attached in the interior model, in range, and with every end on the closure
of an arc of the region.

* `mem_kl`, `kl_nodup`: the kept record list;
* **`postMath : PostMath`**.
-/

namespace Chazelle.Core

namespace DrvX

open Set
open BuildNF (buildNF)
open DrvR (regHost OnArcKey endPos)

@[expose] public section

section GlueB

variable {P : Polygon} {v : XV} {NR : NF}

/-- Membership in the kept record list. -/
theorem mem_kl {i t : ℕ} : t ∈ kl P v NR i ↔ t < i ∧ kR P v (NR.chord t) := by
  ufs kl

/-- The kept record list has no repetition. -/
theorem kl_nodup (i : ℕ) : (kl P v NR i).Nodup := List.nodup_range.filter _

/-- The chord record `t < #chords` is a member of the record list. -/
theorem chord_mem_chords {t : ℕ} (ht : t < NR.chords.length) : NR.chord t ∈ NR.chords := by
  unfold NF.chord; rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht

end GlueB

/-- **Glue B**: the triples of the kept chord records describe the kept chords. -/
theorem postMath : PostMath := by
  intro P li L E reg r C NR v X hm hT hβ hli hH
  obtain ⟨i0, g, Y⟩ := X.ctx
  set K := NR.chords.length with hKdef
  -- the values agree with the chain, the bit and the host
  have hxT : ∀ t, xT P v NR t = xTriple (Qof P).n
      (regHost li (Qof P).n (buildNF (interiorModel (Qof P)) (Qof P) L E) r) li C.m C.topIdx
      C.sideBeta (NR.chord t).h (NR.chord t).lp (NR.chord t).rp := by
    intro t; unfold xT; rw [hm, hT, hβ, hli, hH]
  have hkR : ∀ t, t < NR.nChords → (kR P v (NR.chord t) ↔
      ((NR.chord t).toSet (chainModel C) (Qof P) ∩ reg r).Nonempty) := by
    intro t ht; unfold kR; rw [hm, hT, hβ, hli, hH]; exact Y.kept_iff ht
  -- the facts of a kept record
  have hset : ∀ t ∈ kl P v NR K, (recOf (xT P v NR t)).toSet (interiorModel (Qof P)) (Qof P) =
      (NR.chord t).toSet (chainModel C) (Qof P) := by
    intro t ht
    obtain ⟨htK, hk⟩ := mem_kl.1 ht
    rw [hxT]
    exact (Y.kept_pos htK ((hkR t htK).1 hk)).1
  have hatt : ∀ t ∈ kl P v NR K, (recOf (xT P v NR t)).Attached (interiorModel (Qof P)) (Qof P) ∧
      (xT P v NR t).1 < (Qof P).n := by
    intro t ht
    obtain ⟨htK, hk⟩ := mem_kl.1 ht
    rw [hxT]
    have hp := Y.kept_pos htK ((hkR t htK).1 hk)
    exact ⟨hp.2.1, hp.2.2.1⟩
  have hon : ∀ t ∈ kl P v NR K,
      (∃ j ∈ ((buildNF (interiorModel (Qof P)) (Qof P) L E).region r).arcs,
        OnArcKey (Qof P) (buildNF (interiorModel (Qof P)) (Qof P) L E) j
          (recOf (xT P v NR t)).lpos) ∧
      (∃ j ∈ ((buildNF (interiorModel (Qof P)) (Qof P) L E).region r).arcs,
        OnArcKey (Qof P) (buildNF (interiorModel (Qof P)) (Qof P) L E) j
          (recOf (xT P v NR t)).rpos) := by
    intro t ht
    obtain ⟨htK, hk⟩ := mem_kl.1 ht
    rw [hxT]
    have hp := Y.kept_pos htK ((hkR t htK).1 hk)
    exact ⟨hp.2.2.2.2.2.1, hp.2.2.2.2.2.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the kept chords
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      unfold xL at hy
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
      obtain ⟨htK, hk⟩ := mem_kl.1 ht
      rw [hset t ht]
      exact ⟨⟨NR.chord t, chord_mem_chords htK, rfl⟩, (hkR t htK).1 hk⟩
    · rintro ⟨⟨c, hc, rfl⟩, hne⟩
      obtain ⟨t, htK, rfl⟩ := List.getElem_of_mem hc
      have hct : NR.chord t = NR.chords[t] := by
        unfold NF.chord; rw [List.getD_eq_getElem _ _ htK]
      have ht : t ∈ kl P v NR K := mem_kl.2 ⟨htK, (hkR t htK).2 (by rwx [hct])⟩
      refine ⟨xT P v NR t, List.mem_map.2 ⟨t, ht, rfl⟩, ?_⟩
      rw [hset t ht, hct]
  · -- no repetition
    have e : (xL P v NR K).map (fun y => (recOf y).toSet (interiorModel (Qof P)) (Qof P)) =
        (kl P v NR K).map (fun t => (NR.chord t).toSet (chainModel C) (Qof P)) := by
      unfold xL
      rw [List.map_map]
      exact List.map_congr_left hset
    rw [e]
    exact (kl_nodup K).map_on fun t ht t' ht' h =>
      X.hNR.2.1 t t' (mem_kl.1 ht).1 (mem_kl.1 ht').1 h
  · -- attached, in range
    intro y hy
    unfold xL at hy
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
    exact hatt t ht
  · -- the ends on arcs of the region
    intro q hq
    have hlen : (xL P v NR K).length = (kl P v NR K).length := by
      unfold xL; rw [List.length_map]
    have hq2 : q / 2 < (kl P v NR K).length := by omega
    have ht  := List.getElem_mem hq2
    have hget : (xL P v NR K).getD (q / 2) (0, 0, 0) = xT P v NR ((kl P v NR K)[q / 2]) := by
      unfold xL
      rw [List.getD_eq_getElem _ _ (by rwx [List.length_map]), List.getElem_map]
    unfold endPos
    rw [hget]
    split_ifs
    · exact (hon _ ht).1
    · exact (hon _ ht).2

end

end DrvX

end Chazelle.Core
