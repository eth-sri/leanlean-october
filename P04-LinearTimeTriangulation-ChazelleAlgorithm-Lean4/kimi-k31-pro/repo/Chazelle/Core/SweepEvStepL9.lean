module

public import Chazelle.Core.SweepEvStepL8
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
set_option maxHeartbeats 2000000

/-!
# The sweep (WP-D), stage 3: the endpoint table at the next key (Task L1)

**`SCtx.tab'`**: the table up to the next key.  A slot is the one of the key, or holds an accepted
triple; a valid query whose chord ends beyond the key and not beyond the next key ends at the next
key (no cut in between), so its chord is a non-stop chord at the next key, accepted by the batch.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)

@[expose] public section

namespace SCtx

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config} {A : Set (ℕ × ℕ × ℕ)} {rs ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
  (S : SCtx sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' A rs ax)
include S

/-- **A valid query ending beyond the key, not beyond the next key, is accepted.** -/
theorem comp_new {j : ℕ} (hj : j < 2 * N₂.nChords) (hv : ValidJ J (Qof P) N₂ j)
    (hlt' : J.whole.hitParam (endOrigin J (Qof P) N₂ j) (endDir j) <
      J.right.hitParam (endOrigin J (Qof P) N₂ j) (endDir j)) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W
      (Merge.shoot J.whole (endOrigin J (Qof P) N₂ j) (endDir j)) p t)
    (h1 : keyOff P J c < oW J (p + t)) (h2 : oW J (p + t) ≤ keyOff P J c') :
    ∃ t' ∈ A, t'.1 = j := by
  have hP := S.E.hP
  have hS₂a  := S.E.hNF₂.1.2.1
  obtain ⟨hc, ha⟩ := query_chord (J := J) (Q := Qof P) hj
  obtain ⟨haR, hav, hat⟩ := hv
  obtain ⟨-, hfree, -⟩ := origin_hit hP (hS₂a hc) ha haR hav hlt'
  have he := shoot_end_mem hc ha hfree
  have heq : oW J (p + t) = keyOff P J c' := by
    rcases h2.lt_or_eq with h | h
    · exact absurd ⟨h1, h⟩ (S.gapK _ he p t hA)
    · exact h
  obtain ⟨e1, e2⟩ := S.posEq hA.1 hA.2.1 hA.2.2.1 heq
  rw [e1, e2] at hA
  have hns := origin_not_stop hP hS₂a (hS₂a hc) ha haR hav hat hlt'
  obtain ⟨t', ht', -, hte, -⟩ := S.nonstop_acc he hA hns
  refine ⟨t', ht', ?_⟩
  obtain ⟨-, hj', -, -, -, -, -, -, hl'⟩ := S.hBA.acc t' ht'
  obtain ⟨haR', hav', hat'⟩ := S.hval t' ht'
  exact (originTask J (Qof P) N₂ hP S.E.hNF₂ (F₂plus_chordFamily S.E)).2 t'.1 j hj' hj
    haR' hav' hat' hl' haR hav hat hlt' hte

/-- **The table up to the next key.** -/
theorem tab' : TabInv P J N₂ c' (keyOff P J c') := by
  have hsome := stp_key_some S.hI S.hd
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmK⟩ :=
    S.hI.2.2.2.2.2.2.2 hsome
  obtain ⟨hW, -, hR, -, -⟩ := S.hI
  obtain ⟨hkp, hmemS, -, -⟩ := stp_pre_frame hW hR
  have eTBs : cs.nreg cTB = c.nreg cTB := hkp 661 (by omega)
  have eTB' : c'.nreg cTB = c.nreg cTB := stp_iter_keep S.hI (k := 661) (by omega)
  have elB : co.nreg lB = c.nreg lB := stp_co_keep S.hI (k := 2430) (by omega)
  have elC : co.nreg lC = c.nreg lC := stp_co_keep S.hI (k := 2431) (by omega)
  have hAl := (stp_alloc_mono S.hI).1
  have l1 := S.L.lay1
  have l2 := S.L.lay2
  have l4 := S.L.lay4
  have hTc : ∀ x, x < c.nreg cTB + 6 * N₂.nChords → c'.nmem x = co.nmem x := fun x hx =>
    hmK x (by omega) (Or.inl (by rwo [elB, elC]))
  have hTs : ∀ x, x < c.nreg cTB + 6 * N₂.nChords → cs.nmem x = c.nmem x := fun x hx =>
    hmemS x (by omega)
  have hlt := (stp_next_key S.E S.L S.hI S.hd).1
  intro j hj
  rw [eTB']
  obtain ⟨o0, o1, o2⟩ := S.L.tab j hj
  have hslot := S.hBA.slot j hj
  rw [eTBs] at hslot
  have hT0 : c'.nmem (c.nreg cTB + 3 * j) = co.nmem (c.nreg cTB + 3 * j) := hTc _ (by omega)
  have hT1 : c'.nmem (c.nreg cTB + 3 * j + 1) = co.nmem (c.nreg cTB + 3 * j + 1) :=
    hTc _ (by omega)
  have hT2 : c'.nmem (c.nreg cTB + 3 * j + 2) = co.nmem (c.nreg cTB + 3 * j + 2) :=
    hTc _ (by omega)
  rw [hT0, hT1, hT2]
  -- a flag of the key stays
  have hkeep : c.nmem (c.nreg cTB + 3 * j) = 1 → co.nmem (c.nreg cTB + 3 * j) = 1 := by
    intro h
    rcases hslot with ⟨s0, -, -⟩ | ⟨e, h', -, f0, -⟩
    · rw [s0, hTs _ (by omega), h]
    · exact f0
  refine ⟨?_, ?_, fun hv hlt' p t hA hpt hL hle => ?_⟩
  · rcases hslot with ⟨s0, -, -⟩ | ⟨e, h', -, f0, -⟩
    · rwx [s0, hTs _ (by omega)]
    · rw [f0]
  · intro hf
    rcases hslot with ⟨s0, s1, s2⟩ | ⟨e, h', hmA, f0, f1, f2⟩
    · rw [s0, hTs _ (by omega)] at hf
      rw [s1, s2, hTs _ (by omega), hTs _ (by omega)]
      exact o1 hf
    · rw [f1, f2]
      exact (S.hBA.acc _ hmA).2.2
  · by_cases hc : oW J (p + t) ≤ keyOff P J c
    · exact hkeep (o2 hv hlt' p t hA hpt hL hc)
    · obtain ⟨t', ht', rfl⟩ := S.comp_new hj hv hlt' hA (not_le.1 hc) hle
      have := S.hBA.flag t' ht'
      rwa [eTBs] at this

end SCtx

end

end SweepEv

end Chazelle.Core
