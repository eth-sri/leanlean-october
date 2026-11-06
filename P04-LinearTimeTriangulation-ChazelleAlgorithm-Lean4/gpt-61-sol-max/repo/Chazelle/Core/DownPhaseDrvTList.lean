module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvTPiece
public import Chazelle.Core.NFBuildValid
public import Chazelle.Core.DownPhaseMathLevel
public import Chazelle.Core.DownPhaseMathCount

/-!
# Down-phase transition (D2), part 4: the filtered chord list

For the canonical normal form `N` of the top chain `C` of `Q = Qof P`, the RAM filter outputs
`transL li n c₀ (triplesOf N)`: the kept triples (`keepT`), mapped (`trT`).  Then:

* `famOf_transL`: its chords are exactly the pieces `Trans.pieces Q (N.F …)` (T-R1);
* `chordTriplesOK_transL`: it is a valid chord list of the interior model (distinct, attached,
  admissible chords; T-R2);
* `transL_length_le`: it is not longer than the chord list of `N`, and `ncard_F`: the family
  of `N` has as many chords as `N` has records;
* **`trans_math`**: with the transition theorem (`Trans.transition`) and Lemma 2.3 for the top
  chain (`DownMath.trans_count`): (I1) degree `≤ 4`, (I2) weight `≤ 2^(⌈βp⌉+12)`, and the count
  bound of `DownMath.cnt_trans`.
-/

namespace Chazelle.Core

namespace DrvT

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sidePt IsHChordIn)
open Chazelle.Visibility (hseg)
open BuildRegions (famOf)

/-- The triples `(h, lp, rp)` of the chord records of a normal form. -/
def triplesOf (N : NF) : List (ℕ × ℕ × ℕ) := N.chords.map fun r => (r.h, r.lp, r.rp)

section
variable (li : Bool) (n c₀ : ℕ) (L₀ : List (ℕ × ℕ × ℕ))
include li n c₀ L₀
/-- **The output of the filter.** -/
def transL : List (ℕ × ℕ × ℕ) :=
  (L₀.filter (keepT li n c₀)).map (trT n c₀)

theorem transL_length_le :
    (transL li n c₀ L₀).length ≤ L₀.length := by
  core_grind


end

/-- The chords of the computed normal form are the chords of the list. -/
theorem F_buildNF (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) :
    (BuildNF.buildNF M Q L E).F M Q = famOf M Q L := by
  ext c
  simp only [NF.F, BuildNF.buildNF, List.mem_map, List.mem_range, famOf]
  constructor
  · rintro ⟨r, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨_, BuildOrder.getD_mem hi, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    refine ⟨_, ⟨i, hi, rfl⟩, ?_⟩
    aesop (add simp [List.getD_eq_getElem?_getD, Option.getD_some, BuildNF.chordRec]) (add safe (by omega))

/-- **Two chords of a domain containing the same nondegenerate segment are equal.** -/
theorem chord_eq_of_sub {D : Set Point} {y₁ a₁ b₁ y₂ a₂ b₂ y a b : ℝ}
    (h₁ : IsHChordIn D y₁ a₁ b₁) (h₂ : IsHChordIn D y₂ a₂ b₂) (hab : a < b)
    (s₁ : hseg y a b ⊆ hseg y₁ a₁ b₁) (s₂ : hseg y a b ⊆ hseg y₂ a₂ b₂) :
    hseg y₁ a₁ b₁ = hseg y₂ a₂ b₂ := by
  obtain ⟨ey₁, ha₁, hb₁⟩ := hseg_sub hab.le s₁
  obtain ⟨ey₂, ha₂, hb₂⟩ := hseg_sub hab.le s₂
  ram_grind

variable {P : Polygon} {C : Chain} {N : NF}

/-- The record of a triple has the chord and attachment of the record. -/
theorem recOf_triple (M : Model) (Q : Polygon) (r : CRec) :
    (recOf (r.h, r.lp, r.rp)).toSet M Q = r.toSet M Q := rfl

section
variable {Q : Polygon} (hN : IsNF (chainModel C) Q N)
include hN
/-- **The records of a valid chain normal form.** -/
theorem triples_props {x : ℕ × ℕ × ℕ}
    (hx : x ∈ triplesOf N) :
    x.1 < Q.n ∧ (recOf x).toSet (chainModel C) Q ∈ (chainModel C).Adm ∧
      (recOf x).Attached (chainModel C) Q ∧
      (recOf x).toSet (chainModel C) Q ∈ N.F (chainModel C) Q := by
  obtain ⟨hFam, -, hatt, reg, -, -, -, -, -, hh, -⟩ := hN
  unfold triplesOf at hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  have hci : N.chord i = N.chords[i] := by
    grind [NF.chord, List.getD_eq_getElem?_getD, Option.getD_some]
  have hmem : N.chords[i].toSet (chainModel C) Q ∈ N.F (chainModel C) Q :=
    ⟨_, List.getElem_mem hi, rfl⟩
  refine ⟨?_, hFam.2.1 hmem, ?_, hmem⟩
  · have := hh i hi; simp_all
  · have := hatt i hi; rw [hci] at this; exact this

/-- The chain chords of the records are pairwise distinct. -/
theorem nodup_triples_toSet :
    ((triplesOf N).map fun x => (recOf x).toSet (chainModel C) Q).Nodup := by
  obtain ⟨-, hdist, -⟩ := hN
  unfold triplesOf
  rw [List.map_map]
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  simp only [List.getElem_map, Function.comp] at hij
  have e1 : N.chord i.1 = N.chords[i.1]'(by ram_grind) := by
    unfold NF.chord
    ram_grind
  have e2 : N.chord j.1 = N.chords[j.1]'(by ram_grind) := by
    unfold NF.chord
    ram_grind
  have := hdist i.1 j.1 (by grind [NF.nChords])
    (by grind [NF.nChords]) (by rw [e1, e2]; exact hij)
  omega


end

/-- **The number of chords** of a valid normal form is its number of records. -/
theorem ncard_F {M : Model} {Q : Polygon} {N : NF}
    (hdist : ∀ i i', i < N.nChords → i' < N.nChords →
      (N.chord i).toSet M Q = (N.chord i').toSet M Q → i = i') :
    (N.F M Q).ncard = N.chords.length := by
  have hF : N.F M Q = {c | c ∈ N.chords.map fun r => r.toSet M Q} := by
    grind [NF.F, mem_ofPred_eq, List.mem_map]
  have hnd : (N.chords.map fun r => r.toSet M Q).Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro i j hij
    grind [List.getElem_map, NF.chord, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some, NF.nChords]
  rw [hF, show {c | c ∈ N.chords.map fun r => r.toSet M Q} =
      ((N.chords.map fun r => r.toSet M Q).toFinset : Set (Set Point)) by
    ext c; simp, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map]

section filt

variable {Q : Polygon}
variable (hQ : Q.Simple) (T : Trans.Top Q C) (hD : Trans.DistinctH Q) {li : Bool}
  (hli : li = true ↔ Mountain.LeftInside Q)
include hQ T hD hli

section
variable (hN : IsNF (chainModel C) Q N)
include hN
/-- **(T-R1) The chords of the filtered list are the pieces.** -/
theorem famOf_transL :
    famOf (interiorModel Q) Q (transL li Q.n (c0 C li) (triplesOf N)) =
      Trans.pieces Q (N.F (chainModel C) Q) := by
  have hmn := T.hm
  have hm1 := C.one_le
  have hh' : (Q.vtx C.m).2 ≠ (Q.vtx 0).2 := hD C.m 0 (by omega) (by omega) (by omega)
  ext d
  constructor
  · rintro ⟨x', hx', rfl⟩
    unfold transL at hx'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
    obtain ⟨hxm, hk⟩ := List.mem_filter.1 hx
    obtain ⟨h1, h2, h3, h4⟩ := triples_props hN hxm
    obtain ⟨hA, hsub, -⟩ := rec_kept hQ T hD hli h1 h2 h3 hk
    exact ⟨hA, _, h4, hsub⟩
  · rintro ⟨hdA, c, ⟨r, hr, rfl⟩, hdc⟩
    have hxm : (r.h, r.lp, r.rp) ∈ triplesOf N := List.mem_map.2 ⟨r, hr, rfl⟩
    obtain ⟨h1, h2, h3, -⟩ := triples_props hN hxm
    rw [← recOf_triple] at hdc
    cases hk : keepT li Q.n (c0 C li) (r.h, r.lp, r.rp) with
    | false => exact (rec_dropped hQ T hD hli h1 h2 h3 hk hdA hdc).elim
    | true =>
      obtain ⟨hA, hsub, -⟩ := rec_kept hQ T hD hli h1 h2 h3 hk
      obtain ⟨y, a, b, hch, -, hcab⟩ := h2
      rw [hcab] at hsub hdc
      have := Trans.one_piece hQ T hh' hch hdA hA hdc hsub
      refine ⟨_, ?_, this⟩
      grind [transL]

/-- **(T-R2) The filtered list is a valid chord list of the interior model.** -/
theorem chordTriplesOK_transL
    (hFam : (interiorModel Q).ChordFamily Q (Trans.pieces Q (N.F (chainModel C) Q))) :
    ChordTriplesOK (interiorModel Q) Q (transL li Q.n (c0 C li) (triplesOf N)) := by
  
  
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := famOf_transL hQ T hD hli hN
    grind [famOf]
  · unfold transL
    rw [List.map_map]
    refine List.Nodup.map_on (fun x hx x' hx' hxx => ?_)
      ((List.Nodup.of_map _ (nodup_triples_toSet hN)).filter _)
    obtain ⟨hxm, hk⟩ := List.mem_filter.1 hx
    obtain ⟨hxm', hk'⟩ := List.mem_filter.1 hx'
    obtain ⟨h1, h2, h3, -⟩ := triples_props hN hxm
    obtain ⟨h1', h2', h3', -⟩ := triples_props hN hxm'
    obtain ⟨hA, hsub, -⟩ := rec_kept hQ T hD hli h1 h2 h3 hk
    obtain ⟨hA', hsub', -⟩ := rec_kept hQ T hD hli h1' h2' h3' hk'
    simp only [Function.comp] at hxx
    rw [hxx] at hsub
    obtain ⟨y, a, b, hch, -, hcab⟩ := h2
    obtain ⟨y', a', b', hch', -, hcab'⟩ := h2'
    obtain ⟨y'', a'', b'', hch'', hd⟩ := hA'
    rw [hd] at hsub hsub'
    rw [hcab] at hsub
    rw [hcab'] at hsub'
    have heq := chord_eq_of_sub hch hch' hch''.lt hsub hsub'
    refine List.inj_on_of_nodup_map (nodup_triples_toSet hN) hxm hxm' ?_
    simp_all
  · intro x' hx'
    unfold transL at hx'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
    obtain ⟨hxm, hk⟩ := List.mem_filter.1 hx
    obtain ⟨h1, h2, h3, -⟩ := triples_props hN hxm
    exact (rec_kept hQ T hD hli h1 h2 h3 hk).2.2
  · intro x' hx'
    unfold transL at hx'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
    obtain ⟨hxm, -⟩ := List.mem_filter.1 hx
    exact (triples_props hN hxm).1


end

end filt

/-! ## The math of the transition -/

/-- **The math of the transition**: from the canonical normal form of the top chain, the
filtered list is a valid interior chord list whose family has degree `≤ 4` and weight
`≤ 2^(⌈βp⌉+12)`, with at most as many chords as the normal form, which satisfies the count of
Lemma 2.3. -/
theorem trans_math (hG : GoodEnv P) (hC : TopChain P C)
    (hN : IsCanonicalNF (chainModel C) (Qof P) N (topGran P.n) 4) {li : Bool}
    (hli : li = true ↔ Mountain.LeftInside (Qof P)) :
    ChordTriplesOK (interiorModel (Qof P)) (Qof P) (transL li P.n (c0 C li) (triplesOf N)) ∧
      (interiorModel (Qof P)).DegLe
        (famOf (interiorModel (Qof P)) (Qof P) (transL li P.n (c0 C li) (triplesOf N))) 4 ∧
      (interiorModel (Qof P)).Semigranular
        (famOf (interiorModel (Qof P)) (Qof P) (transL li P.n (c0 C li) (triplesOf N)))
        (2 ^ (Cost.ceilBeta (topGrade P.n) + 12)) ∧
      (transL li P.n (c0 C li) (triplesOf N)).length ≤ (N.F (chainModel C) (Qof P)).ncard ∧
      (N.F (chainModel C) (Qof P)).ncard * (gradeGran (topGrade P.n) + 1) ≤
        840 * (2 * (P.n - 1) + 1) := by
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hG.1
  have hn : (Qof P).n = P.n := shear_n _ _
  have T : Trans.Top (Qof P) C := ⟨hC.1, hC.2.1, by ram_grind⟩
  have hD : Trans.DistinctH (Qof P) := (goodShear_epsOf hG.2).2.1
  have hP : C.P.Simple := by ram_grind
  obtain ⟨hNF, hdeg, hgran, hdec⟩ := hN
  have hFam0 : (chainModel C).ChordFamily C.P (N.F (chainModel C) (Qof P)) := by
    ram_grind
  obtain ⟨hFam, hdegP, hwtP, -⟩ := Trans.transition hQ T hD hFam0 hgran.1 hdeg
  have hfam := famOf_transL hQ T hD hli hNF
  rw [← hn]
  refine ⟨chordTriplesOK_transL hQ T hD hli hNF hFam, by simp_all, ?_, ?_, ?_⟩
  · rw [hfam]
    intro U hU
    refine (hwtP U hU).trans ?_
    have := DownStep.gamma1_le (topGrade P.n)
    core_grind [DownStep.gamma1]
  · rw [ncard_F hNF.2.1]
    have := transL_length_le li (Qof P).n (c0 C li) (triplesOf N)
    simp_all [triplesOf, List.length_map] 
  · have := DownMath.trans_count hP ⟨hNF, hdeg, hgran, hdec⟩
    rw [hn]
    unfold topGran at this
    ram_grind

end

end DrvT

end Chazelle.Core
