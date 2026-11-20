/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PrivateRowFactorization
public import VaughtConjecture.Knight.GradeSplice
public import VaughtConjecture.Knight.SemScheme
public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.AmbientGradeCharts
public import VaughtConjecture.Knight.CanonicalPairedInverse

/-! # From native source repair to repair at the owner's cap

The argument only uses a lawful source on the prescribed face, its readback
from the full chart, and the ability to repair it on the native grid. It works
for either original face and at both the initial and subsequent installations.
-/

@[expose] public section

namespace VaughtConjecture.Knight.PrivateRowFactorization
open Transform ExtOrd Value CanonicalPairedInverse SharpWitnessComposition

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {A : Finset ι} {B : Finset κ} {D : CellScheme A} {E : CellScheme B}
  {sem : Semantics D} {out : Semantics E} {I : Finset ι × ℕ}
  {j m : ℕ} {t q : E.below (B, j) → ExtOrd} {s p : D.below I → ExtOrd}
  {σ : ExtOrd → ExtOrd} {γ : ExtOrd}

/-- Extend an owner-capped factorization through a grid repair, retaining the
external cap even on the cells outside the prescribed face. -/
theorem repairOwner (c : D.below I) (hc : D.cell c.1 = I) (hg : D.grade c.1 = j)
    (inc : D.below I → E.below (B, j))
    (hs : RespectsSemanticsBelow sem I s) (hp : RespectsSemanticsBelow sem I p)
    (hq : RespectsSemanticsBelow out (B, j) q) (ht : ∀ d, t (inc d) = s d)
    (hcode : ∀ d, s d ∈ ExtOrd.codedAlphabet (2 * m) j) (hshort : ∀ d, Short j (t d))
    (hσ : Witness (gTop j) σ) (hγ : SelfVis j γ) (hpos : ⊥ < γ) (hactive : γ < p c)
    (hchart : ∀ d, min (σ (t d)) γ = min (q d) γ)
    (hag : ∀ d, min (q (inc d)) γ = min (p d) γ)
    (repair : ∀ {b}, b ≤ 2*m+1 → ∀ {v}, sem.Lawful v → CappedEq v s (grid j b) →
      out.FaceLift inc v t (grid j b)) :
    out.FaceLift inc (fun d => min (p d) (p c)) q γ := by
  rcases c with ⟨c, hc'⟩
  change D.cell c = I at hc
  change D.grade c = j at hg
  subst I j
  let j := D.grade c
  let M := p ⟨c,GradedLe.refl _⟩
  let τ := fun x => min (σ x) γ
  have hface (d) : τ (s d) = min (p d) γ := by
    change min (σ (s d)) γ = _
    rw [← ht]; exact (hchart _).trans (hag d)
  have hshort' d : Short j (s d) := ht d ▸ hshort (inc d)
  obtain ⟨h,ρ,δ,H,hh,_,hvis,_,hρ,hγδ,hδM,hδ,hread,hface',halign,hcap,_⟩ :=
    OwnerLocalAlignment.exists_alignment c hs hp (fun e => coded_proper (hcode e)) hshort'
      (FreeDiagonal.clip_witness hσ hγ) hγ hpos (fun _ => min_le_right _ _) hface hactive
  obtain ⟨e,_,he⟩ := H.exists_witness
  obtain ⟨b,hb,hb'⟩ := endpoint_grid (hcode e) (hshort' e) (he.symm ▸ hh)
  obtain rfl : h = grid j b := he.symm.trans hb'
  have room : grid j b < ofOrd (Ordinal.omega0 * (b+1 : ℕ)) :=
    ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (Nat.lt_succ_self b)) j)
  let pp := fun d => min (p d) M
  obtain ⟨w,hw,hr,hpre⟩ := repair (b := b) (hb.trans (Nat.le_succ _))
    (AlignedCutEncoding.encode_respects hs (hp.cap (hp.orderly ⟨c,GradedLe.refl _⟩).symm)
      (fun d => d.2.2) hvis hh.ne' hδ room halign)
    (AlignedCutEncoding.encode_cap s pp room halign)
  let ν := PaddedSourceDecoder.extend (b+1) ρ δ
  have hc d : min (ν (w d)) γ = min (q d) γ := by
    refine (GradeTailRestoration.cap_below
      (PaddedSourceDecoder.extend_cap_agreement hρ hδ room hread.ge (hpre d)) hγδ).trans ?_
    exact (hcap (t d) (hshort d)).trans (by
      change min (min (σ (t d)) γ) γ = _; rw [min_assoc,min_self]; exact hchart d)
  refine ⟨_,map_respects_of_positive_cap_agreement hw hq (fun d => d.2.2)
    (boundedMap_of_witness (PaddedSourceDecoder.extend_witness hρ hδ)) hpos.ne' hc,?_,hc⟩
  intro d
  change ν (w (inc d)) = _
  rw [hr]
  apply AlignedCutEncoding.decode_encode s pp hρ.mono room hread.ge
  intro e
  change min (ρ (s e)) δ = min (min (p e) M) δ
  rw [min_assoc,min_eq_right hδM]; exact (hface' e).symm

end VaughtConjecture.Knight.PrivateRowFactorization

namespace VaughtConjecture.Knight.AmbientGradeCharts
open AmalgamationPlan

/-- On a complete original face any active cell supplies a maximal active
owner. This also handles a grade previously clipped at the arity: activity
forces the clipping to have left that grade unchanged. -/
theorem activeOwner {n i j : ℕ} {S : SemScheme n}
    {p : S.scheme.below (Finset.univ, i) → ExtOrd} {γ : ExtOrd}
    (hp : RespectsSemanticsBelow S.rows (Finset.univ, i) p) (hij : i ≤ j)
    (active : ∃ d, S.scheme.grade d.1 = j ∧ γ < p d) :
    ∃ c, S.scheme.cell c.1 = (Finset.univ, i) ∧ S.scheme.grade c.1 = j ∧ γ < p c ∧
      (∀ d, S.scheme.grade d.1 = j → p d ≤ p c) ∧ SelfVis j (p c) ∧ j ≤ n := by
  obtain ⟨d, hd, hpd⟩ := active
  obtain rfl : i = j := le_antisymm hij (hd ▸ d.2.2)
  have hn : i ≤ n := hd ▸ (S.scheme.grade_le_card_scope d.1).trans (by simpa using Finset.card_le_univ (S.scheme.scope d.1))
  obtain ⟨x, hx⟩ := S.complete (Finset.univ, i) (Plan.mem_gradedPlan.mpr
    ⟨S.scheme.isPlan.domain_mem, hd ▸ S.scheme.grade_pos d.1, by simpa using hn⟩)
  obtain ⟨c, hc, hm⟩ := exists_maximizer hp ⟨⟨x, by rw [hx]; exact GradedLe.refl _⟩, hx⟩
  have hg : S.scheme.grade c.1 = i := congrArg Prod.snd hc
  exact ⟨c, hc, hg, hpd.trans_le (hm d hd), hm, hg ▸ (hp.orderly c).symm, hn⟩

end VaughtConjecture.Knight.AmbientGradeCharts
