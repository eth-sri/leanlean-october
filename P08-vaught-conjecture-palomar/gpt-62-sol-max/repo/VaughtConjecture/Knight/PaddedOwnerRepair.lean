/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PrivateRowFactorization
public import VaughtConjecture.Knight.AmbientGradeCharts
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.SourceBlockLocalityTransport

@[expose] public section

namespace VaughtConjecture.Knight.PaddedOwnerRepair

open Transform Value ExtOrd SharpWitnessComposition CanonicalPairedInverse

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {A : Finset ι} {B : Finset κ}
  {D : CellScheme B} {E : CellScheme A} {J : Finset κ × ℕ} {j : ℕ}

/-- Repair on the fixed grid of an encoded source. -/
abbrev GridRepair (m : ℕ) (rd : Semantics D) (re : Semantics E)
    (emb : D.below J → E.below (A, j)) (p : D.below J → ExtOrd) (s : E.below (A, j) → ExtOrd) : Prop :=
  ∀ b ≤ 2 * m + 1, ∀ {v : D.below J → ExtOrd}, RespectsSemanticsBelow rd J v →
    (∀ d, min (v d) (grid j b) = min (p d) (grid j b)) →
    ∃ w, RespectsSemanticsBelow re (A, j) w ∧ (∀ d, w (emb d) = v d) ∧
      ∀ d, min (w d) (grid j b) = min (s d) (grid j b)

/-- The ambient prescription can be repaired up to the selected owner's value. -/
abbrev Capped (rd : Semantics D) (re : Semantics E)
    (emb : D.below J → E.below (A, j)) : Prop :=
  ∀ (c : D.below J), D.cell c.1 = J → D.grade c.1 = j →
    ∀ {p : D.below J → ExtOrd} {q : E.below (A, j) → ExtOrd},
    RespectsSemanticsBelow rd J p → RespectsSemanticsBelow re (A, j) q →
    ∀ {γ : ExtOrd}, SelfVis j γ → ⊥ < γ → γ < p c →
    (∀ d, min (q (emb d)) γ = min (p d) γ) →
    ∃ u, RespectsSemanticsBelow re (A, j) u ∧ (∀ d, u (emb d) = min (p d) (p c)) ∧
      (∀ d, min (u d) γ = min (q d) γ) ∧ ∀ d, u d ≤ p c

/-- Factor the original prescription on the owner, repair the encoded source,
and decode the repair without changing the ambient cap. -/
theorem capped_of_catalogue {m : ℕ} {X : Type*} {rd : Semantics D} {re : Semantics E}
    {emb : D.below J → E.below (A, j)}
    (source : X → Cell E → ExtOrd) (hgrade : ∀ d, E.grade (emb d).1 = D.grade d.1)
    (chart : ∀ {q}, RespectsSemanticsBelow re (A, j) q →
      ∃ a σ H, Witness (gTop j) σ ∧ (∀ d, E.grade d.1 = j → q d ≤ H) ∧
        ∀ d, σ (source a d.1) = min (q d) H)
    (short : ∀ a d, Short j (source a d))
    (face : ∀ a, ∃ p, (∀ d, source a (emb d).1 = p d) ∧ RespectsSemanticsBelow rd J p ∧
        (∀ d, p d ∈ ExtOrd.codedAlphabet (2 * m) j) ∧ GridRepair m rd re emb p (fun d => source a d.1)) :
    Capped rd re emb := by
  classical
  intro c hc hg p q hp hq γ hγ hpos hactive hag
  rcases c with ⟨c, hc'⟩
  change D.cell c = J at hc
  subst J
  obtain ⟨a, σ, H, hσ, hmax, hread⟩ := chart hq
  obtain ⟨v, hface, hv, hcoded, repair⟩ := face a
  let s : E.below (A, j) → ExtOrd := fun d => source a d.1
  have heq : s ∘ emb = v := funext hface
  have hs : RespectsSemanticsBelow rd (D.cell c) (s ∘ emb) := heq.symm ▸ hv
  have hreach : γ ≤ H := by grind
  have hchart (d) : min (σ (s d)) γ = min (q d) γ := by
    change min (σ (source a d.1)) γ = _
    rw [hread, min_assoc, min_eq_right hreach]
  obtain ⟨δ, hδ, hδpos, ⟨fac⟩⟩ := PrivateRowFactorization.exists_factorization c m hs hp
    (by simpa only [hg, heq] using hcoded)
    (by simpa only [hg, Function.comp_apply] using fun d => short a (emb d).1)
    (by simpa only [hg] using hσ) (by simpa only [hg] using hγ) hpos hactive
    (fun d => (hchart _).trans (hag d))
  rw [hg] at hδ
  rcases Finset.mem_insert.mp hδ with rfl | hd
  · trivial
  obtain ⟨b, hb, hbδ⟩ := Finset.mem_image.mp hd
  change grid j b = δ at hbδ
  subst δ
  obtain ⟨w, hw, hwread, hwcap⟩ := repair b (by have := Finset.mem_range.mp hb; omega)
    fac.lawful (fun d => by simpa only [s, Function.comp_apply, hface] using fac.prefix_eq d)
  have hcap (d) := (AmbientGradeCharts.map_cap_agreement fac.witness.mono (hwcap d) fac.reaches).trans
    ((fac.caps _ (by simpa only [hg] using short a d.1)).trans (hchart d))
  have hν : Witness (gTop j) fac.outgoing := hg ▸ fac.witness
  exact ⟨fac.outgoing ∘ w,
    map_respects_of_positive_cap_agreement hw hq (fun d => d.2.2)
      (hν.bounded) (ne_of_gt hpos) hcap,
    fun d => (congrArg fac.outgoing (hwread d)).trans (fac.readback d), hcap, fun _ => fac.bounded _⟩

end VaughtConjecture.Knight.PaddedOwnerRepair
