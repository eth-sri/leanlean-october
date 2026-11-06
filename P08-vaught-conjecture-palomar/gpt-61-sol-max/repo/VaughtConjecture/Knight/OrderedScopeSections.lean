
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.OrderedScopeRelocation

/-! # Selected sections through ordered ambient relocation

The local renderer is applied to the actual restriction of the preceding
section. The grid and ceiling are unchanged. Support is flattened to the
original field vector rather than treating earlier auxiliaries as new fields.
-/

namespace VaughtConjecture.Knight.OrderedScopeRelocation
open  Transform   SourcePrefixRows OrbitPrefixSupport
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}
variable {D : CellScheme A} (sem : Semantics D) (hB : B ∈ D.plan) {k : ℕ}
variable (S : OrdinaryScopeOperator.Core (ScopeBoundary.rows D B hB sem) k)
variable (hsep : Separated (D := D) (B := B))

local notation "K" => carrier sem hB S
local notation "l" => old sem hB S
local notation "r" => localCell sem hB S

local notation "toCell₀" => ScopeBoundary.toCell D B hB

def boundaryFace : ExactSemanticFace (ScopeBoundary.rows D B hB sem) sem where
  map := (toCell₀).toEmbedding
  index _ := rfl
  exhaustive _ := ScopeBoundary.exhaustive D B hB
  row _ _ := rfl

local notation "RespectsSemantics₀" => RespectsSemantics (rows sem hB S hsep)

local notation "covered₀" => covered

/-- Compatible whole sections glue on the actual occurrences. -/
theorem lawful_of_restrictions {v}
    (hp : RespectsSemantics sem (v ∘ l))
    (hq : RespectsSemantics S.rows (v ∘ r)) :
    RespectsSemantics₀ v where
  orderly z := by
    rcases covered₀ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · simpa only [Function.comp_apply, CellScheme.grade, old_index] using hp.orderly c
    · simpa only [Function.comp_apply, CellScheme.grade, local_index] using hq.orderly c
  locality z := by
    rcases covered₀ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact TransformsTo.of_equiv (oldBelow sem hB S hsep c)
        (fun d => congrArg Prod.snd (old_index S d.1))
        (row_old sem hB S hsep c) (fun _ => rfl) (hp.locality c)
    · exact (localFace sem hB S hsep).locality_of_restrict hq c
  availability z c hs hg := by
    rcases covered₀ c with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · have hz : (K).scope z ⊆ D.scope c := by
        simpa only [CellScheme.scope, old_index] using hs
      obtain ⟨d, rfl⟩ := old_exhaustive sem hB S hsep c z hz
      have hdc : D.scope d ⊆ D.scope c := by
        simpa only [CellScheme.scope, old_index] using hs
      have hdg : D.grade d = D.grade c := by
        simpa only [CellScheme.grade, old_index] using hg
      obtain ⟨e, he, hv⟩ := hp.availability d c hdc hdg
      exact ⟨l e, (old_index S e).trans
        (he.trans (old_index S c).symm), hv⟩
    · exact (localFace sem hB S hsep).availability_at hq z c hs hg

def paste (p : CellLabels D) (q : CellLabels S.carrier) : CellLabels K :=
  fun z => ProfileFaceUnion.paste (rightMap sem hB S) p q ((enumeration sem hB S).symm z)

theorem paste_old p q d :
    paste sem hB S p q (l d) = p d := by
  unfold paste old
  rw [Equiv.symm_apply_apply]
  rfl

theorem paste_local {p} {q}
    (he : ∀ c, p (toCell₀ c) = q (S.original c)) d :
    paste sem hB S p q (r d) = q d := by
  unfold paste localCell
  rw [Equiv.symm_apply_apply]
  exact ProfileFaceUnion.paste_right he d

theorem paste_lawful {p} {q}
    (hp : RespectsSemantics sem p) (hq : RespectsSemantics S.rows q)
    (he : ∀ c, p (toCell₀ c) = q (S.original c)) :
    RespectsSemantics₀ (paste sem hB S p q) := by
  apply lawful_of_restrictions sem hB S hsep
  · simpa only [Function.comp_def, paste_old] using hp
  · simpa only [Function.comp_def, paste_local sem hB S he] using hq

def render {p} (hp : RespectsSemantics sem p) (ht : AvoidsValue p ⊤)
    G θ :=
  paste sem hB S p (S.render ((boundaryFace sem hB).restrict hp)
    (fun c => ht (toCell₀ c)) G θ)

variable {p : CellLabels D} (hp : RespectsSemantics sem p) (ht : AvoidsValue p ⊤)
variable {G : Finset ExtOrd} {θ : ExtOrd}

local notation "render₀" => render sem hB S hp ht G θ

theorem render_old d : render₀ (l d) = p d :=
  paste_old sem hB S _ _ d

theorem render_local (hG : VisibleOn k G) (hθ : SelfVis k θ) d :
    render₀ (r d) =
      S.render ((boundaryFace sem hB).restrict hp)
        (fun c => ht (toCell₀ c)) G θ d :=
  paste_local sem hB S (fun c => (S.readback ((boundaryFace sem hB).restrict hp)
    (fun c => ht (toCell₀ c)) hG hθ c).symm) d

theorem render_lawful (hG : VisibleOn k G) (hθ : SelfVis k θ) :
    RespectsSemantics₀ (render₀) :=
  paste_lawful sem hB S hsep hp (S.lawful _ _ hG hθ)
    (fun c => (S.readback ((boundaryFace sem hB).restrict hp)
      (fun c => ht (toCell₀ c)) hG hθ c).symm)

theorem render_bound (hG : VisibleOn k G) (hθ : SelfVis k θ)
    (hb : BoundedBy p θ) d : render₀ d ≤ θ := by
  rcases covered₀ d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · rw [render_old]; exact hb c
  · rw [render_local sem hB S hp ht hG hθ]
    exact S.bound _ _ hθ (fun c => hb _) c

theorem render_supported {X : Type*} {v : X → ExtOrd} {L} (hk : k ≤ L)
    (hG : VisibleOn L G) (hθ : SelfVis k θ) (hθG : θ ∈ G)
    (hv : ∀ d, Supported L (G : Set ExtOrd) v (p d)) d :
    Supported L (G : Set ExtOrd) v (render sem hB S hp ht G θ d) := by
  rcases covered₀ d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · rw [render_old]; exact hv c
  · rw [render_local sem hB S hp ht (fun z hz => selfVis_mono (hG z hz) hk) hθ]
    exact (S.support _ _ hk hθG c).substitute hG (fun c => hv _)

theorem render_agreement {q} (hq : RespectsSemantics sem q)
    (htq : AvoidsValue q ⊤) (hG : VisibleOn k G) (hθ : SelfVis k θ)
    {γ} (hγ : γ ∈ G) (hγθ : γ ≤ θ) (he : Agree p q γ) :
    Agree (render sem hB S hp ht G θ) (render sem hB S hq htq G θ) γ := by
  intro d
  rcases covered d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · simp_all [render_old] <;> aesop
  · rw [render_local sem hB S hp ht hG hθ, render_local sem hB S hq htq hG hθ]
    exact S.agreement _ _ _ _ hG hθ hγ hγθ (fun c => he _) c

