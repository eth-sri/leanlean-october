/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrderedScopeRelocation

@[expose] public section

namespace VaughtConjecture.Knight.OrderedScopeRelocation

open AmalgamationPlan Transform Value ExtOrd SourcePrefixRows OrbitPrefixSupport

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}

variable {D : CellScheme A} (sem : Semantics D) (hB : B ∈ D.plan) {k : ℕ}

variable (S : OrdinaryScopeOperator.Core (ScopeBoundary.rows D B hB sem) k)

variable (hsep : Separated (D := D) (B := B))

local notation "K" => carrier sem hB S

local notation "l" => old sem hB S

local notation "r" => localCell sem hB S

def boundaryFace : ExactSemanticFace (ScopeBoundary.rows D B hB sem) sem where
  map := (ScopeBoundary.toCell D B hB).toEmbedding
  index _ := rfl
  exhaustive _ := ScopeBoundary.exhaustive D B hB
  row _ _ := rfl

/-- Compatible whole sections glue on the actual occurrences. -/
theorem lawful_of_restrictions {v : Cell K → ExtOrd}
    (hp : RespectsSemantics sem (v ∘ l))
    (hq : RespectsSemantics S.rows (v ∘ r)) :
    RespectsSemantics (rows sem hB S hsep) v :=
  (patches sem hB S hsep).respects sem S.rows (agreement sem hB S hsep) hp hq

def paste (p : Cell D → ExtOrd) (q : Cell S.carrier → ExtOrd) : Cell K → ExtOrd :=
  fun z => ProfileFaceUnion.paste (rightMap sem hB S) p q ((enumeration sem hB S).symm z)

theorem paste_old (p : Cell D → ExtOrd) (q : Cell S.carrier → ExtOrd) (d : Cell D) :
    paste sem hB S p q (l d) = p d := by
  unfold paste old
  rw [Equiv.symm_apply_apply]
  rfl

theorem paste_local {p : Cell D → ExtOrd} {q : Cell S.carrier → ExtOrd}
    (he : ∀ c, p (ScopeBoundary.toCell D B hB c) = q (S.original c)) (d : Cell S.carrier) :
    paste sem hB S p q (r d) = q d := by
  unfold paste localCell
  rw [Equiv.symm_apply_apply]
  exact ProfileFaceUnion.paste_right _ _ he d

theorem paste_lawful {p : Cell D → ExtOrd} {q : Cell S.carrier → ExtOrd}
    (hp : RespectsSemantics sem p) (hq : RespectsSemantics S.rows q)
    (he : ∀ c, p (ScopeBoundary.toCell D B hB c) = q (S.original c)) :
    RespectsSemantics (rows sem hB S hsep) (paste sem hB S p q) := by
  apply lawful_of_restrictions sem hB S hsep
  · simpa [Function.comp_def, paste_old] using hp
  · simpa only [Function.comp_def, paste_local sem hB S he] using hq

abbrev scopeRender {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤) :=
  S.render ((boundaryFace sem hB).restrict hp) (fun c => ht (ScopeBoundary.toCell D B hB c))

def render {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    (G : Finset ExtOrd) (θ : ExtOrd) : Cell K → ExtOrd :=
  paste sem hB S p (scopeRender sem hB S hp ht G θ)

variable {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)

variable {G : Finset ExtOrd} {θ : ExtOrd}

theorem render_old (d : Cell D) : render sem hB S hp ht G θ (l d) = p d :=
  paste_old sem hB S _ _ d

theorem render_lawful (hG : ∀ z ∈ G, SelfVis k z) (hθ : SelfVis k θ) :
    RespectsSemantics (rows sem hB S hsep) (render sem hB S hp ht G θ) :=
  paste_lawful sem hB S hsep hp (S.lawful _ _ hG hθ)
    (fun c => (S.readback ((boundaryFace sem hB).restrict hp)
      (fun c => ht (ScopeBoundary.toCell D B hB c)) hG hθ c).symm)

theorem render_bound (hθ : SelfVis k θ) (hb : ∀ d, p d ≤ θ) (d : Cell K) :
    render sem hB S hp ht G θ d ≤ θ :=
  ProfileFaceUnion.paste_pred (rightMap sem hB S) (R := (· ≤ θ))
    (p := p) (q := scopeRender sem hB S hp ht G θ) hb
    (S.bound ((boundaryFace sem hB).restrict hp) (fun c => ht _) hθ (fun c => hb _))
    ((enumeration sem hB S).symm d)

theorem render_supported {X : Type*} {v : X → ExtOrd} {L : ℕ} (hk : k ≤ L)
    (hG : ∀ z ∈ G, SelfVis L z) (hθG : θ ∈ G)
    (hv : ∀ d, Supported L (G : Set ExtOrd) v (p d)) (d : Cell K) :
    Supported L (G : Set ExtOrd) v (render sem hB S hp ht G θ d) :=
  ProfileFaceUnion.paste_pred (rightMap sem hB S) (R := Supported L (G : Set ExtOrd) v)
    (p := p) (q := scopeRender sem hB S hp ht G θ) hv
    (fun c => (S.support ((boundaryFace sem hB).restrict hp) (fun c => ht _) hk hθG c).substitute hG
      (fun _ => hv _)) ((enumeration sem hB S).symm d)

theorem render_agreement {q : Cell D → ExtOrd} (hq : RespectsSemantics sem q)
    (htq : ∀ d, q d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis k z) (hθ : SelfVis k θ)
    {γ : ExtOrd} (hγ : γ ∈ G) (hγθ : γ ≤ θ) (he : Agree p q γ) :
    Agree (render sem hB S hp ht G θ) (render sem hB S hq htq G θ) γ :=
  fun d => ProfileFaceUnion.paste_rel (rightMap sem hB S) (R := fun x y => min x γ = min y γ) he
    (S.agreement ((boundaryFace sem hB).restrict hp) (fun c => ht _) ((boundaryFace sem hB).restrict hq)
      (fun c => htq _) hG hθ hγ hγθ (fun c => he _)) ((enumeration sem hB S).symm d)

end

end VaughtConjecture.Knight.OrderedScopeRelocation
