/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReferenceContext
public import VaughtConjecture.Knight.ReductModel
public import VaughtConjecture.Knight.OnePointRootedExtension
public import VaughtConjecture.Knight.ActualOccurrence

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization AmalgamationPlan Value ExtOrd

open CellScheme.restrictFace (toCell)

universe w

section RequiredFace

variable {γ : Ordinal.{0}} {k m : ℕ}

/-- **The requested projection forces the domain**: a projection along `f` to `P` exists only if
the face `univ.image f` is visible in the domain and the domain (with its rows) restricts to
`P`'s domain there. -/
theorem face_of_typeMap_eq_some (f : Fin k ↪ Fin m) {q : S γ m} {P : S γ k}
    (h : typeMap f q = some P) :
    ∃ hv : Finset.univ.image f ∈ q.scheme.scheme.plan, q.scheme.restrictFace f hv = P.scheme := by
  have hv : Finset.univ.image f ∈ q.scheme.scheme.plan :=
    (typeMap_isSome_iff f q).mp (by rw [h]; rfl)
  refine ⟨hv, ?_⟩
  rw [typeMap_eq_some f q hv] at h
  aesop

/-- **Projected correctness, cellwise**: once the face is visible and the domains match,
`typeMap f q = some P` says exactly that every cell of the face reads `P`'s label at the
corresponding cell. -/
theorem typeMap_eq_some_iff_labels (f : Fin k ↪ Fin m) (q : S γ m) (P : S γ k)
    (hv : Finset.univ.image f ∈ q.scheme.scheme.plan)
    (hs : q.scheme.restrictFace f hv = P.scheme) :
    typeMap f q = some P ↔
      ∀ i : Cell (q.scheme.restrictFace f hv).scheme,
        q.label (toCell q.scheme.scheme f hv i) = P.label (SemScheme.castCell hs i) := by
  rw [typeMap_eq_some f q hv, Option.some_inj]
  constructor
  · rintro rfl i
    rfl
  · intro h
    obtain ⟨Ps, Pl, Pb, Pr⟩ := P
    dsimp only at hs h
    subst hs
    exact StageType.ext rfl (heq_of_eq (funext fun i => h i))

end RequiredFace

end VaughtConjecture.Knight
