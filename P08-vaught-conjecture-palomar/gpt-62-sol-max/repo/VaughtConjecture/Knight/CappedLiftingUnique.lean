/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedLifting
public import VaughtConjecture.Knight.NormalForm
public import VaughtConjecture.CapCompatibleExtension

@[expose] public section

namespace VaughtConjecture.Knight.ExtensionInjectivity

open Transform Value ExtOrd AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} (sem : Semantics D)
  {I U : Finset ι × ℕ} (h : GradedLe I U)

/-- **Existence**: every lawful section below `I` extends lawfully to `U`, literally on `I`. -/
def LawfulExtension : Prop :=
  ∀ p : D.below I → ExtOrd, RespectsSemanticsBelow sem I p →
    ∃ r : D.below U → ExtOrd, RespectsSemanticsBelow sem U r ∧
      ∀ d, r (CellScheme.below.mono h d) = p d

/-- **Uniqueness**: lawful sections below `U` agreeing on `I` agree on every occurrence below
`U`. -/
def RestrictionInjective : Prop :=
  ∀ r r' : D.below U → ExtOrd, RespectsSemanticsBelow sem U r → RespectsSemanticsBelow sem U r' →
    (∀ d, r (CellScheme.below.mono h d) = r' (CellScheme.below.mono h d)) → ∀ d, r d = r' d

variable {sem h}

/-- A single lawful extension of each prescription preserves every compatible permitted cap,
even when a different lawful ambient is supplied for each cap. -/
def AllCapsExtension (sem : Semantics D) (h : GradedLe I U) : Prop :=
  ∀ p : D.below I → ExtOrd, RespectsSemanticsBelow sem I p →
    ∃ r : D.below U → ExtOrd, RespectsSemanticsBelow sem U r ∧
      (∀ d, r (CellScheme.below.mono h d) = p d) ∧
      ∀ (γ : ExtOrd) (q : D.below U → ExtOrd), SelfVis U.2 γ →
        RespectsSemanticsBelow sem U q →
        (∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) →
        ∀ d, min (r d) γ = min (q d) γ

/-- Instantiate commuting restriction on the actual lawful-section subtypes. Capping is
permitted at the target grade, hence also at the source grade. -/
theorem allCapsExtension_of_extension_injective (hext : LawfulExtension sem h)
    (hinj : RestrictionInjective sem h) : AllCapsExtension sem h := by
  let X := {r : D.below U → ExtOrd // RespectsSemanticsBelow sem U r}
  let Y := {p : D.below I → ExtOrd // RespectsSemanticsBelow sem I p}
  let Γ := {γ : ExtOrd // SelfVis U.2 γ}
  let restrict : X → Y := fun r => ⟨fun d => r.1 (CellScheme.below.mono h d), r.2.mono h⟩
  let capX : Γ → X → X := fun γ r => ⟨fun d => min (r.1 d) γ.1, r.2.cap γ.2⟩
  let capY : Γ → Y → Y := fun γ p =>
    ⟨fun d => min (p.1 d) γ.1, p.2.cap (extVisReplace_self_of_le γ.2 h.2)⟩
  have hr : Function.Bijective restrict := by
    constructor
    · intro r s hrs
      apply Subtype.ext
      exact funext (hinj r.1 s.1 r.2 s.2 (congrFun (congrArg Subtype.val hrs)))
    · intro p
      obtain ⟨r, hr, hres⟩ := hext p.1 p.2
      aesop
  intro p hp
  obtain ⟨r, hres, hcaps⟩ := CapCompatibleExtension.exists_extension restrict capX capY hr
    (fun _ _ => rfl) ⟨p, hp⟩
  refine ⟨r.1, r.2, congrFun (congrArg Subtype.val hres), ?_⟩
  intro γ q hγ hq hag
  exact congrFun (congrArg Subtype.val (hcaps ⟨γ, hγ⟩ ⟨q, hq⟩
    (Subtype.ext (funext (fun d => (hag d).symm)))))

/-- The traditional one-cap lifting interface is a specialization of simultaneous extension. -/
theorem AllCapsExtension.cappedLift (hall : AllCapsExtension sem h) :
    CoatomBoundaryExtension.CappedLift sem h := by
  intro p q γ hp hq hγ hag
  obtain ⟨r, hr, hres, hcaps⟩ := hall p hp
  grind

end VaughtConjecture.Knight.ExtensionInjectivity
