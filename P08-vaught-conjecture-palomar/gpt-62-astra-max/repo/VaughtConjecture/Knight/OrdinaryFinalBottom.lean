/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryFinalRepair
public import VaughtConjecture.Knight.OrdinaryFinalDisplay

/-! # Independent private bottom-cap supply on the ordinary final layer

The ordinary private fibre supplies a gate-off admitted vector for an arbitrary
lawful private prescription. Terminal insertion gives a catalogue member and
decoder with finite original-field bottom reflection. Mixed-row decoding proves
lawfulness on the actual physical carrier; no positive external cap, ambient
completion, or output bountifulness is used. Literal tops are allowed.

The scope predecessor's short-new/original-long classification is explicit,
as in the actual-display construction. Every marked gate, not just the selected
one, is bottom in the constructed section.
-/

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryFinalBottom
open Transform Value ExtOrd CappedDonor CappedDonor.Ref SharpWitnessComposition
open OrdinaryFinalCatalogue
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (F : FinalGateLayer.Input D N (Field P C) (OrdinaryFinalCatalogue.Member R))

/-- Arbitrary private data, including literal top, has a lawful physical
extension with every marked gate off. No ambient or positive cap is required. -/
theorem exists_private_display
    (hfields : ∀ a f, F.fields a f = a.val f)
    (hgrid : ∀ z ∈ F.grid, Short N z)
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (howners : ∀ a (c : D.below (A, N)),
      (∀ d : D.RowDomain c.1, Short (D.grade c.1) (F.sem.E c.1 d)) ∨
      (∀ d : D.RowDomain c.1, ∃ f : Field P C, F.lower a d.1 = a.val f))
    (priv : Cell C.scheme ↪ Cell D)
    (hpriv : ∀ a d, F.lower a (priv d) = a.val (.priv d))
    {p : C.ClippedCells N → ExtOrd}
    (hp : C.rows.Lawful p) :
    ∃ (b : OrdinaryFinalCatalogue.Member R) (δ : ExtOrd → ExtOrd),
      F.rows.Lawful (fun d : F.carrier.below (A,N) => δ (F.source b d.1)) ∧
      ∀ d : C.ClippedCells N, δ (F.source b (F.old (priv d.1))) = p d := by
  obtain ⟨a,ha,hp',_⟩ := (Admitted.zero R).private_repair hp (selfVis_bot N) (fun _ => by simp)
  obtain ⟨b,δ,hlaw,hr⟩ := OrdinaryFinalDisplay.display R F hfields hgrid hsupport howners ha
  refine ⟨b,δ,hlaw,fun d => ?_⟩
  rw [F.source_old,hpriv,hr]; exact hp' d

end
end VaughtConjecture.Knight.OrdinaryFinalBottom
