/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorRepairPackage
public import VaughtConjecture.Knight.OrdinaryFinalCatalogue

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryFinalRepair

open Transform Value ExtOrd CappedDonor CappedDonor.Ref SourcePrefixRows

open OrdinaryFinalCatalogue CanonicalPairedInverse

noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}

variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (F : FinalGateLayer.Input D N (Field P C) (OrdinaryFinalCatalogue.Member R))

/-- A proper private repair is installed in the fixed physical inventory with
lawfulness and the entire source-cut vector constructed. -/
theorem exists_source_repair
    (hfields : ∀ a f, F.fields a f = a.val f)
    (hgrid : F.grid = PairedSlotComparison.sourceGrid N (Fintype.card (Field P C)))
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (priv : Cell C.scheme ↪ Cell D)
    (hpriv : ∀ a d, F.lower a (priv d) = a.val (.priv d))
    (a : OrdinaryFinalCatalogue.Member R)
    {v : C.scheme.below (effC N N) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC N N) v) (hproper : ∀ d, v d ≠ ⊤)
    {B : ℕ} (hB : grid N B ∈ F.grid)
    (hag : ∀ d, min (v d) (grid N B) = min (a.val (.priv d.1)) (grid N B)) :
    ∃ (b : OrdinaryFinalCatalogue.Member R) (κ : ExtOrd → ExtOrd),
      Witness (gTop N) κ ∧
      RespectsSemanticsBelow F.rows (A, N) (fun d => κ (F.source b d.1)) ∧
      (∀ d : F.carrier.below (A, N),
        min (κ (F.source b d.1)) (grid N B) = min (F.source a d.1) (grid N B)) ∧
      (∀ d : C.scheme.below (effC N N), κ (F.source b (F.old (priv d.1))) = v d) := by
  obtain ⟨b₀, -, -, hprivate, hprefix, hcat, hnorm, κ, hκ, hread, hfix, hreach, -⟩ :=
    positive_cap_repair a.property hv hproper hag
  let b : OrdinaryFinalCatalogue.Member R := ⟨PairedSlotEncoding.normalize N b₀, hcat⟩
  have hfixFields : ∀ f, F.fields a f < grid N B → κ (F.fields a f) = F.fields a f := by
    grind
  have hfixGrid : ∀ z ∈ F.grid, z < grid N B → κ z = z := by
    rw [hgrid]
    exact fix_sourceGrid hκ.bot hfix _
  have hag' : Agree (F.fields b) (F.fields a) (grid N B) := by
    intro f
    grind
  obtain ⟨hlaw, hcaps⟩ := F.decode_source_prefix hsupport a b hB (ofOrd_ne_bot _)
    hag' hκ hreach hfixGrid hfixFields
  refine ⟨b, κ, hκ, hlaw, hcaps, ?_⟩
  intro d
  rw [F.source_old, hpriv]
  grind

end

end VaughtConjecture.Knight.OrdinaryFinalRepair
