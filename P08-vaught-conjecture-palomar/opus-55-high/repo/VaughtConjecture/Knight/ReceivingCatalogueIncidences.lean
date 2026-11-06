/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PrivateRowFactorization
public import VaughtConjecture.Knight.CappedDonorLowHighNormalization
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.PairedSlotComparison
public import VaughtConjecture.Knight.OrbitPrefixSupport
public import VaughtConjecture.Knight.LadderScalarRendering
public import VaughtConjecture.Knight.SourcePrefixRows
public import VaughtConjecture.Knight.AmbientGradeCharts

/-! # Rank-row incidences with retained private owners

Rank compression preserves the source-block bottom condition at grade one.
Consequently the admitted private section supplies faithful locality for the
long lower ladder rows against original owners, not just upper-row locality.
-/

@[expose] public section

namespace VaughtConjecture.Knight.ReceivingCatalogueIncidences
open Transform Value ExtOrd CappedDonor CappedDonor.Ref
open LadderScalarRendering
noncomputable section

/-- Visible postprocessing needs bottom reflection only on the actual target
table. This is a constructed faithful witness, not transformation transitivity. -/
theorem postprocess {Y} [Finite Y] {E t}
    (h : TransformsTo (fun _ => 1) E t) (hE : ∀ d, SelfVis 1 (E d))
    {f} (hm : Monotone f) (h0 : f ⊥ = ⊥)
    (hv : ∀ d, SelfVis 1 (f (t d))) (hb : ∀ d, f (t d) = ⊥ ↔ t d = ⊥) :
    TransformsTo (fun _ : Y => 1) E (fun d => f (t d)) := by
  apply LongGuardRows.transforms_of_visible_table hE hv
  · intro d e he
    obtain ⟨g, σ, _, _, _, hσ, _, hr⟩ := h
    apply hm
    rw [hr d, hr e]
    exact min_le_min (hσ he) le_rfl
  · intro d hd
    obtain ⟨g, σ, _, _, hσ, _, _, hr⟩ := h
    rw [hr d, hd, hσ, min_bot_left, h0]
  · intro d e he hd
    exact (hb e).mpr (LongGuardRows.bottom_of_same_block h he ((hb d).mp hd))

end
end VaughtConjecture.Knight.ReceivingCatalogueIncidences
