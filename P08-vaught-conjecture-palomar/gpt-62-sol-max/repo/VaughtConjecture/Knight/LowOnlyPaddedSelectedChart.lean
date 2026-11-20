/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedRenderChart
public import VaughtConjecture.Knight.LowOnlyTerminal
public import VaughtConjecture.Knight.CappedDonorRepairPackage
public import VaughtConjecture.Knight.ReferenceContext

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedSelectedChart

open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder

open LowOnlyPaddedContract LowOnlyPaddedIteration

open LowOnlyPaddedRenderChart SharpWitnessComposition

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (L : BuildContext A B C R m n K)

/-- The native chart and the whole supported display are produced together.
One top complete field makes the chart's reserved ceiling top. -/
theorem exists_whole_chart (t : ℕ) (ht : t + 2 ≤ A.card) (r : ℕ)
    (hr : t + r + 2 ≤ A.card) (hfull : t + r + 2 = A.card)
    {S : State L.I.left L.I.right} (hS : L.F.Admissible (t + r + 2) S)
    (htop : ∃ f, S.profile f = ⊤) :
    ∃ w : Cell (L.tower (t + r) hr).carrier → ExtOrd,
      RespectsSemantics (L.tower (t + r) hr).rows w ∧
      (∀ d, w ((L.tower (t + r) hr).original d) = S.profile (field L.I d)) ∧
      (∀ d, OrbitPrefixSupport.Supported (t + r + 2) ({⊤} : Set ExtOrd) S.profile (w d)) ∧
      ∃ a : L.F.Anchor (t + 2), ∃ σ : ExtOrd → ExtOrd,
        BoundedMap (t + 2) σ ∧
        (∀ f, σ (a.val f) = S.profile f) ∧
        σ (CanonicalFieldLayer.ceiling (t + 2) (Field L.I.left L.I.right)) = ⊤ ∧
        ∀ d : (L.tower t ht).carrier.below (A, t + 2),
          w (L.advance t ht r hr d).1 =
            σ ((L.tower t ht).source a d.1) := by
  obtain ⟨Q, hQ, hcanon, δ, hδ, hread, hreflect, hsupp⟩ :=
    L.F.terminalContext.exists_supported_decoder (by omega) hS
  change ∀ f, δ (Q.profile f) = S.profile f at hread
  let b : L.F.Anchor (t + r + 2) := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  have horiginal : RespectsSemanticsBelow L.I.rows (A, t + r + 2)
      (fun d => δ (b.val (field L.I d.1))) := by
    simpa only [b, hread] using
      LowOnlyOrderedLadder.boundary_lawful L.I L.F L.root S hS
  have hw := (L.tower (t + r) hr).decoded_lawful b hδ hreflect horiginal
  have hall (d : Cell (L.tower (t + r) hr).carrier) :
      GradedLe ((L.tower (t + r) hr).carrier.cell d) (A, t + r + 2) := by
    let D := (L.tower (t + r) hr).carrier
    have hs := D.scope_subset d
    exact ⟨hs, ((D.grade_le_card_scope d).trans (Finset.card_le_card hs)).trans_eq hfull.symm⟩
  obtain ⟨a, τ, hτ, hf, hc, hd⟩ := source_chart L t ht r hr b
  have hcomp := (hδ.bounded).comp hτ (by omega)
  have hceiling : δ (CanonicalFieldLayer.ceiling (t + r + 2) (Field L.I.left L.I.right)) = ⊤ := by
    obtain ⟨f, hf⟩ := htop
    apply top_le_iff.mp
    exact (hf.symm.trans (hread f).symm).le.trans
      (hδ.mono (LowOnlyRecursiveCharts.anchor_bound L.F b f))
  refine ⟨fun d => δ ((L.tower (t + r) hr).source b d),
    hw.toRespects hall, ?_, fun d => hsupp _, a, δ ∘ τ, hcomp, ?_,
    (congrArg δ hc).trans hceiling, ?_⟩
  · intro d
    exact (congrArg δ ((L.tower (t + r) hr).source_original b d)).trans
      (hread _)
  · intro f
    exact (congrArg δ (hf f)).trans (hread f)
  tauto

end

end VaughtConjecture.Knight.LowOnlyPaddedSelectedChart
