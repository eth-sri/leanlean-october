/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.ModelTheory.ProjectedExtension
public import VaughtConjecture.Knight.FiniteCoverReceivingCore
public import VaughtConjecture.Knight.ChartLanguage
public import VaughtConjecture.Knight.OneSidedTransfer

/-! # Structural chart comparison without modelhood

Exactly parent-consistent, covering, finite-cut receiving realizations supply actual
chart receipts at each block. Lowering uses the structural reduct laws and the existing
capped receiving reduction, not a modelhood theorem or inverse donor lifting. The one-sided
step needs covering only on the source and receiving only on the target. Both sides supply
these hypotheses for BF comparison.

Tuples are arbitrary coordinate selections from injective actual containers. Repeated
coordinates and empty roots are retained. Fixed block-zero structures are part of the
receipt, and an initial common chart is explicit. `RankedMatchingFamily` supplies the only
ordinal induction; this module constructs receipts and finite extension steps only.
-/

@[expose] public section

namespace VaughtConjecture.Knight.StructuralChartComparison

open TypeTower FirstOrder Language KnightRealization VaughtConjecture.ModelTheory

universe w w'

theorem lowerChart {α β : LimitStage} (h : β ≤ α) {M : Type w} {N : Type w'}
    {W : KnightRealization α M} {W' : KnightRealization α N} {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} (hc : HasCommonChart W W' a b) :
    HasCommonChart (W.reduct h) (W'.reduct h) a b := by
  obtain ⟨k, ta, tb, σ, p, hta, htb, ha, hb⟩ := hc
  refine ⟨k, ta, tb, σ, reduceType β.2 h p, ?_, ?_, ha, hb⟩
  · rw [Realization.reduct_eval, hta]; rfl
  · rw [Realization.reduct_eval, htb]; rfl

/-- One structural forth step. Source consistency and generic covering produce a lawful
donor over the literal root; target consistency and receiving transfer it with one strict
block drop. No receiving on the source or covering on the target is needed. -/
theorem extend_commonChart (α : Ordinal.{0}) {M : Type w} {N : Type w'}
    (W : KnightRealization (blockStage (α + 1)) M)
    (W' : KnightRealization (blockStage (α + 1)) N)
    (hc : W.IsExactParentConsistent) (hcover : W.IsCovering)
    (hc' : W'.IsExactParentConsistent) (hr' : FiniteCutReceiving W')
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} (seed : HasCommonChart W W' a b) (x : M) :
    ∃ y : N, HasCommonChart (W.reduct (blockStage_le_succ α))
      (W'.reduct (blockStage_le_succ α)) (Fin.snoc a x) (Fin.snoc b y) := by
  obtain ⟨k, ta, tb, σ, p, hta, htb, ha, hb⟩ := seed
  by_cases hmem : x ∈ Set.range ta
  · obtain ⟨j, hj⟩ := hmem
    refine ⟨tb j, lowerChart (blockStage_le_succ α) ?_⟩
    refine ⟨k, ta, tb, Fin.snoc σ j, p, hta, htb, ?_, ?_⟩
    · rw [Fin.comp_snoc, ha, hj]
    · rw [Fin.comp_snoc, hb]
  · obtain ⟨l, s, f, hfs, hsome⟩ := hcover (snoc ta x hmem)
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hsome
    let g : Fin k ↪ Fin l := Fin.castSuccEmb.trans f
    have hseg : g.trans s = ta := by
      change (Fin.castSuccEmb.trans f).trans s = ta
      rw [Function.Embedding.trans_assoc, hfs, castSuccEmb_trans_snoc]
    have hface : typeMap g P = some p := by
      have he := hc s P g hP
      rw [hseg, hta] at he
      exact he.symm
    obtain ⟨ub, Q, hroot, hub, hred⟩ :=
      receive_donor_uniform α hc' hr' P g tb p hface htb
    have hx : s (f (Fin.last k)) = x := by
      have he := congrArg (fun t : Fin (k + 1) ↪ M => t (Fin.last k)) hfs
      simpa only [Function.Embedding.trans_apply, snoc_apply_last] using he
    have hsource : (s : Fin l → M) ∘ (fun i => g (σ i)) = a := by
      funext i
      have hi := congrArg (fun t : Fin k ↪ M => t (σ i)) hseg
      exact hi.trans (congrFun ha i)
    have htarget : (ub : Fin l → N) ∘ (fun i => g (σ i)) = b := by
      funext i
      have hi := congrArg (fun t : Fin k ↪ N => t (σ i)) hroot
      exact hi.trans (congrFun hb i)
    refine ⟨ub (f (Fin.last k)), ?_⟩
    refine ⟨l, s, ub, Fin.snoc (fun i => g (σ i)) (f (Fin.last k)),
      reduceType (blockStage α).2 (blockStage_le_succ α) P, ?_, ?_, ?_, ?_⟩
    · rw [Realization.reduct_eval, hP]; rfl
    · rw [Realization.reduct_eval, hub, ← hred]; rfl
    · rw [Fin.comp_snoc, hsource, hx]
    · rw [Fin.comp_snoc, htarget]
