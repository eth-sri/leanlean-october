/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Scott.BackAndForth
public import VaughtConjecture.Knight.OrdinaryFiniteCutReceiving
public import VaughtConjecture.Knight.Sentence
public import VaughtConjecture.Knight.StructuralChartComparison

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower FirstOrder Language KnightRealization StructuralChartComparison

universe w w'

private theorem chart_symm {α : LimitStage} {M : Type w} {N : Type w'}
    {W : KnightRealization α M} {V : KnightRealization α N} {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} (h : HasCommonChart W V a b) :
    HasCommonChart V W b a := by
  obtain ⟨k, t, s, σ, p, ht, hs, ha, hb⟩ := h
  exact ⟨k, s, t, σ, p, hs, ht, hb, ha⟩

/-- A common chart at block `α` implies back-and-forth equivalence at rank `α`
in the base language. A successor step uses finite-cut receiving; at a limit it
suffices to compare the reducts at every lower block. -/
theorem bfEquiv_of_commonChart (α : Ordinal.{0}) {M : Type w} {N : Type w'}
    (W : KnightRealization (blockStage α) M) (V : KnightRealization (blockStage α) N)
    (hW : W.IsModel) (hV : V.IsModel) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hc : HasCommonChart W V a b) :
    @BFEquiv knightLang M (structureOf (W.reduct (omegaStage_le _)))
      N (structureOf (V.reduct (omegaStage_le _))) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero =>
    refine (@BFEquiv.zero knightLang M (structureOf (W.reduct (omegaStage_le _)))
      N (structureOf (V.reduct (omegaStage_le _))) n a b).mpr ?_
    exact sameAtomicType_of_commonChart
      (hW.consistent_reduct _) (hV.consistent_reduct _) (lowerChart (omegaStage_le _) hc)
  | add_one β ih =>
    let sm := structureOf (W.reduct (omegaStage_le _))
    let sn := structureOf (V.reduct (omegaStage_le _))
    change @BFEquiv knightLang M sm N sn (β + 1) n a b
    rw [← Order.succ_eq_add_one, @BFEquiv.succ knightLang M sm N sn]
    let h := blockStage_le_succ β
    have descend {k} {s : Fin k → M} {t : Fin k → N}
        (hs : HasCommonChart (W.reduct h) (V.reduct h) s t) :
        @BFEquiv knightLang M (structureOf (W.reduct (omegaStage_le _)))
          N (structureOf (V.reduct (omegaStage_le _))) β k s t := by
      have H := ih (W.reduct h) (V.reduct h) (hW.reduct h) (hV.reduct h) hs
      rwa [Realization.reduct_reduct, Realization.reduct_reduct] at H
    refine ⟨descend (lowerChart h hc), ?_, ?_⟩
    · intro x
      obtain ⟨y, hy⟩ := extend_commonChart β W V hW.consistent hW.isCovering
        hV.consistent (OrdinaryModelReceiving.finiteCutReceiving hV) hc x
      exact ⟨y, descend hy⟩
    · intro y
      obtain ⟨x, hx⟩ := extend_commonChart β V W hV.consistent hV.isCovering
        hW.consistent (OrdinaryModelReceiving.finiteCutReceiving hW) (chart_symm hc) y
      exact ⟨x, descend (chart_symm hx)⟩
  | limit β hβ ih =>
    rw [@BFEquiv.limit knightLang M (structureOf (W.reduct (omegaStage_le _)))
      N (structureOf (V.reduct (omegaStage_le _))) n β hβ]
    intro γ hγ
    let h := blockStage_mono hγ.le
    have H := ih γ hγ (W.reduct h) (V.reduct h) (hW.reduct h) (hV.reduct h) (lowerChart h hc)
    rwa [Realization.reduct_reduct, Realization.reduct_reduct] at H

end VaughtConjecture.Knight
