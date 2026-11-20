/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteCoverReceivingCore
public import VaughtConjecture.Knight.BlockStages
public import VaughtConjecture.Knight.LimitOfChain

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower KnightRealization StageType Value ExtOrd

universe w

/-- **One-sided uniform transfer.**  Let `W'` at block `β + 1` be exactly parent-consistent and
satisfy finite-cut receiving. A lawful donor `Q` on `m` points whose face along `f` is the actual
root type `p` of `tb` in `W'` is received over `tb` literally: some cover `ub` extends `tb` and
reduces to block `β` exactly as `Q` does, whatever the size of the cover.

Only the target is used. The empty root (`n = 0`) needs no separate case. Repeated
coordinates never reach this lemma: the root is an embedding, and the forth step handles a
repeated point through the chart's selector, without transfer. One direction of one step does
not give back-and-forth equivalence. -/
theorem receive_donor_uniform (β : Ordinal.{0}) {N : Type w}
    {W' : KnightRealization (blockStage (β + 1)) N} (hcons : W'.IsExactParentConsistent)
    (hFC : FiniteCutReceiving W') {n m : ℕ} (Q : S (blockStage (β + 1)).1 m)
    (f : Fin n ↪ Fin m) (tb : Fin n ↪ N) (p : S (blockStage (β + 1)).1 n)
    (hp : typeMap f Q = some p) (htb : W'.eval tb = some p) :
    ∃ (ub : Fin m ↪ N) (Q' : S (blockStage (β + 1)).1 m), f.trans ub = tb ∧
      W'.eval ub = some Q' ∧
      reduceType (blockStage β).2 (blockStage_le_succ β) Q' =
        reduceType (blockStage β).2 (blockStage_le_succ β) Q := by
  have hlt : (blockStage β).1 < (blockStage (β + 1)).1 :=
    Subtype.coe_lt_coe.mpr (blockStage_strictMono (Order.lt_add_one_iff.mpr le_rfl))
  obtain ⟨ub, Q', hfub, hub, hs, hagree⟩ :=
    FiniteCoverReceiving.finiteCoverReceiving_of_receiving hcons hFC Q f tb p hp htb
      (ofOrd (blockStage β).1) (bot_lt_ofOrd _) (ofOrd_lt_ofOrd.mpr hlt)
  refine ⟨ub, Q', hfub, hub, ext_of_scheme_label hs fun d => ?_⟩
  change truncExt (blockStage β).1 (Q'.label d) =
    truncExt (blockStage β).1 (Q.label (SemScheme.castCell hs d))
  exact min_eq_min_iff_truncExt_eq.mp (hagree d)

end VaughtConjecture.Knight
