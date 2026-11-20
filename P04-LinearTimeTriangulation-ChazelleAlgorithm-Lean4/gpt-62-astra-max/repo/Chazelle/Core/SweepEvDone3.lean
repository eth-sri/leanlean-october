module

public import Chazelle.Core.SweepEvDone2

/-!
# The sweep (WP-D), stage 3: task L2 from the absence of cuts after the last key

`DoneNoCut`: in the last iteration (`dF = 1`: no best candidate, no stop left, the window runs to
the part end), no cut of `F₂⁺` lies after the key of the iteration (the shared step-1 fact of
tasks L1/L2).  `doneTask_of : DoneNoCut → DoneTask`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-- **No cut after the last key** (the step-1 fact of the last iteration). -/
def DoneNoCut : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction) (N₁ N₂ : NF)
    (c cw cs co c' : Config), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ →
    LoopInv P J N₁ N₂ c₀ c → IterRel P J N₁ N₂ c cw cs co c' → c'.nreg dF = 1 →
    NoCutIn J (N₂.F (chainModel J.right) (Qof P)) (keyOff P J c) (chainModel J.whole).W.n

/-- **Task L2 from the absence of cuts after the last key.** -/
theorem doneTask_of (h : DoneNoCut) : DoneTask := by
  intro sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' E hL hIt hd
  exact done_out E hL hIt hd (h sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' E hL hIt hd)

end

end SweepEv

end Chazelle.Core
