module

public import Chazelle.Core.ShootCutShTop
public import Chazelle.UnfoldTactics

/-!
# WP-G, part 60: the ray-shooter and the arc-cutter

`shootCutSpec`: for a valid implementation `O` of Lemma 3.6, the ray-shooter `shooter O.query`
and the arc-cutter `cutter` meet `ShootCutSpec O` with the constant `κs O` (the arc-cutter's
own constant `κc` is smaller, `cutterOK_mono`).
-/

namespace Chazelle.Core

namespace ShootCut

open Machine

@[expose] public section

/-- **A larger bound** on the pieces and steps of an arc-cutter. -/
theorem cutterOK_mono {cu : Stmt} {B : Finset ℕ} {G G' H : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hc : CutterOK cu B G H X Ok) (hG : ∀ γ, G γ ≤ G' γ) :
    CutterOK cu B G' H X Ok := by
  intro P W c hw hpre hcost
  obtain ⟨c', k, ex, hk, post, fr⟩ := hc P W c hw hpre (by
    have := hG (rd c bCut 9); dsimp at hcost ⊢; omega)
  refine ⟨c', k, ex, le_trans hk (hG _), fun M hM => ?_, fr⟩
  obtain ⟨a, b, c3, rest⟩ := post M hM
  exact ⟨a, b, le_trans c3 (hG _), rest⟩

/-- **WP-G.** -/
theorem shootCutSpec (O : OracleIface) (hV : O.Valid) : ShootCutSpec O := by
  refine ⟨shooter O.query, cutter, κs O, shooter_ok hV, cutterOK_mono (cutter_ok O) ?_⟩
  intro γ
  have : κc ≤ κs O := by ufo κc κs
  exact Nat.mul_le_mul_right _ this

end

end ShootCut

end Chazelle.Core
