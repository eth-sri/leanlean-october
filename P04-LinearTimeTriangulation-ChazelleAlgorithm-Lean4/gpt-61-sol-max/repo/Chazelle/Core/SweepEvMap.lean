module

public import Chazelle.Core.SweepEvStep

/-!
# The sweep (WP-D), stage 3: the `C₁` part of the walk of `C` read in the walk of `C₁`

The `C₁` part of the walk of `M = chainModel J.whole` (offsets `[Lst, n)` from `gW`) is the walk of
`M₁ = chainModel J.left` read from the vertex `b₁` (`= g₁ = 6 + tpos C₁ m₁`, except `2m₁ + 6`
when the box block of `M` precedes the left stretch, case `Lst < lOff`), for `E₁` steps; the
position at `b₁`-offset `d` corresponds to the offset `Lst + ψ d` of `M` (`ψ` is the identity
except in the left case G, where the box block of `M₁` is a gap `[lL1, lL1 + 7]` whose two ends are
the split vertex).  `MValid d t`: the position has a counterpart and its point is not `v`.

* `map_sound`: a genuine hit of the model of `C₁` arriving at such a position (which is the hit of
  `C`) gives the chord of `C` attached at the corresponding position of `M`, at offset
  `Lst + ψ d + t`;
* `map_complete`: conversely, a chord of `C` seen from `a` (not above the top of `C₁`) whose far
  attachment lies beyond the start (not at `v`) is a genuine hit of the model of `C₁`, arriving at
  a valid position that corresponds to the attachment.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

section Map

variable (J : Merge.Junction)

/-- The first vertex of the walk of `C₁` read along the `C₁` part. -/
noncomputable def b₁ : ℕ := if Lst J < lOff J then 2 * J.left.m + 6 else 6 + tpos J.left J.m₁

/-- The number of steps of the walk of `C₁` read along the `C₁` part. -/
noncomputable def E₁ : ℕ := (chainModel J.whole).W.n - Lst J + lδ J

section
variable (d : ℕ)
include d
/-- The `C₁`-part offset (beyond `Lst`) of the `b₁`-offset `d`. -/
noncomputable def ψ : ℕ :=
  if 0 < lδ J ∧ lL1 J < d then (if d < lL1 J + lδ J then lL1 J else d - lδ J) else d

/-- The walk edge of `M` at the `C₁`-part offset of `d`. -/
noncomputable def mEdge : ℕ := (gW J + (Lst J + ψ J d)) % (chainModel J.whole).W.n

/-- A `b₁`-offset `d` and parameter `t` of the walk of `C₁` with a counterpart on the `C₁` part,
whose point is not the shared vertex. -/
def MValid (t : ℝ) : Prop :=
  d < E₁ J ∧ ¬ (0 < lδ J ∧ lL1 J < d ∧ d < lL1 J + lδ J) ∧ ¬ (0 < lδ J ∧ d = lL1 J ∧ t ≠ 0) ∧
    (t = 0 → sidePt (chainModel J.left).W ((b₁ J + d) % (chainModel J.left).W.n) 0 ≠ J.shared)

/-! ## The cases -/


end

theorem vtx_tpos' (C : Chain) {k : ℕ} (hk : k ≤ C.m) :
    (chainModel C).W.vtx (6 + tpos C k) = C.vertex k := by
  have hn := cm_n C
  have hτ := tpos_lt C k
  
  have := walk_tour C k 0 (by omega)
  rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega)] at this
  rw [this]
  unfold tourV
  rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  grind [Chazelle.Chain.sideE]

theorem Lst_rlen : Lst J = rlen J := rL1_add_rL2 J

/-- When `v` is the top of `C` it is the top of `C₁`, at the tour position `0` of `C₁`, and the left
correspondence has no gap. -/
theorem nvt_left (hP : J.P.Simple) (hv : ¬ VNotTop J) :
    tpos J.left J.m₁ = 0 ∧ lδ J = 0 ∧ lL1 J = 2 * J.m₁ ∧ lL2 J = 0 ∧ llen J = 2 * J.m₁ := by
  have htop := left_top_eq J hv
  have hm1 : J.left.m = J.m₁ := rfl
  have hk : J.left.topIdx = J.m₁ := by
    have h1 : J.left.vertex J.left.topIdx = J.left.vertex J.m₁ := htop
    exact J.left.sideVertex_inj hP J.left.topIdx_le (by rw [hm1]) h1
  have h1 := J.one_le_m₁
  have hτ : tpos J.left J.m₁ = 0 := by
    unfold tpos bS Chain.sideS
    rw [hk, hm1]
    split_ifs
    · simp_all
    · rw [show J.m₁ + 2 * J.m₁ - (2 * J.m₁ - J.m₁) = 2 * J.m₁ by omega, Nat.mod_self]
  
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  have hA : ¬ 2 * J.whole.m - tpos J.whole (J.m₁ + 2 * J.m₂) < 2 * J.m₁ := by
    rw [tpos_second J]
    
    
    have hm2 : J.right.m = J.m₂ := rfl
    rcases vtop_cases J hv with h | h
    · rw [h, zero_add, Nat.mod_eq_of_lt (show 2 * J.m₂ < 2 * J.whole.m by omega)]
      omega
    simp_all
  grind [lδ, lL1, lL2, llen]

/-- Case b: the box block of `M` precedes the left stretch. -/
theorem caseB_facts (hlt : Lst J < lOff J) :
    ¬ VNotTop J ∧ lOff J = Lst J + 7 ∧ tpos J.whole J.m₁ + 2 * J.m₂ = 2 * J.whole.m ∧
      Lst J = 2 * J.m₂ := by
  have hτ := tpos_lt J.whole J.m₁
  grind [Lst_rlen, lOff_eq, rlen, VNotTop]

/-- Case c: `v` is the top of `C` and the box block of `M` follows the left stretch. -/
theorem caseC_facts (hv : ¬ VNotTop J) (hle : ¬ Lst J < lOff J) :
    tpos J.whole J.m₁ = 0 ∧ lOff J = Lst J ∧ Lst J = 2 * J.m₂ := by
  have hτ := tpos_lt J.whole J.m₁
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  
  
  have hc := vtop_cases J hv
  grind [Lst_rlen, lOff_eq, rlen]

/-- The base of the left stretch is `gW + lOff`. -/
theorem gL_eq : (gW J + lOff J) % (chainModel J.whole).W.n = 6 + tpos J.whole (J.m₁ + 2 * J.m₂) := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hτ := tpos_lt J.whole J.m₁
  have hτ' := tpos_lt J.whole (J.m₁ + 2 * J.m₂)
  unfold gW lOff
  exact add_dOf (by omega) (by omega)

/-- The walk edge of the left stretch at `d` is the edge at offset `lOff + d`. -/
theorem left_edge_eq (d : ℕ) :
    (6 + tpos J.whole (J.m₁ + 2 * J.m₂) + d) % (chainModel J.whole).W.n =
      (gW J + (lOff J + d)) % (chainModel J.whole).W.n := by
  rw [← gL_eq J, ← add_assoc, Nat.mod_add_mod]

end Map

end Sweep

end

end Chazelle.Core
