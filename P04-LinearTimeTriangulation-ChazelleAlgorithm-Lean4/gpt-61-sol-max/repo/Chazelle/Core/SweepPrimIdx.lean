module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepPrimJun
public import Chazelle.Core.SweepLabelJG
public import Chazelle.Core.SweepLabelJL0

/-!
# Sweep RAM primitives (WP-D2), part 12: index conversions along a junction

With the constants of `junConst`, the conversions of design-merge-v2 §9.1 are index arithmetic
(design §9.6 item 5):

* `corrR`/`corrL` (offset `d` of a stretch of `M` to the walk index of `M₂`/`M₁`):
  `(g' + dq L1 δ d) mod n'` — `dqP`, then `modAdd`;
* `wholePos` (offset `d` to the walk index of `M`): `(g + d) mod n` — `modAdd`;
* the inverse direction (a walk index `p'` of `M₂`/`M₁` to its offset, and back to `M`):
  `(p' + n' - g') mod n'` — `modSub`, then `dqInv` (which also detects the box gap `δ > 0`).

Each is a standalone procedure writing only band `bLocate` (inputs `50201 … 50203`, outputs
`50210`, `50211`), with a `Meets` contract whose postcondition is the arithmetic value.  The
geometric meaning is `Sweep.Corr.sidePt_eq`, `attach_iff`, `faces_iff`, `off_M`, `off_M₂` of the
correspondences `Sweep.corr_right` and `Sweep.corr_left` (`corrR_sidePt`, `corrL_sidePt` restate
the first for the junction).  `boxTwin`: a position on a vertical side of the box is the same
position in both chain models (`boxTwin_pos`: equal radii give equal walks there).
-/

namespace Chazelle.Core

namespace SweepPrim

open Machine Machine.Stmt Programs SignK
open Chazelle.Chain (sidePt)

@[expose] public section

/-- The registers the index procedures write. -/
def Bidx (r : ℕ) : Bool := decide (50100 ≤ r ∧ r < 50110) || decide (50210 ≤ r ∧ r < 50212)

theorem Bidx_frame {c c' : Config} (h : FrameB Bidx c c') (k : ℕ) : Frame {bLocate} c c' k :=
  NFLoc.frame_of_frameB h (fun r hr => by
    ram_grind) k

/-! ## `(a + b) mod n` -/

/-! ## `(p + n - g) mod n` -/

/-! ## The offset of the other walk: `dq` and its inverse -/

/-! ## The geometric meaning -/

section
variable (J : Merge.Junction) (hP : J.P.Simple) {d : ℕ}
include hP
/-- **`corrR`**: the walk point at offset `d` of the right stretch of `M` is the walk point of
`M₂` at `dq rL1 rδ d` from its base. -/
theorem corrR_sidePt (hd : d < Sweep.rL1 J + Sweep.rL2 J) (t : ℝ) :
    sidePt (chainModel J.whole).W ((6 + WalkEmbed.tpos J.whole J.m₁ + d) %
        (chainModel J.whole).W.n) t =
      sidePt (chainModel J.right).W ((6 + WalkEmbed.tpos J.right 0 +
        Sweep.dq (Sweep.rL1 J) (Sweep.rδ J) d) % (chainModel J.right).W.n) t :=
  (Sweep.corr_right0 J hP (S₂ := ∅) (Set.empty_subset _) Set.finite_empty).sidePt_eq hd t

/-- **`corrL`**: the walk point at offset `d` of the left stretch of `M` is the walk point of
`M₁` at `dq lL1 lδ d` from its base. -/
theorem corrL_sidePt (hd : d < Sweep.lL1 J + Sweep.lL2 J) (t : ℝ) :
    sidePt (chainModel J.whole).W ((6 + WalkEmbed.tpos J.whole (J.m₁ + 2 * J.m₂) + d) %
        (chainModel J.whole).W.n) t =
      sidePt (chainModel J.left).W ((6 + WalkEmbed.tpos J.left J.m₁ +
        Sweep.dq (Sweep.lL1 J) (Sweep.lδ J) d) % (chainModel J.left).W.n) t :=
  (Sweep.corr_left0 J hP (S₁ := ∅) (Set.empty_subset _) Set.finite_empty).sidePt_eq hd t


end

/-- **`boxTwin`**: on the vertical sides of the box (walk edges `1` and `3`) two chain models with
the same box have the same positions. -/
theorem boxTwin_pos {C₁ C₂ : Chain} (hR : C₁.radius = C₂.radius) {e : ℕ} (he : e = 1 ∨ e = 3)
    (Q : Polygon) (h : ℕ) :
    (chainModel C₁).wa e = (chainModel C₂).wa e ∧ (chainModel C₁).wb e = (chainModel C₂).wb e ∧
      (chainModel C₁).param Q ⟨e, h⟩ = (chainModel C₂).param Q ⟨e, h⟩ ∧
      (chainModel C₁).pos Q ⟨e, h⟩ = (chainModel C₂).pos Q ⟨e, h⟩ := by
  have ha : (chainModel C₁).wa e = (chainModel C₂).wa e := by
    simp only [Model.wa]
    rcases he with rfl | rfl
    · rw [show (chainModel C₁).W = C₁.sideWalk C₁.sideBeta from rfl,
        show (chainModel C₂).W = C₂.sideWalk C₂.sideBeta from rfl, C₁.sideWalk_vtx_one,
        C₂.sideWalk_vtx_one, hR]
    · rw [show (chainModel C₁).W = C₁.sideWalk C₁.sideBeta from rfl,
        show (chainModel C₂).W = C₂.sideWalk C₂.sideBeta from rfl, C₁.sideWalk_vtx_three,
        C₂.sideWalk_vtx_three, hR]
  have hb : (chainModel C₁).wb e = (chainModel C₂).wb e := by
    simp only [Model.wb]
    rw [show (chainModel C₁).W = C₁.sideWalk C₁.sideBeta from rfl,
      show (chainModel C₂).W = C₂.sideWalk C₂.sideBeta from rfl,
      C₁.sideWalk_mod_small _ (by omega),
      C₂.sideWalk_mod_small _ (by omega)]
    rcases he with rfl | rfl
    · rw [C₁.sideWalk_vtx_two, C₂.sideWalk_vtx_two, hR]
    aesop
  simp_all [Model.param, Model.pos] <;> omega_nf

end

end SweepPrim

end Chazelle.Core
