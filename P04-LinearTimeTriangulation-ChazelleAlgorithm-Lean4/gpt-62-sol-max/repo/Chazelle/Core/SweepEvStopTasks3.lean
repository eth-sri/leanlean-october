module

public import Chazelle.Core.SweepEvStopRD
public import Chazelle.Core.SweepEvStopTasks2

/-!
# The sweep (WP-D), stage 2: contracts of the pieces of the per-origin step

The per-origin step `org` (`OrgTask`) for a code `(kind, k, b)` (registers `oKd, oKk, oB`), with
origin `a = stOrig` and direction `σ = dirOf b`:

1. `stLoad` (`stLoad_irs`, done): the admissibility flag `oAd` and the origin's position
   `(oPE, oPH)` in the walk of `C₂` (`OrgPos`);
2. `stA` (`stA_irs`, done): the freeness flag `oF0` and the attachment `A₀ = (oF0 + 1, oF0 + 2)` at
   the origin in the walk of `C`;
3. **`M2Task`**: the candidate of `C₂` for the far end (`r2F … r2F + 6`, `ResOK`), and the arrival
   position `(pE2, pH2)` of the origin in the walk of `C₂` (shared and top codes);
4. **`M1Task`**: the candidate of `C₁` for the far end (`r1F … r1F + 6`, `ResOK`);
5. the winner of the two candidates, its position in the walk of `C`, and the
   attachment `A₁ = (a1F + 1, a1F + 2)` at the far end;
6. **`FinTask`**: the offsets, the parent, the labels, and the emission of the raw records
   (`OrgOut`);
7. **`NoParCut`** (mathematics): without a parent, the counterpart in the walk of `C₂` of a
   stretch attachment of a stop chord (inside a walk edge) is not a cut of `S₂` (the precondition
   of `FaceRTask` there).

Register map of the per-origin step (all `sw i`): code `4010 … 4012`, `oNB 4013`, `oPE, oPH 4014,
4015`, `oAd 4019`, `oF0 4020 … 4022` (`A₀`), `m2F, pE2, pH2 4024 … 4026`, `4027 … 4029` (scratch
of the `M₁` candidate), `r1F 4030 … 4036`, `r2F 4040 … 4046`, `4047 … 4049` (winner),
`a1F 4050 … 4052` (`A₁`), `4054 … 4067` (free for `FinTask`: offsets, anchor, labels, parent
`oPar 4064`), `4068 … 4079` (`ParTask`), `4080 … 4091` (`BruteTask`), `4092 … 4095` (`stLoad`),
`4096 … 4109`, `4116 … 4199` (scratch), `4110 … 4115` (`FaceRTask`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-! ## Registers -/

def m2F : ℕ := sw 4024
def r1F : ℕ := sw 4030
def r2F : ℕ := sw 4040
def a1F : ℕ := sw 4050

/-! ## The candidate of `C₂` -/

/-- The registers the candidate of `C₂` may write (besides the oracle bands and the allocator). -/
def M2R (r : ℕ) : Prop :=
  (sw 700 ≤ r ∧ r < sw 2200) ∨ (sw 3000 ≤ r ∧ r < sw 4000) ∨ (sw 4024 ≤ r ∧ r ≤ sw 4026) ∨
    (sw 4040 ≤ r ∧ r ≤ sw 4046) ∨ (sw 4096 ≤ r ∧ r < sw 4110) ∨ (sw 5000 ≤ r ∧ r < sw 6000)

/-- **The post of the candidate of `C₂`**: a saved candidate of the first hit of `C₂` from the
origin (`ResOK` at `r2F`, good when the direction is free for `C₂`); for the shared and top codes
(origin on `C₂`), if the direction is free for `C₂`, the arrival position `(pE2, pH2)` of the origin
in the walk of `C₂` (direction `-σ`). -/
def M2Out (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) (c' : Config) : Prop :=
  ResOK P J.right (stOrig J (Qof P) N kind k b) (dirOf b)
      (FreeAt J.right (stOrig J (Qof P) N kind k b) (dirOf b)) r2F c' ∧
    (kind ≠ 1 → FreeAt J.right (stOrig J (Qof P) N kind k b) (dirOf b) →
      c'.nreg pE2 < (chainModel J.right).W.n ∧
      ProperPos (chainModel J.right) (Qof P) P.n ⟨c'.nreg pE2, c'.nreg pH2⟩ ∧
      Arrival (chainModel J.right).W (stOrig J (Qof P) N kind k b) (-dirOf b) (c'.nreg pE2)
        ((chainModel J.right).param (Qof P) ⟨c'.nreg pE2, c'.nreg pH2⟩))

/-- **Task M2: the candidate of `C₂`** for an admissible code with a free direction (`OrgD`), from
the origin's position `(oPE, oPH)` in the walk of `C₂` (`OrgPos`), with the model context of `C₂`
at `gMD2, gCD2, sw 4`, cost `κ D (F γ + TLR + 1)`.  (Shared and top codes: `callArr` in the walk
of `C₂` from `(oPE, oPH)`, then `lhSave` from the arrival; wall codes: `lhSave` from
`(oPE, oPH)`.) -/
def M2Task : Prop :=
  ∃ (m2 : Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) c →
      OrgD P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) →
      OrgPos P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) (c.nreg oPE) (c.nreg oPH) →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ (m2 sh) c (κ (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))
        (fun c' => M2Out P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c' ∧ EFr M2R c c')

/-! ## The candidate of `C₁` -/

/-- The registers the candidate of `C₁` may write (besides the oracle bands and the allocator). -/
def M1R (r : ℕ) : Prop :=
  (sw 700 ≤ r ∧ r < sw 2200) ∨ (sw 3000 ≤ r ∧ r < sw 4000) ∨ (sw 4027 ≤ r ∧ r ≤ sw 4036) ∨
    (sw 4068 ≤ r ∧ r < sw 4092) ∨ (sw 4096 ≤ r ∧ r < sw 4110) ∨ (sw 5000 ≤ r ∧ r < sw 6000)

/-- **Task M1: the candidate of `C₁`** (`ResOK` at `r1F`, good when the origin is not above the
top of `C₁` and the direction is free for `C₁`) for an admissible code with a free direction, from
the origin's position `(oPE, oPH)` in the walk of `C₂`, cost `κ D (F γ + TLR + 1)` for a wall code,
`κ D (K₁ + K₂ + 1) (F γ + TLR + 1)` otherwise.  (Shared code: `callArr` in the walk of `C₁` from
`(cstL 1, 0)`, then `lhSave` with `MD₁, CD₁, sw 3`; wall code: `lhSave` from `(oPE, oPH)` in the
walk of `C₁` (`boxTwin_pos`); top code: unless the top of `C₂` is above the top of `C₁`, the
brute-force shot `BruteTask` from it.) -/
def M1Task : Prop :=
  ∃ (m1 : Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      OrgD P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) →
      OrgPos P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) (c.nreg oPE) (c.nreg oPH) →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ (m1 sh) c (κ (c₀.nreg (sw 6)) * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))
        (fun c' => ResOK P J.left (stOrig J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
          (dirOf (c.nreg oB))
          (FreeAt J.left (stOrig J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
              (dirOf (c.nreg oB)) ∧
            (stOrig J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB)).2 ≤ J.left.top.2)
          r1F c' ∧ EFr M1R c c')

/-! ## The finish: offsets, parent, labels, records -/

/-- **The precondition of the finish**: the attachment `A₀` at the origin (`oF0 + 1, oF0 + 2`,
the arrival of the origin in direction `-σ`), the attachment `A₁` at the far end
(`a1F + 1, a1F + 2`, the arrival of `farPt` in direction `σ`), both positions of the walk of `C`;
for the shared and top codes the arrival position `(pE2, pH2)` of the origin in the walk of
`C₂`. -/
def FinPre (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) (c : Config) : Prop :=
  c.nreg (oF0 + 1) < (chainModel J.whole).W.n ∧
    ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg (oF0 + 1), c.nreg (oF0 + 2)⟩ ∧
    Arrival (chainModel J.whole).W (stOrig J (Qof P) N kind k b) (-dirOf b) (c.nreg (oF0 + 1))
      ((chainModel J.whole).param (Qof P) ⟨c.nreg (oF0 + 1), c.nreg (oF0 + 2)⟩) ∧
    c.nreg (a1F + 1) < (chainModel J.whole).W.n ∧
    ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg (a1F + 1), c.nreg (a1F + 2)⟩ ∧
    Arrival (chainModel J.whole).W (farPt J.whole (stOrig J (Qof P) N kind k b) (dirOf b))
      (dirOf b) (c.nreg (a1F + 1))
      ((chainModel J.whole).param (Qof P) ⟨c.nreg (a1F + 1), c.nreg (a1F + 2)⟩) ∧
    (kind ≠ 1 → c.nreg pE2 < (chainModel J.right).W.n ∧
      ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg pE2, c.nreg pH2⟩ ∧
      Arrival (chainModel J.right).W (stOrig J (Qof P) N kind k b) (-dirOf b) (c.nreg pE2)
        ((chainModel J.right).param (Qof P) ⟨c.nreg pE2, c.nreg pH2⟩))

/-- **Task Fin: the finish of the per-origin step** for an admissible code with a free direction:
the offsets of `A₀`, `A₁` (`callOff` against `Lst` and `0`: the records on the `C₁` part, anchor,
pocket, `anc_pocket_iff`), the parent (`k + 1` for a wall code, else `ParTask` from `(pE2, pH2)`,
`parent_key_iff`), the labels (the regions `up, dn` of the parent, else `FaceRTask` at the
counterpart of the stretch attachment, `LabTask`, `NoParCut`), and the raw records of `A₀`
(`dc = b`) and `A₁` (`dc = 1 - b`) on the `C₁` part (`orig_attach`, `attach_two`), as `OrgOut`.
Cost as `OrgTask`. -/
def FinTask : Prop :=
  ∃ (fin : Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      OrgD P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) →
      FinPre P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c →
      c₀.nreg ALLOC ≤ c.nreg gRB → c.nreg gRB + 11 * (c.nreg gRC + 2) ≤ c.nreg ALLOC →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ fin c (κ (c₀.nreg (sw 6)) * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))
        (OrgOut P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c)

/-! ## The counterpart of a stretch attachment without a parent (mathematics) -/

/-- **Task N (mathematics)**: a stop chord `e ∈ F₂⁺` contained in no chord of `S₂`, attached at
the position `(gW + d, t)` of the open right stretch inside a walk edge (`0 < t < 1`): the
counterpart key `cpA d + t` of the walk of `C₂` is not a cut of `S₂` (a chord of `S₂` attached
there contains a chord of `F₂⁺` attached at `(gW + d, t)`, `Corr0.transfer`; two chords of `F₂⁺`
attached at the same position inside a walk edge are nested, hence equal, `Corr0.nest`). -/
def NoParCut : Prop :=
  ∀ (J : Merge.Junction) (Q : Polygon) (S₂ : Set (Set Point)) (e : Set Point), J.P.Simple →
    (chainModel J.right).ChordFamily Q S₂ → e ∈ F₂plus J S₂ → (∀ c ∈ S₂, ¬ e ⊆ c) →
    ∀ (d : ℕ) (t : ℝ), d < Lst J → 0 < t → t < 1 →
    SideAttach (chainModel J.whole).W e ((gW J + d) % (chainModel J.whole).W.n) t →
    ¬ (chainModel J.right).IsCut S₂ ((cpA J d : ℝ) + t)

end

end SweepEv

end Chazelle.Core
