module

public import Chazelle.Core.SweepIoS0CandQMath

/-!
# The sweep RAM (WP-D), answers: the side-0 stop and table candidates of a query, part 1

* `compl_of`: the completeness clauses of `S0CandSpec` (stop records and regular table entries
  at the query position) follow from the completeness of the slot read: for the log record of
  the query position with a flagged slot, the parameter of every candidate origin is offered.
* The program `candQ ls` (with the binary search `ls` of `LSearchSpec`): search the query
  position in the log, check that the record found has that position (`callOff`, both bits `0`),
  read the slot of the query direction and offer its origin (`offerF`, tag `1`).
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Set
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt SideAttach)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {E : ℕ} {c₀ : Config}

/-- **The completeness clauses** from the completeness of the slot read. -/
theorem compl_of (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hX : AuxCore P J N₂ c₀) {z : Point}
    {zp zh d : ℕ} {L' : Set ℝ}
    (harr : Arrival (chainModel J.whole).W z (-dirOf d) zp
      ((chainModel J.whole).param (Qof P) ⟨zp, zh⟩))
    (H : ∀ i, i < rd c₀ bSweep 301 → c₀.nmem (rd c₀ bSweep 300 + 7 * i) = zp →
      (chainModel J.whole).param (Qof P) (logPos c₀.nmem (rd c₀ bSweep 300) i) =
        (chainModel J.whole).param (Qof P) ⟨zp, zh⟩ →
      c₀.nmem (slotA (c₀.nreg sB) i (qS d)) = 1 →
      ∀ (o : Point) (τ : ℝ), CandAt J o (dS (qS d)) z → 0 < τ → o = rayPt z (dirOf d) τ →
        τ ∈ L') :
    (∀ (rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)), rs.length = rd c₀ bSweep 201 →
      StopRecsAt c₀.nmem (rd c₀ bSweep 200) rs →
      ∀ r ∈ rs, r.1 = zp →
        (chainModel J.whole).param (Qof P) ⟨r.1, r.2.1⟩ =
          (chainModel J.whole).param (Qof P) ⟨zp, zh⟩ →
        dirOf r.2.2.2.2 = -dirOf d →
        ∀ τ, 0 < τ → stopOrig J (Qof P) N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 =
          rayPt z (dirOf d) τ → τ ∈ L') ∧
    (∀ j, j < 2 * N₂.nChords →
      tabOf J (Qof P) c₀.nmem (rd c₀ bSweep 302) j =
        some (zp, (chainModel J.whole).param (Qof P) ⟨zp, zh⟩) →
      endDir j = -dirOf d → endOrigin J (Qof P) N₂ j ∈ J.right.set →
      endOrigin J (Qof P) N₂ j ≠ J.shared → endOrigin J (Qof P) N₂ j ≠ J.right.top →
      ∀ τ, 0 < τ → endOrigin J (Qof P) N₂ j = rayPt z (dirOf d) τ → τ ∈ L') := by
  refine ⟨fun rs hrsl hrs r hr hr1 hr2 hdir τ hτ ho => ?_,
    fun j hj hT hdir hv1 hv2 hv3 τ hτ ho => ?_⟩
  · obtain ⟨i, hi, e1, e2, e3, hc⟩ := stop_match hA hX harr hrsl hrs hr hr1 hr2
    have hs : sOf r.2.2.2.2 = qS d := by
      apply dS_inj (sOf_le _) (qS_le _)
      grind [dS_sOf, dS_qS]
    rw [hs] at e3
    rw [← dS_sOf, hs] at hc
    exact H i hi (congrArg WPos.edge e1) e2 e3 _ τ hc hτ ho
  · obtain ⟨i, hi, e1, e2, e3, hc⟩ := tab_match hA hX harr hj hT ⟨hv1, hv2, hv3⟩
    have hs : j % 2 = qS d := by
      apply dS_inj (by omega) (qS_le _)
      grind [dS_mod, dS_qS]
    rw [hs] at e3
    rw [← dS_mod, hs] at hc
    exact H i hi (congrArg WPos.edge e1) e2 e3 _ τ hc hτ ho

/-! ## Registers and program -/

def kA : ℕ := sw 4100
def kE : ℕ := sw 4101
def kH : ℕ := sw 4102
def kO : ℕ := sw 4104
def kS : ℕ := sw 4106
def kF : ℕ := sw 4107
def kPe : ℕ := sw 4108
def kPh : ℕ := sw 4109
def kPo : ℕ := sw 4110

/-- Copy the query position to the target registers of the search. -/
def cIn : List Instr := [.copyN lsxE zP, .copyN lsxH zPh]

/-- The key of the log record found. -/
def cAddr : List Instr :=
  [.copyN kA (sw 300), .addN kA kA lsI, .addN kA kA lsI, .addN kA kA lsI, .addN kA kA lsI,
    .addN kA kA lsI, .addN kA kA lsI, .addN kA kA lsI, .loadN kE kA, .addN kA kA K1, .loadN kH kA]

/-- The address of the slot of the log record found (east). -/
def cSlot : List Instr :=
  [.copyN kS sB, .addN kS kS lsI, .addN kS kS lsI, .addN kS kS lsI, .addN kS kS lsI,
    .addN kS kS lsI, .addN kS kS lsI]

/-- The slot of the query direction: west (`+ 3`) for the direction code `1`. -/
def cDir : Stmt := .ifLtN qD K1 .skip (.ifLtN K1 qD .skip (.instr (.addN kS kS K3)))

/-- Read the slot. -/
def cRead : List Instr :=
  [.loadN kF kS, .addN kS kS K1, .loadN kPe kS, .addN kS kS K1, .loadN kPh kS]

/-- Offer the origin of a flagged slot. -/
def cOffer : Stmt := .ifLtN K0 kF (offerF accA (sw 21) kPe kPh K1 qD (sw 34) kPo) .skip

/-- The slot part. -/
def cHit : Stmt := .seq (block cSlot) (.seq cDir (.seq (block cRead) cOffer))

/-- The check of the record found and the slot part. -/
def cCheck : Stmt :=
  .seq (block cAddr) (.seq (callOff (sw 2) kE kH lsxE lsxH (sw 40) kO)
    (.ifLtN K0 kO .skip (.ifLtN K0 (kO + 1) .skip cHit)))

/-- **The per-query procedure** (with the binary search `ls`). -/
def candQ (ls : Stmt) : Stmt :=
  .seq (block cIn) (.seq ls (.ifLtN lsI (sw 301) cCheck .skip))

end

end S0C

end SweepIo

end Chazelle.Core
