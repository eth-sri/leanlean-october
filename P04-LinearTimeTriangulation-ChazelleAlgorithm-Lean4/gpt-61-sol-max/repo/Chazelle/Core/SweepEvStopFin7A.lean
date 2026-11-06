module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvStopFin7S

/-!
# The sweep (WP-D), stage 2: the emission of the raw records (helpers)

* `slfRec_words`: the raw record of the words `slfWords pe ph dc` of a configuration;
* `slfRawV`: a raw record of an attachment of the stop chord on the `C₁` part is valid (`RawV`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Chain (SideAttach sidePt)

@[expose] public section

variable {P : Polygon} {J : Merge.Junction} {N : NF}

/-- **The raw record of the emitted words.** -/
theorem slfRec_words {m : ℕ → ℕ} {RB j pe ph dc : ℕ} {cc : Config}
    (hw : ∀ i, i < 11 → m (RB + 11 * j + i) = cc.nreg ((slfWords pe ph dc).getD i 0)) :
    rawRec m RB j = (cc.nreg pe, cc.nreg ph, cc.nreg oKd, cc.nreg oKk, cc.nreg oB) ∧
      rawDc m RB j = cc.nreg dc ∧
      rawAux m RB j = (cc.nreg slfA, cc.nreg slfN, cc.nreg slfL0, cc.nreg slfL1, cc.nreg oPar) := by
  have w : ∀ i, i < 11 → m (RB + 11 * j + i) = cc.nreg ((slfWords pe ph dc).getD i 0) := hw
  have w0 := w 0 (by norm_num)
  simp_all [slfWords, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, rawRec, rawDc, rawAux] <;> omega_nf

/-- **A valid raw record.** -/
theorem slfRawV {kind k b : ℕ} (hD : OrgD P J N kind k b) {d : ℕ} (hd : d ≤ 1) {p h : ℕ}
    (hA : SideAttach (chainModel J.whole).W (stopSet J (Qof P) N kind k b) p
      ((chainModel J.whole).param (Qof P) ⟨p, h⟩))
    (hpt : sidePt (chainModel J.whole).W p ((chainModel J.whole).param (Qof P) ⟨p, h⟩) =
      (if d = 1 then Merge.lend (stopSet J (Qof P) N kind k b)
        else Merge.rend (stopSet J (Qof P) N kind k b)))
    (hL : (Lst J : ℝ) ≤ oW J (p + (chainModel J.whole).param (Qof P) ⟨p, h⟩))
    (hpw : PosW P J p h) {x : ℕ × ℕ × ℕ × ℕ × ℕ}
    (hax : AuxOK P J N (stopSet J (Qof P) N kind k b) x) {m : ℕ → ℕ} {RB j : ℕ}
    (hr : rawRec m RB j = (p, h, kind, k, b)) (hdc : rawDc m RB j = d) (hx : rawAux m RB j = x) :
    RawV P J N m RB j := by
  unfold RawV
  rw [hr, hdc, hx]
  exact ⟨⟨hD.ok, hD.free, hA, hL, hd, hpt⟩, hpw, hax⟩

/-- The raw record only reads its eleven words. -/
theorem slfRec_congr {m m' : ℕ → ℕ} {RB j : ℕ}
    (h : ∀ i, i < 11 → m' (RB + 11 * j + i) = m (RB + 11 * j + i)) :
    rawRec m' RB j = rawRec m RB j ∧ rawDc m' RB j = rawDc m RB j ∧
      rawAux m' RB j = rawAux m RB j := by
  have h0 := h 0 (by norm_num)
  simp_all [Nat.add_zero, rawRec, rawDc, rawAux] <;> omega_nf

variable {W : ℕ} {c₀ : Config}

/-- **A conditional emission**: skipped when the bit is set. -/
theorem slfMaybe_irs {bitr pe ph dc : ℕ} (hpe : pe ≠ slfX) (hph : ph ≠ slfX) (hdc : dc ≠ slfX)
    {c : Config} (hI : IInv W c₀ c) (hk0 : c.nreg K0 = 0) (hk1 : c.nreg K1 = 1)
    (hA : c₀.nreg ALLOC ≤ c.nreg gRB) (hW : c.nreg gRB + 11 * (c.nreg gRC + 1) ≤ W)
    (hb : c.nreg bitr ≤ 1) :
    IRS P W c₀ (.ifLtN K0 bitr .skip (slfEmit pe ph dc)) c 37 (fun c' =>
      c'.nreg gRC = c.nreg gRC + (if c.nreg bitr = 1 then 0 else 1) ∧
      (c.nreg bitr ≠ 1 → ∀ i, i < 11 → c'.nmem (c.nreg gRB + 11 * c.nreg gRC + i) =
        c.nreg ((slfWords pe ph dc).getD i 0)) ∧
      (∀ a, (a < c.nreg gRB + 11 * c.nreg gRC ∨ c.nreg gRB + 11 * c.nreg gRC + 11 ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ slfX → r ≠ gRC → c'.nreg r = c.nreg r)) := by
  refine IRS.ite (fun h => ?_) (fun h => ?_)
  · have h1 : c.nreg bitr = 1 := by omega
    refine IRS.skip hI ⟨by simp_all, fun h' => absurd h1 h', fun _ _ => rfl,
      fun _ _ _ => rfl⟩
  · have h1 : c.nreg bitr ≠ 1 := by omega
    refine (slfEmit_irs hpe hph hdc hI hk1 hA hW).mono (by norm_num) ?_
    ram_grind

end

end SweepEv

end Chazelle.Core
