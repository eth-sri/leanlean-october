module

public import Chazelle.Core.SweepEvStopFin3
public import Chazelle.Core.SweepEvStopM3
public import Chazelle.Core.SweepEvStopM4
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.MiscTactics
set_option maxHeartbeats 4000000

/-!
# The sweep (WP-D), stage 2, the finish of a stop origin: the parent (RAM)

`slfParS ps`: the parent `oPar` of the stop chord: `k + 1` for a wall code, else the parent scan
`ps` (`ParTask`) from the arrival position `(pE2, pH2)` of the origin in the walk of `C₂`
(`parent_key_iff`).  Post: the parent facts of `AuxOK` (`SlfParOK`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- **The parent step.** -/
def slfParS (ps : Stmt) : Stmt :=
  .ifLtN oKd K1 ps (.ifLtN K1 oKd ps (block [.addN oPar oKk K1]))

/-- The parent facts of `AuxOK`. -/
def SlfParOK (P : Polygon) (J : Merge.Junction) (N₂ : NF) (e : Set Point) (par : ℕ) : Prop :=
  par ≤ N₂.nChords ∧
    (∀ c ∈ N₂.F (chainModel J.right) (Qof P), e ⊆ c →
      0 < par ∧ (N₂.chord (par - 1)).toSet (chainModel J.right) (Qof P) = c) ∧
    (0 < par → e ⊆ (N₂.chord (par - 1)).toSet (chainModel J.right) (Qof P))

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-- **The parent facts from the parent scan.** -/
theorem slfParOK_scan (hP : J.P.Simple) (hN : IsNF (chainModel J.right) (Qof P) N₂)
    {kind k b : ℕ} (hD : OrgD P J N₂ kind k b) (h1 : kind ≠ 1) {p h par : ℕ}
    (hA : Arrival (chainModel J.right).W (stOrig J (Qof P) N₂ kind k b) (-dirOf b) p
      ((chainModel J.right).param (Qof P) ⟨p, h⟩))
    (hle : par ≤ N₂.nChords)
    (hpos : 0 < par → (chainModel J.right).key (Qof P) (endPos N₂ (par - 1) (1 - b)) =
      (chainModel J.right).key (Qof P) ⟨p, h⟩)
    (hzero : par = 0 → ∀ i, i < N₂.nChords → (chainModel J.right).key (Qof P)
      (endPos N₂ i (1 - b)) ≠ (chainModel J.right).key (Qof P) ⟨p, h⟩) :
    SlfParOK P J N₂ (stopSet J (Qof P) N₂ kind k b) par := by
  have hok := hD.ok
  have hb  := hok.2.1
  obtain ⟨-, -, -, haR, -⟩ := stOrig_facts hP hN hok
  have hiff := fun i (hi : i < N₂.nChords) =>
    parent_key_iff hP hN (haR h1) hb hD.free hA hi
  rw [stopSet_eq]
  have hsub : 0 < par → Merge.shoot J.whole (stOrig J (Qof P) N₂ kind k b) (dirOf b) ⊆
      (N₂.chord (par - 1)).toSet (chainModel J.right) (Qof P) := fun hp =>
    (hiff (par - 1) (by omega)).1 (hpos hp)
  refine ⟨hle, fun cc hcc hec => ?_, hsub⟩
  obtain ⟨i, hi, rfl⟩ := chord_of_mem hcc
  have hp : 0 < par := by
    by_contra h0
    exact hzero (by omega) i hi ((hiff i hi).2 hec)
  refine ⟨hp, ?_⟩
  have e := stopSet_eq J (Qof P) N₂ kind k b
  exact parent_eq hP hN hD (chord_mem (by omega)) hcc (e ▸ hsub hp) (e ▸ hec)

/-- **The parent facts of a wall code.** -/
theorem slfParOK_wall (hP : J.P.Simple) (hN : IsNF (chainModel J.right) (Qof P) N₂)
    {k b : ℕ} (hD : OrgD P J N₂ 1 k b) :
    SlfParOK P J N₂ (stopSet J (Qof P) N₂ 1 k b) (k + 1) := by
  have hk  := (hD.ok.2.2.1 rfl).1
  have hw := parent_wall hP hN hD
  unfold SlfParOK
  simp only [Nat.add_sub_cancel]
  exact ⟨hk, fun cc hcc hec => ⟨Nat.succ_pos _, parent_eq hP hN hD (chord_mem hk) hcc hw hec⟩,
    fun _ => hw⟩

/-- **The parent step.** -/
theorem slfPar_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {ps : Stmt}
    {κp : ℕ} (hps : ∀ c, IInv W c₀ c → c.nreg pE2 < (chainModel J.right).W.n →
      ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg pE2, c.nreg pH2⟩ →
      (c.nreg pH2 = 0 → 6 ≤ c.nreg pE2) → c.nreg oB ≤ 1 →
      c.nreg ALLOC + κp * (N₂.nChords + 1) ≤ W →
      IRS P W c₀ ps c (κp * (N₂.nChords + 1)) (ParOut P J N₂ c))
    (hD : OrgD P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
    (hpre : c.nreg oKd ≠ 1 → c.nreg pE2 < (chainModel J.right).W.n ∧
      ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg pE2, c.nreg pH2⟩ ∧
      Arrival (chainModel J.right).W (stOrig J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
        (-dirOf (c.nreg oB)) (c.nreg pE2)
        ((chainModel J.right).param (Qof P) ⟨c.nreg pE2, c.nreg pH2⟩))
    (hroom : c.nreg oKd ≠ 1 → c.nreg ALLOC + κp * (N₂.nChords + 1) ≤ W) :
    IRS P W c₀ (slfParS ps) c (if c.nreg oKd = 1 then 5 else κp * (N₂.nChords + 1) + 4)
      (fun c' => SlfParOK P J N₂ (stopSet J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
        (c'.nreg oPar) ∧ SlfFr ParR c c') := by
  have hP := E.hP
  have hN := E.hNF₂
  obtain ⟨k0, k1, -⟩ := E.hK.fix hI
  have hk2  := hD.ok.1
  have hb  := hD.ok.2.1
  -- the scan
  have scan : c.nreg oKd ≠ 1 → IRS P W c₀ ps c (κp * (N₂.nChords + 1))
      (fun c' => SlfParOK P J N₂ (stopSet J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
        (c'.nreg oPar) ∧ SlfFr ParR c c') := by
    intro h1
    obtain ⟨he, hpp, hA⟩ := hpre h1
    obtain ⟨-, -, hy, -, -⟩ := stOrig_facts hP hN hD.ok
    have h6 : c.nreg pH2 = 0 → 6 ≤ c.nreg pE2 := fun h0 =>
      h6_of_abs J.right (Qof P) (x := ⟨c.nreg pE2, c.nreg pH2⟩) (by
        rwx [pos_eq_sidePt', hA.2.2.2.1, radius_right]) h0
    refine (hps c hI he hpp h6 hb (hroom h1)).mono le_rfl ?_
    rintro c' ⟨hle, hpos, hzero, hm, hA', fr⟩
    exact ⟨slfParOK_scan hP hN hD h1 hA hle hpos hzero, fr, hA', hm⟩
  unfold slfParS
  by_cases h0 : c.nreg oKd < c.nreg K1
  · have hk : c.nreg oKd ≠ 1 := by omega
    rw [ite_eq_right hk]
    exact (IRS.ifT h0 (scan hk)).mono (by omega) (fun _ => id)
  · refine (IRS.ifF (K := if c.nreg oKd = 1 then 3 else κp * (N₂.nChords + 1) + 2) h0 ?_).mono
      (by splao) (fun _ => id)
    by_cases h2 : c.nreg K1 < c.nreg oKd
    · have hk : c.nreg oKd ≠ 1 := by omega
      rw [ite_eq_right hk]
      exact IRS.ifT h2 (scan hk)
    · have hk : c.nreg oKd = 1 := by omega
      rw [ite_eq_left hk]
      have hD1  := hk ▸ hD
      have hkK  := (hD1.ok.2.2.1 rfl).1
      have hTW := E.hTW
      have hpar : IScr oPar := iscr_sw' (by norm_num) (by norm_num)
      refine IRS.ifF h2 ((IRS.block [.addN oPar oKk K1] hI
        ⟨⟨hpar, by first | (rwo [k1])⟩, trivial⟩).mono (by simp) ?_)
      rintro c' rfl
      have hv : regB c.nmem [.addN oPar oKk K1] c.nreg oPar = c.nreg oKk + 1 := by
        simp only [regB, regI, upd_same]; rw [k1]
      refine ⟨by simp only; rw [hv, hk]; exact slfParOK_wall hP hN hD1, fun r _ hr _ => ?_,
        ?_, fun _ _ => rfl⟩
      · simp only [regB, regI]
        rw [upd_other _ _ _ (fun h => hr (Or.inl h))]
      · simp only [regB, regI]
        rw [upd_other _ _ _ (by ufo ALLOC oPar sw)]

end

end SweepEv

end Chazelle.Core
