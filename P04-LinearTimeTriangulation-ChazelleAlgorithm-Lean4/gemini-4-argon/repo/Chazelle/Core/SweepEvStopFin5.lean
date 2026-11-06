module

public import Chazelle.Core.SweepEvStopFin4
public import Chazelle.Core.SweepEvStopFinS0
public import Chazelle.Core.SweepEvStopLabFinal
public import Chazelle.Core.SweepEvStepL0
public import Chazelle.Core.SweepEvLabM
public import Chazelle.Core.SweepMachine9

/-!
# The sweep (WP-D), stage 2, the finish of a stop origin: the side labels (mathematics)

The side labels of an anchored stop chord (not a pocket, with an attachment on the `C₁` part) from
`LabTask`: the regions above and below its parent (`slf_lab_par`), else the regions faced at the
counterpart of its stretch attachment (`slf_lab_str`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

theorem slf_labSet2 (J : Merge.Junction) (Q : Polygon) (N : NF) (l₀ l₁ l₂ l₃ : ℕ) :
    labSet J Q N 2 l₀ l₁ l₂ l₃ =
      {regOf (chainModel J.right) Q N l₀, regOf (chainModel J.right) Q N l₁} := by
  ext V
  simp only [labSet, Set.mem_image, mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rcases hl with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
    · omega
  · rintro (rfl | rfl)
    · exact ⟨l₀, Or.inl ⟨by norm_num, rfl⟩, rfl⟩
    · exact ⟨l₁, Or.inr (Or.inl ⟨by norm_num, rfl⟩), rfl⟩

/-- A stretch attachment: its offset `d`. -/
theorem slf_stretch (hP : J.P.Simple) (hN : IsNF (chainModel J.right) (Qof P) N₂) {p : ℕ} {t : ℝ}
    (hp : p < (chainModel J.whole).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) (h0 : 0 < oW J (p + t))
    (hL : oW J (p + t) < Lst J) :
    ∃ d, d < Lst J ∧ (t = 0 → d ≠ 0) ∧ p = (gW J + d) % (chainModel J.whole).W.n :=
  stretch_decomp J hP hN.1.2.1 hN.1.1 hp ht0 ht1 h0 (by exact_mod_cast hL)

/-- **The side labels below and above the parent.** -/
theorem slf_lab_par (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {kind k b : ℕ}
    (hD : OrgD P J N₂ kind k b) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W (stopSet J (Qof P) N₂ kind k b) p t)
    (h0 : 0 < oW J (p + t)) (hL : oW J (p + t) < Lst J)
    (hnp : ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W (stopSet J (Qof P) N₂ kind k b)
      q s → oW J (q + s) ≠ 0)
    (hC1 : ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W (stopSet J (Qof P) N₂ kind k b)
      q s ∧ (Lst J : ℝ) ≤ oW J (q + s))
    {i : ℕ} (hi : i < N₂.nChords)
    (hsub : stopSet J (Qof P) N₂ kind k b ⊆ (N₂.chord i).toSet (chainModel J.right) (Qof P)) :
    EvSideLab J (N₂.F (chainModel J.right) (Qof P))
      (labSet J (Qof P) N₂ 2 (N₂.chord i).up (N₂.chord i).dn 0 0)
      (stopSet J (Qof P) N₂ kind k b) := by
  have hP := E.hP
  have hN := E.hNF₂
  obtain ⟨d, hd, htd, hpd⟩ := slf_stretch hP hN hA.1 hA.2.1 hA.2.2.1 h0 hL
  obtain ⟨hm, hst⟩ := stop_mem hP hN hD.ok hD.free
  have hL1 := (labTask J (Qof P) _ _ hP hN.1 (F₂plus_chordFamily E) hm hst hnp hC1 d t hd
    hA.2.1 hA.2.2.1 htd (by rwa [← hpd])).1
  obtain ⟨hreg, -⟩ := regOf_spec hN
  obtain ⟨hu, hdn, -⟩ := (regOf_spec hN).2.1 i hi
  obtain ⟨s1, s2⟩ := sideOf_rec hN hi
  rw [slf_labSet2]
  exact hL1 _ (chord_mem hi) hsub _ (hreg.1 _ hu) _ (hreg.1 _ hdn) s1 s2

/-- **The side labels faced at the counterpart of the stretch attachment.** -/
theorem slf_lab_str (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {kind k b : ℕ}
    (hD : OrgD P J N₂ kind k b) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W (stopSet J (Qof P) N₂ kind k b) p t)
    (hnp : ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W (stopSet J (Qof P) N₂ kind k b)
      q s → oW J (q + s) ≠ 0)
    (hC1 : ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W (stopSet J (Qof P) N₂ kind k b)
      q s ∧ (Lst J : ℝ) ≤ oW J (q + s))
    (hnopar : ∀ cc ∈ N₂.F (chainModel J.right) (Qof P), ¬ stopSet J (Qof P) N₂ kind k b ⊆ cc)
    {d : ℕ} (hd : d < Lst J) (htd : t = 0 → d ≠ 0) (hpd : p = (gW J + d) % (chainModel J.whole).W.n)
    {la lb : ℕ} (hla : la < N₂.nRegions) (hlb : lb < N₂.nRegions)
    (hAf : AfterFaces (chainModel J.right) (cpA J d) t (regOf (chainModel J.right) (Qof P) N₂ la))
    (hB1 : 0 < t → BeforeFaces (chainModel J.right) (cpA J d) t
      (regOf (chainModel J.right) (Qof P) N₂ lb))
    (hB0 : t = 0 → BeforeFaces (chainModel J.right) (cpB J d) 0
      (regOf (chainModel J.right) (Qof P) N₂ lb)) :
    EvSideLab J (N₂.F (chainModel J.right) (Qof P)) (labSet J (Qof P) N₂ 2 la lb 0 0)
      (stopSet J (Qof P) N₂ kind k b) := by
  have hP := E.hP
  have hN := E.hNF₂
  obtain ⟨hm, hst⟩ := stop_mem hP hN hD.ok hD.free
  have hL2 := (labTask J (Qof P) _ _ hP hN.1 (F₂plus_chordFamily E) hm hst hnp hC1 d t hd
    hA.2.1 hA.2.2.1 htd (by rwa [← hpd])).2
  obtain ⟨hreg, -⟩ := regOf_spec hN
  rw [slf_labSet2]
  exact hL2 hnopar _ (hreg.1 _ hla) _ (hreg.1 _ hlb) hAf hB1 hB0

end

end SweepEv

end Chazelle.Core
