module

public import Chazelle.Core.SweepEvLoop
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

/-!
# The sweep (WP-D), stage 3: one iteration of the event loop (RAM, the run)

`iter_irs`: from `LoopInv`, one iteration runs within `iterK` steps and its stages are related by
`IterRel`, given the contracts of the window, the origin enumeration and the next key (in their
forms for the fixed environment).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)

@[expose] public section

theorem keepR_of {r : ℕ} (h : (240000 ≤ r ∧ r < 240700) ∨ (242400 ≤ r ∧ r < 242410) ∨
    (242426 ≤ r ∧ r < 242460) ∨ (242480 ≤ r ∧ r < 243000)) : KeepR r := by
  ufo KeepR WR OrgR CandR BestR LblR LR bF bE bH bN bL oK oS sw

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-- **One iteration of the event loop.** -/
theorem iter_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {win key g : Stmt} {orgs : Stmt → Stmt}
    {KW KK κO KG : ℕ} (hgen : GenOK P W c₀ J g KG)
    (hreg : ∀ r, r < N₁.nRegions → (N₁.region r).arcs.length ≤ c₀.nreg (sw 6) + 1)
    (hcount : (keyS P J N₁ N₂).ncard ≤ 4 * N₂.nChords + 2 * N₁.nChords + 9)
    (hwin : ∀ c, IInv W c₀ c → PosW P J (c.nreg kE) (c.nreg kH) →
      (Lst J : ℝ) ≤ offK P J (c.nreg kE) (c.nreg kH) → c.nreg ALLOC + KW ≤ W →
      IRS P W c₀ win c KW (WinOut P J N₁ c))
    (horgs : ∀ (od : Stmt) (Kod : ℕ) (Inv : Set ℕ → Config → Prop),
      (∀ (O : Set ℕ) (c : Config), IInv W c₀ c → Inv O c → c.nreg oK < N₂.nChords →
        c.nreg oS ≤ 1 → c.nreg ALLOC + Kod ≤ W →
        IRS P W c₀ od c Kod (fun c' => Inv (insert (2 * c.nreg oK + c.nreg oS) O) c' ∧
          (∀ r, (LR r ∧ r ≠ oK ∧ r ≠ oS) ∨ ER r → c'.nreg r = c.nreg r) ∧
          (∀ x, c.nreg aB ≤ x → x < c.nreg aB + 5 * c.nreg sC → c'.nmem x = c.nmem x))) →
      (∀ (O : Set ℕ) (c c' : Config), Inv O c → (∀ r, ¬ LR r → c'.nreg r = c.nreg r) →
        c'.nmem = c.nmem → c'.rmem = c.rmem → c'.rreg = c.rreg → c'.output = c.output →
        Inv O c') →
      ∀ (O : Set ℕ) (c : Config), IInv W c₀ c → Inv O c →
        (∀ i, i < min (c.nreg kN) 4 → c.nreg (kL + i) < N₂.nRegions) →
        (∀ i, i < min (c.nreg gN) 2 → c.nreg (gR + i) < N₂.nRegions) →
        (∀ i, i < c.nreg sC → parOf c i ≤ N₂.nChords) →
        c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC →
        c.nreg ALLOC + ((12 * c₀.nreg (sw 6) + 8) * (Kod + κO) + κO) ≤ W →
        IRS P W c₀ (orgs od) c ((12 * c₀.nreg (sw 6) + 8) * (Kod + κO) + κO)
          (Inv (O ∪ iterO N₂ c)))
    (hkey : ∀ c, IInv W c₀ c →
      PosW P J (c.nreg kE) (c.nreg kH) →
      (c.nreg bF = 1 → PosW P J (c.nreg bE) (c.nreg bH)) →
      (c.nreg wX = 0 → PosW P J (c.nreg wE) (c.nreg wH)) →
      (∀ i, i < c.nreg sC → PosW P J (stopE c i) (stopH c i)) →
      (∀ i i', i ≤ i' → i' < c.nreg sC →
        offK P J (stopE c i) (stopH c i) ≤ offK P J (stopE c i') (stopH c i')) →
      (∀ i, i + 2 < c.nreg sC →
        offK P J (stopE c i) (stopH c i) < offK P J (stopE c (i + 2)) (stopH c (i + 2))) →
      c.nreg sP ≤ c.nreg sC → c.nreg kN ≤ 4 → c.nreg bN ≤ 4 →
      c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC → c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC →
      c₀.nreg ALLOC ≤ c.nreg lB → c.nreg lB + 7 * (c.nreg lC + 1) ≤ c.nreg ALLOC →
      c.nreg ALLOC + KK ≤ W →
      IRS P W c₀ key c KK (KeyOut P J c))
    {c : Config} (hI : IInv W c₀ c) (hL : LoopInv P J N₁ N₂ c₀ c)
    (hroom : c.nreg ALLOC + iterK KW KK κO (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) KG ≤ W) :
    IRS P W c₀ (iter win key orgs sh g) c (iterK KW KK κO (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) KG)
      (fun c' => ∃ cw cs co, IterRel P J N₁ N₂ c cw cs co c') := by
  obtain ⟨rs, ax, hlen, haxl, hrecs, haux, hSok, hword, hauxok, hsize⟩ := hL.stops
  unfold iter iterK at *
  -- 1. the window
  refine IRS.seq (K₁ := KW) (K₂ := 2 + (((12 * (c₀.nreg (sw 6)) + 8) * (odK (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) KG + κO) + κO) + KK)) (hwin c hI hL.key hL.keyL (by omega)) ?_
  rintro cw hIw hAw hAw' hWO
  have hWO' := hWO
  obtain ⟨rsW, hrsW2, hrsWR, hgK, hgB1, hgB2, harcs, hwX1, hwE, -, hmW, hfrW⟩ := hWO
  have keepW : ∀ r, KeepR r → cw.nreg r = c.nreg r := fun r h =>
    hfrW r (band_sw_not ⟨h.1, h.2.1⟩) h.2.2.1 (by have := h.1; ufo ALLOC)
  -- 2. the reset
  refine IRS.seq (K₁ := resetL.length) (K₂ := ((12 * (c₀.nreg (sw 6)) + 8) * (odK (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) KG + κO) + κO) + KK)
    (IRS.block resetL hIw ⟨⟨iscr_sw (by ufo bF sw) (by ufo bF sw), by omega⟩,
      ⟨iscr_sw (by ufo bN sw) (by ufo bN sw), by omega⟩, trivial⟩) ?_
  rintro cs hIs hAs hAs' rfl
  have hrl : resetL.length = 2 := rfl
  set cs : Config := { cw with nreg := regB cw.nmem resetL cw.nreg } with hcsd
  have hsF : cs.nreg bF = 0 := by
    sis only [hcsd, resetL, regB, regI, upd, bF, bN, sw]
  have hsN : cs.nreg bN = 0 := by
    sis only [hcsd, resetL, regB, regI, upd, bF, bN, sw]
  have hsO : ∀ r, r ≠ bF → r ≠ bN → cs.nreg r = cw.nreg r := fun r h1 h2 =>
    regB_other _ _ _ (by
      intro i hi
      simp [resetL, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact Ne.symm h1
      · exact Ne.symm h2)
  have hRes : ResetRel cw cs := ⟨rfl, hsF, hsN, hsO⟩
  have keepS : ∀ r, KeepR r → cs.nreg r = c.nreg r := fun r h =>
    (hsO r h.2.2.2.1 h.2.2.2.2.1).trans (keepW r h)
  have hmS : ∀ x, x < c.nreg ALLOC → cs.nmem x = c.nmem x := hmW
  -- the window registers, kept by the reset
  have sGK : cs.nreg wGK = cw.nreg wGK := hsO _ (by ufo wGK bF sw) (by ufo wGK bN sw)
  have sGB : cs.nreg wGB = cw.nreg wGB := hsO _ (by ufo wGB bF sw) (by ufo wGB bN sw)
  have sX : cs.nreg wX = cw.nreg wX := hsO _ (by ufo wX bF sw) (by ufo wX bN sw)
  have sE : cs.nreg wE = cw.nreg wE := hsO _ (by ufo wE bF sw) (by ufo wE bN sw)
  have sH : cs.nreg wH = cw.nreg wH := hsO _ (by ufo wH bF sw) (by ufo wH bN sw)
  -- kept registers
  have kTB : cs.nreg cTB = c.nreg cTB := keepS _ (keepR_of (by ufo cTB sw))
  have kaB : cs.nreg aB = c.nreg aB := keepS _ (keepR_of (by ufo aB sw))
  have ksC : cs.nreg sC = c.nreg sC := keepS _ (keepR_of (by ufo sC sw))
  have ksB : cs.nreg sB = c.nreg sB := keepS _ (keepR_of (by ufo sB sw))
  have kkE : cs.nreg kE = c.nreg kE := keepS _ (keepR_of (by ufo kE sw))
  have kkH : cs.nreg kH = c.nreg kH := keepS _ (keepR_of (by ufo kH sw))
  have kkN : cs.nreg kN = c.nreg kN := keepS _ (keepR_of (by ufo kN sw))
  have kgN : cs.nreg gN = c.nreg gN := keepS _ (keepR_of (by ufo gN sw))
  have klB : cs.nreg lB = c.nreg lB := keepS _ (keepR_of (by ufo lB sw))
  have klC : cs.nreg lC = c.nreg lC := keepS _ (keepR_of (by ufo lC sw))
  have ksP : cs.nreg sP = c.nreg sP := keepS _ (keepR_of (by ufo sP sw))
  have kkL : ∀ i, i < 4 → cs.nreg (kL + i) = c.nreg (kL + i) := fun i hi =>
    keepS _ (keepR_of (by ufo kL sw))
  have kgR : ∀ i, i < 2 → cs.nreg (gR + i) = c.nreg (gR + i) := fun i hi =>
    keepS _ (keepR_of (by ufo gR sw))
  have hAcs : c.nreg ALLOC ≤ cs.nreg ALLOC := hAw
  -- the layout at `cs`
  have hT : cs.nreg cTB + 6 * N₂.nChords ≤ cs.nreg ALLOC := by
    have := hL.lay1; have := hL.lay2; have := hL.lay4; rwo [kTB]
  have hWT : cs.nreg cTB + 6 * N₂.nChords ≤ cs.nreg wGB := by
    have := hL.lay1; have := hL.lay2; have := hL.lay4; rwo [kTB, sGB]
  have hauxT : cs.nreg cTB + 6 * N₂.nChords ≤ cs.nreg aB := by
    have := hL.lay1; have := hL.lay3; rwo [kTB, kaB]
  have hauxL : cs.nreg aB + 5 * cs.nreg sC ≤ cs.nreg ALLOC := by
    have := hL.lay5; rwo [kaB, ksC]
  -- the gathered arcs
  have hLlen : (regArcs N₁ rsW).length ≤ 2 * ((c₀.nreg (sw 6)) + 1) := by
    have := regArcs_length_le (N := N₁) (rs := rsW) (B := (c₀.nreg (sw 6)) + 1)
      (fun r hr => hreg r (hrsWR r hr))
    have h2 : rsW.length * ((c₀.nreg (sw 6)) + 1) ≤ 2 * ((c₀.nreg (sw 6)) + 1) := Nat.mul_le_mul_right _ hrsW2
    omega
  have hLarc : ∀ a ∈ regArcs N₁ rsW, a < N₁.arcs.length := regArcs_lt E.hNF₁ hrsWR
  -- 3. the origins
  have hod : ∀ (O : Set ℕ) (c' : Config), IInv W c₀ c' →
      BatchInv P J N₂ cs (ShotList.loSet (chainModel J.left) (Qof P) cs.nmem (cs.nreg wGB)
        (cs.nreg wGK) []) O c' → c'.nreg oK < N₂.nChords → c'.nreg oS ≤ 1 →
      c'.nreg ALLOC + odK (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) KG ≤ W →
      IRS P W c₀ (orgDo sh g) c' (odK (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) KG) (fun c'' =>
        BatchInv P J N₂ cs (ShotList.loSet (chainModel J.left) (Qof P) cs.nmem (cs.nreg wGB)
          (cs.nreg wGK) []) (insert (2 * c'.nreg oK + c'.nreg oS) O) c'' ∧
        (∀ r, (LR r ∧ r ≠ oK ∧ r ≠ oS) ∨ ER r → c''.nreg r = c'.nreg r) ∧
        (∀ x, c'.nreg aB ≤ x → x < c'.nreg aB + 5 * c'.nreg sC → c''.nmem x = c'.nmem x)) := by
    intro O c' hI' hInv hk hs hroom'
    rw [sGK, hgK] at hInv ⊢
    have hmono := orgDoK_mono (Fg := F (c₀.nreg (sw 5))) (KG := KG) hLlen
    exact (orgDo_batch E hgen (cs := cs) (L := regArcs N₁ rsW) hLarc (by rw [sGK, hgK])
      (by rwo [sGB]) (fun k hk' => by rw [sGB]; exact harcs k hk') hT hWT hauxT hauxL
      (by rw [kkE, kkH]; exact hL.key) O c' hI' hInv hk hs
      (by ufo odK at hroom')).mono (by unfold odK; exact hmono) (fun _ => id)
  have hstab : ∀ (O : Set ℕ) (c1 c2 : Config),
      BatchInv P J N₂ cs (ShotList.loSet (chainModel J.left) (Qof P) cs.nmem (cs.nreg wGB)
        (cs.nreg wGK) []) O c1 → (∀ r, ¬ LR r → c2.nreg r = c1.nreg r) →
      c2.nmem = c1.nmem → c2.rmem = c1.rmem → c2.rreg = c1.rreg → c2.output = c1.output →
      BatchInv P J N₂ cs (ShotList.loSet (chainModel J.left) (Qof P) cs.nmem (cs.nreg wGB)
        (cs.nreg wGK) []) O c2 :=
    fun O c1 c2 h hr hm _ _ _ => batch_stable h hr hm
  have hpar : ∀ i, i < cs.nreg sC → parOf cs i ≤ N₂.nChords := fun i hi => by
    rw [ksC, ← hlen] at hi
    have hA := haux i (by rwx [haxl])
    have hok := (hauxok i hi).2.2.2.2.2.2.1
    unfold parOf
    rw [kaB, hmS _ (by have := hL.lay5; omega)]
    rwx [hA.2.2.2.2]
  refine IRS.seq (K₁ := ((12 * (c₀.nreg (sw 6)) + 8) * (odK (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) KG + κO) + κO)) (K₂ := KK)
    (horgs (orgDo sh g) (odK (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) KG) _ hod hstab ∅ cs hIs (batch_base hsF (by omega))
      (fun i hi => by
        rw [kkL i (by omega)]
        exact hL.labR i (by rwo [kkN] at hi))
      (fun i hi => by
        rw [kgR i (by omega)]
        exact hL.gapR i (by rwo [kgN] at hi))
      hpar hauxL (by omega)) ?_
  rintro co hIo hAo hAo' hBo
  rw [Set.empty_union] at hBo
  have hBo' := hBo
  obtain ⟨hregO, hAO, A, hBA⟩ := hBo
  have keepO : ∀ r, KeepR r → co.nreg r = cs.nreg r := fun r h =>
    hregO r (band_sw_not ⟨h.1, h.2.1⟩) h.2.2.2.2.2.1 h.2.2.2.2.2.2
      (by have := h.1; ufo ALLOC)
  have keepOC : ∀ r, KeepR r → co.nreg r = c.nreg r := fun r h => (keepO r h).trans (keepS r h)
  have hmO : ∀ x, cs.nreg cTB + 6 * N₂.nChords ≤ x → x < c.nreg ALLOC → co.nmem x = c.nmem x :=
    fun x h1 h2 => (hBA.memT x (by omega) (Or.inr h1)).trans (hmS x h2)
  -- registers at `co`
  have oaB : co.nreg aB = c.nreg aB := keepOC _ (keepR_of (by ufo aB sw))
  have osC : co.nreg sC = c.nreg sC := keepOC _ (keepR_of (by ufo sC sw))
  have osB : co.nreg sB = c.nreg sB := keepOC _ (keepR_of (by ufo sB sw))
  have okE : co.nreg kE = c.nreg kE := keepOC _ (keepR_of (by ufo kE sw))
  have okH : co.nreg kH = c.nreg kH := keepOC _ (keepR_of (by ufo kH sw))
  have okN : co.nreg kN = c.nreg kN := keepOC _ (keepR_of (by ufo kN sw))
  have olB : co.nreg lB = c.nreg lB := keepOC _ (keepR_of (by ufo lB sw))
  have olC : co.nreg lC = c.nreg lC := keepOC _ (keepR_of (by ufo lC sw))
  have osP : co.nreg sP = c.nreg sP := keepOC _ (keepR_of (by ufo sP sw))
  have nW : ∀ r, (r = wX ∨ r = wE ∨ r = wH) → co.nreg r = cw.nreg r := fun r hr => by
    rw [hregO r (band_sw_not (by ufo wX wE wH sw at hr))
      (by unfold OrgR CandR BestR LblR bF bE bH bN bL; unfold wX wE wH sw at hr; ufo sw)
      (by unfold LR oK oS; unfold wX wE wH sw at hr; ufo sw)
      (by unfold wX wE wH sw at hr; ufo ALLOC)]
    exact hsO r (by unfold wX wE wH sw at hr; ufo bF sw)
      (by unfold wX wE wH sw at hr; ufo bN sw)
  have oX : co.nreg wX = cw.nreg wX := nW _ (Or.inl rfl)
  have oE : co.nreg wE = cw.nreg wE := nW _ (Or.inr (Or.inl rfl))
  have oH : co.nreg wH = cw.nreg wH := nW _ (Or.inr (Or.inr rfl))
  -- the stops at `co`
  have hstopM : ∀ i, i < c.nreg sC → stopE co i = stopE c i ∧ stopH co i = stopH c i := by
    intro i hi
    have := hL.lay4; have := hL.lay1; have := hL.lay2
    unfold stopE stopH
    rw [osB, hmO _ (by rwo [kTB]) (by omega), hmO _ (by rwo [kTB]) (by omega)]
    exact ⟨rfl, rfl⟩
  have hoff : ∀ i, i < c.nreg sC → offK P J (stopE co i) (stopH co i) = stopOff P J c i :=
    fun i hi => by rwr [(hstopM i hi).1, (hstopM i hi).2]
  -- the room of the log
  have hroomL : co.nreg lB + 7 * (co.nreg lC + 1) ≤ co.nreg ALLOC := by
    have hm := hL.meas
    have h2 := hL.lay2; have h4 := hL.lay4
    rw [olB, olC]
    have : c.nreg lC + 1 ≤ logCap N₁ N₂ := by ufo logCap
    omega
  refine (hkey co hIo (by rw [okE, okH]; exact hL.key) (fun h => by
      obtain ⟨⟨j, hj⟩, -⟩ := hBA.bAcc h
      exact (hBA.acc _ hj).2.2.2.2.2.2.2.1)
    (fun h => by rw [oE, oH]; rw [oX] at h; exact (hwE h).1)
    (fun i hi => by
      rw [osC] at hi
      rw [(hstopM i hi).1, (hstopM i hi).2]
      have hi' : i < rs.length := by rwx [hlen]
      obtain ⟨r1, r2, -⟩ := hrecs i hi'
      unfold stopE stopH; rw [r1, r2]
      exact (hword _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; exact List.getElem_mem hi')).1)
    (fun i i' h1 h2 => by
      rw [osC] at h2; rw [hoff i (by omega), hoff i' h2]; exact hL.sorted i i' h1 h2)
    (fun i h => by
      rw [osC] at h; rw [hoff i (by omega), hoff (i + 2) h]; exact hL.two i h)
    (by rw [osP, osC]; exact hL.ptr) (by rw [okN]; exact hL.labN) hBA.fN
    (by rw [osB, osC]; have := hL.lay4; omega) (by rw [oaB, osC]; have := hL.lay5; omega)
    (by rw [olB]; have := hL.lay1; have := hL.tab0; omega) hroomL (by omega)).mono le_rfl ?_
  intro c' hK
  exact ⟨cw, cs, co, hWO', hAw, hRes, hBo', hK⟩

end

end SweepEv

end Chazelle.Core
