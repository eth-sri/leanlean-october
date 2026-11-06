module

public import Chazelle.Core.SweepEvRunCost
set_option maxHeartbeats 8000000

/-!
# The sweep (WP-D), stages 2–3: the run steps (`RunTask`)

`runTask_of`: the run steps `prep ; mk2 sh ; start ; while (dF < K1) iter` meet `RunTask`, given
the contracts of the pieces (genuineness, stage 2, window, origin enumeration, next key,
preparation, start, step, done, arcs per region, number of keys).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-- **The run steps.** -/
def runProg (prep start win key : Stmt) (mk2 orgs mkG : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .seq prep (.seq (mk2 sh) (.seq start (.whileLtN dF K1 (iter win key orgs sh (mkG sh)))))

/-- **The run steps meet `RunTask`.** -/
theorem runTask_of (hGen : GenTask) (hStop : StopTask) (hWin : WinTask) (hOrgs : OrgsTask)
    (hKey : KeyTask) (hPrep : PrepTask) (hL0 : LoopStartTask) (hL1 : StepTask) (hL2 : DoneTask)
    (hRA : RegArcsTask) (hC : CountTask) : RunTask := by
  obtain ⟨mkG, κG, hG⟩ := hGen
  obtain ⟨mk2, κS, hS⟩ := hStop
  obtain ⟨win, κW, hW⟩ := hWin
  obtain ⟨orgs, κO, hO⟩ := hOrgs
  obtain ⟨key, κK, hK⟩ := hKey
  obtain ⟨prep, κP, hPr⟩ := hPrep
  obtain ⟨start, κS0, hSt⟩ := hL0
  refine ⟨runProg prep start win key mk2 orgs mkG,
    fun D => runA D (κW D) (κG D) κO κK κP (κS D) (κS0 D), ?_⟩
  intro sh Bs F X Ok P W c₀ J N₁ N₂ E hwb hroom
  have hI0 : IInv W c₀ c₀ := ⟨hwb, fun _ _ => rfl, le_rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  beta_reduce at hroom ⊢
  obtain ⟨hfin0, hcnt0⟩ := hC P J N₁ N₂ E.hP E.hNF₁ E.hNF₂
  have hfin : (keyS P J N₁ N₂).Finite := hfin0
  have hcnt : (keyS P J N₁ N₂).ncard ≤ 4 * N₂.nChords + 2 * N₁.nChords + 9 := hcnt0
  have hPl : J.left.P.Simple := E.ctx1.2.2.2.2.1
  have hreg := hRA J.left (Qof P) N₁ (c₀.nreg (sw 6)) hPl E.hNF₁ E.hdeg₁
  have hT := E.hTLR
  have hsum := run_cost (D := c₀.nreg (sw 6)) (Fg := F (c₀.nreg (sw 5)))
    (L := Nat.clog 2 (N₁.nChords + N₂.nChords + 1)) (T := c₀.nreg TLR)
    (K' := N₁.nChords + N₂.nChords + 1) (n := (keyS P J N₁ N₂).ncard) (κWD := κW (c₀.nreg (sw 6)))
    (κGD := κG (c₀.nreg (sw 6))) (κO := κO) (κK := κK) (κP := κP) (κSD := κS (c₀.nreg (sw 6)))
    (κS0D := κS0 (c₀.nreg (sw 6)))
    (KG := κG (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1)) rfl hT (by omega)
    (by omega) rfl
  unfold runProg
  refine IRS.mono (IRS.seq (hPr sh Bs F X Ok P W c₀ c₀ J N₁ N₂ E hI0 E.hTA.symm (by
      have := Nat.mul_le_mul_left κP (Nat.le_refl (N₁.nChords + N₂.nChords + 1)); omega)) ?_)
    hsum (fun _ => id)
  rintro c₁ hI₁ hA₁ hA₁' hPO
  refine IRS.seq (hS sh Bs F X Ok P W c₀ c₁ J N₁ N₂ E hI₁ (by omega)) ?_
  rintro c₂ hI₂ hA₂ hA₂' hSO
  refine IRS.seq (hSt sh Bs F X Ok P W c₀ c₁ c₂ J N₁ N₂ E hPO hSO hI₂ (by omega)) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨hL3, -, -⟩
  refine (loop_irs (Kb := iterK (κW (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1)) κK κO
      (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))
      (κG (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1)))
    (fun c hIc hLc hr => iter_irs E (hG sh Bs F X Ok P W c₀ J N₁ N₂ E) hreg
      hcnt
      (fun c hIc hpos hL hr => hW sh Bs F X Ok P W c₀ c J N₁ N₂ E hIc hpos hL hr)
      (hO sh Bs F X Ok P W c₀ J N₁ N₂ E)
      (fun c hIc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 =>
        hK sh Bs F X Ok P W c₀ c J N₁ N₂ E hIc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14)
      hIc hLc hr)
    (fun c cw cs co c' h1 h2 h3 => hL1 sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' E h1 h2 h3)
    (fun c cw cs co c' h1 h2 h3 => hL2 sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' E h1 h2 h3)
    hfin hI₃ (E.hK.fix hI₃).2.1 hL3 (by omega)).mono le_rfl ?_
  exact fun c' h => h.2

end

end SweepEv

end Chazelle.Core
