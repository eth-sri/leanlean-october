module

public import Chazelle.Core.SweepIoS0CandQ2
public import Chazelle.Core.SweepIoPipe
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-!
# The sweep RAM (WP-D), answers: the side-0 stop and table candidates of a query, part 3

`hit_irs`: the slot part `cHit` at the log record found (whose point is the query point `z`):
read the slot of the query direction; if it is flagged, its origin is `rayPt z σ τ` with
`τ > 0` (`cand_ray`) and is offered (`offerF`, tag `1`).
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
  {H : Host} {N₁ N₂ : NF} {E : ℕ} {c₀ c : Config}

/-- The cost of the slot part. -/
def hitK : ℕ := 7 + (5 + (5 + (offerFK + 2)))

theorem onCB_whole_of_right {x : Point} (h : OnCB J.right x) : OnCB J.whole x := by
  rcases h with h | h | h
  · exact Or.inl (J.right_set_subset h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **The slot part.** -/
theorem hit_irs (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hX : AuxCore P J N₂ c₀) (hI : IInv W c₀ c)
    {z : Point} {L : Set ℝ} (ht : c.nreg lsI < rd c₀ bSweep 301)
    (hpt : logPt P J c₀.nmem (rd c₀ bSweep 300) (c.nreg lsI) = z)
    (hz : z ∈ J.left.set) (hzs : z ≠ J.shared) (hz2 : z.2 ≤ J.right.top.2)
    (hacc : AccOK P accA (ModB J 1 1) J.whole.radius z (dirOf (c.nreg qD)) L c)
    (hroom : c.nreg ALLOC + hitK ≤ W) :
    IRS P W c₀ cHit c hitK (fun c' => ∃ L', AccOK P accA (ModB J 1 1) J.whole.radius z
        (dirOf (c.nreg qD)) L' c' ∧ L ⊆ L' ∧
      (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.whole (rayPt z (dirOf (c.nreg qD)) τ))) ∧
      (c₀.nmem (slotA (c₀.nreg sB) (c.nreg lsI) (qS (c.nreg qD))) = 1 → ∀ τ, 0 < τ →
        (chainModel J.right).pos (Qof P)
          ⟨c₀.nmem (slotA (c₀.nreg sB) (c.nreg lsI) (qS (c.nreg qD)) + 1),
            c₀.nmem (slotA (c₀.nreg sB) (c.nreg lsI) (qS (c.nreg qD)) + 2)⟩ =
          rayPt z (dirOf (c.nreg qD)) τ → τ ∈ L') ∧
      FrQ c c') := by
  have hK := hA.hK
  have hKc := hK.fix hI
  set t := c.nreg lsI with htdef
  set d := c.nreg qD with hddef
  set B := c₀.nreg sB with hBdef
  set s := qS d with hsdef
  set S := slotA B t s with hSdef
  set σ := dirOf d with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by rw [hσdef]; unfold dirOf; split_ifs <;> simp
  obtain ⟨b1, -, -, -, hsl, -, -⟩ := hX
  rw [rd_sw] at b1
  have hBc : c.nreg sB = B := hI.hin _ (by ufo IFix sB sw)
  have hm : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a := hI.hm
  have hAW : c.nreg ALLOC ≤ W := hI.hw.1 ALLOC
  have hA0 := hI.hA
  have hE' : t < c₀.nreg (sw 301) := ht
  have hS6 : S + 3 ≤ B + 6 * c₀.nreg (sw 301) := by
    rw [hSdef]; unfold slotA; have := qS_le d; nlinarith
  have hslot : SlotOK P J c₀.nmem B (rd c₀ bSweep 300) t s := hsl t ht s (qS_le d)
  -- the slot address
  have hok1 : okB W c.nmem cSlot c.nreg := cSlot_ok _ _ (by rwnl [hBc])
  refine IRS.mono (K := cSlot.length + (5 + (5 + (offerFK + 2)))) (IRS.seq
    (IRS.block cSlot hI hok1) ?_) (by simp [cSlot, hitK]) (fun _ => id)
  rintro c₁ hI₁ hA₁ hA₁' rfl
  obtain ⟨v1S, k1⟩ := cSlot_val c.nmem c.nreg
  rw [hBc] at v1S
  set c₁ : Config := { c with nreg := regB c.nmem cSlot c.nreg } with hc₁
  have hK₁ : Consts c₁ := hK.fix hI₁
  have hAc₁ : c₁.nreg ALLOC = c.nreg ALLOC := k1 ALLOC (by ufo ALLOC kS sw)
  have hd₁ : c₁.nreg qD = d := k1 qD (by ufo qD kS sw)
  refine IRS.seq (K₁ := 5) (cDir_irs hI₁ hK₁ (by
    show regB c.nmem cSlot c.nreg kS + 3 ≤ W
    rwo [v1S])) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨v2S, k2, hm2⟩
  rw [hd₁] at v2S
  have v2S' : c₂.nreg kS = S := by
    rw [v2S]; show regB c.nmem cSlot c.nreg kS + 3 * qS d = S
    rw [v1S, hSdef]; ufring slotA
  have hK₂ : Consts c₂ := hK.fix hI₂
  have hok3 : okB W c₂.nmem cRead c₂.nreg := cRead_ok _ _ hK₂.2.1 (by rwo [v2S'])
  refine IRS.seq (K₁ := cRead.length) (IRS.block cRead hI₂ hok3) ?_
  rintro c₃ hI₃ hA₃ hA₃' rfl
  obtain ⟨v3F, v3E, v3H, k3⟩ := cRead_val c₂.nmem c₂.nreg hK₂.2.1
  set c₃ : Config := { c₂ with nreg := regB c₂.nmem cRead c₂.nreg } with hc₃
  rw [v2S'] at v3F v3E v3H
  have hm₂ : ∀ a, a < c₀.nreg ALLOC → c₂.nmem a = c₀.nmem a := hI₂.hm
  have hF : c₃.nreg kF = c₀.nmem S := by
    show regB c₂.nmem cRead c₂.nreg kF = _; rw [v3F, hm₂ S (by omega)]
  have hPe : c₃.nreg kPe = c₀.nmem (S + 1) := by
    show regB c₂.nmem cRead c₂.nreg kPe = _; rw [v3E, hm₂ (S + 1) (by omega)]
  have hPh : c₃.nreg kPh = c₀.nmem (S + 2) := by
    show regB c₂.nmem cRead c₂.nreg kPh = _; rw [v3H, hm₂ (S + 2) (by omega)]
  -- registers through the three steps
  have keep : ∀ q, q ≠ kS → q ≠ kF → q ≠ kPe → q ≠ kPh → c₃.nreg q = c.nreg q := by
    intro q h1 h2 h3 h4
    show regB c₂.nmem cRead c₂.nreg q = c.nreg q
    rw [k3 q h1 h2 h3 h4, k2 q h1]
    exact k1 q h1
  have nk : ∀ q, (q < sw 4100 ∨ sw 4111 < q) → c₃.nreg q = c.nreg q := fun q hq =>
    keep q (by ufo kS sw at *) (by ufo kF sw at *)
      (by ufo kPe sw at *) (by ufo kPh sw at *)
  have hAc₃ : c₃.nreg ALLOC = c.nreg ALLOC := nk ALLOC (by ufo ALLOC sw)
  have hd₃ : c₃.nreg qD = d := nk qD (by ufo qD sw)
  have hk1₃ : c₃.nreg K1 = 1 := hK.fix hI₃ |>.2.1
  have hk0₃ : c₃.nreg K0 = 0 := hK.fix hI₃ |>.1
  have hacc₃ : AccOK P accA (ModB J 1 1) J.whole.radius z σ L c₃ :=
    hacc.transport (fun j hj => nk (accA + j) (by ufo accA sw))
  have hfr₃ : FrQ c c₃ := ⟨fun r _ hr _ => keep r (fun h => hr (by subst h; right; ufo kS sw))
      (fun h => hr (by subst h; right; ufo kF sw))
      (fun h => hr (by subst h; right; ufo kPe sw))
      (fun h => hr (by subst h; right; ufo kPh sw)), hAc₃.ge,
    fun a ha => by rw [hm2]⟩
  have hfl : c₀.nmem S ≤ 1 := hslot.1
  unfold cOffer
  by_cases hf : c₃.nreg K0 < c₃.nreg kF
  · -- a flagged slot: offer its origin
    rw [hk0₃, hF] at hf
    have hf1 : c₀.nmem S = 1 := by omega
    obtain ⟨he, hpp, hc⟩ := hslot.2 hf1
    rw [hpt] at hc
    obtain ⟨hτ, hpos⟩ := cand_ray (dS_eq s) hc (z_mem_right_dom hA.hP hz hzs hz2)
      (z_not_mem_whole_dom hz)
    set τs := J.whole.hitParam ((chainModel J.right).pos (Qof P) ⟨c₀.nmem (S + 1), c₀.nmem (S + 2)⟩)
      (dS s) with hτs
    have hds : -dS s = σ := by rw [hsdef, dS_qS, neg_neg]
    rw [hds] at hpos
    have hMod : ModB J 1 1 (c₃.nreg K1) = J.right := by rw [hk1₃]; simp [ModB]
    have hctx₃ : ChainCtx P W c₃ (sw 21) (ModB J 1 1 (c₃.nreg K1)) := by
      rw [hMod]; exact hA.ctxR hI₃
    have hn₃ : c₃.nreg (sw 34) = 2 * (ModB J 1 1 (c₃.nreg K1)).m + 7 := by
      rw [hMod, hI₃.hin _ (by ufo IFix sw)]
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h34, -⟩ := hA.hst
      exact h34
    have hy : |z.2| < J.whole.radius := (J.left.set_subset_box hz).2
    refine (IRS.ifT (by rwo [hk0₃, hF]) (offerF_irs (L := L) (τ := τs) hI₃ hK hA.hG
      (by have := hA.hWh; ufo hostWords at this)
      ⟨by ufn accA sw, by ufn accA sw⟩
      ⟨by ufn sw, by ufn sw, by ufn kPe sw,
        by ufn kPe sw, by ufn kPh sw, by ufn kPh sw,
        by ufn K1 sw, by ufn K1 sw, by ufn qD sw,
        by ufn qD sw, by ufn sw, by ufn sw,
        by ufn kPo sw, by ufn kPo sw⟩
      ⟨by ufn kPe kPh sw, by ufn kPo kPe sw,
        by ufn kPo kPh sw, by ufn kPo kPe sw,
        by ufn kPo kPh sw, by ufn kPo K1 sw,
        by ufn kPo qD sw, by ufn kPo sw, by ufn kPh K1 sw,
        by ufn kPh qD sw, by ufn kPh sw, by ufn kPo sw,
        by ufn kPh sw, by ufn kPo K1 sw, by ufn kPo qD sw,
        by ufn kPo sw, by ufn kPo sw⟩
      ⟨by ufn accA sw, by ufn kPe accA sw,
        by ufn kPh accA sw, by ufn K1 accA sw,
        by ufn qD accA sw, by ufn kPo accA sw⟩
      (by rwx [hd₃]) (by rwn [hk1₃]) hctx₃ (by rwr [hMod]) hn₃
      (by rwx [hMod, hPe]) (by rwx [hMod, hPe, hPh])
      (by rwx [hMod, hPe, hPh, hd₃]) hy
      (by ruo [hAc₃] hitK at hroom))).mono (by omega) ?_
    rintro c' ⟨⟨L', hacc', hL', hins⟩, hk', hal', hm'⟩
    rw [hd₃] at hacc'
    have hL'eq : L' = insert τs L := hins (by rwx [hMod])
    refine ⟨L', hacc', by rw [hL'eq]; exact Set.subset_insert _ _, fun τ hτ' => ?_,
      fun _ τ hτ0 hτe => ?_, ?_⟩
    · rcases hL' with rfl | ⟨-, hon⟩
      · exact Or.inl hτ'
      · rw [hL'eq] at hτ'
        rcases hτ' with rfl | h
        · rw [hMod, hd₃] at hon; exact Or.inr ⟨hτ, onCB_whole_of_right hon⟩
        · exact Or.inl h
    · rw [hL'eq]
      have : τ = τs := rayPt_param hσ (by rw [← hτe, ← hpos])
      rw [this]; exact Set.mem_insert _ _
    · refine hfr₃.trans ⟨fun r hr hq hra => hk' r hr (by
          unfold QSet at hq; ufo accA sw at *)
        (fun h => hq (by subst h; right; ufo kPh sw))
        (fun h => hq (by subst h; right; ufo kPo sw))
        (fun h => hq (by subst h; right; ufo kPo sw)) hra, hal', hm'⟩
  · -- an empty slot
    have hf0 : c₀.nmem S = 0 := by rwo [hk0₃, hF] at hf
    refine (IRS.ifF hf (IRS.skip (K := 0) hI₃ ⟨L, hacc₃, le_rfl, fun τ h => Or.inl h,
      fun h => absurd (hf0 ▸ h) (by norm_num), hfr₃⟩)).mono (by ufo offerFK offerK)
      (fun _ => id)

end

end S0C

end SweepIo

end Chazelle.Core
