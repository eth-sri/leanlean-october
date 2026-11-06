module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoS0CandQ2
public import Chazelle.Core.SweepIoPipe

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

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
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
  
  set t := c.nreg lsI with htdef
  set d := c.nreg qD with hddef
  set B := c₀.nreg sB with hBdef
  set s := qS d with hsdef
  set S := slotA B t s with hSdef
  set σ := dirOf d with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by simp_all [dirOf] <;> omega_nf
  obtain ⟨b1, -, -, -, hsl, -, -⟩ := hX
  rw [rd_sw] at b1
  have hBc : c.nreg sB = B := hI.hin _ (by omega_nf)
  have hm : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a := hI.hm
  have hAW : c.nreg ALLOC ≤ W := hI.hw.1 ALLOC
  have hA0 := hI.hA
  have hE' : t < c₀.nreg (sw 301) := ht
  have hS6 : S + 3 ≤ B + 6 * c₀.nreg (sw 301) := by
    rw [hSdef]; unfold slotA; have := qS_le d; nlinarith
  have hslot : SlotOK P J c₀.nmem B (rd c₀ bSweep 300) t s := hsl t ht s (qS_le d)
  -- the slot address
  have hok1 : okB W c.nmem cSlot c.nreg := cSlot_ok _ _ (by omega)
  refine IRS.mono (K := cSlot.length + (5 + (5 + (offerFK + 2)))) (IRS.seq
    (IRS.block cSlot hI hok1) ?_) (by simp [cSlot, hitK]) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' rfl
  obtain ⟨v1S, k1⟩ := cSlot_val c.nmem c.nreg
  rw [hBc] at v1S
  set c₁ : Config := { c with nreg := regB c.nmem cSlot c.nreg } with hc₁
  have hK₁ : Consts c₁ := hK.fix hI₁
  have hAc₁ : c₁.nreg ALLOC = c.nreg ALLOC := k1 ALLOC (by omega_nf)
  have hd₁ : c₁.nreg qD = d := k1 qD (by omega_nf)
  refine IRS.seq (K₁ := 5) (cDir_irs hI₁ hK₁ (by
    ram_grind)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨v2S, k2, hm2⟩
  rw [hd₁] at v2S
  have v2S' : c₂.nreg kS = S := by
    grind [slotA]
  have hK₂ : Consts c₂ := hK.fix hI₂
  have hok3 : okB W c₂.nmem cRead c₂.nreg := cRead_ok _ _ hK₂.2.1 (by omega)
  refine IRS.seq (K₁ := cRead.length) (IRS.block cRead hI₂ hok3) ?_
  rintro c₃ hI₃ hA₃ hA₃' rfl
  obtain ⟨v3F, v3E, v3H, k3⟩ := cRead_val c₂.nmem c₂.nreg hK₂.2.1
  set c₃ : Config := { c₂ with nreg := regB c₂.nmem cRead c₂.nreg } with hc₃
  rw [v2S'] at v3F v3E v3H
  
  have hF : c₃.nreg kF = c₀.nmem S := by
    ram_grind
  have hPe : c₃.nreg kPe = c₀.nmem (S + 1) := by
    ram_grind
  have hPh : c₃.nreg kPh = c₀.nmem (S + 2) := by
    ram_grind
  -- registers through the three steps
  have keep : ∀ q, q ≠ kS → q ≠ kF → q ≠ kPe → q ≠ kPh → c₃.nreg q = c.nreg q := by
    grind
  have nk : ∀ q, (q < sw 4100 ∨ sw 4111 < q) → c₃.nreg q = c.nreg q := fun q hq =>
    keep q (by grind [kS, sw]) (by grind [kF, sw])
      (by grind [kPe, sw]) (by grind [kPh, sw])
  have hAc₃ : c₃.nreg ALLOC = c.nreg ALLOC := nk ALLOC (by omega_nf)
  have hd₃ : c₃.nreg qD = d := nk qD (by omega_nf)
  have hk1₃ : c₃.nreg K1 = 1 := hK.fix hI₃ |>.2.1
  have hk0₃ : c₃.nreg K0 = 0 := hK.fix hI₃ |>.1
  have hacc₃ : AccOK P accA (ModB J 1 1) J.whole.radius z σ L c₃ :=
    hacc.transport (fun j hj => nk (accA + j) (by omega_nf))
  have hfr₃ : FrQ c c₃ := ⟨fun r _ hr _ => keep r (fun h => hr (by grind [Chazelle.Core.SweepIo.S0C.QSet, kS, sw]))
      (fun h => hr (by grind [Chazelle.Core.SweepIo.S0C.QSet, kF, sw]))
      (fun h => hr (by grind [Chazelle.Core.SweepIo.S0C.QSet, kPe, sw]))
      (fun h => hr (by grind [Chazelle.Core.SweepIo.S0C.QSet, kPh, sw])), hAc₃.ge,
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
    have hds : -dS s = σ := by grind [dS_qS, neg_neg]
    rw [hds] at hpos
    have hMod : ModB J 1 1 (c₃.nreg K1) = J.right := by rw [hk1₃]; simp [ModB]
    have hctx₃ : ChainCtx P W c₃ (sw 21) (ModB J 1 1 (c₃.nreg K1)) := by
      rw [hMod]; exact hA.ctxR hI₃
    have hn₃ : c₃.nreg (sw 34) = 2 * (ModB J 1 1 (c₃.nreg K1)).m + 7 := by
      rw [hMod, hI₃.hin _ (by omega_nf)]
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h34, -⟩ := hA.hst
      exact h34
    have hy : |z.2| < J.whole.radius := (J.left.set_subset_box hz).2
    refine (IRS.ifT (by omega) (offerF_irs (L := L) (τ := τs) hI₃ hK hA.hG
      (by have := hA.hWh; grind [hostWords])
      ⟨by omega_nf, by omega_nf⟩
      ⟨by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf⟩
      ⟨by omega_nf, by omega_nf,
        by omega_nf, by omega_nf,
        by omega_nf, by omega_nf,
        by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf⟩
      ⟨by omega_nf, by omega_nf,
        by omega_nf, by omega_nf,
        by omega_nf, by omega_nf⟩
      (by ram_grind) (by omega) hctx₃ (by rw [hMod]; rfl) hn₃
      (by ram_grind) (by ram_grind)
      (by ram_grind) hy
      (by grind [hitK]))).mono (by omega) ?_
    rintro c' ⟨⟨L', hacc', hL', hins⟩, hk', hal', hm'⟩
    rw [hd₃] at hacc'
    have hL'eq : L' = insert τs L := hins (by ram_grind)
    refine ⟨L', hacc', by grind, fun τ hτ' => ?_,
      fun _ τ hτ0 hτe => ?_, ?_⟩
    · rcases hL' with rfl | ⟨-, hon⟩
      · ram_grind
      · rw [hL'eq] at hτ'
        rcases hτ' with rfl | h
        · rw [hMod, hd₃] at hon; exact Or.inr ⟨hτ, onCB_whole_of_right hon⟩
        ram_grind
    · rw [hL'eq]
      have : τ = τs := rayPt_param hσ (by rw [← hτe, ← hpos])
      rw [this]; exact Set.mem_insert _ _
    · refine hfr₃.trans ⟨fun r hr hq hra => hk' r hr (by
          unfold QSet at hq; unfold accA sw at *; omega)
        (fun h => hq (by subst h; omega_nf))
        (fun h => hq (by subst h; omega_nf))
        (fun h => hq (by subst h; omega_nf)) hra, hal', hm'⟩
  · -- an empty slot
    have hf0 : c₀.nmem S = 0 := by omega
    refine (IRS.ifF hf (IRS.skip (K := 0) hI₃ ⟨L, hacc₃, le_rfl, fun τ h => Or.inl h,
      fun h => absurd (hf0 ▸ h) (by norm_num), hfr₃⟩)).mono (by omega)
      (fun _ h => h)

end

end S0C

end SweepIo

end Chazelle.Core
