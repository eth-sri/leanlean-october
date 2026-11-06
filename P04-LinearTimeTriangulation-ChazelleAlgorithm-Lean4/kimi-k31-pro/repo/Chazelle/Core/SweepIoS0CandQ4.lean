module

public import Chazelle.Core.SweepIoS0CandQ3
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-!
# The sweep RAM (WP-D), answers: the side-0 stop and table candidates of a query, part 4

`check_irs`: after the binary search (result `t < E`), the check of the log record `t` against
the query position (`callOff`) and the slot part.  Its post-condition states the completeness of
the slot read (`HC`): for every log record with the query position and a flagged slot of the
query direction, the parameter of a candidate origin on the ray is offered.
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

/-- **The completeness of the slot read** (the hypothesis of `compl_of`). -/
def HC (P : Polygon) (J : Merge.Junction) (c₀ : Config) (z : Point) (zp zh d : ℕ) (L' : Set ℝ) :
    Prop :=
  ∀ i, i < rd c₀ bSweep 301 → c₀.nmem (rd c₀ bSweep 300 + 7 * i) = zp →
    (chainModel J.whole).param (Qof P) (logPos c₀.nmem (rd c₀ bSweep 300) i) =
      (chainModel J.whole).param (Qof P) ⟨zp, zh⟩ →
    c₀.nmem (slotA (c₀.nreg sB) i (qS d)) = 1 →
    ∀ (o : Point) (τ : ℝ), CandAt J o (dS (qS d)) z → 0 < τ → o = rayPt z (dirOf d) τ → τ ∈ L'

/-- The cost of the check. -/
def checkK : ℕ := 11 + (11008 + (2 + (2 + hitK)))

theorem key_of_match {i zp zh : ℕ} {m : ℕ → ℕ} {AL : ℕ} (h1 : m (AL + 7 * i) = zp)
    (h2 : (chainModel J.whole).param (Qof P) (logPos m AL i) =
      (chainModel J.whole).param (Qof P) ⟨zp, zh⟩) :
    (chainModel J.whole).key (Qof P) (logPos m AL i) =
      (chainModel J.whole).key (Qof P) ⟨zp, zh⟩ := by
  unfold Model.key; rw [h2]; ufs logPos; rw [h1]

theorem gW_lt_nat (J : Merge.Junction) : gW J < (chainModel J.whole).W.n := by
  have := gW_lt J; exact_mod_cast this

/-- **The check of the record found and the slot part.** -/
theorem check_irs (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hX : AuxCore P J N₂ c₀)
    (hI : IInv W c₀ c) {z : Point} {L : Set ℝ} {zp zh : ℕ}
    (hz : z ∈ J.left.set) (hzs : z ≠ J.shared) (hz2 : z.2 ≤ J.right.top.2)
    (hzP : zp < (chainModel J.whole).W.n)
    (hzPp : ProperPos (chainModel J.whole) (Qof P) P.n ⟨zp, zh⟩)
    (harr : Arrival (chainModel J.whole).W z (-dirOf (c.nreg qD)) zp
      ((chainModel J.whole).param (Qof P) ⟨zp, zh⟩))
    (hxE : c.nreg lsxE = zp) (hxH : c.nreg lsxH = zh)
    (ht : c.nreg lsI < rd c₀ bSweep 301)
    (hs1 : ∀ j, j < c.nreg lsI →
      lsPr P J c₀.nmem (rd c₀ bSweep 300) (c₀.nreg (sw 40)) ⟨zp, zh⟩ j)
    (hs2 : ∀ j, c.nreg lsI ≤ j → j < rd c₀ bSweep 301 →
      ¬ lsPr P J c₀.nmem (rd c₀ bSweep 300) (c₀.nreg (sw 40)) ⟨zp, zh⟩ j)
    (hacc : AccOK P accA (ModB J 1 1) J.whole.radius z (dirOf (c.nreg qD)) L c)
    (hroom : c.nreg ALLOC + checkK ≤ W) :
    IRS P W c₀ cCheck c checkK (fun c' => ∃ L', AccOK P accA (ModB J 1 1) J.whole.radius z
        (dirOf (c.nreg qD)) L' c' ∧ L ⊆ L' ∧
      (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.whole (rayPt z (dirOf (c.nreg qD)) τ))) ∧
      HC P J c₀ z zp zh (c.nreg qD) L' ∧ FrQ c c') := by
  have hK := hA.hK
  have hKc := hK.fix hI
  set t := c.nreg lsI with htdef
  set d := c.nreg qD with hddef
  set AL := rd c₀ bSweep 300 with hAL
  set G := c₀.nreg (sw 40) with hGdef
  have hXc := hX
  obtain ⟨-, b2, -, -, hsl, -, -⟩ := hX
  have hAW  := hI.hw.1 ALLOC
  have hA0 := hI.hA
  have hm  := hI.hm
  have hALc : c.nreg (sw 300) = AL := hI.hin _ (by ufo IFix sw)
  have hb2  := b2
  -- the search result is the log record at the query position, if there is one
  have hmatch : ∀ i, i < rd c₀ bSweep 301 → c₀.nmem (AL + 7 * i) = zp →
      (chainModel J.whole).param (Qof P) (logPos c₀.nmem AL i) =
        (chainModel J.whole).param (Qof P) ⟨zp, zh⟩ → t = i := fun i hi h1 h2 =>
    search_eq hA hs1 hs2 hi (key_of_match h1 h2)
  -- the address block
  have hok1 : okB W c.nmem cAddr c.nreg := cAddr_ok _ _ hKc.2.1 (by rwnl [hALc])
  refine IRS.seq (K₁ := cAddr.length) (K₂ := 11008 + (2 + (2 + hitK)))
    (IRS.block cAddr hI hok1) ?_ |>.mono (by simp [cAddr, checkK]) (fun _ => id)
  rintro c₁ hI₁ hA₁ hA₁' rfl
  obtain ⟨v1E, v1H, k1⟩ := cAddr_val c.nmem c.nreg hKc.2.1
  rw [hALc] at v1E v1H
  set c₁ : Config := { c with nreg := regB c.nmem cAddr c.nreg } with hc₁
  have nk1 : ∀ q, (q < sw 4100 ∨ sw 4102 < q) → c₁.nreg q = c.nreg q := fun q hq =>
    k1 q (by ufo kA sw at *) (by ufo kE sw at *) (by ufo kH sw at *)
  have hlp := log_posW hA ht
  have hE1 : c₁.nreg kE = c₀.nmem (AL + 7 * t) := by
    show regB c.nmem cAddr c.nreg kE = _; rw [v1E, hm _ (by nlinarith)]
  have hH1 : c₁.nreg kH = c₀.nmem (AL + 7 * t + 1) := by
    show regB c.nmem cAddr c.nreg kH = _; rw [v1H, hm _ (by nlinarith)]
  have hxE1 : c₁.nreg lsxE = zp := by rwx [nk1 _ (by ufo lsxE sw)]
  have hxH1 : c₁.nreg lsxH = zh := by rwx [nk1 _ (by ufo lsxH sw)]
  have hG1 : c₁.nreg (sw 40) = G := hI₁.hin _ (by ufo IFix sw)
  have h6z : zh = 0 → 6 ≤ zp := fun h0 => query_h6 hz harr h0
  -- the comparison
  refine IRS.seq (K₁ := 11008) (callOff_irs (C := J.whole) (dsc := sw 2) (ex := kE) (hx := kH)
    (ey := lsxE) (hy := lsxH) (g := sw 40) (o := kO) hI₁ (hA.ctxW hI₁)
    (by ufo kE kH lsxE lsxH sw) (by ufo kO sw)
    (by rw [hE1]; exact hlp.1) (by rwx [hxE1])
    (by rw [hG1, hGdef, aenv_gW hA]; exact gW_lt_nat J)
    (by rw [hE1, hH1]; exact hlp.2.1) (by rwx [hxE1, hxH1])
    (by rw [hE1, hH1]; exact hlp.2.2) (by rwx [hxE1, hxH1])
    (by unfold checkK hitK offerFK offerK at hroom; rw [show c₁.nreg ALLOC = c.nreg ALLOC from
      nk1 _ (by ufo ALLOC sw)]; omega)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hb1, hb2', k2, hal2, hm2⟩
  rw [hE1, hH1, hxE1, hxH1, hG1] at hb1 hb2'
  set kt := (chainModel J.whole).key (Qof P) (logPos c₀.nmem AL t) with hkt
  set kx := (chainModel J.whole).key (Qof P) ⟨zp, zh⟩ with hkx
  have hkt' : (chainModel J.whole).key (Qof P) ⟨c₀.nmem (AL + 7 * t), c₀.nmem (AL + 7 * t + 1)⟩
      = kt := rfl
  rw [hkt'] at hb1 hb2'
  have nk2 : ∀ q, (q < sw 4100 ∨ sw 4105 < q) → bandOf q ∉ oracleBands → q ≠ ALLOC →
      c₂.nreg q = c.nreg q :=
    fun q hq hb hqa => by
      rw [k2 q hb (by ufo kO sw at *) (by ufo kO sw at *) hqa]
      exact nk1 q (by ufo sw at *)
  have hfr2 : FrQ c c₂ := ⟨fun r hr hq hra => by
      rw [k2 r hr (fun h => hq (by subst h; right; ufo kO sw))
        (fun h => hq (by subst h; right; ufo kO sw)) hra]
      exact k1 r (fun h => hq (by subst h; right; ufo kA sw))
        (fun h => hq (by subst h; right; ufo kE sw))
        (fun h => hq (by subst h; right; ufo kH sw)),
    by rw [show c₁.nreg ALLOC = c.nreg ALLOC from nk1 _ (by ufo ALLOC sw)] at hal2
       exact hal2,
    fun a ha => hm2 a (by rw [show c₁.nreg ALLOC = c.nreg ALLOC from
      nk1 _ (by ufo ALLOC sw)]; exact ha)⟩
  have hk0₂  := (hK.fix hI₂).1
  have hacc₂ : AccOK P accA (ModB J 1 1) J.whole.radius z (dirOf d) L c₂ :=
    hacc.transport (fun j hj => nk2 (accA + j) (by ufo accA sw)
      (nob (by ufo accA sw) (by ufo accA sw)) (by ufo accA ALLOC sw))
  -- no offer when the record found is not at the query position
  have noOffer : ¬ (off (chainModel J.whole).W.n G kt = off (chainModel J.whole).W.n G kx) →
      ∀ K, IRS P W c₀ .skip c₂ K (fun c' => ∃ L', AccOK P accA (ModB J 1 1) J.whole.radius z
        (dirOf d) L' c' ∧ L ⊆ L' ∧ (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.whole (rayPt z (dirOf d) τ))) ∧
        HC P J c₀ z zp zh d L' ∧ FrQ c c') := by
    intro hne K
    refine IRS.skip (K := K) hI₂ ⟨L, hacc₂, le_rfl, fun τ h => Or.inl h, ?_, hfr2⟩
    intro i hi h1 h2 _ o τ _ _ _
    exfalso; apply hne
    have := hmatch i hi h1 h2
    rw [hkt, this, key_of_match h1 h2]
  by_cases hc1 : c₂.nreg K0 < c₂.nreg kO
  · rw [hk0₂] at hc1
    have hlt : off (chainModel J.whole).W.n G kt < off (chainModel J.whole).W.n G kx :=
      hb1.2.1 (by have := hb1.1; omega)
    exact (IRS.ifT (by rwx [hk0₂]) (noOffer (ne_of_lt hlt) 0)).mono (by omega)
      (fun _ => id)
  · refine (IRS.ifF hc1 ?_).mono (K := 2 + hitK + 2) (by omega) (fun _ => id)
    rw [hk0₂] at hc1
    have hn1 : ¬ off (chainModel J.whole).W.n G kt < off (chainModel J.whole).W.n G kx :=
      fun h => by have := hb1.2.2 h; omega
    by_cases hc2 : c₂.nreg K0 < c₂.nreg (kO + 1)
    · rw [hk0₂] at hc2
      have hlt : off (chainModel J.whole).W.n G kx < off (chainModel J.whole).W.n G kt :=
        hb2'.2.1 (by have := hb2'.1; omega)
      exact (IRS.ifT (by rwx [hk0₂]) (noOffer (ne_of_gt hlt) 0)).mono (by omega)
        (fun _ => id)
    · refine (IRS.ifF (K := hitK) hc2 ?_).mono (by omega) (fun _ => id)
      rw [hk0₂] at hc2
      have hn2 : ¬ off (chainModel J.whole).W.n G kx < off (chainModel J.whole).W.n G kt :=
        fun h => by have := hb2'.2.2 h; omega
      -- the record found is at the query position
      obtain ⟨he, hpar⟩ := bits_eq (x := logPos c₀.nmem AL t) hA hlp.1 hzP hlp.2.1 hzPp hn1 hn2
      have hpt : logPt P J c₀.nmem AL t = z := by
        unfold logPt; rw [he, hpar]; exact harr.2.2.2.1
      have ht₂ : c₂.nreg lsI = t := nk2 _ (by ufo lsI sw)
        (nob (by ufo lsI sw) (by ufo lsI sw)) (by ufo lsI ALLOC sw)
      have hd₂ : c₂.nreg qD = d := nk2 _ (by ufo qD sw)
        (nob (by ufo qD sw) (by ufo qD sw)) (by ufo qD ALLOC sw)
      refine (hit_irs hA hXc hI₂
        (by rwx [ht₂]) (by rwx [ht₂]) hz hzs hz2
        (by rwx [hd₂])
        (by unfold checkK at hroom; have := hA₂'
            rw [show c₁.nreg ALLOC = c.nreg ALLOC from nk1 _ (by ufo ALLOC sw)] at this
            omega)).mono le_rfl ?_
      rintro c' ⟨L', hacc', hLL, hsnd, hcmp, hfr'⟩
      rw [hd₂] at hacc' hsnd
      rw [hd₂, ht₂] at hcmp
      refine ⟨L', hacc', hLL, hsnd, ?_, hfr2.trans hfr'⟩
      intro i hi h1 h2 hf o τ hc hτ ho
      have hti := hmatch i hi h1 h2
      rw [← hti] at hf
      have hslot := hsl t ht (qS d) (qS_le d)
      have hpt'  := hpt
      have heq := slot_eq hA.hP hslot hf hpt' hz hzs hz2 hc
      exact hcmp hf τ hτ (heq.trans ho)

end

end S0C

end SweepIo

end Chazelle.Core
