module

public import Chazelle.Core.SweepIoS0CandQ3

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
  unfold Model.key; rw [h2]; unfold logPos; simp only; rw [h1]

theorem gW_lt_nat (J : Merge.Junction) : gW J < (chainModel J.whole).W.n := by
  have := gW_lt J; exact_mod_cast this

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
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
  have hAW : c.nreg ALLOC ≤ W := hI.hw.1 ALLOC
  have hA0 := hI.hA
  have hm : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a := hI.hm
  have hALc : c.nreg (sw 300) = AL := hI.hin _ (by unfold IFix sw; omega)
  have hb2 : AL + 7 * rd c₀ bSweep 301 ≤ c₀.nreg ALLOC := b2
  -- the search result is the log record at the query position, if there is one
  have hmatch : ∀ i, i < rd c₀ bSweep 301 → c₀.nmem (AL + 7 * i) = zp →
      (chainModel J.whole).param (Qof P) (logPos c₀.nmem AL i) =
        (chainModel J.whole).param (Qof P) ⟨zp, zh⟩ → t = i := fun i hi h1 h2 =>
    search_eq hA hs1 hs2 hi (key_of_match h1 h2)
  -- the address block
  have hok1 : okB W c.nmem cAddr c.nreg := cAddr_ok _ _ hKc.2.1 (by rw [hALc]; nlinarith)
  refine IRS.seq (K₁ := cAddr.length) (K₂ := 11008 + (2 + (2 + hitK)))
    (IRS.block cAddr hI hok1) ?_ |>.mono (by simp [cAddr, checkK]) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' rfl
  obtain ⟨v1E, v1H, k1⟩ := cAddr_val c.nmem c.nreg hKc.2.1
  rw [hALc] at v1E v1H
  set c₁ : Config := { c with nreg := regB c.nmem cAddr c.nreg } with hc₁
  have nk1 : ∀ q, (q < sw 4100 ∨ sw 4102 < q) → c₁.nreg q = c.nreg q := fun q hq =>
    k1 q (by unfold kA sw at *; omega) (by unfold kE sw at *; omega) (by unfold kH sw at *; omega)
  have hlp := log_posW hA ht
  have hE1 : c₁.nreg kE = c₀.nmem (AL + 7 * t) := by
    show regB c.nmem cAddr c.nreg kE = _; rw [v1E, hm _ (by nlinarith)]
  have hH1 : c₁.nreg kH = c₀.nmem (AL + 7 * t + 1) := by
    show regB c.nmem cAddr c.nreg kH = _; rw [v1H, hm _ (by nlinarith)]
  have hxE1 : c₁.nreg lsxE = zp := by rw [nk1 _ (by unfold lsxE sw; omega)]; exact hxE
  have hxH1 : c₁.nreg lsxH = zh := by rw [nk1 _ (by unfold lsxH sw; omega)]; exact hxH
  have hG1 : c₁.nreg (sw 40) = G := hI₁.hin _ (by unfold IFix sw; omega)
  have h6z : zh = 0 → 6 ≤ zp := fun h0 => query_h6 hz harr h0
  -- the comparison
  refine IRS.seq (K₁ := 11008) (callOff_irs (C := J.whole) (dsc := sw 2) (ex := kE) (hx := kH)
    (ey := lsxE) (hy := lsxH) (g := sw 40) (o := kO) hI₁ (hA.ctxW hI₁)
    (by unfold kE kH lsxE lsxH sw; omega) (by unfold kO sw; omega)
    (by rw [hE1]; exact hlp.1) (by rw [hxE1]; exact hzP)
    (by rw [hG1, hGdef, aenv_gW hA]; exact gW_lt_nat J)
    (by rw [hE1, hH1]; exact hlp.2.1) (by rw [hxE1, hxH1]; exact hzPp)
    (by rw [hE1, hH1]; exact hlp.2.2) (by rw [hxE1, hxH1]; exact h6z)
    (by unfold checkK hitK offerFK offerK at hroom; rw [show c₁.nreg ALLOC = c.nreg ALLOC from
      nk1 _ (by unfold ALLOC sw; omega)]; omega)) ?_
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
      rw [k2 q hb (by unfold kO sw at *; omega) (by unfold kO sw at *; omega) hqa]
      exact nk1 q (by unfold sw at *; omega)
  have hfr2 : FrQ c c₂ := ⟨fun r hr hq hra => by
      rw [k2 r hr (fun h => hq (by subst h; right; unfold kO sw; omega))
        (fun h => hq (by subst h; right; unfold kO sw; omega)) hra]
      exact k1 r (fun h => hq (by subst h; right; unfold kA sw; omega))
        (fun h => hq (by subst h; right; unfold kE sw; omega))
        (fun h => hq (by subst h; right; unfold kH sw; omega)),
    by rw [show c₁.nreg ALLOC = c.nreg ALLOC from nk1 _ (by unfold ALLOC sw; omega)] at hal2
       exact hal2,
    fun a ha => hm2 a (by rw [show c₁.nreg ALLOC = c.nreg ALLOC from
      nk1 _ (by unfold ALLOC sw; omega)]; exact ha)⟩
  have hk0₂ : c₂.nreg K0 = 0 := (hK.fix hI₂).1
  have hacc₂ : AccOK P accA (ModB J 1 1) J.whole.radius z (dirOf d) L c₂ :=
    hacc.transport (fun j hj => nk2 (accA + j) (by unfold accA sw; omega)
      (nob (by unfold accA sw; omega) (by unfold accA sw; omega)) (by unfold accA ALLOC sw; omega))
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
    exact (IRS.ifT (by rw [hk0₂]; exact hc1) (noOffer (ne_of_lt hlt) 0)).mono (by omega)
      (fun _ h => h)
  · refine (IRS.ifF hc1 ?_).mono (K := 2 + hitK + 2) (by omega) (fun _ h => h)
    rw [hk0₂] at hc1
    have hn1 : ¬ off (chainModel J.whole).W.n G kt < off (chainModel J.whole).W.n G kx :=
      fun h => by have := hb1.2.2 h; omega
    by_cases hc2 : c₂.nreg K0 < c₂.nreg (kO + 1)
    · rw [hk0₂] at hc2
      have hlt : off (chainModel J.whole).W.n G kx < off (chainModel J.whole).W.n G kt :=
        hb2'.2.1 (by have := hb2'.1; omega)
      exact (IRS.ifT (by rw [hk0₂]; exact hc2) (noOffer (ne_of_gt hlt) 0)).mono (by omega)
        (fun _ h => h)
    · refine (IRS.ifF (K := hitK) hc2 ?_).mono (by omega) (fun _ h => h)
      rw [hk0₂] at hc2
      have hn2 : ¬ off (chainModel J.whole).W.n G kx < off (chainModel J.whole).W.n G kt :=
        fun h => by have := hb2'.2.2 h; omega
      -- the record found is at the query position
      obtain ⟨he, hpar⟩ := bits_eq (x := logPos c₀.nmem AL t) hA hlp.1 hzP hlp.2.1 hzPp hn1 hn2
      have hpt : logPt P J c₀.nmem AL t = z := by
        unfold logPt; rw [he, hpar]; exact harr.2.2.2.1
      have ht₂ : c₂.nreg lsI = t := nk2 _ (by unfold lsI sw; omega)
        (nob (by unfold lsI sw; omega) (by unfold lsI sw; omega)) (by unfold lsI ALLOC sw; omega)
      have hd₂ : c₂.nreg qD = d := nk2 _ (by unfold qD sw; omega)
        (nob (by unfold qD sw; omega) (by unfold qD sw; omega)) (by unfold qD ALLOC sw; omega)
      refine (hit_irs hA hXc hI₂
        (by rw [ht₂]; exact ht) (by rw [ht₂]; exact hpt) hz hzs hz2
        (by rw [hd₂]; exact hacc₂)
        (by unfold checkK at hroom; have := hA₂'
            rw [show c₁.nreg ALLOC = c.nreg ALLOC from nk1 _ (by unfold ALLOC sw; omega)] at this
            omega)).mono le_rfl ?_
      rintro c' ⟨L', hacc', hLL, hsnd, hcmp, hfr'⟩
      rw [hd₂] at hacc' hsnd
      rw [hd₂, ht₂] at hcmp
      refine ⟨L', hacc', hLL, hsnd, ?_, hfr2.trans hfr'⟩
      intro i hi h1 h2 hf o τ hc hτ ho
      have hti := hmatch i hi h1 h2
      rw [← hti] at hf
      have hslot := hsl t ht (qS d) (qS_le d)
      have hpt' : logPt P J c₀.nmem (rd c₀ bSweep 300) t = z := hpt
      have heq := slot_eq hA.hP hslot hf hpt' hz hzs hz2 hc
      exact hcmp hf τ hτ (heq.trans ho)

end

end S0C

end SweepIo

end Chazelle.Core
