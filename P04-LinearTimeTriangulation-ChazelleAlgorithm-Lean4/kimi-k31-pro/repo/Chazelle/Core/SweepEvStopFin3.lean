module

public import Chazelle.Core.SweepEvStopFin2
public import Chazelle.Core.SweepEvStartM
public import Chazelle.Rwx
public import Chazelle.UnfoldTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 8000000

/-!
# The sweep (WP-D), stage 2, the finish of a stop origin: the offsets (RAM)

`slfOffs`: the offsets of the attachments `A₀` (`oF0 + 1, oF0 + 2`) and `A₁` (`a1F + 1, a1F + 2`)
compared with `Lst` (the start key `(cGL, 0)`) and with `0` (the base `(cGW, 0)`), and the anchor
flag `slfA` (`1` iff an attachment lies before the start).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop

@[expose] public section

/-- One comparison of the offset of `(ex, hx)` with that of `(y, 0)`. -/
def slfCmp (ex hx y o : ℕ) : Stmt := callOff (sw 2) ex hx y K0 cGW o

/-- The anchor flag. -/
def slfAnc : Stmt :=
  .ifLtN K0 slfO (.instr (.constN slfA 1))
    (.ifLtN K0 (slfO + 4) (.instr (.constN slfA 1)) (.instr (.constN slfA 0)))

/-- **The offsets** of `A₀`, `A₁` against `Lst` and `0`, and the anchor flag. -/
def slfOffs : Stmt :=
  .seq (.seq (slfCmp (oF0 + 1) (oF0 + 2) cGL slfO) (slfCmp (oF0 + 1) (oF0 + 2) cGW (slfO + 2)))
    (.seq (.seq (slfCmp (a1F + 1) (a1F + 2) cGL (slfO + 4))
      (slfCmp (a1F + 1) (a1F + 2) cGW (slfO + 4 + 2))) slfAnc)

/-- The offset of a stored position. -/
noncomputable def slfOff (P : Polygon) (J : Merge.Junction) (c : Config) (e h : ℕ) : ℝ :=
  oW J ((c.nreg e : ℝ) + (chainModel J.whole).param (Qof P) ⟨c.nreg e, c.nreg h⟩)

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-- **One comparison.** -/
theorem slfCmp_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {ex hx y o : ℕ}
    (hr : 240000 ≤ ex ∧ ex < 250000 ∧ 240000 ≤ hx ∧ hx < 250000 ∧ 240000 ≤ y ∧ y < 250000)
    (ho : 240700 ≤ o ∧ o + 1 < 250000)
    (hex : c.nreg ex < (chainModel J.whole).W.n)
    (hpp : ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg ex, c.nreg hx⟩)
    (h6 : c.nreg hx = 0 → 6 ≤ c.nreg ex) (hyn : c.nreg y < (chainModel J.whole).W.n)
    (h6y : 6 ≤ c.nreg y) {v : ℝ} (hv : oW J ((c.nreg y : ℝ) + 0) = v)
    (hroom : c.nreg ALLOC + 11008 ≤ W) :
    IRS P W c₀ (slfCmp ex hx y o) c 11008 (fun c' =>
      BitIs c' o (slfOff P J c ex hx < v) ∧ BitIs c' (o + 1) (v < slfOff P J c ex hx) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ o → r ≠ o + 1 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hgw := E.gw' hI
  have k0  := (E.hK.fix hI).1
  have hgn : gW J < (chainModel J.whole).W.n := by
    unfold gW; rw [cm_n]; have := tpos_lt J.whole J.m₁; omega
  refine (callOff_irs (P := P) (C := J.whole) hI (E.ctxW' hI)
    ⟨by ufo sw, by ufo sw, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2, by ufo K0 sw, by ufo K0 sw, by ufo cGW sw,
      by ufo cGW sw⟩ ho hex hyn (by rwx [hgw]) hpp
    (by rw [k0]; exact ⟨le_rfl, zero_lt_one, Nat.zero_le _⟩) h6 (fun _ => h6y) hroom).mono le_rfl ?_
  rintro c' ⟨b1, b2, fr, hA, hm⟩
  rw [hgw, k0] at b1 b2
  have hk : ∀ e h, (chainModel J.whole).key (Qof P) ⟨e, h⟩ =
      (e : ℝ) + (chainModel J.whole).param (Qof P) ⟨e, h⟩ := fun _ _ => rfl
  have hy0 : off (chainModel J.whole).W.n (gW J : ℝ)
      ((chainModel J.whole).key (Qof P) ⟨c.nreg y, 0⟩) = v := by
    rwx [hk]
  rw [hy0] at b1 b2
  exact ⟨b1, b2, fr, hA, hm⟩

/-! ## Frames -/

/-- The frame of a finish step writing the registers `R`. -/
def SlfFr (R : ℕ → Prop) (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ R r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)

theorem SlfFr.trans {R : ℕ → Prop} {c c₁ c₂ : Config} (h₁ : SlfFr R c c₁) (h₂ : SlfFr R c₁ c₂) :
    SlfFr R c c₂ :=
  ⟨fun r a b d => (h₂.1 r a b d).trans (h₁.1 r a b d), h₁.2.1.trans h₂.2.1,
    fun a ha => (h₂.2.2 a (by have := h₁.2.1; omega)).trans (h₁.2.2 a ha)⟩

theorem SlfFr.mono {R R' : ℕ → Prop} {c c' : Config} (h : SlfFr R c c') (hR : ∀ r, R r → R' r) :
    SlfFr R' c c' :=
  ⟨fun r a b d => h.1 r a (fun h' => b (hR r h')) d, h.2.1, h.2.2⟩

/-- The registers of the offsets step. -/
def slfOffR (r : ℕ) : Prop := sw 4054 ≤ r ∧ r ≤ sw 4062

theorem slfAnc_irs (hI : IInv W c₀ c) (k0 : c.nreg K0 = 0) (hb0 : c.nreg slfO ≤ 1)
    (hb4 : c.nreg (slfO + 4) ≤ 1) (hW : 1 ≤ W) :
    IRS P W c₀ slfAnc c 5 (fun c' => c'.nreg slfA ≤ 1 ∧
      (c'.nreg slfA = 1 ↔ (c.nreg slfO = 1 ∨ c.nreg (slfO + 4) = 1)) ∧
      (∀ q, q ≠ slfA → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  have hr : 240700 ≤ slfA ∧ slfA < 250000 := by ufo slfA sw
  unfold slfAnc
  by_cases h0 : c.nreg K0 < c.nreg slfO
  · refine (IRS.ifT h0 (set1_irs hI hr hW)).mono (by norm_num) ?_
    rintro c' ⟨h1, h2, h3⟩
    exact ⟨by omega, ⟨fun _ => Or.inl (by omega), fun _ => h1⟩, h2, h3⟩
  · refine (IRS.ifF h0 ?_).mono le_rfl (fun _ => id)
    by_cases h4 : c.nreg K0 < c.nreg (slfO + 4)
    · refine (IRS.ifT h4 (set1_irs hI hr hW)).mono (by norm_num) ?_
      rintro c' ⟨h1, h2, h3⟩
      exact ⟨by omega, ⟨fun _ => Or.inr (by omega), fun _ => h1⟩, h2, h3⟩
    · refine (IRS.ifF h4 (set1_irs hI hr (by omega))).mono (by norm_num) ?_
      rintro c' ⟨h1, h2, h3⟩
      exact ⟨by omega, ⟨fun h => by omega, fun h => by omega⟩, h2, h3⟩

/-- The facts of a position compared in the offsets step. -/
def SlfPos (P : Polygon) (J : Merge.Junction) (c : Config) (e h : ℕ) : Prop :=
  c.nreg e < (chainModel J.whole).W.n ∧
    ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg e, c.nreg h⟩ ∧ (c.nreg h = 0 → 6 ≤ c.nreg e)

theorem SlfPos.congr {e h : ℕ} {c c' : Config} (hp : SlfPos P J c e h) (he : c'.nreg e = c.nreg e)
    (hh : c'.nreg h = c.nreg h) : SlfPos P J c' e h := by
  unfold SlfPos at *; rwx [he, hh]

theorem slfOff_congr {e h : ℕ} {c c' : Config} (he : c'.nreg e = c.nreg e)
    (hh : c'.nreg h = c.nreg h) : slfOff P J c' e h = slfOff P J c e h := by
  unfold slfOff; rw [he, hh]

/-- **Comparing a position with the start and the base.** -/
theorem slfCmp2_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {ex hx o : ℕ}
    (hr : 240000 ≤ ex ∧ ex < 250000 ∧ 240000 ≤ hx ∧ hx < 250000)
    (ho : 240700 ≤ o ∧ o + 3 < 250000) (hoe : ex < o ∨ o + 3 < ex) (hoh : hx < o ∨ o + 3 < hx)
    (hp : SlfPos P J c ex hx) (hroom : c.nreg ALLOC + 2 * 11008 ≤ W) :
    IRS P W c₀ (.seq (slfCmp ex hx cGL o) (slfCmp ex hx cGW (o + 2))) c (2 * 11008) (fun c' =>
      BitIs c' o (slfOff P J c ex hx < Lst J) ∧ BitIs c' (o + 3) (0 < slfOff P J c ex hx) ∧
      SlfFr (fun r => o ≤ r ∧ r ≤ o + 3) c c') := by
  have hgn : gW J < (chainModel J.whole).W.n := by
    unfold gW; rw [cm_n]; have := tpos_lt J.whole J.m₁; omega
  have hLn := Lst_lt_n J
  have hgl := (E.hM.fix hI).gl
  have hgw := E.gw' hI
  have hcl : 240000 ≤ cGL ∧ cGL < 250000 := by ufo cGL sw
  have hcw : 240000 ≤ cGW ∧ cGW < 250000 := by ufo cGW sw
  refine IRS.seq (K₁ := 11008) (K₂ := 11008) (slfCmp_irs E hI ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
    hcl.1, hcl.2⟩ ⟨ho.1, by omega⟩ hp.1 hp.2.1 hp.2.2 (by rw [hgl]; exact Nat.mod_lt _ (by omega))
    (by rw [hgl]; exact start_key_ge_six J) (v := (Lst J : ℝ)) (by
      rw [hgl, oW_def]
      have := off_key (t := 0) hgn hLn le_rfl one_pos
      rw [this, add_zero]) (by omega)) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨b1, -, fr1, -, hm1⟩
  have k1 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ o → r ≠ o + 1 → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => fr1 r (band_sw_not ⟨h1, h2⟩) h3 h4 (by ufo ALLOC)
  have e1 := k1 ex hr.1 hr.2.1 (by omega) (by omega)
  have h1 := k1 hx hr.2.2.1 hr.2.2.2 (by omega) (by omega)
  have hp1 := hp.congr e1 h1
  refine (slfCmp_irs E hI₁ ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, hcw.1, hcw.2⟩ ⟨by omega, by omega⟩
    hp1.1 hp1.2.1 hp1.2.2 (by rwx [E.gw' hI₁]) (by ruo [E.gw' hI₁] gW)
    (v := 0) (by rw [E.gw' hI₁, add_zero, oW_def]; exact off_self _ _) (by omega)).mono le_rfl ?_
  rintro c₂ ⟨-, b2, fr2, hA2, hm2⟩
  rw [slfOff_congr e1 h1] at b2
  refine ⟨b1.of_eq (fr2 o (band_sw_not ⟨by omega, by omega⟩) (by omega) (by omega)
    (by ufo ALLOC)), b2, ⟨fun r hb hr' ha => ?_, hA₁.trans hA2, fun a ha => ?_⟩⟩
  · simp [not_and_or, not_le] at hr'
    rw [fr2 r hb (by omega) (by omega) ha, fr1 r hb (by omega) (by omega) ha]
  · rw [hm2 a (by omega), hm1 a ha]

/-- **The offsets step.** -/
theorem slfOffs_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hp₀ : SlfPos P J c (oF0 + 1) (oF0 + 2)) (hp₁ : SlfPos P J c (a1F + 1) (a1F + 2))
    (hroom : c.nreg ALLOC + 44037 ≤ W) :
    IRS P W c₀ slfOffs c 44037 (fun c' =>
      BitIs c' slfO (slfOff P J c (oF0 + 1) (oF0 + 2) < Lst J) ∧
      BitIs c' (slfO + 3) (0 < slfOff P J c (oF0 + 1) (oF0 + 2)) ∧
      BitIs c' (slfO + 4) (slfOff P J c (a1F + 1) (a1F + 2) < Lst J) ∧
      BitIs c' (slfO + 7) (0 < slfOff P J c (a1F + 1) (a1F + 2)) ∧
      c'.nreg slfA ≤ 1 ∧ (c'.nreg slfA = 1 ↔ (slfOff P J c (oF0 + 1) (oF0 + 2) < Lst J ∨
        slfOff P J c (a1F + 1) (a1F + 2) < Lst J)) ∧ SlfFr slfOffR c c') := by
  have r0 : 240000 ≤ oF0 + 1 ∧ oF0 + 1 < 250000 ∧ 240000 ≤ oF0 + 2 ∧ oF0 + 2 < 250000 := by
    ufo oF0 sw
  have r1 : 240000 ≤ a1F + 1 ∧ a1F + 1 < 250000 ∧ 240000 ≤ a1F + 2 ∧ a1F + 2 < 250000 := by
    ufo a1F sw
  have hO : 240700 ≤ slfO ∧ slfO + 3 < 250000 := by ufo slfO sw
  have k0 := (E.hK.fix hI).1
  unfold slfOffs
  refine IRS.seq (K₁ := 2 * 11008) (K₂ := 2 * 11008 + 5) (slfCmp2_irs E hI r0 hO
    (by ufo oF0 slfO sw) (by ufo oF0 slfO sw) hp₀ (by omega)) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨b0, b3, fr1⟩
  have k1 : ∀ r, 240000 ≤ r → r < 250000 → (r < slfO ∨ slfO + 3 < r) → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => fr1.1 r (band_sw_not ⟨h1, h2⟩) (by omega) (by ufo ALLOC)
  have e1 := k1 (a1F + 1) r1.1 r1.2.1 (by ufo a1F slfO sw)
  have h1 := k1 (a1F + 2) r1.2.2.1 r1.2.2.2 (by ufo a1F slfO sw)
  refine IRS.seq (K₁ := 2 * 11008) (K₂ := 5) (slfCmp2_irs E hI₁ r1
    (o := slfO + 4) (by ufo slfO sw)
    (by ufo a1F slfO sw) (by ufo a1F slfO sw) (hp₁.congr e1 h1)
    (by omega)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨b4, b7, fr2⟩
  rw [slfOff_congr e1 h1] at b4 b7
  have k2 : ∀ r, 240000 ≤ r → r < 250000 → (r < slfO + 4 ∨ slfO + 4 + 3 < r) →
      c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => fr2.1 r (band_sw_not ⟨h1, h2⟩) (by omega) (by ufo ALLOC)
  have b0' := b0.of_eq (k2 slfO (by ufo slfO sw) (by ufo slfO sw) (by omega))
  have b3' := b3.of_eq (k2 (slfO + 3) (by ufo slfO sw) (by ufo slfO sw)
    (by omega))
  refine (slfAnc_irs hI₂ (E.hK.fix hI₂).1 b0'.1 b4.1 (by omega)).mono le_rfl ?_
  rintro c₃ ⟨a1, a2, a3, a4⟩
  have hne : ∀ q, (q < slfA ∨ slfA < q) → c₃.nreg q = c₂.nreg q := fun q hq => a3 q (by omega)
  refine ⟨b0'.of_eq (hne _ (by ufo slfO slfA sw)),
    b3'.of_eq (hne _ (by ufo slfO slfA sw)),
    b4.of_eq (hne _ (by ufo slfO slfA sw)),
    b7.of_eq (hne _ (by ufo slfO slfA sw)), a1, ?_, ?_⟩
  · rw [a2, b0'.2, b4.2]
  · refine (fr1.mono fun r hr => ?_).trans ((fr2.mono fun r hr => ?_).trans
      ⟨fun r _ hr _ => a3 r (fun h => hr (by subst h; ufo slfOffR slfA sw)),
        (a3 ALLOC (by ufo ALLOC slfA sw)).ge,
        fun a _ => by rw [a4]⟩)
    · ufo slfOffR slfO sw at *
    · ufo slfOffR slfO sw at *

end

end SweepEv

end Chazelle.Core
