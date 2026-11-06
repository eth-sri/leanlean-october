module

public import Chazelle.MacT
public import Chazelle.Core.RestoreFTest
public import Chazelle.Core.DownPhaseDrvBTopMain
public import Chazelle.Core.RestoreRound
public import Chazelle.Core.WalkEmbed
public import Chazelle.Core.DownPhaseDrvDRound3
public import Chazelle.Core.DownPhaseDrvRLvB
public import Chazelle.Core.NFBuildArcs
public import Chazelle.Core.DownPhaseDrvHArc

namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideInArc)
variable {E : FEnv} {c₀ c : Config}

/-- The inner part of `endHead` (the end is in `[g', g' + L)`). -/
def endHeadIn (s p : ℕ) : Stmt :=
  .seq (cmpA ztyd p 81011 p 81155)
    (.seq (.ifLtN 81131 p ztffy
      ztzai)
      (.ifLtN 81011 s zttju .skip))

/-- **The head of an end**: in-stretch bit, host edge and height code. -/
def endHead (s p : ℕ) : Stmt :=
  .seq (Stmt.block [.constN s 0, .constN ztfz 0, .constN ztsk 0])
    (.ifLtN p 81131 .skip (.ifLtN p 81135 (endHeadIn s p) .skip))

/-- The height code of an end: `h + 1` inside a walk edge, `0` at a vertex. -/
noncomputable def endCode (Cα : Chain) (Q : Polygon) (p h1 : ℕ) : ℕ :=
  if (chainModel Cα).key Q ztcye < (chainModel Cα).key Q ⟨p, h1⟩ then h1 else 0

/-- The registers `endHead` writes (besides the key registers). -/
def HeadW (s q : ℕ) : Prop := KeyW q ∨ q = s ∨ q = s + 1 ∨ q = s + 2 ∨ q = s + 5 ∨ q = s + 6 ∨
  q = s + 7 ∨ q = s + 8 ∨ q = s + 9

/-- The cost bound of `endHead`. -/
def ehK : ℕ := 11040
theorem endHead_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s p : ℕ} (hs : 81160 ≤ s ∧ s + 9 < 81190) (hp : p = 81153 ∨ p = 81154)
    {H : Host} {Cα : Chain}
    (hwf : ChainWF E.P ztm c.nmem ztcpp)
    (hC : ChainDescAt c.nmem ztcpp zti H Cα) (hWm : 2 * Cα.m + 7 ≤ E.W)
    (h6 : 6 ≤ c.nreg 81131) (hg : c.nreg 81130 < E.M.W.n)
    (hL : c.nreg 81135 - c.nreg 81131 ≤ E.M.W.n)
    (hpe : PosOK Cα zti E.P.n ztgoo)
    (hroom : c.nreg ALLOC + ehK ≤ E.W) :
    FRS B E.P E.W c₀ zttjt c ehK (fun c' =>
      BitIs c' s (c.nreg 81131 ≤ c.nreg p ∧ c.nreg p < c.nreg 81135 ∧
        (c.nreg 81131 < c.nreg p ∨ (chainModel Cα).key zti ztryt <
          (chainModel Cα).key zti ztgoo)) ∧
      (c'.nreg s = 1 → c'.nreg ztbk = ztdcr % E.M.W.n ∧
        c'.nreg ztfp = endCode Cα zti ztfgw ztvix ∧
        BitIs c' ztyd ((chainModel Cα).key zti ztryt <
          (chainModel Cα).key zti ztgoo)) ∧
      c'.nreg ztfz = 0 ∧ c'.nreg ztsk = 0 ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ HeadW s q → c'.nreg q = c.nreg q) := by
  zubkz
  zucb
  set g' := c.nreg 81131
  set pE := c.nreg p
  set h1 := c.nreg 81155
  set kz := (chainModel Cα).key _ ztuje
  set kh := (chainModel Cα).key _ ztujf
  have ok0 : okB E.W c.nmem [.constN s 0, .constN ztfz 0, .constN ztsk 0] c.nreg := by
    zudu
    exact ⟨ztzof,
      ⟨Or.inl ztec, by_omega⟩,
      ⟨Or.inl ztec, by_omega⟩, trivial⟩
  refine (FRS.seq (K₂ := 11035) ztemq ztiy).mono
    (by simp [ehK]) ztb
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.constN s 0, .constN _ 0, .constN _ 0]
      c.nreg q := fun q => by zvnbm
  have v0 : c₁.nreg s = 0 := by zumwx; zumxd
  have v5 : c₁.nreg ztfz = 0 := by zumwx; zumxd
  have v6 : c₁.nreg ztsk = 0 := by zumwx; zumxd
  have f₁ : ∀ q, q ≠ s → q ≠ s + 5 → q ≠ s + 6 → c₁.nreg q = c.nreg q := fun q a b d => by
    zumwx; simp [regB, regI, upd, a, b, d]
  zulp
  have hA₁' : ztdc := f₁ _ ztu
    ztu ztu
  have r := fun q (hq : q < 81160 ∨ 81190 ≤ q) => f₁ q by_omega by_omega by_omega
  have rp : c₁.nreg p = pE := by_grind
  have r31 : ztuql := by_grind
  have r35 : c₁.nreg 81135 = c.nreg 81135 := by_simp_all
  have fin0 : ∀ c' : Config, (∀ q, 80000 ≤ q → q < 90000 → ¬ HeadW s q → c'.nreg q = c₁.nreg q) →
      ∀ q, 80000 ≤ q → q < 90000 → ¬ HeadW s q → c'.nreg q = c.nreg q :=
    fun c' h q a b hq => by
      zumqz
      rw [h q a b (by unfold HeadW; exact hq), f₁ q by_omega by_omega by_omega]
  have no : ¬ (g' ≤ pE ∧ pE < c.nreg 81135 ∧ ztnzu) →
      FRS B E.P E.W c₀ .skip c₁ 0 (fun c' =>
      BitIs c' s _ ∧
      (c'.nreg s = 1 → c'.nreg ztbk = (c.nreg 81130 + ztoef) % E.M.W.n ∧
        c'.nreg ztfp = endCode Cα zti pE h1 ∧ BitIs c' ztyd (kz < kh)) ∧
      c'.nreg _ = 0 ∧ c'.nreg _ = 0 ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ HeadW s q → c'.nreg q = c.nreg q) := fun hn =>
    FRS.skip hI₁ ⟨BitIs.const_zero v0 hn, by_grind, v5, v6,
      by grind⟩
  by_cases a1 : c₁.nreg p < c₁.nreg 81131
  · exact (FRS.ifT a1 ztvzy).mono by_omega
      by_grind
  zuhip
  by_cases a2 : c₁.nreg p < c₁.nreg 81135
  swap
  · exact (FRS.ifF a2 ztvzy).mono by_omega
      by_grind
  refine (FRS.ifT a2 ?_).mono (K := 11033) by_omega ztb
  rw [rp, r31] at a1
  rw [rp, r35] at a2
  -- the comparison
  have hpz : PosOK Cα zti E.P.n ⟨c₁.nreg p, c₁.nreg 81011⟩ := by
    rw [rp, r 81011 by_omega, hI.hin _ ztbc, hE.k0]
    exact ⟨hpe.1, ⟨le_of_eq rfl, by show (0 : ℝ) < 1; norm_num, Nat.zero_le _⟩,
      by grind⟩
  have hph : PosOK Cα zti E.P.n ⟨c₁.nreg p, c₁.nreg 81155⟩ := by
    rw [rp, r 81155 by_omega]; exact hpe
  have ir : ∀ q, 80000 ≤ q → q < 90000 → InR q := fun q a b => ztbqy
  have nk : ztcpg := fun q a b h => by unfold KeyW at h; omega
  refine FRS.seq (K₂ := 21) (cmpA_fs hE hB hI₁ (r := s + 7) ztgy
    ztrsk (ir 81011 by_norm_num by_norm_num) ztrsk
    (ir 81155 by_norm_num by_norm_num) ztrtz (nk _ by_norm_num
    by_norm_num) (nk p by_omega by_omega) (nk _ by_norm_num by_norm_num)
    (by rw [m₁, r 81133 by_omega, hA₁']; exact hwf) (by rw [m₁, r 81133 by_omega]; exact hC)
    hWm hpz hph (by rw [hA₁']; unfold ehK at hroom; omega))
    (fun c₂ hI₂ hA₂ ⟨b7, _, f₂⟩ => ?_)
  rw [rp, r 81011 by_omega, hI.hin 81011 ztbc, hE.k0,
    r 81155 by_omega] at b7
  have g₂ := f₂
  have w0 : c₂.nreg s = 0 := by
    rw [g₂ s by_omega by_omega (nk s by_omega by_omega) by_omega by_omega, v0]
  zudpz
  have w31 : zturk := by
    rw [g₂ _ by_norm_num by_norm_num ztmg by_omega
      by_omega, r31]
  have w7 : c₂.nreg p = pE := by
    rw [g₂ _ by_omega by_omega ztrtz by_omega by_omega, rp]
  -- the in-stretch bit
  have step : FRS B E.P E.W c₀ (.ifLtN 81131 p ztffy
      ztzai) c₂ 5 (fun c' =>
        BitIs c' s ztnzu ∧ ∀ q, q ≠ s → c'.nreg q = c₂.nreg q) := by
    by_cases a3 : c₂.nreg 81131 < c₂.nreg p
    · exact (FRS.ifT a3 ((setR_fs hB hI₂ ztgy hW1).mono le_rfl
        (fun c' ⟨v, f⟩ => ⟨BitIs.const_one v by_omega, f⟩))).mono
        by_omega ztb
    zuhir
    by_cases a4 : c₂.nreg 81011 < c₂.nreg ztyd
    · exact (FRS.ifT a4 ((setR_fs hB hI₂ ztgy hW1).mono le_rfl
        (fun c' ⟨v, f⟩ => ⟨BitIs.const_one v (Or.inr (b7.2.1 (by have := b7.1; omega))), f⟩))).mono
        by_omega ztb
    · exact (FRS.ifF a4 (FRS.skip (K := 0) hI₂ ⟨BitIs.const_zero w0 (fun h => by
        zuy
        · rw [w31, w7] at a3; exact a3 h
        · have := b7.2.2 h; omega), by_omega⟩)).mono by_omega (fun _ h => h)
  refine (FRS.seq (K₂ := 12) step (fun c₃ hI₃ hA₃ ⟨b0, f₃⟩ => ?_)).mono by_omega
    ztb
  have fin : ∀ c' : Config, zteaz →
      ∀ q, 80000 ≤ q → q < 90000 → ¬ HeadW s q → c'.nreg q = c.nreg q := by
    intro c' h q a b hq
    zumqz
    rw [h q by_omega by_omega by_omega, f₃ q by_omega, g₂ q a b by_grind by_omega
      by_omega, f₁ q by_omega by_omega by_omega]
  have s5 : ∀ c' : Config, zteaz →
      c'.nreg ztfz = 0 ∧ c'.nreg ztsk = 0 := fun c' h => by
    rw [h _ by_omega by_omega by_omega, h _ by_omega by_omega by_omega,
      f₃ _ by_omega, f₃ _ by_omega, g₂ _ by_omega by_omega ztnm
      by_omega by_omega, g₂ _ by_omega by_omega ztnm by_omega
      by_omega]
    zulyc
  zufxa
  by_cases a5 : c₃.nreg 81011 < c₃.nreg s
  · have b7' : c₃.nreg ztyd ≤ 1 := by rw [f₃ _ by_omega]; exact b7.1
    refine (FRS.ifT a5 ((endMap_fs hE hB hI₃ ztgy
      ⟨by_omega, by_omega⟩ by_omega by_omega
      ztjwd by_omega by_omega by_omega by_omega
      by_omega by_omega
      ztgfq
      (by rw [f₃ _ by_omega, g₂ _ by_norm_num by_norm_num ztmg
        by_omega by_omega, r 81130 by_omega]; exact hg)
      ztgfq b7').mono le_rfl
      (fun c' ⟨u1, u2, u3, uf⟩ => ?_))).mono by_omega (fun _ h => h)
    have e30 : c₃.nreg 81130 = c.nreg 81130 := by
      rw [f₃ _ by_omega, g₂ _ by_norm_num by_norm_num ztmg
        by_omega by_omega, r 81130 by_omega]
    have e7 : c₃.nreg p = pE := by rw [f₃ _ by_omega, w7]
    have e31 : ztusk := by rw [f₃ _ by_omega, w31]
    have e55 : c₃.nreg 81155 = h1 := by
      rw [f₃ _ by_omega, g₂ _ by_norm_num by_norm_num ztmg
        by_omega by_omega, r 81155 by_omega]
    have e77 : c₃.nreg _ = c₂.nreg ztyd := f₃ _ by_omega
    refine ⟨(b0.of_eq (uf s by_omega by_omega by_omega)).congr ⟨by_grind,
      by grind⟩, fun _ => ⟨by rw [u1, e30, e7, e31], ?_,
        b7.of_eq (by rw [uf _ by_omega by_omega by_omega, e77])⟩, (s5 c' uf).1, (s5 c' uf).2,
      fin c' uf⟩
    unfold endCode
    zulss
    · rw [u2 (by rw [e77]; exact b7.2.2 hk), e55]
    · exact u3 (by
        rw [e77]; have h1 := b7.1; by_contra hne; exact hk (b7.2.1 by_omega))
  · have z : c₃.nreg s = 0 := by rw [k0₃] at a5; omega
    exact (FRS.ifF a5 (FRS.skip (K := 0) hI₃ ⟨by_grind,
      by grind, (s5 c₃ by_omega).1, (s5 c₃ by_omega).2,
      fin c₃ by_omega⟩)).mono by_omega (fun _ h => h)

/-- **The tail of an end**: if it is strictly inside the stretch and its host edge is in the
edge range, the two tests (`endRun`), then the side bit (`endSd`). -/
def endTail (s σ : ℕ) (sT : Stmt) : Stmt :=
  .ifLtN 81011 s (.seq (.ifLtN ztbk 81021 .skip (.ifLtN ztbk 81025 (endRun s σ sT) .skip))
    ztvpx) .skip

/-- The cost bound of `endTail`. -/
def etK (E : FEnv) : ℕ := erK E + 33095

/-- The registers `endTail` writes below the test's registers. -/
def TailW (s q : ℕ) : Prop := RunW s q ∨ SdW s q
theorem FWin.congr' {c c' : Config} (h : FWin E c)
    (hq : ∀ q, 81007 ≤ q → q ≤ 81010 → c'.nreg q = c.nreg q) : FWin E c' := by
  zumqt
  rw [hq 81007 by_norm_num by_norm_num, hq 81008 by_norm_num by_norm_num,
    hq 81009 by_norm_num by_norm_num, hq 81010 by_norm_num by_norm_num]
  zubh

/-- The edge range of the candidates. -/
def InRange (c₀ : Config) (e : ℕ) : Prop := c₀.nreg 81021 ≤ e ∧ e < c₀.nreg 81025
theorem nfregs_of (hE : FGood E c₀) : ∃ reg, NFRegs E.M zti E.N reg := by
  zucbc
theorem endTail_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {s σ : ℕ}
    (hs : 81160 ≤ s ∧ s + 9 < 81190) (hσ : σ ≤ 1) (h5 : c.nreg ztfz = 0)
    (h6 : c.nreg ztsk = 0) (hs1 : c.nreg s ≤ 1)
    (hcand : c.nreg s = 1 → InRange c₀ ztwra → ∀ σb, σb ≤ 1 →
      CandOK E ztwke ztqih σb)
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M zti E.P.n ztke)
    (hroom : c.nreg ALLOC + etK E ≤ E.W) :
    FRS B E.P E.W c₀ (endTail s σ E.sT) c (etK E) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ TailW s q → c'.nreg q = c.nreg q) ∧
      ztfn ∧
      (c.nreg s = 1 → InRange c₀ ztwra →
        ∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
        c.nreg ztfp = 0 → ∀ σb, σb ≤ 1 → GoodAt E reg ztwra σb →
          c'.nreg 81007 = 1) ∧
      c'.nreg ztfz ≤ 1 ∧
      (c'.nreg ztfz = 1 → c.nreg s = 1 ∧ InRange c₀ ztwra ∧ c.nreg 81007 = 0) ∧
      (c.nreg s = 1 → InRange c₀ ztwra → c.nreg 81007 = 0 →
        ∃ ct ct' : Config, TOut E ct ct' ∧ ct.nreg 81060 = c.nreg ztbk ∧
        ct.nreg 81061 = c.nreg ztfp ∧ ct.nreg 81063 = σ ∧
        c'.nreg ztjv = ct'.nreg 83012 ∧ c'.nreg ztiz = ct'.nreg 83013 ∧
        (c'.nreg ztfz = 1 ↔ (ct'.nreg 83010 = 1 ∧ ct'.nreg 83011 = 1 ∧
          ztdbt)) ∧
        ztcmv) ∧
      c'.nreg ztsk ≤ 1 ∧
      (c'.nreg ztfz = 1 → ztceg →
        (c'.nreg ztsk = 1 ↔ (E.M.key zti ztke =
          E.M.key zti ztwke ∨
        sideInArc ztbakc
          ztxdq
          ztxdp)))) := by
  zuicu
  zubgm
  have i21 : ∀ c' : Config, FInv E.W c₀ c' → c'.nreg 81021 = c₀.nreg 81021 := fun c' h =>
    h.hin _ ztbc
  have i25 : ∀ c' : Config, FInv E.W c₀ c' → c'.nreg 81025 = c₀.nreg 81025 := fun c' h =>
    h.hin _ ztbc
  by_cases a0 : c.nreg 81011 < c.nreg s
  swap
  · have z : c.nreg s = 0 := by zvnib at a0; omega
    exact (FRS.ifF a0 (FRS.skip (K := 0) hI by_grind)).mono
      ztqgl ztb
  have o : ztpmj := by zvnib at a0; omega
  refine (FRS.ifT a0 ?_).mono (K := erK E + 33093) ztqgl ztb
  -- the tests
  have part1 : FRS B E.P E.W c₀ (.ifLtN ztbk 81021 .skip
      (.ifLtN ztbk 81025 ztrpg .skip)) c (erK E + 4) (fun c' => FWin E c' ∧
      ztcfl ∧
      ztfn ∧
      (InRange c₀ ztwra →
        ∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
        c.nreg ztfp = 0 → ∀ σb, σb ≤ 1 → GoodAt E reg ztwra σb →
          c'.nreg 81007 = 1) ∧
      c'.nreg ztfz ≤ 1 ∧
      ztbalq ∧
      (InRange c₀ ztwra → c.nreg 81007 = 0 →
        ∃ ct ct' : Config, TOut E ct ct' ∧ ct.nreg 81060 = c.nreg ztbk ∧
        ct.nreg 81061 = c.nreg ztfp ∧ ct.nreg 81063 = σ ∧
        c'.nreg ztjv = ct'.nreg 83012 ∧ c'.nreg ztiz = ct'.nreg 83013 ∧
        (c'.nreg ztfz = 1 ↔ (ct'.nreg 83010 = 1 ∧ ct'.nreg 83011 = 1 ∧
          ztdbt)) ∧
        ztcmv)) := by
    have out : ¬ InRange c₀ _ → FRS B E.P E.W c₀ .skip c 0 (fun c' => FWin E c' ∧
        ztcfl ∧
        ztfn ∧
        (InRange c₀ _ →
          ∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
          c.nreg ztfp = 0 → ∀ σb, σb ≤ 1 → GoodAt E reg ztwra σb →
            c'.nreg 81007 = 1) ∧
        c'.nreg ztfz ≤ 1 ∧
        ztbalq ∧
        (InRange c₀ ztwra → c.nreg 81007 = 0 →
          ∃ ct ct' : Config, TOut E ct ct' ∧ ct.nreg 81060 = c.nreg ztbk ∧
          ct.nreg 81061 = c.nreg ztfp ∧ ct.nreg 81063 = σ ∧
          c'.nreg ztjv = ct'.nreg 83012 ∧ c'.nreg ztiz = ct'.nreg 83013 ∧
          (c'.nreg ztfz = 1 ↔ (ct'.nreg 83010 = 1 ∧ ct'.nreg 83011 = 1 ∧
            ztdbt)) ∧
          ztcmv)) := fun hn =>
      FRS.skip hI ⟨hw, by_omega, id, fun h => absurd h hn, by_omega,
        by simp_all, fun h => absurd h hn⟩
    by_cases r1 : c.nreg ztbk < c.nreg 81021
    · exact (FRS.ifT r1 (out (fun h => by have := h.1; rw [i21 c hI] at r1; omega))).mono
        by_omega by_grind
    refine (FRS.ifF r1 ?_).mono le_rfl ztb
    by_cases r2 : c.nreg ztbk < c.nreg 81025
    swap
    · exact (FRS.ifF r2 (out (fun h => by have := h.2; rw [i25 c hI] at r2; omega))).mono
        by_omega by_grind
    have hr : InRange c₀ ztwra :=
      ⟨by rw [i21 c hI] at r1; omega, by rw [i25 c hI] at r2; exact r2⟩
    refine (FRS.ifT r2 ((endRun_fs hE hB hBT hI hw by_omega hσ h5 by_grind
      by_omega (by unfold etK at hroom; omega)).mono le_rfl
      (fun c' ⟨w', f', m', g', v', v1', t'⟩ => ⟨w', f', m', by_grind, v',
        by grind, fun _ hz => by have := t' hz; rw [i21 c hI] at this; exact this⟩))).mono
      by_omega ztb
  refine (FRS.seq (K₂ := 33087) part1 (fun c₁ hI₁ hA₁ ⟨w₁, f₁, m₁, g₁, v₁, vv₁, t₁⟩ => ?_)).mono
    by_omega ztb
  have e1 : ztzpm := f₁ _ by_omega by_omega
    ztfgb
  have e2 : c₁.nreg _ = c.nreg ztfp := f₁ _ by_omega by_omega
    ztfgb
  have e40 : ztmvf := f₁ _ by_omega by_omega
    ztfgb
  have e41 : ztmvg := f₁ _ by_omega by_omega
    ztfgb
  zuhhz
  have hxE : c₁.nreg _ = 1 → PosG E.M _ E.P.n ⟨c₁.nreg _, c₁.nreg ztfp⟩ :=
    fun h => by
      obtain ⟨hr, -⟩ := vv₁ h
      have hc := hcand o hr 0 by_omega
      zuea
      exact posG_of_vlo hE hI hc.1 hc.2.1 (Or.inr (by rw [i21 c hI]; exact hr.1))
  have hxF : c₁.nreg _ = 1 → PosG E.M _ E.P.n ⟨c₁.nreg _, c₁.nreg ztiz⟩ :=
    fun h => by
      obtain ⟨hr, hz⟩ := vv₁ h
      obtain ⟨ct, ct', hT, -, -, -, h3, h4, hv, -⟩ := t₁ hr hz
      obtain ⟨b10, b11, b12⟩ := hv.1 h
      zubfd

      zukru
      exact posG_of_vlo hE hI₁ hfe hfp (by rw [i21 c₁ hI₁]; exact b12)
  have hr1 : c₁.nreg ALLOC + 33087 ≤ E.W := by
    have h' : c.nreg ALLOC + (erK E + 33095) ≤ E.W := hroom
    linarith
  refine (endSd_fs hE hB hI₁ ztgy v₁ hxE hxF ztkst
    hr1).mono le_rfl (fun c' ⟨u6, us, uf⟩ => ?_)
  have back : ∀ q, 81011 ≤ q → q < 83000 → ¬ SdW s q → c'.nreg q = c₁.nreg q := by_grind
  have b5 : c'.nreg _ = c₁.nreg ztfz := back _ by_omega by_omega
    ztfgc
  have b3 : c'.nreg _ = c₁.nreg ztjv := back _ by_omega by_omega
    ztfgc
  have b4 : c'.nreg _ = c₁.nreg ztiz := back _ by_omega by_omega
    ztfgc
  have bflag : ∀ q, 81007 ≤ q → q ≤ 81010 → c'.nreg q = c₁.nreg q := fun q a b =>
    uf q by_omega by_omega ztfgc
  have bf7 : ztmuj := by_grind
  refine ⟨w₁.congr' bflag, fun q a b h => ?_, fun h => bf7 ▸ m₁ h,
    fun _ hr reg hr' hch h2 σb hσb hg => bf7 ▸ g₁ hr reg hr' hch h2 σb hσb hg,
    by rw [b5]; exact v₁, fun h => by rw [b5] at h; exact by_grind, fun _ hr hz => ?_, u6,
    fun h hj => ?_⟩
  · unfold TailW at h
    rw [back q by_omega by_omega by_grind,
      f₁ q a b by_grind]
  · obtain ⟨ct, ct', hT, a1, a2, a3, h3, h4, hv, hm⟩ := t₁ hr hz
    refine ⟨ct, ct', hT, a1, a2, a3, by rw [b3, h3], by rw [b4, h4], by rw [b5]; exact hv,
      by omega⟩
  · rw [b5] at h
    have := us h (by rw [e40, e41, i21 c₁ hI₁]; exact hj)
    rw [e1, e2, e40, e41, ← b3, ← b4] at this
    zufep
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs

/-- The environment rebased at `c₀'`. -/
def FEnv.re (E : FEnv) (c₀' : Config) : FEnv := { E with A₀ := c₀'.nreg ALLOC, m₀ := c₀'.nmem }
variable {E : FEnv} {c₀ c₀' : Config}

/-- **Rebasing the run facts.** -/
theorem FGood.rebase (hE : FGood E c₀) (hI : FInv E.W c₀ c₀') : FGood (E.re c₀') c₀' := by
  have hag : ∀ a, a < E.A₀ → c₀'.nmem a = E.m₀ a := hI.agree hE
  have hA : E.A₀ ≤ c₀'.nreg ALLOC := hI.allocA hE
  have hag' : ∀ a, a < E.A₀ → E.m₀ a = c₀'.nmem a := fun a ha => (hag a ha).symm
  zufyc
  have hfx : ∀ q, FFix q → c₀'.nreg q = c₀.nreg q := hI.hin
  have hMD0 : c₀'.nmem E.MD = E.m₀ E.MD := hag _ (by have := hE.hwf.1; omega)
  have hback : c₀'.nmem E.MD = 0 → ∀ H C, ChainDescAt c₀'.nmem ztcsy zti H C →
      ChainDescAt E.m₀ ztcsy zti H C := fun h0 H C hC => by
    have hW := (hwf'.2 h0).2 H C hC
    exact ShotList.chainDescAt_copy hC hW.2.2.1 hag' (fun j hj => hag' _ (by have := hE.hwf.1; omega))
  exact {
    hT := hE.hT, hcu := hE.hcu, hBc := hE.hBc, hBo := hE.hBo, hB8 := hE.hB8, hloc := hE.hloc,
    hhalf := hE.hhalf, hOkM := hE.hOkM, hG := hE.hG, hWh := hE.hWh,
    hX := E.X.mono _ _ _ _ _ hA (E.X.local_ _ _ _ _ _ hag' hE.hX),
    hcap := by
      show E.γ ≤ E.X.cap E.P c₀'.nmem E.g
      rw [hE.hloc _ _ _ _ _ hag hE.hX]; exact hE.hcap
    hwf := hwf'.mono hA
    hreg := fun h0 H C hC => hE.hreg ztljf H C ztqpv
    hsimp := fun h0 H C hC => hE.hsimp ztljf H C ztqpv
    hMD := hMD', hGM := hE.hGM, hOk := hE.hOk,
    hNW := (Robust.transport hE.hNW hag).mono hA
    hNF := hE.hNF, hdeg := hE.hdeg, hsg := hE.hsg, hr := hE.hr, a0 := rfl, m0 := rfl,
    i0 := by zumzw; exact hE.i0
    i1 := by zumzw; exact hE.i1
    i2 := by zumzw; exact hE.i2
    i3 := by zumzw; exact hE.i3
    i4 := by zumzw; exact hE.i4
    i5 := by zumzw; exact hE.i5
    i6 := by zumzw; exact hE.i6
    k0 := by zumyj; exact hE.k0
    k1 := by zumyj; exact hE.k1
    k2 := by zumyj; exact hE.k2
    k3 := by zumyj; exact hE.k3
    k5 := by zumyj; exact hE.k5
    k7 := by zumyj; exact hE.k7
    pn := by zumyj; exact hE.pn
    nE := by zumyj; exact hE.nE
    hE2 := by zumyj; exact hE.hE2
    wn := by zumyj; exact hE.wn
    k10 := by zumyj; exact hE.k10
    hvr := by
      zuntl; exact hE.hvr
    hvc := by
      zuntl; exact hE.hvc
    vlo6 := by rw [hfx 81021 ztbc]; exact hE.vlo6
    ehr := by
      zuntm; exact hE.ehr
    ehc := by
      zuntm; exact hE.ehc }

/-- **A run step from a later base** is a run step from the earlier one. -/
theorem FRS.restrict {B : Finset ℕ} {P : Polygon} {W : ℕ} {s : Stmt} {c : Config} {K : ℕ}
    {Q : Config → Prop} (hI : FInv W c₀ c₀') (h : FRS B P W c₀' s c K Q)
    (hc : c₀.nreg ALLOC ≤ c₀'.nreg ALLOC) : FRS B P W c₀ s c K Q := by
  obtain ⟨c', k, ex, hk, hI', hrf, hq⟩ := h
  refine ⟨c', k, ex, hk, ⟨hI'.hw, fun q hq => (hI'.hin q hq).trans ztfsi, le_trans hI.hA hI'.hA,
    fun a ha => (hI'.hm a by_omega).trans ztduw⟩, ?_, hq⟩
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁, b₁⟩ := hrf
  exact ztedy
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Chazelle.Chain (sideInArc)

/-- **What the test at an end leaves**: if the end `d` is in the open stretch, the offsets
satisfying `G` are those on one side of the arrival `α'`, which is at the other end `d'` when it
is in the open stretch. -/
def EndInfo (L d d' : ℝ) (G : ℝ → Prop) : Prop :=
  0 < d → d < L → ∃ α' : ℝ, ∃ s : Prop, 0 ≤ α' ∧ (0 < α' → α' < L → α' = d') ∧
    ∀ v, G v ↔ (sideInArc d α' v ↔ s)

/-- With both ends outside the open stretch, the side is constant on it. -/
theorem side_const {L d b v w : ℝ} (hd : d = 0 ∨ L ≤ d) (hb : b = 0 ∨ L ≤ b) (hv0 : 0 < v)
    (hvL : v < L) (hw0 : 0 < w) (hwL : w < L) : sideInArc d b v ↔ sideInArc d b w := by
  rcases hd with rfl | hd <;> rcases hb with rfl | hb <;> unfold sideInArc <;>
    split_ifs with h <;> constructor <;> intro h' <;>
    first
    | (left; linarith)
    | (right; linarith)
    | (exact ⟨by_linarith, by_linarith⟩)
    | (exfalso; rcases h' with h' | h' <;> linarith)
theorem out_of {L y : ℝ} (hy : 0 ≤ y) (h : ¬ ztndj) : y = 0 ∨ L ≤ y := by
  grind

/-- **The side of the node chord is the same for all offsets left by the tests.** -/
theorem stretch_side {L da βb : ℝ} (hda0 : 0 ≤ da) (hβ0 : 0 ≤ βb) (hne : da ≠ βb)
    {GA GB : ℝ → Prop} (hA : EndInfo L da βb GA) (hB : EndInfo L βb da GB)
    {u x : ℝ} (hu0 : 0 < u) (huL : u < L) (hx0 : 0 < x) (hxL : x < L) (hua : u ≠ da)
    (hub : u ≠ βb) (hxa : x ≠ da) (hxb : x ≠ βb) (hAu : GA u) (hAx : GA x) (hBu : GB u)
    (hBx : GB x) : sideInArc da βb u ↔ sideInArc da βb x := by
  by_cases ha : 0 < da ∧ da < L
  · obtain ⟨α', sA, hα0, hα', hGA⟩ := hA ha.1 ha.2
    exact witness_side ha.1 ha.2 hβ0 hne hα0 hα' hB hu0 huL hx0 hxL hua hub hxa hxb
      ((hGA u).1 hAu) ((hGA x).1 hAx) hBu hBx
  · zugji
    · obtain ⟨β', sB, hβ0', hβ', hGB⟩ := hB hb.1 hb.2
      have h := witness_side hb.1 hb.2 hda0 ztnr hβ0' hβ' hA hu0 huL hx0 hxL hub hua
        hxb hxa ((hGB u).1 hBu) ((hGB x).1 hBx) hAu hAx
      rw [Chazelle.Chain.sideInArc_swap ztnr hub hua,
        Chazelle.Chain.sideInArc_swap ztnr hxb hxa] at h
      grind
    · exact side_const (out_of hda0 ha) (out_of hβ0 hb) hu0 huL hx0 hxL
open Set
open Chazelle.Chain (sidePt SideAttach sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)

/-- **A stretch of a kind-1 piece.** -/
structure Stretch (M : Model) (Cα : Chain) (g g' L : ℕ) : Prop where
  hA : WalkEmbed.Agree M.W (chainModel Cα).W g g' L
  hg : g < M.W.n
  hL0 : 0 < L
  hLn : L < M.W.n
  h6 : 6 ≤ g'
  hgL : g' + L ≤ 2 * Cα.m + 6
namespace Stretch
variable {M : Model} {Cα : Chain} {g g' L : ℕ}
theorem nα (Cα : Chain) : (chainModel Cα).W.n = 2 * Cα.m + 7 := Cα.sideWalk_n _
theorem mod' (hS : Stretch M Cα g g' L) {d : ℕ} (hd : d ≤ L) :
    zthr % (chainModel Cα).W.n = g' + d :=
  Nat.mod_eq_of_lt (by zupav; have := hS.hgL; omega)

/-- The points of `Cα`'s walk inside the stretch lie on `Cα`. -/
theorem memα (hS : Stretch M Cα g g' L) {d : ℕ} (hd : d < L) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) : sidePt (chainModel Cα).W zthr t ∈ Cα.set := by
  have h := Cα.sideWalk_tour_pt_mem Cα.sideBeta (i := g' + d - 6) (t := t)
    (by have := hS.hgL; omega) (fun h => by exfalso; have := hS.hgL; have := hS.h6; omega) ht0 ht1
  rw [show g' + d - 6 + 6 = g' + d by have := hS.h6; omega] at h
  zubh

/-- The points of `M`'s walk inside the stretch lie on `Cα`. -/
theorem memM (hS : Stretch M Cα g g' L) {d : ℕ} (hd : d < L) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) : sidePt M.W ztwje t ∈ Cα.set := by
  rw [hS.hA.sidePt_eq hd, hS.mod' hd.le]
  exact hS.memα hd ht0 ht1
theorem rayPt_inj {a : Point} {σ s s' : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : rayPt a σ s = rayPt a σ s') : s = s' := by
  zuftb
  zuimk
  grind

/-- **Arrival at the other end (M2' in offsets).** -/
theorem arrive (hS : Stretch M Cα g g' L) (hGα : WalkAx ztbdc) {c : Set Point}
    (hc : c ∈ (chainModel Cα).Adm) {pB : ℕ} {tB : ℝ} (hB : SideAttach (chainModel Cα).W c pB tB)
    {a : Point} (haC : a ∈ Cα.set) {σ L₀ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hL₀ : 0 < L₀)
    (hceq : c = Chazelle.segment a zthzm)
    (hoB : rayPt a σ L₀ = sidePt (chainModel Cα).W pB tB)
    (hkopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a zthzm s ∈ Cα.dom)
    (hsetD : ∀ x ∈ Cα.set, x ∉ M.D) {T : ℝ} (hT : 0 < T)
    (hdom : ∀ s, 0 < s → s < T → rayPt a σ s ∈ M.D) {d : ℕ} {t : ℝ} (hd : d < L)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hdt : t = 0 → 1 ≤ d)
    (hfar : sidePt M.W ztwje t = rayPt a σ T)
    (hFA : SideAttach M.W ztrnj ztwje t) :
    pB = g' + d ∧ tB = t := by
  set o := rayPt a σ L₀ with ho
  have hoD : o ∉ Cα.dom := by
    rw [hoB]; exact hGα.trace _ hB.1 _ hB.2.1 hB.2.2.1.le
  have hoy : o.2 = a.2 := by_rfl
  have hdir : 0 < σ * ztodv := by
    rw [ho, rayPt_fst]; grind
  have hfarC : rayPt a σ T ∈ Cα.set := by rw [← hfar]; exact hS.memM hd ht0 ht1
  have harr := arrive_other hsetD hoy haC hkopen hoD hσ hdir hT hdom hfarC
  have hTL : T = L₀ := rayPt_inj hσ harr
  subst hTL
  have hch : chordOf a σ T = c := by rw [chordOf_eq_segment hσ hT, hceq]
  rw [hch] at hFA
  zucmg
  have hnα : 0 < (chainModel Cα).W.n := by zupav; omega
  have hAα := (hS.hA.sideAttach_iff hn hnα hd hdt c).1 hFA
  rw [hS.mod' hd.le] at hAα
  have heq : sidePt (chainModel Cα).W zthr t = sidePt (chainModel Cα).W pB tB := by
    rw [← hS.mod' hd.le, ← hS.hA.sidePt_eq hd, hfar, harr, hoB]
  obtain ⟨h1, h2⟩ := attach_unique hGα hc hAα hB heq
  grind
end Stretch
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft sideInArc)
theorem lt_after (a k : ℝ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (a < k + ε ↔ a ≤ k) := by
  by_cases h : a ≤ k
  · zulg
    grind
  · zubpo
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < a - k by linarith)] with ε hε
    grind
theorem after_lt (b k : ℝ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (k + ε < b ↔ k < b) := by
  by_cases h : k < b
  · filter_upwards [Ioo_mem_nhdsGT ztecr] with ε hε
    grind
  · zubpo
    zulg
    grind

/-- **The side just after a key.** -/
theorem side_after {a b : ℝ} (hab : a ≠ b) (k : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (sideInArc a b zthig ↔ (k = a ∨ sideInArc a b k)) := by
  filter_upwards [lt_after a k, after_lt b k] with ε h1 h2
  zuiq

/-- Just after its start, a key interval contains the keys. -/
theorem after_start (a b : ℝ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc a b (a + ε) := by
  zufqx
  · zumqb
    zulg
    have : ztfzo := hε
    zuxb
  · filter_upwards [side_after hab a] with ε h
    simp_all

/-- **The side of the good vertex** after a failed test at `a`, from `prune`. -/
theorem end_side {ka kf kx aj bj : ℝ} (hakf : ka ≠ kf)
    (hpr : ∀ y, sideInArc aj bj y → (sideInArc ka kf kx ↔ sideInArc ka kf y)) :
    sideInArc ka kf kx ↔ (aj = ka ∨ sideInArc ka kf aj) := by
  obtain ⟨ε, h1, h2⟩ := ((after_start aj bj).and (side_after hakf aj)).exists
  grind

/-- **The side of the good vertex after a failed test**, in the terms of `prune`. -/
theorem prune_side {M : Model} (hM : WalkAx M) {S : Set ztf} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) (hne : S.Nonempty) {R : Set Point} {ai bi aj bj : ℝ}
    (hAi : M.IsArc S R ai bi) (hAj : M.IsArc S R aj bj) (hij : ai ≠ aj)
    {ea : Set Point} (hea : ea ∈ M.Adm) {pa pa' : ℕ} {ta ta' : ℝ}
    (hA : SideAttach M.W ea pa ta) (hA' : SideAttach M.W ea pa' ta')
    (hAA' : sidePt M.W pa ta ≠ sidePt M.W pa' ta') (hka : sideInArc ai bi ztbf)
    {ex : Set Point} (hex : ex ∈ M.Adm) {px px' : ℕ} {tx tx' : ℝ}
    (hX : SideAttach M.W ex px tx) (hX' : SideAttach M.W ex px' tx')
    (hXX' : sidePt M.W px tx ≠ sidePt M.W px' tx') (hkx : ClosedArc ai bi ztcat)
    (hkx' : ClosedArc aj bj ztdvt)
    (hgood : CountOK M S R ztcat ztdvt) (hbad : ¬ CountOK M S R ztbf ztdhw)
    (hxa : (px : ℝ) + tx ≠ pa + ta) (hxa' : (px : ℝ) + tx ≠ pa' + ta') :
    sideInArc ztbf ztdhw ztcat ↔
      (aj = pa + ta ∨ sideInArc ztbf ztdhw aj) :=
  end_side (WalkAx.key_ne_of_pt_ne hA hA' hAA') (prune hM hS hfin hne hAi hAj hij hea hA hA' hAA' hka
    hex hX hX' hXX' hkx hkx' hgood hbad hxa hxa').2
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp)
open WalkEmbed (off off_nonneg off_key off_key' dOf dOf_lt add_dOf)
variable {M : Model} {Cα : Chain} {g g' L : ℕ}

/-- **The arrival offset** of the test at an end of a node chord. -/
theorem arrival_off (hS : Stretch M Cα g g' L) (hGα : WalkAx ztbdc) {c : Set Point}
    (hc : c ∈ (chainModel Cα).Adm) {pO : ℕ} {tO : ℝ}
    (hO : SideAttach (chainModel Cα).W c pO tO)
    {a : Point} (haC : a ∈ Cα.set) {σ L₀ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hL₀ : 0 < L₀)
    (hceq : c = Chazelle.segment a zthzm)
    (hoO : rayPt a σ L₀ = sidePt (chainModel Cα).W pO tO)
    (hkopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a zthzm s ∈ Cα.dom)
    (hsetD : ∀ x ∈ Cα.set, x ∉ M.D) {T : ℝ} (hT : 0 < T)
    (hdom : ∀ s, 0 < s → s < T → rayPt a σ s ∈ M.D) {pF : ℕ} {tF : ℝ}
    (hfar : sidePt M.W pF tF = rayPt a σ T) (hFA : SideAttach M.W ztrnj pF tF) :
    0 ≤ off M.W.n g ztbud ∧
      (0 < off M.W.n g ztbud → off M.W.n g ztbud < L →
        off M.W.n g ztbud = off (chainModel Cα).W.n g' ztkcd) := by
  zucmg
  have hg : ztehn := by exact_mod_cast hS.hg
  have hFA' := hFA
  obtain ⟨hpF, htF0, htF1, -⟩ := hFA'
  have hk0 : (0 : ℝ) ≤ pF + tF := by_positivity
  refine ⟨off_nonneg hk0 hg, fun h0 hL => ?_⟩
  set d := dOf M.W.n g pF with hd
  have he : off M.W.n g ztbud = d + tF := off_key' hS.hg hpF htF0 htF1
  zvmxm at h0 hL ⊢
  have hdL : d < L := by
    zulgs
    simp_all
  have hdt : tF = 0 → 1 ≤ d := fun h => by
    rw [h, add_zero] at h0
    have : ztiwt := h0
    zufc
  have hpF' : pF = ztbe % M.W.n := (add_dOf hS.hg hpF).symm
  rw [hpF'] at hfar
  obtain ⟨hpO, htO⟩ := hS.arrive hGα hc hO haC hσ hL₀ hceq hoO hkopen hsetD hT hdom hdL htF0
    htF1 hdt hfar by_grind
  have hg' : ztpov := by zunks; have := hS.hgL; omega
  have hdα : d < (chainModel Cα).W.n := by zunks; have := hS.hgL; omega
  rw [hpO, htO, ← hS.mod' hdL.le, off_key hg' hdα htF0 htF1]
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Chazelle.Chain (sidePt SideAttach sideInArc)
open WalkEmbed (off off_nonneg off_key off_key' dOf dOf_lt add_dOf)
variable {M : Model} {Cα : Chain} {g g' L : ℕ}

/-- **An end is strictly inside the stretch** iff its rotated key is in `(0, L)`. -/
theorem inE_iff (hS : Stretch M Cα g g' L) {p : ℕ} (hp : p < (chainModel Cα).W.n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (g' ≤ p ∧ p < g' + L ∧ (g' < p ∨ 0 < t)) ↔
      (0 < off (chainModel Cα).W.n g' ztk ∧ off (chainModel Cα).W.n g' ztk < L) := by
  zuerw
  have hg' : ztpov := by rw [hnα]; have := hS.hgL; omega
  rw [off_key' hg' hp ht0 ht1]
  zujqj
  zuiyc
  by_cases hge : g' ≤ p
  · have e : ztlrp % (chainModel Cα).W.n = p - g' := by
      rw [show p + (chainModel Cα).W.n - g' = zttvf + (chainModel Cα).W.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
    zui
    have hc : ((p - g' : ℕ) : ℝ) = (p : ℝ) - g' := by_simp_all
    constructor
    · rintro ⟨-, h2, h3⟩
      zujx
      · zujh
        · have : (1 : ℝ) ≤ ((p - g' : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ p - g' by omega)
          linarith
        grind
      · have : ((p - g' : ℕ) : ℝ) + 1 ≤ L := by exact_mod_cast (show p - g' + 1 ≤ L by omega)
        linarith
    · zubf
      refine ⟨hge, ?_, ?_⟩
      · by_contra hc'
        have : (L : ℝ) ≤ ((p - g' : ℕ) : ℝ) := by exact_mod_cast (show L ≤ p - g' by omega)
        linarith
      grind
  · zugrh
    have e : ztlrp % (chainModel Cα).W.n =
        p + (chainModel Cα).W.n - g' := Nat.mod_eq_of_lt by_omega
    zui
    constructor
    · omega
    · rintro ⟨-, h2⟩
      exfalso
      have : (L : ℝ) ≤ ((p + (chainModel Cα).W.n - g' : ℕ) : ℝ) := by
        exact_mod_cast (show L ≤ p + (chainModel Cα).W.n - g' by rw [hnα]; omega)
      linarith

/-- The parameter of a vertex position is `0`. -/
theorem key_vtx (M : Model) (Q : Polygon) (p : ℕ) : M.key Q ztcye = p := by
  simp

/-- The comparison of `(p, 0)` and `(p, h)` tells whether the parameter is positive. -/
theorem key_pz (M : Model) (Q : Polygon) (p h : ℕ) :
    M.key Q ztcye < M.key Q ztnk ↔ 0 < M.param Q ztnk := by
  rw [key_vtx]
  show (p : ℝ) < p + M.param Q ztnk ↔ _
  simp

/-- **The host position of an end** has the parameter of the end. -/
theorem endM_param (hS : Stretch M Cα g g' L) {Q : Polygon} {d : ℕ} (hd : d < L) (h : ℕ) :
    M.param Q ztwvk = (chainModel Cα).param Q ztrcm := by
  rw [param_agree hS.hA hd h, hS.mod' hd.le]
theorem endM_pos (hS : Stretch M Cα g g' L) {Q : Polygon} {d : ℕ} (hd : d < L) (h : ℕ) :
    M.pos Q ztwvk = (chainModel Cα).pos Q ztrcm := by
  rw [pos_agree hS.hA hd h, hS.mod' hd.le]

/-- **The host offset of an end** is its rotated key. -/
theorem endM_off (hS : Stretch M Cα g g' L) {d : ℕ} (hd : d < L) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) : off M.W.n g ztwjt = d + t :=
  off_key hS.hg (by have := hS.hLn; omega) ht0 ht1
theorem endα_off (hS : Stretch M Cα g g' L) {d : ℕ} (hd : d < L) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) : off (chainModel Cα).W.n g' (((g' + d : ℕ) : ℝ) + t) = d + t := by
  have h := off_key (n := (chainModel Cα).W.n) (g := g') (d := d)
    (by zunks; have := hS.hgL; omega) (by zunks; have := hS.hgL; omega) ht0 ht1
  rwa [hS.mod' hd.le] at h
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Chazelle.Chain (sidePt SideAttach sideInArc)
variable {E : FEnv} {c₀ : Config} {Cα : Chain} {g g' L : ℕ}
theorem pos_of_param {M : Model} {Q : Polygon} {e a b : ℕ} (h : M.param Q ztoni = M.param Q ztonj) :
    M.pos Q ztoni = M.pos Q ztonj := by
  show Geometry.lerp ztmbq ztmbr (M.param Q ztoni) =
    Geometry.lerp ztmbq ztmbr (M.param Q ztonj)
  zuzx

/-- **The candidate at a node chord end.** -/
theorem end_cand (hE : FGood E c₀) (hS : Stretch E.M Cα g g' L) {c : Set Point} {h : ℕ} {d : ℕ}
    (hd : d < L) (hpe : PosOK Cα zti E.P.n ztbfm)
    (hA : SideAttach (chainModel Cα).W c zthr ((chainModel Cα).param zti ztbfm))
    (hc : ∀ z ∈ c, z.2 = ((Qof E.P).vtx h).2)
    (hr : InRange c₀ ztxlk) {σb : ℕ} (hσb : σb ≤ 1) :
    CandOK E ztwmo h σb := by
  set t := (chainModel Cα).param zti ztbfm with ht
  obtain ⟨-, ⟨ht0, ht1, hhn⟩, -⟩ := hpe
  zucmh
  -- the parameter and the point
  have hpar : E.M.param zti ztwmo = t ∧
      E.M.pos zti ztwmo =
        (chainModel Cα).pos zti ztbfm := by
    zuecw

    · simp_all
    · have h0 : ztbhh := by
        zuilh
      have e : (chainModel Cα).param zti ztrcl =
          (chainModel Cα).param zti ztbfm := by
        simp_all
      exact ztmqd
  obtain ⟨hp, hpos⟩ := hpar
  have hy : ((Qof E.P).vtx h).2 = (E.M.pos zti
      ⟨ztbe % E.M.W.n, endCode Cα zti zthr ztgn⟩).2 := by
    rw [hpos, pos_eq_sidePt]
    exact (hc _ hA.2.2.2.1).symm
  have hcode : endCode Cα zti zthr ztgn ≤ E.P.n := by
    unfold endCode; grind
  have hpp : ProperPos E.M zti E.P.n
      ⟨ztbe % E.M.W.n, endCode Cα zti zthr ztgn⟩ :=
    ⟨by_simp_all, by_simp_all, hcode⟩
  refine ⟨Nat.mod_lt _ hn, hpp, ?_, fun C hM => ?_, by_simp_all, hy, hσb⟩
  · zumel
    unfold endCode at hp' ⊢
    split_ifs at hp' ⊢ with hk
    · right; rw [hp']; rw [key_pz] at hk; exact hk
    simp
  · exact hE.ehr _ _ zthp hr.1 hr.2 hpp C hM
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft sideInArc)
theorem after_ne (k a : ℝ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), k + ε ≠ a := by
  filter_upwards [lt_after a k, after_lt a k, self_mem_nhdsWithin] with ε h1 h2 h3 h
  simp_all
theorem small_lt (b : ℝ) (hb : 0 < b) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < b := by
  filter_upwards [Ioo_mem_nhdsGT hb] with ε hε using hε.2

/-- **The child of a node on the side of the target.** -/
theorem child_side {M : Model} {Q : Polygon} {N : NF} {reg : ℕ → Set Point} {D : ℕ}
    (hGM : GoodModel M) (hN : IsNF M Q N) (hT : Dec.RecTree N D) (hregs : NFRegs M Q N reg)
    {k : ℕ} (hk : k < N.nChords) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W ztbpa pa ta)
    (hB : SideAttach M.W ztbpa pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    {r : ℕ} (hr : r < N.nRegions) {p : ℕ} (hp : p < M.W.n)
    (hf : ∀ᶠ ε in 𝓝[>] (0 : ℝ), M.Faces p ε ztcz)
    (hpa : (p : ℝ) ≠ pa + ta) (_hpb : (p : ℝ) ≠ pb + tb)
    {j : ℕ} (hj : j < N.arcs.length) (hjr : (N.arc j).reg = (N.chord k).dn) :
    ((sideInArc ztbf ztbd p ↔
        ztxif) →
      r ∈ N.lowSide k) ∧
    (¬ (sideInArc ztbf ztbd p ↔
        ztxif) →
      r ∈ N.highSide k) := by
  zubm
  set ka : ℝ := pa + ta
  set kb : ℝ := pb + tb
  have hab : ka ≠ kb := WalkAx.key_ne_of_pt_ne hA hB hAB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hprop⟩ := id hN
  obtain ⟨hτ0, hτ1, -⟩ := (hprop j hj).1
  have harc := (hregs.2.2.1.1 j hj).2
  zugdy
  set s := (N.arc j).s with hs
  set τ := M.param Q s with hτ
  have hks : M.key Q s = s.edge + τ := rfl
  zukzq
  set ke := M.key Q (N.arc j).e
  obtain ⟨ε, hε⟩ := (hf.and ((side_after hab p).and ((side_after hab ks).and
    ((after_start ks ke).and ((after_ne p ka).and ((after_ne p kb).and ((after_ne ks ka).and
      ((after_ne ks kb).and ((small_lt 1 one_pos).and ((small_lt ztcsf by_linarith).and
        self_mem_nhdsWithin)))))))))).exists
  obtain ⟨hfp, hsp, hss, hst, n1, n2, n3, n4, hε1, hετ, hε0⟩ := hε
  have hε0' : ztfzo := hε0
  have hsedge : s.edge < M.W.n := by
    obtain ⟨-, h, -⟩ := harc
    have := hτ0
    have h' : (s.edge : ℝ) < M.W.n := by
      grind
    simp_all
  have hf₀ : M.Faces s.edge ztufj ztpdm :=
    harc.2.2.2.2.2.2 s.edge ztufj hsedge by_linarith by_linarith
      by_grind
  have hd := decide_side hGM hN hT hregs.1 hregs.2.1 hk hA hB hAB hr hp hε0' hε1 hfp hsedge
    by_linarith by_linarith hf₀
  have sw : ∀ v, v ≠ ka → v ≠ kb → (sideInArc kb ka v ↔ ¬ sideInArc ka kb v) := fun v h1 h2 =>
    Chazelle.Chain.sideInArc_swap ztmbt h2 h1
  grind
open WalkEmbed (tpos tourV)

/-- **The stretches of a kind-1 piece.** -/
theorem piece_stretches {M : Model} {Cα : Chain} {p₀ J : ℕ} (hp₀ : p₀ < M.W.n)
    (hmn : Cα.m < M.W.n)
    (hV : ∀ d, d ≤ Cα.m → M.W.vtx ztzzr = tourV Cα J d) :
    (tpos Cα J + Cα.m ≤ 2 * Cα.m → Stretch M Cα p₀ ztpuw Cα.m) ∧
    (2 * Cα.m < tpos Cα J + Cα.m →
      Stretch M Cα p₀ ztpuw ztbxs ∧
      Stretch M Cα (ztzxw % M.W.n) 6 (Cα.m - ztbxs)) := by
  zudxx

  refine ⟨fun hs => ⟨fun d hd => ?_, hp₀, h1, hmn, by_omega, by_omega⟩, fun hs => ⟨⟨fun d hd => ?_,
    hp₀, by_omega, by_omega, by_omega, by_omega⟩, ⟨fun d hd => ?_, Nat.mod_lt _ by_omega,
    by omega, by_omega, le_rfl, by_omega⟩⟩⟩
  · zufng
  · zufnf
  · have e1 : (ztzxw % M.W.n + d) % M.W.n =
        (p₀ + (ztbxs + d)) % M.W.n := by
      grind
    have e2 : ztfmw % (chainModel Cα).W.n =
        (6 + tpos Cα J + ztbxs + 7 + d) % (chainModel Cα).W.n := by
      rw [hn', show 6 + tpos Cα J + ztbxs + 7 + d =
        ztfmw + ztgb by omega, Nat.add_mod_right]
    zudtr

/-- **The direction test**: the height vertex `h` of the piece's first vertex is the chain's first
vertex iff the walk goes up the chain. -/
theorem dir_correct {M : Model} {Q : Polygon} (hDH : DistinctHeights Q) {Cα : Chain}
    (hQ : Cα.P = Q) {s h : ℕ} (hh : h < Q.n) (hsP : Cα.s < Q.n) (hsn : s < M.W.n)
    (hy : (Q.vtx h).2 = (M.W.vtx s).2)
    (hdir : (∀ d, d ≤ Cα.m → M.W.vtx ztxys = Cα.vertex d) ∨
      (∀ d, d ≤ Cα.m → M.W.vtx ztxys = Cα.vertex ztclf)) :
    ∀ d, d ≤ Cα.m → M.W.vtx ztxys = tourV Cα (if h = Cα.s then 0 else Cα.m) d := by
  zumax
  have hmn := Cα.add_one_le
  zvnao at hmn
  have v0 : Cα.vertex 0 = Q.vtx Cα.s := by
    unfold Chain.vertex Chain.edgeIdx; rw [hQ, Nat.add_zero, Nat.mod_eq_of_lt hsP]
  have vm : Cα.vertex Cα.m = Q.vtx (ztjhs % Q.n) := by
    unfold Chain.vertex Chain.edgeIdx; zvnao
  have hs0 : zttzc % M.W.n = s := by rw [Nat.add_zero, Nat.mod_eq_of_lt hsn]
  zufzv
  · have e := hu 0 ztbg
    rw [hs0, v0] at e
    have hhs : h = Cα.s := by
      by_contra hne; exact hDH h Cα.s hh hsP hne by_simp_all
    rw [ite_eq_left hhs]
    intro d hd'; rw [hu d hd', ShootCut.tourV_up Cα hd']
  · have e := hd 0 ztbg
    rw [hs0, Nat.sub_zero, vm] at e
    have hlt := Nat.mod_lt ztjhs (by omega : 0 < Q.n)
    have hne : ztjhs % Q.n ≠ Cα.s := by
      zuhgj
      by_cases hc : Cα.s + Cα.m < Q.n
      · rw [Nat.mod_eq_of_lt hc] at h'; omega
      · zvnae at h'; omega
    have hhs : h = ztjhs % Q.n := by
      by_contra hne'; exact hDH h _ hh hlt hne' by_simp_all
    zufa
    intro d hd'; rw [hd d hd', ShootCut.tourV_down Cα hd']
def GEnd (L d α : ℝ) (s : Prop) (v : ℝ) : Prop := (0 < d ∧ d < L) → (sideInArc d α v ↔ s)

/-- An offset passing both end tests. -/
def WOK (L da db αa αb : ℝ) (sa sb : Prop) (v : ℝ) : Prop :=
  0 < v ∧ v < L ∧ v ≠ da ∧ v ≠ db ∧ GEnd L da αa sa v ∧ GEnd L db αb sb v

/-- Without an end of the interval in `[u, x]`, the side is the same at `u` and `x`. -/
theorem side_same {a b u x : ℝ} (hux : u ≤ x) (ha : a < u ∨ x < a) (hb : b < u ∨ x < b) :
    sideInArc a b u ↔ sideInArc a b x := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> unfold sideInArc <;>
    split_ifs with h <;> constructor <;> intro h' <;>
    first
    | (left; linarith)
    | (right; linarith)
    | (exact ⟨by_linarith, by_linarith⟩)
    | (exfalso; rcases h' with h' | h' <;> linarith)
variable {L da db αa αb : ℝ} {sa sb : Prop}
theorem gend_transfer {d d' α : ℝ} {s : Prop} (hα0 : 0 ≤ α) (hα : 0 < α → α < L → α = d')
    {ℓ u x : ℝ} (hℓ : 0 ≤ ℓ) (hℓu : ℓ < u) (hux : u ≤ x) (hxL : x < L)
    (hd : ¬ (ℓ < d ∧ d ≤ x)) (hd' : ¬ (ℓ < d' ∧ d' ≤ x)) (hx : GEnd L d α s x) :
    GEnd L d α s u := by
  intro hdL
  refine (side_same hux ?_ ?_).trans (hx hdL)
  · grind
  grind

/-- **Transfer of the test conditions** from `x` to an offset `u ≤ x` with no end in
`(ℓ, x]`. -/
theorem wok_transfer (hαa0 : 0 ≤ αa) (hαa : 0 < αa → αa < L → αa = db) (hαb0 : 0 ≤ αb)
    (hαb : 0 < αb → αb < L → αb = da) {ℓ u x : ℝ} (hℓ : 0 ≤ ℓ) (hℓu : ℓ < u) (hux : u ≤ x)
    (hda : ¬ (ℓ < da ∧ da ≤ x)) (hdb : ¬ (ℓ < db ∧ db ≤ x))
    (hx : WOK L da db αa αb sa sb x) : WOK L da db αa αb sa sb u := by
  obtain ⟨hx0, hxL, -, -, ga, gb⟩ := hx
  refine ⟨by_linarith, by_linarith, fun h => hda ztkjb,
    fun h => hdb ztkjb,
    gend_transfer hαa0 hαa hℓ hℓu hux hxL hda hdb ga,
    gend_transfer hαb0 hαb hℓ hℓu hux hxL hdb hda gb⟩

/-- **A witness offset exists among `1`, `⌊da⌋ + 1`, `⌊db⌋ + 1`.** -/
theorem witness_exists (hαa0 : 0 ≤ αa) (hαa : 0 < αa → αa < L → αa = db) (hαb0 : 0 ≤ αb)
    (hαb : 0 < αb → αb < L → αb = da) (hda0 : 0 ≤ da) (hdb0 : 0 ≤ db) {x : ℕ}
    (hx : WOK L da db αa αb sa sb x) :
    WOK L da db αa αb sa sb 1 ∨ (0 < da ∧ da < L ∧ WOK L da db αa αb sa sb (⌊da⌋₊ + 1 : ℕ)) ∨
      (0 < db ∧ db < L ∧ WOK L da db αa αb sa sb (⌊db⌋₊ + 1 : ℕ)) := by
  obtain ⟨hx0, hxL, hxa, hxb, ga, gb⟩ := hx
  have hx1 : (1 : ℝ) ≤ x := by
    have : ztrzq := by_simp_all
    zufc
  have fl : ∀ d : ℝ, 0 ≤ d → d < x → (d < ((⌊d⌋₊ + 1 : ℕ) : ℝ) ∧ ((⌊d⌋₊ + 1 : ℕ) : ℝ) ≤ x) :=
    fun d hd hdx => by
      refine ⟨by push_cast; exact Nat.lt_floor_add_one d, ?_⟩
      have : ⌊d⌋₊ < x := (Nat.floor_lt hd).2 hdx
      zufc
  by_cases hA : 0 < da ∧ da < x
  · by_cases hB : 0 < db ∧ db < x ∧ da < db
    · obtain ⟨h1, h2⟩ := fl db hdb0 hB.2.1
      exact Or.inr (Or.inr ⟨hB.1, by_linarith, wok_transfer hαa0 hαa hαb0 hαb hdb0 h1 h2
        ztbay ztrpx ⟨hx0, hxL, hxa, hxb,
          ga, gb⟩⟩)
    · obtain ⟨h1, h2⟩ := fl da hda0 hA.2
      refine Or.inr (Or.inl ⟨hA.1, by_linarith, wok_transfer hαa0 hαa hαb0 hαb hda0 h1 h2
        ztbay ztep zteym⟩)
      grind
  · by_cases hB : 0 < db ∧ db < x
    · obtain ⟨h1, h2⟩ := fl db hdb0 hB.2
      refine Or.inr (Or.inr ⟨hB.1, by_linarith, wok_transfer hαa0 hαa hαb0 hαb hdb0 h1 h2
        ztep ztbay zteym⟩)
      grind
    · refine Or.inl (wok_transfer hαa0 hαa hαb0 hαb le_rfl zero_lt_one hx1 ztep
        ztep zteym)
      · grind
      grind

/-- **Every passing offset is on the side of the good vertex.** -/
theorem witness_side_ok (hαa0 : 0 ≤ αa) (hαa : 0 < αa → αa < L → αa = db) (hαb0 : 0 ≤ αb)
    (hαb : 0 < αb → αb < L → αb = da) (hda0 : 0 ≤ da) (hdb0 : 0 ≤ db) (hne : da ≠ db)
    {u x : ℝ} (hu : WOK L da db αa αb sa sb u) (hx : WOK L da db αa αb sa sb x) :
    sideInArc da db u ↔ sideInArc da db x := by
  obtain ⟨hu0, huL, hua, hub, gau, gbu⟩ := hu
  obtain ⟨hx0, hxL, hxa, hxb, gax, gbx⟩ := hx
  exact stretch_side hda0 hdb0 hne (GA := GEnd L da αa sa) (GB := GEnd L db αb sb)
    (fun h1 h2 => ⟨αa, sa, hαa0, hαa, fun v => ztxzo⟩)
    (fun h1 h2 => ⟨αb, sb, hαb0, hαb, fun v => ztxzo⟩)
    hu0 huL hx0 hxL hua hub hxa hxb gau gax gbu gbx
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set
open Chazelle.Chain (sidePt SideAttach sideLeft sideInArc)
open Chazelle.Visibility (rayPt)
open Chazelle.Geometry (lerp)
open WalkEmbed (off off_nonneg off_lt off_key off_key')
variable {M : Model} {Cα : Chain} {g g' L : ℕ}

/-- Rotation of a host-key interval test at an integer offset of the stretch. -/
theorem rot_u (hS : Stretch M Cα g g' L) {a b : ℝ} (ha0 : 0 ≤ a) (han : a < M.W.n) (hb0 : 0 ≤ b)
    (hbn : b < M.W.n) {u : ℕ} (hu : u < L) :
    sideInArc a b ((ztesw % M.W.n : ℕ) : ℝ) ↔
      sideInArc (off M.W.n g a) (off M.W.n g b) (u : ℝ) := by
  zucmg
  zuiya
  have hgn : ztehn := by exact_mod_cast hS.hg
  have hx0 : (0 : ℝ) ≤ ((ztesw % M.W.n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hxn : ((ztesw % M.W.n : ℕ) : ℝ) < M.W.n := by exact_mod_cast Nat.mod_lt _ hn
  zufoi
  have h := off_key (n := M.W.n) (g := g) (d := u) hS.hg (by have := hS.hLn; omega)
    (t := 0) le_rfl zero_lt_one
  simp_all
theorem ray_ne' {z : Point} {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T) : z ≠ rayPt z σ T := by
  zuq
  have := congrArg Prod.fst h
  rw [Chazelle.Visibility.rayPt_fst] at this
  zubbe

/-- **A failed end test, in offsets.** -/
theorem end_gend (hS : Stretch M Cα g g' L) (hGα : WalkAx ztbdc) (hM : WalkAx M)
    {S : Set ztf} (hSA : S ⊆ M.Adm) (hfin : S.Finite) (hne : S.Nonempty)
    {R : Set Point} {ai bi aj bj : ℝ} (hAi : M.IsArc S R ai bi) (hAj : M.IsArc S R aj bj)
    (hij : ai ≠ aj)
    -- the node chord and its other end in the piece chain's walk
    {c : Set Point} (hc : c ∈ (chainModel Cα).Adm) {pO : ℕ} {tO : ℝ}
    (hO : SideAttach (chainModel Cα).W c pO tO)
    -- the end, at offset `d + t` of the stretch
    {d : ℕ} (hd : d < L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (_hdt : 0 < (d : ℝ) + t)
    {σ L₀ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hL₀ : 0 < L₀)
    (hceq : c = Chazelle.segment ztbajo
      (rayPt ztbajo σ L₀))
    (hoO : rayPt ztbajo σ L₀ = sidePt (chainModel Cα).W pO tO)
    (hkopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp ztbajo
      (rayPt ztbajo σ L₀) s ∈ Cα.dom)
    (hsetD : ∀ x ∈ Cα.set, x ∉ M.D)
    -- the test
    {T : ℝ} (hT : 0 < T)
    (hdom : ∀ s, 0 < s → s < T → rayPt ztbajo σ s ∈ M.D)
    {pF : ℕ} {tF : ℝ}
    (hfar : sidePt M.W pF tF = rayPt ztbajo σ T)
    (hea : chordOf ztbajo σ T ∈ M.Adm)
    (hEA : SideAttach M.W (chordOf ztbajo σ T) ztwje t)
    (hFA : SideAttach M.W (chordOf ztbajo σ T) pF tF)
    (hka : sideInArc ai bi ztwjt)
    (hbad : ¬ CountOK M S R ztwjt ztbud)
    -- the good vertex at offset `x`
    {ex : Set Point} (hex : ex ∈ M.Adm) {x : ℕ} (hx : x < L) {px' : ℕ} {tx' : ℝ}
    (hX : SideAttach M.W ex ztzzu 0) (hX' : SideAttach M.W ex px' tx')
    (hXX' : sidePt M.W ztzzu 0 ≠ sidePt M.W px' tx')
    (hkx : ClosedArc ai bi ztydi) (hkx' : ClosedArc aj bj ztdvt)
    (hgood : CountOK M S R ztydi ztdvt)
    (hxa : ((ztfrx % M.W.n : ℕ) : ℝ) + 0 ≠ (ztbe % M.W.n : ℕ) + t)
    (hxa' : ((ztfrx % M.W.n : ℕ) : ℝ) + 0 ≠ pF + tF) :
    0 ≤ off M.W.n g ztbud ∧
      (0 < off M.W.n g ztbud → off M.W.n g ztbud < L →
        off M.W.n g ztbud = off (chainModel Cα).W.n g' ztkcd) ∧
      (sideInArc zteiy ztznc (x : ℝ) ↔
        (aj = (ztbe % M.W.n : ℕ) + t ∨
          sideInArc ztwvo ztbud aj)) ∧
      ∀ u : ℕ, u < L →
        (sideInArc ztwvo ztbud ((ztesw % M.W.n : ℕ) : ℝ) ↔
          sideInArc zteiy ztznc (u : ℝ)) := by
  have haC : sidePt M.W ztwje t ∈ Cα.set := hS.memM hd ht0 ht1
  obtain ⟨h0, harr⟩ := arrival_off hS hGα hc hO haC hσ hL₀ hceq hoO hkopen hsetD hT hdom hfar hFA
  have hpr := prune_side hM hSA hfin hne hAi hAj hij hea hEA hFA
    (by rw [hfar]; exact ray_ne' hσ hT) hka hex hX hX' hXX' hkx hkx' hgood hbad hxa hxa'
  obtain ⟨hkE0, hkEn⟩ := key_range hEA
  obtain ⟨hkF0, hkFn⟩ := key_range hFA
  have hoE : off M.W.n g ztwvo = d + t := endM_off hS hd ht0 ht1
  refine ⟨h0, harr, ?_, fun u hu => ?_⟩
  · have hr := rot_u hS hkE0 hkEn hkF0 hkFn hx
    rw [hoE] at hr
    rw [← hr]
    zvncl at hpr
    omega
  · have hr := rot_u hS hkE0 hkEn hkF0 hkFn hu
    grind
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt Programs SignK WalkKey
open BuildRam (FrameM FrameM.mono FrameM.trans FrameB.toM)
@[expose] public section
def ptLoop : Stmt := .seq (.instr (.constN 212017 0)) (.whileLtN 212017 212016 ptS)
theorem flatMap_range_length_mono {α : Type*} (f : ℕ → List α) {m m' : ℕ} (h : m ≤ m') :
    ((List.range m).flatMap f).length ≤ ((List.range m').flatMap f).length := by
  induction m' with
  | zero => have : m = 0 := by_omega
            subst this; exact le_rfl
  | succ m' ih =>
    rcases Nat.lt_or_ge m (m' + 1) with h' | h'
    · rw [List.range_succ, List.flatMap_append, List.length_append]
      omega
    · grind
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **The points of a region**: its records are appended. -/
theorem ptLoop_exec {E : BEnv} (hE : BGood E) {r PA : ℕ} (hr : r < E.K + 1) (c : Config)
    {T : List ztwjg} (hS : PtSt E r PA c T)
    (hT : T.length + (E.recs r).length ≤ 2 * E.P.n) :
    ∃ c' k, Exec E.P E.W ptLoop c c' k ∧ k ≤ zthzg * (E.pts r).length + 3 ∧
      PtSt E r PA c' (T ++ (E.recs r).map fun x => ztcof) ∧ FrameM Bpt c c' ∧
      ztwta := by
  zujna
  set f := ptRecs E.li E.Q l with hf
  have hrecs : E.recs r = (List.range l.length).flatMap f := regList_eq_flatMap _ _ _
  -- the counter
  have e₀ := Exec.constN (P := E.P) hS.wb 212017 0 ztbg
  set c₀ : Config := { c with nreg := upd c.nreg 212017 0 } with hc₀
  have f₀ : FrameB ztfrt c c₀ := exec_frameB e₀ by_decide
  have S₀ : PtSt E r PA c₀ T := hS.regStep e₀.wb_right (fun q hq => f₀.1 q (by
    zubht
    · unfold FixP FixB at hq; grind
    grind)) f₀.2.2.1
  have FM₀ : FrameM Bpt c c₀ := (FrameB.toM f₀).mono fun q hq => by
    zufpq
  let Inv : ℕ → Config → Prop := fun j e => WordsBounded E.W e ∧ e.nreg 212017 = j ∧
    e.nreg 212016 = l.length ∧ PtSt E r PA e (T ++ ((List.range j).flatMap f).map fun x => ztcof) ∧
    FrameM Bpt c e ∧ (∀ a, ztbee → e.nmem a = c.nmem a)
  have I0 : Inv 0 c₀ := ⟨e₀.wb_right, by_rfl, S₀.np, by_simp_all, FM₀,
    fun a _ => by_rfl⟩
  obtain ⟨c', k, ex, ⟨-, -, -, S', FM', M'⟩, hk⟩ := DrvR.forLoop (P := E.P) (W := E.W)
    (ir := 212017) (nr := 212016) (body := ptS) Inv (ptK E.Cm) l.length
    ztbko
    (fun j e hj ⟨hw, h1, h2, S, FM, M⟩ => by
      have hlen : (T ++ ((List.range j).flatMap f).map fun x => ztcof).length +
          (f j).length ≤ 2 * E.P.n := by
        have := flatMap_range_length_mono f (show j + 1 ≤ l.length by omega)
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append]
          at this
        grind
      obtain ⟨e', k', x, hk', S', h17, FM'', M''⟩ := ptS_exec hE hr e S h1 by_omega hlen
      refine ⟨e', k', x, ⟨x.wb_right, h17, S'.np, ?_, FM.trans FM'', fun a ha => ?_⟩, hk'⟩
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.map_append,
          ← List.append_assoc]
        exact S'
      simp_all)
    I0 ztbg
  rw [Nat.sub_zero] at hk
  refine ⟨c', _, .seq e₀ ex, by_omega, ?_, FM', M'⟩
  simp_all
end exec
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt Programs SignK WalkKey
open BuildRam (FrameM FrameM.mono FrameM.trans FrameB.toM)
@[expose] public section
def rdS : Stmt :=
  .seq (block [.subN 212032 216031 212002, .loadN 212034 212032, .addN 212032 212032 212000,
    .loadN 212033 212032, .addN 212033 212033 216016])
    (.ifLtN 212001 212012 .skip (.instr (.constN 212034 1)))

/-- The host of the whole walk (`K = 0`). -/
def host0 : Stmt :=
  block [.copyN 212022 9999, .addN 9999 9999 212000, .addN 9999 9999 212000,
    .addN 9999 9999 212000, .addN 9999 9999 212000, .storeN 212022 212000,
    .addN 212032 212022 212000, .storeN 212032 212001, .addN 212032 212032 212000,
    .storeN 212032 212001, .addN 212032 212032 212000, .subN 212035 212010 212000,
    .storeN 212032 212035, .copyN 212016 212010, .copyN 212021 212000]

/-- `MX := max MX NP`. -/
def mxS : Stmt := .ifLtN 212018 212016 (.instr (.copyN 212018 212016)) .skip

/-- One step of the reservation of the point array. -/
def resPB : Stmt :=
  block [.addN 9999 9999 212000, .addN 9999 9999 212000, .addN 9999 9999 212000,
    .addN 212035 212035 212000]

/-- The reservation of the point array (`PA = r212015`, `3 NP` words). -/
def resPS : Stmt :=
  .seq (block [.copyN 212015 9999, .constN 212035 0]) (.whileLtN 212035 212016 resPB)

/-- The next region. -/
def incS : Stmt := block [.addN 212014 212014 212000, .addN 216031 216031 216006]
theorem host_len_le (n : ℕ) (H : Host) : H.length ≤ (H.pts n).length := by
  induction H with
  | nil => simp
  | cons it H ih =>
    have : 1 ≤ (it.pts n).length := by
      cases it with
      | run a l => zunjr
      | pt x => zunjr
    simp only [Host.pts, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    omega
section exec
variable {P : Polygon} {W : ℕ}
variable (c : Config)
set_option maxHeartbeats 2000000 in
/-- **The region record.** -/
theorem rdS_exec (hw : WordsBounded W c) {p LB K : ℕ}
    (h31 : c.nreg 216031 = p) (h16 : c.nreg 216016 = LB) (hK : c.nreg 212012 = K) (hp : 2 ≤ p)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) (c2 : c.nreg 212002 = 2)
    (hLB : LB + c.nmem ztoq ≤ W) :
    ∃ c' k, Exec P W rdS c c' k ∧ k ≤ 8 ∧
      c'.nreg 212034 = (if K = 0 then 1 else c.nmem ztftr) ∧
      c'.nreg 212033 = LB + c.nmem ztoq ∧
      FrameB (fun r => decide (212032 ≤ r ∧ r ≤ 212034)) c c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, v34, v33, g⟩ : ∃ c₁ k₁, Exec P W (block [.subN 212032 216031 212002,
      .loadN 212034 212032, .addN 212032 212032 212000, .loadN 212033 212032,
      .addN 212033 212033 216016]) c c₁ k₁ ∧ k₁ = 5 ∧ c₁.nreg 212034 = c.nmem (p - 2) ∧
      c₁.nreg 212033 = LB + c.nmem ztoq ∧ c₁.nreg 212001 = 0 ∧ c₁.nreg 212012 = K := by
    have hp1 : p - 2 + 1 = p - 1 := by_omega
    have hpW := hw.1 216031
    exec_block
    all_goals try (config_simp; simp only [h31, c2, c0, h16, hp1]; omega)
    refine ztboc <;> config_simp <;> simp only [h31, c2, c0, h16, c1, hK, hp1]
    · ring
  zud
  by_cases h0 : K = 0
  · have e₂ := Exec.constN (P := P) w₁ 212034 1 (by have := hw.1 212000; omega)
    have ex : Exec P W rdS c _ (k₁ + ztgxh) := .seq e₁ (.ifLtN_false by_simp_all e₂)
    refine zthmh
    simp_all
  · have ex : Exec P W rdS c c₁ (k₁ + ztbgo) :=
      .seq e₁ ztxdi
    exact ⟨c₁, _, ex, by_omega, by_simp_all, v33, exec_frameB ex by_decide⟩

/-- A frame of band `bDownDrv` from a register frame within the band and the allocator. -/
theorem frame21 {B : ℕ → Bool} {c c' : Config} {k : ℕ}
    (hB : ∀ r, B r = true → bandOf r = bDownDrv ∨ r = ALLOC) (hf : FrameM B c c')
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hrr : c'.rreg = c.rreg)
    (hA1 : c.nreg ALLOC ≤ c'.nreg ALLOC) (hA2 : c'.nreg ALLOC ≤ c.nreg ALLOC + k) :
    Frame {bDownDrv} c c' k := by
  refine ⟨fun r hr hra => hf.1 r ?_, fun r _ => by zvnhk, hm, fun a _ => by zuode,
    hf.2.2.2, hA1, hA2⟩
  grind
set_option maxHeartbeats 4000000 in
/-- **The host of the whole walk** (`K = 0`). -/
theorem host0_exec (hw : WordsBounded W c) {n : ℕ} (hn : c.nreg 212010 = n)
    (_hn1 : 1 ≤ n) (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0)
    (hA : c.nreg ALLOC + 4 ≤ W) :
    ∃ c' k, Exec P W host0 c c' k ∧ k = 15 ∧ c'.nreg 212022 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 4 ∧
      HostAt c'.nmem ztm [HostItem.run 0 ztkl] ∧
      c'.nreg 212016 = n ∧ c'.nreg 212021 = 1 ∧
      (∀ a, (a < c.nreg ALLOC ∨ c.nreg ALLOC + 4 ≤ a) → c'.nmem a = c.nmem a) ∧
      FrameM (fun r => decide (r = 212016 ∨ r = 212021 ∨ r = 212022 ∨ r = 212032 ∨
        r = 212035 ∨ r = 9999)) c c' ∧ Frame {bDownDrv} c c' k := by
  zudbg
  zufti
  obtain ⟨c', k, ex, hk, v22, vA, m0, m1, m2, m3, v16, v21, hm, hrr⟩ : ∃ c' k,
      Exec P W host0 c c' k ∧ k = 15 ∧ c'.nreg 212022 = A ∧ c'.nreg 9999 = A + 4 ∧
      c'.nmem A = 1 ∧ c'.nmem ztbo = 0 ∧ c'.nmem ztbcl = 0 ∧ c'.nmem zttf = n - 1 ∧
      c'.nreg 212016 = n ∧ c'.nreg 212021 = 1 ∧
      ztzt ∧ c'.rreg = c.rreg := by
    unfold host0
    exec_block
    all_goals try (config_simp; simp only [hA', c0, c1, hn]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, rfl⟩
    all_goals simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hA', c0, c1, hn]
  have FM : FrameM (fun r => decide (r = 212016 ∨ r = 212021 ∨ r = 212022 ∨ r = 212032 ∨
      r = 212035 ∨ r = 9999)) c c' := BuildRam.exec_frameM ex by_decide
  refine ⟨c', k, ex, hk, v22, vA, ⟨by_omega, fun i hi => ?_⟩, v16, v21, hm, FM,
    frame21 ztqob FM (fun a ha => hm a ztbbu) hrr (by show A ≤ c'.nreg 9999; omega)
      (by show c'.nreg 9999 ≤ A + k; omega)⟩
  · simp_all
  · zudcd
    rcases h with h | h | h | h | h | h <;> subst h
    · decide
    · decide
    · decide
    · decide
    · decide
    decide

/-- **`MX := max MX NP`.** -/
theorem mxS_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W mxS c c' k ∧ k ≤ 2 ∧
      c'.nreg 212018 = max ztvhy (c.nreg 212016) ∧
      FrameB (fun r => decide (r = 212018)) c c' := by
  by_cases h : c.nreg 212018 < c.nreg 212016
  · have e := Exec.copyN (P := P) hw 212018 212016
    have ex : Exec P W mxS c _ _ := .ifLtN_true h e
    refine ⟨_, _, ex, le_refl _, ?_, exec_frameB ex by_decide⟩
    zudbz
  · have ex : Exec P W mxS c c _ := .ifLtN_false h ztjd
    exact ⟨c, _, ex, le_refl _, by_omega, FrameB.refl _ _⟩
set_option maxHeartbeats 4000000 in
/-- **The reservation of the point array.** -/
theorem resPS_exec (hw : WordsBounded W c) {NP : ℕ} (h16 : c.nreg 212016 = NP)
    (c0 : c.nreg 212000 = 1) (hA : c.nreg ALLOC + 3 * NP ≤ W) :
    ∃ c' k, Exec P W resPS c c' k ∧ k ≤ 6 * NP + 4 ∧ c'.nreg 212015 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * NP ∧
      FrameB ztcvm c c' ∧
      Frame {bDownDrv} c c' k := by
  zudbg
  zufti
  obtain ⟨c₁, k₁, e₁, hk₁, v15, v35, g₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 212015 9999,
      .constN 212035 0]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 212015 = A ∧ c₁.nreg 212035 = 0 ∧
      ∀ r, r ≠ 212015 → r ≠ 212035 → c₁.nreg r = c.nreg r := by
    exec_block
    · omega
    simp_all
  have B₁ : FrameB ztcvm c c₁ :=
    exec_frameB e₁ by_decide
  have F₁ : ztpjy := frame21 (fun r h => by
      zudcd
      rcases h with h | h | h <;> subst h
      · decide
      · decide
      decide) (FrameB.toM B₁) (fun a _ => by rw [B₁.2.2.1])
    (funext fun r => WalkKey.exec_rframe e₁ (B := fun _ => false) by_decide r rfl)
    (by rw [g₁ _ by_decide by_decide]) by_grind
  let Inv : ℕ → Config → Prop := fun j e => WordsBounded W e ∧ e.nreg 212035 = j ∧
    e.nreg 212016 = NP ∧ e.nreg 9999 = A + 3 * j ∧
    FrameB ztcvm c e ∧ e.nreg 212015 = A
  have I0 : Inv 0 c₁ := ⟨e₁.wb_right, v35, by_simp_all,
    by simp_all, B₁, v15⟩
  obtain ⟨c', k, ex, ⟨w', j35, j16, jA, fr, j15⟩, hk, F⟩ := DrvG.forLoopF (P := P) (W := W)
    (ir := 212035) (nr := 212016) (body := resPB) (B := {bDownDrv}) Inv 4 NP
    ztbko
    (fun j e hj ⟨hw, h1, h2, h3, fr, h15⟩ => by
      have c0e : e.nreg 212000 = 1 := by rw [fr.1 _ by_decide, c0]
      obtain ⟨e', k', ex, hk', v35, vA⟩ : ∃ e' k', Exec P W resPB e e' k' ∧ k' = 4 ∧
          e'.nreg 212035 = j + 1 ∧ e'.nreg 9999 = A + 3 * ztl := by
        unfold resPB
        exec_block
        all_goals try (config_simp; zunva; omega)
        refine ztkw <;> config_simp <;> zunva; ring
      have fb : FrameB (fun r => decide (r = 212035 ∨ r = 9999)) e e' := exec_frameB ex by_decide
      refine ⟨e', k', ex, ⟨ex.wb_right, v35, by rw [fb.1 _ by_decide, h2], vA,
        fr.trans (fbMono fb fun r h => by_simp_all),
        by rw [fb.1 _ by_decide, h15]⟩,
        by omega, frame21 ztqob (FrameB.toM fb) (fun a _ => by zuodf)
          (funext fun r => WalkKey.exec_rframe ex (B := fun _ => false) by_decide r rfl)
          (by show e.nreg 9999 ≤ e'.nreg 9999; omega)
          (by show e'.nreg 9999 ≤ e.nreg 9999 + k'; omega)⟩
      zudcd
      rcases h with h | h <;> subst h
      · decide
      decide)
    I0 ztbg
  have F' := F₁.trans F
  rw [Finset.union_self] at F'
  refine ⟨c', _, .seq e₁ ex, by_omega, j15, jA, fr, F'⟩

/-- **The next region.** -/
theorem incS_exec (hw : WordsBounded W c) {r p : ℕ} (h14 : c.nreg 212014 = r)
    (h31 : c.nreg 216031 = p) (c0 : c.nreg 212000 = 1) (c6 : c.nreg 216006 = 5)
    (hr : r + 1 ≤ W) (hp : p + 5 ≤ W) :
    ∃ c' k, Exec P W incS c c' k ∧ k = 2 ∧ c'.nreg 212014 = r + 1 ∧ c'.nreg 216031 = p + 5 ∧
      FrameB (fun q => decide (q = 212014 ∨ q = 216031)) c c' := by
  obtain ⟨c', k, ex, hk, v1, v2⟩ : ∃ c' k, Exec P W incS c c' k ∧ k = 2 ∧
      c'.nreg 212014 = r + 1 ∧ c'.nreg 216031 = p + 5 := by
    unfold incS
    exec_block
    all_goals try (config_simp; simp only [h14, h31, c0, c6]; omega)
    simp_all
  exact ⟨c', k, ex, hk, v1, v2, exec_frameB ex by_decide⟩
end exec
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt Programs SignK WalkKey
open BuildRam (FrameM FrameM.mono FrameM.trans FrameB.toM)
open DrvR (regHost)
@[expose] public section
def HostOK (sH : Stmt) (κH : ℕ) : Prop :=
  Meets sH {bDownDrv}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ c.nreg 215002 ≤ 1 ∧
      ztxks ∧
      ∃ (L : List zte) (E : List ℕ), L ≠ [] ∧
        ChordTriplesOK ztwiq zta L ∧ E.Perm ztct ∧
        E.Pairwise ztbajk ∧
        (interiorModel zta).DegLe
          ((BuildNF.buildNF ztwiq zta L E).F ztwiq
            zta) 4 ∧
        NFWithin c.nmem ztghd ztm
          ztbaja ∧
        c.nreg 215001 < (BuildNF.buildNF ztwiq zta L E).nRegions)
    (fun P c c' =>
      ztbff ∧
      ∀ (L : List zte) (E : List ℕ), L ≠ [] →
        ChordTriplesOK ztwiq zta L → E.Perm ztct →
        E.Pairwise ztbajk →
        NFAt c.nmem ztghd ztbaja →
        let H := regHost ztzei (Qof P).n
          ztbaja ztdzj
        c.nreg ALLOC ≤ c'.nreg 215010 ∧ c'.nreg 215010 + 3 * H.length + 1 ≤ c'.nreg ALLOC ∧
          HostAt c'.nmem ztmfe H ∧ c'.nreg 215011 = H.length ∧
          c'.nreg 215012 = (H.pts (Qof P).n).length)
    (fun _ _ => κH)
theorem hostOK_of (h : DrvR.HostRamSpec) : ∃ sH κH, HostOK sH κH := h

/-- The body of `ExpSpec`. -/
def ExpOK (sE : Stmt) (κE : ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (c : Config) (H : Host) (li : Bool),
    WordsBounded W c → HostAt c.nmem ztmfy H → HostWF P.n H →
    c.nreg 212021 = H.length → c.nreg 212016 = (H.pts P.n).length →
    c.nreg 212011 = ztfhy → c.nreg 212010 = P.n →
    c.nreg 212000 = 1 → c.nreg 212001 = 0 → c.nreg 212002 = 2 →
    c.nreg 212022 + 3 * H.length + 1 ≤ c.nreg 212015 →
    c.nreg 212015 + 3 * (H.pts P.n).length ≤ W →
    ∃ c' k, Exec P W sE c c' k ∧ k ≤ κE * ztlcj ∧
      PtArrB c'.nmem zthun ztzyj ∧
      (∀ a, ztgfa →
        c'.nmem a = c.nmem a) ∧
      FrameM ztzfp c c'
theorem expOK_of (h : ExpSpec) : ∃ sE κE, ExpOK sE κE := h

/-- The host RAM call (`K > 0`). -/
def hostK (sH : Stmt) : Stmt :=
  .seq zthta
    (.seq sH zthsz)

/-- **The host of the region.** -/
def hostS (sH : Stmt) : Stmt := .ifLtN 212001 212012 (hostK sH) host0
section exec
variable {P : Polygon} {W : ℕ}

/-- A register frame within band `bDownDrv` is a `bDownDrv` frame. -/
theorem frame21_of_B {B : ℕ → Bool} {c c' : Config} {k : ℕ}
    (hB : ∀ r, B r = true → bandOf r = bDownDrv) (hf : FrameB B c c') (hrr : c'.rreg = c.rreg) :
    Frame {bDownDrv} c c' k := by
  have hA : ztble := hf.1 _ (by
    cases h : B ALLOC
    · rfl
    · have := hB _ h; tauto)
  exact frame21 (fun r h => Or.inl (hB r h)) (FrameB.toM hf) (fun a _ => by zuode) hrr
    by_omega by_omega
set_option maxHeartbeats 8000000 in
/-- **The host of the region.** -/
theorem hostS_exec {sH : Stmt} {κH : ℕ} (hH : HostOK sH κH) {E : BEnv} (hE : BGood E) {r : ℕ}
    (hr : r < E.K + 1) (c : Config) (hw : WordsBounded E.W c) (R : BRegs E c)
    (h14 : c.nreg 212014 = r) (hlow : ∀ a, a < E.B₂ → c.nmem a = E.m₀ a)
    (hA : E.B₂ ≤ c.nreg ALLOC) (hroom : c.nreg ALLOC + κH + 20 ≤ E.W) :
    ∃ c' k, ∃ H : Host, Exec E.P E.W ztmlk c c' k ∧ k ≤ κH + 20 ∧
      HostAt c'.nmem (c'.nreg 212022) H ∧ HostWF E.P.n H ∧ c'.nreg 212021 = H.length ∧
      c'.nreg 212016 = (H.pts E.P.n).length ∧ E.pts r = wlist E.li (H.pts E.P.n) ∧
      c.nreg ALLOC ≤ c'.nreg 212022 ∧ c'.nreg 212022 + 3 * H.length + 1 ≤ c'.nreg ALLOC ∧
      (∀ q, bandOf q = bDownDrv → zthjj → q ≠ 212016 → q ≠ 212021 →
        q ≠ 212022 → q ≠ 212032 → q ≠ 212035 → c'.nreg q = c.nreg q) ∧
      Frame {bDownDrv} c c' k := by
  zucgm
  zumeg
  zuhk
  · -- the whole walk
    obtain ⟨c', k, e, hk, v22, vA, hH0, v16, v21, hm, FM, F⟩ := host0_exec (P := E.P) c hw R.n
      by_omega R.c0 R.c1 by_omega
    have ex : Exec E.P E.W ztmlk c c' ztcnq :=
      .ifLtN_false (by rw [R.c1, R.K, hK]; omega) e
    refine ⟨c', k + 2, [HostItem.run 0 (E.P.n - 1)], ex, by_omega, by_simp_all,
      fun it hit => ?_, by_omega, ?_, ?_, by zuodg, by_simp_all,
      fun q hq1 _ a b d e f => FM.1 q (by
        have h9 : q ≠ 9999 := by intro h; subst h; tauto
        simp_all),
      F.mono le_rfl by_omega⟩
    · grind
    · zuouv; zuoiu; omega
    · rw [BGood.pts_zero hK, hQn]
  · -- the host RAM
    have hr' : ztjaf := by zuoda; exact hr
    obtain ⟨c₁, k₁, e₁, hk₁, v0, v1, v2, g₁, m₁, rr₁⟩ : ∃ c₁ k₁, Exec E.P E.W
        zthta c c₁ k₁ ∧
        k₁ = 3 ∧ c₁.nreg 215000 = E.H ∧ c₁.nreg 215001 = r ∧
        c₁.nreg 215002 = (if E.li then 1 else 0) ∧
        (∀ q, q ≠ 215000 → q ≠ 215001 → q ≠ 215002 → c₁.nreg q = c.nreg q) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg := by
      exec_block
      refine ztfwx <;> config_simp
      · exact R.h5
      · omega
      · exact R.li
      simp_all
    zud
    have A₁ : ztdc := g₁ _ by_decide by_decide by_decide
    have hNW : ztylg := by
      rw [A₁]
      exact (hE.hNF.transport ztese).mono hA
    have hLne : E.L ≠ [] := List.ne_nil_of_length_pos hK
    obtain ⟨c₂, k₂, e₂, hk₂, ⟨pk, pH⟩, F₂⟩ := hH E.P E.W c₁ w₁
      ⟨hE.hG, hE.hWh, by_grind,
        by rw [v2, ← hE.hli]; simp, E.L, E.E, hLne, hE.hok, hE.hperm, hE.hsort,
        hE.hdeg, by_simp_all, by_simp_all⟩
      by_grind
    have hp := pH E.L E.E hLne hE.hok hE.hperm hE.hsort (by zuouw; exact hNW.nfAt)
    dsimp only at hp
    have hdec : decide (c₁.nreg 215002 = 1) = E.li := by rw [v2]; simp
    rw [hdec, v1] at hp
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hp
    zue
    obtain ⟨c₃, k₃, e₃, hk₃, u22, u21, u16, g₃, m₃, rr₃⟩ : ∃ c₃ k₃, Exec E.P E.W
        zthsz c₂ c₃ k₃ ∧
        k₃ = 3 ∧ c₃.nreg 212022 = c₂.nreg 215010 ∧ c₃.nreg 212021 = c₂.nreg 215011 ∧
        c₃.nreg 212016 = c₂.nreg 215012 ∧
        (∀ q, q ≠ 212022 → q ≠ 212021 → q ≠ 212016 → c₃.nreg q = c₂.nreg q) ∧
        c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg := by
      exec_block
      refine ztfwx <;> config_simp
      simp [a, b, d]
    have ex : Exec E.P E.W ztmlk c c₃ (k₁ + zttl + 1) :=
      .ifLtN_true (by rw [R.c1, R.K]; exact hK) ztwrj
    set H := regHost E.li (Qof E.P).n E.N r with hHd
    have hwf : HostWF E.Q.n H := by
      obtain ⟨-, -, -, -, -, -, -, hwf⟩ := DownMath.walk_rep ((hE.ctx hK).rc hr') hE.hli
      rw [hHd]; unfold regHost; split_ifs
      · omega
      · zufxn
    have F₁ : ztpjy := frame21_of_B
      (B := fun q => decide (q = 215000 ∨ q = 215001 ∨ q = 215002))
      (fun q h => by zvmwo at h; rcases h with h | h | h <;> subst h <;> rfl)
      ztduj rr₁
    have F₃ : ztiyh := frame21_of_B
      (B := fun q => decide (q = 212022 ∨ q = 212021 ∨ q = 212016))
      (fun q h => by zvmwo at h; rcases h with h | h | h <;> subst h <;> rfl)
      ztduk rr₃
    have F := (F₁.trans (F₂.trans F₃))
    zujnn
    have A₃ : ztbox := g₃ _ by_decide by_decide by_decide
    have hk₂' : k₂ ≤ κH := hk₂
    refine ⟨c₃, _, H, ex, by_omega, by rw [u22, m₃]; omega, by zvnof; omega,
      by omega, by rw [u16, hb5, hQn], ?_, by_omega,
      by omega, fun q hq1 hq2 a b d _ _ => ?_, F.mono le_rfl by_omega⟩
    · rw [BGood.pts_pos hK, hHd]; unfold regPts; zvmxg
    · rw [g₃ q d b a, pk q hq1 hq2, g₁ q by_omega by_omega by_omega]
end exec
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt Programs SignK WalkKey
open BuildRam (FrameM FrameM.mono FrameM.trans FrameB.toM)
open DrvR (regHost)
@[expose] public section
def regB (sH sE : Stmt) : Stmt :=
  .seq rdS (.seq ztmlk (.seq mxS (.seq resPS (.seq sE (.seq ptLoop incS)))))

/-! ## Facts -/
theorem bktOK_congr {M : Model} {Q : Polygon} {N : NF} {T : List ztwjg}
    {bk bk' : ℕ → ℕ} (h : DrvD.BktOK M Q N T bk) (he : ∀ q, q < 2 * T.length → bk' q = bk q) :
    DrvD.BktOK M Q N T bk' :=
  ⟨fun q hq => by zuoiv; exact h.key q hq, fun q hq => by zuoiv; exact h.arc q hq⟩
variable {E : BEnv}
/-- The output survives a change of the registers outside `216020 … 216022` and of the memory
at or above the end of the output area. -/
theorem OutSt.congr {c c' : Config} {T : List ztwjg} (h : OutSt E c T)
    (hT : T.length ≤ 2 * E.P.n)
    (hr : ∀ q, 216020 ≤ q → q ≤ 216022 → c'.nreg q = c.nreg q)
    (hm : ∀ a, a < E.B₂ + 10 * E.P.n → c'.nmem a = c.nmem a) : OutSt E c' T := by
  zuddy
  have hBK : E.BK = E.B₂ + 6 * E.P.n := rfl
  refine ⟨?_, ?_, ?_, ?_, fun hK => ?_, fun hK q hq => ?_, fun a ha => ?_⟩
  · simp_all
  · simp_all
  · simp_all
  · refine Gran.ChordListAt.congr a4 fun a h1 h2 => hm a ?_
    grind
  · exact bktOK_congr (a5 hK) by_grind
  · grind
  grind

/-- **At most `2 n` new chords.** -/
theorem newLB_len (hE : BGood E) : (newLB E.li E.Q E.L E.E).length ≤ 2 * E.P.n := by
  rw [← hE.hQn]
  apply length_le_of_chords
  · zuhk
    · zudki
    · zuilt
      have := (newL_ok ztqpf).2.1
      grind
  · zuh
    zukxy
    zucoe
    have hr' := List.mem_range.1 hr
    zubxi

/-- **The tagged records of the regions `< r`** are at most `2 n`. -/
theorem TL_len (hE : BGood E) {r : ℕ} (hr : r ≤ E.K + 1) :
    (E.TL r).length ≤ 2 * E.P.n := by
  have h1 := flatMap_range_length_mono (fun r' => (E.recs r').map fun x => zttya) hr
  have h2 : (E.TL zthal).length = (newLB E.li E.Q E.L E.E).length := by
    rw [BEnv.TL_all]; unfold newLB; simp
  have := newLB_len hE
  unfold BEnv.TL at h2
  unfold BEnv.TL
  omega
theorem inDrv_of {B : ℕ → Bool} (h : ∀ r, B r = true → 10000 ≤ r ∧ r < 230000) : DrvD.InDrv B :=
  fun r hr => ⟨DrvD.mem_drvBands by_simp_all by_simp_all, by
    have := (h r hr).1; unfold ALLOC; omega⟩
theorem inDrv_pt : DrvD.InDrv Bpt := inDrv_of fun r h => by
  simp only [Bpt, Bemit, Brec, DrvD.Bapp, DrvD.BappT, DrvD.Bscan, BuildRam.Bhalf, Bk,
    Bool.or_eq_true, decide_eq_true_eq] at h
  omega

/-- The step bound of one region. -/
def regK (E : BEnv) (κH κE : ℕ) : ℕ := κH + κE * ztptq + zthzh * E.S₀ + 50
section exec
theorem rf21 {A₀ : ℕ} {c c' : Config} {k : ℕ} (h : Frame {bDownDrv} c c' k)
    (hA : A₀ ≤ c.nreg ALLOC) : Restore.RF DrvR.drvBands A₀ c c' k :=
  (Restore.RF.of_frame h hA).mono (Finset.singleton_subset_iff.2 DrvR.bDownDrv_mem_drvBands) le_rfl
set_option maxHeartbeats 16000000 in
/-- **One region of the region loop.** -/
theorem regB_exec {sH sE : Stmt} {κH κE : ℕ} (hH : HostOK sH κH) (hX : ExpOK sE κE)
    {E : BEnv} (hE : BGood E) {r : ℕ} (hr : r < E.K + 1) (c : Config) (S : RSt E r c)
    (hroom : c.nreg ALLOC + regK E κH κE ≤ E.W) :
    ∃ c' k, Exec E.P E.W ztogx c c' k ∧ k ≤ regK E κH κE ∧ RSt E ztgu c' ∧
      Restore.RF DrvR.drvBands E.B₂ c c' k ∧
      ztybq := by
  have R := S.regs
  have O := S.out
  zucgm
  zumeg
  have hS₀ := hE.hS₀ r hr
  have hTr := TL_len hE (r := r) by_omega
  have hTr1 := TL_len hE (r := r + 1) by_omega
  zudio
  have hLP := hE.LP_lt hr
  have hAc := S.alloc
  have hBW := hE.hBW
  unfold regK at hroom
  have hmul : 8 * E.S₀ ≤ zthzh * E.S₀ := by_grind
  -- 1. the region record
  have hRP2 : E.RP r - 2 = E.m₀ ztbaq + 5 * r := by unfold BEnv.RP; omega
  have hRP1 : E.RP r - 1 = E.m₀ ztbaq + 5 * r + 1 := by unfold BEnv.RP; omega
  obtain ⟨c₁, k₁, e₁, hk₁, v34, v33, f₁⟩ := rdS_exec (P := E.P) c S.wb S.p31 R.d16 R.K
    by_omega R.c0 R.c1 R.c2
    (by rw [hRP1, O.low _ by_omega]; unfold BEnv.LP at hLP; omega)
  rw [hRP2, O.low _ by_omega] at v34
  rw [hRP1, O.low _ by_omega] at v33
  have g₁ : ∀ q, (q < 212032 ∨ 212034 < q) → c₁.nreg q = c.nreg q := fun q h =>
    f₁.1 q by_grind
  have hnR : c₁.nreg 212034 = E.nRg r := by
    rw [v34]; unfold BEnv.nRg
    split_ifs
    · rfl
    · exact (hE.nA_eq hr).symm
  have hlp : c₁.nreg 212033 = E.LP r := v33
  have R₁ := R.congr fun q hq => g₁ q zteqj
  zucfz
  -- 2. the host
  obtain ⟨c₂, k₂, H, e₂, hk₂, hHA, hwf, h21, h16, hpts, hHB1, hHB2, keep₂, F₂⟩ :=
    hostS_exec hH hE hr c₁ e₁.wb_right R₁ (by rw [g₁ _ by_omega]; exact S.r14)
      (fun a ha => by rw [f₁.2.2.1]; exact O.low a ha) by_omega
      by_omega
  have hNPl : (E.pts r).length = (H.pts E.P.n).length := by rw [hpts, wlist_length]
  have hHl := host_len_le E.P.n H
  have K2 : ∀ q, zthjj → q ≠ 212016 → q ≠ 212021 → q ≠ 212022 →
      q ≠ 212032 → q ≠ 212035 → q ≠ ALLOC → c₂.nreg q = c₁.nreg q := by
    intro q h1 a b d e f g
    by_cases hb : bandOf q = bDownDrv
    · grind
    · exact F₂.1 q by_grind g
  have A₂ := F₂.2.2.2.2.2.2
  have A₂' := F₂.2.2.2.2.2.1
  -- 3. `MX`
  obtain ⟨c₃, k₃, e₃, hk₃, v18, f₃⟩ := mxS_exec (P := E.P) c₂ e₂.wb_right
  have g₃ : ∀ q, q ≠ 212018 → c₃.nreg q = c₂.nreg q := fun q h => f₃.1 q by_grind
  -- 4. the point array
  obtain ⟨c₄, k₄, e₄, hk₄, v15, vA₄, f₄, F₄⟩ := resPS_exec (P := E.P) c₃ e₃.wb_right
    (NP := (H.pts E.P.n).length) by_grind
    (by rw [g₃ _ by_norm_num, K2 _ by_omega by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num by_decide, R₁.c0])
    by_grind
  have g₄ : ∀ q, q ≠ 212015 → q ≠ 212035 → q ≠ 9999 → c₄.nreg q = c₃.nreg q := fun q a b d =>
    f₄.1 q by_grind
  set PA := c₃.nreg ALLOC with hPAd
  have hPA2 : PA = c₂.nreg ALLOC := by_grind
  -- the registers kept from `c₁` to `c₄`
  have K4 : ∀ q, zthjj → q ≠ 212015 → q ≠ 212016 → q ≠ 212018 →
      q ≠ 212021 → q ≠ 212022 → q ≠ 212032 → q ≠ 212035 → q ≠ 9999 →
      c₄.nreg q = c₁.nreg q := fun q h1 a b d e f g i j => by
    rw [g₄ q a i j, g₃ q d, K2 q h1 b e f g i (by unfold ALLOC; exact j)]
  -- 5. the expansion
  obtain ⟨c₅, k₅, e₅, hk₅, harr, hm₅, FM₅⟩ := hX E.P E.W c₄ H E.li e₄.wb_right
    (by rw [g₄ _ by_norm_num by_norm_num by_norm_num, g₃ _ by_norm_num, f₄.2.2.1,
      f₃.2.2.1]; omega) hwf
    by_grind
    by_grind
    (by rw [K4 _ by_omega by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num by_norm_num by_norm_num]; exact R₁.li)
    (by rw [K4 _ by_omega by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num by_norm_num by_norm_num]; exact R₁.n)
    (by rw [K4 _ by_omega by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num by_norm_num by_norm_num]; exact R₁.c0)
    (by rw [K4 _ by_omega by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num by_norm_num by_norm_num]; exact R₁.c1)
    (by rw [K4 _ by_omega by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num by_norm_num by_norm_num]; exact R₁.c2)
    by_grind
    by_omega
  have g₅ : ∀ q, (q < 212023 ∨ 212031 < q) → c₅.nreg q = c₄.nreg q := fun q h =>
    FM₅.1 q by_grind
  have K5 : ∀ q, (FixB q ∨ q = 216031 ∨ q = 212033 ∨ q = 212034 ∨ q = 212013 ∨ q = 216006 ∨
      q = 212014 ∨ ztgyn) → c₅.nreg q = c₁.nreg q := fun q hq => by
    zumqw
    rw [g₅ q by_omega, K4 q by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega by_omega by_omega]
  have A₄ := vA₄
  have A₅ : ztcrj := g₅ _ by_decide
  have hmem5 : ztjbd := fun a ha => by
    rw [hm₅ a by_omega, f₄.2.2.1, f₃.2.2.1, F₂.2.2.1 a by_omega,
      f₁.2.2.1]
  have S₅ : PtSt E r PA c₅ ztuxr := by
    refine ⟨e₅.wb_right, R₁.congr fun q hq => K5 q ztjks, ?_, fun hK => ?_, ?_, ?_, ?_,
      ?_, by_omega, by_omega, ?_⟩
    · rw [K5 _ by_simp, g₁ _ by_omega]; exact S.p31
    · zuigl
    · zuigl
    · rw [g₅ _ by_omega]; omega
    · rw [g₅ _ by_omega, g₄ _ by_norm_num by_norm_num by_norm_num, g₃ _ by_norm_num,
        h16, hNPl]
    · zugf
      rw [hNPl] at hk
      have := harr k by_grind
      rw [v15, ← hpts] at this
      cases hs : (E.pts r).getD k _ <;> zvmyz at this <;> exact this
    · exact O.congr hTr (fun q h1 h2 => by rw [K5 _ by_omega, g₁ _ by_omega])
        (fun a ha => hmem5 a by_omega)
  -- 6. the points
  have hT : (E.TL r).length + (E.recs r).length ≤ 2 * E.P.n := by
    rw [BEnv.TL_succ, List.length_append, List.length_map] at hTr1; omega
  obtain ⟨c₆, k₆, e₆, hk₆, S₆, FM₆, hm₆⟩ := ptLoop_exec hE hr c₅ S₅ hT
  rw [← BEnv.TL_succ] at S₆
  have g₆ := FM₆.1
  -- 7. the next region
  have r14 : c₆.nreg 212014 = r := by
    zunin; exact S.r14
  have r31 := S₆.p31
  have r06 : c₆.nreg 216006 = 5 := by
    zunin; exact S.c6
  obtain ⟨c₇, k₇, e₇, hk₇, u14, u31, f₇⟩ := incS_exec (P := E.P) c₆ S₆.wb r14 r31 S₆.regs.c0 r06
    by_omega by_omega
  have g₇ : ∀ q, q ≠ 212014 → q ≠ 216031 → c₇.nreg q = c₆.nreg q := fun q a b =>
    f₇.1 q by_grind
  have ex : Exec E.P E.W ztogx c c₇ _ :=
    .seq e₁ ztfc
  -- the allocator
  zuhvl
  have A₇ : ztfky := g₇ _ by_decide by_decide
  -- the cost
  have hNS : (H.pts E.P.n).length ≤ E.S₀ := by_omega
  have hk₅' : k₅ ≤ κE * ztptq := hk₅.trans ztdfv
  have hk₆' : k₆ ≤ zthzg * E.S₀ + 3 :=
    hk₆.trans (by have := Nat.mul_le_mul_left zthzg hS₀; omega)
  have hsplit : zthzh * E.S₀ = zthzg * E.S₀ + 6 * E.S₀ := by_ring
  have hcost : k₁ + ztxkw ≤ regK E κH κE := by
    unfold regK; omega
  -- the frame
  have RF₁ : Restore.RF DrvR.drvBands E.B₂ c c₁ k₁ :=
    DrvD.rf_of_frameB ztilg f₁
  have RF₂ : Restore.RF DrvR.drvBands E.B₂ c₁ c₂ k₂ := rf21 F₂ by_omega
  have RF₃ : Restore.RF DrvR.drvBands E.B₂ c₂ c₃ k₃ :=
    DrvD.rf_of_frameB ztilg f₃
  have RF₄ : Restore.RF DrvR.drvBands E.B₂ c₃ c₄ k₄ := rf21 F₄ by_omega
  have RF₅ : Restore.RF DrvR.drvBands E.B₂ c₄ c₅ k₅ :=
    DrvD.rf_of_frameM ztilg FM₅
      (fun a ha => hm₅ a by_omega)
  have RF₆ : Restore.RF DrvR.drvBands E.B₂ c₅ c₆ k₆ :=
    DrvD.rf_of_frameM inDrv_pt FM₆ (fun a ha => hm₆ a ztbbu)
  have RF₇ : Restore.RF DrvR.drvBands E.B₂ c₆ c₇ k₇ :=
    DrvD.rf_of_frameB (inDrv_of fun q h => by zvmwo at h; omega) f₇
  have RF := RF₁.trans (RF₂.trans (RF₃.trans (RF₄.trans ztqci)))
  -- registers kept
  have keep : ∀ q, ztdbv → c₇.nreg q = c.nreg q := fun q hq => by
    zubwm
    zumqw
    rw [g₇ q by_omega by_omega, g₆ q (by
      simp only [Bpt, Bemit, Brec, DrvD.Bapp, DrvD.BappT, DrvD.Bscan, BuildRam.Bhalf, Bk,
        Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega),
      K5 q by_grind, g₁ q by_omega]
  refine ⟨c₇, _, ex, hcost, ?_, RF, keep⟩
  -- the state of the next region
  have v18 : c₇.nreg 212018 = max ztvhy (H.pts E.P.n).length := by
    rw [g₇ _ by_norm_num by_norm_num, g₆ _ by_decide, g₅ _ by_omega,
      g₄ _ by_norm_num by_norm_num by_norm_num, v18, h16,
      K2 _ by_omega by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_decide, g₁ _ by_omega]
  refine ⟨e₇.wb_right, S₆.regs.congr fun q hq => g₇ q zteqj
      zteqj, by rw [g₇ _ by_norm_num by_norm_num]; omega, u14,
    by rw [u31]; rfl, fun r' hr' => ?_, ?_, ?_, ?_⟩
  · zuoux
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr' with h | h
    · exact (S.mx r' h).trans by_omega
    · subst h; omega
  · zuoux; exact max_le S.mxS hNS
  · exact S₆.out.congr hTr1 (fun q h1 h2 => g₇ q by_omega by_omega) (fun a _ => by
      rw [f₇.2.2.1])
  omega
end exec

/-- The constant of the per-point bound. -/
def ptA : ℕ := 10 * ztcom + 20 * ztjic + 3300
theorem ptK_le (C : ℕ) : ptK C + 8 ≤ ptA * ztsvu := by
  unfold ptK dirK ptA; grind

/-- The constant of one region. -/
def κR (κH κE : ℕ) : ℕ := κH + 3 * κE + ptA + 50
theorem regK_le (E : BEnv) (κH κE : ℕ) :
    regK E κH κE ≤ κR κH κE * ztnku * ztjid := by
  unfold regK κR
  have h1 := ptK_le E.Cm
  have h2 : zthzh * E.S₀ ≤ ptA * ztjid * E.S₀ := Nat.mul_le_mul_right _ h1
  grind

/-- **One region of the region loop meets its contract.** -/
theorem regStep {sH sE : Stmt} {κH κE : ℕ} (hH : HostOK sH κH) (hX : ExpOK sE κE) :
    RegStepSpec ztogx (κR κH κE) := by
  intro E hE r c hr S hroom
  have hle := regK_le E κH κE
  obtain ⟨c', k, ex, hk, S', RF, keep⟩ := regB_exec hH hX hE hr c S by_omega
  grind

/-- **The region step**, from the host RAM and the expansion. -/
theorem regStepSpec_of (hHR : DrvR.HostRamSpec) (hEx : ExpSpec) :
    ∃ s κ, RegStepSpec s κ := by
  obtain ⟨sH, κH, hH⟩ := hostOK_of hHR
  obtain ⟨sE, κE, hX⟩ := expOK_of hEx
  exact ⟨regB sH sE, κR κH κE, regStep hH hX⟩
end
end DrvB
end Chazelle.Core
section
set_option hygiene false
local macro "zqbkn" : tactic => `(tactic| (refine ⟨?_, fun q hq => by zvmwg; zumyf⟩
                                           zvmwg; zumxt))
local macro "zqbko" : tactic => `(tactic| (have nk : ztcpg := fun q h1 h2 h => by unfold KeyW at h; omega))
local macro "zqbkp" : tactic => `(tactic| (zumzu
                                           refine ⟨⟨Or.inl ztec, ?_⟩, trivial⟩))
local macro "zqbkq" : tactic => `(tactic| (zumzu; exact ⟨Or.inl ztec, trivial⟩))
local macro "zqbkr" : tactic => `(tactic| (have hW1 : ztehs := by have := hE.hWh; unfold hostWords at this; omega))
set_option hygiene true

/-!
# WP-E, the search on the RAM (`FindOK`), part 15: the test condition at a candidate offset

`gEnd s o`: for the candidate host vertex `(81182, 0)` (key `κ`), `o := [if the end `s` is in the
stretch and its first test was valid then (κ ∈ (kE, kF) ↔ s + 6) else true]` — the condition
`GEnd` the test at the end leaves (`81196 … 81199`, `81190 … 81195` scratch).
-/
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideInArc)
variable {E : FEnv} {c₀ c : Config}

/-- The comparisons of the test condition. -/
def gEndC (s o : ℕ) : Stmt :=
  .seq ztyvt (.seq (cmpM 81192 ztbk ztfp 81182 81011)
    (.seq (cmpM 81194 81182 81011 ztjv ztiz) (.seq (side3 81196 81190 81192 81194)
      (xnorR o 81196 ztsk))))

/-- **The test condition of the end `s` at the candidate vertex `81182`.** -/
def gEnd (s o : ℕ) : Stmt :=
  .seq ztoxu
    (.ifLtN 81011 s (.ifLtN 81011 ztfz (gEndC s o) .skip) .skip)

/-- The registers `gEnd` writes. -/
def GW (o q : ℕ) : Prop := KeyW q ∨ q = o ∨ ztnia
theorem gEnd_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s o : ℕ} (hs : 81160 ≤ s ∧ s + 9 < 81190) (ho : 81197 ≤ o ∧ o < 81200)
    (hs1 : c.nreg s ≤ 1) (hs5 : c.nreg ztfz ≤ 1) (hs6 : c.nreg ztsk ≤ 1)
    (hxE : c.nreg s = 1 → c.nreg ztfz = 1 →
      PosG E.M zti E.P.n ztwke)
    (hxF : c.nreg s = 1 → c.nreg ztfz = 1 →
      PosG E.M zti E.P.n ztwmn)
    (hxU : PosG E.M zti E.P.n ztrys)
    (hroom : c.nreg ALLOC + 33100 ≤ E.W) :
    FRS B E.P E.W c₀ (gEnd s o) c 33100 (fun c' =>
      BitIs c' o (c.nreg s = 1 → c.nreg ztfz = 1 →
        (sideInArc ztbakc
          ztbako
          (E.M.key zti ztrys) ↔ c.nreg ztsk = 1)) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ GW o q → c'.nreg q = c.nreg q) := by
  zuicu
  zufuf
  refine (FRS.seq (K₂ := 33084) (setR_fs hB hI (r := o) ztgy hW1)
    ztesj).mono by_omega (fun _ h => h)
  zucna
  have g := f₁
  set P : Prop := c.nreg s = 1 → c.nreg _ = 1 →
    (sideInArc _
      _
      _ ↔ c.nreg _ = 1) with hP
  have fin : ∀ c' : Config, (∀ q, 80000 ≤ q → q < 90000 → ¬ GW o q → c'.nreg q = c₁.nreg q) →
      ∀ q, 80000 ≤ q → q < 90000 → ¬ GW o q → c'.nreg q = c.nreg q :=
    fun c' h q a b hq => by rw [h q a b hq, g q ztbapj]
  have vac : ¬ (c.nreg s = 1 ∧ c.nreg _ = 1) →
      FRS B E.P E.W c₀ .skip c₁ 0 (fun c' => BitIs c' o P ∧
        ∀ q, 80000 ≤ q → q < 90000 → ¬ GW o q → c'.nreg q = c.nreg q) := fun hn =>
    FRS.skip hI₁ ⟨BitIs.const_one v₁ (fun a b => absurd ztbqy hn), by_grind⟩
  have q0 := g s by_omega
  zukip
  zuhbi

  · exact (FRS.ifF a1 ztwhp).mono by_omega
      by_grind
  refine (FRS.ifT a1 ?_).mono (K := 33084) by_omega ztb
  by_cases a2 : c₁.nreg 81011 < c₁.nreg ztfz
  swap
  · exact (FRS.ifF a2 ztwhp).mono by_omega
      by_grind
  refine (FRS.ifT a2 ?_).mono (K := 33082) by_omega ztb
  have h0 : ztpmj := by_omega
  have h5 : ztbacm := by_omega
  -- the comparisons
  zqbko
  zufwz
  zucaz

  have r82 := g 81182 by_omega
  have r11 := k0
  have hxE' := hxE h0 h5
  have hxF' := hxF h0 h5
  refine (FRS.seq (K₂ := 22058) (cmpM_fs hE hB hI₁ (r := 81190) ztfm
    ztpy ztpy ztpy
    ztpy ztnm ztnm
    ztnm ztnm by_grind
    by_grind by_omega)
    (fun c₂ hI₂ hA₂ ⟨b0, b1, f₂⟩ => ?_)).mono by_omega (fun _ h => h)
  have g₂ : ∀ q, 81100 ≤ q → q < 81190 → c₂.nreg q = c₁.nreg q := fun q h1 h2 =>
    f₂ q by_omega by_omega by_grind by_omega by_omega
  zudpz
  refine (FRS.seq (K₂ := 11036) (cmpM_fs hE hB hI₂ (r := 81192) ztfm
    ztpy ztpy ztpy
    ztpy ztnm ztnm
    ztnm ztnm
    by_grind
    by_grind by_omega)
    (fun c₃ hI₃ hA₃ ⟨b2, b3, f₃⟩ => ?_)).mono by_omega (fun _ h => h)
  rw [g₂ ztbk by_omega by_omega, g₂ ztfp by_omega by_omega, r1, r2,
    g₂ 81182 by_omega by_omega, k0₂, r82] at b2
  have g₃ : ∀ q, 81100 ≤ q → q < 81190 → c₃.nreg q = c₁.nreg q := fun q h1 h2 => by
    rw [f₃ q by_omega by_omega by_grind by_omega by_omega, g₂ q h1 h2]
  zufxa
  refine (FRS.seq (K₂ := 14) (cmpM_fs hE hB hI₃ (r := 81194) ztfm
    ztpy ztpy ztpy
    ztpy ztnm ztnm
    ztnm ztnm
    (by rw [g₃ 81182 by_omega by_omega, k0₃, r82]; omega)
    (by rw [g₃ _ by_omega by_omega, g₃ _ by_omega by_omega, r3, r4]; omega)
    by_omega) (fun c₄ hI₄ hA₄ ⟨b4, b5, f₄⟩ => ?_)).mono by_omega (fun _ h => h)
  rw [g₃ 81182 by_omega by_omega, k0₃, r82, g₃ ztjv by_omega by_omega,
    g₃ ztiz by_omega by_omega, r3, r4] at b4
  have p4 : ∀ q, 81190 ≤ q → q ≤ 81193 → c₄.nreg q = c₃.nreg q := fun q h1 h2 =>
    f₄ q by_omega by_omega zthyz by_omega by_omega
  have b0' := b0.of_eq (show c₄.nreg 81190 = c₂.nreg 81190 by
    rw [p4 _ by_norm_num by_norm_num, f₃ _ by_norm_num by_norm_num
      ztmg by_norm_num by_norm_num])
  have b2' := b2.of_eq (p4 81192 by_norm_num by_norm_num)
  rw [r1, r2, r3, r4] at b0'
  refine (FRS.seq (K₂ := 6) (side3_fs hE hB hI₄ (r := 81196) ztfm
    by_norm_num by_norm_num by_norm_num by_norm_num b0' b2' b4)
    (fun c₅ hI₅ hA₅ ⟨b6, f₅⟩ => ?_)).mono by_omega (fun _ h => h)
  have e6 : c₅.nreg ztsk = c.nreg ztsk := by
    rw [f₅ _ by_omega, f₄ _ by_omega by_omega ztnm by_omega
      by_omega, g₃ _ by_omega by_omega, g _ by_omega]
  have b7 : BitIs c₅ ztsk _ := ⟨by_omega, by rw [e6]⟩
  refine (xnorR_fs hE hB hI₅ (r := o) ztgy by_omega by_omega b6 b7).mono
    le_rfl (fun c' ⟨b8, f₈⟩ => ⟨b8.congr ?_, fun q a b hq => ?_⟩)
  · rw [hP, sideInArc_iff']
    grind
  · have hk := fun h => hq zteg
    have ho' := fun h => hq ztwkb
    have h9 : ¬ ztnia := fun h => hq ztwxb
    rw [f₈ q ho', f₅ q by_omega, f₄ q a b hk by_omega by_omega, f₃ q a b hk by_omega
      by_omega, f₂ q a b hk by_omega by_omega, g q ho']

/-! ## A candidate offset -/

/-- The host vertex `81182 := (g + u) mod n` and the piece-chain vertex `81183 := g' + u` of the
candidate offset `u` in `81180`. -/
def wPos : Stmt :=
  .seq (Stmt.block [.subN 81188 81017 81130])
    (.seq (.ifLtN 81180 81188 ztnpk
      ztnpl) (Stmt.block [.addN 81183 81131 81180]))

/-- `o := ¬ (end s in the stretch ∧ its vertex is the candidate's ∧ it is at a vertex)`. -/
def neEnd (s p o : ℕ) : Stmt :=
  .seq ztoxu
    (.ifLtN 81011 s (.ifLtN 81183 p .skip (.ifLtN p 81183 .skip
      (.ifLtN 81011 ztyd .skip (Stmt.block [.constN o 0])))) .skip)

/-- **The candidate check**: `81181 := [u < L ∧ 81021 ≤ vM ∧ (u is not an end) ∧ GA ∧ GB]`. -/
def wcand : Stmt :=
  .seq wPos (.seq (Stmt.block [.constN 81181 0])
    (.ifLtN 81180 81132 (.ifLtN 81182 81021 .skip
      (.seq (gEnd 81160 81197) (.seq (gEnd 81170 81198) (.seq (neEnd 81160 81153 81184)
        (.seq (neEnd 81170 81154 81185) (.seq (andR 81186 81184 81185)
          (.seq (andR 81187 81197 81198) (andR 81181 81186 81187)))))))) .skip))
theorem wPos_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hg : c.nreg 81130 < E.M.W.n) (hun : c.nreg 81180 < E.M.W.n)
    (hu' : c.nreg 81131 + c.nreg 81180 ≤ E.W) :
    FRS B E.P E.W c₀ wPos c 5 (fun c' =>
      c'.nreg 81182 = ztqig % E.M.W.n ∧
      c'.nreg 81183 = c.nreg 81131 + c.nreg 81180 ∧
      ∀ q, q ≠ 81182 → q ≠ 81183 → q ≠ 81188 → c'.nreg q = c.nreg q) := by
  zumpi
  have n17 : c.nreg 81017 = n := by zunic
  have ok1 : okB E.W c.nmem [.subN 81188 81017 81130] c.nreg := by
    zqbkq
  refine FRS.seq (K₂ := 4) ztbbr ztiy
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.subN 81188 81017 81130] c.nreg q := by_simp_all
  have v88 : c₁.nreg 81188 = n - c.nreg 81130 := by zumwx; simp [regB, regI, upd, n17]
  have f₁ : ∀ q, q ≠ 81188 → c₁.nreg q = c.nreg q := fun q hq => by
    zutt
  have w30 := f₁ 81130 by_norm_num
  have w80 := f₁ 81180 by_norm_num
  have w31 := f₁ 81131 by_norm_num
  have hnW : n ≤ E.W := by
    have := hI₁.hw.1 81017; simp_all
  have step : FRS B E.P E.W c₀ (.ifLtN 81180 81188 ztnpk
      ztnpl) c₁ 3 (fun c' =>
        c'.nreg 81182 = ztqig % n ∧
        ∀ q, q ≠ 81182 → c'.nreg q = c₁.nreg q) := by
    by_cases hc : c₁.nreg 81180 < c₁.nreg 81188
    · have okc : okB E.W c₁.nmem [.addN 81182 81130 81180] c₁.nreg := by
        zqbkp
        omega
      refine (FRS.ifT hc ztgdt).mono by_simp zthi
      have e' : ∀ q, c'.nreg q = regB c₁.nmem [.addN 81182 81130 81180] c₁.nreg q :=
        by simp_all
      zqbkn
      rw [w30, w80, Nat.mod_eq_of_lt by_omega]
    · have okc : okB E.W c₁.nmem [.subN 81182 81180 81188] c₁.nreg := by
        zqbkq
      refine (FRS.ifF hc ztgdt).mono by_simp zthi
      have e' : ∀ q, c'.nreg q = regB c₁.nmem [.subN 81182 81180 81188] c₁.nreg q :=
        by simp_all
      zqbkn
      rw [v88, w80] at hc ⊢
      have e2 : c.nreg 81130 + c.nreg 81180 = (c.nreg 81180 - ztrtw) + n := by_omega
      zuhlc
  refine FRS.seq (K₂ := 1) step (fun c₂ hI₂ hA₂ ⟨u2, f₂⟩ => ?_)
  have ok3 : okB E.W c₂.nmem [.addN 81183 81131 81180] c₂.nreg := by
    zqbkp
    simp_all
  zucpc
  have e' : ∀ q, c'.nreg q = regB c₂.nmem [.addN 81183 81131 81180] c₂.nreg q :=
    by simp_all
  refine ⟨by zvmwg; tauto, ?_, fun q h1 h2 h3 => ?_⟩
  · zujn
    simp_all
  · zvmwg; zundw; simp_all
theorem neEnd_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s p o : ℕ} (ho : SReg o) (hs1 : c.nreg s ≤ 1) (hos : o ≠ s) (hop : o ≠ p)
    (ho83 : o ≠ 81183) (ho7 : o ≠ s + 7) (_ho11 : o ≠ 81011) :
    FRS B E.P E.W c₀ (neEnd s p o) c 10 (fun c' =>
      BitIs c' o ztxex ∧
      ∀ q, q ≠ o → c'.nreg q = c.nreg q) := by
  zqbkr
  refine (FRS.seq (K₂ := 9) (setR_fs hB hI ho hW1) ztcvg).mono
    by_omega ztb
  zucna
  have q0 := f₁ s (Ne.symm hos)
  have q83 := f₁ 81183 (Ne.symm ho83)
  have qp := f₁ p (Ne.symm hop)
  have q7 := f₁ _ (Ne.symm ho7)
  have yes : ¬ (c.nreg s = 1 ∧ c.nreg 81183 = c.nreg p ∧ c.nreg _ = 0) →
      FRS B E.P E.W c₀ .skip c₁ 0 (fun c' => BitIs c' o
        ztxex ∧
        ∀ q, q ≠ o → c'.nreg q = c.nreg q) := fun h =>
    FRS.skip hI₁ ⟨BitIs.const_one v₁ h, f₁⟩
  zuhbi

  · exact (FRS.ifF a1 (yes by_simp_all)).mono by_omega by_simp_all
  refine (FRS.ifT a1 ?_).mono (K := 9) by_omega ztb
  by_cases a2 : c₁.nreg 81183 < c₁.nreg p
  · exact (FRS.ifT a2 ztqzg).mono by_omega
      by_simp_all
  zuhiq
  by_cases a3 : c₁.nreg p < c₁.nreg 81183
  · exact (FRS.ifT a3 ztqzg).mono by_omega
      by_simp_all
  zuhir
  by_cases a4 : c₁.nreg 81011 < c₁.nreg ztyd
  · exact (FRS.ifT a4 ztqzg).mono by_omega
      by_simp_all
  · exact (FRS.ifF a4 ((setR_fs hB hI₁ ho ztbg).mono le_rfl (fun c' ⟨v, f⟩ =>
      ⟨BitIs.const_zero v by_omega,
        by simp_all⟩))).mono by_omega (fun _ h => h)

/-- The test condition of the end `s` at the host vertex `v`, in the configuration `c`. -/
def GAt (E : FEnv) (c : Config) (s v : ℕ) : Prop :=
  c.nreg s = 1 → c.nreg ztfz = 1 →
    (sideInArc ztbakc
      ztbako
      (E.M.key zti ztcfs) ↔ c.nreg ztsk = 1)

/-- The candidate condition of the offset `u`. -/
def WCand (E : FEnv) (c₀ c : Config) (u : ℕ) : Prop :=
  u < c.nreg 81132 ∧ c₀.nreg 81021 ≤ zthva % E.M.W.n ∧
    ¬ (c.nreg 81160 = 1 ∧ c.nreg 81131 + u = c.nreg 81153 ∧ c.nreg 81167 = 0) ∧
    ¬ (c.nreg 81170 = 1 ∧ c.nreg 81131 + u = c.nreg 81154 ∧ c.nreg 81177 = 0) ∧
    GAt E c 81160 ztbaah ∧ GAt E c 81170 ztbaah

/-- The facts of an end that the candidate check needs. -/
def EndOK (E : FEnv) (c : Config) (s : ℕ) : Prop :=
  c.nreg s ≤ 1 ∧ c.nreg ztfz ≤ 1 ∧ c.nreg ztsk ≤ 1 ∧
    (c.nreg s = 1 → c.nreg ztfz = 1 →
      PosG E.M zti E.P.n ztwke ∧
      PosG E.M zti E.P.n ztwmn)

/-- The cost bound of `wcand`. -/
def wcK : ℕ := 66300

/-- The registers `wcand` writes. -/
def WcW (q : ℕ) : Prop := KeyW q ∨ (81181 ≤ q ∧ q ≤ 81199)
theorem wcand_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hA : EndOK E c 81160) (hBo : EndOK E c 81170) (hg : c.nreg 81130 < E.M.W.n)
    (hun : c.nreg 81180 < E.M.W.n) (hu' : c.nreg 81131 + c.nreg 81180 ≤ E.W)
    (hroom : c.nreg ALLOC + wcK ≤ E.W) :
    FRS B E.P E.W c₀ wcand c wcK (fun c' => BitIs c' 81181 (WCand E c₀ c (c.nreg 81180)) ∧
      c'.nreg 81183 = c.nreg 81131 + c.nreg 81180 ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ WcW q → c'.nreg q = c.nreg q) := by
  zqbkr
  zqbko
  set u := c.nreg 81180
  set vM := zthva % E.M.W.n
  refine (FRS.seq (K₂ := 66295) (wPos_fs hE hB hI hg hun hu') (fun c₁ hI₁ hA₁ ⟨w82, w83, f₁⟩ => ?_)).mono
    by_rfl ztb
  refine (FRS.seq (K₂ := 66294) (setR_fs hB hI₁ (r := 81181) ztfm
    ztbg) (fun c₂ hI₂ hA₂ ⟨v81, f₂⟩ => ?_)).mono by_omega (fun _ h => h)
  -- the registers of `c` below the candidate's
  have R2 : ∀ q, (q < 81181 ∨ (81189 < q ∧ q ≠ 81181)) → q ≠ 81182 → q ≠ 81183 → q ≠ 81188 →
      c₂.nreg q = c.nreg q := by_grind
  have r80 : c₂.nreg 81180 = u := by_grind
  have r32 : c₂.nreg 81132 = c.nreg 81132 := by_grind
  have r82 : c₂.nreg 81182 = vM := by_grind
  have r21 : c₂.nreg 81021 = c₀.nreg 81021 := hI₂.hin _ ztbc
  have fin : ∀ c' : Config, (∀ q, 80000 ≤ q → q < 90000 → ¬ WcW q → c'.nreg q = c₂.nreg q) →
      ∀ q, 80000 ≤ q → q < 90000 → ¬ WcW q → c'.nreg q = c.nreg q := fun c' h q a b hq => by
    zumrn
    rw [h q a b by_trivial, f₂ q by_omega, f₁ q by_omega by_omega by_omega]
  have c283 : c₂.nreg 81183 = c.nreg 81131 + u := by rw [f₂ _ by_norm_num, w83]
  have no : ¬ WCand E c₀ c u → FRS B E.P E.W c₀ .skip c₂ 0 (fun c' =>
      BitIs c' 81181 _ ∧ c'.nreg 81183 = c.nreg 81131 + u ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ WcW q → c'.nreg q = c.nreg q) := fun hn =>
    FRS.skip hI₂ ⟨BitIs.const_zero v81 hn, c283, fin c₂ by_omega⟩
  by_cases a1 : c₂.nreg 81180 < c₂.nreg 81132
  swap
  · exact (FRS.ifF a1 (no (fun h => by rw [r80, r32] at a1; exact a1 h.1))).mono by_omega
      by_grind
  refine (FRS.ifT a1 ?_).mono (K := 66294) by_omega ztb
  by_cases a2 : c₂.nreg 81182 < c₂.nreg 81021
  · exact (FRS.ifT a2 (no (fun h => by rw [r82, r21] at a2; have := h.2.1; omega))).mono
      by_omega by_grind
  zuhiq
  have hvl : c₀.nreg 81021 ≤ vM := by_omega
  have hvn : vM < E.M.W.n := Nat.mod_lt _ by_omega
  -- the ends' facts at `c₂`
  have slot : ∀ s, zthkh → ∀ j, j ≤ 9 → c₂.nreg _ = c.nreg ztcoi :=
    fun s hs j hj => R2 _ by_omega by_omega by_omega by_omega
  have eok : ∀ s, zthkh → EndOK E c s → EndOK E c₂ s := by
    intro s hs ⟨e1, e5, e6, ex⟩
    have k0 := slot s hs 0 by_omega
    zvnhg at k0
    refine ⟨by_omega, by rw [slot s hs 5 by_omega]; exact e5,
      by rw [slot s hs 6 by_omega]; exact e6, fun h0 h5 => ?_⟩
    zvnib at h0; rw [slot s hs 5 by_omega] at h5
    rw [slot s hs 1 by_omega, slot s hs 2 by_omega, slot s hs 3 by_omega,
      slot s hs 4 by_omega]
    grind
  have hxU : PosG E.M zti E.P.n ⟨c₂.nreg 81182, 0⟩ := by
    rw [r82]
    exact posG_of_vlo hE hI hvn ztdjf
      (Or.inr (by rw [hI.hin _ ztbc]; omega))
  obtain ⟨a1', a5', a6', ax'⟩ := eok 81160 ztp hA
  have hAW : c₂.nreg ALLOC + 66292 ≤ E.W := by unfold wcK at hroom; omega
  refine (FRS.seq (K₂ := 33138) (gEnd_fs hE hB hI₂ (s := 81160) (o := 81197) ⟨by_norm_num,
    by norm_num⟩ ⟨by_norm_num, by_norm_num⟩ a1' a5' a6' (fun h0 h5 => (ax' h0 h5).1)
    (fun h0 h5 => (ax' h0 h5).2) hxU by_omega) (fun c₃ hI₃ hA₃ ⟨g97, f₃⟩ => ?_)).mono
    by_omega ztb
  have R3 := f₃
  have eok₃ : EndOK E c₃ 81170 := by
    obtain ⟨b1, b5, b6, bx⟩ := eok 81170 ztbt hBo
    have t : ∀ j, j ≤ 9 → c₃.nreg _ = c₂.nreg (81170 + j) := fun j hj =>
      R3 _ by_omega by_omega ztzd
    have t0 := t 0 by_omega
    zvnhg at t0
    refine ⟨by_omega, by rw [t 5 by_omega]; exact b5, by rw [t 6 by_omega]; exact b6,
      fun h0 h5 => ?_⟩
    rw [t0] at h0; rw [t 5 by_omega] at h5
    rw [t 1 by_omega, t 2 by_omega, t 3 by_omega, t 4 by_omega]
    grind
  obtain ⟨b1', b5', b6', bx'⟩ := eok₃
  have hxU₃ : PosG E.M zti E.P.n ⟨c₃.nreg 81182, 0⟩ := by
    rw [R3 _ by_norm_num by_norm_num ztzd]; omega
  refine (FRS.seq (K₂ := 38) (gEnd_fs hE hB hI₃ (s := 81170) (o := 81198) ⟨by_norm_num,
    by norm_num⟩ ⟨by_norm_num, by_norm_num⟩ b1' b5' b6' (fun h0 h5 => (bx' h0 h5).1)
    (fun h0 h5 => (bx' h0 h5).2) hxU₃ by_omega) (fun c₄ hI₄ hA₄ ⟨g98, f₄⟩ => ?_)).mono
    by_omega ztb
  have R4 := f₄
  have s160 : c₄.nreg 81160 ≤ 1 := by
    rw [R4 _ by_norm_num by_norm_num ztzd,
      R3 _ by_norm_num by_norm_num ztzd]; omega
  refine (FRS.seq (K₂ := 28) (neEnd_fs hE hB hI₄ (s := 81160) (p := 81153) (o := 81184)
    ⟨by_norm_num, by_norm_num⟩ s160 by_norm_num by_norm_num by_norm_num by_norm_num
    by_norm_num) (fun c₅ hI₅ hA₅ ⟨n84, f₅⟩ => ?_)).mono by_omega (fun _ h => h)
  have s170 : c₅.nreg 81170 ≤ 1 := by
    rw [f₅ _ by_norm_num, R4 _ by_norm_num by_norm_num ztzd]
    omega
  refine (FRS.seq (K₂ := 18) (neEnd_fs hE hB hI₅ (s := 81170) (p := 81154) (o := 81185)
    ⟨by_norm_num, by_norm_num⟩ s170 by_norm_num by_norm_num by_norm_num by_norm_num
    by_norm_num) (fun c₆ hI₆ hA₆ ⟨n85, f₆⟩ => ?_)).mono by_omega (fun _ h => h)
  have n84' := n84.of_eq (f₆ 81184 by_norm_num)
  refine (FRS.seq (K₂ := 12) (andR_fs hE hB hI₆ (r := 81186) ztfm
    by_norm_num by_norm_num n84' n85) (fun c₇ hI₇ hA₇ ⟨a86, f₇⟩ => ?_)).mono by_omega
    ztb
  have g97' : BitIs c₇ 81197 _ := g97.of_eq (by
    rw [f₇ _ by_norm_num, f₆ _ by_norm_num, f₅ _ by_norm_num,
      R4 _ by_norm_num by_norm_num ztzd])
  have g98' : BitIs c₇ 81198 _ := g98.of_eq (by
    rw [f₇ _ by_norm_num, f₆ _ by_norm_num, f₅ _ by_norm_num])
  refine (FRS.seq (K₂ := 6) (andR_fs hE hB hI₇ (r := 81187) ztfm
    by_norm_num by_norm_num g97' g98') (fun c₈ hI₈ hA₈ ⟨a87, f₈⟩ => ?_)).mono by_omega
    ztb
  refine (andR_fs hE hB hI₈ (r := 81181) ztfm by_norm_num
    by_norm_num (a86.of_eq (f₈ 81186 by_norm_num)) a87).mono le_rfl
    (fun c₉ ⟨a81, f₉⟩ => ⟨a81.congr ?_, ?_, fun q a b hq => ?_⟩)
  · -- the condition, read back in `c`
    have T3 : ∀ q, ztell → c₃.nreg q = c.nreg q := fun q hq => by
      rw [R3 q by_omega by_omega ztzd]
      by_cases h82 : q = 81182
      · omega
      exact R2 q by_omega by_omega by_omega by_omega
    have T4 : ∀ q, ztell → c₄.nreg q = c.nreg q := fun q hq => by
      rw [R4 q by_omega by_omega ztzd, T3 q hq]
    have T5 : ∀ q, ztell → c₅.nreg q = c.nreg q := fun q hq => by
      rw [f₅ q by_omega, T4 q hq]
    have c483 : c₄.nreg 81183 = c.nreg 81131 + u := by
      rw [R4 _ by_norm_num by_norm_num ztzd,
        R3 _ by_norm_num by_norm_num ztzd, f₂ _ by_norm_num, w83]
    have c583 : c₅.nreg 81183 = c.nreg 81131 + u := by rw [f₅ _ by_norm_num, c483]
    rw [T4 81160 by_omega, c483, T4 81153 by_omega,
      T4 _ by_omega, T5 81170 by_omega, c583,
      T5 81154 by_omega, T5 _ by_omega]
    have S2 : ∀ q, ztell → c₂.nreg q = c.nreg q := fun q hq =>
      R2 q by_omega by_omega by_omega by_omega
    have S3 := T3
    rw [S2 81160 by_omega, S2 _ by_omega,
      S2 _ by_omega, S2 _ by_omega,
      S2 _ by_omega, S2 _ by_omega,
      S2 ztsuh by_omega, r82,
      S3 81170 by_omega, S3 _ by_omega,
      S3 _ by_omega, S3 _ by_omega,
      S3 _ by_omega, S3 _ by_omega,
      S3 ztsui by_omega,
      R3 81182 by_norm_num by_norm_num ztzd, r82]
    zultx
    rw [r80, r32] at a1
    exact ⟨fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨a1, hvl, h1, h2, h3, h4⟩,
      fun ⟨_, _, h1, h2, h3, h4⟩ => ⟨ztwo, h3, h4⟩⟩
  · rw [f₉ _ by_norm_num, f₈ _ by_norm_num, f₇ _ by_norm_num, f₆ _ by_norm_num,
      f₅ _ by_norm_num, R4 _ by_norm_num by_norm_num ztzd,
      R3 _ by_norm_num by_norm_num ztzd, c283]
  · zumrn
    have hk : ztsnx := by_grind
    have hr := by_omega
    have gw : ∀ o, 81181 ≤ o → o ≤ 81199 → ¬ GW o q := fun o h1 h2 h => by
      zude
      · grind
      · omega
      · omega
    rw [f₉ q by_omega, f₈ q by_omega, f₇ q by_omega, f₆ q by_omega, f₅ q by_omega,
      R4 q a b ztrra, R3 q a b ztrra,
      f₂ q by_omega,
      f₁ q by_omega by_omega by_omega]
end
end Restore
end Chazelle.Core
end
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideInArc)
variable {E : FEnv} {c₀ c : Config}

/-- **A whole end.** -/
def endFull (s p σ : ℕ) (sT : Stmt) : Stmt := .seq zttjt (endTail s σ sT)

/-- The host edge of the end in `p`. -/
def eMof (E : FEnv) (c : Config) (p : ℕ) : ℕ :=
  ztdcr % E.M.W.n

/-- The registers an end writes. -/
def EndW (s q : ℕ) : Prop := KeyW q ∨ VertW q ∨ ztdpk ∨ zteln

/-- **The result of an end**, read in its start configuration `c`. -/
def EndRes (E : FEnv) (c₀ : Config) (Cα : Chain) (s p σ : ℕ) (c c' : Config) : Prop :=
  let pE := c.nreg p
  let h1 := c.nreg 81155
  let pz : Prop := (chainModel Cα).key zti ztuje < (chainModel Cα).key zti ztujf
  let eM := eMof E c p
  let code := endCode Cα zti pE h1
  BitIs c' s (c.nreg 81131 ≤ pE ∧ pE < c.nreg 81135 ∧ (c.nreg 81131 < pE ∨ pz)) ∧
  (c'.nreg s = 1 → c'.nreg ztbk = eM ∧ c'.nreg ztfp = code ∧ BitIs c' ztyd pz) ∧
  (c'.nreg s = 1 → InRange c₀ eM →
    ∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
      code = 0 → ∀ σb, σb ≤ 1 → GoodAt E reg eM σb → c'.nreg 81007 = 1) ∧
  (c'.nreg s = 1 → InRange c₀ eM → c.nreg 81007 = 0 →
    ∃ ct ct' : Config, TOut E ct ct' ∧ ct.nreg 81060 = eM ∧ ct.nreg 81061 = code ∧
      ct.nreg 81063 = σ ∧ c'.nreg ztjv = ct'.nreg 83012 ∧ c'.nreg ztiz = ct'.nreg 83013 ∧
      (c'.nreg ztfz = 1 ↔ (ct'.nreg 83010 = 1 ∧ ct'.nreg 83011 = 1 ∧
        ztdbt)) ∧
      ztcmv) ∧
  (c'.nreg ztfz = 1 → c'.nreg s = 1 ∧ InRange c₀ eM ∧ c.nreg 81007 = 0) ∧
  (c'.nreg ztfz = 1 → ztceg →
    (c'.nreg ztsk = 1 ↔ (E.M.key zti ztke =
        E.M.key zti ztugl ∨
      sideInArc (E.M.key zti ztugl)
        ztxdq
        ztxdp))) ∧
  EndOK E c' s

/-- The cost bound of `endFull`. -/
def efK (E : FEnv) : ℕ := ehK + etK E
theorem endFull_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {s p σ : ℕ}
    (hs : 81160 ≤ s ∧ s + 9 < 81190) (hp : p = 81153 ∨ p = 81154) (hσ : σ ≤ 1)
    {H : Host} {Cα : Chain}
    (hwf : ChainWF E.P ztdq c₀.nmem ztcpp)
    (hC : ChainDescAt c₀.nmem ztcpp zti H Cα) (hWm : 2 * Cα.m + 7 ≤ E.W)
    (h6 : 6 ≤ c.nreg 81131) (hg : c.nreg 81130 < E.M.W.n)
    (hL : c.nreg 81135 - c.nreg 81131 ≤ E.M.W.n)
    (hpe : PosOK Cα zti E.P.n ztgoo)
    (hcand : c.nreg 81131 ≤ c.nreg p → c.nreg p < c.nreg 81135 →
      InRange c₀ (eMof E c p) → ∀ σb, σb ≤ 1 →
        CandOK E ⟨eMof E c p, endCode Cα zti ztfgw ztvix⟩ ztqih σb)
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M zti E.P.n ztke)
    (hroom : c.nreg ALLOC + efK E ≤ E.W) :
    FRS B E.P E.W c₀ (endFull s p σ E.sT) c (efK E) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ EndW s q → c'.nreg q = c.nreg q) ∧
      ztfn ∧ EndRes E c₀ Cα s p σ c c') := by
  zubkz
  obtain ⟨hC', hwf'⟩ := chain_keep hwf hC zttj hI.hA
  refine (FRS.seq (K₂ := etK E) (endHead_fs hE hB hI (s := s) (p := p) ztuif hp hwf' hC' hWm
    h6 hg hL hpe ztnvr) (fun c₁ hI₁ hA₁ ⟨b0, bp, z5, z6, f₁⟩ => ?_)).mono
    by_rfl ztb
  zuddk
  have F1' : ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → ¬ ztdpk →
      c₁.nreg q = c.nreg q :=
    fun q h1 h2 hk h3 => f₁ q h1 h2 (by
      unfold HeadW; rintro (h | h | h | h | h | h | h | h | h | h)
      · grind
      all_goals omega)
  have F1 : ∀ q, 81000 ≤ q → q < 82000 → ¬ ztdpk → c₁.nreg q = c.nreg q :=
    fun q h1 h2 h3 => F1' q by_omega by_omega (nk q h1 h2) h3
  have hw₁ : ztmtb := hw.congr' (fun q h1 h2 => F1 q by_omega by_omega by_omega)
  have j40 := F1 81140 by_norm_num by_norm_num by_omega
  have j41 := F1 81141 by_norm_num by_norm_num by_omega
  have j52 := F1 81152 by_norm_num by_norm_num by_omega
  have hb0 := b0.1
  have hcand₁ : c₁.nreg s = 1 → InRange c₀ (c₁.nreg ztbk) → ∀ σb, σb ≤ 1 →
      CandOK E ⟨c₁.nreg ztbk, c₁.nreg ztfp⟩ (c₁.nreg 81152) σb := by
    intro h1 hr σb hσb
    zucoj
    obtain ⟨a, b, -⟩ := b0.2.1 h1
    rw [u1, u2, j52]; rw [u1] at hr
    exact hcand a b hr σb hσb
  refine (endTail_fs hE hB hBT hI₁ hw₁ (s := s) (σ := σ) ztuif hσ z5 z6 hb0 hcand₁
    by_grind ztnvr).mono le_rfl
    (fun c₂ ⟨w₂, f₂, m₂, g₂, v5, v5', t₂, v6, s6⟩ => ?_)
  -- reading back
  have F2 : ∀ q, 81011 ≤ q → q < 83000 → ¬ TailW s q → c₂.nreg q = c₁.nreg q := f₂
  have tw : ∀ j, j ≤ 9 → j ≠ 3 → j ≠ 4 → j ≠ 5 → j ≠ 6 → j ≠ 8 → ¬ TailW s ztcoi :=
    fun j hj a b d e f h => by
      unfold TailW RunW SdW VertW KeyW at h; omega
  have t0 : ¬ TailW s s := by unfold TailW RunW SdW VertW KeyW; omega
  have k0 := F2 s by_omega by_omega t0
  have k1 := F2 ztbk by_omega by_omega (tw 1 by_omega by_omega by_omega by_omega
    by_omega by_omega)
  have k2 := F2 ztfp by_omega by_omega (tw 2 by_omega by_omega by_omega by_omega
    by_omega by_omega)
  have k7 := F2 ztyd by_omega by_omega (tw 7 by_omega by_omega by_omega by_omega
    by_omega by_omega)
  have flag₁ : ztmve := F1 _ by_norm_num by_norm_num by_omega
  zuhhz
  refine ⟨w₂, fun q h1 h2 hq => ?_, fun h => m₂ by_omega, ?_⟩
  · zugmo
    have hv : ¬ VertW q := fun h => hq ztwkb
    have hs' : ¬ ztdpk := fun h => hq ztbase
    have h9 : ¬ zteln := fun h => hq (Or.inr ztwxb)
    have ht : ¬ TailW s q := by
      unfold TailW RunW SdW
      rintro ((h | h | h | h | h) | (h | h | h))
      · grind
      · omega
      · omega
      · omega
      · omega
      · grind
      · omega
      omega
    rw [F2 q h1 h2 ht, F1' q by_omega by_omega hk hs']
  -- the result
  refine ⟨b0.of_eq k0, fun h1 => ?_, fun h1 hr => ?_, fun h1 hr hz => ?_, fun h5 => ?_,
    fun h5 hj => ?_, ?_⟩
  · zugew
    obtain ⟨u1, u2, u7⟩ := bp h1
    exact ⟨by rw [k1, u1]; rfl, by_omega, u7.of_eq k7⟩
  · zugew
    zucoj
    intro reg hr' hch hc0 σb hσb hg
    exact g₂ h1 ztmeb reg hr' hch by_omega σb hσb
      (by rw [u1]; exact hg)
  · zugew
    zucoj
    obtain ⟨ct, ct', hT, a1, a2, a3, h3, h4, hv, hm⟩ := t₂ h1 ztmeb
      by_omega
    exact ⟨ct, ct', hT, by rw [a1, u1]; rfl, by_omega, a3, h3, h4, hv, hm⟩
  · obtain ⟨a, b, d⟩ := v5' h5
    obtain ⟨u1, -, -⟩ := bp a
    exact ⟨by_omega, by rw [u1] at b; exact b, by_omega⟩
  · obtain ⟨a, -, -⟩ := v5' h5
    zufze
    have := s6 h5 by_omega
    rw [j40, j41, u1, u2] at this
    trivial
  · -- `EndOK`
    refine ⟨by_omega, v5, v6, fun h1 h5 => ?_⟩
    obtain ⟨a, hr, hz⟩ := v5' h5
    zufze
    have hc := hcand₁ a hr 0 by_omega
    obtain ⟨ct, ct', hT, -, -, -, h3, h4, hv, -⟩ := t₂ a hr hz
    obtain ⟨b10, b11, b12⟩ := hv.1 h5
    zubfd

    zujx
    · rw [k1, k2]
      exact posG_of_vlo hE hI₁ hc.1 hc.2.1 (Or.inr (by
        zuomv; exact hr.1))
    · zukru
      exact posG_of_vlo hE hI₁ hfe hfp (by zuomv; omega)
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideInArc)
variable {E : FEnv} {c₀ c : Config}

/-- Try the offset `p - g' + 1` of the end `s` (edge register `p`) if it is in the stretch. -/
def wTry (s p : ℕ) : Stmt :=
  .ifLtN 81011 81181 .skip (.ifLtN 81011 s
    (.seq (Stmt.block [.subN 81180 p 81131, .addN 81180 81180 81012]) wcand) .skip)

/-- **The witness selection.** -/
def wsel : Stmt :=
  .seq (Stmt.block [.constN 81180 1]) (.seq wcand (.seq (wTry 81160 81153) (wTry 81170 81154)))

/-- The registers the witness selection writes. -/
def WsW (q : ℕ) : Prop := KeyW q ∨ (81180 ≤ q ∧ q ≤ 81199)

/-- The candidate condition depends only on the registers it reads. -/
theorem WCand.congr {c' : Config} (h : ∀ q, ¬ WsW q → 81100 ≤ q → q < 81200 → c'.nreg q = c.nreg q)
    {u : ℕ} : WCand E c₀ c' u ↔ WCand E c₀ c u := by
  have e : ∀ q, (81130 ≤ q ∧ q < 81180) → c'.nreg q = c.nreg q := fun q hq =>
    h q ztbkm by_omega by_omega
  zultx
  rw [e 81132 by_norm_num, e 81130 by_norm_num, e 81160 by_norm_num, e 81131 by_norm_num,
    e 81153 by_norm_num, e (81160 + 7) by_norm_num, e 81170 by_norm_num,
    e 81154 by_norm_num, e (81170 + 7) by_norm_num, e (81160 + 5) by_norm_num,
    e (81160 + 1) by_norm_num, e (81160 + 2) by_norm_num, e (81160 + 3) by_norm_num,
    e (81160 + 4) by_norm_num, e ztsuh by_norm_num, e (81170 + 5) by_norm_num,
    e (81170 + 1) by_norm_num, e (81170 + 2) by_norm_num, e (81170 + 3) by_norm_num,
    e (81170 + 4) by_norm_num, e ztsui by_norm_num]

/-- The invariant of the witness selection, relative to the start `c`. -/
def WsInv (E : FEnv) (c₀ c c' : Config) : Prop :=
  c'.nreg 81181 ≤ 1 ∧ (c'.nreg 81181 = 1 → WCand E c₀ c ztjrk ∧
    c'.nreg 81183 = c.nreg 81131 + c'.nreg 81180) ∧
  (∀ q, 80000 ≤ q → q < 90000 → ¬ WsW q → c'.nreg q = c.nreg q) ∧ 1 ≤ c'.nreg 81180
theorem EndOK.congr {c c' : Config} {s : ℕ} (h : EndOK E c s)
    (he : ∀ j, j ≤ 6 → c'.nreg ztcoi = c.nreg ztcoi) : EndOK E c' s := by
  obtain ⟨e1, e5, e6, ex⟩ := h
  have e0 := he 0 by_omega
  zufba
  refine ⟨by_omega, by_simp_all,
    by simp_all, fun h0 h5 => ?_⟩
  grind
theorem wcand_inv (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) {c' : Config}
    (hI : FInv E.W c₀ c') (hA : EndOK E c 81160) (hBo : EndOK E c 81170)
    (hfr : ∀ q, 80000 ≤ q → q < 90000 → ¬ WsW q → c'.nreg q = c.nreg q)
    (hg : c.nreg 81130 < E.M.W.n) (hun : c'.nreg 81180 < E.M.W.n)
    (hu' : c.nreg 81131 + c'.nreg 81180 ≤ E.W) (hu1 : 1 ≤ c'.nreg 81180)
    (hroom : c'.nreg ALLOC + wcK ≤ E.W) :
    FRS B E.P E.W c₀ wcand c' wcK (fun c'' => WsInv E c₀ c c'' ∧
      (WCand E c₀ c ztjrk → c''.nreg 81181 = 1) ∧ c''.nreg 81180 = c'.nreg 81180) := by
  have fr : ztfxh := fun q h a b =>
    hfr q by_omega by_omega h
  have sl : ∀ s, zthkh → ∀ j, j ≤ 6 → c'.nreg ztcoi = c.nreg ztcoi :=
    fun s hs j hj => fr _ ztbkm by_omega by_omega
  refine (wcand_fs hE hB hI ((hA.congr (sl 81160 ztp))) (hBo.congr (sl 81170 ztbt))
    (by rw [fr 81130 ztbkm by_norm_num by_norm_num]; exact hg) hun
    (by rw [fr 81131 ztbkm by_norm_num by_norm_num]; omega)
    hroom).mono le_rfl (fun c'' ⟨b, e83, f⟩ => ?_)
  have wc : WCand E c₀ c' ztjrk ↔ WCand E c₀ c ztjrk := WCand.congr fr
  have u80 : c''.nreg 81180 = c'.nreg 81180 := f _ by_norm_num by_norm_num
    (by unfold WcW KeyW; omega)
  refine ⟨⟨b.1, fun h => ⟨by rw [u80]; exact wc.1 (b.2.1 h), by
    rw [e83, u80, fr 81131 ztbkm by_norm_num by_norm_num]⟩,
    fun q a b' hq => ?_, by_omega⟩, fun h => b.2.2 (wc.2 h), u80⟩
  have hq' : ¬ WcW q := fun h => hq (h.elim Or.inl (fun h' => Or.inr ⟨by_omega, h'.2⟩))
  grind

/-- **One try.** -/
theorem wTry_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) {c' : Config}
    (hI : FInv E.W c₀ c') (hA : EndOK E c 81160) (hBo : EndOK E c 81170)
    (hv : WsInv E c₀ c c') {s p : ℕ} (hsp : (s = 81160 ∧ p = 81153) ∨ (s = 81170 ∧ p = 81154))
    (hg : c.nreg 81130 < E.M.W.n) (hL : c.nreg 81132 < E.M.W.n)
    (hgL : c.nreg 81131 + c.nreg 81132 ≤ E.W)
    (hp : c.nreg s = 1 → c.nreg 81131 ≤ c.nreg p ∧ c.nreg p - c.nreg 81131 < c.nreg 81132)
    (hroom : c'.nreg ALLOC + wcK + 6 ≤ E.W) :
    FRS B E.P E.W c₀ (wTry s p) c' (wcK + 6) (fun c'' => WsInv E c₀ c c'' ∧
      (c'.nreg 81181 = 1 → c''.nreg 81181 = 1) ∧
      (c.nreg s = 1 → WCand E c₀ c (c.nreg p - c.nreg 81131 + 1) → c''.nreg 81181 = 1)) := by
  zufuf
  zubgm
  obtain ⟨v1, v2, v3, v4⟩ := hv
  have fr : ztfxh := fun q h a b =>
    v3 q by_omega by_omega h
  have es : c'.nreg s = c.nreg s := fr s ztbkm by_omega by_omega
  have ep : c'.nreg p = c.nreg p := fr p ztbkm by_omega by_omega
  have e31 : c'.nreg 81131 = c.nreg 81131 := fr 81131 ztbkm by_norm_num
    by_norm_num
  have hs1 : c.nreg s ≤ 1 := by rcases hsp with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [hA.1, hBo.1]
  by_cases a1 : c'.nreg 81011 < c'.nreg 81181
  · have h1 : c'.nreg 81181 = 1 := by_omega
    exact (FRS.ifT a1 (FRS.skip (K := 0) hI ⟨ztopt, id, fun _ _ => h1⟩)).mono by_omega
      ztb
  refine (FRS.ifF a1 ?_).mono (K := wcK + 6) le_rfl ztb
  have h0 : c'.nreg 81181 = 0 := by_omega
  by_cases a2 : c'.nreg 81011 < c'.nreg s
  swap
  · exact (FRS.ifF a2 (FRS.skip (K := 0) hI ⟨ztopt, fun h => by_omega,
      fun h => by_omega⟩)).mono by_omega (fun _ h => h)
  refine (FRS.ifT a2 ?_).mono (K := wcK + 4) by_omega ztb
  have hs : ztpmj := by_omega
  obtain ⟨hp1, hp2⟩ := hp hs
  have k1 : ztunf := by rw [hI.hin _ ztbc, hE.k1]
  have ok : okB E.W c'.nmem [.subN 81180 p 81131, .addN 81180 81180 81012] c'.nreg := by
    simp only [okB, okI, regI, upd]
    refine ⟨Or.inl ztwmk,
      ⟨Or.inl ztcgx, ?_⟩, trivial⟩
    grind
  refine FRS.seq (K₂ := wcK) ztgds ztiy
  have e₁ : ∀ q, c₁.nreg q = regB c'.nmem [.subN 81180 p 81131, .addN 81180 81180 81012]
      c'.nreg q := fun q => by zvnbm
  have u80 : c₁.nreg 81180 = c.nreg p - c.nreg 81131 + 1 := by
    zumwx; simp [regB, regI, upd, k1, ep, e31]
  have f₁ : ∀ q, q ≠ 81180 → c₁.nreg q = c'.nreg q := fun q hq => by
    zutt
  have hfr₁ : ztfxg := fun q a b h => by
    rw [f₁ q ztbapi, v3 q a b h]
  refine (wcand_inv hE hB hI₁ hA hBo hfr₁ hg by_omega by_omega
    by_omega by_omega).mono le_rfl
    (fun c₂ ⟨iv, hw, u2⟩ => ⟨iv, fun h => by_omega, fun _ h => hw by_grind⟩)

/-- The cost bound of `wsel`. -/
def wsK : ℕ := 3 * wcK + 20
theorem wsel_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hA : EndOK E c 81160) (hBo : EndOK E c 81170) (hg : c.nreg 81130 < E.M.W.n)
    (hL : c.nreg 81132 < E.M.W.n) (hgL : c.nreg 81131 + c.nreg 81132 ≤ E.W)
    (hL0 : 0 < c.nreg 81132)
    (hpA : c.nreg 81160 = 1 → c.nreg 81131 ≤ c.nreg 81153 ∧ c.nreg 81153 - c.nreg 81131 < c.nreg 81132)
    (hpB : c.nreg 81170 = 1 → c.nreg 81131 ≤ c.nreg 81154 ∧ c.nreg 81154 - c.nreg 81131 < c.nreg 81132)
    (hroom : c.nreg ALLOC + wsK ≤ E.W) :
    FRS B E.P E.W c₀ wsel c wsK (fun c' => c'.nreg 81181 ≤ 1 ∧
      (c'.nreg 81181 = 1 → WCand E c₀ c ztjrk ∧
        c'.nreg 81183 = c.nreg 81131 + c'.nreg 81180 ∧ 1 ≤ c'.nreg 81180) ∧
      ((WCand E c₀ c 1 ∨
        (c.nreg 81160 = 1 ∧ WCand E c₀ c (c.nreg 81153 - c.nreg 81131 + 1)) ∨
        (c.nreg 81170 = 1 ∧ WCand E c₀ c (c.nreg 81154 - c.nreg 81131 + 1))) →
          c'.nreg 81181 = 1) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ WsW q → c'.nreg q = c.nreg q) := by
  zufuf
  refine (FRS.seq (K₂ := 3 * wcK + 12) (setR_fs hB hI (r := 81180) ztfm hW1)
    ztesj).mono by_decide (fun _ h => h)
  have hfr₁ : ztfxg := fun q a b h =>
    f₁ q ztbapi
  refine (FRS.seq (K₂ := 2 * wcK + 12) (wcand_inv hE hB hI₁ hA hBo hfr₁ hg by_omega
    by_omega (by rw [v₁]) zthfz)
    (fun c₂ hI₂ hA₂ ⟨iv₂, hw₂, _⟩ => ?_)).mono by_omega (fun _ h => h)
  refine (FRS.seq (K₂ := wcK + 6) (wTry_fs hE hB hI₂ hA hBo iv₂ ztwzn hg hL hgL hpA
    zthfz) (fun c₃ hI₃ hA₃ ⟨iv₃, m₃, t₃⟩ => ?_)).mono by_omega
    ztb
  refine (wTry_fs hE hB hI₃ hA hBo iv₃ ztxch hg hL hgL hpB
    zthfz).mono le_rfl (fun c₄ ⟨iv₄, m₄, t₄⟩ => ?_)
  obtain ⟨b1, b2, b3, b4⟩ := iv₄
  grind
