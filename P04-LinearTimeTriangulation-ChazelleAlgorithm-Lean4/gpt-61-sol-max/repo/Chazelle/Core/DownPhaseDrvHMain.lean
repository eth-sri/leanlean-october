module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvHLoop

/-!
# Down-phase driver, host RAM (D3a), part 8: the contract

`DrvH.hostRamSpec : DrvR.HostRamSpec`.  The program `hostS` (`DownPhaseDrvHProg`): `setupS`
(`setupS_exec`), the arc loop (`arcLoop_exec`), the host handle (`finS_exec`), the copy
(`cpyLoop_exec`) and the padding (`padLoopH_exec`); cost at most `3000`.  The contract quantifies
over every chord list whose normal form is readable at the handle; its host is the one computed,
since the layout determines the chord, arc and region records (`nfAt_recs`, `regHost_congr`).
-/

namespace Chazelle.Core

namespace DrvH

open Machine Machine.Stmt Programs BuildRam DrvR

@[expose] public section

/-- Lists with the same length and entries are equal. -/
theorem list_ext_getD {α : Type} {l l' : List α} (x : α) (hl : l.length = l'.length)
    (h : ∀ i, i < l.length → l.getD i x = l'.getD i x) : l = l' :=
  List.ext_getElem hl fun i h1 h2 => by
    simp_all

/-- **The layout determines the records**: two normal forms readable at the same handle have the
same chord, arc and region records. -/
theorem nfAt_recs {m : ℕ → ℕ} {B : ℕ} {N N' : NF} (h : NFAt m B N) (h' : NFAt m B N') :
    N.chords = N'.chords ∧ N.arcs = N'.arcs ∧ N.regions = N'.regions := by
  obtain ⟨c0, a0, r0, -, -, hc, ha, hr, -⟩ := h
  obtain ⟨c0', a0', r0', -, -, hc', ha', hr', -⟩ := h'
  refine ⟨list_ext_getD ⟨0, 0, 0, 0, 0⟩ (by omega) fun i hi => ?_,
    list_ext_getD ⟨0, ⟨0, 0⟩, ⟨0, 0⟩⟩ (by omega) fun j hj => ?_,
    list_ext_getD ⟨[], [], 0⟩ (by omega) fun q hq => ?_⟩
  · obtain ⟨a1, a2, a3, a4, a5⟩ := hc i hi
    obtain ⟨b1, b2, b3, b4, b5⟩ := hc' i (by omega)
    change N.chord i = N'.chord i
    rcases hx : N.chord i with ⟨x1, x2, x3, x4, x5⟩
    rcases hy : N'.chord i with ⟨y1, y2, y3, y4, y5⟩
    rw [hx] at a1 a2 a3 a4 a5; rw [hy] at b1 b2 b3 b4 b5
    simp only at a1 a2 a3 a4 a5 b1 b2 b3 b4 b5
    simp only [CRec.mk.injEq]; omega
  · obtain ⟨a1, a2, a3, a4, a5⟩ := ha j hj
    obtain ⟨b1, b2, b3, b4, b5⟩ := ha' j (by omega)
    change N.arc j = N'.arc j
    rcases hx : N.arc j with ⟨x1, ⟨x2, x3⟩, ⟨x4, x5⟩⟩
    rcases hy : N'.arc j with ⟨y1, ⟨y2, y3⟩, ⟨y4, y5⟩⟩
    rw [hx] at a1 a2 a3 a4 a5; rw [hy] at b1 b2 b3 b4 b5
    simp only at a1 a2 a3 a4 a5 b1 b2 b3 b4 b5
    simp only [ARec.mk.injEq, WPos.mk.injEq]; omega
  · obtain ⟨a1, a2, a3, a4, a5⟩ := hr q hq
    obtain ⟨b1, b2, b3, b4, b5⟩ := hr' q (by omega)
    change N.region q = N'.region q
    have harcs : (N.region q).arcs = (N'.region q).arcs :=
      list_ext_getD 0 (by omega) fun t ht => by rw [← a4 t ht, ← b4 t (by omega)]
    have hchs : (N.region q).chords = (N'.region q).chords :=
      list_ext_getD 0 (by omega) fun t ht => by rw [← a5 t ht, ← b5 t (by omega)]
    rcases hx : N.region q with ⟨x1, x2, x3⟩
    rcases hy : N'.region q with ⟨y1, y2, y3⟩
    rw [hx, hy] at harcs hchs; rw [hx] at a3; rw [hy] at b3
    simp only at harcs hchs a3 b3
    simp only [RRec.mk.injEq]; exact ⟨harcs, hchs, by omega⟩

/-- `regHost` reads only the chord, arc and region records. -/
theorem regHost_congr {N N' : NF} (hc : N.chords = N'.chords) (ha : N.arcs = N'.arcs)
    (hr : N.regions = N'.regions) (li : Bool) (n r : ℕ) :
    regHost li n N r = regHost li n N' r := by
  obtain ⟨c, a, g, s, d, o, l⟩ := N
  aesop

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The setup**: constants, bases of the normal form and the record of region `r`. -/
theorem setupS_exec (c : Config) (hw : WordsBounded W c) {B r A₀ : ℕ}
    (h00 : c.nreg 215000 = B) (h01 : c.nreg 215001 = r) (hA₀ : c.nreg 9999 = A₀)
    (hB7 : B + 7 < A₀) (hR : c.nmem (B + 5) + 5 * r + 4 < A₀) (hnW : P.n ≤ W)
    (hAW : A₀ + 4 ≤ W) :
    ∃ d k, Exec P W setupS c d k ∧ k = 33 ∧ d.nreg 215020 = 1 ∧ d.nreg 215021 = P.n ∧
      d.nreg 215022 = 0 ∧ d.nreg 215023 = 3 ∧ d.nreg 215024 = 2 ∧
      d.nreg 215025 = c.nmem (B + 3) ∧ d.nreg 215026 = c.nmem (B + 4) ∧
      d.nreg 215027 = c.nmem (B + 7) ∧
      d.nreg 215030 = c.nmem (c.nmem (B + 5) + 5 * r) ∧
      d.nreg 215028 = c.nmem (c.nmem (B + 5) + 5 * r + 1) ∧
      d.nreg 215031 = c.nmem (c.nmem (B + 5) + 5 * r + 2) ∧
      d.nreg 215029 = c.nmem (c.nmem (B + 5) + 5 * r + 3) ∧
      d.nreg 215032 = A₀ ∧ d.nreg 215040 = A₀ ∧ d.nreg 215011 = 0 ∧ d.nreg 215012 = 0 ∧
      d.nreg 215041 = 0 ∧ d.nreg 215002 = c.nreg 215002 ∧ d.nreg 9999 = A₀ ∧ d.nmem = c.nmem ∧
      FrameM Ball c d := by
  obtain ⟨d, k, ex, hk, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
      h17, h18, h19, hm⟩ : ∃ d k, Exec P W setupS c d k ∧ k = 33 ∧ d.nreg 215020 = 1 ∧
      d.nreg 215021 = P.n ∧
      d.nreg 215022 = 0 ∧ d.nreg 215023 = 3 ∧ d.nreg 215024 = 2 ∧
      d.nreg 215025 = c.nmem (B + 3) ∧ d.nreg 215026 = c.nmem (B + 4) ∧
      d.nreg 215027 = c.nmem (B + 7) ∧
      d.nreg 215030 = c.nmem (c.nmem (B + 5) + 5 * r) ∧
      d.nreg 215028 = c.nmem (c.nmem (B + 5) + 5 * r + 1) ∧
      d.nreg 215031 = c.nmem (c.nmem (B + 5) + 5 * r + 2) ∧
      d.nreg 215029 = c.nmem (c.nmem (B + 5) + 5 * r + 3) ∧
      d.nreg 215032 = A₀ ∧ d.nreg 215040 = A₀ ∧ d.nreg 215011 = 0 ∧ d.nreg 215012 = 0 ∧
      d.nreg 215041 = 0 ∧ d.nreg 215002 = c.nreg 215002 ∧ d.nreg 9999 = A₀ ∧ d.nmem = c.nmem := by
    unfold setupS
    exec_block
    all_goals try (config_simp; (try simp only [h00, h01, add_5, add_1_1]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
      config_simp <;> simp only [h00, h01, add_5, add_1_1, hA₀]
  exact ⟨d, k, ex, hk, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, hm, exec_frameM ex wrM_setupS⟩


end exec

set_option maxHeartbeats 4000000 in
/-- **D3a: the host RAM.** -/
theorem hostRamSpec : DrvR.HostRamSpec := by
  refine ⟨hostS, 3000, ?_⟩
  intro P W c hw hPre hroom
  obtain ⟨hG, hWn, hli1, -, L, E, hLne, hL, hperm, hsort, hdeg, hNW, hr⟩ := hPre
  have hAL : ALLOC = 9999 := rfl
  rw [hAL] at hNW hroom
  have hroom' : c.nreg 9999 + 3000 ≤ W := hroom
  have hWn' : 256 * P.n + 16 ≤ W := hWn
  have hn3 : 3 ≤ P.n := hG.1.1
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hG.1
  have hqn : (Qof P).n = P.n := shear_n _ _
  have hF : HFacts P.n (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) (c.nreg 215001) :=
    hqn ▸ hfacts_of hQ hLne hL hperm hsort hdeg hr
  generalize hNdef : BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E = N at hF hNW hr
  generalize hlidef : decide (c.nreg 215002 = 1) = li
  have hliv : c.nreg 215002 = if li then 1 else 0 := by
    grind
  have hN := hNW.nfAt
  obtain ⟨hb7, hbc, hba, hbr, hbra, hbrc⟩ := Restore.nf_bounds hNW
  obtain ⟨-, -, -, -, -, hNc, hNa, hNr, -⟩ := hN
  -- setup
  obtain ⟨d₁, k₁, e₁, hk₁, s20, s21, s22, s23, s24, s25, s26, s27, s30, s28, s31, s29, s32, s40,
    s11, s12, s41, s02, s99, sm, f₁⟩ := setupS_exec (P := P) c hw rfl rfl rfl hb7
    (hbr _ hr) (by omega) (by omega)
  have K₁ : Kst P.n li d₁ := ⟨s20, s21, s22, s23, s24, by omega⟩
  have hE₁ : HEnv W P.n N (c.nreg 215001) li (c.nreg 9999) d₁ := by
    refine ⟨K₁, hF, by rw [s30]; exact (hNr _ hr).1, by rw [s31]; exact (hNr _ hr).2.1, s32,
      fun t ht => ?_, fun v hv => ?_, fun j hj => ?_, fun i hi => ?_, by omega, by omega,
      by omega⟩
    · rw [sm, s27, s28, ← Nat.add_assoc]
      exact ⟨(hNr _ hr).2.2.2.1 t ht, hbra _ hr t ht⟩
    · rw [sm, s27, s29, ← Nat.add_assoc]
      exact ⟨(hNr _ hr).2.2.2.2 v hv, hbrc _ hr v hv⟩
    · ram_simp
    · rw [sm, s25]
      obtain ⟨a1, a2, a3, a4, a5⟩ := hNc i hi
      exact ⟨a1, a2, a3, by have := hbc i hi; omega⟩
  have hB₁ : Buf P.n (c.nreg 9999) [] d₁ := ⟨ItemsAt.nil _ _, by omega,
    by omega, by rw [s12]; rfl⟩
  -- the arc loop
  obtain ⟨d₂, k₂, e₂, hk₂, B₂, E₂, m₂, f₂⟩ := arcLoop_exec (P := P) d₁ e₁.wb_right hE₁ s41 hB₁
  have hK20 : (walkItems li P.n N (c.nreg 215001)).length ≤ 20 := by
    have := pre_length_le li P.n N (c.nreg 215001) (N.region (c.nreg 215001)).arcs.length
    rw [pre_full] at this
    have := hF.hA
    omega
  generalize hxs : walkItems li P.n N (c.nreg 215001) = xs at B₂ hK20
  -- the host handle
  obtain ⟨d₃, k₃, e₃, hk₃, v10, vm₃, v80, v82, v81, v83, v84, f₃⟩ := finS_exec (P := P) d₂
    e₂.wb_right E₂.K B₂.2.1 B₂.2.2.1 E₂.tR (by omega)
  have K₃ := E₂.K.frame f₃ (by decide)
  have I₃ : ItemsAt d₃.nmem (c.nreg 9999) xs := B₂.1.congr fun a h1 h2 => by
    rw [vm₃, Machine.upd_other _ _ _ (by omega)]
  -- the copy
  obtain ⟨d₄, k₄, e₄, hk₄, I₄, w82, m₄, f₄⟩ := cpyLoop_exec (P := P) d₃ e₃.wb_right K₃ I₃
    (by rw [f₃.1 _ (by decide), B₂.2.2.1]) v80 v82 v81 v83 v84 (by omega)
  -- the padding
  have p20 : d₄.nreg 215020 = 1 := by rw [f₄.1 _ (by decide), K₃.one]
  have p99 : d₄.nreg 9999 = c.nreg 9999 := by
    rw [f₄.1 _ (by decide), f₃.1 _ (by decide), f₂.1 _ (by decide), s99]
  have e₅ := padLoopH_exec (P := P) (6 * xs.length + 1) d₄ e₄.wb_right p20 (by omega)
    (by omega)
  have ex : Exec P W hostS c { d₄ with nreg := upd d₄.nreg 9999 (d₄.nreg 215082) }
      (k₁ + (k₂ + (k₃ + (k₄ + (3 * (6 * xs.length + 1) + 2))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  have fA := exec_frameM ex wrM_hostS
  have fR := exec_frameM2 ex wrM2_hostS
  have g₄ : ∀ q, Bcp q = false → d₄.nreg q = d₃.nreg q := f₄.1
  have a99 : (upd d₄.nreg 9999 (d₄.nreg 215082)) 9999 = c.nreg 9999 + 6 * xs.length + 1 := by
    ram_simp
  have a10 : (upd d₄.nreg 9999 (d₄.nreg 215082)) 215010 = c.nreg 9999 + 3 * xs.length := by
    ram_simp
  have a11 : (upd d₄.nreg 9999 (d₄.nreg 215082)) 215011 = xs.length := by
    rw [Machine.upd_other _ _ _ (by decide), g₄ _ (by decide), f₃.1 _ (by decide), B₂.2.2.1]
  have a12 : (upd d₄.nreg 9999 (d₄.nreg 215082)) 215012 = ptsLen P.n xs := by
    rw [Machine.upd_other _ _ _ (by decide), g₄ _ (by decide), f₃.1 _ (by decide), B₂.2.2.2]
  have hmem : ∀ a, a < c.nreg 9999 → d₄.nmem a = c.nmem a := fun a ha => by
    rw [m₄ a (by omega), vm₃, Machine.upd_other _ _ _ (by omega), m₂ a ha, sm]
  have hHB : d₄.nmem (c.nreg 9999 + 3 * xs.length) = xs.length := by
    ram_simp
  refine ⟨_, _, ex, show _ ≤ 3000 by omega, ⟨fun q hq hq' => fA.1 q ?_,
    fun L' E' hLne' hL' hperm' hsort' hNA' => ?_⟩,
    ⟨fun q hq hqA => fA.1 q ?_, fun q _ => fR q rfl, hmem, fun a _ => by rw [fA.2.2.1],
      fA.2.2.2, by simp only [hAL, a99]; omega,
      by simp only [hAL, a99]; omega⟩⟩
  · simp only [bandOf, bDownDrv] at hq
    simp only [Ball, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  · have hrec := nfAt_recs hNA' hNW.nfAt
    have hH : regHost li (Qof P).n (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L' E')
        (c.nreg 215001) = if li then xs else xs.reverse := by
      rw [regHost_congr hrec.1 hrec.2.1 hrec.2.2, hqn, ← hxs]; rfl
    dsimp only
    rw [hlidef, hH]
    have hl : (if li then xs else xs.reverse).length = xs.length := by split_ifs <;> simp
    simp only [hAL, a99, a10, a11, a12, hl]
    refine ⟨by omega, by omega, hostAt_of (by rw [hHB, hl]) I₄, trivial, ?_⟩
    rw [hqn]
    split_ifs
    · rfl
    · exact (ptsLen_reverse P.n xs).symm
  · simp only [Finset.mem_singleton, bandOf, bDownDrv] at hq
    simp only [Ball, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega

end

end DrvH

end Chazelle.Core
