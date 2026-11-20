module

public import Chazelle.Core.RestoreFLeaf
public import Chazelle.Core.RestoreNodeDec

/-!
# WP-E, the search on the RAM (`FindOK`), part 22: the descent of a stretch

From the root of the piece's normal form, run nodes while the code `x` (`81150`) is even, then
run the leaf of the region `x / 2`.  A step counter (`81142`) bounds the number of nodes by the
depth of the decomposition; the continue bit (`81151`) is `1 - x mod 2`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs NFLoc

/-- Load the root code. -/
def rootL : List Instr :=
  [.addN 81150 81134 81016, .addN 81150 81150 81013, .loadN 81150 81150, .constN 81142 0]

/-- The parity of the code: `81121 = x / 2`, `81151 = 1 - x mod 2`. -/
def parS : Stmt :=
  .seq (Stmt.block [.copyN 81120 81150]) (.seq halfS (Stmt.block [.subN 81151 81012 81122]))

/-- The cost bound of `parS`. -/
def paK (E : FEnv) (x : ℕ) : ℕ := halfK E.P.n x + 2

variable {E : FEnv} {c₀ c : Config}

theorem halfK_mono {n x y : ℕ} (h : x ≤ y) : halfK n x ≤ halfK n y := by
  unfold halfK
  have := Nat.div_le_div_right (c := 2 * (n / 2)) h
  omega

theorem ndK_mono {x y : ℕ} (h : x ≤ y) : ndK E x ≤ ndK E y := by
  unfold ndK clK
  have := halfK_mono (n := E.P.n) h
  omega

theorem rootLoad_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {N : NF} (hN : NFWithin c₀.nmem (c.nreg 81134) (c₀.nreg ALLOC) N) :
    FRS B E.P E.W c₀ (Stmt.block rootL) c 4 (fun c' =>
      c'.nreg 81150 = N.root ∧ c'.nreg 81142 = 0 ∧
      ∀ q, q ≠ 81150 → q ≠ 81142 → c'.nreg q = c.nreg q) := by
  have hN' : NFWithin c.nmem (c.nreg 81134) (c₀.nreg ALLOC) N :=
    Robust.transport hN (fun a ha => hI.hm a ha)
  have hNA := hN'.nfAt
  obtain ⟨hB7, -⟩ := nf_bounds hN'
  have hB11 : c.nreg 81134 + 11 < c₀.nreg ALLOC :=
    robust_addr (v := N.dec.length) fun m' hm' => (hN m' hm').2.2.2.2.1
  have hA0 : c₀.nreg ALLOC ≤ c.nreg ALLOC := hI.hA
  have hAW : c.nreg ALLOC ≤ E.W := hI.hw.1 ALLOC
  have k7 : c.nreg 81016 = 7 := by rw [hI.hin _ (by unfold FFix; omega), hE.k7]
  have k2 : c.nreg 81013 = 2 := by rw [hI.hin _ (by unfold FFix; omega), hE.k2]
  have ok : okB E.W c.nmem rootL c.nreg := by
    simp only [rootL, okB, okI, regI, upd, FScr, FOut, k7, k2]; norm_num; omega
  refine (FRS.block hB _ hI ok).mono (by simp [rootL]) (fun c' h' => ?_)
  have e' : ∀ q, c'.nreg q = regB c.nmem rootL c.nreg q := fun q => by rw [h']
  refine ⟨?_, ?_, fun q h1 h2 => ?_⟩
  · rw [e']; simp [rootL, regB, regI, upd, k7, k2]; exact hNA.2.2.2.1
  · rw [e']; simp [rootL, regB, regI, upd]
  · rw [e']; simp [rootL, regB, regI, upd, h1, h2]

theorem parS_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hroom : c.nreg ALLOC + paK E (c.nreg 81150) ≤ E.W) :
    FRS B E.P E.W c₀ parS c (paK E (c.nreg 81150)) (fun c' =>
      c'.nreg 81121 = c.nreg 81150 / 2 ∧ c'.nreg 81151 = 1 - c.nreg 81150 % 2 ∧
      ∀ q, ¬ (81120 ≤ q ∧ q ≤ 81124) → q ≠ 81151 → c'.nreg q = c.nreg q) := by
  have ok1 : okB E.W c.nmem [.copyN 81120 81150] c.nreg := by
    simp only [okB, okI, FScr, FOut]; norm_num
  refine FRS.seq (K₂ := halfK E.P.n (c.nreg 81150) + 1) (FRS.block hB _ hI ok1)
    (fun c₁ hI₁ hA₁ h₁ => ?_) |>.mono (by unfold paK; simp; omega) (fun _ h => h)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.copyN 81120 81150] c.nreg q := fun q => by rw [h₁]
  have v20 : c₁.nreg 81120 = c.nreg 81150 := by rw [e₁]; simp [regB, regI, upd]
  have f₁ : ∀ q, q ≠ 81120 → c₁.nreg q = c.nreg q := fun q h => by
    rw [e₁]; simp [regB, regI, upd, h]
  have hA₁' : c₁.nreg ALLOC = c.nreg ALLOC := f₁ _ (by unfold ALLOC; omega)
  refine FRS.seq (K₂ := 1) (halfS_fs hE hB hI₁ v20 (by rw [hA₁']; unfold paK at hroom; omega))
    (fun c₂ hI₂ hA₂ ⟨h21, h22, f₂⟩ => ?_)
  have k1 : c₂.nreg 81012 = 1 := by rw [hI₂.hin _ (by unfold FFix; omega), hE.k1]
  have ok3 : okB E.W c₂.nmem [.subN 81151 81012 81122] c₂.nreg := by
    simp only [okB, okI, FScr, FOut]; norm_num
  refine (FRS.block hB _ hI₂ ok3).mono (by simp) (fun c' h' => ?_)
  have e' : ∀ q, c'.nreg q = regB c₂.nmem [.subN 81151 81012 81122] c₂.nreg q := fun q => by
    rw [h']
  refine ⟨?_, ?_, fun q h1 h2 => ?_⟩
  · rw [e']; simp [regB, regI, upd]; exact h21
  · rw [e']; simp [regB, regI, upd, k1, h22]
  · rw [e']; simp [regB, regI, upd, h2]
    rw [f₂ q (by omega) (by omega) (by omega) (by omega) (by omega), f₁ q (by omega)]

/-- A valid decomposition code. -/
def VCode (N : NF) (x : ℕ) : Prop :=
  (x % 2 = 0 ∧ x / 2 < N.nChords) ∨ (x % 2 = 1 ∧ x / 2 < N.nRegions)

theorem VCode.le {N : NF} {x : ℕ} (h : VCode N x) : x ≤ 2 * (N.nChords + N.nRegions) + 1 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- The registers the descent writes. -/
def DescW (q : ℕ) : Prop := NodeW q ∨ LeafW q ∨ q = 81151 ∨ q = 81142

/-- The completeness clause of the descent at the code `x` (from the descent's start `c`). -/
def DComp (E : FEnv) (c₀ c : Config) (Cα : Chain) (Nα : NF) (g g' L : ℕ) (f x : ℕ) : Prop :=
  ∀ (reg : ℕ → Set Point) (ai bi aj bj : ℝ) (dX : ℕ) (regα : ℕ → Set Point) (T : ℕ),
    DescGood E c₀ Cα Nα g g' L reg ai bi aj bj dX regα T →
    aj = E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩ →
    (0 < c.nreg 81141 ∨ c₀.nreg 81021 ≤ c.nreg 81140) → f = 1 ∨ Nα.Below x T

/-- **The invariant of the descent loop** (from the descent's start `c`). -/
def DInv (E : FEnv) (c₀ c : Config) (Cα : Chain) (Nα : NF) (g g' L : ℕ) (d : Config) : Prop :=
  FWin E d ∧ (∀ q, 81011 ≤ q → q < 83000 → ¬ DescW q → d.nreg q = c.nreg q) ∧
  (c.nreg 81007 = 1 → d.nreg 81007 = 1) ∧ VCode Nα (d.nreg 81150) ∧
  d.nreg 81151 = 1 - d.nreg 81150 % 2 ∧ d.nreg 81121 = d.nreg 81150 / 2 ∧
  Nα.parentCode^[d.nreg 81142] (d.nreg 81150) = Nα.root ∧
  (∀ t, t < d.nreg 81142 → Nα.parentCode^[t] (d.nreg 81150) ≠ Nα.root) ∧
  DComp E c₀ c Cα Nα g g' L (d.nreg 81007) (d.nreg 81150)

/-- The body of the descent loop. -/
def descBody (sT : Stmt) : Stmt :=
  .seq (nodeS sT) (.seq parS (Stmt.block [.addN 81142 81142 81012]))

/-- The largest code of a normal form. -/
def maxCode (N : NF) : ℕ := 2 * (N.nChords + N.nRegions) + 1

/-- The cost of a descent step. -/
def dbK (E : FEnv) (N : NF) : ℕ := ndK E (maxCode N) + paK E (maxCode N) + 1

theorem desc_body (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) {cs : Config}
    {Cα : Chain} {Hα : Host} {Nα : NF} {g g' L Dα Bα : ℕ}
    (hP : PCtx E c₀ Cα Hα Nα g g' L Dα Bα) (hR : SRegs cs g g' L Dα Bα) {dd : ℕ}
    (hDd : IsDecomp Nα dd)
    (hJ : cs.nreg 81140 < E.M.W.n ∧ ProperPos E.M (Qof E.P) E.P.n ⟨cs.nreg 81140, cs.nreg 81141⟩)
    (hdW : dd + 1 ≤ E.W)
    (hI : FInv E.W c₀ c) (hL : DInv E c₀ cs Cα Nα g g' L c) (hg : c.nreg 81011 < c.nreg 81151)
    (hroom : c.nreg ALLOC + dbK E Nα ≤ E.W) :
    FRS B E.P E.W c₀ (descBody E.sT) c (dbK E Nα) (fun c' => DInv E c₀ cs Cα Nα g g' L c' ∧
      dd + 1 - c'.nreg 81142 < dd + 1 - c.nreg 81142) := by
  obtain ⟨hw, fr, mo, hv, h51, h21, hpath, hnot, hcomp⟩ := hL
  have k0 := k0_of hE hI
  have hev : c.nreg 81150 % 2 = 0 := by rw [k0, h51] at hg; omega
  have hk : c.nreg 81150 / 2 < Nα.nChords := by rcases hv with h | h <;> omega
  have hx : c.nreg 81150 = 2 * (c.nreg 81150 / 2) := by omega
  -- the depth bound
  have hdep : c.nreg 81142 ≤ dd := by
    obtain ⟨j, hj, hjr⟩ := hDd.2.2.2.2.2.2.1 (c.nreg 81150) (fun _ => hk)
    by_contra h
    exact hnot j (by omega) hjr
  have nd : ∀ q, 81011 ≤ q → q < 83000 → ¬ DescW q → ¬ NodeW q := fun q _ _ h h' => h (Or.inl h')
  have rg : ∀ q, (81130 ≤ q ∧ q ≤ 81141) → c.nreg q = cs.nreg q := fun q h =>
    fr q (by omega) (by omega) (fun h' => by
      rcases h' with h' | h' | h' | h'
      · unfold NodeW KeyW VertW at h'; omega
      · unfold LeafW KeyW VertW at h'; omega
      · omega
      · omega)
  obtain ⟨r30, r31, r32, r33, r34, r35⟩ := hR
  have hRc : SRegs c g g' L Dα Bα := ⟨by rw [rg _ (by omega), r30], by rw [rg _ (by omega), r31],
    by rw [rg _ (by omega), r32], by rw [rg _ (by omega), r33], by rw [rg _ (by omega), r34],
    by rw [rg _ (by omega), r35]⟩
  have hJc : c.nreg 81140 < E.M.W.n ∧
      ProperPos E.M (Qof E.P) E.P.n ⟨c.nreg 81140, c.nreg 81141⟩ := by
    rw [rg _ (by omega), rg 81141 (by omega)]; exact hJ
  have hx' : 2 * (c.nreg 81150 / 2) ≤ maxCode Nα := by unfold maxCode; omega
  refine FRS.seq (K₁ := ndK E (2 * (c.nreg 81150 / 2))) (K₂ := paK E (maxCode Nα) + 1)
    (node_fs hE hB hBT hI hw hP hRc hJc hx hk (by
      have := ndK_mono (E := E) hx'; unfold dbK at hroom; omega))
    (fun c₂ hI₂ hA₂ ⟨w₂, f₂, m₂, lh₂, raw₂⟩ => ?_) |>.mono
    (by unfold dbK; have := ndK_mono (E := E) hx'; omega) (fun _ h => h)
  -- the child
  set k := c.nreg 81150 / 2 with hkdef
  have hchild : VCode Nα (c₂.nreg 81150) ∧ c₂.nreg 81150 ≠ Nα.root ∧
      Nα.parentCode (c₂.nreg 81150) = 2 * k := by
    have h9 := hDd.2.2.2.2.2.2.2.2.1 k hk (c₂.nreg 81150) lh₂
    refine ⟨h9.2, h9.1, ?_⟩
    rcases lh₂ with h | h <;> rw [h]
    · exact (hDd.2.2.1 k hk).1
    · exact (hDd.2.2.1 k hk).2
  obtain ⟨hv₂, hnr₂, hpar₂⟩ := hchild
  have hx₂ : c₂.nreg 81150 ≤ maxCode Nα := hv₂.le
  have hnd := ndK_mono (E := E) hx'
  have hpk : paK E (c₂.nreg 81150) ≤ paK E (maxCode Nα) := by
    have := halfK_mono (n := E.P.n) hx₂; unfold paK; omega
  have hroom2 : c₂.nreg ALLOC + paK E (c₂.nreg 81150) ≤ E.W := by unfold dbK at hroom; omega
  refine FRS.seq (K₂ := 1) (parS_fs hE hB hI₂ hroom2)
    (fun c₃ hI₃ hA₃ ⟨p21, p51, f₃⟩ => ?_) |>.mono
    (by unfold paK; have := halfK_mono (n := E.P.n) hx₂; omega) (fun _ h => h)
  have k1 : c₃.nreg 81012 = 1 := by rw [hI₃.hin _ (by unfold FFix; omega), hE.k1]
  have y42 : c₃.nreg 81142 = c.nreg 81142 := by
    rw [f₃ _ (by omega) (by norm_num), f₂ _ (by norm_num) (by norm_num)
      (by unfold NodeW KeyW VertW; omega)]
  have ok : okB E.W c₃.nmem [.addN 81142 81142 81012] c₃.nreg := by
    simp only [okB, okI, FScr, FOut, k1, y42]; norm_num; omega
  refine (FRS.block hB _ hI₃ ok).mono (by simp) (fun c₄ h₄ => ?_)
  have e₄ : ∀ q, c₄.nreg q = regB c₃.nmem [.addN 81142 81142 81012] c₃.nreg q := fun q => by
    rw [h₄]
  have f₄ : ∀ q, q ≠ 81142 → c₄.nreg q = c₃.nreg q := fun q h => by
    rw [e₄]; simp [regB, regI, upd, h]
  have v42 : c₄.nreg 81142 = c.nreg 81142 + 1 := by rw [e₄]; simp [regB, regI, upd, k1, y42]
  have z50 : c₄.nreg 81150 = c₂.nreg 81150 := by
    rw [f₄ _ (by norm_num), f₃ _ (by omega) (by norm_num)]
  have z07 : c₄.nreg 81007 = c₂.nreg 81007 := by
    rw [f₄ _ (by norm_num), f₃ _ (by omega) (by norm_num)]
  refine ⟨⟨w₂.congr' (fun q a b => by rw [f₄ q (by omega), f₃ q (by omega) (by omega)]),
    fun q a b hq => ?_, fun h => by rw [z07]; exact m₂ (mo h), by rw [z50]; exact hv₂,
    by rw [f₄ _ (by norm_num), p51, z50], by rw [f₄ _ (by norm_num), p21, z50],
    by rw [v42, z50, Function.iterate_succ_apply, hpar₂, ← hx]; exact hpath, fun t ht => ?_,
    fun reg ai bi aj bj dX regα T hD hJ' hJr' => ?_⟩, by rw [v42]; omega⟩
  · rw [f₄ q (fun h => hq (Or.inr (Or.inr (Or.inr h)))),
      f₃ q (fun h => hq (Or.inl (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
        (fun h => hq (Or.inr (Or.inr (Or.inl h)))), f₂ q a b (nd q a b hq), fr q a b hq]
  · rw [v42] at ht
    rw [z50]
    rcases Nat.eq_zero_or_pos t with rfl | htp
    · exact hnr₂
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      rw [Function.iterate_succ_apply, hpar₂, ← hx]
      exact hnot s (by omega)
  · rw [z07, z50]
    rcases hcomp reg ai bi aj bj dX regα T hD hJ' hJr' with h | hb
    · exact Or.inl (m₂ h)
    · by_cases hf₂ : c₂.nreg 81007 = 1
      · exact Or.inl hf₂
      · right
        have h0 : c₂.nreg 81007 = 0 := by have := w₂.1; omega
        rw [hx] at hb
        exact node_dec hE hP hRc hD (by rw [rg 81140 (by omega), rg 81141 (by omega)]; exact hJ')
          (by rw [rg 81140 (by omega), rg 81141 (by omega)]; exact hJr') hw hk hb raw₂ h0

/-- **The descent of a stretch.** -/
def descS (sT : Stmt) : Stmt :=
  .seq (Stmt.block rootL) (.seq parS (.seq (.whileLtN 81011 81151 (descBody sT)) (leafS sT)))

/-- A bound on the leaf steps of every region. -/
noncomputable def lmuB (Cα : Chain) (Q : Polygon) (N : NF) : ℕ :=
  (Finset.range N.nRegions).sup (fun r => lmu Cα Q N r (2 * Cα.m + 7))

/-- The cost bound of the descent. -/
noncomputable def descK (E : FEnv) (Cα : Chain) (N : NF) (dd : ℕ) : ℕ :=
  4 + (paK E (maxCode N) + (((dbK E N + 2) * (dd + 1) + 2) +
    (15 + ((lbK E + 2) * lmuB Cα (Qof E.P) N + 2))))

theorem desc_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    {Cα : Chain} {Hα : Host} {Nα : NF} {g g' L Dα Bα : ℕ}
    (hP : PCtx E c₀ Cα Hα Nα g g' L Dα Bα) (hR : SRegs c g g' L Dα Bα) {dd : ℕ}
    (hDd : IsDecomp Nα dd) (hdW : dd + 1 ≤ E.W)
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M (Qof E.P) E.P.n ⟨c.nreg 81140, c.nreg 81141⟩)
    (hnW : 2 * E.M.W.n ≤ E.W) (h2α : 2 * (2 * Cα.m + 7) ≤ E.W)
    (hWa : ∀ r, r < Nα.nRegions → 2 * (2 * Cα.m + 7) + (Nα.region r).arcs.length ≤ E.W)
    (hroom : c.nreg ALLOC + descK E Cα Nα dd ≤ E.W) :
    FRS B E.P E.W c₀ (descS E.sT) c (descK E Cα Nα dd) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ DescW q → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      ∀ (reg : ℕ → Set Point) (ai bi aj bj : ℝ) (dX : ℕ) (regα : ℕ → Set Point) (T : ℕ),
        DescGood E c₀ Cα Nα g g' L reg ai bi aj bj dX regα T →
        aj = E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩ →
        (0 < c.nreg 81141 ∨ c₀.nreg 81021 ≤ c.nreg 81140) → c'.nreg 81007 = 1) := by
  have hR' := hR
  obtain ⟨r30, r31, r32, r33, r34, r35⟩ := hR
  have k0c := k0_of hE hI
  have hv0 : VCode Nα Nα.root := hDd.2.2.2.2.2.2.2.2.2
  -- the root
  refine FRS.seq (K₁ := 4) (K₂ := descK E Cα Nα dd - 4)
    (rootLoad_fs hE hB hI (N := Nα) (by rw [r34]; exact hP.hNW))
    (fun c₁ hI₁ hA₁ ⟨v50, v42, f₁⟩ => ?_) |>.mono (by unfold descK; omega) (fun _ h => h)
  have hpk : paK E (c₁.nreg 81150) ≤ paK E (maxCode Nα) := by
    have := halfK_mono (n := E.P.n) (v50 ▸ hv0.le : c₁.nreg 81150 ≤ maxCode Nα); unfold paK; omega
  refine FRS.seq (K₁ := paK E (c₁.nreg 81150))
    (K₂ := ((dbK E Nα + 2) * (dd + 1) + 2) + (15 + ((lbK E + 2) * lmuB Cα (Qof E.P) Nα + 2)))
    (parS_fs hE hB hI₁ (by unfold descK at hroom; omega))
    (fun c₂ hI₂ hA₂ ⟨p21, p51, f₂⟩ => ?_) |>.mono (by unfold descK; omega) (fun _ h => h)
  have g₂ : ∀ q, 81011 ≤ q → q < 83000 → ¬ DescW q → c₂.nreg q = c.nreg q := fun q a b hq => by
    rw [f₂ q (fun h => hq (Or.inl (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
      (fun h => hq (Or.inr (Or.inr (Or.inl h)))),
      f₁ q (fun h => hq (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))))
        (fun h => hq (Or.inr (Or.inr (Or.inr h))))]
  have y50 : c₂.nreg 81150 = Nα.root := by
    rw [f₂ _ (by omega) (by norm_num), v50]
  have y42 : c₂.nreg 81142 = 0 := by
    rw [f₂ _ (by omega) (by norm_num), v42]
  have e07 : ∀ q, 81007 ≤ q → q ≤ 81010 → c₂.nreg q = c.nreg q := fun q a b => by
    rw [f₂ q (by omega) (by omega), f₁ q (by omega) (by omega)]
  have hL₂ : DInv E c₀ c Cα Nα g g' L c₂ := by
    refine ⟨hw.congr' e07, g₂, fun h => by rw [e07 _ le_rfl (by norm_num)]; exact h,
      by rw [y50]; exact hv0, by rw [p51, v50, y50],
      by rw [p21, v50, y50], by rw [y42, y50]; rfl, fun t ht => by rw [y42] at ht; omega,
      fun reg ai bi aj bj dX regα T hD _ _ => Or.inr (by rw [y50]; exact below_root hDd hD.hT)⟩
  -- the loop
  have nDW : ∀ q, (q = 81011 ∨ (81130 ≤ q ∧ q ≤ 81141) ∨ q = 81007) → ¬ DescW q := fun q hq h => by
    rcases h with h | h | h | h
    · unfold NodeW KeyW VertW at h; omega
    · unfold LeafW KeyW VertW at h; omega
    · omega
    · omega
  refine FRS.seq (K₁ := (dbK E Nα + 2) * (dd + 1) + 2)
    (K₂ := 15 + ((lbK E + 2) * lmuB Cα (Qof E.P) Nα + 2))
    ((FRS.while (a := 81011) (b := 81151) (body := descBody E.sT) (DInv E c₀ c Cα Nα g g' L)
      (fun d => dd + 1 - d.nreg 81142) (dbK E Nα) (fun d hd hgd => ?_)
      (fun d hId hd hgd hroomd => desc_body hE hB hBT hP hR' hDd hJ hdW hId hd hgd hroomd)
      hI₂ hL₂ (by rw [y42, Nat.sub_zero]; unfold descK at hroom; omega)).mono
      (by rw [y42, Nat.sub_zero]) (fun _ h => h))
    (fun c₃ hI₃ hA₃ ⟨hL₃, hex⟩ => ?_) |>.mono le_rfl (fun _ h => h)
  · obtain ⟨-, frd, -, hvd, h51d, -, -, hnotd, -⟩ := hd
    rw [frd _ (by norm_num) (by norm_num) (nDW _ (Or.inl rfl)), k0c, h51d] at hgd
    have hk : d.nreg 81150 / 2 < Nα.nChords := by rcases hvd with h | h <;> omega
    obtain ⟨j, hj, hjr⟩ := hDd.2.2.2.2.2.2.1 (d.nreg 81150) (fun _ => hk)
    have : d.nreg 81142 ≤ j := by
      by_contra h
      exact hnotd j (by omega) hjr
    omega
  obtain ⟨hw₃, fr₃, mo₃, hv₃, h51₃, h21₃, -, -, hcomp₃⟩ := hL₃
  rw [fr₃ _ (by norm_num) (by norm_num) (nDW _ (Or.inl rfl)), k0c, h51₃] at hex
  have hodd : c₃.nreg 81150 % 2 = 1 := by omega
  have hrn : c₃.nreg 81150 / 2 < Nα.nRegions := by rcases hv₃ with h | h <;> omega
  have rg₃ : ∀ q, (81130 ≤ q ∧ q ≤ 81141) → c₃.nreg q = c.nreg q := fun q h =>
    fr₃ q (by omega) (by omega) (nDW q (Or.inr (Or.inl h)))
  have hR₃ : SRegs c₃ g g' L Dα Bα := ⟨by rw [rg₃ _ (by omega), r30], by rw [rg₃ _ (by omega), r31],
    by rw [rg₃ _ (by omega), r32], by rw [rg₃ _ (by omega), r33], by rw [rg₃ _ (by omega), r34],
    by rw [rg₃ _ (by omega), r35]⟩
  have hlm : lmu Cα (Qof E.P) Nα (c₃.nreg 81150 / 2) (2 * Cα.m + 7) ≤ lmuB Cα (Qof E.P) Nα :=
    Finset.le_sup (f := fun r => lmu Cα (Qof E.P) Nα r (2 * Cα.m + 7)) (Finset.mem_range.2 hrn)
  have hlm' := Nat.mul_le_mul_left (lbK E + 2) hlm
  refine (leaf_fs hE hB hBT hI₃ hw₃ hP hR₃ h21₃ hrn hnW h2α (hWa _ hrn)
    (by unfold descK at hroom; omega)).mono (by omega)
    (fun c' ⟨w', f', m', gl⟩ => ⟨w', fun q a b hq => by
      rw [f' q a b (fun h => hq (Or.inr (Or.inl h))), fr₃ q a b hq], fun h => m' (mo₃ h), ?_⟩)
  intro reg ai bi aj bj dX regα T hD hJa hJr
  rcases hcomp₃ reg ai bi aj bj dX regα T hD hJa hJr with h | hb
  · exact m' h
  have hx2 : c₃.nreg 81150 = 2 * (c₃.nreg 81150 / 2) + 1 := by omega
  rw [hx2] at hb
  have hrT := leaf_target hDd hrn hD.hT hb
  have hS := hP.hS
  have hsimp : Cα.P.Simple := by rw [hP.hQ]; exact (shearInvariance (epsOf E.P) E.P).1 hE.hG.1
  have hGα : GoodModel (chainModel Cα) := Or.inl ⟨Cα, hsimp, rfl⟩
  have hnα : (chainModel Cα).W.n = 2 * Cα.m + 7 := Stretch.nα Cα
  have hXn : g' + dX < (chainModel Cα).W.n := by
    rw [hnα]; have := hD.hXL; have := hS.hgL; omega
  obtain ⟨t, ht, hjt, hcl⟩ := arc_of_target hGα hP.hNα hD hXn
  rw [← hrT] at ht hjt hcl
  refine gl t ht (g' + dX) ⟨by have := hD.hX0; omega, by have := hD.hXL; omega, reg, hD.hregs,
    hD.hch, ?_, ?_⟩ ?_
  · rw [show g' + dX - g' = dX by omega]
    intro C hC
    exact hD.hinB C hC (hS.memM hD.hXL le_rfl one_pos)
  · rw [show g' + dX - g' = dX by omega]; exact hD.hgX
  · intro w hw
    unfold lj at hw ⊢
    obtain ⟨-, -, -, regβ, -, -, -, -, -, -, hpp⟩ := hP.hNα
    obtain ⟨hs, he⟩ := hpp _ hjt
    obtain ⟨ese, eee⟩ := arc_edges hP.hNα hjt
    rw [hnα] at ese eee hXn
    exact arc_int ese eee (by unfold Model.key; linarith [hs.1]) (by unfold Model.key; linarith [hs.2.1])
      (by unfold Model.key; linarith [he.1]) (by unfold Model.key; linarith [he.2.1]) hw hXn hcl

end

end Restore

end Chazelle.Core
