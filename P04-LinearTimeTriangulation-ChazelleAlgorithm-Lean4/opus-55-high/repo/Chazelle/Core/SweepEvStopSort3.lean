module

public import Chazelle.MacT
public import Chazelle.Core.SweepEvStepL5
public import Chazelle.Core.SweepEvEnv
public import Chazelle.Core.SweepEvGenR
public import Chazelle.Core.SweepEvBatch
public import Chazelle.Core.RestoreTHoleChain
public import Chazelle.Core.SweepEvWinM2
public import Chazelle.Core.SweepEvOrg
public import Chazelle.Core.RestoreFComplete2

namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop SortR
@[expose] public section
theorem ss_getD_snoc {α : Type} (l : List α) (x d : α) (i : ℕ) :
    (l ++ [x]).getD i d = if i < l.length then l.getD i d else if i = l.length then x else d := by
  grind
theorem KLe.antisymm' {a b : ℝ × ℕ} (h1 : KLe a b) (h2 : KLe b a) : a = b := by
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · grind
  · simp_all
  · simp_all
  grind

/-! ## The program of the pass -/

/-- Check the record of `srX` against the previous one (`srP`); write it unless the keys agree. -/
def ssChk : Stmt :=
  .seq (block [.copyN 30000 srX, .copyN 30001 srP]) (.seq ssCmp (.ifLtN K0 30002 .skip ssWr))

/-- One step of the pass. -/
def ssBody : Stmt :=
  .seq (block [.addN srA srSB srJ, .loadN srX srA])
    (.seq (.ifLtN K0 srJ ssChk ssWr) (block [.copyN srP srX, .addN srJ srJ K1]))

/-- **The dedupe pass.** -/
def ssDedup : Stmt := .whileLtN srJ gRC ssBody

/-! ## Records -/
variable {m m' : ℕ → ℕ} {A : ℕ} {O : List (ℕ × ℕ × ℕ × ℕ × ℕ)} {x : ℕ × ℕ × ℕ × ℕ × ℕ}
theorem stopRecs_snoc
 (h : StopRecsAt m A O)
    (hk : ∀ a, A ≤ a → a < A + 5 * O.length → m' a = m a)
    (hn : m' ztpvn = x.1 ∧ m' ztnii = x.2.1 ∧
      m' ztnij = x.2.2.1 ∧ m' ztnik = x.2.2.2.1 ∧
      m' ztnil = x.2.2.2.2) : StopRecsAt m' A (O ++ [x]) := by
  zug
  zumoy
  zuvw
  zupi
  · zudin

  · simp_all
  · omega
theorem auxRecs_snoc
 (h : AuxRecsAt m A O)
    (hk : ∀ a, A ≤ a → a < A + 5 * O.length → m' a = m a)
    (hn : m' ztpvn = x.1 ∧ m' ztnii = x.2.1 ∧
      m' ztnij = x.2.2.1 ∧ m' ztnik = x.2.2.2.1 ∧
      m' ztnil = x.2.2.2.2) : AuxRecsAt m' A (O ++ [x]) := by
  zug
  zumoy
  zuvw
  zupi
  · zudin

  · simp_all
  · omega

/-! ## The invariant of the pass -/

/-- **The state of the pass after `j` indices** of `L` (from the entry configuration `d₀`). -/
structure SsDI (P : Polygon) (W : ℕ) (J : Merge.Junction) (d2 RB S A₀ : ℕ) (m₀ : ℕ → ℕ)
    (L : List ℕ) (SBv B1 : ℕ) (d₀ : Config) (j : ℕ) (d : Config) : Prop where
  wb : WordsBounded W d
  qj : d.nreg srJ = j
  ctx : SsCtx J d2 RB S A₀ m₀ d
  sb : d.nreg srSB = SBv
  b1 : d.nreg sB = B1
  b2 : d.nreg aB = B1 + 5 * S
  mem : ∀ a, a < B1 → d.nmem a = d₀.nmem a
  recs : ∃ O, DInv ztqwu L j O ∧ d.nreg sC = O.length ∧ O.length ≤ j ∧
    (0 < j → ∃ x', L[j - 1]? = some x' ∧ d.nreg srP = x') ∧
    StopRecsAt d.nmem B1 ztbaep ∧ AuxRecsAt d.nmem ztgde ztbaeo
  regs : ∀ r, bandOf r ∉ oracleBands → ztbnj → r ≠ sC →
    d.nreg r = d₀.nreg r
  rr : ∀ r, bandOf r ∉ oracleBands → d.rreg r = d₀.rreg r
  rm : d.rmem = d₀.rmem
  out : d.output = d₀.output
set_option maxRecDepth 20000 in
/-- **Writing a record keeps the invariant** (the item `x = L[j]` with a new key). -/
theorem ssWr_step {P : Polygon} {W : ℕ} {J : Merge.Junction} {d2 RB S A₀ : ℕ} {m₀ : ℕ → ℕ}
    {B1 : ℕ} {d₀ d : Config} {O : List ℕ} {x : ℕ}
    (hw : WordsBounded W d) (hS : RB + 11 * S ≤ A₀) (hAB : A₀ ≤ B1) (hroom : B1 + 10 * S + 1 ≤ W)
    (hctx : SsCtx J d2 RB S A₀ m₀ d) (hb1 : d.nreg sB = B1) (hb2 : d.nreg aB = B1 + 5 * S)
    (_hmem : ∀ a, a < B1 → d.nmem a = d₀.nmem a) (hx : d.nreg srX = x) (hxS : x < S)
    (hC : d.nreg sC = O.length) (hO : O.length < S)
    (hst : StopRecsAt d.nmem B1 ztbaep)
    (hax : AuxRecsAt d.nmem ztgde ztbaeo) :
    ∃ d' k, Exec P W ssWr d d' k ∧ k = 53 ∧ d'.nreg sC = (O ++ [x]).length ∧
      StopRecsAt d'.nmem B1 ((O ++ [x]).map ztkdx) ∧
      AuxRecsAt d'.nmem ztgde ((O ++ [x]).map ztkdw) ∧
      (∀ a, a < B1 → d'.nmem a = d.nmem a) ∧
      (∀ r, r ≠ sr1 → r ≠ sr2 → r ≠ sr3 → r ≠ sr4 → r ≠ srS → r ≠ srD → r ≠ srE → r ≠ srV → r ≠ sC →
        d'.nreg r = d.nreg r) ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  obtain ⟨-, -, hRB, -, -, hK1, -, hm⟩ := hctx
  obtain ⟨d', k, ex, hk, hmem', hsC, hr, hrr, hrm, ho⟩ := ssWr_exec (P := P) hw hK1
    by_omega by_omega
    by_omega
  rw [hRB, hx, hb1, hb2, hC] at hmem'
  have src : ∀ u, u < 11 → d.nmem ztnop = m₀ ztnop := fun u hu =>
    hm _ by_omega
  have wD : ∀ t, t < 5 → d'.nmem (B1 + 5 * O.length + t) = m₀ (RB + 11 * x + ssOff t) :=
    fun t ht => by
      zujji
      rw [ite_eq_left by_omega, show B1 + 5 * O.length + t - (B1 + 5 * O.length) = t by omega]
      exact src _ (by unfold ssOff; grind)
  have wE : ∀ t, t < 5 → d'.nmem (B1 + 5 * S + 5 * O.length + t) = m₀ (RB + 11 * x + 6 + t) :=
    fun t ht => by
      zujji
      rw [ite_eq_right by_omega, ite_eq_left by_omega,
        show B1 + 5 * S + 5 * O.length + t - (B1 + 5 * S + 5 * O.length) = t by omega]
      grind
  have kD : ∀ a, a < B1 + 5 * O.length → d'.nmem a = d.nmem a := fun a ha => by
    zuhlr
  have kE : ∀ a, a < B1 + 5 * S + 5 * O.length → (a < B1 + 5 * O.length ∨
      B1 + 5 * O.length + 5 ≤ a) → d'.nmem a = d.nmem a := fun a ha ha' => by
    zuhlr
  refine ⟨d', k, ex, hk, by_grind, ?_, ?_, fun a ha => kD a by_omega,
    hr, hrr, hrm, ho⟩
  · zukpo
    refine stopRecs_snoc hst (fun a _ ha => kD a by_grind) ?_
    simp only [List.length_map, rawRec]
    zuflw
    · have := wD 0 by_norm_num; tauto
    · have := wD 1 by_norm_num; tauto
    · have := wD 2 by_norm_num; tauto
    · have := wD 3 by_norm_num; tauto
    · have := wD 4 by_norm_num; tauto
  · zukpo
    refine auxRecs_snoc hax (fun a ha0 ha => kE a by_grind (by
      omega)) ?_
    simp only [List.length_map, rawAux]
    zuflw
    · have := wE 0 by_norm_num; omega
    · have := wE 1 by_norm_num; omega
    · have := wE 2 by_norm_num; omega
    · have := wE 3 by_norm_num; omega
    · have := wE 4 by_norm_num; omega

/-! ## One step of the pass -/
theorem ssCtx_keep {J : Merge.Junction} {d2 RB S A₀ : ℕ} {m₀ : ℕ → ℕ} {d d' : Config}
    (h : SsCtx J d2 RB S A₀ m₀ d)
    (hr : ∀ r, 240000 ≤ r → r < 250000 → ztbnj → r ≠ sC →
      d'.nreg r = d.nreg r)
    (hm : ∀ a, a < A₀ → d'.nmem a = d.nmem a) : SsCtx J d2 RB S A₀ m₀ d' := by
  zucsp
  have k : ∀ i, (i < 3003 ∨ (3016 < i ∧ i < 10000)) ∧ i ≠ 2601 →
      d'.nreg ztcdy = d.nreg ztcdy :=
    fun i hi => hr ztcdy ztce ztce ztce
      (by unfold sC sw; omega)
  exact ⟨(k 2 by_norm_num).trans h1, (k 659 by_norm_num).trans h2,
    (k 4000 by_norm_num).trans h3, (k 4001 by_norm_num).trans h4,
    (k 610 by_norm_num).trans h5, (k 611 by_norm_num).trans h6,
    (k 3000 by_norm_num).trans h7, fun a ha => (hm a ha).trans (h8 a ha)⟩
theorem ssBc_sub {r : ℕ} (h : bandOf r ∉ oracleBands) : bandOf r ∉ ssBc := fun h' =>
  h (by
    simp only [ssBc, bSign, bLocate, bOQuery, Finset.mem_insert, Finset.mem_singleton] at h'
    rcases h' with h' | h' | h' <;> zvmxl <;> decide)

/-- The read of the next index. -/
def ssRd : List Instr := [.addN srA srSB srJ, .loadN srX srA]

/-- The advance. -/
def ssAdv : List Instr := [.copyN srP srX, .addN srJ srJ K1]
set_option maxRecDepth 20000 in
theorem ssRd_val (m f : ℕ → ℕ) : regB m ssRd f srX = m (f srSB + f srJ) ∧
    ∀ r, r ≠ srA → r ≠ srX → regB m ssRd f r = f r := by
  refine ⟨?_, fun r h1 h2 => ?_⟩
  · rfl
  · simp only [ssRd, regB, regI]; simp_all
set_option maxRecDepth 20000 in
theorem ssAdv_val (m f : ℕ → ℕ) : regB m ssAdv f srP = f srX ∧ regB m ssAdv f srJ = f srJ + f K1 ∧
    ∀ r, r ≠ srP → r ≠ srJ → regB m ssAdv f r = f r := by
  refine ztfdb
  · rfl
  · rfl
  · simp only [ssAdv, regB, regI]; simp_all
set_option maxRecDepth 20000 in
theorem ssCp_val (m f : ℕ → ℕ) :
    regB m [.copyN 30000 srX, .copyN 30001 srP] f 30000 = f srX ∧
    regB m [.copyN 30000 srX, .copyN 30001 srP] f 30001 = f srP ∧
    ∀ r, r ≠ 30000 → r ≠ 30001 → regB m [.copyN 30000 srX, .copyN 30001 srP] f r = f r := by
  refine ztfdb
  · rfl
  · rfl
  · zuie
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop SortR
@[expose] public section
variable {P : Polygon} {W : ℕ} {J : Merge.Junction} {d2 RB S A₀ : ℕ} {m₀ : ℕ → ℕ} {L : List ℕ} {SBv B1 : ℕ}
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **One step of the pass.** -/
theorem ssBody_step
 {d₀ d : Config} {j : ℕ}
    (hcmp : CmpOK P W ssCmp ssBc zteoe ztimg 12000)
    (hLlen : L.length = S) (hLm : ∀ x ∈ L, x < S)
    (hLs : L.Pairwise ztfcc)
    (hLmem : ∀ i, i < S → d₀.nmem zttcv = L.getD i 0)
    (hSB : SBv + S ≤ B1) (hS : RB + 11 * S ≤ A₀) (hAB : A₀ ≤ B1) (hroom : B1 + 10 * S + 1 ≤ W)
    (I : SsDI P W J d2 RB S A₀ m₀ L SBv B1 d₀ j d) (hj : j < S) :
    ∃ d' k, Exec P W ssBody d d' k ∧ 8 ≤ k ∧ k ≤ 12100 ∧
      SsDI P W J d2 RB S A₀ m₀ L SBv B1 d₀ ztl d' := by
  obtain ⟨hw, hqj, hctx, hsb, hb1, hb2, hmem, ⟨O, hD, hC, hOj, hprev, hst, hax⟩, hregs, hrr, hrm,
    hout⟩ := I
  have hctx' := hctx
  obtain ⟨-, -, -, -, j0, j1, -, -⟩ := hctx'
  have hBW : B1 ≤ W := by_omega
  -- the next index
  obtain ⟨rX, rO⟩ := ssRd_val d.nmem d.nreg
  have e₁ := exec_regB (P := P) ssRd hw (by
    simp only [ssRd, okW, okWI]; grind)
  set d₁ : Config := { d with nreg := regB d.nmem ssRd d.nreg } with hd₁
  set x := L.getD j 0 with hxd
  have hxL : L[j]? = some x := by
    grind
  have hxS := hLm x (List.mem_of_getElem? hxL)
  have q1X : d₁.nreg srX = x := by
    show regB _ _ _ srX = _
    rw [rX, hsb, hqj, hmem _ by_omega, hLmem j hj]
  have q1o : ∀ r, r ≠ srA → r ≠ srX → d₁.nreg r = d.nreg r := rO
  zuka
  have r1 : ∀ r, bandOf r ∉ oracleBands → ztbnj → d₁.nreg r = d.nreg r :=
    fun r _ h => q1o r ztqet ztzdp
  have hctx₁ := ssCtx_keep hctx (fun r a b c' _ =>
    r1 r ztodt c') by_grind
  have K0₁ := hctx₁.2.2.2.2.1
  have qJ₁ := (q1o _ (by ssoSrt) (by ssoSrt)).trans hqj
  have sC₁ := (q1o _ (by ssoSrt) (by ssoSrt)).trans hC
  have sB₁ := (q1o _ (by ssoSrt) (by ssoSrt)).trans hb1
  have aB₁ := (q1o _ (by ssoSrt) (by ssoSrt)).trans hb2
  have hOS : O.length < S := by_omega
  -- the advance, from a configuration with the item written or skipped
  have adv : ∀ (d₃ : Config) (O' : List ℕ), WordsBounded W d₃ → d₃.nreg srX = x →
      d₃.nreg srJ = j → d₃.nreg K1 = 1 → SsCtx J d2 RB S A₀ m₀ d₃ → d₃.nreg srSB = SBv →
      d₃.nreg sB = B1 → d₃.nreg aB = B1 + 5 * S →
      (∀ a, a < B1 → d₃.nmem a = d₀.nmem a) → DInv ztqwu L ztl O' →
      d₃.nreg sC = O'.length → O'.length ≤ j + 1 →
      StopRecsAt d₃.nmem B1 (O'.map ztkdx) →
      AuxRecsAt d₃.nmem ztgde (O'.map ztkdw) →
      (∀ r, bandOf r ∉ oracleBands → ztbnj → r ≠ sC →
        d₃.nreg r = d₀.nreg r) →
      (∀ r, bandOf r ∉ oracleBands → d₃.rreg r = d₀.rreg r) → d₃.rmem = d₀.rmem →
      d₃.output = d₀.output →
      ∃ d', Exec P W (block ssAdv) d₃ d' 2 ∧ SsDI P W J d2 RB S A₀ m₀ L SBv B1 d₀ ztl d' := by
    intro d₃ O' w₃ x₃ j₃ k₃ c₃ sb₃ b1₃ b2₃ m₃ D₃ C₃ l₃ st₃ ax₃ g₃ rr₃ rm₃ o₃
    obtain ⟨vP, vJ, vo⟩ := ssAdv_val d₃.nmem d₃.nreg
    have e := exec_regB (P := P) ssAdv w₃ (by
      simp only [ssAdv, okW, okWI, regI]
      refine ⟨trivial, ?_, trivial⟩
      rw [upd_other _ _ _ (by ssoSrt), upd_other _ _ _ (by ssoSrt), j₃, k₃]; omega)
    have ko := vo
    refine ⟨_, e, e.wb_right, by_grind, ?_, ?_, ?_, ?_, m₃,
      ⟨O', D₃, by_tauto, l₃,
        by grind, st₃, ax₃⟩,
      fun r h1 h2 h3 => ?_, rr₃, rm₃, o₃⟩
    · tauto
    · tauto
    · tauto
    · tauto
    · show regB _ _ _ r = _
      rw [ko r ztqet ztzdp]
      grind
  by_cases hj0 : j = 0
  · -- the first index: written
    subst hj0
    have hO0 := hD.nil rfl
    subst hO0
    obtain ⟨d₂, k₂, e₂, hk₂, sC₂, st₂, ax₂, m₂, r₂, rr₂, rm₂, o₂⟩ := ssWr_step
      hw₁ hS hAB hroom hctx₁ sB₁ aB₁ by_omega q1X hxS sC₁ hOS hst hax
    have k₂ : ∀ r, bandOf r ∉ oracleBands → ztbnj → r ≠ sC →
        d₂.nreg r = d.nreg r := fun r ho h hs => by
      rw [r₂ r zthej ztxkm
        zthek ztxkn
        zthem ztxko
        zthel ztxkp hs]
      exact r1 r ho h
    have kb := fun q a b h hs => k₂ q ztodt h hs
    obtain ⟨d', ex', hI'⟩ := adv d₂ _ e₂.wb_right
      (by rw [r₂ srX (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)
        (by ssoSrt)]; omega)
      (by rw [r₂ srJ (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt), qJ₁])
      (by rw [kb K1 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; exact j1)
      (ssCtx_keep hctx kb (fun a ha => by rw [m₂ a by_omega]))
      (by rw [r₂ srSB (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt), q1o srSB (by ssoSrt) (by ssoSrt)]; omega)
      (by rw [kb sB (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; omega)
      (by rw [kb aB (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; omega)
      (fun a ha => by rw [m₂ a ha]; exact hmem a ha)
      ((hD.step hLs hxL).1 ztp) sC₂ by_simp st₂ ax₂
      (fun r ho h hs => (k₂ r ho h hs).trans ztqqr)
      (fun r ho => by zunsn; exact hrr r ho) by_grind by_grind
    have nlt : ¬ d₁.nreg K0 < d₁.nreg srJ := by_omega
    exact ⟨d', _, .seq e₁ (.seq (.ifLtN_false nlt e₂) ex'), by_omega, by
      zunuc; omega, hI'⟩
  · -- a later index: compared with the previous one
    have hlt : d₁.nreg K0 < d₁.nreg srJ := by_omega
    obtain ⟨x', hx', hqP⟩ := hprev by_omega
    have hx'S := hLm x' (List.mem_of_getElem? hx')
    have hqP₁ := (q1o _ (by ssoSrt) (by ssoSrt)).trans hqP
    -- sorted: the previous key is at most this one
    have hsort : KLe ztpee ztpef := by
      have := List.pairwise_iff_getElem.1 hLs zthv j by_omega by_omega by_omega
      rw [List.getElem?_eq_getElem by_omega] at hx' hxL
      grind
    -- the inputs of the comparator
    obtain ⟨c0, c1, co⟩ := ssCp_val d₁.nmem d₁.nreg
    have e₂ := exec_regB (P := P) [.copyN 30000 srX, .copyN 30001 srP] hw₁ (by
      trivial)
    set d₂ : Config := { d₁ with
      nreg := regB d₁.nmem [.copyN 30000 srX, .copyN 30001 srP] d₁.nreg } with hd₂
    have k₂ : ∀ r, r ≠ 30000 → r ≠ 30001 → d₂.nreg r = d₁.nreg r := co
    zuja
    have hctx₂ := ssCtx_keep hctx₁ (fun r a _ _ _ =>
      k₂ r by_omega by_omega) by_grind
    obtain ⟨d₃, k₃, e₃, hk₃, hctx₃, hbit, hr₃, hrr₃, hm₃, hrm₃, ho₃⟩ := hcmp d₂ hw₂ hctx₂
    have i0 : d₂.nreg 30000 = x := by_grind
    have i1 : d₂.nreg 30001 = x' := by_grind
    rw [i0, i1] at hbit
    have hiff := ssLe_in (P := P) (J := J) (m := m₀) (RB := RB) hxS hx'S
    -- registers kept by the comparator
    have k₃ := fun r ho =>
      hr₃ r zteps (by rintro rfl; exact ho by_decide)
        zteps (Or.inl (ssBc_sub ho))
    have k31 : ∀ r, bandOf r ∉ oracleBands → ztbnj → d₃.nreg r = d.nreg r :=
      fun r ho h => by
        rw [k₃ r ho, k₂ r zteps
          zteps, r1 r ho h]
    have kb : ztcge := fun q a b =>
      not_oracle_sw a b
    have qX₃ : d₃.nreg srX = x := by
      rw [k₃ srX (kb _ (by ssoSrt) (by ssoSrt)), k₂ srX (by ssoSrt) (by ssoSrt), q1X]
    have K0₃ := hctx₃.2.2.2.2.1
    have hm₃' : ∀ a, d₃.nmem a = d.nmem a := by_grind
    by_cases hle : KLe ztpef ztpee
    · -- equal keys: skipped
      have heq := KLe.antisymm' hsort hle
      have b1 : d₃.nreg 30002 = 1 := by_grind
      have t : d₃.nreg K0 < d₃.nreg 30002 := by_omega
      obtain ⟨d', ex', hI'⟩ := adv d₃ O e₃.wb_right qX₃
        (by rw [k₃ srJ (kb _ (by ssoSrt) (by ssoSrt)), k₂ srJ (by ssoSrt) (by ssoSrt), qJ₁])
        hctx₃.2.2.2.2.2.1 hctx₃
        (by rw [k₃ srSB (kb _ (by ssoSrt) (by ssoSrt)), k₂ srSB (by ssoSrt) (by ssoSrt), q1o srSB (by ssoSrt) (by ssoSrt)]; omega)
        (by rw [k31 sB (kb _ (by ssoSrt) (by ssoSrt)) (by ssoSrt)]; omega)
        (by rw [k31 aB (kb _ (by ssoSrt) (by ssoSrt)) (by ssoSrt)]; omega)
        (fun a ha => by rw [hm₃' a]; exact hmem a ha)
        ((hD.step hLs hxL).2 ⟨by_omega, fun y hy => by
          grind⟩)
        (by rw [k31 sC (kb _ (by ssoSrt) (by ssoSrt)) (by ssoSrt)]; exact hC) by_omega
        by_grind by_grind
        (fun r ho h _ => (k31 r ho h).trans (hregs r ho h (by
          omega)))
        (fun r ho => by
          rw [hrr₃ r ztweu]; exact hrr r ho)
        by_grind by_grind
      refine ⟨d', _, .seq e₁ (.seq (.ifLtN_true hlt (.seq e₂ (.seq e₃
        (.ifLtN_true t ztjdx)))) ex'), by zunuc; omega, by zunuc; omega, hI'⟩
    · -- a new key: written
      have b0 : d₃.nreg 30002 = 0 := by_grind
      have t : ¬ d₃.nreg K0 < d₃.nreg 30002 := by_omega
      have hne : ∀ y, L[j - 1]? = some y → ssKey P J m₀ RB y ≠ ssKey P J m₀ RB x := by
        grind
      have sC₃ : d₃.nreg sC = O.length := by
        rw [k31 sC (kb _ (by ssoSrt) (by ssoSrt)) (by ssoSrt)]; exact hC
      obtain ⟨d₄, k₄, e₄, hk₄, sC₄, st₄, ax₄, m₄, r₄, rr₄, rm₄, o₄⟩ := ssWr_step
        e₃.wb_right hS hAB hroom hctx₃
        (by rw [k31 sB (kb _ (by ssoSrt) (by ssoSrt)) (by ssoSrt)]; omega)
        (by rw [k31 aB (kb _ (by ssoSrt) (by ssoSrt)) (by ssoSrt)]; omega)
        (fun a ha => (hm₃' a).trans ztoaw) qX₃ hxS sC₃ hOS
        by_grind by_grind
      have k₄ : ∀ r, bandOf r ∉ oracleBands → ztbnj → r ≠ sC →
          d₄.nreg r = d.nreg r := fun r ho h hs => by
        rw [r₄ r zthej ztxkm
          zthek ztxkn
          zthem ztxko
          zthel ztxkp hs]
        exact k31 r ho h
      have kb4 := fun q a b h hs => k₄ q ztodt h hs
      obtain ⟨d', ex', hI'⟩ := adv d₄ _ e₄.wb_right
        (by rw [r₄ srX (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)
          (by ssoSrt)]; omega)
        (by rw [r₄ srJ (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt), k₃ srJ (kb _ (by ssoSrt) (by ssoSrt)), k₂ srJ (by ssoSrt) (by ssoSrt), qJ₁])
        (by rw [kb4 K1 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; exact j1)
        (ssCtx_keep hctx kb4 (fun a ha => by rw [m₄ a by_omega, hm₃' a]))
        (by rw [r₄ srSB (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt), k₃ srSB (kb _ (by ssoSrt) (by ssoSrt)), k₂ srSB (by ssoSrt) (by ssoSrt),
          q1o srSB (by ssoSrt) (by ssoSrt)]; omega)
        (by rw [kb4 sB (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; omega)
        (by rw [kb4 aB (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; omega)
        (fun a ha => by rw [m₄ a ha, hm₃' a]; exact hmem a ha)
        ((hD.step hLs hxL).1 (Or.inr hne)) sC₄ ztbaw st₄ ax₄
        (fun r ho h hs => (k₄ r ho h hs).trans ztqqr)
        (fun r ho => by rw [rr₄, hrr₃ r ztweu]; exact hrr r ho)
        (by rw [rm₄, hrm₃]; omega) (by rw [o₄, ho₃]; omega)
      refine ⟨d', _, .seq e₁ (.seq (.ifLtN_true hlt (.seq e₂ (.seq e₃
        (.ifLtN_false t e₄)))) ex'), by_omega, by zunuc; omega, hI'⟩

/-- **A loop with bounded body costs**: an invariant indexed by the number `j` of iterations done,
the test true exactly while `j < L`, each body cost in `[Bmin, Bmax]`. -/
theorem while_range {a b : ℕ} {body : Stmt} (I : ℕ → Config → Prop)
    (L Bmin Bmax : ℕ) (htest : ∀ j d, I j d → ztlmx)
    (hwb : ∀ j d, I j d → WordsBounded W d)
    (hbody : ∀ j d, I j d → j < L →
      ∃ d' k, Exec P W body d d' k ∧ Bmin ≤ k ∧ k ≤ Bmax ∧ I ztl d') :
    ∀ j d, I j d → j ≤ L →
      ∃ d' k, Exec P W ztpx d d' k ∧ (Bmin + 2) * ztnmd + 2 ≤ k ∧
        k ≤ (Bmax + 2) * ztnmd + 2 ∧ I L d' := by
  zulnb
  induction hn : L - j generalizing j d with
  | zero =>
    zugmm

    exact ⟨d, 2, .whileLtN_false by_grind
      by_grind, by_simp, by_simp, hI⟩
  | succ n ih =>
    zukdh
    obtain ⟨d₁, k₁, e₁, hk1, hk2, hI₁⟩ := hbody j d hI hlt
    obtain ⟨d', k', e', hk1', hk2', hI'⟩ := ih _ d₁ hI₁ by_omega by_omega
    refine ⟨d', _, Exec.whileLtN_true by_grind e₁ e', ?_, ?_, hI'⟩
    · grind
    · grind

/-- **The dedupe pass.** -/
theorem ssDedup_exec
 {d₀ : Config}
    (hcmp : CmpOK P W ssCmp ssBc zteoe ztimg 12000)
    (hLlen : L.length = S) (hLm : ∀ x ∈ L, x < S)
    (hLs : L.Pairwise ztfcc)
    (hLmem : ∀ i, i < S → d₀.nmem zttcv = L.getD i 0)
    (hSB : SBv + S ≤ B1) (hS : RB + 11 * S ≤ A₀) (hAB : A₀ ≤ B1) (hroom : B1 + 10 * S + 1 ≤ W)
    (I : SsDI P W J d2 RB S A₀ m₀ L SBv B1 d₀ 0 d₀) :
    ∃ d' k, Exec P W ssDedup d₀ d' k ∧ 10 * S + 2 ≤ k ∧ k ≤ 12102 * S + 2 ∧
      SsDI P W J d2 RB S A₀ m₀ L SBv B1 d₀ S d' := by
  obtain ⟨d', k, ex, h1, h2, hI⟩ := while_range (P := P) (W := W) (a := srJ) (b := gRC)
    (body := ssBody) (SsDI P W J d2 RB S A₀ m₀ L SBv B1 d₀) S 8 12100
    (fun j d h => by rw [h.qj, h.ctx.2.2.2.1])
    (fun j d h => h.wb)
    (fun j d h hj => ssBody_step hcmp hLlen hLm hLs hLmem hSB hS hAB hroom h hj)
    0 d₀ I ztbg
  exact ⟨d', k, ex, by_omega, by_omega, hI⟩
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop SortR
open SortL
@[expose] public section
def ssIdxHead : List Instr := [.copyN srA0 ALLOC, .copyN srIB ALLOC, .constN srI 0]
def ssIdxBody : List Instr := [.addN srA srIB srI, .storeN srA srI, .addN srI srI K1]

/-- The indices `0 … S - 1` at the allocator. -/
def ssIdx : Stmt :=
  .seq (block ssIdxHead) (.seq (.whileLtN srI gRC (block ssIdxBody)) (.instr (.addN ALLOC ALLOC gRC)))

/-- The inputs of the sort. -/
def ssSortIn : List Instr := [.copyN 30003 srIB, .copyN 30004 gRC]

/-- The output arrays. -/
def ssAllocL : List Instr :=
  [.copyN srSB 30005, .copyN sB ALLOC, .addN srT gRC gRC, .addN srT srT srT, .addN srT srT gRC,
    .addN aB sB srT, .addN ALLOC ALLOC srT, .addN ALLOC ALLOC srT, .constN sC 0, .constN srJ 0]

/-- **The sort task.** -/
def ssSrt : Stmt :=
  .seq ssIdx (.seq (block ssSortIn) (.seq (sortStmt ssCmp) (.seq (block ssAllocL) ssDedup)))

/-! ## The indices -/
set_option maxRecDepth 20000 in
theorem ssIdx_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    (hK1 : c.nreg K1 = 1) (hroom : c.nreg ALLOC + c.nreg gRC + 1 ≤ W) :
    ∃ c' k, Exec P W ssIdx c c' k ∧ k = 5 * c.nreg gRC + 6 ∧
      c'.nreg ALLOC = c.nreg ALLOC + c.nreg gRC ∧ c'.nreg srA0 = c.nreg ALLOC ∧
      c'.nreg srIB = c.nreg ALLOC ∧ (∀ i, i < c.nreg gRC → c'.nmem ztfqi = i) ∧
      zth ∧
      (∀ r, r ≠ ALLOC → r ≠ srA0 → r ≠ srIB → r ≠ srI → r ≠ srA → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zujq
  set S := c.nreg gRC with hS
  have e₀ := exec_regB (P := P) ssIdxHead hw (by
    simp only [ssIdxHead, okW, okWI]; simp)
  set c₁ : Config := { c with nreg := regB c.nmem ssIdxHead c.nreg } with hc₁
  have v1 : ∀ r, r ≠ srA0 → r ≠ srIB → r ≠ srI → c₁.nreg r = c.nreg r := fun r a b d => by
    simp only [hc₁, ssIdxHead, regB, regI]
    simp_all
  have vI : c₁.nreg srI = 0 := by_rfl
  have vB : c₁.nreg srIB = A := by
    rfl
  have v0 : c₁.nreg srA0 = A := by
    rfl
  have vA : c₁.nreg ALLOC = A := v1 _ (by ssoSrt) (by ssoSrt) (by ssoSrt)
  have vS : c₁.nreg gRC = S := v1 _ (by ssoSrt) (by ssoSrt) (by ssoSrt)
  have vK : c₁.nreg K1 = 1 := (v1 _ (by ssoSrt) (by ssoSrt) (by ssoSrt)).trans hK1
  let I : ℕ → Config → Prop := fun i d => WordsBounded W d ∧ d.nreg srI = i ∧
    (∀ t, t < i → d.nmem ztsut = t) ∧ (∀ a, a < A → d.nmem a = c.nmem a) ∧
    (∀ r, r ≠ srI → r ≠ srA → d.nreg r = c₁.nreg r) ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem ∧
    d.output = c.output
  have I₀ : I 0 c₁ := ⟨e₀.wb_right, vI, fun t ht => absurd ht zthrl,
    fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  obtain ⟨c₂, e₁, w₂, hI2, ht2, hm2, hr2, rr2, rm2, o2⟩ :=
    while_exact (P := P) (W := W) (a := srI) (b := gRC) (body := block ssIdxBody) I S 3
      (fun i d h => by rw [h.2.1, h.2.2.2.2.1 _ (by ssoSrt) (by ssoSrt), vS])
      (fun i d h => h.1)
      (fun i d ⟨hwd, hi, ht, hm, hr, rr, rm, o⟩ hlt => by
        have dB : d.nreg srIB = A := by rw [hr _ (by ssoSrt) (by ssoSrt), vB]
        have dK : d.nreg K1 = 1 := by rw [hr _ (by ssoSrt) (by ssoSrt), vK]
        have x₁ := Exec.addN (P := P) hwd srA srIB srI by_omega
        have x₂ := Exec.storeN (P := P) x₁.wb_right srA srI
        have x₃ := Exec.addN (P := P) x₂.wb_right srI srI K1 (by
          zubi
          rw [upd_other _ _ _ (by ssoSrt), upd_other _ _ _ (by ssoSrt), hi, dK]; omega)
        refine ⟨_, Exec.block_cons x₁ (Exec.block_cons x₂ (Exec.block_cons x₃
          (Exec.block_nil x₃.wb_right))), x₃.wb_right, ?_, fun t ht' => ?_, fun a ha => ?_,
          fun r h1 h2 => ?_, rr, rm, o⟩
        · zufb
          rw [upd_other _ _ _ (by ssoSrt), upd_other _ _ _ (by ssoSrt), hi, dK]
        · zufb
          rw [upd_other _ _ _ (show srI ≠ srA by ssoSrt), dB, hi]
          rcases Nat.lt_or_ge t i with h | h
          · zurj
          · rw [show t = i by omega, upd_same]
        · zufb
          zurj
        simp_all)
      0 c₁ I₀ ztbg
  have gA : c₂.nreg ALLOC = A := by rw [hr2 _ (by ssoSrt) (by ssoSrt), vA]
  have gS : c₂.nreg gRC = S := by rw [hr2 _ (by ssoSrt) (by ssoSrt), vS]
  have x₄ := Exec.addN (P := P) w₂ ALLOC ALLOC gRC by_omega
  refine ⟨_, _, .seq e₀ (.seq e₁ x₄), by simp [ssIdxHead]; ring, ?_, ?_, ?_, ?_, ?_,
    fun r h0 h1 h2 h3 h4 => ?_, rr2, rm2, o2⟩
  · simp_all
  · zubi
    rw [upd_other _ _ _ (by ssoSrt), hr2 _ (by ssoSrt) (by ssoSrt), v0]
  · zubi
    rw [upd_other _ _ _ (by ssoSrt), hr2 _ (by ssoSrt) (by ssoSrt), vB]
  · omega
  · omega
  simp_all
set_option maxRecDepth 20000 in
theorem ssAllocL_val (m f : ℕ → ℕ) :
    regB m ssAllocL f srSB = f 30005 ∧ regB m ssAllocL f sB = f ALLOC ∧
    regB m ssAllocL f aB = f ALLOC + ztday ∧
    regB m ssAllocL f ALLOC = f ALLOC + ztday +
      ztday ∧
    regB m ssAllocL f sC = 0 ∧ regB m ssAllocL f srJ = 0 ∧
    ∀ r, r ≠ srSB → r ≠ sB → r ≠ srT → r ≠ aB → r ≠ ALLOC → r ≠ sC → r ≠ srJ →
      regB m ssAllocL f r = f r := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r a b d e g h i => ?_⟩
  all_goals simp only [ssAllocL, regB, regI, srSB, sB, srT, aB, ALLOC, sC, srJ, gRC, sw,
    Nat.reduceAdd, upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true]
  simp only [srSB, sB, srT, aB, ALLOC, sC, srJ, sw, Nat.reduceAdd] at a b d e g h i
  simp_all
set_option maxRecDepth 20000 in
theorem ssAllocL_ok {W : ℕ} (m f : ℕ → ℕ)
    (h : f ALLOC + 10 * f gRC ≤ W) : okW W m ssAllocL f := by
  simp only [ALLOC, gRC, sw, Nat.reduceAdd] at h
  simp only [ssAllocL, okW, okWI, regI, srSB, sB, srT, aB, ALLOC, sC, srJ, gRC, sw,
    Nat.reduceAdd, upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true, true_and,
    and_true]
  omega
set_option hygiene false in
/-- Register arithmetic with the hypotheses. -/
macro "sshSrt" : tactic =>
  `(tactic| (simp (config := { failIfUnchanged := false }) only [srA0, srIB, srI, srA, srSB, srJ, srX,
                srP, srT, srS, srD, srE, srV, sr1, sr2, sr3, sr4, sB, sC, aB, gRB, gRC, K0, K1, ALLOC,
                sw, Nat.reduceAdd, ne_eq] at *; omega))
variable {m : ℕ → ℕ}
theorem ss_seg_range {A S : ℕ} (h : ∀ i, i < S → m ztfna = i) :
    seg m A S = List.range S := by
  zuhav
  rw [List.map_congr_left (g := id) by_simp_all, List.map_id]
theorem ss_seg_getD {A S i : ℕ} (hi : i < S) : (seg m A S).getD i 0 = m ztfna :=
  seg_getD i hi
theorem ss_clog_mono (S : ℕ) : S * ztgeg ≤ ztbgu * ztzcf :=
  Nat.mul_le_mul by_omega (by have := Nat.clog_mono_right 2 (show S ≤ S + 1 by omega); omega)
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **Task S: sort and dedupe the raw stop records.** -/
theorem sortTask : SortTask := by
  refine ⟨ssSrt, 40000, fun sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hrec hRB hroom => ?_⟩
  set S := c.nreg gRC with hSd
  zudbg
  set RB := c.nreg gRB with hRBd
  zudvs
  set d2 := c.nreg ztjl with hd2
  have hY : S * ztgeg ≤ ztbgu * ztdld := ss_clog_mono S
  have hX1 : S + 1 ≤ ztbgu * ztzcf := by_simp_all
  have hsc : sortCost 12000 S = 12030 * (S * ztgeg + 1) := rfl
  rw [Nat.mul_assoc] at hroom ⊢
  generalize hXd : ztbgu * ztdld = XX at hY hX1 hroom ⊢
  generalize hYd : S * ztgeg = Y at hY hsc
  clear hXd hYd
  zubod
  obtain ⟨k0, k1, -, -, -, -, -⟩ := E.hK.fix hI
  zuhey
  obtain ⟨hG, hWh, hwf, ⟨H, hC, -⟩, -, hWm⟩ := E.ctxW' hI
  have hgn : ztboy := by
    zugq
  have h11 : A + 11000 ≤ W := by_omega
  have hcmp : CmpOK P W ssCmp ssBc (SsCtx J d2 RB S A m₀) _ 12000 :=
    ssCmp_ok hG hWh hwf hC hWm h11 hRB by_simp_all hgn
  -- 1. the indices
  obtain ⟨c₁, k₁, e₁, hk₁, a₁, q0₁, qB₁, t₁, m₁, r₁, rr₁, rm₁, o₁⟩ :=
    ssIdx_exec (P := P) hw k1 by_omega
  have kr₁ : ∀ r, 240000 ≤ r → r < 250000 → r < sw 3000 ∨ sw 3003 < r →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 =>
    r₁ r (by unfold ALLOC; omega) (by sshSrt) (by sshSrt) (by sshSrt) (by sshSrt)
  -- 2. the inputs of the sort
  have e₂ := exec_regB (P := P) ssSortIn e₁.wb_right (by
    trivial)
  set c₂ : Config := { c₁ with nreg := regB c₁.nmem ssSortIn c₁.nreg } with hc₂
  have r₂ : ∀ r, r ≠ 30003 → r ≠ 30004 → c₂.nreg r = c₁.nreg r := fun r a b => by
    zunqr; rw [upd_other _ _ _ b, upd_other _ _ _ a]
  have v3 : c₂.nreg 30003 = A := by
    zunqr; rw [upd_other _ _ _ by_norm_num, upd_same, qB₁]
  have v4 : c₂.nreg 30004 = S := by
    simp only [hc₂, ssSortIn, regB, regI, upd_same]
    rw [upd_other _ _ _ (by ssoSrt), kr₁ gRC (by ssoSrt) (by ssoSrt) (by ssoSrt)]
  have kr₂ : ∀ r, 240000 ≤ r → r < 250000 → r < sw 3000 ∨ sw 3003 < r →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [r₂ r by_omega by_omega]; grind
  have A₂ : c₂.nreg ALLOC = A + S := by rw [r₂ ALLOC (by ssoSrt) (by ssoSrt)]; exact a₁
  have ctx₂ : SsCtx J d2 RB S A m₀ c₂ := by
    refine ⟨kr₂ _ (by ssoSrt) (by ssoSrt) (by ssoSrt),
      (kr₂ cGW by_decide by_decide by_decide).trans hgw,
      kr₂ gRB (by ssoSrt) (by ssoSrt) (by ssoSrt), kr₂ gRC (by ssoSrt) (by ssoSrt) (by ssoSrt),
      (kr₂ K0 (by ssoSrt) (by ssoSrt) (by ssoSrt)).trans k0, (kr₂ K1 (by ssoSrt) (by ssoSrt) (by ssoSrt)).trans k1,
      (r₂ srA0 (by ssoSrt) (by ssoSrt)).trans q0₁, by_omega⟩
  -- 3. the sort
  have hsortroom : c₂.nreg ALLOC + sortCost 12000 (rd c₂ bSort 4) ≤ W := by
    show c₂.nreg ALLOC + sortCost 12000 ztvmx ≤ W
    grind
  obtain ⟨c₃, k₃, e₃, hk₃, ⟨p1, p2, pperm, ppair⟩, fr₃⟩ :=
    sort_meets (cmp := ssCmp) bSort_not_ssBc 12000 (fun _ _ _ d => SsCtx J d2 RB S A m₀ d)
      (fun _ _ => ssLe P J m₀ RB S) P W c₂ e₂.wb_right
      ⟨ctx₂, hcmp, ssCtx_stable by_omega, ssLe_trans, ssLe_total,
        by show c₂.nreg 30003 + c₂.nreg 30004 ≤ c₂.nreg ALLOC; omega⟩ hsortroom
  have hk₃' : k₃ ≤ 12030 * ztteg := by
    have : k₃ ≤ sortCost 12000 ztvmx := hk₃
    grind
  set SBv := c₃.nreg 30005 with hSBv
  have p1' : A + S ≤ SBv := by have := p1; rw [A₂] at this; exact this
  have p2' : SBv + S ≤ c₃.nreg ALLOC := by have := p2; rw [show rd c₂ bSort 4 = S from v4] at this
                                           exact this
  set L := seg c₃.nmem SBv S with hL
  have hLr : seg c₂.nmem (rd c₂ bSort 3) S = List.range S := by
    rw [show rd c₂ bSort 3 = A from v3]
    exact ss_seg_range by_omega
  have pperm' : L.Perm (List.range S) := by
    have := pperm; rw [show rd c₂ bSort 4 = S from v4] at this; rw [hLr] at this; exact this
  have ppair' : L.Pairwise fun a b => ssLe P J m₀ RB S a b = true := by
    have := ppair; rw [show rd c₂ bSort 4 = S from v4] at this; exact this
  have hLm : ∀ x ∈ L, x < S := fun x hx => List.mem_range.1 (pperm'.mem_iff.1 hx)
  have hLlen : L.length = S := by rw [hL, seg_length]
  have hLs : L.Pairwise (fun x y => KLe _ _) :=
    ppair'.imp_of_mem fun hx hy h => (ssLe_in by_grind by_grind).1 h
  -- frame of the sort
  have fb : ∀ r, 240000 ≤ r → r < 250000 → bandOf r ∉ insert bSort ssBc := fun r h1 h2 => by
    zuecu
  have kr₃ : ∀ r, 240000 ≤ r → r < 250000 → c₃.nreg r = c₂.nreg r := fun r h1 h2 =>
    fr₃.1 r by_grind ztu
  have hB1 := by_omega
  have hB1' : c₃.nreg ALLOC ≤ A + S + k₃ := by have := fr₃.2.2.2.2.2.2; omega
  set B1 := c₃.nreg ALLOC with hB1d
  -- 4. the output arrays
  have e₄ := exec_regB (P := P) ssAllocL e₃.wb_right (ssAllocL_ok c₃.nmem c₃.nreg (by
    rw [kr₃ gRC (by ssoSrt) (by ssoSrt), kr₂ gRC (by ssoSrt) (by ssoSrt) (by ssoSrt)]; omega))
  set c₄ : Config := { c₃ with nreg := regB c₃.nmem ssAllocL c₃.nreg } with hc₄
  obtain ⟨vSB, vsB, vaB, vAl, vsC, vqJ, vo⟩ := ssAllocL_val c₃.nmem c₃.nreg
  have gS₃ : c₃.nreg gRC = S := by
    rw [kr₃ gRC (by ssoSrt) (by ssoSrt), kr₂ gRC (by ssoSrt) (by ssoSrt) (by ssoSrt)]
  rw [gS₃] at vaB vAl
  have k₄ : ∀ r, r ≠ srSB → r ≠ sB → r ≠ srT → r ≠ aB → r ≠ ALLOC → r ≠ sC → r ≠ srJ →
      c₄.nreg r = c₃.nreg r := vo
  have kr₄ : ∀ r, 240000 ≤ r → r < 250000 → (r < sw 2600 ∨ sw 2602 < r) →
      (r < sw 3000 ∨ sw 3016 < r) → c₄.nreg r = c.nreg r := fun r h1 h2 h3 h4 => by
    rw [k₄ r (by sshSrt) (by sshSrt) (by sshSrt) (by sshSrt) (by unfold ALLOC; omega) (by sshSrt) (by sshSrt),
      kr₃ r h1 h2, kr₂ r h1 h2 (by sshSrt)]
  have q0₄ : c₄.nreg srA0 = A := by
    rw [k₄ srA0 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt),
      kr₃ srA0 (by ssoSrt) (by ssoSrt), r₂ srA0 (by ssoSrt) (by ssoSrt), q0₁]
  have mA₄ : ∀ a, a < A → c₄.nmem a = m₀ a := fun a ha => by
    show c₃.nmem a = _
    rw [fr₃.2.2.1 a by_omega]; grind
  have ctx₄ : SsCtx J d2 RB S A m₀ c₄ :=
    ⟨kr₄ _ (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt),
      (kr₄ cGW by_decide by_decide by_decide
        by_decide).trans hgw,
      kr₄ gRB (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt), kr₄ gRC (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt),
      (kr₄ K0 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)).trans k0,
      (kr₄ K1 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)).trans k1, q0₄, mA₄⟩
  zubwq
  have I₀ : SsDI P W J d2 RB S A m₀ L SBv B1 c₄ 0 c₄ :=
    { wb := hw₄, qj := vqJ, ctx := ctx₄, sb := vSB, b1 := vsB,
      b2 := by_grind,
      mem := by_omega,
      recs := ⟨[], DInv.start L, vsC, le_rfl, by_omega,
        fun i hi => absurd hi by_simp, fun i hi => absurd hi by_simp⟩,
      regs := by_omega, rr := by_grind, rm := rfl, out := rfl }
  have hLmem : ∀ i, i < S → c₄.nmem _ = L.getD i 0 := fun i hi => by
    show c₃.nmem _ = _
    rw [hL, ss_seg_getD hi]
  -- 5. the dedupe pass
  obtain ⟨c₅, k₅, e₅, hk5a, hk5b, I5⟩ := ssDedup_exec hcmp hLlen hLm hLs hLmem p2' hRB
    by_omega by_omega I₀
  obtain ⟨w₅, -, -, -, b1₅, b2₅, mem₅, ⟨O, hD, hC₅, hO, -, hst, hax⟩, regs₅, rr₅, rm₅, out₅⟩ := I5
  have A₄ : c₄.nreg ALLOC = B1 + 10 * S := by_grind
  have A₅ : c₅.nreg ALLOC = B1 + 10 * S := by
    rw [regs₅ _ by_decide by_decide by_decide, A₄]
  -- registers of the band of the sweep outside the writes, through all steps
  have kr₅ : ∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → ¬ SoR r → c₅.nreg r = c.nreg r := by
    intro r ho hA hS
    unfold SoR at hS
    simp only [sw] at hS
    have hn : r ≠ sC := by rintro rfl; exact hS (Or.inr (Or.inl by_decide))
    rw [regs₅ r ho ztdzc hn]
    by_cases hb : 240000 ≤ r ∧ r < 250000
    · exact kr₄ r hb.1 hb.2 ztdzc ztdzc
    · have nb : ∀ q, 240000 ≤ q → q < 250000 → r ≠ q := by_omega
      rw [k₄ r (nb _ (by ssoSrt) (by ssoSrt)) (nb _ (by ssoSrt) (by ssoSrt)) (nb _ (by ssoSrt) (by ssoSrt))
          (nb _ (by ssoSrt) (by ssoSrt)) hA by_omega (nb _ (by ssoSrt) (by ssoSrt)),
        fr₃.1 r (by
          zuq
          simp only [Finset.mem_insert, ssBc, bSign, bLocate, bOQuery, bSort,
            Finset.mem_singleton] at h
          apply ho
          rcases h with h | h | h | h <;> zvmwc <;> decide) hA,
        r₂ r (by intro h; subst h; exact ho by_decide) (by intro h; subst h; exact ho by_decide),
        r₁ r hA (nb _ (by ssoSrt) (by ssoSrt)) (nb _ (by ssoSrt) (by ssoSrt)) (nb _ (by ssoSrt) (by ssoSrt))
          (nb _ (by ssoSrt) (by ssoSrt))]
  -- memory below the entry allocator
  have mem₅' : ∀ a, a < A → c₅.nmem a = m₀ a := fun a ha => by
    rw [mem₅ a by_omega]; exact mA₄ a ha
  have hk₁' := hk₁
  refine ⟨c₅, _, .seq e₁ ztbq, ?_, ⟨w₅, fun q hq => ?_, ?_,
    fun a ha => ?_, fun a ha => ?_⟩, ⟨fun r hr hrA => ?_, fun r hr => ?_, ?_, ?_, ?_⟩,
    ⟨O, fun i hi => hLm i (hD.sub i hi), hD.inc, fun i hi => ?_, hC₅, ?_, ?_, ?_, ?_, ?_, ?_,
      by omega, fun r h1 h2 h3 => kr₅ r h1 h3 h2⟩⟩
  · simp only [ssSortIn, ssAllocL, List.length_cons, List.length_nil]
    grind
  · zujpt
    rw [kr₅ q ztbet ztu (by
      unfold SoR; simp only [sw]; omega)]
    exact hI.hin q (by unfold IFix; omega)
  · zunji; have := hI.hA; omega
  · rw [mem₅' a (by have := hI.hA; omega)]; exact hI.hm a ha
  · rw [rm₅]
    show c₃.rmem a = _
    rw [fr₃.2.2.2.1 a (by rw [A₂]; have := hI.hA; omega)]
    show c₁.rmem a = _
    zunkf; exact hI.hrm a ha
  · exact kr₅ r ztdzw hrA (by
      zuq
      zuhbg
      unfold SoR at h
      simp only [sw] at h
      exact sw_io by_omega by_omega)
  · rw [rr₅ r ztdzw]
    show c₃.rreg r = _
    rw [fr₃.2.1 r (fun h => hr (by
      have  := ssBc_oracle.trans oracle_sub
      exact this h))]
    grind
  · rw [out₅]; show c₃.output = _; rw [fr₃.2.2.2.2.1]; omega
  · grind
  · grind
  · -- covering
    have hiL := pperm'.mem_iff.2 ztuzq
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hiL
    have hnL : n < L.length := by
      by_contra h; rw [List.getElem?_eq_none by_omega] at hn; cases hn
    obtain ⟨y, hy, hk⟩ := hD.cov n by_omega i hn
    exact ⟨y, hy, hk⟩
  · grind
  · grind
  · grind
  · grind
  · grind
  grind
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)
@[expose] public section
def RawV (P : Polygon) (J : Merge.Junction) (N : NF) (m : ℕ → ℕ) (RB i : ℕ) : Prop :=
  RawOK P J N ztlsf ztruv ∧ PosW P J (rawRec m RB i).1 (rawRec m RB i).2.1 ∧
    AuxOK P J N (rSet P J N ztlsf) (rawAux m RB i)

/-- The registers the per-origin step may write (besides the oracle bands and the allocator):
the count `gRC`, the scratch of stage 2 and the origin registers `sw 4010 … sw 4199`. -/
def SOrgR (r : ℕ) : Prop :=
  ztgz ∨ r = gRC ∨ ztph ∨
    ztfuu ∨ ztbgd

/-- **The post of the per-origin step** for the code `(kind, k, b)` (`RC = gRC`, `RB = gRB`): at
most two new raw records `RC ≤ i < gRC'`, valid (`RawV`); if the code is admissible with a free
direction (`OrgD`), every attachment of its stop chord on the `C₁` part is one of them; the
memory below the allocator is kept except the two raw slots; registers outside `SOrgR` kept. -/
def OrgOut (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) (c c' : Config) : Prop :=
  c.nreg gRC ≤ c'.nreg gRC ∧ c'.nreg gRC ≤ c.nreg gRC + 2 ∧
    (∀ i, c.nreg gRC ≤ i → i < c'.nreg gRC → RawV P J N c'.nmem ztbsp i) ∧
    (OrgD P J N kind k b → ∀ (p : ℕ) (t : ℝ),
      SideAttach (chainModel J.whole).W ztwjv p t →
      (Lst J : ℝ) ≤ oW J ztk → ∃ i, c.nreg gRC ≤ i ∧ i < c'.nreg gRC ∧
        (rawRec c'.nmem ztbsp i).1 = p ∧ rPar P J ztznl = t ∧
        rSet P J N ztznl = stopSet J zta N kind k b) ∧
    (∀ a, a < c.nreg ALLOC → (a < c.nreg gRB + 11 * c.nreg gRC ∨
      c.nreg gRB + 11 * ztees ≤ a) → c'.nmem a = c.nmem a) ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ SOrgR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task O: the per-origin step** for any code `kind ≤ 2`, `b ≤ 1`, `kind = 1 → k < K₂`
(no records unless the code is admissible), with the model context of `C₂` at `gMD2, gCD2`, at
cost `κ D · (1 or K₁ + K₂ + 1) · (F γ + TLR + 1)` (the factor `K₁ + K₂ + 1` for the shared and
top codes only). -/
def OrgTask : Prop :=
  ∃ (org : Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz c →
      c.nreg oKd ≤ 2 → c.nreg oB ≤ 1 → (c.nreg oKd = 1 → c.nreg oKk < N₂.nChords) →
      c₀.nreg ALLOC ≤ c.nreg gRB → c.nreg gRB + 11 * ztees ≤ c.nreg ALLOC →
      c.nreg ALLOC + κ zto * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ ztwbe c (κ zto * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))
        ztwrn

/-! ## The parent scan -/
def pE2 : ℕ := sw 4025
def pH2 : ℕ := sw 4026
def oPar : ℕ := sw 4064

/-- The registers the parent scan may write (besides the oracle bands). -/
def ParR (r : ℕ) : Prop := r = oPar ∨ (sw 4068 ≤ r ∧ r < sw 4080)

/-- **The post of the parent scan**: `oPar = i + 1` for a chord `i` of `N₂` whose end in the
direction of code `oB` (`lpos` for `1`, `rpos` for `0`) has the key of the position
`(pE2, pH2)` of the walk of `C₂`, or `0` if there is none. -/
def ParOut (P : Polygon) (J : Merge.Junction) (N : NF) (c c' : Config) : Prop :=
  c'.nreg oPar ≤ N.nChords ∧
    (0 < c'.nreg oPar → (chainModel J.right).key zta (endPos N (c'.nreg oPar - 1)
      ztcce) = (chainModel J.right).key (Qof P) ⟨c.nreg pE2, c.nreg pH2⟩) ∧
    (c'.nreg oPar = 0 → ∀ i, i < N.nChords → (chainModel J.right).key zta
      ztzln ≠ (chainModel J.right).key zta ztbii) ∧
    zth ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ ParR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task P: the parent scan**, from a proper position `(pE2, pH2)` of the walk of `C₂` (code
`0` only at a tour vertex), cost `κ (K₂ + 1)`. -/
def ParTask : Prop :=
  ∃ (ps : Stmt) (κ : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      c.nreg pE2 < (chainModel J.right).W.n →
      ProperPos ztj zta P.n ztbii →
      ztlls → c.nreg oB ≤ 1 →
      c.nreg ALLOC + κ * ztcer ≤ W →
      IRS P W c₀ ps c (κ * ztcer) ztjlg
def prI : ℕ := sw 4068
def prK : ℕ := sw 4069
def prB : ℕ := sw 4070
def prX : ℕ := sw 4071
def prE : ℕ := sw 4072
def prH : ℕ := sw 4073
/-- The comparison bits `prO`, `prO + 1`. -/
def prO : ℕ := sw 4074

/-- `oPar = 0`, `i = 0`, `K₂`, the base of the chord records. -/
def prInitL : List Instr :=
  [.constN oPar 0, .constN prI 0, .loadN prK ztbz, .addN prB ztbz K3, .loadN prB prB]

/-- The address of the record of chord `i`. -/
def prAdrL : List Instr :=
  [.addN prX prB prI, .addN prX prX prI, .addN prX prX prI, .addN prX prX prI, .addN prX prX prI]

/-- The end: height code `h + 1`, edge at `+ 2 - oB`. -/
def prEndL : List Instr :=
  [.loadN prH prX, .addN prH prH K1, .addN prX prX K2, .subN prX prX oB, .loadN prE prX]

/-- One chord. -/
def prBody : Stmt :=
  .seq ztvfh (.seq ztvfi (.seq (callOff zted prE prH pE2 pH2 K0 prO)
    (.seq (.ifLtN K0 prO .skip (.ifLtN K0 zttwi .skip (block [.addN oPar prI K1])))
      ztnsg)))

/-- **The parent scan.** -/
def parScan : Stmt := .seq (block prInitL) (.whileLtN prI prK prBody)

/-- The invariant of the scan. -/
def PrInv (P : Polygon) (J : Merge.Junction) (N : NF) (c d : Config) : Prop :=
  EFr ParR c d ∧ d.nreg prK = N.nChords ∧ d.nreg prB = c.nmem ztwxz ∧
  d.nreg prI ≤ N.nChords ∧ d.nreg oPar ≤ d.nreg prI ∧
  (0 < d.nreg oPar → (chainModel J.right).key zta (endPos N (d.nreg oPar - 1)
      ztcce) = (chainModel J.right).key (Qof P) ⟨c.nreg pE2, c.nreg pH2⟩) ∧
  (d.nreg oPar = 0 → ∀ i, i < d.nreg prI → (chainModel J.right).key zta
      ztzln ≠ (chainModel J.right).key zta ztbii)
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c d : Config} {J : Merge.Junction} {N₁ N₂ : NF}
theorem prR_par {r : ℕ} (h1 : sw 4068 ≤ r) (h2 : r < sw 4080) : ParR r := Or.inr by_omega

/-! ## Blocks -/
theorem prAdr_irs (hI : IInv W c₀ d) (hW : d.nreg prB + 5 * d.nreg prI ≤ W) :
    IRS P W c₀ ztvfh d 5 (fun d' => d'.nreg prX = d.nreg prB + 5 * d.nreg prI ∧
      (∀ q, q ≠ prX → d'.nreg q = d.nreg q) ∧ d'.nmem = d.nmem) := by
  simp only [prB, prI, sw, Nat.reduceAdd] at hW
  refine (IRS.block prAdrL hI ?_).mono le_rfl ?_
  · simp [prAdrL, okB, okI, regI, upd, prX, prB, prI, sw, IScr]
    omega
  · zugbf
    simp [prAdrL, regB, regI, upd, prX, prB, prI, sw]
    grind
theorem prEnd_irs (hI : IInv W c₀ d) (hK1 : d.nreg K1 = 1) (hK2 : d.nreg K2 = 2)
    (hW : d.nreg prX + 2 ≤ W) (hh : d.nmem ztvos + 1 ≤ W) :
    IRS P W c₀ ztvfi d 5 (fun d' => d'.nreg prH = d.nmem ztvos + 1 ∧
      d'.nreg prE = d.nmem (d.nreg prX + 2 - d.nreg oB) ∧
      (∀ q, q ≠ prX → q ≠ prH → q ≠ prE → d'.nreg q = d.nreg q) ∧ d'.nmem = d.nmem) := by
  simp only [prX, K1, K2, sw, Nat.reduceAdd] at hK1 hK2 hW hh
  refine (IRS.block prEndL hI ?_).mono le_rfl ?_
  · simp [prEndL, okB, okI, regI, upd, prX, prH, prE, oB, K1, K2, sw, IScr, hK1, hK2]
    omega
  · zugbf
    simp [prEndL, regB, regI, upd, prX, prH, prE, oB, K1, K2, sw, hK1, hK2]
    simp_all

/-! ## One chord -/
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem prBody_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hpe : c.nreg pE2 < (chainModel J.right).W.n)
    (hpp : ProperPos ztj zta P.n ztbii)
    (hp6 : c.nreg pH2 = 0 → 6 ≤ c.nreg pE2) (hoB : c.nreg oB ≤ 1)
    (hId : IInv W c₀ d) (hv : PrInv P J N₂ c d) (hlt : d.nreg prI < d.nreg prK)
    (hroom : d.nreg ALLOC + 11030 ≤ W) :
    IRS P W c₀ prBody d 11030 (fun d' => PrInv P J N₂ c d' ∧
      N₂.nChords - d'.nreg prI < N₂.nChords - d.nreg prI) := by
  obtain ⟨fr, hK, hB, hIK, hPI, hpos, hneg⟩ := hv
  zulid
  set i := d.nreg prI with hi
  zukst
  have kp : ∀ r, ¬ ParR r → 240000 ≤ r ∧ r < 250000 → d.nreg r = c.nreg r :=
    fun r h1 h2 => fr.kkeep h1 h2
  have nPar : ∀ r, (r = sw 4 ∨ r = oB ∨ r = pE2 ∨ r = pH2) → ¬ ParR r ∧ 240000 ≤ r ∧ r < 250000 := by
    zuz
    simp only [oB, pE2, pH2, sw] at hr
    simp only [ParR, oPar, sw]
    omega
  have e4 : d.nreg _ = c.nreg _ := kp _ by_grind (nPar _ ztp).2
  have eB : d.nreg oB = c.nreg oB := by_grind
  have eE2 : d.nreg pE2 = c.nreg pE2 := by_grind
  have eH2 : d.nreg pH2 = c.nreg pH2 := by_grind
  -- the normal form
  zulit
  zudns
  obtain ⟨-, hb2, -⟩ := Restore.nf_bounds hNW
  obtain ⟨r0, r1, r2, -, -⟩ := hNA.2.2.2.2.2.1 i hlt
  have hb2i := hb2 i hlt
  zuki
  have hhn := (regOf_spec E.hNF₂).2.2.2.2.2.1 i hlt
  zuc
  zudnt
  have hmem := fr.2.2
  set Xa := c.nmem ztwxz + 5 * i with hXa
  -- 1. the address
  refine IRS.seq (K₂ := 11025) (prAdr_irs hId by_omega) ?_
  rintro d₁ hI₁ hA₁ hA₁' ⟨a1, a2, a3⟩
  rw [hB] at a1
  zubke
  have m1 : ∀ x, x < c.nreg ALLOC → d₁.nmem x = c.nmem x := fun x hx => by_grind
  -- 2. the end
  refine IRS.seq (K₂ := 11020) (prEnd_irs hI₁ hK₁.2.1 hK₁.2.2.2.2.2.1 by_omega
    by_grind) ?_
  rintro d₂ hI₂ hA₂ hA₂' ⟨b1, b2, b3, b4⟩
  have eB₁ := (a2 _ by_decide).trans eB
  rw [a1, m1 _ by_omega, r0] at b1
  rw [a1, eB₁] at b2
  have hs : (ztkkt : WPos) = endPos N₂ i ztcce := by
    rw [b1, b2]
    zuiqc
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hoB with h0 | h1
    · rw [h0, ite_eq_right by_norm_num, m1 _ by_omega]
      simp only [Nat.sub_zero]
      zukyk
    · rw [h1, ite_eq_left by_norm_num, show Xa + 2 - 1 = Xa + 1 by omega, m1 _ by_omega, r1]; rfl
  have hA := E.hNF₂.2.2.1 i hlt
  have hpE : ProperPos ztj zta P.n ztkkt := by
    zvmyz; unfold endPos; split_ifs
    · exact ⟨hA.1.2.1, hA.1.2.2.1, by show (N₂.chord i).h + 1 ≤ P.n; omega⟩
    · exact ⟨hA.2.2.1, hA.2.2.2.1, by show (N₂.chord i).h + 1 ≤ P.n; omega⟩
  have heE : d₂.nreg prE < (chainModel J.right).W.n := by
    have : (ztkkt : WPos).edge = (endPos N₂ i ztcce).edge := by
      zubqb
    zugzu
    zvmwk; unfold endPos; split_ifs
    · exact hA.1.1
    · exact hA.2.1
  have hH0 : d₂.nreg prH ≠ 0 := by_omega
  have k2 : ∀ q, q ≠ prX → q ≠ prH → q ≠ prE → d₂.nreg q = d.nreg q := by_grind
  have eE2₂ := (k2 _ by_decide
    by_decide by_decide).trans eE2
  have eH2₂ := (k2 _ by_decide
    by_decide by_decide).trans eH2
  zudhh
  have hn0 : ztphm := by_omega
  -- 3. the comparison
  refine IRS.seq (K₂ := 12) (callOff_irs hI₂ ztmas
    ⟨by_decide, by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide, by_decide⟩
    ⟨by_decide, by_decide⟩ heE by_omega
    (by zuogj; omega) hpE by_grind by_grind
    by_omega by_omega) ?_
  rintro d₃ hI₃ hA₃ hA₃' ⟨o1, o2, k₃, ha₃, hm₃⟩
  have hg0 : ((d₂.nreg K0 : ℕ) : ℝ) = 0 := by zuogj; simp
  rw [hg0, Restore.off_zero (Restore.key_nonneg hpE), Restore.off_zero (Restore.key_nonneg
    (by rw [eE2₂, eH2₂]; omega)), hs, eE2₂, eH2₂] at o1 o2
  set kE' := (chainModel J.right).key zta (endPos N₂ i ztcce) with hkE'
  set kP := (chainModel J.right).key zta ztbii with hkP
  have k3 : ∀ q, (q = oPar ∨ q = prI ∨ q = prK ∨ q = prB ∨ q = K0 ∨ q = K1) →
      d₃.nreg q = d.nreg q := by
    zuco
    have hq' : q = 244064 ∨ q = 244068 ∨ q = 244069 ∨ q = 244070 ∨ q = 240610 ∨ q = 240611 := by
      tauto
    rw [k₃ q ztbet ztozs
      ztozs ztu]
    exact k2 q (by unfold prX; unfold sw; omega) (by unfold prH sw; omega) (by unfold prE sw; omega)
  have frd3 : EFr ParR d d₃ := by
    refine ⟨fun r hb hr hra => ?_, by_omega, fun a ha => ?_⟩
    · have h1 : r ≠ prX := by rintro rfl; exact hr (prR_par by_decide by_decide)
      have h2 : r ≠ prH := by rintro rfl; exact hr (prR_par by_decide by_decide)
      have h3 : r ≠ prE := by rintro rfl; exact hr (prR_par by_decide by_decide)
      have h4 : r ≠ prO := by rintro rfl; exact hr (prR_par by_decide by_decide)
      have h5 : r ≠ prO + 1 := by rintro rfl; exact hr (prR_par by_decide by_decide)
      rw [k₃ r hb h4 h5 hra, k2 r h1 h2 h3]
    · rw [hm₃ a by_omega, b4, a3]
  zuhei
  have eI3 : d₃.nreg prI = i := k3 _ by_simp
  have eP3 : d₃.nreg oPar = d.nreg oPar := k3 _ by_simp
  have hiW : ztsiz := by
    omega
  -- the final increment
  have incr : ∀ d₄ : Config, IInv W c₀ d₄ → EFr ParR d d₄ → d₄.nreg prI = i →
      d₄.nreg K1 = 1 → d₄.nreg prK = N₂.nChords → d₄.nreg prB = c.nmem ztwxz →
      d₄.nreg oPar ≤ i + 1 →
      (0 < d₄.nreg oPar → (chainModel J.right).key zta (endPos N₂ (d₄.nreg oPar - 1)
        ztcce) = kP) →
      (d₄.nreg oPar = 0 → ∀ i', i' < i + 1 → (chainModel J.right).key zta
        (endPos N₂ i' ztcce) ≠ kP) →
      IRS P W c₀ ztnsg d₄ 1 (fun d' => PrInv P J N₂ c d' ∧
        N₂.nChords - d'.nreg prI < N₂.nChords - i) := by
    intro d₄ hI₄ fr4 eI eK1 eK eB4 hP1 hP2 hP3
    refine (IRS.block _ hI₄ (by
      zudu
      exact ⟨ztkmb, trivial⟩)).mono le_rfl ?_
    zugbe
    have w1 : d'.nreg prI = i + 1 := by zumzk; simp [regB, regI, eI, eK1]
    have w2 : ∀ r, r ≠ prI → d'.nreg r = d₄.nreg r := fun r hr => by
      zutu
    have fr' : EFr ParR d₄ d' := ⟨fun r _ hr _ => w2 r (by
        rintro rfl; exact hr (prR_par by_rfl by_decide)),
      by zuoos, fun a _ => by zumzk⟩
    have eP : d'.nreg oPar = d₄.nreg oPar := w2 _ by_decide
    refine ⟨⟨fr.trans (fr4.trans fr'), by rw [w2 _ by_decide, eK],
      by rw [w2 _ by_decide, eB4], by_omega, by_omega,
      fun h => by_grind, fun h => by zuogr; rw [eP] at h; exact hP3 h⟩,
      by omega⟩
  have k01 := hK₃.1
  by_cases h1 : d₃.nreg K0 < d₃.nreg prO
  · -- the end is before the position
    zuglf

    have hlt' := o1.2.1 (by have := o1.1; omega)
    refine (IRS.seq (K₁ := 0 + 2) (K₂ := 1) (IRS.ifT h1 zthau) ?_).mono by_norm_num
      ztb
    zukof
    exact incr d₃ hI₃ frd3 eI3 hK₃.2.1 ztkuc ztkub
      by_omega ztbay
      (fun h i' hi' => by
        zuell

        · zulfm
        grind)
  · zuglf

    have hnlt : ¬ kE' < kP := fun h => by have := o1.2.2 h; omega
    by_cases h2 : d₃.nreg K0 < d₃.nreg zttwi
    · zugli

      have hgt := o2.2.1 (by have := o2.1; omega)
      refine (IRS.seq (K₁ := 0 + 2 + 2) (K₂ := 1) (IRS.ifF h1
        (IRS.ifT h2 zthau)) ?_).mono by_norm_num (fun _ h => h)
      zukof
      exact incr d₃ hI₃ frd3 eI3 hK₃.2.1 ztkuc
        ztkub by_omega
        ztbay
        (fun h i' hi' => by
          zuell

          · zulfm
          grind)
    · zugli

      have hngt : ¬ kP < kE' := fun h => by have := o2.2.2 h; omega
      have heq : kE' = kP := by_grind
      refine (IRS.seq (K₂ := 1) (IRS.ifF h1
        (IRS.ifF h2 (IRS.block [.addN oPar prI K1] hI₃ (by
          zudu
          exact ⟨⟨iscr_sw' by_norm_num by_norm_num, by rw [eI3, hK₃.2.1]; omega⟩, trivial⟩)))) ?_).mono by_norm_num
        ztb
      rintro d₄ hI₄ - - hd₄
      have w1 : d₄.nreg oPar = i + 1 := by zungl; simp [regB, regI, eI3, hK₃.2.1]
      have w2 : ∀ r, r ≠ oPar → d₄.nreg r = d₃.nreg r := fun r hr => by
        zuedd
      have fr4 : EFr ParR d₃ d₄ := ⟨fun r _ hr _ => w2 r ztwnm,
        by zuoos, fun a _ => by zungl⟩
      exact incr d₄ hI₄ (frd3.trans fr4) (by rw [w2 _ by_decide, eI3])
        (by rw [w2 _ by_decide, hK₃.2.1])
        (by zunub; exact hK)
        (by zunub; exact hB)
        ztqfg (fun _ => by rw [w1, Nat.add_sub_cancel]; omega)
        by_grind

/-! ## The scan -/
set_option maxHeartbeats 16000000 in
theorem parScan_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hpe : c.nreg pE2 < (chainModel J.right).W.n)
    (hpp : ProperPos ztj zta P.n ztbii)
    (hp6 : c.nreg pH2 = 0 → 6 ≤ c.nreg pE2) (hoB : c.nreg oB ≤ 1)
    (hroom : c.nreg ALLOC + 11040 * ztcer ≤ W) :
    IRS P W c₀ parScan c (11040 * ztcer) ztjlg := by
  zuiw
  zulit
  zudns
  obtain ⟨hb0, -⟩ := Restore.nf_bounds hNW
  zuki
  unfold parScan
  zumfj
  refine (IRS.seq (K₁ := 5) (K₂ := 11032 * N₂.nChords + 2) (IRS.block prInitL hI (by
    simp only [sw, K3, Nat.reduceAdd] at k3 hb0 hAW
    simp [prInitL, okB, okI, regI, upd, oPar, prI, prK, prB, K3, sw, IScr, k3]
    omega)) ?_).mono by_omega (fun _ h => h)
  rintro d hId hA hA' hd
  have v0 : d.nreg oPar = 0 := by zvnej; rfl
  have vI : d.nreg prI = 0 := by zvnej; rfl
  have vK : d.nreg prK = N₂.nChords := by
    zvnej; simp [prInitL, regB, regI, upd, oPar, prI, prK, prB, sw]; exact hNA.1
  have vB : d.nreg prB = c.nmem ztwxz := by
    zvnej; simp [prInitL, regB, regI, upd, oPar, prI, prK, prB, K3, sw]
    tauto
  have frd : EFr ParR c d := by
    zumne
    refine ⟨fun r _ hr _ => regB_other _ _ _ (fun i hi h => hr ?_), ?_, fun _ _ => rfl⟩
    · simp only [prInitL, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> zvmwd at h <;> subst h <;>
        simp only [ParR, oPar, prI, prK, prB, sw] <;> norm_num
    rfl
  have inv0 : PrInv P J N₂ c d := ⟨frd, vK, vB, by_omega, by_omega,
    by simp_all, by_simp_all⟩
  refine (IRS.while _ (fun d => N₂.nChords - d.nreg prI) 11030
    (fun d hv h => by have := hv.2.1; omega)
    (fun d hId hv hlt hroom => prBody_irs E hI hpe hpp hp6 hoB hId hv hlt hroom) hId inv0
    by_omega).mono by_omega ?_
  rintro d' ⟨⟨fr', hK', hB', hIK', hPI, hpos, hneg⟩, hex⟩
  rw [hK'] at hex
  refine ⟨by_omega, hpos, by_grind, fr'.2.2, fr'.2.1,
    fr'.1⟩

/-- **Task P: the parent scan.** -/
theorem parTask : ParTask :=
  ⟨parScan, 11040, fun _ _ _ _ _ _ _ _ _ _ _ _ E hI hpe hpp hp6 hoB hroom =>
    parScan_irs E hI hpe hpp hp6 hoB hroom⟩
end
end SweepEv
open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
open WalkEmbed
@[expose] public section
namespace SweepStop
open Sweep SweepEv SweepIo
variable {J : Merge.Junction}
variable (C : Chain) (Q : Polygon) {z : Point} {a : Point} {P : Polygon} {N : NF}
/-- **Height code `0` strictly inside the height band** is a tour position. -/
theorem h6_of_abs {x : WPos}
    (hy : |((chainModel C).pos Q x).2| < C.radius) (h0 : x.hgt = 0) : 6 ≤ x.edge := by
  zubkw
  zujpd
  zubvi
  zube

  have hv : (chainModel C).pos Q ztjy = (chainModel C).W.vtx e := by
    show sidePt _ e ztymr = _
    rw [show (chainModel C).param Q ztjy = 0 from rfl, Chazelle.Chain.sidePt_zero]
  rw [hv, Restore.chain_box_vtx_abs C hlt] at hy
  simp_all

/-- Points of `C₁` or of the box are off the domain of `C`. -/
theorem onCB_not_dom_left (h : OnCB J.left z) : z ∉ J.whole.dom := by
  zudqe
  zuljo
  zude
  · exact J.whole.not_mem_set_of_mem_dom hd ztpzf
  · have := hb.1; zvmwc at this; exact lt_irrefl _ this
  · have := hb.2; zvmwc at this; exact lt_irrefl _ this

/-- Points of `C₂` or of the box are off the domain of `C`. -/
theorem onCB_not_dom_right (h : OnCB J.right z) : z ∉ J.whole.dom := by
  zudqe
  zuljo
  zude
  · exact J.whole.not_mem_set_of_mem_dom hd ztjjc
  · have := hb.1; zvmwc at this; exact lt_irrefl _ this
  · have := hb.2; zvmwc at this; exact lt_irrefl _ this

/-- **The far end sees the origin back.** -/
theorem far_free (ha : a.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hf : FreeAt C a σ) : FreeAt C zthwq (-σ) := by
  zueim
  show ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt zthwq (-σ) s ∈ C.dom
  zunv
  zulbs

  simp_all

/-- **Only the candidate of `C₂`**: without a first hit of `C₁` it is the first hit of `C`. -/
theorem win_only2 (ha : a.2 ≤ J.right.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hf : FreeAt J.whole a σ) (hno : ¬ (FreeAt J.left a σ ∧ a.2 ≤ J.left.top.2)) {τ₂ : ℝ}
    (h2 : τ₂ = J.right.hitParam a σ) : τ₂ = J.whole.hitParam a σ := by
  rcases hit_cases ha hσ with h | ⟨h1, h⟩
  · simp_all
  · exact absurd ⟨free_left hf h1, h1⟩ hno

/-- **The nearer candidate** is the first hit of `C`. -/
theorem win_min (ha : a.2 ≤ J.right.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hf : FreeAt J.whole a σ) {τ₁ τ₂ τ : ℝ} (h1 : 0 < τ₁) (h1o : OnCB J.left ztruy)
    (h1g : FreeAt J.left a σ ∧ a.2 ≤ J.left.top.2 → τ₁ = J.left.hitParam a σ)
    (h2 : 0 < τ₂) (h2o : OnCB J.right (rayPt a σ τ₂)) (h2g : τ₂ = J.right.hitParam a σ)
    (hτ : τ = τ₁ ∨ τ = τ₂) (hτ1 : τ ≤ τ₁) (hτ2 : τ ≤ τ₂) : τ = J.whole.hitParam a σ := by
  have haW : ztlal := le_trans ha J.right_top_le
  refine hit_min hσ haW hf (L := {τ₁, τ₂}) ?_ ?_ ?_ ?_
  · zuh
    rcases hx with rfl | hx
    · exact ⟨h1, onCB_not_dom_left h1o⟩
    · rw [mem_singleton_iff] at hx; subst hx
      exact ⟨h2, onCB_not_dom_right h2o⟩
  · rcases hit_cases ha hσ with h | ⟨hl, h⟩
    · simp_all
    · rw [h, ← h1g ztrcj]; simp
  · simp_all
  simp_all

/-! ## The origins in the walk of `C₂` -/
theorem right_v_pos :
    (chainModel J.right).pos Q ztexj = J.shared := by
  show sidePt _ _ ((chainModel J.right).param Q ztexj) = _
  rw [show (chainModel J.right).param Q ztexj = 0 from rfl,
    Chazelle.Chain.sidePt_zero, vtx_tpos' J.right ztbg, J.right_vertex_zero]
theorem right_top_pos : (chainModel J.right).pos Q ztbcw = J.right.top := by
  show sidePt _ _ ((chainModel J.right).param Q ztbcw) = _
  rw [show (chainModel J.right).param Q ztbcw = 0 from rfl]
  exact (sidePt_top_copies J.right).1

/-- The top of `C₂` is off `C₁` unless it is the shared vertex. -/
theorem top_not_left (hP : J.P.Simple) (ht : J.right.topIdx ≠ 0) : J.right.top ∉ J.left.set :=
  J.right_vertex_not_mem_left hP (Nat.pos_of_ne_zero ht) J.right.topIdx_le

/-! ## The parent of a shared or top chord -/

/-- The point of the end `1 - b` of a chord record. -/
theorem endPos_pt (hN : IsNF ztj zta N) {i b : ℕ}
    (hi : i < N.nChords) (hb : b ≤ 1) :
    (chainModel J.right).pos zta ztxdz =
      (if b = 1 then Merge.lend ztxje
        else Merge.rend ztxje) := by
  have hj : 2 * i + ztlp < 2 * N.nChords := by_omega
  zufyb
  rw [show ztzat / 2 = i by omega, show ztzat % 2 = 1 - b by omega] at hEO
  rw [← hEO]
  zulbr
  grind

/-- The attachment of a chord record at its end. -/
theorem endPos_attach (hN : IsNF ztj zta N) {i : ℕ}
    (hi : i < N.nChords) (s : ℕ) :
    SideAttach (chainModel J.right).W ztxje
      (endPos N i s).edge ((chainModel J.right).param zta (endPos N i s)) := by
  have hA := hN.2.2.1 i hi
  zuhan
  · exact hA.1
  · exact hA.2

/-- **The parent of a shared or top chord**: the chord record `i` contains the chord of `a` in the
direction of code `b` iff its end `1 - b` has the key of the arrival position of `a` in the walk
of `C₂`. -/
theorem parent_key_iff (hP : J.P.Simple) {P : Polygon} {N : NF}
    (hN : IsNF ztj zta N) {a : Point} (haR : a ∈ J.right.set) {b : ℕ}
    (hb : b ≤ 1) (hf : FreeAt J.whole a ztkz) {p h : ℕ}
    (hA : Arrival (chainModel J.right).W a ztcrx p ztynf)
    {i : ℕ} (hi : i < N.nChords) :
    (chainModel J.right).key zta ztxdz =
        (chainModel J.right).key zta ztnk ↔
      Merge.shoot J.whole a ztkz ⊆ (N.chord i).toSet ztj zta := by
  have hS₂ := hN.1.2.1
  have hc := chord_mem (M := chainModel J.right) (Q := Qof P) hi
  have hAt := endPos_attach hN hi ztlp
  have hpt := endPos_pt hN hi hb
  zudia
  have hiff := parent_vt_iff hP hS₂ haR hb hf hc
  set c := (N.chord i).toSet ztj zta with hcdef
  zuhqn
  constructor
  · zuibt
    obtain ⟨he, ht⟩ := Chazelle.Chain.sideKey_inj hAt.2.1 hAt.2.2.1 hA.2.1 hA.2.2.1 hk
    have hpa : (chainModel J.right).pos zta ztxdz = a := by
      show sidePt _ _ _ = _
      rw [he, ht]; exact hA.2.2.2.1
    grind
  · intro hsub
    have hend := hiff.1 hsub
    -- the chord is the chord of `C₂` seen from `a`
    obtain ⟨y, l, r, hH, -, heq, hl, hr⟩ := Merge.augChords_spec ztbac
    have hcs : c = Merge.shoot J.right a ztkz := by
      rcases hend with ⟨rfl, h⟩ | ⟨rfl, h⟩
      · rw [dirOf_one, ← h, hl, heq]; exact Merge.hseg_eq_shoot J.right hH
      · rw [dirOf_zero, ← h, hr, heq]; exact Merge.hseg_eq_shoot_neg J.right hH
    zueqv
    have hay := J.right.snd_le_top_of_mem_set haR
    have hfR := free_right hf hay
    have hA' := attach_of_origin (C := J.right) hP hay haD hσ hfR hA
    rw [← hcs] at hA'
    have hM : WalkAx ztj := FactsChain.walkAx J.right hP
    have hpa : sidePt (chainModel J.right).W (endPos N i ztlp).edge
        ((chainModel J.right).param zta ztxdz) = a := by
      show (chainModel J.right).pos zta ztxdz = a
      grind
    obtain ⟨e1, e2⟩ := hM.attach_unique ztbac hAt hA' (by rw [hpa, hA.2.2.2.1])
    simp_all
end SweepStop
end
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
def oAd : ℕ := sw 4019
def tX : ℕ := sw 4092
def tH : ℕ := sw 4093
def tL : ℕ := sw 4094
def tR : ℕ := sw 4095

/-- **The position of the origin** of the code `(kind, k, b)` in the walk of `C₂`. -/
def OrgPos (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b e h : ℕ) : Prop :=
  e < (chainModel J.right).W.n ∧ ProperPos ztj zta P.n ztcq ∧
    PosClass J.right zta ztcq ∧
    (chainModel J.right).pos zta ztcq = stOrig J zta N kind k b ∧
    (kind ≠ 1 → h = 0 ∧ 6 ≤ e ∧ e < 2 * J.right.m + 6) ∧
    (kind = 1 → (ztcq : WPos) = endPos N k ztlp)

/-- The post of `stLoad`. -/
def LdOK (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) (c : Config) : Prop :=
  c.nreg oNB = 1 - b ∧ c.nreg oAd ≤ 1 ∧ (c.nreg oAd = 1 ↔ StOK P J N kind k b) ∧
    (c.nreg oAd = 1 → OrgPos P J N kind k b ztdzo ztdzp)

/-- The registers the branches of `stLoad` write. -/
def LdW₀ (r : ℕ) : Prop := r = oPE ∨ r = oPH ∨ r = oAd ∨ (tX ≤ r ∧ r ≤ tR)

/-- The registers `stLoad` writes. -/
def LdW (r : ℕ) : Prop := r = oNB ∨ LdW₀ r

/-! ## The program -/
def ldV : List Instr := [.copyN oPE ztbex, .constN oPH 0, .constN oAd 1]
def ldT : Stmt :=
  .seq (block [.constN oPE 6, .constN oPH 0])
    (.ifLtN K0 cTop ztoun ztoum)
def ldRd : List Instr :=
  [.addN tX ztbz K3, .loadN tX tX, .addN tX tX oKk, .addN tX tX oKk, .addN tX tX oKk,
    .addN tX tX oKk, .addN tX tX oKk, .loadN tH tX, .addN tX tX K1, .loadN tL tX,
    .addN tX tX K1, .loadN tR tX, .addN oPH tH K1]
def ldW : Stmt :=
  .seq (block ldRd) (.seq ztfmh
    (.ifLtN oPE K6 ztoun ztoum))

/-- **The origin of a code.** -/
def stLoad : Stmt :=
  .seq (.instr (.subN oNB K1 oB)) (.ifLtN oKd K1 ztvff (.ifLtN K1 oKd ldT ldW))

/-! ## A one-register assignment -/
theorem set1_irs (hI : IInv W c₀ c) {r v : ℕ} (hr : 240700 ≤ r ∧ r < 250000) (hv : v ≤ W) :
    IRS P W c₀ ztcyq c 1 (fun c' => c'.nreg r = v ∧
      ztbcc ∧ c'.nmem = c.nmem) := by
  refine (IRS.instr1 (i := .constN r v) hI ztrdn).mono le_rfl ?_
  zuu
  zumkd
theorem copy1_irs (hI : IInv W c₀ c) {r a : ℕ} (hr : 240700 ≤ r ∧ r < 250000) :
    IRS P W c₀ ztdsf c 1 (fun c' => c'.nreg r = c.nreg a ∧
      ztbcc ∧ c'.nmem = c.nmem) := by
  refine (IRS.instr1 (i := .copyN r a) hI zttpo).mono le_rfl ?_
  zuu
  zumkd

/-! ## The branches -/
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}
theorem orgPos_v (P : Polygon) (N : NF) (k b : ℕ) :
    OrgPos P J N 0 k b ztbrv 0 := by
  zubau
  zudhu
  have hp0 : (chainModel J.right).param zta ztexj = 0 := rfl
  refine ⟨by_omega, ztcfo,
    Or.inr by_grind, ?_, by_omega, by_omega⟩
  rw [right_v_pos]; rfl
theorem orgPos_t (P : Polygon) (N : NF) (k b : ℕ) : OrgPos P J N 2 k b 6 0 := by
  zudhu
  zumay
  have hp0 : (chainModel J.right).param zta ztbcw = 0 := rfl
  refine ⟨by_omega, ztcfo,
    Or.inr by_grind, ?_, by_omega, by_omega⟩
  rw [right_top_pos]; rfl
theorem orgPos_w (hP : J.P.Simple) (hN : IsNF ztj zta N₂) {k b : ℕ}
    (hk : k < N₂.nChords) (hb : b ≤ 1) :
    OrgPos P J N₂ 1 k b (endPos N₂ k ztlp).edge (endPos N₂ k ztlp).hgt := by
  obtain ⟨hcl, -⟩ := end_off_iff hP hN hk (s := 1 - b)
  zuivo
  zucwi
  zuc
  refine ⟨hA.1, ztrcq, hcl, ?_, by_omega, by_simp_all⟩
  · unfold endPos; split_ifs <;> show (N₂.chord k).h + 1 ≤ P.n <;> omega
  · exact (stOrig_wall hN hk hb).1.symm

/-! ## The read of the chord record -/
variable (m f : ℕ → ℕ)
theorem ldRd_val (hk1 : f K1 = 1) (hk3 : f K3 = 3) :
    regB m ldRd f tH = m ztbale ∧
    regB m ldRd f tL = m (m ztwkt + 5 * f oKk + 1) ∧
    regB m ldRd f tR = m (m ztwkt + 5 * f oKk + 2) ∧
    regB m ldRd f oPH = m ztbale + 1 := by
  zubx
  zubtd
  simp only [ldRd, regB, regI, upd, tX, oKk, tH, tL, tR, oPH, K1, K3, sw]
  grind
theorem ldRd_other {q : ℕ} (h : q ≠ tX ∧ q ≠ tH ∧ q ≠ tL ∧ q ≠ tR ∧ q ≠ oPH) :
    regB m ldRd f q = f q :=
  regB_other m ldRd f (fun i hi => by
    simp only [ldRd, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zvmwd <;> intro he <;> subst he <;> simp at h)
theorem ldRd_ok (hk1 : f K1 = 1) (hk3 : f K3 = 3) (hb : f ztbz + 3 ≤ W)
    (hb2 : m ztwkt + 5 * f oKk + 4 ≤ W) (hh : m ztbale + 1 ≤ W) :
    okB W m ldRd f := by
  zubx
  zubtd
  have s : ∀ j, 4092 ≤ j → j ≤ 4095 → IScr ztjfo := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  have sH : IScr (240000 + 4015) := iscr_sw by_omega by_omega
  zufuk
  have hb2' : m ztcnb + 5 * f 244011 + 4 ≤ W := hb2
  have hh' : m (m ztcnb + f 244011 + f 244011 + f 244011 + f 244011 + f 244011) + 1 ≤ W := by
    have : m ztcnb + f 244011 + f 244011 + f 244011 + f 244011 + f 244011 =
      m ztcnb + 5 * f 244011 := by_ring
    zujls
  simp only [ldRd, okB, okI, regI, upd, tX, oKk, tH, tL, tR, oPH, K1, K3, sw]
  grind

/-! ## The main lemma -/

/-- The post of a branch of `stLoad`. -/
def LdBr (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) (c₁ c' : Config) : Prop :=
  (∀ q, ¬ LdW₀ q → c'.nreg q = c₁.nreg q) ∧ c'.nmem = c₁.nmem ∧ c'.nreg oAd ≤ 1 ∧
    (c'.nreg oAd = 1 ↔ StOK P J N kind k b) ∧
    (c'.nreg oAd = 1 → OrgPos P J N kind k b (c'.nreg oPE) (c'.nreg oPH))
theorem ldV_irs (hI : IInv W c₀ c) (hfx : Fx P W J c) {k b : ℕ} (hb : b ≤ 1) (hW : 1 ≤ W) :
    IRS P W c₀ ztvff c 3 (LdBr P J N₂ 0 k b c) := by
  refine (IRS.block ldV hI ?_).mono by_rfl ?_
  · simp only [ldV, okB, okI]
    exact ⟨iscr_sw by_decide by_decide,
      ⟨iscr_sw by_decide by_decide, Nat.zero_le _⟩,
      ⟨iscr_sw by_decide by_decide, hW⟩, trivial⟩
  · zuu
    zujxs
    simp only [cstR, List.getD_cons_zero, List.getD_cons_succ] at g1
    have vE : regB c.nmem ldV c.nreg oPE = 6 + tpos J.right 0 := by
      tauto
    have vH : regB c.nmem ldV c.nreg oPH = 0 := by
      rfl
    have vA : regB c.nmem ldV c.nreg oAd = 1 := by
      rfl
    refine ⟨fun q hq => ?_, rfl, by_rfl, ⟨fun _ => ⟨by_norm_num, hb,
      by omega, by_omega⟩, by_simp_all⟩, fun _ => by simp only; rw [vE, vH]; exact orgPos_v P N₂ k b⟩
    zubi
    zunn
    simp only [ldV, List.mem_cons, List.not_mem_nil, or_false] at hi
    zujpv
    rcases hi with rfl | rfl | rfl <;> zvmwd <;> intro he <;> subst he <;> tauto
theorem ldT_irs (hI : IInv W c₀ c) (hO : OrgK P J c) (hK : Consts c) {k b : ℕ} (hb : b ≤ 1)
    (hW : 6 ≤ W) :
    IRS P W c₀ ldT c 7 (LdBr P J N₂ 2 k b c) := by
  unfold ldT
  refine IRS.seq (K₂ := 5) ztleu ?_
  · zudu
    exact ⟨⟨iscr_sw by_decide by_decide, hW⟩,
      ⟨iscr_sw by_decide by_decide, Nat.zero_le _⟩, trivial⟩
  zuer
  set c₁ : Config := { c with nreg := regB c.nmem [.constN oPE 6, .constN oPH 0] c.nreg } with hc₁
  have vE : c₁.nreg oPE = 6 := by
    rfl
  have vH : c₁.nreg oPH = 0 := by
    rfl
  have ko : ∀ q, q ≠ oPE → q ≠ oPH → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    simp only [hc₁, regB, regI, upd, ite_eq_right h1, ite_eq_right h2]
  have k0 : zteib := by zuogs; exact hK.1
  have kT : ztuqp := by
    zuogs; exact hO.top
  have post : ∀ v, v ≤ 1 → (v = 1 ↔ J.right.topIdx ≠ 0) → ∀ c', c'.nreg oAd = v ∧
      (∀ q, q ≠ oAd → c'.nreg q = c₁.nreg q) ∧ c'.nmem = c₁.nmem → LdBr P J N₂ 2 k b c c' := by
    zufmd
    have e1 : c'.nreg oPE = 6 := by rw [a2 _ by_decide, vE]
    have e2 : c'.nreg oPH = 0 := by rw [a2 _ by_decide, vH]
    refine ⟨fun q hq => ?_, a3, by_omega, ?_, fun _ => by
      zvmws; exact orgPos_t P N₂ k b⟩
    · zujpv
      simp_all
    · zukqb
      exact ⟨fun h => ztexs,
        fun h => h.2.2.2 rfl⟩
  zura
  · refine (set1_irs hI₁ ztkp
      by_omega).mono by_norm_num (post 1 le_rfl by_omega)
  · refine (set1_irs hI₁ ztkp
      by_omega).mono by_norm_num (post 0 by_norm_num by_omega)
set_option maxHeartbeats 1000000 in
theorem ldW_irs (hI : IInv W c₀ c) (hK : Consts c) (hP : J.P.Simple)
    (hN : IsNF ztj zta N₂) {E : ℕ} (hNW : NFWithin c.nmem ztwrb E N₂)
    (hEW : E ≤ W) (hPn : P.n ≤ W) {k b : ℕ} (hkk : c.nreg oKk = k) (hk : k < N₂.nChords)
    (hb : b ≤ 1) (hNB : c.nreg oNB = 1 - b) :
    IRS P W c₀ ldW c 21 (LdBr P J N₂ 1 k b c) := by
  zucnq
  zudns
  zuicm
  obtain ⟨r0, r1, r2, -, -⟩ := hch k hk
  zucwi
  zuc
  zubof
  zumfj
  zumfl
  unfold ldW
  refine IRS.seq (K₂ := 8) (IRS.block ldRd hI (ldRd_ok c.nmem c.nreg k1 k3
    by_omega by_grind (by
      grind))) ?_
  zuer
  obtain ⟨vH, vL, vR, vPH⟩ := ldRd_val c.nmem c.nreg k1 k3
  set c₁ : Config := { c with nreg := regB c.nmem ldRd c.nreg } with hc₁
  rw [hkk] at vH vL vR vPH
  have ko : ∀ q, q ≠ tX → q ≠ tH → q ≠ tL → q ≠ tR → q ≠ oPH → c₁.nreg q = c.nreg q :=
    fun q a1 a2 a3 a4 a5 => ldRd_other _ _ by_omega
  have c1NB : c₁.nreg oNB = 1 - b := by
    tauto
  have c1K1 : ztcpf := by
    tauto
  have c1K6 : ztpmz := by
    tauto
  have c1PH : c₁.nreg oPH = (endPos N₂ k ztlp).hgt := by
    show regB c.nmem ldRd c.nreg oPH = _
    rw [vPH, r0]; unfold endPos; split_ifs <;> rfl
  -- the edge
  have hpick : IRS P W c₀ ztfmh c₁ 3
      (fun c₂ => c₂.nreg oPE = (endPos N₂ k ztlp).edge ∧
        (∀ q, q ≠ oPE → c₂.nreg q = c₁.nreg q) ∧ c₂.nmem = c₁.nmem) := by
    zura
    · zucbu

      show regB c.nmem ldRd c.nreg tL = _
      rw [vL, r1]; unfold endPos; zunab; rfl
    · zucbu

      show regB c.nmem ldRd c.nreg tR = _
      rw [vR, r2]; unfold endPos; zvmyd; rfl
  refine (IRS.seq (K₂ := 3) hpick ?_).mono by_norm_num ztb
  rintro c₂ hI₂ - - ⟨e2, k2, m2⟩
  have c2K6 : zturp := by rw [k2 _ by_decide, c1K6]
  have hwp := orgPos_w hP hN hk hb
  have post : ∀ v, v ≤ 1 → (v = 1 ↔ (endPos N₂ k ztlp).edge < 6) → ∀ c', c'.nreg oAd = v ∧
      (∀ q, q ≠ oAd → c'.nreg q = c₂.nreg q) ∧ c'.nmem = c₂.nmem → LdBr P J N₂ 1 k b c c' := by
    zufmd
    have eE : c'.nreg oPE = (endPos N₂ k ztlp).edge := by
      rw [a2 _ by_decide, e2]
    have eH : c'.nreg oPH = (endPos N₂ k ztlp).hgt := by
      rw [a2 _ by_decide, k2 _ by_decide, c1PH]
    refine ⟨fun q hq => ?_, by_grind, by_omega, ?_, by_grind⟩
    · zujpv
      rw [a2 q by_omega,
        k2 q by_omega,
        ko q (fun h => hq ((Or.inr (Or.inr ztgqp))))
          ztxih
          ztxih
          (fun h => hq ((Or.inr (Or.inr (Or.inr ⟨by zvmwc; decide, by zvmwc⟩)))))
          by_omega]
    · zukqb
      exact ⟨fun h => ztexs,
        fun h => (h.2.2.1 rfl).2⟩
  zura
  · refine (set1_irs hI₂ ztkp
      by_omega).mono le_rfl (post 1 le_rfl by_omega)
  · refine (set1_irs hI₂ ztkp
      by_omega).mono le_rfl (post 0 by_norm_num by_omega)

/-- **The origin of a code** as a run step. -/
theorem stLoad_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hkd : c.nreg oKd ≤ 2) (hb : c.nreg oB ≤ 1) (hk : c.nreg oKd = 1 → c.nreg oKk < N₂.nChords)
    (hroom : c.nreg ALLOC + 30 ≤ W) :
    IRS P W c₀ stLoad c 30 (fun c' => LdOK P J N₂ ztka ztij ztfb c' ∧
      EFr LdW c c') := by
  zuiw
  zubof
  unfold stLoad
  refine IRS.seq (K₂ := 29) (IRS.instr1 hI
    ztbua) ?_
  rintro c₁ hI₁ - hA₁ rfl
  set c₁ : Config := { c with nreg := regI c.nmem (.subN oNB K1 oB) c.nreg } with hc₁
  have vNB : c₁.nreg oNB = 1 - c.nreg oB := by simp [hc₁, regI, upd, k1]
  have ko : ∀ q, q ≠ oNB → c₁.nreg q = c.nreg q := fun q hq => by simp [hc₁, regI, upd, hq]
  have kKd : c₁.nreg oKd = c.nreg oKd := ko _ by_decide
  have kKk : c₁.nreg oKk = c.nreg oKk := ko _ by_decide
  have kK1 := (ko _ by_decide).trans k1
  have hW := hroom
  have post : ∀ kind, kind = c.nreg oKd → ∀ c', LdBr P J N₂ kind ztij ztfb c₁ c' →
      LdOK P J N₂ ztka ztij ztfb c' ∧ EFr LdW c c' := by
    rintro kind rfl c' ⟨a1, a2, a3, a4, a5⟩
    have hnb : c'.nreg oNB = c₁.nreg oNB := a1 _ (by unfold LdW₀ oNB oPE oPH oAd tX tR sw; omega)
    have hA : ztble := by
      rw [a1 _ (by unfold LdW₀ ALLOC oPE oPH oAd tX tR sw; omega), ko _ by_decide]
    refine ⟨⟨by_omega, a3, a4, a5⟩, fun r _ h2 _ => ?_, by zvmze, fun a _ => by zungr⟩
    unfold LdW at h2
    simp_all
  refine IRS.ite ztfrp ztfrp
  · have hk0 : c.nreg oKd = 0 := by_omega
    refine (ldV_irs hI₁ ztpxk hb by_omega).mono by_norm_num
      (post 0 hk0.symm)
  refine IRS.ite ztczl ztczl
  · zukcy
    refine (ldT_irs hI₁ (E.hO.fix hI₁) ztuxx hb
      by_omega).mono by_norm_num (post 2 hk2.symm)
  · zukcx
    have hNW : ztyua := by
      have h4 : c₁.nreg _ = c₀.nreg ztbz := hI₁.hin _ by_trivial
      zujic
      exact E.hNW₂.transport hI₁.hm
    zudnt
    refine (ldW_irs hI₁ ztuxx E.hP E.hNF₂ hNW (by have := hI₁.hA; omega)
      hPn kKk (hk hk1) hb vNB).mono by_norm_num by_simp_all
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)
@[expose] public section
def m2F : ℕ := sw 4024
def r1F : ℕ := sw 4030
def r2F : ℕ := sw 4040
def a1F : ℕ := sw 4050

/-! ## The candidate of `C₂` -/

/-- The registers the candidate of `C₂` may write (besides the oracle bands and the allocator). -/
def M2R (r : ℕ) : Prop :=
  ztgz ∨ ztph ∨ (sw 4024 ≤ r ∧ r ≤ sw 4026) ∨
    ztltv ∨ ztlty ∨ ztbgd

/-- **The post of the candidate of `C₂`**: a saved candidate of the first hit of `C₂` from the
origin (`ResOK` at `r2F`, good when the direction is free for `C₂`); for the shared and top codes
(origin on `C₂`), if the direction is free for `C₂`, the arrival position `(pE2, pH2)` of the origin
in the walk of `C₂` (direction `-σ`). -/
def M2Out (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) (c' : Config) : Prop :=
  ResOK P J.right ztwjf ztkz
      (FreeAt J.right ztwjf ztkz) r2F c' ∧
    (kind ≠ 1 → FreeAt J.right ztwjf ztkz →
      c'.nreg pE2 < (chainModel J.right).W.n ∧
      ProperPos ztj zta P.n ztrba ∧
      Arrival (chainModel J.right).W ztwjf ztcrx (c'.nreg pE2)
        ((chainModel J.right).param zta ztrba))

/-- **Task M2: the candidate of `C₂`** for an admissible code with a free direction (`OrgD`), from
the origin's position `(oPE, oPH)` in the walk of `C₂` (`OrgPos`), with the model context of `C₂`
at `gMD2, gCD2, sw 4`, cost `κ D (F γ + TLR + 1)`.  (Shared and top codes: `callArr` in the walk
of `C₂` from `(oPE, oPH)`, then `lhSave` from the arrival; wall codes: `lhSave` from
`(oPE, oPH)`.) -/
def M2Task : Prop :=
  ∃ (m2 : Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz c →
      OrgD P J N₂ ztka ztij ztfb →
      OrgPos P J N₂ ztka ztij ztfb ztdzo ztdzp →
      c.nreg ALLOC + κ zto * ztwit ≤ W →
      IRS P W c₀ ztvyo c ztbajz
        ztwlw

/-! ## The candidate of `C₁` -/

/-- The registers the candidate of `C₁` may write (besides the oracle bands and the allocator). -/
def M1R (r : ℕ) : Prop :=
  ztgz ∨ ztph ∨ (sw 4027 ≤ r ∧ r ≤ sw 4036) ∨
    (sw 4068 ≤ r ∧ r < sw 4092) ∨ ztlty ∨ ztbgd

/-- **Task M1: the candidate of `C₁`** (`ResOK` at `r1F`, good when the origin is not above the
top of `C₁` and the direction is free for `C₁`) for an admissible code with a free direction, from
the origin's position `(oPE, oPH)` in the walk of `C₂`, cost `κ D (F γ + TLR + 1)` for a wall code,
`κ D (K₁ + K₂ + 1) (F γ + TLR + 1)` otherwise.  (Shared code: `callArr` in the walk of `C₁` from
`(cstL 1, 0)`, then `lhSave` with `MD₁, CD₁, sw 3`; wall code: `lhSave` from `(oPE, oPH)` in the
walk of `C₁` (`boxTwin_pos`); top code: unless the top of `C₂` is above the top of `C₁`, the
brute-force shot `BruteTask` from it.) -/
def M1Task : Prop :=
  ∃ (m1 : Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      OrgD P J N₂ ztka ztij ztfb →
      OrgPos P J N₂ ztka ztij ztfb ztdzo ztdzp →
      c.nreg ALLOC + κ zto * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ ztvyl c (κ zto * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))
        (fun c' => ResOK P J.left ztwmw
          ztwow
          (FreeAt J.left ztwmw
              ztwow ∧
            (stOrig J zta N₂ ztka ztij ztfb).2 ≤ J.left.top.2)
          r1F c' ∧ EFr M1R c c')

/-! ## The finish: offsets, parent, labels, records -/

/-- **The precondition of the finish**: the attachment `A₀` at the origin (`oF0 + 1, oF0 + 2`,
the arrival of the origin in direction `-σ`), the attachment `A₁` at the far end
(`a1F + 1, a1F + 2`, the arrival of `farPt` in direction `σ`), both positions of the walk of `C`;
for the shared and top codes the arrival position `(pE2, pH2)` of the origin in the walk of
`C₂`. -/
def FinPre (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) (c : Config) : Prop :=
  c.nreg ztjf < (chainModel J.whole).W.n ∧
    ProperPos ztbm zta P.n ztwvh ∧
    Arrival (chainModel J.whole).W ztwjf ztcrx ztyis
      ztbalc ∧
    c.nreg ztlq < (chainModel J.whole).W.n ∧
    ProperPos ztbm zta P.n ztxhw ∧
    Arrival (chainModel J.whole).W ztbakp
      ztkz ztbagr
      ztbano ∧
    (kind ≠ 1 → c.nreg pE2 < (chainModel J.right).W.n ∧
      ProperPos ztj zta P.n ztbii ∧
      Arrival (chainModel J.right).W ztwjf ztcrx ztvju
        ztynb)

/-- **Task Fin: the finish of the per-origin step** for an admissible code with a free direction:
the offsets of `A₀`, `A₁` (`callOff` against `Lst` and `0`: the records on the `C₁` part, anchor,
pocket, `anc_pocket_iff`), the parent (`k + 1` for a wall code, else `ParTask` from `(pE2, pH2)`,
`parent_key_iff`), the labels (the regions `up, dn` of the parent, else `FaceRTask` at the
counterpart of the stretch attachment, `LabTask`, `NoParCut`), and the raw records of `A₀`
(`dc = b`) and `A₁` (`dc = 1 - b`) on the `C₁` part (`orig_attach`, `attach_two`), as `OrgOut`.
Cost as `OrgTask`. -/
def FinTask : Prop :=
  ∃ (fin : Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      OrgD P J N₂ ztka ztij ztfb →
      FinPre P J N₂ ztka ztij ztfb c →
      c₀.nreg ALLOC ≤ c.nreg gRB → c.nreg gRB + 11 * ztees ≤ c.nreg ALLOC →
      c.nreg ALLOC + κ zto * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ fin c (κ zto * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))
        ztwrn

/-! ## The counterpart of a stretch attachment without a parent (mathematics) -/

/-- **Task N (mathematics)**: a stop chord `e ∈ F₂⁺` contained in no chord of `S₂`, attached at
the position `(gW + d, t)` of the open right stretch inside a walk edge (`0 < t < 1`): the
counterpart key `cpA d + t` of the walk of `C₂` is not a cut of `S₂` (a chord of `S₂` attached
there contains a chord of `F₂⁺` attached at `(gW + d, t)`, `Corr0.transfer`; two chords of `F₂⁺`
attached at the same position inside a walk edge are nested, hence equal, `Corr0.nest`). -/
def NoParCut : Prop :=
  ∀ (J : Merge.Junction) (Q : Polygon) (S₂ : Set ztf) (e : Set Point), J.P.Simple →
    (chainModel J.right).ChordFamily Q S₂ → e ∈ F₂plus J S₂ → ztluu →
    ∀ (d : ℕ) (t : ℝ), d < Lst J → 0 < t → t < 1 →
    SideAttach (chainModel J.whole).W e ztfq t →
    ¬ (chainModel J.right).IsCut S₂ ((cpA J d : ℝ) + t)
theorem npc_inner_unique {M : Model} (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    {c c' : Set Point} (hc : c ∈ F) (hc' : c' ∈ F) {p : ℕ} {t : ℝ} (ht : 0 < t)
    (hA : SideAttach M.W c p t) (hA' : SideAttach M.W c' p t) : c = c' := by
  zuct
  zuxr
  · exact absurd (hM.tie_shape hF hc hc' hA hA' h1 h2).1 ht.ne'
  · exact absurd (hM.tie_shape hF hc' hc hA' hA h2 h1).1 ht.ne'

/-- **Task N: no cut at the counterpart of a stretch attachment without a parent.** -/
theorem noParCut : NoParCut := by
  intro J Q S₂ e hP hS₂ he hno d t hd ht0 ht1 heA ⟨c, hc, p, t', hA, hkey⟩
  zucf
  have hd' : ztizq := hd
  obtain ⟨hp, htt⟩ := Chazelle.Chain.sideKey_inj ht0.le ht1 hA.2.1 hA.2.2.1 hkey
  have hA2 : SideAttach (chainModel J.right).W c
      ztwmz t := by
    have h : SideAttach (chainModel J.right).W c ztbcq t := by_simp_all
    zubh
  obtain ⟨e', he', he'c, -, he'A⟩ := hC.transfer hd' ht0.le ht1 (fun h => absurd h ht0.ne') hc hA2
  have heA' : SideAttach (chainModel J.whole).W e
      ztbn t := heA
  have := npc_inner_unique hC.hM hC.hF he he' ht0 heA' he'A
  simp_all
def slfStSeq (x : ℕ) : List ℕ → Stmt
  | [] => .skip
  | v :: vs => .seq ztowe (.seq (block [.addN x x K1]) ztuao)
variable {P : Polygon} {W : ℕ} {c₀ : Config}
set_option maxHeartbeats 4000000 in
/-- **Storing a list of registers.** -/
theorem slfStSeq_irs {x : ℕ} (hx : IScr x) (hK1x : K1 ≠ x) : ∀ (vs : List ℕ) {c : Config},
    IInv W c₀ c → c.nreg K1 = 1 → ztmps → c₀.nreg ALLOC ≤ c.nreg x →
    c.nreg x + vs.length ≤ W →
    IRS P W c₀ ztuao c ztsso (fun c' =>
      (∀ i, i < vs.length → c'.nmem ztrmo = c.nreg (vs.getD i 0)) ∧
      (∀ a, (a < c.nreg x ∨ c.nreg x + vs.length ≤ a) → c'.nmem a = c.nmem a) ∧
      ztivl ∧ c'.nreg x = c.nreg x + vs.length)
  | [], c, hI, _, _, _, _ => IRS.skip hI ⟨fun i hi => absurd hi by_simp, fun _ _ => rfl,
      fun _ _ => rfl, by_simp⟩
  | v :: vs, c, hI, hk1, hvx, hA, hW => by
    have hvx' : v ≠ x := hvx v List.mem_cons_self
    have hvs : ∀ w ∈ vs, w ≠ x := fun w hw => hvx w (List.mem_cons_of_mem _ hw)
    zuiox
    refine IRS.mono (K := 1 + ztpsk) (IRS.seq ztnlr ?_) by_omega
      ztb
    zuer
    refine IRS.seq (K₁ := 1) (K₂ := 2 * vs.length) (IRS.block [.addN x x K1] hI₁
      ⟨⟨hx, by simp only; rw [hk1]; omega⟩, trivial⟩) ?_
    zubib
    have r2x : c₂.nreg x = c.nreg x + 1 := by
      zumyw; zvmzj; rw [hk1]
    have r2o : ∀ r, r ≠ x → c₂.nreg r = c.nreg r := fun r hr => by
      zumyw; zumxi; zunhy
    have m2 : c₂.nmem = upd c.nmem ztmhf ztjsn := by zumyw
    refine (slfStSeq_irs hx hK1x vs hI₂ (by rw [r2o _ hK1x]; exact hk1) hvs
      zteqb zteqb).mono le_rfl ?_
    rintro c' ⟨h1, h2, h3, h4⟩
    refine ⟨fun i hi => ?_, fun a ha => ?_, fun r hr => by rw [h3 r hr, r2o r hr], by
      rw [h4, r2x]; ring⟩
    · zukna
      · rw [h2 _ (Or.inl zteqb), m2]
        simp
      · have := h1 j by_omega
        have hmem : vs.getD j 0 ∈ vs := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem by_omega]
          zulee
        rw [r2x, r2o _ (hvs _ hmem)] at this
        zufax
        rw [show c.nreg x + ztl = c.nreg x + 1 + j by ring, this]
    · rw [h2 _ zteqb, m2, upd_other _ _ _ by_omega]

/-! ## Emitting a raw record -/

/-- The finish registers: the offset bits `slfO … slfO + 7`, the anchor flag, the label count and
labels, the address register. -/
def slfO : ℕ := sw 4054
def slfA : ℕ := sw 4062
def slfN : ℕ := sw 4063
def slfL0 : ℕ := sw 4065
def slfL1 : ℕ := sw 4066
def slfX : ℕ := sw 4100

/-- The address of the next raw record. -/
def slfAddrL : List Instr :=
  [.copyN slfX gRB, .addN slfX slfX gRC, .addN slfX slfX gRC, .addN slfX slfX gRC,
    .addN slfX slfX gRC, .addN slfX slfX gRC, .addN slfX slfX gRC, .addN slfX slfX gRC,
    .addN slfX slfX gRC, .addN slfX slfX gRC, .addN slfX slfX gRC, .addN slfX slfX gRC]

/-- The words of a raw record: position, leaving code, code, auxiliary data. -/
def slfWords (pe ph dc : ℕ) : List ℕ := [pe, ph, dc, oKd, oKk, oB, slfA, slfN, slfL0, slfL1, oPar]

/-- **Emit a raw record** `(pe, ph, dc, …)` at `gRB + 11 gRC` and count it. -/
def slfEmit (pe ph dc : ℕ) : Stmt :=
  .seq (block slfAddrL) (.seq (slfStSeq slfX ztrxc) (block [.addN gRC gRC K1]))
theorem slfAddrL_val (m f : ℕ → ℕ) :
    regB m slfAddrL f slfX = f gRB + 11 * f gRC ∧ ∀ q, q ≠ slfX → regB m slfAddrL f q = f q := by
  zubnq

  refine ⟨?_, fun q hq => regB_other _ _ _ (fun i hi => by
    simp only [slfAddrL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zvmwd <;> exact fun h => hq h.symm)⟩
  simp only [slfAddrL, regB, regI, upd_same, upd_other _ _ _ hC]
  ring
set_option maxHeartbeats 8000000 in
/-- **Emitting a raw record.** -/
theorem slfEmit_irs {pe ph dc : ℕ} (hpe : pe ≠ slfX) (hph : ph ≠ slfX) (hdc : dc ≠ slfX)
    {c : Config} (hI : IInv W c₀ c) (hk1 : c.nreg K1 = 1) (hA : c₀.nreg ALLOC ≤ c.nreg gRB)
    (hW : c.nreg gRB + 11 * zteer ≤ W) :
    IRS P W c₀ ztrxb c (12 + 2 * 11 + 1) (fun c' =>
      (∀ i, i < 11 → c'.nmem ztllo =
        c.nreg ztdkb) ∧
      (∀ a, ztfbg →
        c'.nmem a = c.nmem a) ∧
      c'.nreg gRC = c.nreg gRC + 1 ∧ ztgsr) := by
  have hsX : IScr slfX := iscr_sw' by_norm_num by_norm_num
  have hsC : IScr gRC := iscr_sw' by_norm_num by_norm_num
  zubnq

  have hK1X : K1 ≠ slfX := by unfold K1 slfX sw; omega
  have hK1C : K1 ≠ gRC := by unfold K1 gRC sw; omega
  have hok : okB W c.nmem slfAddrL c.nreg := by
    simp only [slfAddrL, okB, okI, regI, upd_same, upd_other _ _ _ hC]
    refine ⟨hsX, ztklr, ztklr, ztklr, ztklr,
      ⟨hsX, by_omega⟩, ⟨hsX, by_omega⟩, ⟨hsX, by_omega⟩, ⟨hsX, by_omega⟩, ⟨hsX, by_omega⟩,
      ⟨hsX, by_omega⟩, ⟨hsX, by_omega⟩, trivial⟩
  obtain ⟨va, vo⟩ := slfAddrL_val c.nmem c.nreg
  refine IRS.seq (K₁ := 12) (K₂ := 2 * 11 + 1) (IRS.block slfAddrL hI hok) ?_
  zugn
  have a1 : c₁.nreg slfX = c.nreg gRB + 11 * c.nreg gRC := by zvmwl; exact va
  have o1 : ∀ q, q ≠ slfX → c₁.nreg q = c.nreg q := fun q hq => by zvmwl; exact vo q hq
  zufp
  have hws : ∀ v ∈ slfWords pe ph dc, v ≠ slfX := by
    zuml
    simp only [slfWords, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | (zunbv; omega)
  refine IRS.seq (K₁ := 2 * 11) (K₂ := 1) (slfStSeq_irs hsX hK1X ztrxc hI₁
    (by rw [o1 _ hK1X]; exact hk1) hws ztnta
    (by rw [a1]; simp only [slfWords, List.length_cons, List.length_nil]; omega)) ?_
  rintro c₂ hI₂ - - ⟨s1, s2, s3, s4⟩
  have c2C : ztshi := by rw [s3 _ hC, o1 _ hC]
  have c2K : ztgat := by rw [s3 _ hK1X, o1 _ hK1X]; exact hk1
  refine (IRS.block [.addN gRC gRC K1] hI₂ ⟨⟨hsC, by zuooq; omega⟩, trivial⟩).mono
    by_simp ?_
  rintro c₃ hc3
  zucwz
  simp only [slfWords, List.length_cons, List.length_nil] at s1 s2
  refine ⟨fun i hi => ?_, fun a ha => ?_, ?_, fun r hr1 hr2 => ?_⟩
  · rw [m3, ← a1, s1 i hi, o1 _ ?_]
    · rfl
    · have hm : (slfWords pe ph dc).getD i 0 ∈ slfWords pe ph dc := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [slfWords]; omega)]
        zulee
      exact hws _ hm
  · rw [m3, s2 a ztnta, m1]
  · zvnar; zvmzj; zuooq
  · zvnar; zumxi; rw [upd_other _ _ _ hr2, s3 _ hr1, o1 _ hr1]
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
@[expose] public section
def slfCmp (ex hx y o : ℕ) : Stmt := callOff ztjl ex hx y K0 cGW o

/-- The anchor flag. -/
def slfAnc : Stmt :=
  .ifLtN K0 slfO ztouq
    (.ifLtN K0 ztbnn ztouq (.instr (.constN slfA 0)))

/-- **The offsets** of `A₀`, `A₁` against `Lst` and `0`, and the anchor flag. -/
def slfOffs : Stmt :=
  .seq (.seq (slfCmp ztjf ztms cGL slfO) (slfCmp ztjf ztms cGW (slfO + 2)))
    (.seq (.seq (slfCmp ztlq ztoo cGL ztbnn)
      (slfCmp ztlq ztoo cGW (slfO + 4 + 2))) slfAnc)

/-- The offset of a stored position. -/
noncomputable def slfOff (P : Polygon) (J : Merge.Junction) (c : Config) (e h : ℕ) : ℝ :=
  oW J ((c.nreg e : ℝ) + (chainModel J.whole).param zta ztkv)
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}
set_option maxHeartbeats 4000000 in
/-- **One comparison.** -/
theorem slfCmp_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {ex hx y o : ℕ}
    (hr : 240000 ≤ ex ∧ ex < 250000 ∧ 240000 ≤ hx ∧ hx < 250000 ∧ 240000 ≤ y ∧ y < 250000)
    (ho : 240700 ≤ o ∧ o + 1 < 250000)
    (hex : c.nreg ex < (chainModel J.whole).W.n)
    (hpp : ProperPos ztbm zta P.n ztgon)
    (h6 : c.nreg hx = 0 → 6 ≤ c.nreg ex) (hyn : c.nreg y < (chainModel J.whole).W.n)
    (h6y : 6 ≤ c.nreg y) {v : ℝ} (hv : oW J ((c.nreg y : ℝ) + 0) = v)
    (hroom : c.nreg ALLOC + 11008 ≤ W) :
    IRS P W c₀ (slfCmp ex hx y o) c 11008 (fun c' =>
      BitIs c' o (slfOff P J c ex hx < v) ∧ BitIs c' ztbql (v < slfOff P J c ex hx) ∧
      ztdwu ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zuhey
  zugnq
  have hgn : ztboy := by
    zugq
  refine (callOff_irs (P := P) (C := J.whole) hI (E.ctxW' hI)
    ⟨by_decide, by_decide, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2, by_decide, by_decide, by_decide,
      by decide⟩ ho hex hyn by_omega hpp
    (by zvnib; exact ztdxk) h6 (fun _ => h6y) hroom).mono le_rfl ?_
  rintro c' ⟨b1, b2, fr, hA, hm⟩
  rw [hgw, k0] at b1 b2
  have hk : ∀ e h, (chainModel J.whole).key zta ztcq =
      (e : ℝ) + (chainModel J.whole).param zta ztcq := fun _ _ => rfl
  have hy0 : off (chainModel J.whole).W.n (gW J : ℝ)
      ((chainModel J.whole).key zta ⟨c.nreg y, 0⟩) = v := by
    tauto
  rw [hy0] at b1 b2
  exact ⟨b1, b2, fr, hA, hm⟩

/-! ## Frames -/

/-- The frame of a finish step writing the registers `R`. -/
def SlfFr (R : ℕ → Prop) (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ R r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth
theorem SlfFr.trans {R : ℕ → Prop} {c c₁ c₂ : Config} (h₁ : SlfFr R c c₁) (h₂ : SlfFr R c₁ c₂) :
    SlfFr R c c₂ :=
  ⟨fun r a b d => (h₂.1 r a b d).trans ztjyh, h₁.2.1.trans h₂.2.1,
    fun a ha => (h₂.2.2 a (by have := h₁.2.1; omega)).trans ztdux⟩
theorem SlfFr.mono {R R' : ℕ → Prop} {c c' : Config} (h : SlfFr R c c') (hR : ∀ r, R r → R' r) :
    SlfFr R' c c' :=
  ⟨fun r a b d => h.1 r a (fun h' => b zttmq) d, h.2.1, h.2.2⟩

/-- The registers of the offsets step. -/
def slfOffR (r : ℕ) : Prop := sw 4054 ≤ r ∧ r ≤ sw 4062
theorem slfAnc_irs (hI : IInv W c₀ c) (k0 : c.nreg K0 = 0) (hb0 : c.nreg slfO ≤ 1)
    (hb4 : c.nreg ztbnn ≤ 1) (hW : 1 ≤ W) :
    IRS P W c₀ slfAnc c 5 (fun c' => c'.nreg slfA ≤ 1 ∧
      (c'.nreg slfA = 1 ↔ (c.nreg slfO = 1 ∨ c.nreg ztbnn = 1)) ∧
      (∀ q, q ≠ slfA → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  have hr : 240700 ≤ slfA ∧ slfA < 250000 := by_decide
  unfold slfAnc
  by_cases h0 : c.nreg K0 < c.nreg slfO
  · refine (IRS.ifT h0 ztrwu).mono by_norm_num ?_
    grind
  · refine (IRS.ifF h0 ?_).mono le_rfl ztb
    by_cases h4 : c.nreg K0 < c.nreg ztbnn
    · refine (IRS.ifT h4 ztrwu).mono by_norm_num ?_
      grind
    · refine (IRS.ifF h4 (set1_irs hI hr by_omega)).mono by_norm_num ?_
      simp_all

/-- The facts of a position compared in the offsets step. -/
def SlfPos (P : Polygon) (J : Merge.Junction) (c : Config) (e h : ℕ) : Prop :=
  c.nreg e < (chainModel J.whole).W.n ∧
    ProperPos ztbm zta P.n ztkv ∧ (c.nreg h = 0 → 6 ≤ c.nreg e)
variable {e h : ℕ}
theorem SlfPos.congr {c c' : Config} (hp : SlfPos P J c e h) (he : c'.nreg e = c.nreg e)
    (hh : c'.nreg h = c.nreg h) : SlfPos P J c' e h := by
  unfold SlfPos at *; simp_all
theorem slfOff_congr {c c' : Config} (he : c'.nreg e = c.nreg e)
    (hh : c'.nreg h = c.nreg h) : slfOff P J c' e h = slfOff P J c e h := by
  unfold slfOff; simp_all
set_option maxHeartbeats 4000000 in
/-- **Comparing a position with the start and the base.** -/
theorem slfCmp2_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {ex hx o : ℕ}
    (hr : 240000 ≤ ex ∧ ex < 250000 ∧ 240000 ≤ hx ∧ hx < 250000)
    (ho : 240700 ≤ o ∧ o + 3 < 250000) (hoe : ex < o ∨ o + 3 < ex) (hoh : hx < o ∨ o + 3 < hx)
    (hp : SlfPos P J c ex hx) (hroom : c.nreg ALLOC + 2 * 11008 ≤ W) :
    IRS P W c₀ (.seq (slfCmp ex hx cGL o) (slfCmp ex hx cGW ztdvm)) c (2 * 11008) (fun c' =>
      BitIs c' o (slfOff P J c ex hx < Lst J) ∧ BitIs c' (o + 3) (0 < slfOff P J c ex hx) ∧
      SlfFr (fun r => o ≤ r ∧ r ≤ o + 3) c c') := by
  have hgn : ztboy := by
    zugq
  have hLn := Lst_lt_n J
  have hgl := (E.hM.fix hI).gl
  zuhey
  have hcl : 240000 ≤ cGL ∧ cGL < 250000 := by_decide
  have hcw : 240000 ≤ cGW ∧ cGW < 250000 := by_decide
  refine IRS.seq (K₁ := 11008) (K₂ := 11008) (slfCmp_irs E hI ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
    hcl.1, hcl.2⟩ ⟨ho.1, by_omega⟩ hp.1 hp.2.1 hp.2.2 (by zupco; exact Nat.mod_lt _ by_omega)
    (by zupco; exact start_key_ge_six J) (v := (Lst J : ℝ)) (by
      rw [hgl, oW_def]
      have := off_key (t := 0) hgn hLn le_rfl one_pos
      simp_all) by_omega) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨b1, -, fr1, -, hm1⟩
  have k1 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ o → r ≠ o + 1 → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => fr1 r ztyid h3 h4 ztu
  have e1 := k1 ex hr.1 hr.2.1 by_omega by_omega
  have h1 := k1 hx hr.2.2.1 hr.2.2.2 by_omega by_omega
  have hp1 := hp.congr e1 h1
  refine (slfCmp_irs E hI₁ ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, hcw.1, hcw.2⟩ ztgy
    hp1.1 hp1.2.1 hp1.2.2 (by zuotd; omega) (by zuotd; unfold gW; omega)
    (v := 0) (by rw [E.gw' hI₁, add_zero, oW_def]; exact off_self _ _) by_omega).mono le_rfl ?_
  rintro c₂ ⟨-, b2, fr2, hA2, hm2⟩
  rw [slfOff_congr e1 h1] at b2
  refine ⟨b1.of_eq (fr2 o (band_sw_not ztgy) by_omega by_omega
    ztu), b2, ⟨fun r hb hr' ha => ?_, hA₁.trans hA2, fun a ha => ?_⟩⟩
  · simp only [not_and_or, not_le] at hr'
    rw [fr2 r hb by_omega by_omega ha, fr1 r hb by_omega by_omega ha]
  · rw [hm2 a by_omega, hm1 a ha]
set_option maxHeartbeats 8000000 in
/-- **The offsets step.** -/
theorem slfOffs_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hp₀ : SlfPos P J c ztjf ztms) (hp₁ : SlfPos P J c ztlq ztoo)
    (hroom : c.nreg ALLOC + 44037 ≤ W) :
    IRS P W c₀ slfOffs c 44037 (fun c' =>
      BitIs c' slfO ztwvc ∧
      BitIs c' ztfup ztyhd ∧
      BitIs c' ztbnn ztyfr ∧
      BitIs c' zthkl ztyhe ∧
      c'.nreg slfA ≤ 1 ∧ (c'.nreg slfA = 1 ↔ (slfOff P J c ztjf ztms < Lst J ∨
        slfOff P J c ztlq ztoo < Lst J)) ∧ SlfFr slfOffR c c') := by
  have r0 : 240000 ≤ oF0 + 1 ∧ oF0 + 1 < 250000 ∧ 240000 ≤ oF0 + 2 ∧ oF0 + 2 < 250000 := by
    decide
  have r1 : 240000 ≤ a1F + 1 ∧ a1F + 1 < 250000 ∧ 240000 ≤ a1F + 2 ∧ a1F + 2 < 250000 := by
    decide
  have hO : 240700 ≤ slfO ∧ slfO + 3 < 250000 := by_decide
  zuiba
  unfold slfOffs
  refine IRS.seq (K₁ := 2 * 11008) (K₂ := 2 * 11008 + 5) (slfCmp2_irs E hI r0 hO
    by_decide by_decide hp₀ by_omega) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨b0, b3, fr1⟩
  have k1 : ∀ r, 240000 ≤ r → r < 250000 → (r < slfO ∨ slfO + 3 < r) → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => fr1.1 r ztyid by_omega ztu
  have e1 := k1 ztlq r1.1 r1.2.1 by_decide
  have h1 := k1 ztoo r1.2.2.1 r1.2.2.2 by_decide
  refine IRS.seq (K₁ := 2 * 11008) (K₂ := 5) (slfCmp2_irs E hI₁ r1
    (o := slfO + 4) by_decide
    by_decide by_decide (hp₁.congr e1 h1)
    by_omega) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨b4, b7, fr2⟩
  rw [slfOff_congr e1 h1] at b4 b7
  have k2 : ∀ r, 240000 ≤ r → r < 250000 → (r < slfO + 4 ∨ slfO + 4 + 3 < r) →
      c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => fr2.1 r ztyid by_omega ztu
  have b0' := b0.of_eq (k2 slfO by_omega by_omega by_omega)
  have b3' := b3.of_eq (k2 ztfup by_omega by_omega
    by_omega)
  refine (slfAnc_irs hI₂ (E.hK.fix hI₂).1 b0'.1 b4.1 by_omega).mono le_rfl ?_
  rintro c₃ ⟨a1, a2, a3, a4⟩
  have hne : ∀ q, (q < slfA ∨ slfA < q) → c₃.nreg q = c₂.nreg q := fun q hq => a3 q by_omega
  refine ⟨b0'.of_eq ztjxz,
    b3'.of_eq ztjxz,
    b4.of_eq ztjxz,
    b7.of_eq ztjxz, a1, ?_, ?_⟩
  · rw [a2, b0'.2, b4.2]
  · refine (fr1.mono fun r hr => ?_).trans ((fr2.mono fun r hr => ?_).trans
      ⟨fun r _ hr _ => a3 r (fun h => hr ztpb),
        (a3 ALLOC by_decide).ge,
        fun a _ => by rw [a4]⟩)
    · zuiqd
    · zuiqd
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)
@[expose] public section
def slfParS (ps : Stmt) : Stmt :=
  .ifLtN oKd K1 ps (.ifLtN K1 oKd ps (block [.addN oPar oKk K1]))

/-- The parent facts of `AuxOK`. -/
def SlfParOK (P : Polygon) (J : Merge.Junction) (N₂ : NF) (e : Set Point) (par : ℕ) : Prop :=
  par ≤ N₂.nChords ∧
    (∀ c ∈ N₂.F ztj zta, e ⊆ c →
      0 < par ∧ (N₂.chord zthje).toSet ztj zta = c) ∧
    (0 < par → e ⊆ (N₂.chord zthje).toSet ztj zta)
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-- **The parent facts from the parent scan.** -/
theorem slfParOK_scan (hP : J.P.Simple) (hN : IsNF ztj zta N₂)
    {kind k b : ℕ} (hD : OrgD P J N₂ kind k b) (h1 : kind ≠ 1) {p h par : ℕ}
    (hA : Arrival (chainModel J.right).W ztwme ztcrx p
      ztynf)
    (hle : par ≤ N₂.nChords)
    (hpos : 0 < par → (chainModel J.right).key zta (endPos N₂ zthje ztlp) =
      (chainModel J.right).key zta ztnk)
    (hzero : par = 0 → ∀ i, i < N₂.nChords → (chainModel J.right).key zta
      (endPos N₂ i ztlp) ≠ (chainModel J.right).key zta ztnk) :
    SlfParOK P J N₂ ztwja par := by
  have hok := hD.ok
  have hb : b ≤ 1 := hok.2.1
  obtain ⟨-, -, -, haR, -⟩ := stOrig_facts hP hN hok
  have hiff := fun i (hi : i < N₂.nChords) =>
    parent_key_iff hP hN (haR h1) hb hD.free hA hi
  zuezm
  have hsub : 0 < par → Merge.shoot J.whole ztwme ztkz ⊆
      (N₂.chord zthje).toSet ztj zta := fun hp =>
    (hiff zthje by_omega).1 (hpos hp)
  refine ⟨hle, fun cc hcc hec => ?_, hsub⟩
  obtain ⟨i, hi, rfl⟩ := chord_of_mem hcc
  have hp : 0 < par := by
    grind
  refine ztuhs
  have e := stopSet_eq J zta N₂ kind k b
  exact parent_eq hP hN hD (chord_mem by_omega) hcc (e ▸ hsub hp) (e ▸ hec)

/-- **The parent facts of a wall code.** -/
theorem slfParOK_wall (hP : J.P.Simple) (hN : IsNF ztj zta N₂)
    {k b : ℕ} (hD : OrgD P J N₂ 1 k b) :
    SlfParOK P J N₂ (stopSet J zta N₂ 1 k b) zts := by
  have hk : k < N₂.nChords := (hD.ok.2.2.1 rfl).1
  have hw := parent_wall hP hN hD
  unfold SlfParOK
  zudli
  exact ⟨hk, fun cc hcc hec => ⟨Nat.succ_pos _, parent_eq hP hN hD ztvlj hcc hw hec⟩,
    fun _ => hw⟩
set_option maxHeartbeats 4000000 in
/-- **The parent step.** -/
theorem slfPar_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {ps : Stmt}
    {κp : ℕ} (hps : ∀ c, IInv W c₀ c → c.nreg pE2 < (chainModel J.right).W.n →
      ProperPos ztj zta P.n ztbii →
      ztlls → c.nreg oB ≤ 1 →
      c.nreg ALLOC + κp * ztcer ≤ W →
      IRS P W c₀ ps c ztbabd ztjlg)
    (hD : OrgD P J N₂ ztka ztij ztfb)
    (hpre : c.nreg oKd ≠ 1 → c.nreg pE2 < (chainModel J.right).W.n ∧
      ProperPos ztj zta P.n ztbii ∧
      Arrival (chainModel J.right).W ztwmw
        ztxtx ztvju
        ztynb)
    (hroom : c.nreg oKd ≠ 1 → c.nreg ALLOC + κp * ztcer ≤ W) :
    IRS P W c₀ ztwej c (if c.nreg oKd = 1 then 5 else κp * ztcer + 4)
      (fun c' => SlfParOK P J N₂ ztxaj
        ztvgv ∧ SlfFr ParR c c') := by
  zubns
  zueqm
  obtain ⟨k0, k1, -⟩ := E.hK.fix hI
  have hk2 : ztuov := hD.ok.1
  zufui
  -- the scan
  have scan : c.nreg oKd ≠ 1 → IRS P W c₀ ps c ztbabd
      (fun c' => SlfParOK P J N₂ ztxaj
        ztvgv ∧ SlfFr ParR c c') := by
    zudqd
    obtain ⟨he, hpp, hA⟩ := hpre h1
    zudim
    have h6 : c.nreg pH2 = 0 → 6 ≤ c.nreg pE2 := fun h0 =>
      h6_of_abs J.right zta (x := ztbii) (by
        rw [pos_eq_sidePt', hA.2.2.2.1, radius_right]; exact hy) h0
    refine (hps c hI he hpp h6 hb (hroom h1)).mono le_rfl ?_
    rintro c' ⟨hle, hpos, hzero, hm, hA', fr⟩
    exact ⟨slfParOK_scan hP hN hD h1 hA hle hpos hzero, fr, hA', hm⟩
  unfold slfParS
  zuhsj
  · zufuy

    exact (IRS.ifT h0 ztwdf).mono by_omega ztb
  · refine (IRS.ifF (K := if c.nreg oKd = 1 then 3 else κp * ztcer + 2) h0 ?_).mono
      by_grind ztb
    zuhsq
    · zufuy

      exact IRS.ifT h2 ztwdf
    · have hk : ztpmi := by_omega
      rw [ite_eq_left hk]
      have hD1 : OrgD P J N₂ 1 ztij ztfb := hk ▸ hD
      have hkK : ztuow := (hD1.ok.2.2.1 rfl).1
      have hTW := E.hTW
      have hpar : IScr oPar := iscr_sw' by_norm_num by_norm_num
      refine IRS.ifF h2 ((IRS.block [.addN oPar oKk K1] hI
        ⟨⟨hpar, by_omega⟩, trivial⟩).mono by_simp ?_)
      zuu
      have hv : regB c.nmem [.addN oPar oKk K1] c.nreg oPar = c.nreg oKk + 1 := by
        zvmzj; rw [k1]
      refine ⟨by simp only; rw [hv, hk]; exact slfParOK_wall hP hN hD1, fun r _ hr _ => ?_,
        ?_, fun _ _ => rfl⟩
      · zudj
        rw [upd_other _ _ _ ztwnm]
      rfl
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Chain (SideAttach)
@[expose] public section
def slfDc : ℕ := sw 4067

/-- **The emission of the raw records.** -/
def slfEmits : Stmt :=
  .seq (block [.subN slfDc K1 oB])
    (.seq (.ifLtN K0 slfO .skip (slfEmit ztjf ztms oB))
      (.ifLtN K0 ztbnn .skip (slfEmit ztlq ztoo slfDc)))

/-- **The contract of the emission.** -/
def SlfEmitsSpec : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      OrgD P J N₂ ztka ztij ztfb →
      Arrival (chainModel J.whole).W ztwmw
        ztxtx ztyis
        ztbalc →
      PosW P J ztyis (c.nreg ztms) →
      Arrival (chainModel J.whole).W
        (farPt J.whole ztwmw
          ztwow) (dirOf (c.nreg oB)) (c.nreg (a1F + 1))
        ztbano →
      PosW P J ztbagr (c.nreg ztoo) →
      BitIs c slfO ztwvc →
      BitIs c ztbnn ztyfr →
      ((∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W
          ztxaj q s ∧
          (Lst J : ℝ) ≤ oW J ztej) →
        AuxOK P J N₂ ztxaj
          (c.nreg slfA, c.nreg slfN, c.nreg slfL0, c.nreg slfL1, c.nreg oPar)) →
      c₀.nreg ALLOC ≤ c.nreg gRB → c.nreg gRB + 11 * ztees ≤ c.nreg ALLOC →
      c.nreg ALLOC + 100 ≤ W →
      IRS P W c₀ slfEmits c 100 ztwrn
open Chazelle.Chain (sidePt)
variable {P : Polygon} {J : Merge.Junction} {N : NF}

/-- **The raw record of the emitted words.** -/
theorem slfRec_words {m : ℕ → ℕ} {RB j pe ph dc : ℕ} {cc : Config}
    (hw : ∀ i, i < 11 → m ztenv = cc.nreg ztdkb) :
    rawRec m RB j = (cc.nreg pe, cc.nreg ph, cc.nreg oKd, cc.nreg oKk, cc.nreg oB) ∧
      rawDc m RB j = cc.nreg dc ∧
      rawAux m RB j = (cc.nreg slfA, cc.nreg slfN, cc.nreg slfL0, cc.nreg slfL1, cc.nreg oPar) := by
  have w : ∀ i, i < 11 → m ztenv = cc.nreg ztdkb := hw
  have w0 := w 0 by_norm_num
  have w1 := w 1 by_norm_num
  have w2 := w 2 by_norm_num
  have w3 := w 3 by_norm_num
  have w4 := w 4 by_norm_num
  have w5 := w 5 by_norm_num
  have w6 := w 6 by_norm_num
  have w7 := w 7 by_norm_num
  have w8 := w 8 by_norm_num
  have w9 := w 9 by_norm_num
  have w10 := w 10 by_norm_num
  simp only [slfWords, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at w0 w1 w2 w3
  simp only [slfWords, List.getD_cons_zero, List.getD_cons_succ] at w4 w5 w6 w7
  simp only [slfWords, List.getD_cons_zero, List.getD_cons_succ] at w8 w9 w10
  zuluu

/-- **A valid raw record.** -/
theorem slfRawV {kind k b : ℕ} (hD : OrgD P J N kind k b) {d : ℕ} (hd : d ≤ 1) {p h : ℕ}
    (hA : SideAttach (chainModel J.whole).W ztwjv p
      ztynk)
    (hpt : sidePt (chainModel J.whole).W p ztynk =
      (if d = 1 then Merge.lend ztwjv
        else Merge.rend ztwjv))
    (hL : (Lst J : ℝ) ≤ oW J (p + (chainModel J.whole).param zta ztnk))
    (hpw : PosW P J p h) {x : ℕ × ℕ × ℕ × ℕ × ℕ}
    (hax : AuxOK P J N ztwjv x) {m : ℕ → ℕ} {RB j : ℕ}
    (hr : rawRec m RB j = (p, h, kind, k, b)) (hdc : rawDc m RB j = d) (hx : rawAux m RB j = x) :
    RawV P J N m RB j := by
  unfold RawV
  rw [hr, hdc, hx]
  exact ⟨⟨hD.ok, hD.free, hA, hL, hd, hpt⟩, hpw, hax⟩

/-- The raw record only reads its eleven words. -/
theorem slfRec_congr {m m' : ℕ → ℕ} {RB j : ℕ}
    (h : ∀ i, i < 11 → m' ztenv = m ztenv) :
    rawRec m' RB j = rawRec m RB j ∧ rawDc m' RB j = rawDc m RB j ∧
      rawAux m' RB j = rawAux m RB j := by
  zujxz
  rw [Nat.add_zero] at h0
  zuluu
variable {W : ℕ} {c₀ : Config}

/-- **A conditional emission**: skipped when the bit is set. -/
theorem slfMaybe_irs {bitr pe ph dc : ℕ} (hpe : pe ≠ slfX) (hph : ph ≠ slfX) (hdc : dc ≠ slfX)
    {c : Config} (hI : IInv W c₀ c) (hk0 : c.nreg K0 = 0) (hk1 : c.nreg K1 = 1)
    (hA : c₀.nreg ALLOC ≤ c.nreg gRB) (hW : c.nreg gRB + 11 * zteer ≤ W)
    (hb : c.nreg bitr ≤ 1) :
    IRS P W c₀ (.ifLtN K0 bitr .skip ztrxb) c 37 (fun c' =>
      c'.nreg gRC = c.nreg gRC + (if c.nreg bitr = 1 then 0 else 1) ∧
      (c.nreg bitr ≠ 1 → ∀ i, i < 11 → c'.nmem ztllo =
        c.nreg ztdkb) ∧
      (∀ a, ztfbg →
        c'.nmem a = c.nmem a) ∧
      ztgsr) := by
  zura
  · have h1 : c.nreg bitr = 1 := by_omega
    refine IRS.skip hI ⟨by_simp_all, fun h' => absurd h1 h', fun _ _ => rfl,
      fun _ _ _ => rfl⟩
  · have h1 : c.nreg bitr ≠ 1 := by_omega
    refine (slfEmit_irs hpe hph hdc hI hk1 hA hW).mono by_norm_num ?_
    simp_all
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Chain (SideAttach sidePt)
@[expose] public section
set_option maxHeartbeats 4000000 in
theorem slfEmits_spec : SlfEmitsSpec := by
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hD arr0 pw0 arr1 pw1 bit0 bit1 hax hR0 hR1 hroom
  zucqn

  set e := stopSet J zta N₂ kind k b with he
  have hb : b ≤ 1 := hD.ok.2.1
  obtain ⟨i1, i2, -⟩ := orig_attach E.hP E.hNF₂ hD
  obtain ⟨A0, pt0⟩ := i1 _ _ arr0
  obtain ⟨A1, pt1⟩ := i2 _ _ arr1
  zuiw
  have hX : ∀ r, r = oF0 + 1 ∨ r = oF0 + 2 ∨ r = oB ∨ r = a1F + 1 ∨ r = a1F + 2 ∨ r = slfDc →
      r ≠ slfX := by
    intro r hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [oF0, oB, a1F, slfDc, slfX, sw] <;> omega
  -- 1. the reversed code
  refine (IRS.seq (K₁ := 1) (K₂ := 37 + 37) (IRS.block [.subN slfDc K1 oB] hI
    ⟨iscr_sw by_decide by_decide, trivial⟩) ?_).mono
    by_norm_num ztb
  zuer
  set c₁ : Config := { c with nreg := regB c.nmem [.subN slfDc K1 oB] c.nreg } with hc₁
  have v1 : c₁.nreg slfDc = 1 - b := by simp [hc₁, regB, regI, upd, hK.2.1, hbb]
  have k1 : ∀ q, q ≠ slfDc → c₁.nreg q = c.nreg q := fun q hq => by
    simp [hc₁, regB, regI, upd, hq]
  have rr1 : ∀ q, (sw 4000 ≤ q ∧ q ≤ sw 4066) ∨ q = K0 ∨ q = K1 ∨ q = ALLOC →
      c₁.nreg q = c.nreg q := fun q hq => k1 q (by
        rcases hq with h | rfl | rfl | rfl <;> simp only [slfDc, K0, K1, ALLOC, sw] at * <;> omega)
  have c1RB : ztsgm := rr1 _ ztihm
  have c1RC : ztsgn := rr1 _ ztwos
  have c1O : ztsgr := rr1 _ ztwos
  -- 2. the record of `A₀`
  refine IRS.seq (K₁ := 37) (K₂ := 37) (slfMaybe_irs (bitr := slfO) (hX _ ztp)
    (hX _ ztwiz) (hX _ ztbajm) hI₁
    (by rw [rr1 _ ztwiz]; exact hK.1) (by rw [rr1 _ ztbajm]; exact hK.2.1)
    by_omega by_omega
    (by rw [c1O]; exact bit0.1)) ?_
  rintro c₂ hI₂ - - ⟨g2, w2, m2, r2⟩
  simp only [c1O, c1RC, c1RB] at g2 w2 m2
  have c2r : ∀ q, q ≠ slfX → q ≠ gRC → q ≠ slfDc → c₂.nreg q = c.nreg q :=
    fun q h1 h2 h3 => (r2 q h1 h2).trans (k1 q h3)
  have c2RB : ztshh :=
    c2r _ by_decide by_decide by_decide
  have c2O4 : c₂.nreg ztbnn = c.nreg ztbnn :=
    c2r _ by_decide by_decide by_decide
  have c2Dc : c₂.nreg slfDc = 1 - b := by
    rw [r2 _ by_decide by_decide, v1]
  have hgrc2 : c₂.nreg gRC ≤ c.nreg gRC + 1 := by rw [g2]; split_ifs <;> omega
  -- 3. the record of `A₁`
  refine (slfMaybe_irs (bitr := slfO + 4) (hX _ ztbaje)
    (hX _ (Or.inr ztbaje)) (hX _ (Or.inr (Or.inr (Or.inr (Or.inr
      ztbt))))) hI₂
    (by rw [c2r _ by_decide by_decide
      by_decide]; exact hK.1)
    (by rw [c2r _ by_decide by_decide
      by_decide]; exact hK.2.1)
    by_omega by_omega
    (by rw [c2O4]; exact bit1.1)).mono by_norm_num ?_
  rintro c' ⟨g3, w3, m3, r3⟩
  simp only [c2O4, c2RB] at g3 w3 m3
  -- the facts
  set t₀ := (chainModel J.whole).param zta ztwvh with ht₀
  set t₁ := (chainModel J.whole).param zta ztxhw with ht₁
  have hE0 : c.nreg slfO ≠ 1 → (Lst J : ℝ) ≤ oW J ztzkx := fun h => by
    have := bit0.2; unfold slfOff at this; grind
  have hE1 : c.nreg ztbnn ≠ 1 → (Lst J : ℝ) ≤ oW J ztzkz := fun h => by
    have := bit1.2; unfold slfOff at this; grind
  have hN0 : c.nreg slfO = 1 → oW J ztzkx < Lst J := fun h => by
    have := bit0.2; unfold slfOff at this; grind
  have hN1 : c.nreg ztbnn = 1 → oW J ztzkz < Lst J := fun h => by
    have := bit1.2; unfold slfOff at this; grind
  -- the record of `A₀` in `c'`
  have rec0 : c.nreg slfO ≠ 1 → RawV P J N₂ c'.nmem ztbsp ztvjn ∧
      rawRec c'.nmem ztbsp ztvjn =
        (c.nreg ztjf, c.nreg ztms, kind, k, b) := by
    zuq
    obtain ⟨q1, q2, q3⟩ := slfRec_words (cc := c₁) (w2 h)
    have hc' := slfRec_congr (m := c₂.nmem) (m' := c'.nmem) (RB := c.nreg gRB) (j := c.nreg gRC)
      (fun i hi => m3 _ ztzz)
    rw [← hc'.1] at q1
    rw [← hc'.2.1] at q2
    rw [← hc'.2.2] at q3
    have g : ∀ q, (q = oF0 + 1 ∨ q = oF0 + 2 ∨ q = oKd ∨ q = oKk ∨ q = oB ∨ q = slfA ∨ q = slfN ∨
        q = slfL0 ∨ q = slfL1 ∨ q = oPar) → c₁.nreg q = c.nreg q := by
      zuco
      exact k1 q (by rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [oF0, oKd, oKk, oB, slfA, slfN, slfL0, slfL1, oPar, slfDc, sw] <;> omega)
    rw [g ztjf by_simp, g ztms by_simp, g oKd by_simp, g oKk by_simp,
      g oB by_simp] at q1
    rw [g oB by_simp] at q2
    rw [g slfA by_simp, g slfN by_simp, g slfL0 by_simp, g slfL1 by_simp,
      g oPar by_simp] at q3
    refine ⟨slfRawV hD hb A0 pt0 (hE0 h) pw0 (hax ⟨_, _, A0, hE0 h⟩) q1 q2 q3, q1⟩
  -- the record of `A₁` in `c'`
  have rec1 : c.nreg ztbnn ≠ 1 → RawV P J N₂ c'.nmem ztbsp ztvna ∧
      rawRec c'.nmem ztbsp ztvna =
        (c.nreg ztlq, c.nreg ztoo, kind, k, b) := by
    zuq
    obtain ⟨q1, q2, q3⟩ := slfRec_words (cc := c₂) (w3 h)
    have e1 : c₂.nreg ztlq = c.nreg ztlq :=
      c2r _ by_decide by_decide by_decide
    have e2 : c₂.nreg ztoo = c.nreg ztoo :=
      c2r _ by_decide by_decide by_decide
    have g : ∀ q, (q = oKd ∨ q = oKk ∨ q = oB ∨ q = slfA ∨ q = slfN ∨ q = slfL0 ∨ q = slfL1 ∨
        q = oPar) → c₂.nreg q = c.nreg q := by
      zuco
      exact c2r q (by rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          zunbv <;> omega)
        (by rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [oKd, oKk, oB, slfA, slfN, slfL0, slfL1, oPar, gRC, sw] <;> omega)
        (by rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [oKd, oKk, oB, slfA, slfN, slfL0, slfL1, oPar, slfDc, sw] <;> omega)
    rw [e1, e2, g oKd by_simp, g oKk by_simp, g oB by_simp] at q1
    rw [c2Dc] at q2
    rw [g slfA by_simp, g slfN by_simp, g slfL0 by_simp, g slfL1 by_simp,
      g oPar by_simp] at q3
    refine ⟨slfRawV hD (d := 1 - b) by_omega A1 pt1 (hE1 h) pw1 (hax ⟨_, _, A1, hE1 h⟩) q1 q2 q3,
      q1⟩
  -- the post
  have hO0 : c.nreg slfO ≤ 1 := bit0.1
  have hO4 : c.nreg ztbnn ≤ 1 := bit1.1
  refine ⟨by_omega, by rw [g3, g2]; split_ifs <;> omega, fun i hi1 hi2 => ?_,
    fun _ p t hA hL => ?_, fun a ha hs => ?_, ?_, fun r hr hS hrA => ?_⟩
  · -- validity
    by_cases hlt : i < c₂.nreg gRC
    · grind
    · have hE : ztbacl := by_grind
      have hi : i = c₂.nreg gRC := by_grind
      grind
  · -- completeness
    rcases attach_two E.hP E.hNF₂ hD arr0 arr1 hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hE : c.nreg slfO ≠ 1 := fun h => absurd (hN0 h) ztwam
      obtain ⟨-, hr⟩ := rec0 hE
      refine ⟨c.nreg gRC, le_rfl, by_grind, ?_, ?_, ?_⟩
      · zubim
      · zubim
      grind
    · have hE : ztbacl := fun h => absurd (hN1 h) ztwam
      obtain ⟨-, hr⟩ := rec1 hE
      refine ⟨c₂.nreg gRC, by_omega, by_grind, ?_, ?_, ?_⟩
      · zubim
      · zubim
      grind
  · -- memory
    rw [m3 a by_omega,
      m2 a by_omega]
  · -- the allocator
    rw [r3 _ by_decide by_decide,
      c2r _ by_decide by_decide
        by_decide]
  · -- the registers
    have hS' : ¬ (ztgz ∨ r = gRC ∨ ztph ∨
      ztfuu ∨ ztbgd) := hS
    have a1 : r ≠ slfX := by intro h; apply hS'; subst h; decide
    have a2 : r ≠ gRC := fun h => hS' ztwkb
    have a3 : r ≠ slfDc := by intro h; apply hS'; subst h; decide
    rw [r3 r a1 a2, c2r r a1 a2 a3]
def slfSE : ℕ := sw 4116
def slfSH : ℕ := sw 4117

/-- The registers the stretch labels may write. -/
def StrR (r : ℕ) : Prop :=
  FRR r ∨ ztltx ∨ ztlub

/-- **Task SL: the stretch labels.** -/
def StrLabTask : Prop :=
  ∃ (sl : Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      c.nreg slfSE < (chainModel J.whole).W.n →
      ProperPos ztbm zta P.n ztst →
      |((chainModel J.whole).pos (Qof P) ⟨c.nreg slfSE, c.nreg slfSH⟩).2| < J.whole.radius →
      (∃ e, e ∈ F₂plus J ztwis ∧
        ztxzf ∧
        SideAttach (chainModel J.whole).W e ztere
          ztwqd) →
      0 < oW J ztwsw →
      oW J ztwsw < Lst J →
      c.nreg ALLOC + κ zto * ztgf ≤ W →
      IRS P W c₀ sl c ztxen (fun c' =>
        c'.nreg frA < N₂.nRegions ∧ c'.nreg frB < N₂.nRegions ∧
        (∃ d, d < Lst J ∧
          ztxqf ∧
          c.nreg slfSE = ztefg % (chainModel J.whole).W.n ∧
          AfterFaces ztj ztbcq
            ztwqd
            ztxhh ∧
          (0 < (chainModel J.whole).param zta ztst →
            BeforeFaces ztj ztbcq
              ztwqd
              ztwva) ∧
          ((chainModel J.whole).param zta ztst = 0 →
            BeforeFaces ztj zterj 0
              ztwva)) ∧
        zth ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
        ztfcw)
open Chazelle.Merge (FreeAt)
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}
theorem slf_labSet2 (J : Merge.Junction) (Q : Polygon) (N : NF) (l₀ l₁ l₂ l₃ : ℕ) :
    labSet J Q N 2 l₀ l₁ l₂ l₃ =
      {regOf ztj Q N l₀, regOf ztj Q N l₁} := by
  ext V
  simp only [labSet, Set.mem_image, mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  grind

/-- A stretch attachment: its offset `d`. -/
theorem slf_stretch (hP : J.P.Simple) (hN : IsNF ztj zta N₂) {p : ℕ} {t : ℝ}
    (hp : p < (chainModel J.whole).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) (h0 : 0 < oW J ztk)
    (hL : oW J ztk < Lst J) :
    ∃ d, d < Lst J ∧ ztevv ∧ p = ztefg % (chainModel J.whole).W.n :=
  stretch_decomp J hP hN.1.2.1 hN.1.1 hp ht0 ht1 h0 by_tauto

/-- **The side labels below and above the parent.** -/
theorem slf_lab_par (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {kind k b : ℕ}
    (hD : OrgD P J N₂ kind k b) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W ztwja p t)
    (h0 : 0 < oW J ztk) (hL : oW J ztk < Lst J)
    (hnp : ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W ztwja
      q s → oW J ztej ≠ 0)
    (hC1 : ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W ztwja
      q s ∧ (Lst J : ℝ) ≤ oW J ztej)
    {i : ℕ} (hi : i < N₂.nChords)
    (hsub : stopSet J zta N₂ kind k b ⊆ (N₂.chord i).toSet ztj zta) :
    EvSideLab J ztwis
      (labSet J zta N₂ 2 (N₂.chord i).up (N₂.chord i).dn 0 0)
      ztwja := by
  zubns
  zueqm
  obtain ⟨d, hd, htd, hpd⟩ := slf_stretch hP hN hA.1 hA.2.1 hA.2.2.1 h0 hL
  zufjv
  have hL1 := (labTask J zta _ _ hP hN.1 ztpza hm hst hnp hC1 d t hd
    hA.2.1 hA.2.2.1 htd by_simp_all).1
  zudiv
  obtain ⟨hu, hdn, -⟩ := (regOf_spec hN).2.1 i hi
  obtain ⟨s1, s2⟩ := sideOf_rec hN hi
  zumow
  exact hL1 _ (chord_mem hi) hsub _ (hreg.1 _ hu) _ (hreg.1 _ hdn) s1 s2

/-- **The side labels faced at the counterpart of the stretch attachment.** -/
theorem slf_lab_str (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {kind k b : ℕ}
    (hD : OrgD P J N₂ kind k b) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W ztwja p t)
    (hnp : ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W ztwja
      q s → oW J ztej ≠ 0)
    (hC1 : ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W ztwja
      q s ∧ (Lst J : ℝ) ≤ oW J ztej)
    (hnopar : ∀ cc ∈ N₂.F ztj zta, ¬ stopSet J zta N₂ kind k b ⊆ cc)
    {d : ℕ} (hd : d < Lst J) (htd : t = 0 → d ≠ 0) (hpd : p = ztefg % (chainModel J.whole).W.n)
    {la lb : ℕ} (hla : la < N₂.nRegions) (hlb : lb < N₂.nRegions)
    (hAf : AfterFaces ztj ztbcq t (regOf ztj zta N₂ la))
    (hB1 : 0 < t → BeforeFaces ztj ztbcq t
      ztzgu)
    (hB0 : t = 0 → BeforeFaces ztj zterj 0
      ztzgu) :
    EvSideLab J ztwis (labSet J zta N₂ 2 la lb 0 0)
      ztwja := by
  zubns
  zueqm
  zufjv
  have hL2 := (labTask J zta _ _ hP hN.1 ztpza hm hst hnp hC1 d t hd
    hA.2.1 hA.2.2.1 htd by_simp_all).2
  zudiv
  zumow
  exact hL2 hnopar _ (hreg.1 _ hla) _ (hreg.1 _ hlb) hAf hB1 hB0
