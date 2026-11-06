module

public import Chazelle.Core.DownPhaseDrvPGTop
public import Chazelle.Core.SweepPrimKer

/-!
# Down-phase pieces (D4), part 3: the host count and the top of a short piece by a scan

* `cntS`: the host handle (`218000`) into `NFLoc`'s register `50060`, the number `N` of host
  points into `218012` (`NFLoc.cntStmt`), constants `218020 = 0`, `218021 = 1`,
  `218022 = 65` (`cntS_exec`; it leaves `NFLoc.HostEnv` for the lookups).
* `scanS`: for a piece of `m ≤ 64` edges from the host point `s` (`218001`), a left-to-right
  scan of the host points `s, …, s + m` (one lookup and one height test each) keeping the first
  highest one: `218013 := T`, the least offset of a highest point (`scanS_exec`).

Registers: `218012 … 218046` of band `21`, `NFLoc`'s `50046 … 50076` (band `5`), the sign
kernel (band `1`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace DrvP

open Machine Machine.Stmt Programs SignK WalkKey NFLoc

@[expose] public section

/-! ## Host points -/

/-- The symbolic point of index `i` of the host. -/
def pt (H : Host) (n i : ℕ) : SymPt := (H.pts n).getD i (.vtx 0)

/-- The height of the host point `i`. -/
noncomputable def Yh (P : Polygon) (H : Host) (i : ℕ) : ℝ := ((pt H P.n i).eval (Qof P)).2

theorem pt_of_some {H : Host} {n i : ℕ} {sp : SymPt} (h : (H.pts n)[i]? = some sp) :
    pt H n i = sp := by
  unfold pt; rw [List.getD_eq_getElem?_getD, h]; rfl

theorem pt_lt {H : Host} {n i : ℕ} (hwf : HostWF n H) (hn : 0 < n) (hi : i < (H.pts n).length) :
    (pt H n i).Lt n := by
  unfold pt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact hostWF_pts hwf hn _ (List.getElem_mem hi)

/-! ## The programs -/

/-- **The host count** and the constants. -/
def cntS : Stmt := .seq (block [.copyN 50060 218000]) (.seq cntStmt
  (block [.copyN 218012 50063, .constN 218020 0, .constN 218021 1, .constN 218022 65]))

/-- The first point of the piece into the best slot `218040`. -/
def scInit : Stmt := .seq (block [.copyN 50071 218001]) (.seq lookStmt
  (block [.copyN 218040 50046, .copyN 218041 50047, .copyN 218042 50048, .constN 218030 0,
    .constN 218031 1, .addN 218032 218002 218021]))

/-- The best slot takes the current point. -/
def scTake : Stmt := block [.copyN 218030 218031, .copyN 218040 218043, .copyN 218041 218044,
  .copyN 218042 218045]

/-- One point of the scan. -/
def scBody : Stmt := .seq (block [.addN 50071 218001 218031]) (.seq lookStmt
  (.seq (block [.copyN 218043 50046, .copyN 218044 50047, .copyN 218045 50048])
  (.seq (SweepPrim.kbit 218040 218043 218040 1 218046)
  (.seq (.ifLtN 218020 218046 scTake .skip) (block [.addN 218031 218031 218021])))))

/-- **The scan.** -/
def scanS : Stmt :=
  .seq scInit (.seq (.whileLtN 218031 218032 scBody) (block [.copyN 218013 218030]))

/-- The registers written by the count and the scan. -/
def Bsc (r : ℕ) : Bool := decide (50046 ≤ r ∧ r < 50080) || Bk r || decide (218012 ≤ r ∧ r < 218100)

/-- The registers written by the scan (finer than `Bsc`). -/
def Bscan (r : ℕ) : Bool :=
  Bhost r || Bk r || decide (r = 218013) || decide (218030 ≤ r ∧ r < 218047)

theorem wr_cntS : wr Bsc cntS = true := by
  have h : wr Bsc cntStmt = true := SweepPrim.wr_mono wr_cntStmt (fun r hr => by
    simp only [Bhost, Bool.or_eq_true, decide_eq_true_eq] at hr
    simp only [Bsc, Bool.or_eq_true, decide_eq_true_eq]; omega)
  simp only [cntS, wr, block, wrOK, h, Bool.and_true, Bool.true_and]
  decide

theorem wr_scanS' : wr Bscan scanS = true := by
  have hk : wr Bscan (SweepPrim.kbit 218040 218043 218040 1 218046) = true :=
    SweepPrim.wr_mono (SweepPrim.wr_kbit _ _ _ _ _) (fun r hr => by
      simp only [SweepPrim.Bkb, Bool.or_eq_true, beq_iff_eq] at hr
      simp only [Bscan, Bool.or_eq_true, decide_eq_true_eq]
      rcases hr with hr | hr
      · exact Or.inl (Or.inl (Or.inr hr))
      · subst hr; right; omega)
  have h : wr Bscan lookStmt = true := SweepPrim.wr_mono wr_lookStmt (fun r hr => by
    simp only [Bscan, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inl (Or.inl (Or.inl hr)))
  simp only [scanS, scInit, scBody, scTake, wr, block, wrOK, h, hk, Bool.and_true,
    Bool.true_and]
  decide

/-! ## The count -/

section exec

variable {P : Polygon} {W : ℕ}

/-- **The host count.** -/
theorem cntS_exec (c : Config) (hw : WordsBounded W c) {H : Host}
    (hH : HostAt c.nmem (c.nreg 218000) H) (haW : c.nreg 218000 + 3 * H.length + 4 ≤ W)
    (hN : (H.pts P.n).length ≤ W) (hW : 65 ≤ W) :
    ∃ c' k, Exec P W cntS c c' k ∧ k ≤ 12 * H.length + 17 ∧ FrameB Bsc c c' ∧
      c'.nreg 218012 = (H.pts P.n).length ∧ c'.nreg 218020 = 0 ∧ c'.nreg 218021 = 1 ∧
      c'.nreg 218022 = 65 ∧ HostEnv W (c.nreg 218000) H.length c.nmem c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, h60, m₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50060 218000]) c c₁ k₁ ∧
      k₁ = 1 ∧ c₁.nreg 50060 = c.nreg 218000 ∧ c₁.nmem = c.nmem := by
    exec_block
    exact ⟨rfl, by config_simp, rfl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, n₂, E₂⟩ := cnt_exec (P := P) (n := P.n) c₁ e₁.wb_right
    (by rwa [m₁]) h60 haW hN
  have w₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, v12, v20, v21, v22, E₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN 218012 50063, .constN 218020 0, .constN 218021 1, .constN 218022 65])
      c₂ c₃ k₃ ∧ k₃ = 4 ∧ c₃.nreg 218012 = (H.pts P.n).length ∧ c₃.nreg 218020 = 0 ∧
      c₃.nreg 218021 = 1 ∧ c₃.nreg 218022 = 65 ∧
      HostEnv W (c.nreg 218000) H.length c.nmem c₃ := by
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, by config_simp; exact n₂, by config_simp, by config_simp, by config_simp,
      ⟨‹_›, by config_simp; exact E₂.h60, by config_simp; exact E₂.h61, by config_simp; exact E₂.h67,
        by config_simp; exact E₂.h68, by config_simp; exact E₂.h69, ?_⟩⟩
    config_simp; rw [E₂.mem, m₁]
  have ex : Exec P W cntS c c₃ (k₁ + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  exact ⟨c₃, _, ex, by omega, exec_frameB ex wr_cntS, v12, v20, v21, v22, E₃⟩

/-! ## The scan -/

/-- **The invariant of the scan** after the points `s, …, s + k - 1` (`k` in `218031`): the
best offset `218030 < k`, its point in the slot `218040`, at least as high as the points seen
and strictly higher than those before it. -/
structure ScI (P : Polygon) (W : ℕ) (H : Host) (m₀ : ℕ → ℕ) (HB s m : ℕ) (c : Config) : Prop where
  env : HostEnv W HB H.length m₀ c
  r01 : c.nreg 218001 = s
  r20 : c.nreg 218020 = 0
  r21 : c.nreg 218021 = 1
  r32 : c.nreg 218032 = m + 1
  k1 : 1 ≤ c.nreg 218031
  km : c.nreg 218031 ≤ m + 1
  bk : c.nreg 218030 < c.nreg 218031
  slot : SymPtIn c 218040 (pt H P.n (s + c.nreg 218030))
  le : ∀ j, j < c.nreg 218031 → Yh P H (s + j) ≤ Yh P H (s + c.nreg 218030)
  lt : ∀ j, j < c.nreg 218030 → Yh P H (s + j) < Yh P H (s + c.nreg 218030)

/-- The facts of the scan's environment. -/
structure ScE (P : Polygon) (W : ℕ) (H : Host) (m₀ : ℕ → ℕ) (HB : ℕ) : Prop where
  good : GoodEnv P
  hW : hostWords P.n ≤ W
  hH : HostAt m₀ HB H
  hwf : HostWF P.n H
  hl : H.length ≤ 64
  haW : HB + 3 * H.length + 4 ≤ W

theorem ScE.nW {H : Host} {m₀ : ℕ → ℕ} {HB : ℕ} (h : ScE P W H m₀ HB) : P.n + 3 ≤ W := by
  have := h.hW; unfold hostWords at this; omega

theorem ScE.npos {H : Host} {m₀ : ℕ → ℕ} {HB : ℕ} (h : ScE P W H m₀ HB) : 0 < P.n := by
  have := Chazelle.Jordan.simple_three_le h.good.1; omega

theorem ScE.hN {H : Host} {m₀ : ℕ → ℕ} {HB : ℕ} (h : ScE P W H m₀ HB) :
    (H.pts P.n).length ≤ W := by
  have h1 := Host.pts_length_le h.hwf
  have := h.hW; unfold hostWords at this
  have : H.length * P.n ≤ 64 * P.n := Nat.mul_le_mul_right _ h.hl
  omega

/-- **One lookup** of the host point `p` into the slot `50046`. -/
theorem look_pt {H : Host} {m₀ : ℕ → ℕ} {HB p : ℕ} (E : ScE P W H m₀ HB) (c : Config)
    (hE : HostEnv W HB H.length m₀ c) (h71 : c.nreg 50071 = p) (hp : p < (H.pts P.n).length) :
    ∃ c' k, Exec P W lookStmt c c' k ∧ k ≤ 1733 ∧ FrameB Bhost c c' ∧
      HostEnv W HB H.length m₀ c' ∧ SymPtIn c' 50046 (pt H P.n p) := by
  obtain ⟨c', k, e, hk, F, E', -, sp, hsp, hin⟩ := look_exec (P := P) c hE h71 E.hH E.hwf
    (by have := E.nW; omega) E.haW E.hN hp
  rw [← pt_of_some hsp] at hin
  exact ⟨c', k, e, by have := E.hl; omega, F, E', hin⟩

theorem bhost_218 {r : ℕ} (h : 218000 ≤ r) : Bhost r = false := by
  simp only [Bhost, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

theorem bkb_218 {r d : ℕ} (h : 218000 ≤ r) (hd : r ≠ d) : SweepPrim.Bkb d r = false := by
  simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne]; exact ⟨by omega, hd⟩

set_option maxHeartbeats 2000000 in
/-- **One point of the scan.** -/
theorem scBody_exec {H : Host} {m₀ : ℕ → ℕ} {HB s m : ℕ} (E : ScE P W H m₀ HB)
    (hsm : s + m + 1 ≤ (H.pts P.n).length) (c : Config) (hI : ScI P W H m₀ HB s m c)
    (hlt : c.nreg 218031 < c.nreg 218032) :
    ∃ c' k, Exec P W scBody c c' k ∧ ScI P W H m₀ HB s m c' ∧ k ≤ 1990 ∧
      m + 1 - c'.nreg 218031 < m + 1 - c.nreg 218031 := by
  have hw := hI.env.wb
  have hk := hI.km
  rw [hI.r32] at hlt
  obtain ⟨k, hkdef⟩ : ∃ k, c.nreg 218031 = k := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b, c.nreg 218030 = b := ⟨_, rfl⟩
  rw [hkdef] at hk hlt
  -- the address
  obtain ⟨c₁, k₁, e₁, hk₁, v71, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 50071 218001 218031])
      c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 50071 = s + k ∧ (∀ r, r ≠ 50071 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    · config_simp; rw [hI.r01, hkdef]; have := E.hN; omega
    refine ⟨rfl, by config_simp; rw [hI.r01, hkdef], fun r hr => ?_, rfl⟩
    simp only [Config.nreg_mk, upd, ite_eq_right hr]
  have E₁ : HostEnv W HB H.length m₀ c₁ := ⟨e₁.wb_right, by rw [r₁ _ (by decide)]; exact hI.env.h60,
    by rw [r₁ _ (by decide)]; exact hI.env.h61, by rw [r₁ _ (by decide)]; exact hI.env.h67,
    by rw [r₁ _ (by decide)]; exact hI.env.h68, by rw [r₁ _ (by decide)]; exact hI.env.h69,
    by rw [m₁]; exact hI.env.mem⟩
  -- the lookup
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, E₂, s₂⟩ := look_pt E c₁ E₁ v71 (by omega)
  have w₂ := e₂.wb_right
  have k₂' : ∀ r, 218000 ≤ r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [F₂.1 r (bhost_218 hr), r₁ r (by omega)]
  -- the copy into the current slot
  obtain ⟨c₃, k₃, e₃, hk₃, s₃, r₃, m₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN 218043 50046, .copyN 218044 50047, .copyN 218045 50048]) c₂ c₃ k₃ ∧ k₃ = 3 ∧
      SymPtIn c₃ 218043 (pt H P.n (s + k)) ∧
      (∀ r, r ≠ 218043 → r ≠ 218044 → r ≠ 218045 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem := by
    exec_block
    refine ⟨rfl, symPtIn_copy s₂ (by config_simp) (by config_simp) (by config_simp),
      fun r h1 h2 h3 => ?_, rfl⟩
    simp only [Config.nreg_mk, upd, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
  have w₃ := e₃.wb_right
  have k₃' : ∀ r, 218000 ≤ r → r ≠ 218043 → r ≠ 218044 → r ≠ 218045 → c₃.nreg r = c.nreg r :=
    fun r h0 h1 h2 h3 => by rw [r₃ r h1 h2 h3, k₂' r h0]
  have sl := hI.slot
  rw [hbdef] at sl
  have sb₃ : SymPtIn c₃ 218040 (pt H P.n (s + b)) := symPtIn_copy sl
    (k₃' _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (k₃' _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (k₃' _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  -- the height test
  have hlb : (pt H P.n (s + b)).Lt P.n := pt_lt E.hwf E.npos (by have := hI.bk; omega)
  have hlk : (pt H P.n (s + k)).Lt P.n := pt_lt E.hwf E.npos (by omega)
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, b₄, t₄⟩ := SweepPrim.kbit_exec (P := P) E.good E.nW c₃ w₃
    (a := 218040) (b := 218043) (d := 218040) (op := 1) (dst := 218046) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlb hlk hlb sb₃ s₃ sb₃
  simp only [SignTest] at t₄
  have w₄ := e₄.wb_right
  have k₄' : ∀ r, 218000 ≤ r → r ≠ 218046 → c₄.nreg r = c₃.nreg r := fun r h0 h1 =>
    F₄.1 r (bkb_218 h0 h1)
  have m₄ : c₄.nmem = m₀ := by rw [F₄.2.2.1, m₃]; exact E₂.mem
  have E₄ : HostEnv W HB H.length m₀ c₄ := by
    have g : ∀ r, 50060 ≤ r → r < 50070 → c₄.nreg r = c₂.nreg r := fun r h1 h2 => by
      rw [F₄.1 r (by simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        beq_eq_false_iff_ne]; omega), r₃ r (by omega) (by omega) (by omega)]
    exact ⟨w₄, by rw [g _ (by norm_num) (by norm_num)]; exact E₂.h60,
      by rw [g _ (by norm_num) (by norm_num)]; exact E₂.h61,
      by rw [g _ (by norm_num) (by norm_num)]; exact E₂.h67,
      by rw [g _ (by norm_num) (by norm_num)]; exact E₂.h68,
      by rw [g _ (by norm_num) (by norm_num)]; exact E₂.h69, m₄⟩
  have c420 : c₄.nreg 218020 = 0 := by
    rw [k₄' _ (by norm_num) (by norm_num), k₃' _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]; exact hI.r20
  have c421 : c₄.nreg 218021 = 1 := by
    rw [k₄' _ (by norm_num) (by norm_num), k₃' _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]; exact hI.r21
  have c431 : c₄.nreg 218031 = k := by
    rwa [k₄' _ (by norm_num) (by norm_num), k₃' _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
  have c430 : c₄.nreg 218030 = b := by
    rwa [k₄' _ (by norm_num) (by norm_num), k₃' _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
  have sk₄ : SymPtIn c₄ 218043 (pt H P.n (s + k)) := symPtIn_copy s₃
    (k₄' _ (by norm_num) (by norm_num)) (k₄' _ (by norm_num) (by norm_num))
    (k₄' _ (by norm_num) (by norm_num))
  have sb₄ : SymPtIn c₄ 218040 (pt H P.n (s + b)) := symPtIn_copy sb₃
    (k₄' _ (by norm_num) (by norm_num)) (k₄' _ (by norm_num) (by norm_num))
    (k₄' _ (by norm_num) (by norm_num))
  -- the decision
  obtain ⟨c₅, k₅, e₅, hk₅, b₅, s₅, r₅, m₅⟩ : ∃ c₅ k₅,
      Exec P W (.ifLtN 218020 218046 scTake .skip) c₄ c₅ k₅ ∧ k₅ ≤ 6 ∧
      c₅.nreg 218030 = (if Yh P H (s + b) < Yh P H (s + k) then k else b) ∧
      SymPtIn c₅ 218040 (pt H P.n (s + (if Yh P H (s + b) < Yh P H (s + k) then k else b))) ∧
      (∀ r, r ≠ 218030 → r ≠ 218040 → r ≠ 218041 → r ≠ 218042 → c₅.nreg r = c₄.nreg r) ∧
      c₅.nmem = c₄.nmem := by
    by_cases hc : c₄.nreg 218020 < c₄.nreg 218046
    · have hy : Yh P H (s + b) < Yh P H (s + k) := t₄.1 (by omega)
      rw [ite_eq_left hy]
      refine spec_ifLtN_true hc ?_
      unfold scTake
      exec_block
      refine ⟨by omega, by config_simp; exact c431, symPtIn_copy sk₄ (by config_simp)
        (by config_simp) (by config_simp), fun r h1 h2 h3 h4 => ?_, rfl⟩
      simp only [Config.nreg_mk, upd, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
    · have hy : ¬ Yh P H (s + b) < Yh P H (s + k) := fun h => hc (by
        rw [c420]; have := t₄.2 h; omega)
      rw [ite_eq_right hy]
      exact spec_ifLtN_false hc (spec_skip w₄ ⟨by omega, c430, sb₄, fun r _ _ _ _ => rfl, rfl⟩)
  have w₅ := e₅.wb_right
  have k₅' : ∀ r, 218000 ≤ r → r ≠ 218030 → r ≠ 218040 → r ≠ 218041 → r ≠ 218042 →
      r ≠ 218043 → r ≠ 218044 → r ≠ 218045 → r ≠ 218046 → c₅.nreg r = c.nreg r :=
    fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 => by
      rw [r₅ r h1 h2 h3 h4, k₄' r h0 h8, k₃' r h0 h5 h6 h7]
  -- the next point
  obtain ⟨c₆, k₆, e₆, hk₆, v31, r₆⟩ : ∃ c₆ k₆, Exec P W (block [.addN 218031 218031 218021])
      c₅ c₆ k₆ ∧ k₆ = 1 ∧ c₆.nreg 218031 = k + 1 ∧
      c₆ = { c₅ with nreg := upd c₅.nreg 218031 (k + 1) } := by
    have e31 : c₅.nreg 218031 = k := by
      rw [r₅ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), c431]
    have e21 : c₅.nreg 218021 = 1 := by
      rw [r₅ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), c421]
    exec_block
    · config_simp; rw [e31, e21]; have := E.hN; omega
    refine ⟨rfl, by config_simp; rw [e31, e21], ?_⟩
    rw [e31, e21]
  have w₆ := e₆.wb_right
  have ex : Exec P W scBody c c₆ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))
  have k₆' : ∀ r, 218000 ≤ r → r ≠ 218030 → r ≠ 218031 → r ≠ 218040 → r ≠ 218041 →
      r ≠ 218042 → r ≠ 218043 → r ≠ 218044 → r ≠ 218045 → r ≠ 218046 → c₆.nreg r = c.nreg r :=
    fun r h0 h1 h1' h2 h3 h4 h5 h6 h7 h8 => by
      rw [r₆]; simp only [upd, ite_eq_right h1']; exact k₅' r h0 h1 h2 h3 h4 h5 h6 h7 h8
  have E₆ : HostEnv W HB H.length m₀ c₆ := by
    have g : ∀ r, 50060 ≤ r → r < 50070 → c₆.nreg r = c₄.nreg r := fun r h1 h2 => by
      rw [r₆]; simp only [upd, ite_eq_right (show r ≠ 218031 by omega)]
      exact r₅ r (by omega) (by omega) (by omega) (by omega)
    exact ⟨w₆, by rw [g _ (by norm_num) (by norm_num)]; exact E₄.h60,
      by rw [g _ (by norm_num) (by norm_num)]; exact E₄.h61,
      by rw [g _ (by norm_num) (by norm_num)]; exact E₄.h67,
      by rw [g _ (by norm_num) (by norm_num)]; exact E₄.h68,
      by rw [g _ (by norm_num) (by norm_num)]; exact E₄.h69, by rw [r₆]; exact m₅.trans E₄.mem⟩
  have v30 : c₆.nreg 218030 = (if Yh P H (s + b) < Yh P H (s + k) then k else b) := by
    rw [r₆]; simp only [upd]; exact b₅
  have hbk := hI.bk
  rw [hkdef, hbdef] at hbk
  have hle := hI.le
  have hlt' := hI.lt
  rw [hkdef, hbdef] at hle
  rw [hbdef] at hlt'
  have kk : ∀ r, 218000 ≤ r → r < 218030 → c₆.nreg r = c.nreg r := fun r h0 h1 =>
    k₆' r h0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  have I₆ : ScI P W H m₀ HB s m c₆ := by
    refine ⟨E₆, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [kk _ (by norm_num) (by norm_num)]; exact hI.r01
    · rw [kk _ (by norm_num) (by norm_num)]; exact hI.r20
    · rw [kk _ (by norm_num) (by norm_num)]; exact hI.r21
    · rw [k₆' _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact hI.r32
    · omega
    · omega
    · rw [v30, v31]; split_ifs <;> omega
    · rw [v30]
      exact symPtIn_copy s₅ (by rw [r₆]; simp [upd]) (by rw [r₆]; simp [upd])
        (by rw [r₆]; simp [upd])
    · rw [v30, v31]
      intro j hj
      split_ifs with hy
      · rcases Nat.lt_or_ge j k with h | h
        · exact (hle j h).trans hy.le
        · rw [show j = k by omega]
      · rcases Nat.lt_or_ge j k with h | h
        · exact hle j h
        · rw [show j = k by omega]; exact not_lt.1 hy
    · rw [v30]
      intro j hj
      split_ifs at hj ⊢ with hy
      · rcases Nat.lt_or_ge j b with h | h
        · exact (hlt' j h).trans hy
        · exact lt_of_le_of_lt (hle j hj) hy
      · exact hlt' j hj
  refine ⟨c₆, _, ex, I₆, by omega, by rw [v31, hkdef]; omega⟩

/-- **The scan**: `218013 := T ≤ m`, the least offset of a highest point among the host points
`s, …, s + m`. -/
theorem scanS_exec {H : Host} {m₀ : ℕ → ℕ} {HB : ℕ} (E : ScE P W H m₀ HB) (c : Config)
    (hE : HostEnv W HB H.length m₀ c) (h20 : c.nreg 218020 = 0) (h21 : c.nreg 218021 = 1)
    (hsm : c.nreg 218001 + c.nreg 218002 + 1 ≤ (H.pts P.n).length) :
    ∃ c' k, Exec P W scanS c c' k ∧ k ≤ 1992 * c.nreg 218002 + 1750 ∧ FrameB Bscan c c' ∧
      HostEnv W HB H.length m₀ c' ∧ c'.nreg 218013 ≤ c.nreg 218002 ∧
      (∀ j, j ≤ c.nreg 218002 →
        Yh P H (c.nreg 218001 + j) ≤ Yh P H (c.nreg 218001 + c'.nreg 218013)) ∧
      (∀ j, j < c'.nreg 218013 →
        Yh P H (c.nreg 218001 + j) < Yh P H (c.nreg 218001 + c'.nreg 218013)) := by
  have hw := hE.wb
  have hWn := E.nW
  obtain ⟨s, hs⟩ : ∃ s, c.nreg 218001 = s := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, c.nreg 218002 = m := ⟨_, rfl⟩
  rw [hs, hm] at hsm ⊢
  -- the first point
  obtain ⟨c₁, k₁, e₁, hk₁, v71, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50071 218001])
      c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 50071 = s ∧ (∀ r, r ≠ 50071 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    refine ⟨rfl, by config_simp; exact hs, fun r hr => ?_, rfl⟩
    simp only [Config.nreg_mk, upd, ite_eq_right hr]
  have E₁ : HostEnv W HB H.length m₀ c₁ := ⟨e₁.wb_right, by rw [r₁ _ (by decide)]; exact hE.h60,
    by rw [r₁ _ (by decide)]; exact hE.h61, by rw [r₁ _ (by decide)]; exact hE.h67,
    by rw [r₁ _ (by decide)]; exact hE.h68, by rw [r₁ _ (by decide)]; exact hE.h69,
    by rw [m₁]; exact hE.mem⟩
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, E₂, s₂⟩ := look_pt E c₁ E₁ v71 (by omega)
  have w₂ := e₂.wb_right
  have k₂' : ∀ r, 218000 ≤ r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [F₂.1 r (bhost_218 hr), r₁ r (by omega)]
  obtain ⟨c₃, k₃, e₃, hk₃, I₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN 218040 50046, .copyN 218041 50047, .copyN 218042 50048, .constN 218030 0,
        .constN 218031 1, .addN 218032 218002 218021]) c₂ c₃ k₃ ∧ k₃ = 6 ∧
      ScI P W H m₀ HB s m c₃ := by
    exec_block
    all_goals first | omega | skip
    · config_simp; rw [k₂' _ (by norm_num), k₂' _ (by norm_num), hm, h21]; have := E.hN; omega
    refine ⟨rfl, ⟨⟨‹_›, by config_simp; exact E₂.h60, by config_simp; exact E₂.h61,
      by config_simp; exact E₂.h67, by config_simp; exact E₂.h68, by config_simp; exact E₂.h69,
      by config_simp; exact E₂.mem⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    all_goals config_simp
    all_goals first
      | omega
      | (rw [k₂' _ (by norm_num)]; first | exact hs | exact h20 | exact h21)
      | (rw [k₂' _ (by norm_num), k₂' _ (by norm_num), hm, h21])
      | (rw [Nat.add_zero]; exact symPtIn_copy s₂ (by config_simp) (by config_simp)
          (by config_simp))
      | (intro j hj; rw [show j = 0 by omega])
      | (intro j hj; omega)
  -- the loop
  obtain ⟨c₄, k₄, e₄, I₄, hx₄, hk₄⟩ := Exec.whileLtN_bounded (P := P) (W := W) (a := 218031)
    (b := 218032) (body := scBody) (ScI P W H m₀ HB s m) (fun d => m + 1 - d.nreg 218031) 1990
    (fun d hd => hd.env.wb) (fun d hd ht => by
      obtain ⟨d', k, e, I', hk, hμ⟩ := scBody_exec E hsm d hd ht
      exact ⟨d', k, e, I', hk, hμ⟩) I₃
  have hk₄' : k₄ ≤ 1992 * m + 2 := by
    have := I₃.k1
    have : (1990 + 2) * (m + 1 - c₃.nreg 218031) ≤ 1992 * m := Nat.mul_le_mul_left _ (by omega)
    omega
  have w₄ := e₄.wb_right
  have hx : c₄.nreg 218031 = m + 1 := by have := I₄.km; rw [I₄.r32] at hx₄; omega
  obtain ⟨c₅, k₅, e₅, hk₅, v13, r₅⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 218013 218030]) c₄ c₅ k₅ ∧
      k₅ = 1 ∧ c₅.nreg 218013 = c₄.nreg 218030 ∧
      c₅ = { c₄ with nreg := upd c₄.nreg 218013 (c₄.nreg 218030) } := by
    exec_block
    exact ⟨rfl, by config_simp, rfl⟩
  have ex : Exec P W scanS c c₅ (k₁ + (k₂ + k₃) + (k₄ + k₅)) := .seq (.seq e₁ (.seq e₂ e₃)) (.seq e₄ e₅)
  have hbk := I₄.bk
  rw [hx] at hbk
  refine ⟨c₅, _, ex, by omega, exec_frameB ex wr_scanS', ?_, by rw [v13]; omega, fun j hj => ?_,
    fun j hj => ?_⟩
  · have E₄ := I₄.env
    have w₅ := e₅.wb_right
    rw [r₅] at w₅ ⊢
    exact ⟨w₅, by simp only [upd]; exact E₄.h60, by simp only [upd]; exact E₄.h61,
      by simp only [upd]; exact E₄.h67, by simp only [upd]; exact E₄.h68,
      by simp only [upd]; exact E₄.h69, E₄.mem⟩
  · rw [v13]; exact I₄.le j (by omega)
  · rw [v13] at hj ⊢; exact I₄.lt j hj

end exec

end

end DrvP

end Chazelle.Core
