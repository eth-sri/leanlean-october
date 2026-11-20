module

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.OraclePrepOrd

/-!
# Lemma 3.6 (WP-H), preprocessing part 26: the comparator of the chord table

`chCmp` compares two chord records `a`, `b` (registers `30000`, `30001`) by `ChLe`: height
vertex, then the class of the left end, then (class `1`) the abscissa of the left end, by the sign
kernel.  Records `≥ K` come after, in their natural order (`chLeB`).  The chord area and `K` are in
`116000`, `116001`; the constants of the query (`120010 … 120049`) are those of a configuration
`c₀`, read through the values `qvOf c₀`.  Main result: `chCmp_ok` (the comparator contract).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-! ## The order -/

section Order

variable (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ)

theorem chLe_total (a b : ℕ) : ChLe P C V m a b ∨ ChLe P C V m b a := by
  unfold ChLe
  rcases lt_trichotomy (chH m V a) (chH m V b) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy (xpClass (chL m V a)) (xpClass (chL m V b)) with g | g | g
    · exact Or.inl (Or.inr ⟨h, Or.inl g⟩)
    · rcases le_total (xpX' P C V (chL m V a) (chH m V a)) (xpX' P C V (chL m V b) (chH m V b))
        with f | f
      · exact Or.inl (Or.inr ⟨h, Or.inr ⟨g, fun _ => f⟩⟩)
      · exact Or.inr (Or.inr ⟨h.symm, Or.inr ⟨g.symm, fun _ => f⟩⟩)
    · exact Or.inr (Or.inr ⟨h.symm, Or.inl g⟩)
  · exact Or.inr (Or.inl h)

theorem chLe_trans {a b d : ℕ} (h1 : ChLe P C V m a b) (h2 : ChLe P C V m b d) :
    ChLe P C V m a d := by
  unfold ChLe at *
  rcases h1 with h1 | ⟨e1, h1 | ⟨f1, g1⟩⟩ <;> rcases h2 with h2 | ⟨e2, h2 | ⟨f2, g2⟩⟩ <;>
    first
      | (left; omega)
      | (right; exact ⟨by omega, Or.inl (by omega)⟩)
      | (right; exact ⟨by omega, Or.inr ⟨by omega, fun h => le_trans (g1 h) (g2 (by omega))⟩⟩)

open Classical in
/-- **The comparison of the sort**: records below `K` by `ChLe`, then the others. -/
noncomputable def chLeB (K a b : ℕ) : Bool :=
  if a < K then (if b < K then decide (ChLe P C V m a b) else true)
  else (if b < K then false else decide (a ≤ b))

theorem chLeB_total (K a b : ℕ) : (chLeB P C V m K a b || chLeB P C V m K b a) = true := by
  unfold chLeB
  have := chLe_total P C V m a b
  split_ifs <;> simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.or_true,
    Bool.or_false] <;> first | omega

theorem chLeB_trans (K a b d : ℕ) (h1 : chLeB P C V m K a b = true)
    (h2 : chLeB P C V m K b d = true) : chLeB P C V m K a d = true := by
  unfold chLeB at *
  split_ifs at h1 h2 ⊢ <;> simp only [decide_eq_true_eq] at h1 h2 ⊢ <;>
    first | omega | exact chLe_trans P C V m h1 h2

end Order

/-! ## The values read from the constant registers -/

/-- The values of the query read from the constant registers of `c`. -/
def qvOf (c : Config) : QV where
  D := c.nreg 120013
  NB := c.nreg 120014
  s := c.nreg 120015
  m := c.nreg 120016
  tIdx := c.nreg 120017
  β := c.nreg 120018
  sS := c.nreg 120021
  tv := c.nreg 120022
  hz := c.nreg 120023
  σb := c.nreg 120024
  zo := none
  A := c.nreg 120030
  POS := c.nreg 120031
  FL := c.nreg 120032
  LAB := c.nreg 120033
  DL := c.nreg 120034
  nD := c.nreg 120035
  ORD := c.nreg 120036
  RK := c.nreg 120037
  CH := c.nreg 120038
  K := c.nreg 120039
  MD := c.nreg 120040
  TB := c.nreg 120041
  L := c.nreg 120042
  CB := c.nreg 120043
  AB := c.nreg 120044
  RB := c.nreg 120045
  SB := c.nreg 120046
  LB := c.nreg 120047
  μ := c.nreg 120049

/-- The constant registers of `c` are those of the query for `qvOf c`, when they are consistent. -/
theorem qconst_qvOf {P : Polygon} {c : Config} (hn : c.nreg 120010 = P.n) (h1 : c.nreg 120011 = 1)
    (h0 : c.nreg 120012 = 0) (h2 : c.nreg 120048 = 2) (h6 : c.nreg 120028 = 6)
    (hm2 : c.nreg 120019 = 2 * c.nreg 120016) (hnW : c.nreg 120020 = 2 * c.nreg 120016 + 7)
    (hE : c.nreg 120029 = 2 * c.nreg 120016 + 6) (h25 : c.nreg 120025 = 2) :
    QConst P (qvOf c) c :=
  ⟨hn, h1, h0, rfl, rfl, rfl, rfl, rfl, rfl, hm2, hnW, rfl, rfl, rfl, rfl,
    Or.inl ⟨h25, rfl⟩, h6, hE, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, h2, rfl⟩

/-- Compute the address of a chord record and load its height. -/
def chRec (ix ptr dst : ℕ) : Stmt :=
  block [.addN ptr ix ix, .addN ptr ptr ptr, .addN ptr ptr ix, .addN ptr ptr 116000, .loadN dst ptr]

section

variable {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)

include P hw in
theorem chRec_exec
    {ix ptr dst CB x : ℕ} (hix : ix ≠ ptr) (hptr : 116000 ≠ ptr) (hdst : ptr ≠ dst)
    (h0 : c.nreg 116000 = CB) (hx : c.nreg ix = x) (hb : CB + 5 * x ≤ W) :
    ∃ c' k, Exec P W (chRec ix ptr dst) c c' k ∧ k = 5 ∧
      FrameB (fun r => decide (r = ptr ∨ r = dst)) c c' ∧ c'.nreg ptr = CB + 5 * x ∧
      c'.nreg dst = c.nmem (CB + 5 * x) := by
  refine spec_frame ?_ (by simp [chRec, block, Stmt.check, Footprint.allows])
  unfold chRec
  exec_block
  all_goals try (solve | omega | (ram_simp [*]; omega))
  refine ⟨rfl, ?_, ?_⟩ <;> ram_simp [*] <;> ring_nf

abbrev chRecA := chRec 30000 116012 116010
abbrev chRecB := chRec 30001 116013 116011

abbrev chRecA_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {CB x : ℕ} :=
  chRec_exec (P := P) hw (ix := 30000) (ptr := 116012) (dst := 116010) (CB := CB) (x := x)
    (by decide) (by decide) (by decide)

abbrev chRecB_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {CB x : ℕ} :=
  chRec_exec (P := P) hw (ix := 30001) (ptr := 116013) (dst := 116011) (CB := CB) (x := x)
    (by decide) (by decide) (by decide)

/-- Read the walk edge at the left end of a record. -/
def chW (ptr dst : ℕ) : Stmt := block [.addN dst ptr 120011, .loadN dst dst]

include P hw in
theorem chW_exec {ptr dst a : ℕ}
    (ht : c.nreg ptr = a) (h1 : c.nreg 120011 = 1) (hb : a + 1 ≤ W) :
    ∃ c' k, Exec P W (chW ptr dst) c c' k ∧ k = 2 ∧ FrameB (fun r => decide (r = dst)) c c' ∧
      c'.nreg dst = c.nmem (a + 1) := by
  refine spec_frame ?_ (by simp [chW, block, Stmt.check, Footprint.allows])
  unfold chW
  exec_block <;> ram_finish

abbrev chWA := chW 116012 116014
abbrev chWB := chW 116013 116015

abbrev chWA_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {a : ℕ} :=
  chW_exec (P := P) hw (ptr := 116012) (dst := 116014) (a := a)

abbrev chWB_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {a : ℕ} :=
  chW_exec (P := P) hw (ptr := 116013) (dst := 116015) (a := a)

/-- The class and the symbolic point of the left end of `a`, saved in `116016 … 116019`. -/
def xpA : Stmt :=
  .seq (block [.copyN 120120 116014, .copyN 120121 116010])
    (.seq xpS (block [.copyN 116016 120122, .copyN 116017 120123, .copyN 116018 120124,
      .copyN 116019 120125]))

/-- The class and the symbolic point of the left end of `b` (in `120122 …`). -/
def xpB : Stmt := .seq (block [.copyN 120120 116015, .copyN 120121 116011]) xpS

/-- The registers written by the comparator (besides the kernel's and `30002`). -/
def BCh (r : ℕ) : Bool := decide (116010 ≤ r ∧ r ≤ 116019) || decide (120120 ≤ r ∧ r ≤ 120128)

include P hw in
private theorem xpInputs_exec
    {ix hgt : ℕ} (hh : hgt ≠ 120120) :
    ∃ c' k, Exec P W (block [.copyN 120120 ix, .copyN 120121 hgt]) c c' k ∧ k = 2 ∧
      FrameB (fun r => decide (r = 120120 ∨ r = 120121)) c c' ∧
      c'.nreg 120120 = c.nreg ix ∧ c'.nreg 120121 = c.nreg hgt := by
  refine spec_frame ?_ (by rfl)
  exec_block <;> ram_finish

end

section

variable {P : Polygon} {W : ℕ} (hW : 4 * P.n + 8 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) {c : Config} (hw : WordsBounded W c) (hq : QConst P V c)
include hW hv hw hq

theorem xpA_exec :
    ∃ c' k, Exec P W xpA c c' k ∧ k ≤ 46 ∧
      FrameB (fun r => decide (116016 ≤ r ∧ r ≤ 116019) || decide (120120 ≤ r ∧ r ≤ 120128)) c c' ∧
      c'.nreg 116016 = xpClass (c.nreg 116014) ∧
      (xpClass (c.nreg 116014) = 1 →
        SymPtIn c' 116017 (xpSym C V P.n (c.nreg 116014) (c.nreg 116010))) := by
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, a0, a1⟩ := xpInputs_exec (P := P) hw
    (ix := 116014) (hgt := 116010) (by decide)
  have hq₁ := hq.frame F₁ (fun r h1 h2 => by simp only [decide_eq_false_iff_not]; omega)
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, x1, x2⟩ := xpS_exec (P := P) hW hv c₁ e₁.wb_right hq₁
  rw [a0] at x1 x2; rw [a1] at x2
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, y6, y7, y8, y9⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN 116016 120122, .copyN 116017 120123, .copyN 116018 120124,
        .copyN 116019 120125]) c₂ c₃ k₃ ∧ k₃ = 4 ∧
      FrameB (fun r => decide (116016 ≤ r ∧ r ≤ 116019)) c₂ c₃ ∧
      c₃.nreg 116016 = c₂.nreg 120122 ∧ c₃.nreg 116017 = c₂.nreg 120123 ∧
      c₃.nreg 116018 = c₂.nreg 120124 ∧ c₃.nreg 116019 = c₂.nreg 120125 := by
    refine spec_frame ?_
    have w₂ := e₂.wb_right
    exec_block <;> ram_finish
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, ?_, by rw [y6, x1], fun h => ?_⟩
  · ram_frame
  · have hs := x2 h
    unfold xpSym at hs ⊢
    split_ifs at hs ⊢
    · exact ⟨by rw [y7]; exact hs.1, by rw [y8]; exact hs.2.1, by rw [y9]; exact hs.2.2⟩
    · exact ⟨by rw [y7]; exact hs.1, by rw [y8]; exact hs.2⟩

theorem xpB_exec :
    ∃ c' k, Exec P W xpB c c' k ∧ k ≤ 42 ∧
      FrameB (fun r => decide (120120 ≤ r ∧ r ≤ 120128)) c c' ∧
      c'.nreg 120122 = xpClass (c.nreg 116015) ∧
      (xpClass (c.nreg 116015) = 1 →
        SymPtIn c' 120123 (xpSym C V P.n (c.nreg 116015) (c.nreg 116011))) := by
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, a0, a1⟩ := xpInputs_exec (P := P) hw
    (ix := 116015) (hgt := 116011) (by decide)
  have hq₁ := hq.frame F₁ (fun r h1 h2 => by simp only [decide_eq_false_iff_not]; omega)
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, x1, x2⟩ := xpS_exec (P := P) hW hv c₁ e₁.wb_right hq₁
  rw [a0] at x1 x2; rw [a1] at x2
  refine ⟨c₂, _, .seq e₁ e₂, by omega, ?_, x1, x2⟩
  refine (FrameB.mono F₁ fun r hr => ?_).trans (FrameB.mono F₂ fun r hr => ?_)
  · simp_all <;> omega
  · simp_all [BX, decide_eq_true_eq] <;> omega

end

/-! ## The comparator -/

/-- The decision on equal heights: by the classes, then by the abscissas (sign kernel). -/
def chDec : Stmt :=
  .ifLtN 116016 120122 (.instr (.constN 30002 1))
    (.ifLtN 120122 116016 (.instr (.constN 30002 0))
      (.ifLtN 116016 120011 (.instr (.constN 30002 1))
        (.ifLtN 120011 116016 (.instr (.constN 30002 1))
          (.seq (sgnS 0 (.regs 120123) (.regs 116017) (.regs 116017))
            (.instr (.subN 30002 120011 10010))))))

/-- Equal heights. -/
def chTie : Stmt := .seq chWA (.seq chWB (.seq xpA (.seq xpB chDec)))

/-- Two records. -/
def chBoth : Stmt :=
  .seq chRecA (.seq chRecB (.ifLtN 116010 116011 (.instr (.constN 30002 1))
    (.ifLtN 116011 116010 (.instr (.constN 30002 0)) chTie)))

/-- **The comparator of the chord table.** -/
def chCmp : Stmt :=
  .ifLtN 30000 116001 (.ifLtN 30001 116001 chBoth (.instr (.constN 30002 1)))
    (.ifLtN 30001 116001 (.instr (.constN 30002 0))
      (.ifLtN 30001 30000 (.instr (.constN 30002 0)) (.instr (.constN 30002 1))))

/-- The registers written by the comparator. -/
def BCmp (r : ℕ) : Bool := decide (r = 30002) || BCh r || Bk r

theorem wr_chCmp : wr BCmp chCmp = true := by decide

theorem wrR_chCmp : wrR Bk chCmp = true := by decide

/-- The invariant of the comparator. -/
def ChCJ (c₀ : Config) (m₀ : ℕ → ℕ) (A₀ K : ℕ) (c : Config) : Prop :=
  c.nreg 116000 = (qvOf c₀).CB ∧ c.nreg 116001 = K ∧
    (∀ r, 120010 ≤ r → r ≤ 120049 → c.nreg r = c₀.nreg r) ∧ MemEqBelow A₀ c.nmem m₀

theorem chCJ_stable (c₀ : Config) (m₀ : ℕ → ℕ) (A₀ K : ℕ) :
    SortR.JStable (ChCJ c₀ m₀ A₀ K) A₀ := by
  intro c c' ⟨h0, h1, h2, h3⟩ hr _ hm _ _
  have hb : ∀ r, (116000 ≤ r ∧ r < 130000) → c'.nreg r = c.nreg r := fun r h =>
    hr r (by reg_omega) (by reg_omega)
  exact ⟨by ram_finish, by ram_finish,
    fun r a b => by ram_finish, fun a ha => (hm a ha).trans (h3 a ha)⟩

section

variable {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {c₀ : Config} {m₀ : ℕ → ℕ} {A₀ K : ℕ} (hv : QVOK P C (qvOf c₀))
    (hq : QConst P (qvOf c₀) c₀) (hrec : ∀ i, i < K → (qvOf c₀).CB + 5 * i + 2 ≤ A₀)
    (hAW : A₀ ≤ W)
    (hh : ∀ i, i < K → m₀ ((qvOf c₀).CB + 5 * i) < P.n) (htv : (qvOf c₀).tv < P.n)
    (hn : 0 < P.n)
include hG hW hv hq hrec hAW hh htv hn

set_option maxHeartbeats 8000000 in
theorem chBoth_exec {c : Config} (hw : WordsBounded W c) (hJ : ChCJ c₀ m₀ A₀ K c)
    (hA : c.nreg 30000 < K) (hB : c.nreg 30001 < K) :
    ∃ c' k, Exec P W chBoth c c' k ∧ k ≤ 480 ∧
      (ChLe P C (qvOf c₀) m₀ (c.nreg 30000) (c.nreg 30001) → c'.nreg 30002 = 1) ∧
      (¬ ChLe P C (qvOf c₀) m₀ (c.nreg 30000) (c.nreg 30001) → c'.nreg 30002 = 0) := by
  obtain ⟨j0, j1, j2, j3⟩ := hJ
  have hra := hrec _ hA
  have hrb := hrec _ hB
  set V := qvOf c₀ with hV
  have hq' := hq.congr fun r a b => j2 r a b
  have hW1 : 1 ≤ W := by omega
  have hW4 : 4 * P.n + 8 ≤ W := by omega
  set a := c.nreg 30000 with ha
  set b := c.nreg 30001 with hb
  -- the heights
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, t12, h10⟩ := chRecA_exec (P := P) (CB := V.CB) (x := a) hw j0 rfl
    (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, t13, h11⟩ := chRecB_exec (P := P) (CB := V.CB) (x := b) e₁.wb_right
    (by ram_rw assumption [F₁.1]) (by ram_rw [F₁.1]) (by omega)
  have hHa : c₂.nreg 116010 = chH m₀ V a := by
    frame_finish [F₂.1, h10, j3]
  have hHb : c₂.nreg 116011 = chH m₀ V b := by
    frame_finish [h11, F₁.2.2.1, j3]
  have t12' : c₂.nreg 116012 = V.CB + 5 * a := by ram_rw [F₂.1, t12]
  have hq₂ := (hq'.frame F₁ fun r h1 h2 => by
    simp only [decide_eq_false_iff_not]; omega).frame F₂ fun r h1 h2 => by
      simp only [decide_eq_false_iff_not]; omega
  have hm₂ := F₂.2.2.1.trans F₁.2.2.1
  have w₂ := e₂.wb_right
  rcases lt_trichotomy (chH m₀ V a) (chH m₀ V b) with hlt | heq | hgt
  · refine ⟨_, _, .seq e₁ (.seq e₂ (.ifLtN_true (by rwa [hHa, hHb])
      (Exec.constN w₂ 30002 1 hW1))), by omega, fun _ => by config_simp, fun hc => ?_⟩
    exact absurd (Or.inl hlt) hc
  · -- equal heights
    have nlt : ¬ c₂.nreg 116010 < c₂.nreg 116011 := by rw [hHa, hHb]; omega
    obtain ⟨c₃, k₃, e₃, hk₃, F₃, w14⟩ := chWA_exec (P := P) w₂ t12' hq₂.one (by omega)
    obtain ⟨c₄, k₄, e₄, hk₄, F₄, w15⟩ := chWB_exec (P := P) e₃.wb_right
      (by ram_rw [F₃.1, t13])
      (by ram_rw [F₃.1]; exact hq₂.one) (by omega)
    have hLa : c₄.nreg 116014 = chL m₀ V a := by
      ram_rw [F₄.1, w14, hm₂, j3]; rfl
    have hLb : c₄.nreg 116015 = chL m₀ V b := by
      ram_rw [w15, F₃.2.2.1, hm₂, show V.CB + 5 * b + 1 = V.CB + 5 * b + 1 from rfl,
        j3]; rfl
    have hq₄ := (hq₂.frame F₃ fun r h1 h2 => by
      simp only [decide_eq_false_iff_not]; omega).frame F₄ fun r h1 h2 => by
        simp only [decide_eq_false_iff_not]; omega
    have hHa4 : c₄.nreg 116010 = chH m₀ V a := by
      frame_finish [F₄.1, F₃.1, hHa]
    have hHb4 : c₄.nreg 116011 = chH m₀ V b := by
      frame_finish [F₄.1, F₃.1, hHb]
    obtain ⟨c₅, k₅, e₅, hk₅, F₅, x16, sA⟩ := xpA_exec (P := P) hW4 hv e₄.wb_right hq₄
    rw [hLa] at x16 sA; rw [hHa4] at sA
    have hq₅ := hq₄.frame F₅ fun r h1 h2 => by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have hLb5 : c₅.nreg 116015 = chL m₀ V b := by
      ram_rw [F₅.1, hLb]
    have hHb5 : c₅.nreg 116011 = chH m₀ V b := by
      ram_rw [F₅.1, hHb4]
    obtain ⟨c₆, k₆, e₆, hk₆, F₆, x22, sB⟩ := xpB_exec (P := P) hW4 hv e₅.wb_right hq₅
    rw [hLb5] at x22 sB; rw [hHb5] at sB
    have hq₆ := hq₅.frame F₆ fun r h1 h2 => by
      simp only [decide_eq_false_iff_not]; omega
    have x16' : c₆.nreg 116016 = xpClass (chL m₀ V a) := by ram_rw [F₆.1, x16]
    have sA' : xpClass (chL m₀ V a) = 1 →
        SymPtIn c₆ 116017 (xpSym C V P.n (chL m₀ V a) (chH m₀ V a)) := fun h => by
      have := sA h
      have g7 := F₆.1 116017 (by decide)
      have g8 := F₆.1 116018 (by decide)
      have g9 := F₆.1 116019 (by decide)
      ram_simp [SymPtIn, g7, g8, g9] <;> reg_omega
    have w₆ := e₆.wb_right
    have one₆ := hq₆.one
    have hTie : ∀ c' k, Exec P W chDec c₆ c' k →
        ∃ k', Exec P W chBoth c c' k' ∧ k' = k₁ + k₂ + k₃ + k₄ + k₅ + k₆ + k + 4 := by
      intro c' k ex
      exact ⟨_, .seq e₁ (.seq e₂ (.ifLtN_false nlt (.ifLtN_false (by omega)
        (by ram_path)))), by omega⟩
    
    
    rcases lt_trichotomy (xpClass (chL m₀ V a)) (xpClass (chL m₀ V b)) with g | g | g
    · obtain ⟨k', ex', hk'⟩ := hTie _ _ (.ifLtN_true (by rwa [x16', x22])
        (Exec.constN w₆ 30002 1 hW1))
      exact ⟨_, k', ex', by omega, fun _ => by config_simp,
        fun hc => absurd (Or.inr ⟨heq, Or.inl g⟩) hc⟩
    · by_cases g1 : xpClass (chL m₀ V a) = 1
      · -- the abscissas
        have la := xpSym_lt (C := C) (V := V) (w := chL m₀ V a) hn htv (hh a hA)
        obtain ⟨c₇, k₇, e₇, hk₇, F₇, hbit, hiff⟩ := sgnS_exec (P := P) hG (by omega) 0 (by norm_num)
          (.regs 120123) (.regs 116017) (.regs 116017) c₆ w₆ (by decide) (by decide) (by decide)
          (sB (by omega)) (sA' g1) (sA' g1) (xpSym_lt (C := C) (V := V) (w := chL m₀ V b) hn htv (hh b hB)) la la
        have one₇ : c₇.nreg 120011 = 1 := by ram_rw [F₇.1, one₆]
        obtain ⟨k', ex', hk'⟩ := hTie _ _ (.ifLtN_false (by rw [x16', x22]; omega)
          (.ifLtN_false (by rw [x16', x22]; omega) (.ifLtN_false (by rw [x16', one₆]; omega)
            (.ifLtN_false (by rw [x16', one₆]; omega) (.seq e₇ (Exec.subN (P := P) e₇.wb_right 30002 120011 10010))))))
        refine ⟨_, k', ex', by omega, ?_, ?_⟩
        · intro hc
          config_simp
          rw [one₇]
          have : ¬ c₇.nreg 10010 = 1 := by
            rw [hiff]; simp only [SignTest, not_lt]
            rcases hc with hc | ⟨-, hc | ⟨-, hc⟩⟩
            · omega
            · omega
            · exact hc g1
          omega
        · intro hc
          config_simp
          rw [one₇]
          have : c₇.nreg 10010 = 1 := by
            rw [hiff]; simp only [SignTest]
            by_contra hx
            exact hc (Or.inr ⟨heq, Or.inr ⟨g, fun _ => not_lt.1 hx⟩⟩)
          omega
      · -- the classes `0` and `2`
        have hc1 : xpClass (chL m₀ V a) < 1 ∨ 1 < xpClass (chL m₀ V a) := by omega
        have hok : ChLe P C V m₀ a b := Or.inr ⟨heq, Or.inr ⟨g, fun h => absurd h g1⟩⟩
        rcases hc1 with hc1 | hc1
        · obtain ⟨k', ex', hk'⟩ := hTie _ _ (.ifLtN_false (by rw [x16', x22]; omega)
            (.ifLtN_false (by rw [x16', x22]; omega) (.ifLtN_true (by rwa [x16', one₆])
              (Exec.constN w₆ 30002 1 hW1))))
          exact ⟨_, k', ex', by omega, fun _ => by config_simp, fun hc => absurd hok hc⟩
        · obtain ⟨k', ex', hk'⟩ := hTie _ _ (.ifLtN_false (by rw [x16', x22]; omega)
            (.ifLtN_false (by rw [x16', x22]; omega) (.ifLtN_false (by rw [x16', one₆]; omega)
              (.ifLtN_true (by rwa [x16', one₆]) (Exec.constN w₆ 30002 1 hW1)))))
          exact ⟨_, k', ex', by omega, fun _ => by config_simp, fun hc => absurd hok hc⟩
    · obtain ⟨k', ex', hk'⟩ := hTie _ _ (.ifLtN_false (by rw [x16', x22]; omega)
        (.ifLtN_true (by rwa [x16', x22]) (Exec.constN w₆ 30002 0 (Nat.zero_le _))))
      refine ⟨_, k', ex', by omega, fun hc => ?_, fun _ => by config_simp⟩
      exfalso
      rcases hc with hc | ⟨-, hc | ⟨hc, -⟩⟩ <;> omega
  · refine ⟨_, _, .seq e₁ (.seq e₂ (.ifLtN_false (by rw [hHa, hHb]; omega)
      (.ifLtN_true (by rwa [hHa, hHb]) (Exec.constN w₂ 30002 0 (Nat.zero_le _))))),
      by omega, fun hc => ?_, fun _ => by config_simp⟩
    exfalso
    rcases hc with hc | ⟨hc, -⟩ <;> omega

set_option maxHeartbeats 4000000 in
theorem chCmp_ok :
    SortR.CmpOK P W chCmp {bSign, bOPrep, bOQuery} (ChCJ c₀ m₀ A₀ K)
      (chLeB P C (qvOf c₀) m₀ K) 500 := by
  intro c hw hJ
  obtain ⟨j0, j1, j2, j3⟩ := hJ
  have hBc : ∀ r, (bandOf r = 1 ∨ bandOf r = 11 ∨ bandOf r = 12) →
      bandOf r ∈ ({bSign, bOPrep, bOQuery} : Finset ℕ) := by
    simp [Finset.mem_insert, Finset.mem_singleton, bSign, bOPrep, bOQuery]
  set V := qvOf c₀ with hV
  
  suffices H : ∃ c' k, Exec P W chCmp c c' k ∧ k ≤ 500 ∧
      c'.nreg 30002 = (if chLeB P C V m₀ K (c.nreg 30000) (c.nreg 30001) then 1 else 0) by
    obtain ⟨c', k, ex, hk, hbit⟩ := H
    have f := exec_frameB ex wr_chCmp
    refine ⟨c', k, ex, hk, ⟨?_, ?_, fun r a b => ?_, fun a ha => by rw [f.2.2.1]; exact j3 a ha⟩,
      hbit, fun r h0 h1 h2 hb => f.1 r ?_, fun r hb => (WalkKey.exec_rframe ex wrR_chCmp) r ?_, f.2.2.1, f.2.2.2.1, f.2.2.2.2⟩
    · ram_rw assumption [f.1]
    · ram_rw assumption [f.1]
    · rw [f.1 r (by simp only [BCmp, BCh, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)]
      exact j2 r a b
    · by_contra hc
      simp only [Bool.not_eq_false, BCmp, BCh, Bk, Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hb with hb | hb
      · exact hb (hBc r (by reg_omega))
      · unfold ALLOC at hb; omega
    · by_contra hc
      simp only [Bool.not_eq_false, Bk, decide_eq_true_eq] at hc
      exact hb (hBc r (by reg_omega))
  have hW1 : 1 ≤ W := by omega
  set a := c.nreg 30000 with ha
  set b := c.nreg 30001 with hb
  unfold chCmp chLeB
  by_cases hA : a < K
  · rw [ite_eq_left hA]
    by_cases hB : b < K
    · rw [ite_eq_left hB]
      obtain ⟨c', k, ex, hk, v1, v0⟩ := chBoth_exec hG hW hv hq hrec hAW hh htv hn hw
        ⟨j0, j1, j2, j3⟩ hA hB
      refine ⟨c', _, .ifLtN_true (by rwa [j1]) (.ifLtN_true (by rwa [j1]) ex),
        by omega, ?_⟩
      by_cases hc : ChLe P C V m₀ a b
      · rw [v1 hc]; simp [hc]
      · rw [v0 hc]; simp [hc]
    · rw [ite_eq_right hB]
      exact ⟨_, _, .ifLtN_true (by rwa [j1]) (.ifLtN_false (by rwa [j1])
        (Exec.constN hw 30002 1 hW1)), by omega, by config_simp; simp⟩
  · rw [ite_eq_right hA]
    by_cases hB : b < K
    · rw [ite_eq_left hB]
      exact ⟨_, _, .ifLtN_false (by rwa [j1]) (.ifLtN_true (by rwa [j1])
        (Exec.constN hw 30002 0 (Nat.zero_le _))), by omega, by config_simp; simp⟩
    · rw [ite_eq_right hB]
      by_cases hba : b < a
      · exact ⟨_, _, .ifLtN_false (by rwa [j1]) (.ifLtN_false (by rwa [j1])
          (.ifLtN_true hba (Exec.constN hw 30002 0 (Nat.zero_le _)))), by omega,
          by config_simp; simp; omega⟩
      · exact ⟨_, _, .ifLtN_false (by rwa [j1]) (.ifLtN_false (by rwa [j1])
          (.ifLtN_false hba (Exec.constN hw 30002 1 hW1))), by omega,
          by config_simp; simp; omega⟩

end

end

end OracleR

end Chazelle.Core
