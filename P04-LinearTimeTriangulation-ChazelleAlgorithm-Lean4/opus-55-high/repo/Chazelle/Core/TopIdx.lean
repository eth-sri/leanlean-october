module

public import Chazelle.Core.SpecNF
public import Chazelle.MacT
public import Chazelle.Existence.Diagonal
public import Chazelle.Final.Wedge
public import Chazelle.Core.ClusterEulerRam

namespace Chazelle.Mountain
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Existence
open Chazelle.Visibility (transpose transpose_n transpose_vtx transpose_simple
  mem_transpose_filled_iff)
open Chazelle.Programs (lexLE)
open Chazelle.Geometry (lerp det_cyclic point_ext)

/-- Swapping the coordinates negates the determinant. -/
theorem det_swap_swap_swap (a b c : Point) : det a.swap b.swap c.swap = -det a b c := by
  zumsj

/-- Balls of the sup metric are symmetric under swapping the coordinates. -/
theorem swap_mem_ball_swap_iff {y v : Point} {r : ℝ} : y.swap ∈ ball v.swap r ↔ y ∈ ball v r := by
  rw [mem_ball_iff_abs, mem_ball_iff_abs]
  grind
variable (P : Polygon)

/-- The lowest vertex of a mountain is `ylexLE`-smallest. -/
theorem ylexLE_zero (hM : IsMountain P) {i : ℕ} (hi : i < P.n) : ylexLE ztdt ztdn := by
  zujcx
  · tauto
  · exact ylexLE_of_ylexLT (ylexLT_of_lt P hM hpos hi)

/-- **The open sector at the lowest vertex of a mountain is interior**, on the side of
`det v_{n-1} v₀ v₁`: for `σ = ±1` with `0 < σ * det v_{n-1} v₀ v₁` there is `r > 0` such that
every point of the ball of radius `r` around `v₀` with `0 < σ * det v_{n-1} v₀ x` and
`0 < σ * det v₀ v₁ x` lies in `P.filled \ P.boundary`. -/
theorem sector_lowest_subset_interior (hM : IsMountain P) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 < σ * det ztwjc ztdt ztgk) :
    ∃ r > 0, ∀ y ∈ ball ztdt r,
      0 < σ * det ztwjc ztdt y → 0 < σ * det ztdt ztgk y →
        y ∈ P.filled \ P.boundary := by
  zuiwu
  zuemy

  have hTn : T.n = P.n := transpose_n P
  have hmin : ∀ i, i < T.n → lexLE (T.vtx 0) (T.vtx i) := by
    zug
    rw [hTn] at hi
    rw [hTdef, transpose_vtx, transpose_vtx]
    zuevr
    · tauto
    tauto
  zudpr
  have hposT : ztezf := by
    zuedb

  obtain ⟨r, hr, hsec⟩ := sector_subset_interior hT hmin hσ' hposT
  refine ztkmo
  have := hsec y.swap ztirq
    zthet
    ztiih
  rw [Set.mem_sdiff, mem_transpose_filled_iff, Chazelle.Visibility.mem_transpose_boundary_iff,
    Prod.swap_swap] at this
  grind

/-- **The orientation of a mountain is the sign of its lowest corner**:
`0 < orient P * det v_{n-1} v₀ v₁`. -/
theorem mountain_orient_det (hM : IsMountain P) :
    0 < orient P * det ztwjc ztdt ztgk := by
  zuiwu
  zuoo
  have hdet : ztbamp := by
    have := det_ne_zero_of_lexMin ztwgv (by
      zug
      zufoj

      zuevr
      · tauto
      tauto)
    zueea

  obtain ⟨σ, hσ, hpos⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * det ztwjc ztdt ztgk := by
    grind
  obtain ⟨r, hr, hsec⟩ := sector_lowest_subset_interior P hM hσ hpos
  zujr

  zuboa

  -- a point of the edge `u v` close to `v`, in the ball and on the `σ` side of `v w`

  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp u v zteb ∈ ball v r ∩ {x | 0 < σ * det v w x} ∧
      s ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [(tendsto_lerp_one_sub u v).eventually ztsd,
      Ioo_mem_nhdsGT ztcjf] with s hs hs01
    refine ztbabo
    show 0 < σ * det v w (lerp u v zteb)
    zuekx

  zucdz

  have hor : ztuuq := by
    apply orient_eq_of_eventually hP (i := P.n - 1) by_omega (t := 1 - s)
      ⟨by_grind, by_grind⟩ hσ
    zuyg

    show 0 < σ * det u v (offset u v zteb ztye)
    zucto

  grind

/-- **Correctness with the computable sign.**  For a mountain `P` and any `σ = ±1` with
`0 < σ * det v_{n-1} v₀ v₁`, the stack walk with sign `σ` triangulates `P` and performs at most
`2 * n` corner tests. -/
theorem mountain_triangulates_of_sign (hM : IsMountain P) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 < σ * det ztwjc ztdt ztgk) :
    P.Triangulates ztkbd ∧ mountainTests P σ ≤ 2 * P.n := by
  have hor : σ = orient P := by
    zujxw
    zuies
    · zuclh
    · zuguj
  exact ⟨mountain_triangulates P hM hor, mountainTests_le P hM hor⟩
open Machine Machine.Stmt Programs
open Chazelle.EarClip (detInto detInto_exec)
def stk (f : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | t + 1 => f t :: stk f t
variable (f : ℕ → ℕ) (t v : ℕ)
/-- Unfolding the stack by one entry: the top is `f t`. -/
@[simp] theorem stk_succ (t : ℕ) : stk f (t + 1) = f t :: stk f t := rfl

/-- The stack `stk f t` only depends on the entries of `f` below `t`. -/
theorem stk_congr {f g : ℕ → ℕ} {t : ℕ} (h : ∀ i, i < t → f i = g i) : stk f t = stk g t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [stk_succ, stk_succ, h t by_omega, ih (fun i hi => h i by_omega)]

/-- Writing at address `t` does not change the stack `stk f t`. -/
theorem stk_upd : stk ztrxy t = stk f t :=
  stk_congr (fun i hi => Machine.upd_other _ _ _ by_omega)

/-- **Push**: writing `v` at address `t` and taking `t + 1` entries pushes `v`. -/
theorem stk_push : stk ztrxy ztbx = v :: stk f t := by
  rw [stk_succ, Machine.upd_same, stk_upd]

/-- A stack with at least two entries: its top two entries are `f (t - 1)` and `f (t - 2)`. -/
theorem stk_two {f : ℕ → ℕ} {t : ℕ} (ht : 2 ≤ t) :
    stk f t = f ztso :: f ztubt :: stk f ztubt := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 2 := ⟨t - 2, by_omega⟩
  simp

/-- **Pop**: dropping the top entry. -/
theorem stk_pop {f : ℕ → ℕ} {t : ℕ} (ht : 1 ≤ t) : stk f t = f ztso :: stk f ztso := by
  zucyb
  simp

/-! ### The program -/

/-! ### The constants -/

/-! ### The corner test -/
section specs
variable {P : Polygon} {W : ℕ}

/-! ### The pop loop -/
end specs
open Chazelle.EarClip (subPoly relabelList vtx_subPoly_getD n_subPoly)
def stackS (c : Config) : List ℕ := stk ztkwd (c.nreg 63)
variable {c c' : Config}
/-- The stack only depends on `nreg 61`, `nreg 63` and the natural memory. -/
theorem stackS_congr (h61 : c'.nreg 61 = c.nreg 61)
    (h63 : c'.nreg 63 = c.nreg 63) (hnm : c'.nmem = c.nmem) : stackS c' = stackS c := by
  unfold stackS; rw [h61, h63, hnm]

/-- **Push into a shifted region**: writing `v` at address `s + t` and taking `t + 1` entries
of the region starting at `s` pushes `v`. -/
theorem stk_shift_push (g : ℕ → ℕ) (s t v : ℕ) :
    stk ztyjh ztbx = v :: stk ztzfe t := by
  have e : ztyjh = upd ztzfe t v := by
    funext i
    by_cases h : i = t
    · subst h; rw [Machine.upd_same, Machine.upd_same]
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ h]
  rw [e, stk_push]

/-- The layout hypothesis: the index table `base … base + m - 1` and the stack region
`sbase … sbase + m - 1` are disjoint, and every address of either region is `≤ W`. -/
def SLayout (W base sbase m : ℕ) : Prop :=
  (base + m ≤ sbase ∨ sbase + m ≤ base) ∧ base + m ≤ W ∧ sbase + m ≤ W

/-- The index table: `nmem (base + i) = l[i]` for `i < l.length`. -/
def STab (l : List ℕ) (base : ℕ) (c : Config) : Prop :=
  ∀ i, i < l.length → c.nmem zttgo = l.getD i 0

/-- The constants of the fragment: `nreg 60 = base`, `nreg 61 = sbase`, `nreg 62 = m`,
`nreg 65 = 1`, `nreg 68 = 2`, `nreg 70 = 0`, `rreg 70 = σ`, `rreg 72 = 0`. -/
def SConsts (base sbase m : ℕ) (σ : ℝ) (c : Config) : Prop :=
  c.nreg 60 = base ∧ c.nreg 61 = sbase ∧ c.nreg 62 = m ∧ c.nreg 65 = 1 ∧ c.nreg 68 = 2 ∧
    c.nreg 70 = 0 ∧ c.rreg 70 = σ ∧ c.rreg 72 = 0

/-- **The frame of the fragment**: `c` agrees with `c₀` on every natural register outside
`63 … 74`, every real register outside `61 … 72`, every natural memory cell outside the stack
region `nreg 61 … nreg 61 + nreg 62 - 1` (of `c₀`), and the whole real memory. -/
def SFrame (c₀ c : Config) : Prop :=
  (∀ r, zteva → c.nreg r = c₀.nreg r) ∧
  (∀ r, ztofw → c.rreg r = c₀.rreg r) ∧
  (∀ a, (a < c₀.nreg 61 ∨ c₀.nreg 61 + c₀.nreg 62 ≤ a) → c.nmem a = c₀.nmem a) ∧
  c.rmem = c₀.rmem

/-- The frame is reflexive. -/
theorem sFrame_refl (c : Config) : SFrame c c :=
  ⟨by_omega, by_simp_all, by_omega, rfl⟩

/-- The frame is transitive. -/
theorem sFrame_trans {c₀ c₁ c₂ : Config} (h₁ : SFrame c₀ c₁) (h₂ : SFrame c₁ c₂) :
    SFrame c₀ c₂ := by
  obtain ⟨n₁, r₁, m₁, q₁⟩ := h₁
  obtain ⟨n₂, r₂, m₂, q₂⟩ := h₂
  have e61 : c₁.nreg 61 = c₀.nreg 61 := by_simp_all
  have e62 : c₁.nreg 62 = c₀.nreg 62 := by_simp_all
  refine ⟨by_simp_all, by_simp_all,
    fun a ha => ?_, by rw [q₂, q₁]⟩
  rw [m₂ a (by rw [e61, e62]; exact ha), m₁ a ha]

/-- A step that changes nothing but the natural registers `63 … 74`, the real registers
`61 … 72` and the output keeps the frame. -/
theorem sFrame_of_regs (hn : ∀ r, zteva → c'.nreg r = c.nreg r)
    (hr : ∀ r, ztofw → c'.rreg r = c.rreg r) (hnm : c'.nmem = c.nmem)
    (hrm : c'.rmem = c.rmem) : SFrame c c' :=
  ⟨hn, hr, by_simp_all, hrm⟩

/-! ### The program -/

/-- The corner test, reading: the positions `c := nmem (sbase + top - 1)`,
`b := nmem (sbase + top - 2)`, the original indices `l[c]`, `l[b]`, `l[k]` from the table, then
the coordinates of `vtx l[b]`, `vtx l[c]`, `vtx l[k]` into `rreg 61 … rreg 66`.
Exactly `17` instructions. -/
def subReadStmt : Stmt :=
  block [.addN 71 61 63, .subN 71 71 65, .loadN 66 71, .subN 71 71 65, .loadN 67 71,
    .addN 72 60 66, .loadN 72 72, .addN 73 60 67, .loadN 73 73, .addN 74 60 64, .loadN 74 74,
    .readX 61 73, .readY 62 73, .readX 63 72, .readY 64 72, .readX 65 74, .readY 66 74]

/-- The corner test: `subReadStmt`, `rreg 67 := det (vtx l[b]) (vtx l[c]) (vtx l[k])`,
`rreg 71 := rreg 70 * rreg 67`.  Exactly `25` instructions. -/
def subTestStmt : Stmt :=
  .seq subReadStmt (.seq ztkvt (.instr (.mulR 71 70 67)))

/-- A pop: `emit (l[b], l[c], l[k]); top := top - 1`. -/
def subPopStmt : Stmt := block [.emit 73 72 74, .subN 63 63 65]

/-- The body of the pop loop: `if top < 2 then flag := 0 else (test; if 0 < σ * D then pop
else flag := 0)`. -/
def subInnerBody : Stmt :=
  .ifLtN 63 68 ztouf
    (.seq subTestStmt (.ifLtR 72 71 subPopStmt ztouf))

/-- **The pop loop**: `while 0 < flag do subInnerBody`. -/
def subInnerLoop : Stmt := .whileLtN 70 69 subInnerBody

/-- The push: `nmem (sbase + top) := k; top := top + 1; k := k + 1`.  Exactly `4`
instructions. -/
def subPushStmt : Stmt := block [.addN 71 61 63, .storeN 71 64, .addN 63 63 65, .addN 64 64 65]

/-- The body of the walk: `flag := 1; subInnerLoop; subPushStmt`. -/
def subOuterBody : Stmt := .seq (.instr (.constN 69 1)) (.seq subInnerLoop subPushStmt)

/-- **The walk**: `while k < m do subOuterBody`. -/
def subOuterLoop : Stmt := .whileLtN 64 62 subOuterBody

/-- The initialisation: the constants `1, 2, 0`, the stack `[1, 0]` (`nmem sbase := 0`,
`nmem (sbase + 1) := 1`, `top := 2`), `k := 2`, the original indices `l[m-1], l[0], l[1]`
(into `nreg 72, 73, 74`) and their coordinates into `rreg 61 … rreg 66`, `rreg 72 := 0`.
Exactly `21` instructions. -/
def subInitBlock : Stmt :=
  block [.constN 65 1, .constN 68 2, .constN 70 0, .storeN 61 70, .addN 71 61 65, .storeN 71 65,
    .copyN 63 68, .copyN 64 68, .addN 72 60 62, .subN 72 72 65, .loadN 72 72, .loadN 73 60,
    .addN 74 60 65, .loadN 74 74, .readX 61 72, .readY 62 72, .readX 63 73, .readY 64 73,
    .readX 65 74, .readY 66 74, .constR 72 0]

/-- The sign: `rreg 67 := D₀ = det v_{l[m-1]} v_{l[0]} v_{l[1]};
rreg 70 := if 0 < D₀ then 1 else -1`. -/
def subSignStmt : Stmt :=
  .seq ztkvt
    (.ifLtR 72 67 (.instr (.constR 70 1)) (.instr (.constR 70 (-1))))

/-- **The monotone-mountain triangulator for a sub-polygon given by an index table.** -/
def mountainSubStmt : Stmt := .seq subInitBlock (.seq subSignStmt subOuterLoop)

/-! ### The corner test -/
section specs
variable {P : Polygon} {W : ℕ}
set_option linter.unusedSimpArgs false in
/-- **Spec lemma for `subTestStmt`.**  With `nreg 65 = 1` and the four addresses in range:
cost `≤ 25`; `nreg 72 = l[c]`, `nreg 73 = l[b]`, `nreg 74 = l[k]` read through the table at
`nreg 60` from the positions `c = nmem (sbase + top - 1)`, `b = nmem (sbase + top - 1 - 1)`;
`rreg 71 = rreg 70 * det (vtx l[b]) (vtx l[c]) (vtx l[k])`; natural registers other than
`66, 67, 71, 72, 73, 74`, real registers outside `61 … 69` other than `71`, both memories and
the output are unchanged. -/
theorem subTestStmt_exec (c : Config) (hc : WordsBounded W c) (h65 : c.nreg 65 = 1)
    (hs : c.nreg 61 + c.nreg 63 ≤ W)
    (hcb : c.nreg 60 + c.nmem zthge ≤ W)
    (hbb : c.nreg 60 + c.nmem ztfqg ≤ W)
    (hkb : c.nreg 60 + c.nreg 64 ≤ W) :
    ∃ c' k, Exec P W subTestStmt c c' k ∧ k ≤ 25 ∧
      c'.nreg 72 = c.nmem ztzdw ∧
      c'.nreg 73 = c.nmem ztzdv ∧
      c'.nreg 74 = c.nmem ztqhy ∧
      c'.rreg 71 = c.rreg 70 *
        det (P.vtx (c.nmem ztzdv))
          (P.vtx (c.nmem ztzdw))
          (P.vtx (c.nmem ztqhy)) ∧
      (∀ r, r ≠ 66 → r ≠ 67 → r ≠ 71 → r ≠ 72 → r ≠ 73 → r ≠ 74 → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 61 ∨ 69 < r) → r ≠ 71 → c'.rreg r = c.rreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold subTestStmt subReadStmt
  refine spec_seq ?_
  exec_block
  · zujux
  · config_simp; zuped; exact hcb
  · config_simp; zuped; exact hbb
  · config_simp; exact hkb
  refine spec_seq (spec_use (detInto_exec 67 68 69 61 62 63 64 65 66 by_decide
    by_decide by_decide
    by_omega _ ‹_›) ?_)
  zudfj
  refine spec_instr (Exec.mulR hw₁ 71 70 67) fun hw₂ => ?_
  config_simp at hdet
  have e70 : ztsgs := by
    rw [hfr 70 by_decide by_decide by_decide]; config_simp
  refine ⟨by_omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · config_simp; rw [hn]; config_simp; rw [h65]
  · config_simp; rw [hn]; config_simp; rw [h65]
  · config_simp; zvmxq; config_simp
  · config_simp; rw [hdet, e70, h65]
  · intro r h66 h67 h71 h72 h73 h74
    config_simp; zvmxq; simp [h66, h67, h71, h72, h73, h74]
  · intro r hr h71
    config_simp
    rw [Machine.upd_other _ _ _ h71, hfr r by_omega by_omega by_omega]
    simp [show r ≠ 61 by omega, show r ≠ 62 by omega, show r ≠ 63 by omega,
      show r ≠ 64 by omega, show r ≠ 65 by omega, show r ≠ 66 by omega]
  · config_simp; zupee
  · config_simp; zvnmc
  · config_simp; zuoze
end specs

/-! ### The pop loop -/

/-- The potential of the pop loop at position `k`: `0` once the flag is `0`, otherwise
`32 * (p + 1)` with `p` the number of pops still to come. -/
noncomputable def subInnerPot (P : Polygon) (l : List ℕ) (σ : ℝ) (k : ℕ) (c : Config) : ℕ :=
  if c.nreg 69 = 0 then 0 else 32 * ztwsu

/-- **The invariant of the pop loop** at position `k`, relative to the configuration `c₀` at
the start of the loop, with target output `oF` and target stack `sF`: the word bound, the
constants, the index table, the frame, `nreg 64 = k`, `top ≤ k`, stack entries `< m`, and
either the flag is `1`, the output followed by the (relabelled) triangles still to be emitted by
`popLoop (subPoly P l) σ k (stackS c)` is `oF`, and that call ends with the stack `sF`; or the
flag is `0`, the output is `oF` and the stack is `sF`. -/
def SInnerInv (P : Polygon) (W : ℕ) (l : List ℕ) (base sbase : ℕ) (σ : ℝ) (k : ℕ)
    (c₀ : Config) (oF : List Polygon.Triangle) (sF : List ℕ) (c : Config) : Prop :=
  WordsBounded W c ∧ SConsts base sbase l.length σ c ∧ STab l base c ∧ SFrame c₀ c ∧
    c.nreg 64 = k ∧ c.nreg 63 ≤ k ∧ ztluw ∧
    ((c.nreg 69 = 1 ∧
        c.output ++ (popLoop ztdi σ k ztxq).1.map ztbux = oF ∧
        (popLoop ztdi σ k ztxq).2.1 = sF) ∨
      (c.nreg 69 = 0 ∧ c.output = oF ∧ stackS c = sF))
section inner
variable {P : Polygon} {W : ℕ} {l : List ℕ} {base sbase : ℕ}
variable {σ : ℝ} {k : ℕ} {c₀ : Config} {oF : List Polygon.Triangle} {sF : List ℕ} {c c' : Config}
/-- **A pop re-establishes the invariant** and decreases the potential by `32`.  `c` is the
configuration at the start of the iteration (flag `1`, `2 ≤ top`, a convex corner of
`subPoly P l`), `c'` the one after the pop, described by the equations `e…`. -/
theorem sInnerInv_pop
 (hw' : WordsBounded W c')
    (hC' : SConsts base sbase l.length σ c') (hT' : STab l base c') (hF' : SFrame c₀ c')
    (h64 : c.nreg 64 = k) (htop : c.nreg 63 ≤ k) (hge : 2 ≤ c.nreg 63) (hf : c.nreg 69 = 1)
    (hlt : ∀ x ∈ stackS c, x < l.length)
    (hconv : 0 < σ * det ztyah
      ztyai ztejh)
    (hout : c.output ++ (popLoop ztdi σ k ztxq).1.map ztbux = oF)
    (hst : (popLoop ztdi σ k ztxq).2.1 = sF)
    (e61 : c'.nreg 61 = c.nreg 61) (e63 : c'.nreg 63 = c.nreg 63 - 1)
    (e64 : c'.nreg 64 = c.nreg 64) (e69 : c'.nreg 69 = 1) (enm : c'.nmem = c.nmem)
    (eout : c'.output = c.output ++ [relabelList l (c.nmem ztcmr,
      c.nmem ztdmq, k)]) :
    SInnerInv P W l base sbase σ k c₀ oF sF c' ∧
      subInnerPot P l σ k c' + 32 ≤ subInnerPot P l σ k c := by
  have hs : stackS c = c.nmem _ ::
      c.nmem _ :: stk ztqnw
        _ := stk_two hge
  have hs' : stackS c' = c.nmem ztcmr ::
      stk ztkwd ztrmh := by
    zumva
    rw [e61, e63, enm, stk_pop
      by_omega, show c.nreg 63 - 1 - 1 = c.nreg 63 - 2 by omega]
  have hpl : popLoop ztdi σ k ztxq =
      ((c.nmem ztcmr, c.nmem ztdmq, k) ::
          (popLoop ztdi σ k ztqwz).1,
        (popLoop ztdi σ k ztqwz).2.1,
        (popLoop ztdi σ k ztqwz).2.2 + 1) := by
    rw [hs, hs', popLoop_cons_cons, ite_eq_left hconv]
  refine ⟨⟨hw', hC', hT', hF', by zuoqc, by_omega, ?_, Or.inl ztrcg⟩, ?_⟩
  · zuh
    zukvx
    zubfo
  · rw [eout, List.append_assoc, List.singleton_append, ← hout, hpl, List.map_cons]
  · rw [← hst, hpl]
  · unfold subInnerPot
    rw [ite_eq_right by_omega, ite_eq_right by_omega, hpl, List.length_cons]
    omega

/-- **Stopping re-establishes the invariant** (flag `0`) when the pop loop emits nothing more
and keeps the stack. -/
theorem sInnerInv_stop
 (hw' : WordsBounded W c')
    (hC' : SConsts base sbase l.length σ c') (hT' : STab l base c') (hF' : SFrame c₀ c')
    (h64 : c.nreg 64 = k) (htop : c.nreg 63 ≤ k) (hlt : ∀ x ∈ stackS c, x < l.length)
    (hpl : (popLoop ztdi σ k ztxq).1 = [])
    (hpl2 : (popLoop ztdi σ k ztxq).2.1 = stackS c)
    (hout : c.output ++ (popLoop ztdi σ k ztxq).1.map ztbux = oF)
    (hst : (popLoop ztdi σ k ztxq).2.1 = sF)
    (e61 : c'.nreg 61 = c.nreg 61) (e63 : c'.nreg 63 = c.nreg 63)
    (e64 : c'.nreg 64 = c.nreg 64) (e69 : c'.nreg 69 = 0) (enm : c'.nmem = c.nmem)
    (eout : c'.output = c.output) :
    SInnerInv P W l base sbase σ k c₀ oF sF c' ∧ subInnerPot P l σ k c' = 0 := by
  have hs' := stackS_congr e61 e63 enm
  refine ⟨⟨hw', hC', hT', hF', by zuoqc, by_omega, by rw [hs']; exact hlt,
    Or.inr ztrcg⟩, ?_⟩
  · rw [eout, ← hout, hpl, List.map_nil, List.append_nil]
  · rw [hs', ← hst, hpl2]
  · unfold subInnerPot; rw [ite_eq_left e69]
set_option maxHeartbeats 800000 in
/-- **One iteration of the pop loop** preserves `SInnerInv` and decreases the potential
`subInnerPot` by at least its cost plus `2`. -/
theorem subInnerBody_inv (hL : SLayout W base sbase l.length) {σ : ℝ} {k : ℕ}
    (hk : k < l.length) {c₀ : Config} {oF : List Polygon.Triangle} {sF : List ℕ}
    (c : Config) (hI : SInnerInv P W l base sbase σ k c₀ oF sF c)
    (ht : c.nreg 70 < c.nreg 69) :
    ∃ c' k', Exec P W subInnerBody c c' k' ∧ SInnerInv P W l base sbase σ k c₀ oF sF c' ∧
      subInnerPot P l σ k c' + k' + 2 ≤ subInnerPot P l σ k c := by
  obtain ⟨-, hWb, hWs⟩ := hL
  obtain ⟨hw, hC, hT, hF, h64, htop, hlt, hflag⟩ := hI
  zucsq
  obtain ⟨hf, hout, hst⟩ : c.nreg 69 = 1 ∧
      c.output ++ (popLoop ztdi σ k ztxq).1.map ztbux = oF ∧
      (popLoop ztdi σ k ztxq).2.1 = sF := by
    rcases hflag with h | h
    · zubh
    · omega
  have hpot : subInnerPot P l σ k c =
      32 * ztwsu := by
    zuiqe
  unfold subInnerBody
  by_cases hlt2 : c.nreg 63 < 2
  · -- fewer than two entries: stop
    have hpl : popLoop ztdi σ k ztxq = ([], stackS c, 0) := by
      zumva
      obtain h | h : c.nreg 63 = 0 ∨ c.nreg 63 = 1 := by_omega
      · zvmwc; exact popLoop_nil _ σ k
      · zvmwc; exact popLoop_singleton _ σ k _
    refine spec_ifLtN_true ztmdk
      (spec_instr (Exec.constN hw 69 0 ztbg) fun hw' => ?_)
    obtain ⟨hI', hp'⟩ := sInnerInv_stop hw'
      ⟨by config_simp; exact h60, by config_simp; exact h61, by config_simp; exact h62,
        by config_simp; exact h65, by config_simp; exact h68, by config_simp; exact h70,
        by config_simp; exact hr70, by config_simp; exact hr72⟩
      hT (sFrame_trans hF (sFrame_of_regs
        (fun r hr => by config_simp; exact Machine.upd_other _ _ _ by_omega)
        by_simp_all rfl rfl))
      h64 htop hlt (by rw [hpl]) (by rw [hpl]) hout hst (by config_simp) (by config_simp)
      (by config_simp) (by config_simp) rfl rfl
    zugtb

    simp
  · have hge : 2 ≤ c.nreg 63 := by omega
    have hs : stackS c = c.nmem _ ::
        c.nmem _ :: stk ztqnw
          _ := stk_two hge
    have hcm : ztunj :=
      hlt _ (by zvmyz; exact List.mem_cons_self)
    have hbm : ztunj :=
      hlt _ (by zvmyz; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have ea1 : c.nreg 61 + c.nreg 63 - 1 = c.nreg 61 + (c.nreg 63 - 1) := by_omega
    have ea2 : c.nreg 61 + c.nreg 63 - 1 - 1 = c.nreg 61 + ztrmh := by_omega
    refine spec_ifLtN_false ztmdk ?_
    refine spec_seq (spec_use (subTestStmt_exec c hw h65 (by rw [h61]; omega)
      (by rw [ea1, h60]; omega) (by rw [ea2, h60]; omega) (by rw [h60, h64]; omega)) ?_)
    rintro c₁ k₁ hk₁ hw₁ ⟨e72, e73, e74, e71, efr, erf, enm, erm, eout⟩
    rw [ea2, h60, hT _ hbm] at e73
    rw [ea1, h60, hT _ hcm] at e72
    rw [h60, h64, hT _ hk] at e74
    rw [ea2, ea1, h60, hT _ hbm, hT _ hcm, h64, hT _ hk] at e71
    have n60 : c₁.nreg 60 = c.nreg 60 :=
      by grind
    have n61 : c₁.nreg 61 = c.nreg 61 :=
      by grind
    have n62 : c₁.nreg 62 = c.nreg 62 :=
      by grind
    have n63 : c₁.nreg 63 = c.nreg 63 :=
      by grind
    have n64 : c₁.nreg 64 = c.nreg 64 :=
      by grind
    have n65 : c₁.nreg 65 = c.nreg 65 :=
      by grind
    have n68 : c₁.nreg 68 = c.nreg 68 :=
      by grind
    have n69 : c₁.nreg 69 = c.nreg 69 :=
      by grind
    have n70 : c₁.nreg 70 = c.nreg 70 :=
      by grind
    have r70 : ztsgs := by_grind
    have r72 : ztsgt := by_grind
    have hF₁ := sFrame_of_regs
      by_grind
      by_grind enm erm
    by_cases hconv : 0 < σ * det ztyah
        ztyai ztejh
    · -- a convex corner: pop
      zumdd
      rw [vtx_subPoly_getD P l hbm, vtx_subPoly_getD P l hcm, vtx_subPoly_getD P l hk]
        at hconv'
      refine spec_ifLtR_true zthtq ?_
      unfold subPopStmt
      exec_block
      obtain ⟨hI', hp'⟩ := sInnerInv_pop by_omega
        ⟨by config_simp; zuoqd, by config_simp; zuoqe,
          by config_simp; zuoqf, by config_simp; zuoqg,
          by config_simp; zuoqh, by config_simp; zuoqi,
          by config_simp; zuoqj, by config_simp; zuoqk⟩
        (fun i hi => by config_simp; rw [enm]; exact hT i hi)
        (sFrame_trans hF (sFrame_trans hF₁ (sFrame_of_regs
          (fun r hr => by config_simp; exact Machine.upd_other _ _ _ by_omega)
          by_grind (by config_simp) (by config_simp))))
        h64 htop hge hf hlt hconv hout hst (by config_simp; rw [n61])
        (by config_simp; rw [n63, n65, h65]) (by config_simp; rw [n64])
        (by config_simp; rw [n69, hf]) (by config_simp; rw [enm])
        (by config_simp; rw [eout, e73, e72, e74]; rfl)
      zubfo
    · -- not convex: stop
      zumdd
      rw [vtx_subPoly_getD P l hbm, vtx_subPoly_getD P l hcm, vtx_subPoly_getD P l hk]
        at hconv'
      refine spec_ifLtR_false zthtq
        (spec_instr (Exec.constN hw₁ 69 0 ztbg) fun hw' => ?_)
      have hpl : popLoop ztdi σ k ztxq = ([], stackS c, 1) := by
        rw [hs, popLoop_cons_cons, ite_eq_right hconv]
      obtain ⟨hI', hp'⟩ := sInnerInv_stop hw'
        ⟨by config_simp; zuoqd, by config_simp; zuoqe,
          by config_simp; zuoqf, by config_simp; zuoqg,
          by config_simp; zuoqh, by config_simp; zuoqi,
          by config_simp; zuoqj, by config_simp; zuoqk⟩
        (fun i hi => by config_simp; rw [enm]; exact hT i hi)
        (sFrame_trans hF (sFrame_trans hF₁ (sFrame_of_regs
          (fun r hr => by config_simp; exact Machine.upd_other _ _ _ by_omega)
          by_grind rfl rfl)))
        h64 htop hlt (by rw [hpl]) (by rw [hpl]) hout hst (by config_simp; rw [n61])
        (by config_simp; rw [n63]) (by config_simp; rw [n64]) (by config_simp)
        (by config_simp; rw [enm]) (by config_simp; rw [eout])
      zugtb

      simp only [List.length_nil]
      omega

/-- **Spec lemma for the pop loop.**  From a configuration with the constants, the index table,
`nreg 64 = k < m`, `top ≤ k`, stack entries `< m` and flag `1`, the pop loop emits
`(popLoop (subPoly P l) σ k s).1.map (relabelList l)` (`s = stackS c`), leaves the stack
`(popLoop (subPoly P l) σ k s).2.1`, keeps the constants, the table, the frame, `nreg 64 = k`,
`top ≤ k` and the bound on the entries, and costs `≤ 32 * ((popLoop … s).1.length + 1) + 2`. -/
theorem subInnerLoop_exec (hL : SLayout W base sbase l.length) {σ : ℝ} {k : ℕ}
    (hk : k < l.length) (c : Config) (hw : WordsBounded W c)
    (hC : SConsts base sbase l.length σ c) (hT : STab l base c) (h64 : c.nreg 64 = k)
    (htop : c.nreg 63 ≤ k) (hlt : ∀ x ∈ stackS c, x < l.length) (hf : c.nreg 69 = 1) :
    ∃ c' k', Exec P W subInnerLoop c c' k' ∧
      k' ≤ 32 * ztwsu + 2 ∧
      SConsts base sbase l.length σ c' ∧ STab l base c' ∧ SFrame c c' ∧ c'.nreg 64 = k ∧
      c'.nreg 63 ≤ k ∧ (∀ x ∈ stackS c', x < l.length) ∧
      c'.output = c.output ++ (popLoop ztdi σ k ztxq).1.map ztbux ∧
      stackS c' = (popLoop ztdi σ k ztxq).2.1 := by
  have hI : SInnerInv P W l base sbase σ k c
      _
      (popLoop _ σ k _).2.1 c :=
    ⟨hw, hC, hT, sFrame_refl c, h64, htop, hlt, Or.inl ⟨hf, rfl, rfl⟩⟩
  obtain ⟨c', k', ex, hI', hexit, hk'⟩ := Exec.whileLtN_potential
    (SInnerInv P W l base sbase σ k c
      (c.output ++ (popLoop ztdi σ k ztxq).1.map ztbux)
      (popLoop ztdi σ k ztxq).2.1)
    (subInnerPot P l σ k) ztsa (fun d hd ht => subInnerBody_inv hL hk d hd ht) hI
  obtain ⟨-, hC', hT', hF', h64', htop', hlt', hflag'⟩ := hI'
  have hpot : subInnerPot P l σ k c =
      32 * ztwsu := by
    zuiqe
  rcases hflag' with ⟨hf', -, -⟩ | ⟨-, hout', hst'⟩
  · exfalso; apply hexit; rw [hf', hC'.2.2.2.2.2.1]; omega
  · exact ⟨c', k', ex, by rw [← hpot]; exact hk', hC', hT', hF', h64', htop', hlt', hout', hst'⟩
end inner
section walkLoop
variable {P : Polygon} {W : ℕ}

/-! ### The walk -/
end walkLoop

/-! ### Initialisation and the sign -/

/-- The sign computed by the program: `1` if `0 < det v_{n-1} v₀ v₁`, else `-1`. -/
noncomputable def mountainSign (P : Polygon) : ℝ :=
  if 0 < det ztwjc ztdt ztgk then 1 else -1

/-- **The computed sign is a valid orientation sign for a mountain**: `σ = ±1` and
`0 < σ * det v_{n-1} v₀ v₁` (the determinant is nonzero by `mountain_orient_det`). -/
theorem mountainSign_spec (P : Polygon) (hM : IsMountain P) :
    (mountainSign P = 1 ∨ mountainSign P = -1) ∧
      0 < mountainSign P * det ztwjc ztdt ztgk := by
  zujxw
  have hne : ztbamp := by
    intro h0; simp_all
  unfold mountainSign
  split_ifs with hpos
  · simp_all
  grind
section init
variable {P : Polygon} {W : ℕ}
end init

/-! ### The whole program -/
section main
variable {P : Polygon} {W : ℕ}
end main
open Chazelle.EarClip (subPoly_range getD_range)
open Chazelle.Existence (WeakTriangulates triangulates_of_weak)
noncomputable def subOuterPot (P : Polygon) (l : List ℕ) (σ : ℝ) (c : Config) : ℕ :=
  32 * (walk ztdi σ ztdzn ztxq).1.length + 41 * (l.length - c.nreg 64)

/-- **The invariant of the walk**, relative to the configuration `c₀` at the start of the loop
and the final output `out`: the word bound, the constants, the index table, the frame,
`top ≤ k`, stack entries `< m`, and the output followed by the (relabelled) triangles still to be
emitted by `walk (subPoly P l) σ k (stackS c)` is `out`. -/
def SOuterInv (P : Polygon) (W : ℕ) (l : List ℕ) (base sbase : ℕ) (σ : ℝ) (c₀ : Config)
    (out : List Polygon.Triangle) (c : Config) : Prop :=
  WordsBounded W c ∧ SConsts base sbase l.length σ c ∧ STab l base c ∧ SFrame c₀ c ∧
    c.nreg 63 ≤ c.nreg 64 ∧ ztluw ∧
    c.output ++ (walk ztdi σ ztdzn ztxq).1.map ztbux = out
section walkLoop
variable {P : Polygon} {W : ℕ} {l : List ℕ} {base sbase : ℕ}

/-- **The push re-establishes the invariant of the walk.**  `c` is the configuration at the
start of the iteration (`k = nreg 64 < m`), `c₂` the one after the pop loop, `c'` the one
after the push, described by the equations `e…`. -/
theorem sOuterInv_push {σ : ℝ} {c₀ : Config} {out : List Polygon.Triangle} {c c₂ c' : Config}
    (hw' : WordsBounded W c') (hC' : SConsts base sbase l.length σ c') (hT' : STab l base c')
    (hF' : SFrame c₀ c') (hk : c.nreg 64 < l.length) (htop₂ : c₂.nreg 63 ≤ c.nreg 64)
    (hlt₂ : ∀ x ∈ stackS c₂, x < l.length)
    (hout : c.output ++ (walk ztdi σ ztdzn ztxq).1.map ztbux =
      out)
    (hout₂ : c₂.output = c.output ++
      (popLoop ztdi σ ztdzn ztxq).1.map ztbux)
    (hst₂ : stackS c₂ = (popLoop ztdi σ ztdzn ztxq).2.1)
    (e61 : c'.nreg 61 = c₂.nreg 61) (e63 : c'.nreg 63 = c₂.nreg 63 + 1)
    (e64 : c'.nreg 64 = c.nreg 64 + 1)
    (enm : c'.nmem = upd c₂.nmem ztjtd ztdzn)
    (eout : c'.output = c₂.output) :
    SOuterInv P W l base sbase σ c₀ out c' ∧
      subOuterPot P l σ c' + 32 * (popLoop ztdi σ ztdzn ztxq).1.length +
        41 ≤ subOuterPot P l σ c := by
  have hs' : stackS c' = c.nreg 64 :: (popLoop ztdi σ ztdzn ztxq).2.1 := by
    zumva
    rw [e61, e63, enm, stk_shift_push]
    exact congrArg _ hst₂
  have hkQ : c.nreg 64 < (subPoly P l).n := by zvnnk; exact hk
  have hwalk := walk_of_lt _ σ hkQ ztxq
  refine ⟨⟨hw', hC', hT', hF', by_omega, ?_, ?_⟩, ?_⟩
  · zuh
    zukvx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hk
    · zufeo
  · rw [e64, hs', eout, hout₂, List.append_assoc, ← List.map_append, ← hout, hwalk]
  · unfold subOuterPot
    rw [e64, hs', hwalk, List.length_append]
    omega
set_option maxHeartbeats 800000 in
/-- **One iteration of the walk** (`k < m`) preserves `SOuterInv` and decreases the potential
`subOuterPot` by at least its cost plus `2`. -/
theorem subOuterBody_inv (hL : SLayout W base sbase l.length) {σ : ℝ} {c₀ : Config}
    {out : List Polygon.Triangle} (c : Config) (hI : SOuterInv P W l base sbase σ c₀ out c)
    (ht : c.nreg 64 < c.nreg 62) :
    ∃ c' k', Exec P W subOuterBody c c' k' ∧ SOuterInv P W l base sbase σ c₀ out c' ∧
      subOuterPot P l σ c' + k' + 2 ≤ subOuterPot P l σ c := by
  zumbx
  zugpk
  obtain ⟨hw, hC, hT, hF, htop, hlt, hout⟩ := hI
  zucsq
  have hk : c.nreg 64 < l.length := by rw [h62] at ht; exact ht
  unfold subOuterBody
  refine spec_seq (spec_instr (Exec.constN hw 69 1 by_omega) fun hw₁ => ?_)
  have hs₁ : stackS { c with nreg := upd c.nreg 69 1 } = stackS c :=
    stackS_congr (by config_simp) (by config_simp) rfl
  have hF₁ : SFrame c { c with nreg := upd c.nreg 69 1 } := sFrame_of_regs
    (fun r hr => by config_simp; exact Machine.upd_other _ _ _ by_omega) by_simp_all rfl rfl
  refine spec_seq (spec_use (subInnerLoop_exec hL' hk _ hw₁
    ⟨by config_simp; exact h60, by config_simp; exact h61, by config_simp; exact h62,
      by config_simp; exact h65, by config_simp; exact h68, by config_simp; exact h70,
      by config_simp; exact hr70, by config_simp; exact hr72⟩
    hT (by config_simp) (by config_simp; exact htop) (by rw [hs₁]; exact hlt)
    (by config_simp)) ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨hC₂, hT₂, hF₂, h64₂, htop₂, hlt₂, hout₂, hst₂⟩
  rw [hs₁] at hk₂ hout₂ hst₂
  config_simp at hout₂
  obtain ⟨g60, g61, g62, g65, g68, g70, gr70, gr72⟩ := hC₂
  unfold subPushStmt
  exec_block
  · -- `addN 71 61 63`: `sbase + top ≤ W`
    zuozj; omega
  · -- `addN 63 63 65`: `top + 1 ≤ W`
    config_simp; zupef; omega
  · -- `addN 64 64 65`: `k + 1 ≤ W`
    config_simp; zuoql; omega
  · have hF₃ : SFrame c₂ { c₂ with
        nreg := upd (upd (upd c₂.nreg 71 ztjtd) 63 (c₂.nreg 63 + c₂.nreg 65))
          64 (c₂.nreg 64 + c₂.nreg 65),
        nmem := upd c₂.nmem ztjtd (c₂.nreg 64) } := by
      refine ⟨fun r hr => ?_, by_simp_all, fun a ha => ?_, rfl⟩
      · have h1 : r ≠ 71 := by_omega
        have h2 : ztslm := by_omega
        have h3 : ztsln := by_omega
        zubmk
      · config_simp
        exact Machine.upd_other _ _ _ by_omega
    obtain ⟨hI', hp'⟩ := sOuterInv_push by_omega
      ⟨by config_simp; exact g60, by config_simp; exact g61, by config_simp; exact g62,
        by config_simp; exact g65, by config_simp; exact g68, by config_simp; exact g70,
        by config_simp; exact gr70, by config_simp; exact gr72⟩
      (fun i hi => by
        config_simp
        rw [Machine.upd_other _ _ _ (by rw [g61]; omega)]
        exact hT₂ i hi)
      (sFrame_trans hF (sFrame_trans hF₁ zttzu))
      hk htop₂ hlt₂ hout hout₂ hst₂ (by config_simp)
      (by config_simp; zupef) (by config_simp; zuoql) (by config_simp; rw [h64₂])
      (by config_simp)
    zubfo

/-- **Spec lemma for the walk.**  From a configuration with the constants, the index table,
`top ≤ k` (`k = nreg 64`) and stack entries `< m`, the walk appends
`(walk (subPoly P l) σ k (stackS c)).1.map (relabelList l)` to the output, keeps the constants,
the table and the frame, and costs
`≤ subOuterPot P l σ c + 2 = 32 * (walk … ).1.length + 41 * (m - k) + 2`. -/
theorem subOuterLoop_exec (hL : SLayout W base sbase l.length) {σ : ℝ} (c : Config)
    (hw : WordsBounded W c) (hC : SConsts base sbase l.length σ c) (hT : STab l base c)
    (htop : c.nreg 63 ≤ c.nreg 64) (hlt : ∀ x ∈ stackS c, x < l.length) :
    ∃ c' k', Exec P W subOuterLoop c c' k' ∧ k' ≤ subOuterPot P l σ c + 2 ∧
      c'.output = c.output ++
        (walk ztdi σ ztdzn ztxq).1.map ztbux ∧
      SConsts base sbase l.length σ c' ∧ STab l base c' ∧ SFrame c c' := by
  obtain ⟨c', k', ex, ⟨-, hC', hT', hF', -, -, hout'⟩, hexit, hk⟩ := Exec.whileLtN_potential
    (SOuterInv P W l base sbase σ c
      (c.output ++ (walk ztdi σ ztdzn ztxq).1.map ztbux))
    (subOuterPot P l σ) ztsa (fun d hd ht => subOuterBody_inv hL d hd ht)
    ⟨hw, hC, hT, sFrame_refl c, htop, hlt, rfl⟩
  have hkn : (subPoly P l).n ≤ c'.nreg 64 := by rw [n_subPoly, ← hC'.2.2.1]; omega
  rw [walk_of_le _ σ hkn, List.map_nil, List.append_nil] at hout'
  exact ⟨c', k', ex, hk, hout', hC', hT', hF'⟩
end walkLoop

/-! ### Initialisation and the sign -/
section init
variable {P : Polygon} {W : ℕ} {l : List ℕ}
set_option maxHeartbeats 800000 in
/-- **Spec lemma for `subInitBlock`.**  With `3 ≤ m`, the layout hypothesis and the index
table: cost `≤ 21` (exactly `21`); `top = 2`, `k = 2`, the constants `nreg 65 = 1`,
`nreg 68 = 2`, `nreg 70 = 0`, the inputs `nreg 60, 61, 62` kept, the stack `[1, 0]`, the table
kept, the frame, the coordinates of `v_{l[m-1]}, v_{l[0]}, v_{l[1]}` in `rreg 61 … rreg 66`,
`rreg 72 = 0`, and the output unchanged. -/
theorem subInitBlock_exec (h3 : 3 ≤ l.length) (c : Config) (hc : WordsBounded W c)
    (hL : SLayout W zthuv ztvil l.length) (h62 : c.nreg 62 = l.length)
    (hT : STab l zthuv c) :
    ∃ c' k, Exec P W subInitBlock c c' k ∧ k ≤ 21 ∧
      c'.nreg 60 = c.nreg 60 ∧ c'.nreg 61 = c.nreg 61 ∧ c'.nreg 62 = l.length ∧
      c'.nreg 63 = 2 ∧ c'.nreg 64 = 2 ∧ c'.nreg 65 = 1 ∧ c'.nreg 68 = 2 ∧ c'.nreg 70 = 0 ∧
      stackS c' = [1, 0] ∧ STab l zthuv c' ∧ SFrame c c' ∧
      c'.rreg 61 = (P.vtx ztzwv).1 ∧
      c'.rreg 62 = (P.vtx ztzwv).2 ∧
      c'.rreg 63 = (P.vtx zttrm).1 ∧ c'.rreg 64 = (P.vtx zttrm).2 ∧
      c'.rreg 65 = (P.vtx zttrn).1 ∧ c'.rreg 66 = (P.vtx zttrn).2 ∧
      c'.rreg 72 = 0 ∧ c'.output = c.output := by
  zugpk
  have hg : ∀ i, i < l.length →
      upd zthkt ztlkx 1 ztlkw = l.getD i 0 := by
    zug
    rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega, hT i hi]
  have gA : upd zthkt ztlkx 1 (c.nreg 60 + c.nreg 62 - 1) =
      l.getD ztetw 0 := by
    rw [show c.nreg 60 + c.nreg 62 - 1 = c.nreg 60 + ztetw by omega]
    zubfo
  have gB : upd zthkt ztlkx 1 zthuv = l.getD 0 0 := by
    have := hg 0 by_omega
    rwa [Nat.add_zero] at this
  have gC : upd _ _ 1 _ = l.getD 1 0 :=
    hg 1 by_omega
  unfold subInitBlock
  exec_block
  · omega
  · omega
  · omega
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · refine ⟨by_omega, by config_simp, by config_simp, by config_simp; exact h62, by config_simp,
      by config_simp, by config_simp, by config_simp, by config_simp, ?_,
      fun i hi => by config_simp; exact hg i hi, ?_, by config_simp; zupeg,
      by config_simp; zupeg, by config_simp; zupeh, by config_simp; zupeh,
      by config_simp; zupei, by config_simp; zupei, by config_simp; norm_num, rfl⟩
    · zumva
      config_simp
      simp [stk, upd]
    · refine ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_, rfl⟩
      · zucrr

        have h68 : r ≠ 68 := by_omega
        have h70 : r ≠ 70 := by_omega
        have h71 : r ≠ 71 := by_omega
        zuhwe
        have h73 : r ≠ 73 := by_omega
        have h74 : r ≠ 74 := by_omega
        simp [h63, h64, h65, h68, h70, h71, h72, h73, h74]
      · have h61 : r ≠ 61 := by_omega
        have h62 : r ≠ 62 := by_omega
        zucrr

        have h66 : r ≠ 66 := by_omega
        zuhwe
        simp [h61, h62, h63, h64, h65, h66, h72]
      · config_simp
        zucw
set_option linter.unusedSimpArgs false in
/-- **Spec lemma for `subSignStmt`.**  With `rreg 72 = 0`: cost `≤ 10`;
`rreg 70 = if 0 < det (rreg 61, rreg 62) (rreg 63, rreg 64) (rreg 65, rreg 66) then 1 else -1`;
real registers outside `61 … 72` and `rreg 72`, the natural registers, both memories and the
output are unchanged. -/
theorem subSignStmt_exec (c : Config) (hc : WordsBounded W c) (h72 : c.rreg 72 = 0) :
    ∃ c' k, Exec P W subSignStmt c c' k ∧ k ≤ 10 ∧
      c'.rreg 70 = (if 0 < det ztqjd ztqje ztqjf
        then 1 else -1) ∧
      c'.rreg 72 = c.rreg 72 ∧ ztbos ∧
      c'.nreg = c.nreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold subSignStmt
  refine spec_seq (spec_use (detInto_exec 67 68 69 61 62 63 64 65 66 by_decide
    by_decide by_decide
    by_omega c hc) ?_)
  zudfj
  have e72 : ztsgt := by_simp_all
  by_cases hpos : 0 < det ztqjd ztqje ztqjf
  · refine spec_ifLtR_true ztirm
      (spec_instr (Exec.constR hw₁ 70 1) fun hw₂ => ?_)
    refine ⟨by_omega, ?_, by config_simp; exact e72, fun r hr => ?_, by config_simp; exact hn,
      by config_simp; exact hnm, by config_simp; exact hrm, by config_simp; exact hout⟩
    · config_simp
      zulpz
      norm_num
    · config_simp
      zubc
      zubfo
  · refine spec_ifLtR_false ztirm
      (spec_instr (Exec.constR hw₁ 70 _) fun hw₂ => ?_)
    refine ⟨by_omega, ?_, by config_simp; exact e72, fun r hr => ?_, by config_simp; exact hn,
      by config_simp; exact hnm, by config_simp; exact hrm, by config_simp; exact hout⟩
    · config_simp
      zulqi
      norm_num
    · config_simp
      zubc
      zubfo
end init

/-! ### The whole fragment -/
section main
variable {P : Polygon} {W : ℕ} {l : List ℕ}

/-- **Spec lemma for `mountainSubStmt`, with the computed sign.**  For `3 ≤ m`, the layout
hypothesis, `nreg 62 = m` and the index table at `nreg 60`: the fragment appends
`(mountainTriangulation (subPoly P l) (mountainSign (subPoly P l))).map (relabelList l)` to the
output, keeps the frame, and costs
`≤ 32 * (mountainTriangulation …).length + 41 * (m - 2) + 33`. -/
theorem mountainSubStmt_exec_sign (h3 : 3 ≤ l.length) (c : Config) (hc : WordsBounded W c)
    (hL : SLayout W zthuv ztvil l.length) (h62 : c.nreg 62 = l.length)
    (hT : STab l zthuv c) :
    ∃ c' k, Exec P W mountainSubStmt c c' k ∧
      k ≤ 32 * (mountainTriangulation ztdi ztbaij).length +
        41 * ztocp + 33 ∧
      c'.output = c.output ++
        (mountainTriangulation ztdi ztbaij).map ztbux ∧
      SFrame c c' := by
  unfold mountainSubStmt
  refine spec_seq (spec_use (subInitBlock_exec h3 c hc hL h62 hT) ?_)
  rintro c₁ k₁ hk₁ hw₁
    ⟨n60, n61, n62, n63, n64, n65, n68, n70, hs₁, hT₁, hF₁, r1, r2, r3, r4, r5, r6, r72, hout₁⟩
  refine spec_seq (spec_use (subSignStmt_exec c₁ hw₁ r72) ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨e70, e72, erf, hn, hnm, hrm, hout₂⟩
  have hsig : c₂.rreg 70 = mountainSign ztdi := by
    rw [e70, r1, r2, r3, r4, r5, r6]
    unfold mountainSign
    rw [n_subPoly, vtx_subPoly_getD P l by_omega, vtx_subPoly_getD P l by_omega,
      vtx_subPoly_getD P l by_omega]
  have hC : SConsts _ _ l.length _ c₂ :=
    ⟨by rw [hn, n60], by rw [hn, n61], by rw [hn, n62], by rw [hn, n65], by rw [hn, n68],
      by rw [hn, n70], hsig, by rw [e72, r72]⟩
  have hs₂ : stackS c₂ = [1, 0] := by
    rw [stackS_congr ztqfb ztqfb hnm]; exact hs₁
  have h64 : c₂.nreg 64 = 2 := by rw [hn, n64]
  have hF₂ := sFrame_of_regs by_grind erf hnm hrm
  refine spec_use (subOuterLoop_exec hL c₂ hw₂ hC
    (fun i hi => by zupee; exact hT₁ i hi) (by rw [hn, n63, n64])
    (by rw [hs₂]; intro x hx; simp at hx; omega)) ?_
  rintro c₃ k₃ hk₃ hw₃ ⟨hout₃, -, -, hF₃⟩
  unfold subOuterPot at hk₃
  rw [h64, hs₂] at hk₃
  refine ⟨?_, ?_, sFrame_trans hF₁ zttzu⟩
  · unfold mountainTriangulation; omega
  · rw [hout₃, h64, hs₂, hout₂, hout₁]; rfl

/-- **Spec lemma for `mountainSubStmt`** on a monotone mountain `Q = subPoly P l` whose index
table `nmem (base + i) = l[i]` (`i < m = l.length`) sits at `base = nreg 60`, with `m` in
`nreg 62`, the stack region at `sbase = nreg 61`, the two regions disjoint and every address
`≤ W`.  The fragment appends `(mountainTriangulation Q σ).map (relabelList l)` (triangles in
original indices) to the output, for a sign `σ = ±1` with `0 < σ * det v_{m-1} v₀ v₁` (vertices
of `Q`, so that `mountain_triangulates_of_sign` applies), at cost `≤ 73 * m`.  **Frame:** natural
registers outside `63 … 74` (in particular the inputs `60, 61, 62`), real registers outside
`61 … 72`, natural memory outside the stack region (in particular the index table) and the real
memory are unchanged. -/
theorem mountainSub_exec (hM : IsMountain ztdi) (c : Config) (hc : WordsBounded W c)
    (htab : ∀ i, i < l.length → c.nmem ztlkw = l.getD i 0)
    (hm : c.nreg 62 = l.length)
    (hdisj : c.nreg 60 + l.length ≤ c.nreg 61 ∨ c.nreg 61 + l.length ≤ c.nreg 60)
    (hWb : c.nreg 60 + l.length ≤ W) (hWs : c.nreg 61 + l.length ≤ W) :
    ∃ c' k σ, Exec P W mountainSubStmt c c' k ∧ ztdd ∧
      0 < σ * det ((subPoly P l).vtx ((subPoly P l).n - 1)) ((subPoly P l).vtx 0)
        ((subPoly P l).vtx 1) ∧
      k ≤ 73 * l.length ∧
      c'.output = c.output ++ (mountainTriangulation ztdi σ).map ztbux ∧
      ztybu ∧
      ztbos ∧
      ztezz ∧
      c'.rmem = c.rmem := by
  have h3 : 3 ≤ l.length := by have := hM.1.1; zvnnk at this; exact this
  obtain ⟨hσ, hpos⟩ := mountainSign_spec _ hM
  obtain ⟨c', k, ex, hk, hout, hF⟩ :=
    mountainSubStmt_exec_sign (P := P) h3 c hc ⟨hdisj, hWb, hWs⟩ hm htab
  have hlen := (mountain_triangulates_of_sign _ hM hσ hpos).1.2.1
  zukxw
  obtain ⟨hn, hr, hnm, hrm⟩ := hF
  refine ⟨c', k, mountainSign _, ex, hσ, hpos, by_omega, hout, hn, hr,
    by simp_all, hrm⟩
end main

/-! ### The composable form -/

/-- **The stack walk with a valid sign weakly triangulates a mountain**: for a mountain `Q` and
`σ = ±1` with `0 < σ * det v_{n-1} v₀ v₁`, `mountainTriangulation Q σ` is a weak triangulation
of `Q`. -/
theorem weakTriangulates_mountainTriangulation_of_sign {Q : Polygon} (hM : IsMountain Q)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hpos : 0 < σ * det ztxvv ztccl ztqbq) :
    WeakTriangulates Q (mountainTriangulation Q σ) := by
  have hor : σ = orient Q := by
    have h := mountain_orient_det Q hM
    rcases sign_eq_or_eq_neg hσ ztkbs with h' | h'
    · zuclh
    · zuguj
  exact mountain_weakTriangulates Q hM hor

/-- **Spec lemma for `mountainSubStmt`, composable form**: under the hypotheses of
`mountainSub_exec`, the fragment appends `T.map (relabelList l)` to the output for a weak
triangulation `T` of `subPoly P l`, at cost `≤ 73 * m`, with the same frame. -/
theorem mountainSub_exec_weak {P : Polygon} {W : ℕ} {l : List ℕ} (hM : IsMountain ztdi)
    (c : Config) (hc : WordsBounded W c)
    (htab : ∀ i, i < l.length → c.nmem ztlkw = l.getD i 0)
    (hm : c.nreg 62 = l.length)
    (hdisj : c.nreg 60 + l.length ≤ c.nreg 61 ∨ c.nreg 61 + l.length ≤ c.nreg 60)
    (hWb : c.nreg 60 + l.length ≤ W) (hWs : c.nreg 61 + l.length ≤ W) :
    ∃ c' k T, Exec P W mountainSubStmt c c' k ∧ k ≤ 73 * l.length ∧
      WeakTriangulates ztdi T ∧ c'.output = c.output ++ T.map ztbux ∧
      ztybu ∧
      ztbos ∧
      ztezz ∧
      c'.rmem = c.rmem := by
  obtain ⟨c', k, σ, ex, hσ, hpos, hk, hout, hn, hr, hnm, hrm⟩ :=
    mountainSub_exec hM c hc htab hm hdisj hWb hWs
  exact ⟨c', k, _, ex, hk, weakTriangulates_mountainTriangulation_of_sign hM hσ hpos, hout, hn,
    hr, hnm, hrm⟩

/-! ### A complete program for the special case `l = List.range n`

`mountainRangeStmt` builds the identity table `nmem i = i` (`i < n`) at `base = 0`, puts the
stack region at `sbase = n`, and runs `mountainSubStmt`: it recovers the plain triangulator
`mountainProgram_triangulates` through the relocatable fragment (constants `2 * (n + 1)` for the
word bound, `80 * (n + 1)` for the steps). -/
section rangeProgram
variable {P : Polygon} {W : ℕ}
end rangeProgram
end
end Chazelle.Mountain
section
set_option hygiene false
local macro "zqbhb" : tactic => `(tactic| (have hTy := hT.topVtx_snd hP hq
                                           have hBy := hT.botVtx_snd hP hq
                                           obtain ⟨-, -, hTi, hTj⟩ := hT.topVtx_mem hP hq
                                           obtain ⟨-, -, hBi, hBj⟩ := hT.botVtx_mem hP hq
                                           have h12 := hT.bot_lt.trans hT.lt_top))
local macro "zqbhc" : tactic => `(tactic| (rintro ⟨hT1, hB1⟩
                                           have ht := hT.topVtx_lt hP hq
                                           zukbd
                                           have hTy := hT.topVtx_snd hP hq
                                           have hBy := hT.botVtx_snd hP hq
                                           have h12 := (hT.bot_lt.trans hT.lt_top).le))
local macro "zqbhd" : tactic => `(tactic| rw [edgeX_lerp_snd, lerp_fst, hTy, hBy])
local macro "zqbhe" : tactic => `(tactic| (rw [lerp_snd, hTy, hBy]; nlinarith))
local macro "zqbhf" : tactic => `(tactic| (by_contra hlt
                                           rw [not_le] at hlt))
local macro "zqbhg" : tactic => `(tactic| rw [hy, edgeX_combo P i by_ring, edgeX_combo P j by_ring])
local macro "zqbhh" : tactic => `(tactic| exact hne ((simple_vtx_inj hP ht hsucc e1).trans (simple_vtx_inj hP hb hsucc e2).symm))
local macro "zqbhi" : tactic => `(tactic| (intro y hy
                                           by_contra hlt
                                           rw [mem_ofPred_eq, not_le] at hlt
                                           have hij := hT.edgeX_lt hP hq hy.1 hy.2))
set_option hygiene true

/-!
# The top and bottom vertices of a trapezoid, and its diagonal

Let `hT : IsTrap P q i j y₁ y₂` be the trapezoid data of a free point `q` of a simple polygon
`P` (`Chazelle.Visibility.Trapezoid`).  The closed top side of the trapezoid is the horizontal
segment `[edgeX P i y₂, edgeX P j y₂] × {y₂}`, the closed bottom side is
`[edgeX P i y₁, edgeX P j y₁] × {y₁}`; each carries at least one vertex of `P`
(`IsTrap.top_vertex`, `IsTrap.bot_vertex`, once `edgeX_le_top`/`edgeX_le_bot` show that the
sides are not reversed).

## Tie-break conventions

* `ylexLT p q := p.2 < q.2 ∨ (p.2 = q.2 ∧ p.1 < q.1)` is the `(y, x)`-lexicographic order.
* `sideVtxSet P i j y` is the set of vertex indices at height `y` on the closed segment between
  the two side lines.
* The **top vertex** `topVtx P i j y₂` is the `ylexLT`-*minimal* (= leftmost) vertex of
  `sideVtxSet P i j y₂`; the **bottom vertex** `botVtx P i j y₁` is the `ylexLT`-*maximal*
  (= rightmost) vertex of `sideVtxSet P i j y₁`.  (These are the vertices found by a downward,
  respectively upward, sweep in the `ylexLT`-perturbed picture: the middle slab of the
  perturbed trapezoid has exactly these two as its top and bottom vertices.)
  Both are defined for all `P i j y` through `Classical.epsilon`; the specification lemmas need
  the trapezoid data (`IsTrap.topVtx_mem`, `IsTrap.botVtx_mem`, …).

## Main results

* `IsTrap.edgeX_le_top`, `IsTrap.edgeX_le_bot`: the side lines do not cross inside the
  trapezoid's height range, so `edgeX P i y₂ ≤ edgeX P j y₂` and `edgeX P i y₁ ≤ edgeX P j y₁`;
  `IsTrap.edgeX_lt`: strictly between the heights the order is strict.
* `IsTrap.topVtx_ne_botVtx`: the two vertices differ.
* `IsTrap.diag_lerp_mem_closedTrap`: the segment between them lies in the closed trapezoid;
  `IsTrap.diag_lerp_mem_trapSet`: if they are **not adjacent** in `P`, the open segment lies
  in the open trapezoid, hence (`IsTrap.exists_isDiagonal`) it is an interior diagonal in the
  sense of `Chazelle.Existence.IsDiagonal`, with the closed segment inside `P.filled`.
* `IsTrap.top_eq_side_of_adjacent`, `IsTrap.bot_eq_side_of_adjacent`: if they are adjacent,
  the edge joining them is the left or the right side edge `i` or `j`.
* `IsTrap.vtx_mem_closedTrap_iff`: every vertex of `P` in the closed trapezoid lies on the
  closed top or bottom side.
* `IsTrap.topVtx_eq_of_trapSet_eq`: the top and bottom vertices depend only on the region
  (open trapezoid), not on the particular data `q i j y₁ y₂` describing it.
-/
namespace Chazelle.Mountain
@[expose] public section
open Set Filter Topology
open Chazelle.Jordan
open Chazelle.Visibility
open Chazelle.Existence (IsDiagonal eq_endpoint_of_vtx_mem_edge vtx_mem_boundary)
open Chazelle.Geometry (lerp lerp_fst lerp_snd lerp_zero lerp_one point_ext point_ext_iff
  lerp_mem_segment)

/-! ### The `(y, x)`-lexicographic order -/

/-! ### Vertices on a horizontal side -/

/-- The vertices of `P` at height `y` on the closed horizontal segment between the line of
edge `i` and the line of edge `j`. -/
def sideVtxSet (P : Polygon) (i j : ℕ) (y : ℝ) : Set ℕ :=
  {k | k < P.n ∧ (P.vtx k).2 = y ∧ edgeX P i y ≤ (P.vtx k).1 ∧ (P.vtx k).1 ≤ edgeX P j y}
theorem sideVtxSet_finite (P : Polygon) (i j : ℕ) (y : ℝ) : (sideVtxSet P i j y).Finite :=
  (Set.finite_lt_nat P.n).subset fun _ hk => hk.1

/-- The vertex of smallest abscissa in a set of indices (`0` if the set is empty or infinite). -/
noncomputable def leftmostVtx (P : Polygon) (S : Set ℕ) : ℕ :=
  Classical.epsilon fun k => k ∈ S ∧ ∀ k' ∈ S, (P.vtx k).1 ≤ (P.vtx k').1

/-- The vertex of largest abscissa in a set of indices (`0` if the set is empty or infinite). -/
noncomputable def rightmostVtx (P : Polygon) (S : Set ℕ) : ℕ :=
  Classical.epsilon fun k => k ∈ S ∧ ∀ k' ∈ S, (P.vtx k').1 ≤ (P.vtx k).1
theorem leftmostVtx_spec (P : Polygon) {S : Set ℕ} (hfin : S.Finite) (hne : S.Nonempty) :
    leftmostVtx P S ∈ S ∧ ∀ k' ∈ S, (P.vtx (leftmostVtx P S)).1 ≤ (P.vtx k').1 :=
  Classical.epsilon_spec (p := fun k => k ∈ S ∧ ∀ k' ∈ S, (P.vtx k).1 ≤ (P.vtx k').1)
    (by
      obtain ⟨a, ha, h⟩ := Set.exists_min_image S ztmju hfin hne
      grind)
theorem rightmostVtx_spec (P : Polygon) {S : Set ℕ} (hfin : S.Finite) (hne : S.Nonempty) :
    rightmostVtx P S ∈ S ∧ ∀ k' ∈ S, (P.vtx k').1 ≤ (P.vtx (rightmostVtx P S)).1 :=
  Classical.epsilon_spec (p := fun k => k ∈ S ∧ ∀ k' ∈ S, (P.vtx k').1 ≤ (P.vtx k).1)
    (by
      obtain ⟨a, ha, h⟩ := Set.exists_max_image S ztmju hfin hne
      grind)

/-- **The top vertex** of the trapezoid with side edges `i`, `j` and top height `y`: the
leftmost (= `ylexLT`-minimal) vertex of the closed top side. -/
noncomputable def topVtx (P : Polygon) (i j : ℕ) (y : ℝ) : ℕ := leftmostVtx P ztqwi

/-- **The bottom vertex** of the trapezoid with side edges `i`, `j` and bottom height `y`: the
rightmost (= `ylexLT`-maximal) vertex of the closed bottom side. -/
noncomputable def botVtx (P : Polygon) (i j : ℕ) (y : ℝ) : ℕ := rightmostVtx P ztqwi

/-! ### Affine bookkeeping -/

/-- The abscissa of the line of edge `i` at the height of a point of the segment `a b`. -/
theorem edgeX_lerp_snd (P : Polygon) (i : ℕ) (a b : Point) (s : ℝ) :
    edgeX P i (lerp a b s).2 = zteb * edgeX P i a.2 + s * edgeX P i b.2 := by
  rw [← edgeX_combo P i by_simp_all]
  zucr
  rw [lerp_snd]; ring

/-- For a valid diagonal `(t, b)` (indices in range, distinct, non-adjacent), the arc length
`L` from `t` to `b` satisfies `2 ≤ L ≤ n - 2` and `(t + L) % n = b`. -/
theorem exists_diag_index {P : Polygon} (hn : 3 ≤ P.n) {t b : ℕ} (ht : t < P.n) (hb : b < P.n)
    (htb : t ≠ b) (h1 : b ≠ ztbx % P.n) (h2 : t ≠ ztds % P.n) :
    ∃ L, 2 ≤ L ∧ L + 2 ≤ P.n ∧ ztubq % P.n = b := by
  rw [succIdx_eq P ht] at h1
  rw [succIdx_eq P hb] at h2
  rcases le_or_gt t b with hle | hlt
  · refine ⟨b - t, ?_, ?_, ?_⟩
    · grind
    · grind
    · rw [Nat.add_sub_cancel' hle]; exact Nat.mod_eq_of_lt hb
  · refine ⟨b + P.n - t, ?_, ?_, ?_⟩
    · grind
    · grind
    · rw [show t + (b + P.n - t) = b + P.n by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt hb

/-! ### The side lines do not cross -/
end
end Chazelle.Mountain
namespace Chazelle.Visibility.IsTrap
@[expose] public section
open Set Filter Topology
open Chazelle.Jordan
open Chazelle.Mountain
open Chazelle.Existence (IsDiagonal eq_endpoint_of_vtx_mem_edge vtx_mem_boundary)
open Chazelle.Geometry (lerp lerp_fst lerp_snd lerp_zero lerp_one point_ext point_ext_iff
  lerp_mem_segment)
variable {P : Polygon} {q : Point} {i j : ℕ} {y₁ y₂ : ℝ}

/-- **The top side is not reversed**: `edgeX P i y₂ ≤ edgeX P j y₂`.  (Otherwise the two side
lines would cross at a height in `(q.2, y₂)`; the crossing point lies on both edges, so it is a
common vertex, inside the corridor, contradicting `no_vertex`.) -/
theorem edgeX_le_top (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    edgeX P i y₂ ≤ edgeX P j y₂ := by
  zqbhf
  zufwd
  have hcont : ContinuousOn ztisx (Icc q.2 y₂) :=
    ((continuous_edgeX P j).sub ztnxf).continuousOn
  have h0 : (0 : ℝ) ∈ Ioo (edgeX P j y₂ - edgeX P i y₂) ztlni :=
    ⟨by_linarith, by zuoqm⟩
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Ioo' hT.lt_top.le hcont h0
  zumdl
  have hb := hT.bot_lt
  have hzi : ztyts :=
    hT.mem_edgeL by_grind by_grind rfl
  have hzj : ztytt :=
    hT.mem_edgeR by_grind by_grind
      by_grind
  zuflp
  · zuiuz

  · zuiuy

/-- **The bottom side is not reversed**: `edgeX P i y₁ ≤ edgeX P j y₁`. -/
theorem edgeX_le_bot (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    edgeX P i y₁ ≤ edgeX P j y₁ := by
  zqbhf
  zufwd
  have hcont : ContinuousOn ztisx (Icc y₁ q.2) :=
    ((continuous_edgeX P j).sub ztnxf).continuousOn
  have h0 : (0 : ℝ) ∈ Ioo (edgeX P j y₁ - edgeX P i y₁) ztlni :=
    ⟨by_linarith, by zuoqm⟩
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Ioo hT.bot_lt.le hcont h0
  zumdl
  have ht := hT.lt_top
  have hzi : ztyts :=
    hT.mem_edgeL by_grind by_grind rfl
  have hzj : ztytt :=
    hT.mem_edgeR by_grind by_grind
      by_grind
  zuflp
  · zuiuz

  · zuiuy

/-- Strictly between the two heights, the left side line is strictly left of the right one. -/
theorem edgeX_lt (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) {y : ℝ}
    (h1 : y₁ < y) (h2 : y < y₂) : edgeX P i y < edgeX P j y := by
  zufwd
  have hqlt := hq'.2.2.1.trans hq'.2.2.2
  have hb := hT.edgeX_le_bot hP hq
  have ht := hT.edgeX_le_top hP hq
  have h12 := hT.bot_lt
  have h23 := hT.lt_top
  rcases le_or_gt y q.2 with hle | hlt
  · obtain ⟨l, hl0, hl1, hy⟩ : ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ y = (1 - l) * y₁ + l * q.2 := by
      refine ⟨(y - y₁) / (q.2 - y₁), by_simp_all, ?_, ?_⟩
      · zubid
      grind
    zqbhg
    have e1 := mul_nonneg (sub_nonneg.2 hl1) ztwfo
    have e2 := mul_pos hl0 ztwfy
    linarith
  · obtain ⟨l, hl0, hl1, hy⟩ : ∃ l : ℝ, 0 ≤ l ∧ l < 1 ∧ y = (1 - l) * q.2 + l * y₂ := by
      refine ⟨(y - q.2) / (y₂ - q.2), div_nonneg by_linarith by_linarith, ?_, ?_⟩
      · zubie
      grind
    zqbhg
    have e1 := mul_pos (sub_pos.2 hl1) ztwfy
    have e2 := mul_nonneg hl0 (sub_nonneg.2 ht)
    linarith

/-- The midpoint of the horizontal section at a height strictly between the two heights lies in
the trapezoid. -/
theorem mid_mem_trapSet (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    {y : ℝ} (h1 : y₁ < y) (h2 : y < y₂) :
    (((edgeX P i y + edgeX P j y) / 2, y) : Point) ∈ trapSet P i j y₁ y₂ := by
  have := hT.edgeX_lt hP hq h1 h2
  exact ⟨h1, h2, by_grind,
    by grind⟩

/-! ### The top and bottom vertices -/
theorem sideVtxSet_top_nonempty (hP : P.Simple) (hq : q ∈ freeRegion P)
    (hT : IsTrap P q i j y₁ y₂) : (sideVtxSet P i j y₂).Nonempty := by
  obtain ⟨k, hk, hky, hkx⟩ := hT.top_vertex
  obtain ⟨h1, h2⟩ := hkx (hT.edgeX_le_top hP hq)
  exact ztlwj
theorem sideVtxSet_bot_nonempty (hP : P.Simple) (hq : q ∈ freeRegion P)
    (hT : IsTrap P q i j y₁ y₂) : (sideVtxSet P i j y₁).Nonempty := by
  obtain ⟨k, hk, hky, hkx⟩ := hT.bot_vertex
  obtain ⟨h1, h2⟩ := hkx (hT.edgeX_le_bot hP hq)
  exact ztlwj

/-- The top vertex is a vertex of the closed top side, and the leftmost one. -/
theorem topVtx_spec (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    topVtx P i j y₂ ∈ sideVtxSet P i j y₂ ∧
      ∀ k ∈ sideVtxSet P i j y₂, (P.vtx ztbia).1 ≤ (P.vtx k).1 :=
  leftmostVtx_spec P (sideVtxSet_finite P i j y₂) (hT.sideVtxSet_top_nonempty hP hq)

/-- The bottom vertex is a vertex of the closed bottom side, and the rightmost one. -/
theorem botVtx_spec (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    botVtx P i j y₁ ∈ sideVtxSet P i j y₁ ∧
      ∀ k ∈ sideVtxSet P i j y₁, (P.vtx k).1 ≤ (P.vtx ztbsg).1 :=
  rightmostVtx_spec P (sideVtxSet_finite P i j y₁) (hT.sideVtxSet_bot_nonempty hP hq)
theorem topVtx_mem (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    topVtx P i j y₂ ∈ sideVtxSet P i j y₂ := (hT.topVtx_spec hP hq).1
theorem botVtx_mem (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    botVtx P i j y₁ ∈ sideVtxSet P i j y₁ := (hT.botVtx_spec hP hq).1
theorem topVtx_lt (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    topVtx P i j y₂ < P.n := (hT.topVtx_mem hP hq).1
theorem botVtx_lt (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    botVtx P i j y₁ < P.n := (hT.botVtx_mem hP hq).1

/-- The top vertex is at the top height. -/
theorem topVtx_snd (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    (P.vtx ztbia).2 = y₂ := (hT.topVtx_mem hP hq).2.1

/-- The bottom vertex is at the bottom height. -/
theorem botVtx_snd (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    (P.vtx ztbsg).2 = y₁ := (hT.botVtx_mem hP hq).2.1

/-- **The top and bottom vertices are distinct** (their heights differ). -/
theorem topVtx_ne_botVtx (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    topVtx P i j y₂ ≠ botVtx P i j y₁ := by
  zuq
  have h1 := hT.topVtx_snd hP hq
  have h2 := hT.botVtx_snd hP hq
  zvmwc at h1
  linarith [hT.bot_lt, hT.lt_top]

/-- The bottom vertex is strictly below the top vertex. -/
theorem botVtx_snd_lt (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂) :
    (P.vtx ztbsg).2 < (P.vtx ztbia).2 := by
  rw [hT.topVtx_snd hP hq, hT.botVtx_snd hP hq]
  exact hT.bot_lt.trans hT.lt_top

/-! ### The segment from the top vertex to the bottom vertex -/

/-- The segment between the top and bottom vertices lies in the closed trapezoid. -/
theorem diag_lerp_mem_closedTrap (hP : P.Simple) (hq : q ∈ freeRegion P)
    (hT : IsTrap P q i j y₁ y₂) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    lerp ztyhw ztyhx s ∈ closedTrap P i j y₁ y₂ := by
  zqbhb
  zudfi
  · show y₁ ≤ (lerp _ _ s).2
    zqbhe
  · show (lerp _ _ s).2 ≤ y₂
    zqbhe
  · show edgeX P i (lerp _ _ s).2 ≤ (lerp _ _ s).1
    zqbhd
    have e1 := mul_nonneg ztwfq ztwfm
    have e2 := mul_nonneg hs0 ztwfk
    linarith
  · show (lerp _ _ s).1 ≤ edgeX P j (lerp _ _ s).2
    zqbhd
    have e1 := mul_nonneg ztwfq ztwfn
    have e2 := mul_nonneg hs0 ztwfl
    linarith

/-- If the top and bottom vertices are not adjacent in `P`, they do not both lie on the line
of the left side edge `i` (else they would be the two endpoints of edge `i`). -/
theorem not_both_on_left (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    (h1 : botVtx P i j y₁ ≠ ztdik % P.n)
    (h2 : topVtx P i j y₂ ≠ ztdgr % P.n) :
    ¬ ((P.vtx ztbia).1 = edgeX P i y₂ ∧ (P.vtx ztbsg).1 = edgeX P i y₁) := by
  zqbhc
  have hTe : P.vtx ztbia ∈ P.edge i :=
    hT.mem_edgeL by_simp_all ztqey by_simp_all
  have hBe : P.vtx _ ∈ P.edge i :=
    hT.mem_edgeL ztqex by_simp_all by_simp_all
  zufvz
  have hsucc := succIdx_lt P hT.hi
  rcases eq_endpoint_of_vtx_mem_edge hP ht hT.hi hTe with e1 | e1 <;>
    rcases eq_endpoint_of_vtx_mem_edge hP hb hT.hi hBe with e2 | e2
  · exact hne ((simple_vtx_inj hP ht hT.hi e1).trans (simple_vtx_inj hP hb hT.hi e2).symm)
  · have f1 := simple_vtx_inj hP ht hT.hi e1
    zuhdx

  · zuhvx
    have f2 := simple_vtx_inj hP hb hT.hi e2
    simp_all
  · zqbhh

/-- If the top and bottom vertices are not adjacent in `P`, they do not both lie on the line
of the right side edge `j`. -/
theorem not_both_on_right (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    (h1 : botVtx P i j y₁ ≠ ztdik % P.n)
    (h2 : topVtx P i j y₂ ≠ ztdgr % P.n) :
    ¬ ((P.vtx ztbia).1 = edgeX P j y₂ ∧ (P.vtx ztbsg).1 = edgeX P j y₁) := by
  zqbhc
  have hTe : P.vtx ztbia ∈ P.edge j :=
    hT.mem_edgeR by_simp_all ztqey by_simp_all
  have hBe : P.vtx _ ∈ P.edge j :=
    hT.mem_edgeR ztqex by_simp_all by_simp_all
  zufvz
  have hsucc := succIdx_lt P hT.hj
  rcases eq_endpoint_of_vtx_mem_edge hP ht hT.hj hTe with e1 | e1 <;>
    rcases eq_endpoint_of_vtx_mem_edge hP hb hT.hj hBe with e2 | e2
  · exact hne ((simple_vtx_inj hP ht hT.hj e1).trans (simple_vtx_inj hP hb hT.hj e2).symm)
  · have f1 := simple_vtx_inj hP ht hT.hj e1
    zuhdx

  · zuhvx
    have f2 := simple_vtx_inj hP hb hT.hj e2
    simp_all
  · zqbhh

/-- **The open diagonal lies in the open trapezoid** when the top and bottom vertices are not
adjacent in `P`. -/
theorem diag_lerp_mem_trapSet (hP : P.Simple) (hq : q ∈ freeRegion P)
    (hT : IsTrap P q i j y₁ y₂) (h1 : botVtx P i j y₁ ≠ ztdik % P.n)
    (h2 : topVtx P i j y₂ ≠ ztdgr % P.n) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    lerp ztyhw ztyhx s ∈ trapSet P i j y₁ y₂ := by
  zqbhb
  have hnotL := hT.not_both_on_left hP hq h1 h2
  have hnotR := hT.not_both_on_right hP hq h1 h2
  zudfi
  · show y₁ < (lerp _ _ s).2
    zqbhe
  · show (lerp _ _ s).2 < y₂
    zqbhe
  · show edgeX P i (lerp _ _ s).2 < (lerp _ _ s).1
    zqbhd
    rcases lt_or_eq_of_le hTi with hlt | heq
    · zujxf
      have e2 := mul_nonneg hs0.le ztwfk
      linarith
    · have hlt' : edgeX P i y₁ < (P.vtx _).1 :=
        lt_of_le_of_ne hBi by_grind
      have e1 := mul_nonneg ztwfr ztwfm
      zuiuu

  · show (lerp _ _ s).1 < edgeX P j (lerp _ _ s).2
    zqbhd
    rcases lt_or_eq_of_le hTj with hlt | heq
    · zujxf
      have e2 := mul_nonneg hs0.le ztwfl
      linarith
    · have hlt' : (P.vtx _).1 < edgeX P j y₁ :=
        lt_of_le_of_ne hBj by_simp_all
      have e1 := mul_nonneg ztwfr ztwfn
      zuiuu

/-- A point of the closed diagonal (non-adjacent case) is an endpoint or lies in the open
trapezoid. -/
theorem diag_segment_cases (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    (h1 : botVtx P i j y₁ ≠ ztdik % P.n)
    (h2 : topVtx P i j y₂ ≠ ztdgr % P.n) {p : Point}
    (hp : p ∈ Chazelle.segment ztyhw ztyhx) :
    p = P.vtx ztbia ∨ p = P.vtx ztbsg ∨ p ∈ trapSet P i j y₁ y₂ := by
  zufkr
  zugac
  · zukmg
    · exact Or.inr (Or.inr (hT.diag_lerp_mem_trapSet hP hq h1 h2 hs0 hs1))
    simp
  simp

/-- **The diagonal lemma.**  If the top and bottom vertices of a trapezoid are not adjacent in
`P`, the segment between them is an interior diagonal: `IsDiagonal P s L` with
`s % n = topVtx`, `(s + L) % n = botVtx`, and the closed segment lies in the filled region. -/
theorem exists_isDiagonal (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    (h1 : botVtx P i j y₁ ≠ ztdik % P.n)
    (h2 : topVtx P i j y₂ ≠ ztdgr % P.n) :
    ∃ s L, IsDiagonal P s L ∧ s % P.n = topVtx P i j y₂ ∧ ztny % P.n = botVtx P i j y₁ ∧
      Chazelle.segment ztyhw ztyhx ⊆ P.filled := by
  have ht := hT.topVtx_lt hP hq
  zukbd
  zufvz
  obtain ⟨L, hL2, hLn, hsL⟩ := exists_diag_index ztqwk ht hb hne h1 h2
  have hs := Nat.mod_eq_of_lt ht
  refine ⟨topVtx P i j y₂, L, ztrcs, hs, hsL, ?_⟩
  · zukvy
    intro p hp hpT hpB
    rcases hT.diag_segment_cases hP hq h1 h2 hp with e | e | hin
    · simp_all
    · simp_all
    · exact hT.not_mem_boundary hP hq hin
  · zuda
    rcases hT.diag_segment_cases hP hq h1 h2 hp with rfl | rfl | hin
    · exact boundary_subset_filled P (vtx_mem_boundary P ht)
    · exact boundary_subset_filled P (vtx_mem_boundary P hb)
    · exact (hT.trapSet_subset_interior hP hq hin).1

/-! ### The adjacent case: the diagonal is a side edge -/

/-! ### Vertices of the closed trapezoid -/

/-- **Every vertex of `P` in the closed trapezoid lies on the closed top or bottom side.** -/
theorem vtx_mem_closedTrap_iff (hT : IsTrap P q i j y₁ y₂) {k : ℕ} (hk : k < P.n) :
    P.vtx k ∈ closedTrap P i j y₁ y₂ ↔ k ∈ sideVtxSet P i j y₁ ∨ k ∈ sideVtxSet P i j y₂ := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    zuff
    · zudt
      · exact (hT.no_vertex k hk h1 h2 h3 h4).elim
      · right
        refine ⟨hk, h2, ?_, ?_⟩ <;> rw [← h2] <;> assumption
    · left
      refine ⟨hk, h1.symm, ?_, ?_⟩ <;> zvmwp <;> assumption
  · zuhwa
    rintro (⟨-, hy, h3, h4⟩ | ⟨-, hy, h3, h4⟩)
    · exact ⟨hy.ge, by_simp_all, by_simp_all, by_simp_all⟩
    · exact ⟨by_simp_all, hy.le, by_simp_all, by_simp_all⟩

/-- A vertex of `P` in the closure of the trapezoid lies on the closed top or bottom side. -/
theorem vtx_mem_closure_trapSet (hT : IsTrap P q i j y₁ y₂) {k : ℕ} (hk : k < P.n)
    (h : P.vtx k ∈ closure ztbku) :
    k ∈ sideVtxSet P i j y₁ ∨ k ∈ sideVtxSet P i j y₂ :=
  (hT.vtx_mem_closedTrap_iff hk).1 (closure_trapSet_subset P i j y₁ y₂ h)

/-! ### The top and bottom vertices depend only on the region -/

/-- If the trapezoid lies in another trapezoid, its top height is at most the other's. -/
theorem top_le_of_subset (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    {q' : Point} {i' j' : ℕ} {y₁' y₂' : ℝ} (_hT' : IsTrap P q' i' j' y₁' y₂')
    (hsub : trapSet P i j y₁ y₂ ⊆ trapSet P i' j' y₁' y₂') : y₂ ≤ y₂' := by
  zqbhf
  have hq2 := (hsub zttmw).2.1
  have hmid := hT.mid_mem_trapSet hP hq (y := (y₂' + y₂) / 2) (by linarith [hT.bot_lt])
    by_linarith
  have h := (hsub hmid).2.1
  linarith

/-- If the trapezoid lies in another trapezoid, its bottom height is at least the other's. -/
theorem bot_le_of_subset (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    {q' : Point} {i' j' : ℕ} {y₁' y₂' : ℝ} (_hT' : IsTrap P q' i' j' y₁' y₂')
    (hsub : trapSet P i j y₁ y₂ ⊆ trapSet P i' j' y₁' y₂') : y₁' ≤ y₁ := by
  zqbhf
  have hq1 := (hsub zttmw).1
  have hmid := hT.mid_mem_trapSet hP hq (y := (y₁ + y₁') / 2) by_linarith
    (by linarith [hT.lt_top])
  have h := (hsub hmid).1
  linarith

/-- If the trapezoid lies in another trapezoid, the other's left side line is to the left at
every height of the range. -/
theorem left_le_of_subset (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    {q' : Point} {i' j' : ℕ} {y₁' y₂' : ℝ} (_hT' : IsTrap P q' i' j' y₁' y₂')
    (hsub : trapSet P i j y₁ y₂ ⊆ trapSet P i' j' y₁' y₂') :
    ∀ y ∈ Icc y₁ y₂, edgeX P i' y ≤ edgeX P i y := by
  have hIoo : Ioo y₁ y₂ ⊆ {y | edgeX P i' y ≤ edgeX P i y} := by
    zqbhi
    have hmin1 := min_le_left ztlnh ztlnj
    have hmin2 := min_le_right ztlnh ztlnj
    have hlt2 : edgeX P i y < min _ _ := lt_min hlt hij
    have hp : (((edgeX P i y + min ztlnh ztlnj) / 2, y) : Point) ∈
        trapSet P i j y₁ y₂ :=
      ⟨hy.1, hy.2,
        by grind,
        by grind⟩
    have h2 : edgeX P i' y < (edgeX P i y + min _ _) / 2 :=
      (hsub hp).2.2.1
    linarith
  have hcl := (isClosed_le (continuous_edgeX P i') ztnxf).closure_subset_iff.2
    hIoo
  zufmt

/-- If the trapezoid lies in another trapezoid, the other's right side line is to the right at
every height of the range. -/
theorem right_le_of_subset (hP : P.Simple) (hq : q ∈ freeRegion P) (hT : IsTrap P q i j y₁ y₂)
    {q' : Point} {i' j' : ℕ} {y₁' y₂' : ℝ} (_hT' : IsTrap P q' i' j' y₁' y₂')
    (hsub : trapSet P i j y₁ y₂ ⊆ trapSet P i' j' y₁' y₂') :
    ∀ y ∈ Icc y₁ y₂, edgeX P j y ≤ edgeX P j' y := by
  have hIoo : Ioo y₁ y₂ ⊆ {y | edgeX P j y ≤ edgeX P j' y} := by
    zqbhi
    have hmax1 := le_max_left ztlng ztlnk
    have hmax2 := le_max_right ztlng ztlnk
    have hlt2 : max _ _ < edgeX P j y := max_lt hij hlt
    have hp : (((max ztlng ztlnk + edgeX P j y) / 2, y) : Point) ∈
        trapSet P i j y₁ y₂ :=
      ⟨hy.1, hy.2,
        by grind,
        by grind⟩
    have h2 : (max _ _ + edgeX P j y) / 2 < edgeX P j' y :=
      (hsub hp).2.2.2
    linarith
  have hcl := (isClosed_le (continuous_edgeX P j) (continuous_edgeX P j')).closure_subset_iff.2
    hIoo
  zufmt

/-- **The top and bottom vertices depend only on the region.**  Two trapezoid data describing
the same open trapezoid have the same top vertex and the same bottom vertex. -/
theorem topVtx_eq_of_trapSet_eq (hP : P.Simple) (hq : q ∈ freeRegion P)
    (hT : IsTrap P q i j y₁ y₂) {q' : Point} {i' j' : ℕ} {y₁' y₂' : ℝ} (hq' : q' ∈ freeRegion P)
    (hT' : IsTrap P q' i' j' y₁' y₂') (h : trapSet P i j y₁ y₂ = trapSet P i' j' y₁' y₂') :
    topVtx P i j y₂ = topVtx P i' j' y₂' ∧ botVtx P i j y₁ = botVtx P i' j' y₁' := by
  have hsub := h.subset
  have hsub' := h.symm.subset
  have hy2 :=
    le_antisymm (hT.top_le_of_subset hP hq hT' hsub) (hT'.top_le_of_subset hP hq' hT hsub')
  have hy1 :=
    le_antisymm (hT'.bot_le_of_subset hP hq' hT hsub') (hT.bot_le_of_subset hP hq hT' hsub)
  zuhwa
  have h12' := (hT'.bot_lt.trans hT'.lt_top).le
  have hI2 : y₂ ∈ Icc y₁ y₂ := by_simp_all
  have hI2' : y₂ ∈ Icc y₁' y₂' := by_simp_all
  have hI1 : y₁ ∈ Icc y₁ y₂ := by_simp_all
  have hI1' : y₁ ∈ Icc y₁' y₂' := by_simp_all
  have hi2 :=
    le_antisymm (hT'.left_le_of_subset hP hq' hT hsub' y₂ hI2')
      (hT.left_le_of_subset hP hq hT' hsub y₂ hI2)
  have hj2 :=
    le_antisymm (hT.right_le_of_subset hP hq hT' hsub y₂ hI2)
      (hT'.right_le_of_subset hP hq' hT hsub' y₂ hI2')
  have hi1 :=
    le_antisymm (hT'.left_le_of_subset hP hq' hT hsub' y₁ hI1')
      (hT.left_le_of_subset hP hq hT' hsub y₁ hI1)
  have hj1 :=
    le_antisymm (hT.right_le_of_subset hP hq hT' hsub y₁ hI1)
      (hT'.right_le_of_subset hP hq' hT hsub' y₁ hI1')
  have hS2 : sideVtxSet P i j y₂ = sideVtxSet P i' j' y₂' := by
    rw [← hy2]
    zugkm

  have hS1 : sideVtxSet P i j y₁ = sideVtxSet P i' j' y₁' := by
    rw [← hy1]
    zugkm

  exact ⟨by unfold topVtx; rw [hS2], by unfold botVtx; rw [hS1]⟩
end
end Chazelle.Visibility.IsTrap
end
namespace Chazelle.Mountain
@[expose] public section
open Set
open Chazelle.Jordan
open Chazelle.Visibility
open Chazelle.Existence (IsDiagonal vtx_mem_boundary)
open Chazelle.Geometry (lerp lerp_mem_segment)

/-! ### Segments named by index pairs -/

/-- The closed segment named by a pair of vertex indices. -/
def diagSeg (P : Polygon) (d : ℕ × ℕ) : Set Point := Chazelle.segment ztjla ztjlb

/-! ### Trapezoid data of a region -/

/-- The data of a region of the visibility map: a free point `q` and its trapezoid data. -/
structure TrapData (P : Polygon) where
  /-- A free point of the region. -/
  q : Point
  /-- The left side edge. -/
  i : ℕ
  /-- The right side edge. -/
  j : ℕ
  /-- The bottom height. -/
  y₁ : ℝ
  /-- The top height. -/
  y₂ : ℝ
  free : q ∈ freeRegion P
  isTrap : IsTrap P q i j y₁ y₂
namespace TrapData
variable {P : Polygon}

/-- The region (open trapezoid) described by the data. -/
def region (D : TrapData P) : Set Point := trapSet P D.i D.j D.y₁ D.y₂

/-- The top vertex of the trapezoid (leftmost vertex of the closed top side). -/
noncomputable def top (D : TrapData P) : ℕ := topVtx P D.i D.j D.y₂

/-- The bottom vertex of the trapezoid (rightmost vertex of the closed bottom side). -/
noncomputable def bot (D : TrapData P) : ℕ := botVtx P D.i D.j D.y₁

/-- The index pair of the diagonal of the trapezoid. -/
noncomputable def diag (D : TrapData P) : ℕ × ℕ := (D.top, D.bot)

/-- The top and bottom vertices are not adjacent in `P`. -/
def NonAdj (D : TrapData P) : Prop := D.bot ≠ (D.top + 1) % P.n ∧ D.top ≠ (D.bot + 1) % P.n
theorem region_mem_regions (hP : P.Simple) (D : TrapData P) : D.region ∈ regions P :=
  ⟨D.q, D.free, (D.isTrap.region_eq hP D.free).symm⟩
theorem region_subset_freeRegion (hP : P.Simple) (D : TrapData P) : D.region ⊆ freeRegion P :=
  D.isTrap.trapSet_subset_freeRegion hP D.free
theorem region_subset_interior (hP : P.Simple) (D : TrapData P) :
    D.region ⊆ P.filled \ P.boundary :=
  D.isTrap.trapSet_subset_interior hP D.free
theorem top_lt (hP : P.Simple) (D : TrapData P) : D.top < P.n := D.isTrap.topVtx_lt hP D.free
theorem bot_lt (hP : P.Simple) (D : TrapData P) : D.bot < P.n := D.isTrap.botVtx_lt hP D.free
theorem top_ne_bot (hP : P.Simple) (D : TrapData P) : D.top ≠ D.bot :=
  D.isTrap.topVtx_ne_botVtx hP D.free
theorem top_snd (hP : P.Simple) (D : TrapData P) : (P.vtx D.top).2 = D.y₂ :=
  D.isTrap.topVtx_snd hP D.free
theorem bot_snd (hP : P.Simple) (D : TrapData P) : (P.vtx D.bot).2 = D.y₁ :=
  D.isTrap.botVtx_snd hP D.free
theorem bot_snd_lt_top_snd (hP : P.Simple) (D : TrapData P) :
    (P.vtx D.bot).2 < (P.vtx D.top).2 :=
  D.isTrap.botVtx_snd_lt hP D.free

/-- No vertex lies in a region. -/
theorem not_mem_region_of_vtx (hP : P.Simple) (D : TrapData P) {k : ℕ} (hk : k < P.n) :
    P.vtx k ∉ D.region :=
  fun h => (D.region_subset_interior hP h).2 ztudc

/-- **The diagonal depends only on the region.** -/
theorem diag_eq_of_region_eq (hP : P.Simple) (D D' : TrapData P) (h : D.region = D'.region) :
    D.diag = D'.diag := by
  obtain ⟨h1, h2⟩ := D.isTrap.topVtx_eq_of_trapSet_eq hP D.free D'.free D'.isTrap h
  zulxg

/-- A point of the closed diagonal (non-adjacent case) is an endpoint or lies in the region. -/
theorem segment_cases (hP : P.Simple) (D : TrapData P) (hD : D.NonAdj) {p : Point}
    (hp : p ∈ diagSeg P D.diag) : p = P.vtx D.top ∨ p = P.vtx D.bot ∨ p ∈ D.region :=
  D.isTrap.diag_segment_cases hP D.free hD.1 hD.2 hp

/-- **The diagonal is an interior diagonal** (non-adjacent case). -/
theorem exists_isDiagonal (hP : P.Simple) (D : TrapData P) (hD : D.NonAdj) :
    ∃ s L, IsDiagonal P s L ∧ s % P.n = D.top ∧ ztny % P.n = D.bot ∧
      diagSeg P D.diag ⊆ P.filled :=
  D.isTrap.exists_isDiagonal hP D.free hD.1 hD.2
theorem eq_endpoint_of_mem_diagSeg (hP : P.Simple) (D : TrapData P) (hD : D.NonAdj) {p : Point}
    (hp : p ∈ diagSeg P D.diag) (hnot : p ∉ D.region) : p = P.vtx D.top ∨ p = P.vtx D.bot := by
  zufzn
  · simp_all
  · simp_all
  simp_all

/-- **Every vertex of `P` in the closure of a region lies on the closed top or bottom side of
the trapezoid.** -/
theorem vtx_mem_closure_region (D : TrapData P) {k : ℕ} (hk : k < P.n)
    (h : P.vtx k ∈ closure D.region) :
    k ∈ sideVtxSet P D.i D.j D.y₁ ∨ k ∈ sideVtxSet P D.i D.j D.y₂ :=
  D.isTrap.vtx_mem_closure_trapSet hk h
end TrapData

/-- Every region of the visibility map has trapezoid data. -/
theorem exists_trapData {P : Polygon} (hP : P.Simple) {C : Set Point} (hC : C ∈ regions P) :
    ∃ D : TrapData P, D.region = C := by
  obtain ⟨q, i, j, y₁, y₂, hq, hT, rfl⟩ := regions_eq_trapSet hP hC
  exact ⟨⟨q, i, j, y₁, y₂, hq, hT⟩, rfl⟩

/-! ### The trapezoid diagonals -/

/-- **The trapezoid diagonals**: the pairs `(top, bot)` of the trapezoids whose top and bottom
vertices are not adjacent in `P`. -/
def trapDiagonals (P : Polygon) : Set ztw := {d | ∃ D : TrapData P, D.NonAdj ∧ d = D.diag}
theorem TrapData.diag_mem_trapDiagonals {P : Polygon} (D : TrapData P) (hD : D.NonAdj) :
    D.diag ∈ trapDiagonals P :=
  ⟨D, hD, rfl⟩

/-- Elementary properties of a trapezoid diagonal: indices in range, distinct, the first
strictly above the second, not adjacent. -/
theorem trapDiagonals_spec {P : Polygon} (hP : P.Simple) {d : ℕ × ℕ} (hd : d ∈ trapDiagonals P) :
    d.1 < P.n ∧ d.2 < P.n ∧ d.1 ≠ d.2 ∧ (P.vtx d.2).2 < (P.vtx d.1).2 ∧
      d.2 ≠ zttiu % P.n ∧ d.1 ≠ zttiv % P.n := by
  zubor
  exact ⟨D.top_lt hP, D.bot_lt hP, D.top_ne_bot hP, D.bot_snd_lt_top_snd hP, hD.1, hD.2⟩

/-- **Each trapezoid diagonal is an interior diagonal.** -/
theorem trapDiagonals_isDiagonal {P : Polygon} (hP : P.Simple) {d : ℕ × ℕ}
    (hd : d ∈ trapDiagonals P) :
    ∃ s L, IsDiagonal P s L ∧ s % P.n = d.1 ∧ ztny % P.n = d.2 ∧ diagSeg P d ⊆ P.filled := by
  zubor
  exact D.exists_isDiagonal hP hD
theorem trapDiagonals_finite {P : Polygon} (hP : P.Simple) : (trapDiagonals P).Finite :=
  ((Set.finite_lt_nat P.n).prod (Set.finite_lt_nat P.n)).subset fun _ hd =>
    ⟨(trapDiagonals_spec hP hd).1, (trapDiagonals_spec hP hd).2.1⟩
open Classical in
/-- The region of a trapezoid diagonal (any trapezoid data producing it; well defined by
`TrapData.diag_eq_of_region_eq`), or `∅`. -/
noncomputable def regionOfDiag (P : Polygon) (d : ℕ × ℕ) : Set Point :=
  if h : ∃ D : TrapData P, D.NonAdj ∧ d = D.diag then (Classical.choose h).region else ∅
theorem regionOfDiag_spec {P : Polygon} {d : ℕ × ℕ} (hd : d ∈ trapDiagonals P) :
    ∃ D : TrapData P, D.NonAdj ∧ d = D.diag ∧ regionOfDiag P d = D.region := by
  have h : ∃ D : TrapData P, D.NonAdj ∧ d = D.diag := hd
  refine ⟨Classical.choose h, by_grind, by_grind, ?_⟩
  unfold regionOfDiag
  simp_all

/-- **Distinct trapezoid diagonals meet at most in common endpoints.** -/
theorem trapDiagonals_inter {P : Polygon} (hP : P.Simple) {d d' : ℕ × ℕ}
    (hd : d ∈ trapDiagonals P) (hd' : d' ∈ trapDiagonals P) (hne : d ≠ d') :
    diagSeg P d ∩ diagSeg P d' ⊆
      ({P.vtx d.1, P.vtx d.2} : Set Point) ∩ {P.vtx d'.1, P.vtx d'.2} := by
  zubor
  obtain ⟨D', hD', rfl⟩ := hd'
  have hreg := fun h => hne (TrapData.diag_eq_of_region_eq hP D D' h)
  have hdisj :=
    (regions_eq_or_disjoint ztpxd ztuxo).resolve_left
      hreg
  zujgf
  have h1 : p ∉ D.region := by
    intro hpD
    rcases D'.segment_cases hP hD' hp' with e | e | e
    · exact D.not_mem_region_of_vtx hP ztpxc by_simp_all
    · exact D.not_mem_region_of_vtx hP ztpxb by_simp_all
    grind
  have h1' : p ∉ D'.region := by
    intro hpD
    zufzn
    · exact D'.not_mem_region_of_vtx hP ztgdl by_simp_all
    · exact D'.not_mem_region_of_vtx hP ztmap by_simp_all
    simp_all
  zuhpt
  exact ⟨D.eq_endpoint_of_mem_diagSeg hP hD hp h1, D'.eq_endpoint_of_mem_diagSeg hP hD' hp' h1'⟩

/-! ### Vertex-to-vertex chords -/

/-- **The vertex-to-vertex chords**: `(k, m)` such that the chord of vertex `k` in some locally
interior horizontal direction ends at vertex `m`. -/
def vtxChords (P : Polygon) : Set ztw :=
  {d | d.1 < P.n ∧ d.2 < P.n ∧
    ∃ σ : ℝ, ztdd ∧ DirInterior P d.1 σ ∧ chordEnd P d.1 σ = P.vtx d.2}
theorem vtxChords_spec {P : Polygon} {d : ℕ × ℕ} (hd : d ∈ vtxChords P) :
    ∃ σ : ℝ, ztdd ∧ DirInterior P d.1 σ ∧ chordEnd P d.1 σ = P.vtx d.2 ∧
      diagSeg P d = chordSet P d.1 σ := by
  obtain ⟨-, -, σ, hσ, hdir, hend⟩ := hd
  exact ⟨σ, hσ, hdir, hend, by unfold diagSeg chordSet; simp_all⟩

/-- A vertex-to-vertex chord is a chord of the visibility map. -/
theorem vtxChords_diagSeg_mem_chords {P : Polygon} {d : ℕ × ℕ} (hd : d ∈ vtxChords P) :
    diagSeg P d ∈ chords P := by
  obtain ⟨σ, hσ, hdir, -, hseg⟩ := vtxChords_spec hd
  exact ⟨d.1, σ, hd.1, hσ, hdir, hseg⟩

/-- The two endpoints of a vertex-to-vertex chord are at the same height. -/
theorem vtxChords_snd_eq {P : Polygon} {d : ℕ × ℕ} (hd : d ∈ vtxChords P) :
    (P.vtx d.1).2 = (P.vtx d.2).2 := by
  obtain ⟨σ, -, -, hend, -⟩ := vtxChords_spec hd
  rw [← hend]
  rfl
theorem vtxChords_ne {P : Polygon} (hP : P.Simple) {d : ℕ × ℕ} (hd : d ∈ vtxChords P) :
    d.1 ≠ d.2 := by
  obtain ⟨σ, -, hdir, hend, -⟩ := vtxChords_spec hd
  zuq
  apply chordEnd_ne_vtx hP hd.1 hdir
  simp_all

/-- The endpoints of a vertex-to-vertex chord are not adjacent (the chord's open part is
interior, so it is not an edge). -/
theorem vtxChords_not_adjacent {P : Polygon} (hP : P.Simple) {d : ℕ × ℕ} (hd : d ∈ vtxChords P) :
    d.2 ≠ zttiu % P.n ∧ d.1 ≠ zttiv % P.n := by
  zuble
  zuhyw

  have hpos := chordParam_pos hP hk hdir
  have hzo : rayPt _ σ _ ∈ openChordSet P d.1 σ :=
    ⟨chordParam P d.1 σ / 2, by_simp_all, rfl⟩
  have hzi := openChordSet_subset_interior hP hk hdir hzo
  have hzs : rayPt ztjla σ (chordParam P d.1 σ / 2) ∈ diagSeg P d := by
    rw [hseg, chordSet_eq_openChordSet_union hP hk hdir]
    simp_all
  constructor
  · zuq
    apply hzi.2
    exact ⟨d.1, hk, by unfold Polygon.edge; zvmzi; tauto⟩
  · zuq
    apply hzi.2
    exact ⟨d.2, hm, by unfold Polygon.edge; rw [← h, segment_comm]; tauto⟩

/-- **Each vertex-to-vertex chord is an interior diagonal.** -/
theorem vtxChords_isDiagonal {P : Polygon} (hP : P.Simple) {d : ℕ × ℕ} (hd : d ∈ vtxChords P) :
    ∃ s L, IsDiagonal P s L ∧ s % P.n = d.1 ∧ ztny % P.n = d.2 ∧ diagSeg P d ⊆ P.filled := by
  zuble
  zuhyw

  have hne := vtxChords_ne hP hd
  obtain ⟨h1, h2⟩ := vtxChords_not_adjacent hP hd
  obtain ⟨L, hL2, hLn, hsL⟩ := exists_diag_index ztqwk hk hm hne h1 h2
  have hs := Nat.mod_eq_of_lt hk
  refine ⟨d.1, L, ztrcs, hs, hsL, ?_⟩
  · zukvy
    zuhgu
    have hp' : p ∈ chordSet P d.1 σ := by rw [← hseg]; exact hp
    rcases mem_chordSet_cases hP hk hdir hp' with e | e | e
    · simp_all
    · simp_all
    simp_all
  · zumof
    exact chordSet_subset_filled hP hk hdir

/-- The index of a vertex point (`Classical.epsilon`; meaningful for vertices of a simple
polygon, see `vtxIndex_vtx`). -/
noncomputable def vtxIndex (P : Polygon) (p : Point) : ℕ :=
  Classical.epsilon fun m => m < P.n ∧ P.vtx m = p
theorem vtxIndex_vtx {P : Polygon} (hP : P.Simple) {m : ℕ} (hm : m < P.n) :
    vtxIndex P ztdlh = m := by
  have h := Classical.epsilon_spec (p := fun m' => m' < P.n ∧ P.vtx m' = P.vtx m) ⟨m, hm, rfl⟩
  exact simple_vtx_inj hP h.1 hm h.2
theorem vtxChords_subset_image {P : Polygon} (hP : P.Simple) :
    vtxChords P ⊆ (fun x : ℕ × ℝ => (x.1, vtxIndex P (chordEnd P x.1 x.2))) ''
      ztbxm := by
  rintro ⟨k, m⟩ ⟨hk, hm, σ, hσ, -, hend⟩
  refine ⟨zttqg, ztbjy, ?_⟩
  · simp_all
  · show (k, vtxIndex P _) = zttqf
    rw [hend, vtxIndex_vtx hP hm]
theorem vtxChords_finite {P : Polygon} (hP : P.Simple) : (vtxChords P).Finite :=
  ((Finset.range P.n).finite_toSet.prod by_simp_all).image _
    |>.subset (vtxChords_subset_image hP)

/-- **A vertex-to-vertex chord meets a trapezoid diagonal at most in common endpoints.** -/
theorem vtxChords_inter_trapDiagonals {P : Polygon} (hP : P.Simple) {d d' : ℕ × ℕ}
    (hd : d ∈ trapDiagonals P) (hd' : d' ∈ vtxChords P) :
    diagSeg P d ∩ diagSeg P d' ⊆
      ({P.vtx d.1, P.vtx d.2} : Set Point) ∩ {P.vtx d'.1, P.vtx d'.2} := by
  zubor
  obtain ⟨σ, hσ, hdir, hend, hseg⟩ := vtxChords_spec hd'
  zujgf
  have hpc : ztuur :=
    ⟨chordSet P d'.1 σ, ⟨d'.1, σ, hd'.1, hσ, hdir, rfl⟩, by_simp_all⟩
  have h1 := fun h => (D.region_subset_freeRegion hP h).2 hpc
  have hend1 := D.eq_endpoint_of_mem_diagSeg hP hD hp h1
  have hpb : p ∈ P.boundary := by
    rcases hend1 with rfl | rfl
    · exact vtx_mem_boundary P ztgdl
    · exact vtx_mem_boundary P ztmap
  have hmem : p ∈ ({P.vtx d'.1, chordEnd P d'.1 σ} : Set Point) := by
    rw [← chordSet_inter_boundary hP hd'.1 hdir]
    simp_all
  simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at hmem ⊢
  refine ⟨hend1, ?_⟩
  simp_all

/-- **Two vertex-to-vertex chords with distinct segments meet at most in common endpoints.**
(The pairs `(k, m)` and `(m, k)` name the same chord when both directions are recorded.) -/
theorem vtxChords_inter {P : Polygon} (hP : P.Simple) {d d' : ℕ × ℕ} (hd : d ∈ vtxChords P)
    (hd' : d' ∈ vtxChords P) (hne : diagSeg P d ≠ diagSeg P d') :
    diagSeg P d ∩ diagSeg P d' ⊆
      ({P.vtx d.1, P.vtx d.2} : Set Point) ∩ {P.vtx d'.1, P.vtx d'.2} := by
  zuble
  obtain ⟨σ', hσ', hdir', hend', hseg'⟩ := vtxChords_spec hd'
  rw [hseg, hseg'] at hne ⊢
  zuda
  have := chord_inter hP hd.1 hd'.1 hσ hσ' hdir hdir' hne hp
  simp_all

/-! ### All inserted diagonals -/

/-- **All inserted diagonals**: the trapezoid diagonals together with the vertex-to-vertex
chords. -/
def allDiagonals (P : Polygon) : Set ztw := trapDiagonals P ∪ vtxChords P
theorem allDiagonals_finite {P : Polygon} (hP : P.Simple) : (allDiagonals P).Finite :=
  (trapDiagonals_finite hP).union (vtxChords_finite hP)

/-- **Every inserted diagonal is an interior diagonal.** -/
theorem allDiagonals_isDiagonal {P : Polygon} (hP : P.Simple) {d : ℕ × ℕ}
    (hd : d ∈ allDiagonals P) :
    ∃ s L, IsDiagonal P s L ∧ s % P.n = d.1 ∧ ztny % P.n = d.2 ∧ diagSeg P d ⊆ P.filled := by
  zudsc
  · exact trapDiagonals_isDiagonal hP hd
  · exact vtxChords_isDiagonal hP hd

/-- Indices of an inserted diagonal are in range and distinct. -/
theorem allDiagonals_lt {P : Polygon} (hP : P.Simple) {d : ℕ × ℕ} (hd : d ∈ allDiagonals P) :
    d.1 < P.n ∧ d.2 < P.n ∧ d.1 ≠ d.2 := by
  zudsc
  · exact ⟨(trapDiagonals_spec hP hd).1, (trapDiagonals_spec hP hd).2.1,
      (trapDiagonals_spec hP hd).2.2.1⟩
  · exact ⟨hd.1, hd.2.1, vtxChords_ne hP hd⟩

/-- **Two inserted diagonals with distinct segments meet at most in common endpoints.** -/
theorem allDiagonals_inter {P : Polygon} (hP : P.Simple) {d d' : ℕ × ℕ} (hd : d ∈ allDiagonals P)
    (hd' : d' ∈ allDiagonals P) (hne : diagSeg P d ≠ diagSeg P d') :
    diagSeg P d ∩ diagSeg P d' ⊆
      ({P.vtx d.1, P.vtx d.2} : Set Point) ∩ {P.vtx d'.1, P.vtx d'.2} := by
  rcases hd with hd | hd <;> rcases hd' with hd' | hd'
  · exact trapDiagonals_inter hP hd hd' by_grind
  · exact vtxChords_inter_trapDiagonals hP hd hd'
  · zuda
    have := vtxChords_inter_trapDiagonals hP hd' hd ztuhv
    simp_all
  · exact vtxChords_inter hP hd hd' hne

/-! ### The mountain decomposition theorem: statement and plan

**What remains (not proved here).**  Let `P` be simple and let `Δ = allDiagonals P`.  Call a
list `l : List ℕ` of pairwise distinct indices `< n` a *piece* of the subdivision when
`3 ≤ l.length`, every edge of `subPoly P l` (see `Chazelle.EarClip.SubPoly`) is either an edge
of `P` (`l[k+1] = (l[k] + 1) % n`) or an inserted diagonal (`(l[k], l[k+1]) ∈ Δ` or
`(l[k+1], l[k]) ∈ Δ`, cyclically), and the interior of `(subPoly P l).filled` contains no
point of `P.boundary ∪ ⋃ d ∈ Δ, diagSeg P d` (so that the piece is a face of the subdivision).
The claim is:

  `∀ l, IsPiece P l → ∃ a < l.length, IsMountain (subPoly P l) a`

where `IsMountain Q a` means: the edge `a` of `Q` is the *base*, i.e. writing
`v₀ = Q.vtx ((a+1) % m), v₁, …, v_{m-1} = Q.vtx a` for the remaining vertices in cyclic order,
the sequence `v₀, …, v_{m-1}` is strictly `ylexLT`-monotone (increasing or decreasing); in
particular `Q` is a monotone polygon (with respect to the `ylexLT`-perturbed height) one of
whose two chains is the single edge `a`.  Together with `allDiagonals_isDiagonal` and
`allDiagonals_inter`, and `filled_eq_union_arcs` / `weakTriangulates_of_diagonal` applied along
each diagonal, this reduces the triangulation of `P` to the triangulation of mountains.

**Why the vertex-to-vertex chords are needed.**  With the exact (unperturbed) horizontal
chords of `Chazelle.Visibility`, the top–bottom diagonals alone do *not* decompose `P` into
mountains.  Example: `P = [(0,0), (1,1), (2,0), (3,0), (3,-2), (0,-2)]`.  Its only chord is
the segment from `(0,0)` to `(2,0)` (emitted by both endpoints); the two regions are the
triangle above it and the rectangle `(0,3) × (-2,0)` below.  For the rectangle, the closed top
side carries the vertices `(0,0), (2,0), (3,0)`, so `top = 0` (leftmost), the bottom side
carries `(0,-2), (3,-2)`, so `bot = 4` (rightmost); the diagonal `(0,4)` is inserted.  For the
triangle, `top = 1` and `bot = 2` (rightmost of `(0,0), (2,0)`) are adjacent: no diagonal.
Cutting along `(0,4)` alone leaves the piece `[0,1,2,3,4]`, i.e. `(0,0),(1,1),(2,0),(3,0),(3,-2)`,
whose two chains from the `ylexLT`-minimum `(3,-2)` to the maximum `(1,1)` are
`(3,-2),(0,0),(1,1)` and `(3,-2),(3,0),(2,0),(1,1)`: neither is a single edge, so the piece is
not a mountain (for any tie-break).  Inserting also the vertex-to-vertex chord `(0,2)` gives
the pieces `[0,1,2]`, `[0,2,3,4]` and `[4,5,0]`, all mountains with bases `(2,0)`, `(4,3)`
and `(0,4)`.  In general the `ylexLT`-perturbed trapezoidation (heights `y + ε x`) slices each
unperturbed trapezoid into a middle slab, whose top and bottom vertices are exactly
`topVtx` (leftmost on top) and `botVtx` (rightmost at the bottom), and thin slabs between
consecutive vertices of the closed top (resp. bottom) side, whose diagonals are exactly the
segments between consecutive side vertices, i.e. edges of `P` or vertex-to-vertex chords.  So
`allDiagonals P` is the diagonal set of the perturbed trapezoidation, for which the classical
argument applies.

**Proof plan for the claim.**  The boundary of a piece alternates between maximal chains of
`P`-edges and inserted diagonals.  (1) A maximal chain of `P`-edges `v_a, …, v_b` inside a piece
is `ylexLT`-monotone: if some interior vertex `v` of the chain were a `ylexLT`-local extremum,
say a local minimum, then near `v` the piece lies above `v`; the region of the visibility map
touching `v` from above has `v` on its closed bottom side, and either `v` is its bottom vertex
(so a diagonal is attached at `v` unless it is adjacent to the top vertex, in which case that
edge is a side edge and the trapezoid is a triangle with base at `v`, a mountain apex), or the
segment from `v` to the next side vertex is a vertex-to-vertex chord in `allDiagonals P`, also
attached at `v`; both contradict `v` being interior to a maximal `P`-chain.  (2) Each inserted
diagonal joins a top vertex to a bottom vertex of the same trapezoid (or two vertices at the
same height), so the chains meeting at a diagonal endpoint continue monotonically across it, and
a piece has exactly one `ylexLT`-maximum and one minimum; the base is the diagonal (or edge)
joining them when one of the two chains consists of that single segment, which is forced by
the trapezoid geometry: the chain opposite to the base lies on the side edges `i`, `j` of one
trapezoid and its top/bottom sides.  Auxiliary facts available here:
`TrapData.vtx_mem_closure_region` (every vertex on the closure of a region is on its closed top
or bottom side), `IsTrap.top_side` / `IsTrap.bot_side` (the open sides are boundary or chord
points), `TrapData.top_eq_side_of_adjacent`, `TrapData.bot_eq_side_of_adjacent`.
-/
open Filter Topology Metric
open Chazelle.EarClip (subPoly n_subPoly vtx_subPoly vtx_subPoly_getD subPoly_rotate subPoly_range)
open Chazelle.Existence (simple_rotate n_rotate vtx_rotate)
section Cyclic
variable {α : Type}

/-- A strict total order given by a relation: transitive, irreflexive, total on distinct
elements. -/
structure StrictTotal (r : α → α → Prop) : Prop where
  trans : ∀ x y z, r x y → r y z → r x z
  irrefl : ∀ x, ¬ r x x
  total : ∀ x y, x ≠ y → r x y ∨ r y x

/-- `ylexLT` is a strict total order. -/
theorem strictTotal_ylexLT : StrictTotal ylexLT :=
  ⟨fun _ _ _ h1 h2 => ylexLT_trans h1 h2, ylexLT_irrefl, fun p q h => by
    rcases ylexLT_trichotomy p q with h' | h' | h'
    · simp_all
    · simp_all
    simp_all⟩

/-- A finite injective sequence has a strictly smallest element. -/
theorem exists_minimal_idx {r : α → α → Prop} (hr : StrictTotal r) {f : ℕ → α} {n : ℕ}
    (hn : 0 < n) (hinj : ∀ i j, i < n → j < n → f i = f j → i = j) :
    ∃ k < n, ∀ j < n, j ≠ k → r zterz (f j) := by
  induction n with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · obtain ⟨k, hk, hmin⟩ := ih hN (fun i j hi hj h => hinj i j by_omega by_omega h)
      have hne : f k ≠ f N := by_grind
      rcases hr.total _ _ hne with h | h
      · refine ⟨k, by_omega, fun j hj hjk => ?_⟩
        grind
      · refine ⟨N, by_omega, fun j hj hjk => ?_⟩
        have hjN : ztgun := by_omega
        by_cases hjk' : j = k
        · grind
        · exact hr.trans _ _ _ h by_grind
variable {n k : ℕ}
/-- Cyclic predecessor is different from the index (for `2 ≤ n`). -/
theorem pred_mod_ne (hn : 2 ≤ n) (hk : k < n) : (k + n - 1) % n ≠ k := by
  zuevc
  · rw [show 0 + n - 1 = n - 1 by omega, Nat.mod_eq_of_lt by_omega]
    omega
  · rw [show k + n - 1 = ztie + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
    omega

/-- Cyclic successor is different from the index (for `2 ≤ n`). -/
theorem succ_mod_ne (hn : 2 ≤ n) (hk : k < n) : zts % n ≠ k := by
  by_cases h : k + 1 = n
  · zuohj; omega
  · zupd
end Cyclic

/-! ### Local extrema and monotone chains of a polygon -/

/-- Vertex `k` of `Q` is a strict `ylexLT`-local minimum: both cyclic neighbours are strictly
greater. -/
def IsLocMin (Q : Polygon) (k : ℕ) : Prop :=
  k < Q.n ∧ ylexLT ztbda ztcha ∧ ylexLT ztbda ztwoh

/-- The vertices `Q.vtx ((a+1) % n), Q.vtx ((a+2) % n), …, Q.vtx a` (all vertices, cyclically,
starting after `a`) are strictly `ylexLT`-increasing. -/
def ChainInc (Q : Polygon) (a : ℕ) : Prop :=
  ∀ p, p + 1 < Q.n → ylexLT ztiqc ztxrz

/-- The vertices `Q.vtx ((a+1) % n), …, Q.vtx a` are strictly `ylexLT`-decreasing. -/
def ChainDec (Q : Polygon) (a : ℕ) : Prop :=
  ∀ p, p + 1 < Q.n → ylexLT ztxrz ztiqc

/-- **`Q` is a monotone mountain with base edge `a`**: `Q` is simple and the chain from vertex
`(a + 1) % n` (the minimum) around to vertex `a` (the maximum) is strictly `ylexLT`-increasing,
so the base edge `a` joins the maximum to the minimum. -/
def IsMountainAt (Q : Polygon) (a : ℕ) : Prop := Q.Simple ∧ a < Q.n ∧ ChainInc Q a

/-- `Q` is a monotone mountain with base edge `a`, in one of the two orientations. -/
def IsMonoAt (Q : Polygon) (a : ℕ) : Prop :=
  Q.Simple ∧ a < Q.n ∧ (ChainInc Q a ∨ ChainDec Q a)

/-- Simplicity transfers back along a rotation. -/
theorem simple_of_simple_rotate {Q : Polygon} {s : ℕ} (h : (Q.rotate s).Simple) : Q.Simple := by
  have e : Q.rotate s = subPoly Q ((List.range Q.n).rotate s) := by
    rw [subPoly_rotate, subPoly_range]
  zudtt
  have := simple_subPoly_of_rotate Q h
  rwa [subPoly_range] at this
variable {Q : Polygon} {P : Polygon} {a b p : Point} {l : List ℕ}
/-- **`IsMountainAt` is the stack algorithm's `IsMountain` after rotation**: the rotation of
`Q` starting at the minimum `(a + 1) % n` is a monotone mountain in the sense of
`Chazelle.Mountain.IsMountain`. -/
theorem isMountainAt_iff {a : ℕ} (ha : a < Q.n) :
    IsMountainAt Q a ↔ IsMountain (Q.rotate ztzze) := by
  have key : ∀ i, i < Q.n → (Q.rotate ztzze).vtx i = Q.vtx ((a + 1 + i) % Q.n) := by
    zug
    rw [vtx_rotate Q _ hi, Nat.mod_add_mod]
  constructor
  · rintro ⟨hQ, -, hc⟩
    refine ⟨simple_rotate Q _ hQ, fun i hi => ?_⟩
    rw [n_rotate] at hi
    rw [key i by_omega, key _ hi]
    exact hc i hi
  · rintro ⟨hR, hc⟩
    refine ⟨simple_of_simple_rotate hR, ha, fun p hp => ?_⟩
    have := hc p by_simp_all
    grind

/-- The global `ylexLT`-minimum of a simple polygon is a strict local minimum. -/
theorem exists_isLocMin (hQ : Q.Simple) :
    ∃ k, IsLocMin Q k ∧ ∀ j < Q.n, j ≠ k → ylexLT ztbda zthrw := by
  have h3 := hQ.1
  obtain ⟨k, hk, hmin⟩ := exists_minimal_idx strictTotal_ylexLT (f := Q.vtx) by_omega
    (fun i j hi hj h => hQ.2.1 i j hi hj h)
  exact ⟨k, ⟨hk, hmin _ ztkcm (pred_mod_ne by_omega hk),
    hmin _ ztcv (succ_mod_ne by_omega hk)⟩, hmin⟩

/-! ### Pieces -/

/-- The cyclic edge `x → y` of an index list is an edge of `P` (in either direction) or an
inserted diagonal (in either orientation). -/
def IsPieceEdge (P : Polygon) (x y : ℕ) : Prop :=
  y = zthf % P.n ∨ x = zthlg % P.n ∨ ztjw ∈ allDiagonals P ∨ ztuen ∈ allDiagonals P

/-- **A piece of the subdivision of `P` by `allDiagonals P`**: a list of at least three distinct
vertex indices whose cyclic edges are edges of `P` or inserted diagonals, spanning a simple
polygon whose interior avoids the boundary of `P` and every inserted diagonal, and whose filled
region lies in that of `P`. -/
structure IsPiece (P : Polygon) (l : List ℕ) : Prop where
  nodup : l.Nodup
  lt : ∀ x ∈ l, x < P.n
  three_le : 3 ≤ l.length
  edges : ∀ k < l.length, IsPieceEdge P ztcak ztbamg
  simple : (subPoly P l).Simple
  not_boundary : ∀ p ∈ interior (subPoly P l).filled, p ∉ P.boundary
  not_diag : ∀ d ∈ allDiagonals P, ∀ p ∈ interior (subPoly P l).filled, p ∉ diagSeg P d
  filled_subset : (subPoly P l).filled ⊆ P.filled

/-- The segment of a piece edge is contained in the boundary of `P` (edge case) or is the
segment of an inserted diagonal. -/
theorem IsPieceEdge.segment_cases {x y : ℕ} (hx : x < P.n) (hy : y < P.n)
    (h : IsPieceEdge P x y) :
    Chazelle.segment ztjlc ztjld ⊆ P.boundary ∨
      ∃ d ∈ allDiagonals P, Chazelle.segment ztjlc ztjld = diagSeg P d := by
  zuzp
  · left; zvmwc; tauto
  · left; zunow; tauto
  · tauto
  · exact Or.inr ⟨_, h, by rw [diagSeg, Geometry.segment_comm]⟩

/-! ### (b) Free points are dense in the interior -/

/-- Every point of a chord is at the height of a vertex. -/
theorem chordUnion_snd {p : Point} (hp : p ∈ chordUnion P) :
    ∃ k < P.n, p.2 = (P.vtx k).2 := by
  zuvd

/-- A finite family of reals has a positive lower bound on its positive members. -/
theorem exists_pos_le_of_pos (f : ℕ → ℝ) (n : ℕ) : ∃ g > 0, ∀ j < n, 0 < f j → g ≤ f j := by
  induction n with
  | zero => exact ⟨1, one_pos, by_omega⟩
  | succ N ih =>
    obtain ⟨g, hg, hle⟩ := ih
    by_cases h : 0 < f N
    · grind
    · grind

/-- **(b) Free points are dense in the interior.**  Every open set containing an interior point
of a simple polygon contains a free point (interior, off every chord); it can be taken directly
above the given point. -/
theorem exists_free_of_isOpen (hP : P.Simple) {U : Set Point} (hU : IsOpen U)
    {z : Point} (hz : z ∈ U) (hzi : z ∈ P.filled \ P.boundary) :
    ∃ p ∈ U, p ∈ freeRegion P ∧ p.1 = z.1 ∧ z.2 < p.2 := by
  have hV : ztsbs := hU.inter ztqrv
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV z ⟨hz, hzi⟩
  have hfin : (((Finset.range P.n).image (fun k => (P.vtx k).2 - z.2) : Finset ℝ) :
      Set ℝ).Finite := Finset.finite_toSet _
  obtain ⟨s, hs, hsnot⟩ := ((Set.Ioo_infinite hε).sdiff hfin).nonempty
  have hmem : (ztgnb : Point) ∈ ball z ε := by
    zucjy
    grind
  refine ⟨ztgnb, by_grind, ztbbk, rfl, by
    simp_all⟩
  zuchg
  zufkg

/-! ### (c) The regions touching a vertex -/

/-- If the point `lerp p v t` (`t < 1`) lies on the segment `[v, c]`, then `p` lies on `[v, c]`
or is at least as far from `v` as `c`. -/
theorem mem_segment_or_far {p v c : Point} {t : ℝ} (ht1 : t < 1)
    (hx : Geometry.lerp p v t ∈ Chazelle.segment v c) :
    p ∈ Chazelle.segment v c ∨ dist c v ≤ dist p v := by
  obtain ⟨s, hs0, hs1, hxs⟩ := hx
  have h1t : 0 < 1 - t := by_linarith
  have e1 : p.1 - v.1 = ztyrq * ztthj := by
    have := congrArg Prod.fst hxs
    zuiov

  have e2 : p.2 - v.2 = ztyrq * ztthk := by
    have := congrArg Prod.snd hxs
    zuiov

  have hμ := div_nonneg hs0 h1t.le
  rcases le_or_gt ztyrq 1 with hle | hgt
  · left
    refine ⟨s / ztca, hμ, hle, ?_⟩
    grind
  · right
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq, e1, e2,
      abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < s / ztca)]
    apply max_le_max <;> nlinarith [abs_nonneg ztthj, abs_nonneg ztthk]

/-- **(c) Every free point near a vertex sees the vertex.**  Around a vertex `v` of a simple
polygon there is a ball such that for every free point `p` in it, `v` lies in the closure of the
region of `p`. -/
theorem exists_ball_vtx_mem_closure (hP : P.Simple) {k : ℕ} (hk : k < P.n) :
    ∃ r > 0, ∀ p ∈ ball ztjr r, p ∈ freeRegion P →
      P.vtx k ∈ closure ztzvj := by
  zuoo
  zucqp

  obtain ⟨r₁, hr₁, hball⟩ := Chazelle.Existence.boundary_near_vtx hP hk
  have hav :=
    dist_pos.2 (simple_vtx_ne hP (prevIdx_lt P hk) hk (prevIdx_ne P hn hk))
  have hbv := dist_pos.2 (simple_vtx_succ_ne hP hk).symm
  obtain ⟨g, hg, hgle⟩ := exists_pos_le_of_pos (fun j => |(P.vtx j).2 - v.2|) P.n
  set r := min (min r₁ zttiz) (min zttja g) with hr
  zufwe
  have hrr₁ : r ≤ r₁ := (min_le_left _ _).trans by_simp_all
  have hra : ztslq := (min_le_left _ _).trans ztgh
  have hrb : ztslr := (min_le_right _ _).trans ztff
  have hrg : r ≤ g := (min_le_right _ _).trans ztgh
  -- the case of a point at a different height
  have key : ∀ p ∈ ball v r, p ∈ freeRegion P → p.2 ≠ v.2 →
      v ∈ closure ztzvj := by
    intro p hp hpf hpy
    zukey
    set S := Geometry.lerp p v '' Ico (0 : ℝ) 1 with hS
    have hSball : ztscl := by
      zupc
      zugca

    have hSb : ∀ x ∈ S, x ∉ P.boundary := by
      zugtf
      rcases hball _ (ball_subset_ball hrr₁ (hSball ⟨t, ht, rfl⟩)) hxb with hx | hx
      · rw [Geometry.segment_comm] at hx
        zuier
        · apply hpf.1.2
          refine ⟨prevIdx P k, prevIdx_lt P hk, ?_⟩
          rw [edge_prevIdx P hk, Geometry.segment_comm]
          zubh
        grind
      · zuier
        · exact hpf.1.2 ⟨k, hk, h⟩
        grind
    have hSc : ztulh :=
      isPreconnected_Ico.image _ (Geometry.continuous_lerp p v).continuousOn
    have hpS : p ∈ S := ⟨0, ztuiz, Geometry.lerp_zero p v⟩
    have hSi :=
      subset_interior_of_isPreconnected hP hSc hSb hpS hpf.1
    have hSf : S ⊆ freeRegion P := by
      zuh
      refine ⟨hSi hx, fun hxc => ?_⟩
      obtain ⟨t, ht, rfl⟩ := hx
      obtain ⟨j, hj, hjy⟩ := chordUnion_snd hxc
      have hxv := hSball ztbik
      rw [mem_ball_iff_abs] at hxv
      have hne : (Geometry.lerp p v t).2 - v.2 ≠ 0 := by
        rw [Geometry.lerp_snd]
        have : p.2 + t * (v.2 - p.2) - v.2 = ztca * (p.2 - v.2) := by_ring
        zubk
        exact mul_ne_zero (by zupdo) (sub_ne_zero.2 hpy)
      have h1 := hgle j hj (by
        show 0 < |(P.vtx j).2 - v.2|
        rw [← hjy]; positivity)
      grind
    have hsub : S ⊆ connectedComponentIn _ p :=
      hSc.subset_connectedComponentIn hpS hSf
    have htend : Tendsto (Geometry.lerp p v) (𝓝[<] 1) (𝓝 v) := by
      have := ((Geometry.continuous_lerp p v).tendsto 1)
      rw [Geometry.lerp_one] at this
      zuhv
    zucyz
    filter_upwards [Ioo_mem_nhdsLT ztja] with t ht
    exact hsub ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩
  refine ⟨r, hr0, fun p hp hpf => ?_⟩
  by_cases hpy : p.2 = v.2
  · -- move up inside the region of `p`
    have hCo : IsOpen (connectedComponentIn _ p) :=
      (isOpen_freeRegion hP).connectedComponentIn
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.1 (hCo.inter isOpen_ball) p
      ⟨mem_connectedComponentIn hpf, hp⟩
    have hp' : ((p.1, p.2 + δ / 2) : Point) ∈ ball p δ := by
      zucjy
      zudlq
      exact ⟨hδ, by rw [abs_of_pos by_linarith]; linarith⟩
    obtain ⟨hp'C, hp'b⟩ := hδsub hp'
    have hp'f := connectedComponentIn_subset _ _ hp'C
    have := key _ hp'b hp'f by_grind
    rwa [← connectedComponentIn_eq hp'C] at this
  grind

/-- **(c) The trapezoid of a free point near a vertex.**  Around a vertex `v = P.vtx k` there is a
ball such that every free point `p` in it has trapezoid data `D` (with `D.q = p`) whose region
contains `p` and has `v` in its closure, and then `k` is a vertex of the closed bottom side or
of the closed top side of the trapezoid. -/
theorem exists_ball_vtx_trapData (hP : P.Simple) {k : ℕ} (hk : k < P.n) :
    ∃ r > 0, ∀ p ∈ ball ztjr r, p ∈ freeRegion P →
      ∃ D : TrapData P, D.q = p ∧ p ∈ D.region ∧ P.vtx k ∈ closure D.region ∧
        (k ∈ sideVtxSet P D.i D.j D.y₁ ∨ k ∈ sideVtxSet P D.i D.j D.y₂) := by
  obtain ⟨r, hr, h⟩ := exists_ball_vtx_mem_closure hP hk
  refine ⟨r, hr, fun p hp hpf => ?_⟩
  obtain ⟨i, j, y₁, y₂, hT, hreg⟩ := exists_isTrap_region_eq hP hpf
  let D : TrapData P := ⟨p, i, j, y₁, y₂, hpf, hT⟩
  have hDreg : D.region = connectedComponentIn _ p := hreg.symm
  have hvc : P.vtx k ∈ closure D.region := by_grind
  exact ⟨D, rfl, hT.q_mem hP hpf.1, hvc, D.vtx_mem_closure_region hk hvc⟩

/-- A vertex in the closure of a region, strictly below one of its points, is on the closed
bottom side. -/
theorem TrapData.mem_bot_of_lt (D : TrapData P) {k : ℕ}
    (hk : k < P.n) (hv : P.vtx k ∈ closure D.region) {p : Point} (hp : p ∈ D.region)
    (hlt : (P.vtx k).2 < p.2) : k ∈ sideVtxSet P D.i D.j D.y₁ := by
  zuidi
  · zubh
  · exfalso
    have := hp.2.1
    zuinj

/-- A vertex in the closure of a region, strictly above one of its points, is on the closed top
side. -/
theorem TrapData.mem_top_of_lt (D : TrapData P) {k : ℕ}
    (hk : k < P.n) (hv : P.vtx k ∈ closure D.region) {p : Point} (hp : p ∈ D.region)
    (hlt : p.2 < (P.vtx k).2) : k ∈ sideVtxSet P D.i D.j D.y₂ := by
  zuidi
  · exfalso
    have := hp.1
    zuinj

  omega

/-! ### (d) The segment attached at a vertex of a side -/

/-- A point of the plane at the height of a vertex set strictly between two abscissae. -/
theorem horiz_mem_segment (ha : a.2 = p.2) (hb : b.2 = p.2)
    (h1 : min a.1 b.1 ≤ p.1) (h2 : p.1 ≤ max a.1 b.1) : p ∈ Chazelle.segment a b := by
  rw [segment_horizontal_eq_hseg ztvuj]
  tauto

/-- **The gap lemma.**  Let `m`, `k` be vertices at the same height `y₀`, `m` to the left of `k`,
with no vertex strictly between them at that height, and suppose that just above (`ε = 1`) or
just below (`ε = -1`) every point strictly between them there are only points of a set `U` of
interior points.  Then `m` and `k` are adjacent (the segment is a horizontal edge), or the segment
is a vertex-to-vertex chord in both directions. -/
theorem gap_adjacent_or_chord (hP : P.Simple) {y₀ ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {U : Set Point} (hU : U ⊆ P.filled \ P.boundary) {m k : ℕ} (hm : m < P.n) (hk : k < P.n)
    (hmy : (P.vtx m).2 = y₀) (hky : (P.vtx k).2 = y₀) (hlt : (P.vtx m).1 < (P.vtx k).1)
    (hnear : ∀ x, (P.vtx m).1 < x → x < (P.vtx k).1 →
      ∀ᶠ p' in 𝓝 (ztcoo : Point), 0 < ε * ztkbz → p' ∈ U)
    (hgap : ∀ j < P.n, (P.vtx j).2 = y₀ → (P.vtx m).1 < (P.vtx j).1 →
      (P.vtx j).1 < (P.vtx k).1 → False) :
    (k = ztbl % P.n ∨ m = zts % P.n) ∨ (zttqf ∈ vtxChords P ∧ (m, k) ∈ vtxChords P) := by
  have hmk : m ≠ k := by_grind
  by_cases hB : ∃ x, (P.vtx m).1 < x ∧ x < (P.vtx k).1 ∧ (ztcoo : Point) ∈ P.boundary
  · -- a boundary point in the gap: the segment is a horizontal edge
    left
    obtain ⟨x, hx1, hx2, hxb⟩ := hB
    have hnv : ∀ j, j < P.n → (ztcoo : Point) ≠ P.vtx j := by
      grind
    obtain ⟨g, hg, t, ht, hxe⟩ := exists_openEdge_of_mem_boundary P hxb hnv
    by_cases hh : NonHoriz P g
    · exact absurd (side_edge_false hε hU rfl by_grind hg hh
        ⟨t, ht, hxe⟩) not_false
    · unfold NonHoriz at hh
      zumin
      set e1 := P.vtx g with he1
      set e2 := P.vtx (ztbs % P.n) with he2
      have hx1e : x = e1.1 + t * (e2.1 - e1.1) := congrArg Prod.fst hxe
      have hy1e : y₀ = e1.2 + t * (e2.2 - e1.2) := congrArg Prod.snd hxe
      have he1y : e1.2 = y₀ := by_grind
      have he2y : e2.2 = y₀ := by_grind
      have hne12 : e1.1 ≠ e2.1 := by
        grind
      have hg1 := succIdx_lt P hg
      -- the endpoints of the edge are not in the gap
      have hout1 : ¬ ((P.vtx m).1 < e1.1 ∧ e1.1 < (P.vtx k).1) :=
        by grind
      have hout2 : ¬ ((P.vtx m).1 < e2.1 ∧ e2.1 < (P.vtx k).1) :=
        by grind
      have hmem : ∀ c : ℕ, c < P.n → (P.vtx c).2 = y₀ →
          (P.vtx m).1 ≤ (P.vtx c).1 → (P.vtx c).1 ≤ (P.vtx k).1 → P.vtx c ∈ P.edge g := by
        intro c hc hcy hc1 hc2
        apply horiz_mem_segment (he1y.trans hcy.symm) (he2y.trans hcy.symm)
        · zujel
          · rw [min_eq_left h12.le]
            zuho

            have : e1.1 < x := by zunun; zupdz
            grind
          · rw [min_eq_right h12.le]
            zuho

            have : e2.1 < x := by zunun; zupea
            grind
        · zujel
          · rw [max_eq_right h12.le]
            zuho

            have : x < e2.1 := by zunun; zupea
            grind
          · rw [max_eq_left h12.le]
            zuho

            have : x < e1.1 := by zunun; zupdz
            grind
      have hkg := (simple_vtx_mem_edge_iff hP hk hg).1 (hmem k hk hky hlt.le le_rfl)
      have hmg := (simple_vtx_mem_edge_iff hP hm hg).1 (hmem m hm hmy le_rfl hlt.le)
      rcases hkg with hkg | hkg <;> rcases hmg with hmg | hmg
      · omega
      · right
        rw [← hkg, hmg, prevIdx_succ P hm]
      · left
        rw [← prevIdx_succ P hk, ← hkg, hmg]
      · exfalso
        apply hmk
        rw [← prevIdx_succ P hm, ← prevIdx_succ P hk, ← hmg, ← hkg]
  · -- no boundary point in the gap: a vertex-to-vertex chord
    right
    zugrf
    have hint : ∀ x, (P.vtx m).1 < x → x < (P.vtx k).1 →
        (ztcoo : Point) ∈ P.filled \ P.boundary := by
      zuetl
      zujfw
      have htend : Tendsto (fun s : ℝ => ((x, y₀ + ε * s) : Point)) (𝓝[>] 0) (𝓝 (x, y₀)) := by
        have hc : Continuous fun s : ℝ => ((x, y₀ + ε * s) : Point) := by fun_prop
        have := hc.tendsto 0
        zubzw
        zuhv
      have hcl : (ztcoo : Point) ∈ closure U := by
        zucyz
        filter_upwards [htend.eventually (hnear x hx1 hx2), self_mem_nhdsWithin] with s hs hs0
        apply hs
        zukfo
        zufbf
        rcases hε with rfl | rfl <;> nlinarith
      exact (isClosed_filled P).closure_subset ztnxa
    have hd : 0 < (P.vtx k).1 - (P.vtx m).1 := by_linarith
    constructor
    · -- the chord of `k` to the left ends at `m`
      have hdir : DirInterior P k (-1) := by
        zuhab

        have : rayPt ztjr (-1) t = (((P.vtx k).1 - t, y₀) : Point) := by
          zugcc
        grind
      have hpar : chordParam P k (-1) = (P.vtx k).1 - (P.vtx m).1 := by
        apply chordParam_eq_of_first P k _ hd
        · have : rayPt ztjr (-1) ztjce = P.vtx m := by
            zudtn
          zvmwk; exact vtx_mem_boundary P hm
        · zuetg
          have : rayPt ztjr (-1) s = (((P.vtx k).1 - s, y₀) : Point) := by
            zugcc
          grind
      refine ⟨hk, hm, -1, Or.inr rfl, hdir, ?_⟩
      zudtm
      simp_all
    · -- the chord of `m` to the right ends at `k`
      have hdir : DirInterior P m 1 := by
        zuhab

        have : rayPt ztdlh 1 t = (((P.vtx m).1 + t, y₀) : Point) := by
          zudtn
        grind
      have hpar : chordParam P m 1 = (P.vtx k).1 - (P.vtx m).1 := by
        apply chordParam_eq_of_first P m 1 hd
        · have : rayPt ztdlh 1 ztjce = P.vtx k := by
            zudtn
          zvmwk; exact vtx_mem_boundary P hk
        · zuetg
          have : rayPt ztdlh 1 s = (((P.vtx m).1 + s, y₀) : Point) := by
            zudtn
          grind
      refine ⟨hm, hk, 1, Or.inl rfl, hdir, ?_⟩
      zudtm
      simp_all

/-- **(d) The attached segment at a vertex of the closed top side.**  If vertex `k` lies on the
closed top side of the trapezoid `D`, some vertex `m` strictly `ylexLT`-below `k` is joined to
`k` by an edge of `P` or an inserted diagonal: when `k` is the top vertex, the bottom vertex
(through the trapezoid diagonal, or the side edge when they are adjacent); otherwise the next
vertex to the left on the top side (through a horizontal edge or a vertex-to-vertex chord). -/
theorem TrapData.attached_top (hP : P.Simple) (D : TrapData P) {k : ℕ}
    (hk : k ∈ sideVtxSet P D.i D.j D.y₂) :
    ∃ m < P.n, ylexLT ztdlh ztjr ∧ IsPieceEdge P k m := by
  by_cases htop : k = D.top
  · subst htop
    refine ⟨D.bot, D.bot_lt hP, ylexLT_of_snd_lt ztuxp, ?_⟩
    zuirs
    · exact Or.inr (Or.inr (Or.inl ztjkp))
    tauto
  · zubpd
    have hkt : (P.vtx D.top).1 < (P.vtx k).1 := by
      refine lt_of_le_of_ne (htmin k hk) (fun h => htop ?_)
      exact simple_vtx_inj hP hk.1 htmem.1
        (Geometry.point_ext h.symm (hk.2.1.trans htmem.2.1.symm))
    set S : Set ℕ := {j | j ∈ sideVtxSet P D.i D.j D.y₂ ∧ (P.vtx j).1 < (P.vtx k).1} with hS
    zuegp
    have hSne : S.Nonempty := ⟨D.top, htmem, hkt⟩
    obtain ⟨hmS, hmmax⟩ := rightmostVtx_spec P hSfin hSne
    set m := rightmostVtx P S with hmdef
    refine ⟨m, hmS.1.1, Or.inr ⟨hmS.1.2.1.trans hk.2.1.symm, hmS.2⟩, ?_⟩
    have hres := gap_adjacent_or_chord hP ztbt zthqw
      hmS.1.1 hk.1 hmS.1.2.1 hk.2.1 hmS.2
      (fun x hx1 hx2 => D.isTrap.near_top (by zupeb) (by zupec))
      (fun j hj hjy hj1 hj2 => by
        have hjS : ztsjt := ⟨⟨hj, hjy, by zupeb, by zupec⟩, hj2⟩
        grind)
    tauto

/-! ### The `ylexLT` half-planes -/

/-- Points of a segment from `a` towards a `ylexLE`-larger point are `ylexLE`-above `a`. -/
theorem ylexLE_of_mem_segment (hab : ylexLE a b)
    (hp : p ∈ Chazelle.segment a b) : ylexLE a p := by
  zufkv
  rcases hab with h | ⟨h1, h2⟩
  · rcases ht0.lt_or_eq with ht | ht
    · left; simp_all
    · right; subst ht; simp
  · right; simp only; constructor
    · simp_all
    · nlinarith

/-- Moving from `x` towards a strictly `ylexLT`-smaller point decreases strictly. -/
theorem ylexLT_lerp_lower {x c : Point} (hc : ylexLT c x) {s : ℝ} (hs : 0 < s) :
    ylexLT (Geometry.lerp x c s) x := by
  rcases hc with h | ⟨h1, h2⟩
  · left; simp only [Geometry.lerp_snd]; nlinarith
  · right; simp only [Geometry.lerp_snd, Geometry.lerp_fst]
    exact ⟨by_simp_all, by_nlinarith⟩

/-- The strict `ylexLT`-lower set of a point is convex. -/
theorem convex_ylexLT_lower (x : Point) : Convex ℝ {y : Point | ylexLT y x} := by
  intro y hy z hz a b ha hb hab
  change ylexLT _ _ at hy
  change ylexLT _ _ at hz
  show (a • y + b • z).2 < x.2 ∨ ((a • y + b • z).2 = x.2 ∧ (a • y + b • z).1 < x.1)
  have e2 : a * x.2 + b * x.2 = x.2 := by_grind
  have e1 : a * x.1 + b * x.1 = x.1 := by_grind
  zucoq
  · zukkw
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rcases hy with hy | ⟨hy1, hy2⟩ <;> rcases hz with hz | ⟨hz1, hz2⟩
      · left
        linarith [mul_lt_mul_of_pos_left hy ha', mul_lt_mul_of_pos_left hz hb']
      · left
        zuntc; linarith [mul_lt_mul_of_pos_left hy ha']
      · left
        rw [hy1]; linarith [mul_lt_mul_of_pos_left hz hb']
      · right
        rw [hy1, hz1]
        exact ⟨e2, by linarith [mul_lt_mul_of_pos_left hy2 ha', mul_lt_mul_of_pos_left hz2 hb']⟩
    · subst hb'
      have : a = 1 := by_linarith
      subst this; simpa [ylexLT] using hy
  · subst ha'
    have : ztplm := by_linarith
    subst this; simpa [ylexLT] using hz

/-- Near a vertex of a simple polygon both of whose neighbours are `ylexLT`-greater, the
`ylexLT`-lower half-ball avoids the boundary. -/
theorem lower_halfBall_not_boundary (hQ : Q.Simple) {k : ℕ} (hk : IsLocMin Q k) :
    ∃ r > 0, ∀ y ∈ ball ztbda r, ylexLT y ztbda → y ∉ Q.boundary := by
  obtain ⟨r, hr, hball⟩ := Chazelle.Existence.boundary_near_vtx hQ hk.1
  refine ⟨r, hr, fun y hy hlt hyb => ?_⟩
  rcases hball y hy hyb with h | h
  · zudto
    exact not_ylexLE_of_ylexLT hlt (ylexLE_of_mem_segment (ylexLE_of_ylexLT hk.2.1) h)
  · exact not_ylexLE_of_ylexLT hlt (ylexLE_of_mem_segment (ylexLE_of_ylexLT hk.2.2) h)

/-! ### Pieces have no reflex local extrema -/

/-- The interior region of a piece lies in the interior region of `P`. -/
theorem IsPiece.interior_subset (hl : IsPiece P l) :
    (subPoly P l).filled \ (subPoly P l).boundary ⊆ P.filled \ P.boundary := by
  zusy
  refine ⟨hl.filled_subset hy.1, hl.not_boundary y ?_⟩
  zuotj
  zulfn

/-- A point of the segment attached at a vertex of a piece that is interior to the piece yields
a contradiction. -/
theorem IsPiece.not_mem_attached (hl : IsPiece P l) {K m : ℕ}
    (hK : K < P.n) (hm : m < P.n) (he : IsPieceEdge P K m) {y : Point}
    (hy : y ∈ Chazelle.segment (P.vtx K) ztdlh)
    (hyi : y ∈ (subPoly P l).filled \ (subPoly P l).boundary) : False := by
  have hyi' : y ∈ interior (subPoly P l).filled := by zuotj; omega
  rcases he.segment_cases hK hm with h | ⟨d, hd, h⟩
  · exact hl.not_boundary y hyi' (h hy)
  · exact hl.not_diag d hd y hyi' by_simp_all

/-- **A piece has no reflex local minimum.**  If vertex `k` of a piece `Q = subPoly P l` is a
strict `ylexLT`-local minimum, then near `Q.vtx k` no point strictly `ylexLT`-below it is
interior to `Q` (the interior of `Q` near a local minimum lies above it).  Otherwise a free point
of `P` just below the vertex lies in a trapezoid having the vertex on its closed top side, and the
attached edge or inserted diagonal (`TrapData.attached_top`) enters the interior of `Q`. -/
theorem IsPiece.locMin_lower_exterior (hP : P.Simple) {l : List ℕ}
    (hl : IsPiece P l) {k : ℕ} (hk : IsLocMin ztdi k) :
    ∃ r > 0, ∀ y ∈ ball ztejh r, ylexLT y ztejh →
      y ∉ (subPoly P l).filled \ (subPoly P l).boundary := by
  zucki
  zueqo
  have hkQ : k < l.length := by have := hk.1; simp_all
  set K := l.getD k 0 with hKdef
  have hK : K < P.n := by
    apply hl.lt
    simp_all
  have hxK := vtx_subPoly_getD P l hkQ
  obtain ⟨r₁, hr₁, hr₁b⟩ := lower_halfBall_not_boundary hQ hk
  obtain ⟨r₂, hr₂, hr₂D⟩ := exists_ball_vtx_trapData hP hK
  refine ⟨min r₁ r₂, by_simp_all, fun y₀ hy₀ hy₀lt hy₀i => ?_⟩
  set x := Q.vtx k with hx
  set r := min r₁ r₂ with hr
  -- the lower half-ball is interior to `Q`
  have hB : ∀ y ∈ ball x r, ylexLT y x → y ∈ Q.filled \ Q.boundary := by
    have hconv := (convex_ball x r).inter (convex_ylexLT_lower x)
    intro y hy hylt
    exact subset_interior_of_isPreconnected hQ hconv.isPreconnected
      (fun z hz => hr₁b z (ball_subset_ball by_grind hz.1) hz.2) by_simp_all hy₀i
      by_simp_all
  -- a free point of `P` just below `x`
  have hWo : IsOpen (ball x r ∩ {y : Point | y.2 < x.2}) :=
    isOpen_ball.inter ztdvc
  have hr0 : ztixt := by_grind
  have hz : ((x.1, x.2 - r / 2) : Point) ∈ ball x r ∩ {y : Point | y.2 < x.2} := by
    refine zthma
    zucjy
    grind
  have hzi :=
    hl.interior_subset (hB _ hz.1 (Or.inl hz.2))
  obtain ⟨p, ⟨hpb, hpy⟩, hpf, -, -⟩ := exists_free_of_isOpen hP hWo hz hzi
  obtain ⟨D, -, hpD, hvD, -⟩ := hr₂D p (by rw [← hxK]; exact ball_subset_ball by_grind hpb) hpf
  have hKtop :=
    D.mem_top_of_lt hK hvD hpD by_grind
  obtain ⟨m, hm, hmlt, hme⟩ := D.attached_top hP hKtop
  rw [← hxK] at hmlt
  -- a point of the attached segment close to `x`
  have htend : Tendsto (Geometry.lerp x (P.vtx m)) (𝓝[>] 0) (𝓝 x) := by
    have := (Geometry.continuous_lerp x ztdlh).tendsto 0
    zugcb
    zuhv
  obtain ⟨s, hsb, hs⟩ := ((htend.eventually (isOpen_ball.mem_nhds ztqtj)).and
    ztxve).exists
  apply hl.not_mem_attached hK hm hme (y := Geometry.lerp x ztdlh s)
  · rw [← hxK]; exact Geometry.lerp_mem_segment _ _ hs.1.le hs.2.le
  · exact hB _ hsb (ylexLT_lerp_lower hmlt hs.1)
end
end Chazelle.Mountain
section
set_option hygiene false
local macro "zqui" : tactic => `(tactic| (obtain ⟨δ, ⟨⟨h1, h2⟩, h3⟩, hδ⟩ := ((htend.eventually hev).and self_mem_nhdsWithin).exists; have hδ' := hδ; have hreg := h1 by_simp_all))
local macro "zquj" : tactic => `(tactic| (refine mem_closure_of_tendsto htend ?_; filter_upwards [nhdsWithin_le_nhds hreg, self_mem_nhdsWithin] with ε hε hε0; refine ⟨hε, fun _ => ?_⟩; rw [hdetf]))
local macro "zquk" : tactic => `(tactic| have hev := ((D.isTrap.near_bot hx1 hx2).and (hopen.mem_nhds hxi)).and (hU.mem_nhds hdet0))
local macro "zqul" : tactic => `(tactic| rcases h with h | h | h | h)
local macro "zqum" : tactic => `(tactic| have hk1 : ztzri := Nat.mod_lt _ by_omega)
local macro "zqun" : tactic => `(tactic| (have := hf.tendsto 0; rw [hf0] at this))
local macro "zquo" : tactic => `(tactic| (obtain ⟨hna, hdet⟩ := D.diag_of_mem_region hP hp.1 hd hpd; have := hp.2 hna; simp_all))
local macro "zqup" : tactic => `(tactic| (by_contra h; push Not at h))
set_option hygiene true

/-!
# Pieces of the mountain decomposition: cells, gaps and boundary recognition

Infrastructure for the proof that every piece of the subdivision of a simple polygon `P` by
`allDiagonals P` is a monotone mountain (`Chazelle.Mountain.PiecesMain`).

Throughout, `l` is a piece (`IsPiece P l`) and `Q = subPoly P l`.

* **Piece segments** (`IsPieceEdge`): a vertex of `P` on a piece segment is one of its endpoints
  (`IsPieceEdge.vtx_eq_of_mem`); two piece segments issued from a common vertex and sharing a
  further point coincide (`IsPieceEdge.eq_of_mem_of_mem`).
* **Boundary recognition** (`IsPiece.nbr_of_boundary`): if the points of a piece segment
  `[P.vtx c, P.vtx w]` issued from the vertex `c` of `Q` (at position `k`) lie on the boundary of
  `Q` near `P.vtx c`, then `P.vtx w` is one of the two neighbours of position `k` in `Q`.
* **Cells** (`TrapData.cellL`, `TrapData.cellR`): the parts of a trapezoid region to the left and
  to the right of its inserted diagonal (the whole region if no diagonal is inserted).  A cell
  meets no boundary point of `Q` (`TrapData.cellL_not_mem_boundaryQ`), so a cell containing an
  interior point of `Q` lies in the interior of `Q` (`TrapData.cellL_subset_intQ`).  The closure
  of a cell contains the points of the closed trapezoid on its side of the diagonal
  (`TrapData.mem_closure_cellL`, …).
* **Gaps** (`TrapData.gap_top`): a portion of the open top side of a trapezoid, free of
  vertices and ending at an interior point of a non-horizontal edge, carries no point of the
  boundary of `P` and no point of an inserted diagonal.
* **The trapezoid above a gap** (`exists_trapData_above`): above an open horizontal segment of
  interior chord points there is a trapezoid whose closed bottom side contains the segment;
  `TrapData.i_eq_of_openEdgePt`, `TrapData.j_eq_of_openEdgePt` identify its side edges.
-/
namespace Chazelle.Mountain
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Visibility
open Chazelle.EarClip (subPoly n_subPoly vtx_subPoly_getD)
open Chazelle.Existence (vtx_mem_boundary)
open Chazelle.Geometry (lerp lerp_fst lerp_snd lerp_zero lerp_one point_ext lerp_mem_segment
  continuous_lerp)
variable {P : Polygon}

/-! ### Piece segments -/

/-- Piece edges are symmetric. -/
theorem IsPieceEdge.symm {x y : ℕ} (h : IsPieceEdge P x y) : IsPieceEdge P y x := by
  zqul
  · tauto
  · tauto
  · tauto
  tauto

/-- The two endpoints of a piece edge are distinct. -/
theorem IsPieceEdge.ne (hP : P.Simple) {x y : ℕ} (hx : x < P.n) (hy : y < P.n)
    (h : IsPieceEdge P x y) : x ≠ y := by
  zuoo
  zqul
  · intro e; subst e; exact succIdx_ne P hn hx h.symm
  · intro e; subst e; exact succIdx_ne P hn hy h.symm
  · exact (allDiagonals_lt hP h).2.2
  · exact fun e => (allDiagonals_lt hP h).2.2 e.symm

/-- The two endpoint points of a piece edge are distinct. -/
theorem IsPieceEdge.vtx_ne (hP : P.Simple) {x y : ℕ} (hx : x < P.n) (hy : y < P.n)
    (h : IsPieceEdge P x y) : P.vtx x ≠ P.vtx y :=
  fun e => h.ne hP hx hy (simple_vtx_inj hP hx hy e)

/-- An allowed diagonal: points of its segment other than its endpoints avoid the boundary. -/
theorem allDiagonals_not_mem_boundary (hP : P.Simple) {d : ℕ × ℕ} (hd : d ∈ allDiagonals P)
    {p : Point} (hp : p ∈ diagSeg P d) (h1 : p ≠ P.vtx d.1) (h2 : p ≠ P.vtx d.2) :
    p ∉ P.boundary := by
  obtain ⟨s, L, hD, hs, hsL, -⟩ := allDiagonals_isDiagonal hP hd
  have := hD.2.2 p (by rw [hs, hsL]; exact hp) by_simp_all by_simp_all
  omega

/-- **A point of a piece segment lying on the boundary of `P` and different from its endpoints
lies on the edge of `P` that the segment is.** -/
theorem IsPieceEdge.edge_of_mem_boundary (hP : P.Simple) {x y : ℕ} (hx : x < P.n) (hy : y < P.n)
    (h : IsPieceEdge P x y) {q : Point} (hq : q ∈ Chazelle.segment ztjlc ztjld)
    (hqx : q ≠ P.vtx x) (hqy : q ≠ P.vtx y) {g : ℕ} (hg : g < P.n) (hqg : q ∈ P.edge g) :
    (x = g ∧ y = ztbs % P.n) ∨ (y = g ∧ x = ztbs % P.n) := by
  zqul
  · -- the segment is edge `x`
    by_cases hxg : x = g
    · simp_all
    · exfalso
      have hq' : q ∈ P.edge x := by unfold Polygon.edge; simp_all
      have := (hP.2.2 x g hx hg hxg).subset ztuib
      zuknb
      · simp_all
      simp_all
  · -- the segment is edge `y`
    by_cases hyg : y = g
    · simp_all
    · exfalso
      have hq' : q ∈ P.edge y := by
        unfold Polygon.edge; rw [← h, Geometry.segment_comm]; exact hq
      have := (hP.2.2 y g hy hg hyg).subset ztuib
      zuknb
      · simp_all
      simp_all
  · exact absurd ztrcn (allDiagonals_not_mem_boundary hP h hq hqx hqy)
  · exact absurd ztrcn (allDiagonals_not_mem_boundary hP h
      (by unfold diagSeg; rw [Geometry.segment_comm]; exact hq) hqy hqx)

/-- **A vertex of `P` on a piece segment is one of its endpoints.** -/
theorem IsPieceEdge.vtx_eq_of_mem (hP : P.Simple) {x y z : ℕ} (hx : x < P.n) (hy : y < P.n)
    (hz : z < P.n) (h : IsPieceEdge P x y)
    (hmem : P.vtx z ∈ Chazelle.segment ztjlc ztjld) : z = x ∨ z = y := by
  zuho

  have h1 := fun e => hcon.1 (simple_vtx_inj hP hz hx e)
  have h2 := fun e => hcon.2 (simple_vtx_inj hP hz hy e)
  rcases h.edge_of_mem_boundary hP hx hy hmem h1 h2 hz ztdte with
    ⟨rfl, -⟩ | ⟨rfl, -⟩
  · omega
  omega

/-- **Two piece segments issued from a common vertex and sharing a further point coincide.** -/
theorem IsPieceEdge.eq_of_mem_of_mem (hP : P.Simple) {c w w' : ℕ} (hc : c < P.n) (hw : w < P.n)
    (hw' : w' < P.n) (h : IsPieceEdge P c w) (h' : IsPieceEdge P c w') {x : Point}
    (hx : x ∈ Chazelle.segment ztyg ztbup) (hx' : x ∈ Chazelle.segment ztyg ztvcq)
    (hxc : x ≠ P.vtx c) : w = w' := by
  zufks
  obtain ⟨s', hs0', hs1', he⟩ := hx'
  set a := P.vtx c
  set b := P.vtx w
  set b' := P.vtx w'
  have e1 : s * ztbco = s' * (b'.1 - a.1) := by
    simp_all
  have e2 : s * ztti = s' * (b'.2 - a.2) := by
    simp_all
  have hs : ztppw := by
    grind
  have hs' : s' ≠ 0 := by
    grind
  have hspos : ztxx := by_grind
  have hspos' : ztrzk := by_grind
  rcases le_total s' s with hle | hle
  · -- `w` lies on the segment `[c, w']`
    have hmem : P.vtx w ∈ Chazelle.segment a b' := by
      refine ⟨s' / s, div_nonneg hspos'.le hspos.le, (div_le_one hspos).2 hle, ?_⟩
      grind
    rcases h'.vtx_eq_of_mem hP hc hw' hw hmem with e | e
    · grind
    omega
  · have hmem : P.vtx w' ∈ Chazelle.segment a b := by
      refine ⟨s / s', div_nonneg hspos.le hspos'.le, (div_le_one hspos').2 hle, ?_⟩
      grind
    rcases h.vtx_eq_of_mem hP hc hw hw' hmem with e | e
    · grind
    omega

/-! ### Pieces: indices and boundary -/
variable {l : List ℕ}
/-- The indices of a piece are vertices of `P`. -/
theorem IsPiece.getD_lt (hl : IsPiece P l) {k : ℕ} (hk : k < l.length) :
    l.getD k 0 < P.n := by
  apply hl.lt
  simp_all

/-- The vertex at position `k` of a piece is the vertex `l.getD k 0` of `P`. -/
theorem IsPiece.vtx_eq {k : ℕ} (hk : k < l.length) :
    (subPoly P l).vtx k = P.vtx ztcak :=
  vtx_subPoly_getD P l hk

/-- The cyclic edge of a piece at position `k` is a piece edge. -/
theorem IsPiece.edge_at (hl : IsPiece P l) {k : ℕ} (hk : k < l.length) :
    IsPieceEdge P ztcak ztbamg :=
  hl.edges k hk

/-- Distinct positions of a piece carry distinct vertices of `P`. -/
theorem IsPiece.getD_inj (hl : IsPiece P l) {k k' : ℕ} (hk : k < l.length)
    (hk' : k' < l.length) (h : l.getD k 0 = l.getD k' 0) : k = k' := by
  rw [EarClip.getD_eq_getElem_of_lt _ _ hk, EarClip.getD_eq_getElem_of_lt _ _ hk'] at h
  exact (List.Nodup.getElem_inj_iff hl.nodup).1 h

/-- A boundary point of a piece lies on the boundary of `P` or on an inserted diagonal. -/
theorem IsPiece.mem_boundary_cases (hl : IsPiece P l) {p : Point}
    (hp : p ∈ (subPoly P l).boundary) :
    p ∈ P.boundary ∨ ∃ d ∈ allDiagonals P, p ∈ diagSeg P d := by
  obtain ⟨k, hk, hpk⟩ := hp
  zvnnk at hk
  zqum
  have he : (subPoly P l).edge k =
      Chazelle.segment ztzcx (P.vtx ztbamg) := by
    zucrd
    rw [n_subPoly, IsPiece.vtx_eq hk, IsPiece.vtx_eq hk1]
  zvmxm at hpk
  rcases (hl.edge_at hk).segment_cases ztmlg ztvvk with h | ⟨d, hd, h⟩
  · grind
  grind

/-- A point of a piece segment in the closure of a set of interior points of `Q` lies on the
boundary of `Q`. -/
theorem IsPiece.mem_boundary_of_closure (hl : IsPiece P l) {S : Set Point}
    (hS : S ⊆ (subPoly P l).filled \ (subPoly P l).boundary) {x y : ℕ} (hx : x < P.n)
    (hy : y < P.n) (he : IsPieceEdge P x y) {q : Point}
    (hq : q ∈ Chazelle.segment ztjlc ztjld) (hcl : q ∈ closure S) :
    q ∈ (subPoly P l).boundary := by
  have hf : q ∈ (subPoly P l).filled :=
    (isClosed_filled _).closure_subset ztnxa
  by_contra hnb
  exact hl.not_mem_attached hx hy he hq by_simp_all

/-- A point of the closure of a set of interior points of `Q` which is on no boundary point of
`Q` is an interior point. -/
theorem IsPiece.mem_int_of_closure {S : Set Point}
    (hS : S ⊆ (subPoly P l).filled \ (subPoly P l).boundary) {q : Point} (hcl : q ∈ closure S)
    (hq : q ∉ (subPoly P l).boundary) : q ∈ (subPoly P l).filled \ (subPoly P l).boundary :=
  ⟨(isClosed_filled _).closure_subset ztnxa, hq⟩

/-- **Boundary recognition.**  Let `c = l.getD k 0` be the vertex at position `k` of the piece,
and `[P.vtx c, P.vtx w]` a piece segment whose points near `P.vtx c` are boundary points of
`Q`.  Then `P.vtx w` is the vertex of `Q` at one of the two positions adjacent to `k`. -/
theorem IsPiece.nbr_of_boundary (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) {k : ℕ}
    (hk : k < l.length) {w : ℕ} (hw : w < P.n) (hpe : IsPieceEdge P ztcak w)
    (hb : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      lerp ztzcx ztbup s ∈ (subPoly P l).boundary) :
    P.vtx w = (subPoly P l).vtx ztwwk ∨
      P.vtx w = (subPoly P l).vtx ztwnc := by
  zucki
  zueqo
  have hkQ : ztsjy := by_simp_all
  have hc := hl.getD_lt hk
  set c := l.getD k 0 with hcdef
  obtain ⟨r, hr, hball⟩ := Chazelle.Existence.boundary_near_vtx hQ hkQ
  have htend : Tendsto (lerp (P.vtx c) (P.vtx w)) (𝓝[>] 0) (𝓝 (P.vtx c)) := by
    have := (continuous_lerp ztyg ztbup).tendsto 0
    zukxh
    zuhv
  obtain ⟨s, ⟨hsb, hsB⟩, hs⟩ := ((htend.eventually (isOpen_ball.mem_nhds
    (show P.vtx c ∈ ball ztyg r from mem_ball_self hr))).and hb |>.and
    ztxve).exists
  have hvk : Q.vtx k = P.vtx c := IsPiece.vtx_eq hk
  have hxc : lerp _ _ s ≠ P.vtx c :=
    lerp_ne_left (hpe.vtx_ne hP hc hw) hs.1
  have hxseg : lerp _ _ s ∈ Chazelle.segment ztyg ztbup :=
    lerp_mem_segment _ _ hs.1.le hs.2.le
  have hsb' : lerp ztyg ztbup s ∈ ball ztbda r := by_simp_all
  rcases hball _ hsb' hsB with h | h
  · -- the previous edge of `Q`
    have hpk : prevIdx Q k < l.length := by
      have := prevIdx_lt Q hkQ; simp_all
    have hsucc : (prevIdx Q k + 1) % l.length = k := by
      have := prevIdx_succ Q hkQ; simp_all
    have hedge := hl.edge_at hpk
    rw [hsucc] at hedge
    rw [IsPiece.vtx_eq hpk, hvk] at h
    rw [IsPiece.vtx_eq hpk]
    left
    zudto
    have := hpe.eq_of_mem_of_mem hP hc hw (hl.getD_lt hpk) hedge.symm hxseg h hxc
    simp_all
  · zqum
    have hedge := hl.edge_at hk
    zudnu
    rw [hQn, IsPiece.vtx_eq hk1, hvk] at h
    rw [IsPiece.vtx_eq hk1]
    right
    have := hpe.eq_of_mem_of_mem hP hc hw ztvvk hedge hxseg h hxc
    simp_all

/-! ### Cells of a trapezoid -/
namespace TrapData

/-- **The left cell** of a trapezoid region: the part of the region strictly to the left of the
inserted diagonal from the bottom vertex to the top vertex (the whole region if the two vertices
are adjacent and no diagonal is inserted). -/
def cellL (D : TrapData P) : Set Point :=
  {p | p ∈ D.region ∧ (D.NonAdj → 0 < det ztsv ztsw p)}

/-- **The right cell** of a trapezoid region: the part strictly to the right of the inserted
diagonal (the whole region if no diagonal is inserted). -/
def cellR (D : TrapData P) : Set Point :=
  {p | p ∈ D.region ∧ (D.NonAdj → det ztsv ztsw p < 0)}

/-- The left cell is convex. -/
theorem convex_cellL (D : TrapData P) : Convex ℝ D.cellL := by
  zucuo
  · have e : D.cellL = D.region ∩ {p | 0 < (1 : ℝ) * det ztsv ztsw p} := by
      zufj
      simp only [cellL, mem_ofPred_eq, mem_inter_iff, one_mul]
      simp_all
    zui
    exact (convex_trapSet P D.i D.j D.y₁ D.y₂).inter zteev
  · have e : D.cellL = D.region := by
      zufj
      simp only [cellL, mem_ofPred_eq]
      simp_all
    zui
    zuitd

/-- The right cell is convex. -/
theorem convex_cellR (D : TrapData P) : Convex ℝ D.cellR := by
  zucuo
  · have e : D.cellR = D.region ∩ {p | 0 < (-1 : ℝ) * det ztsv ztsw p} := by
      zufj
      simp only [cellR, mem_ofPred_eq, mem_inter_iff, neg_one_mul, neg_pos]
      simp_all
    zui
    exact (convex_trapSet P D.i D.j D.y₁ D.y₂).inter ztrnu
  · have e : D.cellR = D.region := by
      zufj
      simp only [cellR, mem_ofPred_eq]
      simp_all
    zui
    zuitd

/-- The determinant against the diagonal, in coordinates. -/
theorem det_bot_top (hP : P.Simple) (D : TrapData P) (p : Point) :
    det ztsv ztsw p =
      ((P.vtx D.top).1 - (P.vtx D.bot).1) * (p.2 - D.y₁) - (p.1 - (P.vtx D.bot).1) * ztjhz := by
  zulbn
  rw [D.top_snd hP, D.bot_snd hP]

/-- **The only inserted diagonal through a point of a region is the region's own diagonal.** -/
theorem diag_of_mem_region (hP : P.Simple) (D : TrapData P) {p : Point} (hp : p ∈ D.region)
    {d : ℕ × ℕ} (hd : d ∈ allDiagonals P) (hpd : p ∈ diagSeg P d) :
    D.NonAdj ∧ det ztsv ztsw p = 0 := by
  zudsc
  · zugov
    rcases D'.segment_cases hP hD' hpd with e | e | e
    · exact absurd by_simp_all (D.not_mem_region_of_vtx hP ztpxc)
    · exact absurd by_simp_all (D.not_mem_region_of_vtx hP ztpxb)
    · have heq :=
        (regions_eq_or_disjoint ztpxd ztuxo).resolve_right
          by_grind
      have hdiag := diag_eq_of_region_eq hP D D' heq
      have ht : D.top = D'.top := congrArg Prod.fst hdiag
      have hb : D.bot = D'.bot := congrArg Prod.snd hdiag
      zujx
      · unfold NonAdj; rw [ht, hb]; tauto
      · have h0 : det (P.vtx D'.top) (P.vtx D'.bot) p = 0 :=
          Geometry.det_eq_zero_of_mem_segment hpd
        rw [ht, hb, Geometry.det_swap12, h0, neg_zero]
  · exfalso
    have hpc : ztuur := ⟨diagSeg P d, vtxChords_diagSeg_mem_chords hd, hpd⟩
    exact (D.region_subset_freeRegion hP hp).2 hpc

/-- A point of the left cell is not a boundary point of a piece. -/
theorem cellL_not_mem_boundaryQ (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P)
    {p : Point} (hp : p ∈ D.cellL) : p ∉ (subPoly P l).boundary := by
  zudzz

  · zuhtv
  · zquo

/-- A point of the right cell is not a boundary point of a piece. -/
theorem cellR_not_mem_boundaryQ (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P)
    {p : Point} (hp : p ∈ D.cellR) : p ∉ (subPoly P l).boundary := by
  zudzz

  · zuhtv
  · zquo

/-- **A left cell containing an interior point of a piece lies in the interior of the piece.** -/
theorem cellL_subset_intQ (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P)
    {p₀ : Point} (hp₀ : p₀ ∈ D.cellL)
    (hi : p₀ ∈ (subPoly P l).filled \ (subPoly P l).boundary) :
    D.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary :=
  subset_interior_of_isPreconnected hl.simple D.convex_cellL.isPreconnected
    (fun _ hx => D.cellL_not_mem_boundaryQ hP hl hx) hp₀ hi

/-- **A right cell containing an interior point of a piece lies in the interior of the
piece.** -/
theorem cellR_subset_intQ (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P)
    {p₀ : Point} (hp₀ : p₀ ∈ D.cellR)
    (hi : p₀ ∈ (subPoly P l).filled \ (subPoly P l).boundary) :
    D.cellR ⊆ (subPoly P l).filled \ (subPoly P l).boundary :=
  subset_interior_of_isPreconnected hl.simple D.convex_cellR.isPreconnected
    (fun _ hx => D.cellR_not_mem_boundaryQ hP hl hx) hp₀ hi
end TrapData

/-! ### Closures of regions and cells -/

/-- A convex combination of a point of the closed trapezoid and a point of the open trapezoid,
with positive weight on the latter, lies in the open trapezoid. -/
theorem lerp_mem_trapSet {i j : ℕ} {y₁ y₂ : ℝ} {z w : Point}
    (hz : z ∈ closedTrap P i j y₁ y₂) (hw : w ∈ trapSet P i j y₁ y₂) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1) : lerp z w s ∈ trapSet P i j y₁ y₂ := by
  obtain ⟨z1, z2, z3, z4⟩ := hz
  obtain ⟨w1, w2, w3, w4⟩ := hw
  have e2 : (lerp z w s).2 = zteb * z.2 + s * w.2 := by simp only [lerp_snd]; ring
  have e1 : (lerp z w s).1 = zteb * z.1 + s * w.1 := by simp only [lerp_fst]; ring
  have hs' : 0 ≤ 1 - s := by_linarith
  zudfi
  · show y₁ < (lerp z w s).2
    zucjj
    nlinarith [mul_nonneg hs' (sub_nonneg.2 z1), mul_pos hs0 (sub_pos.2 w1)]
  · show (lerp z w s).2 < y₂
    zucjj
    nlinarith [mul_nonneg hs' (sub_nonneg.2 z2), mul_pos hs0 (sub_pos.2 w2)]
  · show edgeX P i (lerp z w s).2 < (lerp z w s).1
    rw [e2, edgeX_combo P i by_simp_all, e1]
    nlinarith [mul_nonneg hs' (sub_nonneg.2 z3), mul_pos hs0 (sub_pos.2 w3)]
  · show (lerp z w s).1 < edgeX P j (lerp z w s).2
    rw [e2, edgeX_combo P j by_simp_all, e1]
    nlinarith [mul_nonneg hs' (sub_nonneg.2 z4), mul_pos hs0 (sub_pos.2 w4)]
namespace TrapData

/-- **The closed trapezoid lies in the closure of the region.** -/
theorem closedTrap_subset_closure (hP : P.Simple) (D : TrapData P) :
    closedTrap P D.i D.j D.y₁ D.y₂ ⊆ closure D.region := by
  zugh
  have hw := D.isTrap.q_mem hP D.free.1
  have htend : Tendsto (lerp z D.q) (𝓝[>] 0) (𝓝 z) := by
    have := (continuous_lerp z D.q).tendsto 0
    zukxh
    zuhv
  zucyz
  zuhus
  exact lerp_mem_trapSet hz hw hs.1 hs.2.le

/-- A point of the closed trapezoid strictly to the left of the diagonal is in the closure of
the left cell. -/
theorem mem_closure_cellL (hP : P.Simple) (D : TrapData P) {z : Point}
    (hz : z ∈ closedTrap P D.i D.j D.y₁ D.y₂)
    (hdet : D.NonAdj → 0 < det ztsv ztsw z) : z ∈ closure D.cellL := by
  zucuo
  · have hU : ztxtb := by
      have := isOpen_det_pos ztsv ztsw 1
      simp_all
    have := hU.inter_closure ztpfn
    have hsub : {p : Point | 0 < det _ _ p} ∩ D.region ⊆ D.cellL :=
      fun p hp => ztpfq
    zulyd
  · have hsub : D.region ⊆ D.cellL := fun p hp => ztuht
    zulye

/-- A point of the closed trapezoid strictly to the right of the diagonal is in the closure of
the right cell. -/
theorem mem_closure_cellR (hP : P.Simple) (D : TrapData P) {z : Point}
    (hz : z ∈ closedTrap P D.i D.j D.y₁ D.y₂)
    (hdet : D.NonAdj → det ztsv ztsw z < 0) : z ∈ closure D.cellR := by
  zucuo
  · have hU : ztxtc := by
      have := isOpen_det_pos ztsv ztsw (-1)
      simp_all
    have := hU.inter_closure ztpfn
    have hsub : {p : Point | det _ _ p < 0} ∩ D.region ⊆ D.cellR :=
      fun p hp => ztpfq
    zulyd
  · have hsub : D.region ⊆ D.cellR := fun p hp => ztuht
    zulye

/-- A point of the region on the line of the diagonal is in the closure of both cells. -/
theorem mem_closure_cells_of_region (hP : P.Simple) (D : TrapData P) {z : Point}
    (hz : z ∈ D.region) (hdet : det ztsv ztsw z = 0) :
    z ∈ closure D.cellL ∧ z ∈ closure D.cellR := by
  zucuo
  · set b := P.vtx D.bot
    set t := P.vtx D.top
    have hbt : 0 < t.2 - b.2 := by
      have := D.bot_snd_lt_top_snd hP; linarith
    set L := ztubv ^ 2 + ztubw ^ 2 with hL
    have hLpos : ztrze := by_positivity
    let f : ℝ → Point := fun ε => (z.1 - ε * ztubw, z.2 + ε * ztubv)
    zuhyo
    have hf0 : f 0 = z := by simp [f]
    have hdetf : ∀ ε, det b t ztvqg = ε * L := by
      intro ε
      have e : det b t ztvqg = det b t z + ε * L := by
        simp only [f, det, hL]; ring
      simp_all
    have hreg : ∀ᶠ ε in 𝓝 (0 : ℝ), f ε ∈ D.region := by
      zqun
      exact this.eventually ((isOpen_trapSet P D.i D.j D.y₁ D.y₂).mem_nhds hz)
    constructor
    · have htend : Tendsto f (𝓝[>] 0) (𝓝 z) := by
        zqun
        zuhv
      zquj
      simp_all
    · have htend : Tendsto f (𝓝[<] 0) (𝓝 z) := by
        zqun
        zuhv
      zquj
      exact mul_neg_of_neg_of_pos hε0 hLpos
  · exact ⟨subset_closure ztuis, subset_closure ztuis⟩

/-- A point of the region on the line of the diagonal lies on the diagonal. -/
theorem mem_diagSeg_of_det (hP : P.Simple) (D : TrapData P) {z : Point} (hz : z ∈ D.region)
    (hdet : det ztsv ztsw z = 0) : z ∈ diagSeg P D.diag := by
  zuljs
  zuesj
  zuhw
  have hz1 := hz.1
  have hz2 := hz.2.1
  rw [D.det_bot_top hP] at hdet
  set s := (D.y₂ - z.2) / ztjhz with hs
  have hne : D.y₂ - D.y₁ ≠ 0 := by_linarith
  refine ⟨s, div_nonneg by_linarith by_linarith, (div_le_one by_linarith).2 by_linarith,
    ?_⟩
  zudtm
  simp only [diag, ht2, hb2]
  grind

/-- On the open left and right side edges, the determinant against the diagonal has the sign of
the corresponding cell. -/
theorem det_side (hP : P.Simple) (D : TrapData P) (hna : D.NonAdj) {h : ℝ} (h1 : D.y₁ < h)
    (h2 : h < D.y₂) :
    0 < det ztsv ztsw ztpas ∧
      det ztsv ztsw ztpau < 0 := by
  zuljs
  zuesj
  set s := (D.y₂ - h) / ztjhz with hs
  have hne : 0 < D.y₂ - D.y₁ := by_linarith
  zucmo
  have hs1 : ztdrm := (div_lt_one hne).2 by_linarith
  set d := lerp ztsw ztsv s with hd'
  have hd : d ∈ D.region := D.isTrap.diag_lerp_mem_trapSet hP D.free hna.1 hna.2 hs0 hs1
  have hd2 : d.2 = h := by
    rw [hd', lerp_snd]
    grind
  have hdet0 : det ztsv ztsw d = 0 := by
    rw [Geometry.det_swap12]
    rw [Geometry.det_eq_zero_of_mem_segment (lerp_mem_segment _ _ hs0.le hs1.le), neg_zero]
  have key : ∀ X : ℝ, det ztsv ztsw zttee = (d.1 - X) * ztjhz := by
    intro X
    have e1 := D.det_bot_top hP zttee
    have e2 := D.det_bot_top hP d
    grind
  have hdi : edgeX P D.i h < d.1 := by
    have := hd.2.2.1; simp_all
  have hdj : d.1 < edgeX P D.j h := by
    have := hd.2.2.2; simp_all
  zujx
  · simp_all
  · rw [key]; exact mul_neg_of_neg_of_pos by_linarith hne
end TrapData

/-! ### Gaps on the top side -/

/-- If a point strictly between two abscissae `a < x < b` lies on a horizontal segment whose
endpoints are not strictly between `a` and `b` and differ from the point, then the segment
contains the points of abscissae `a` and `b`. -/
theorem horiz_seg_ends {u w : Point} {y a b x : ℝ} (hu : u.2 = y) (hw : w.2 = y)
    (hx : (ztjw : Point) ∈ Chazelle.segment u w) (hxu : x ≠ u.1) (hxw : x ≠ w.1)
    (hua : ¬ (a < u.1 ∧ u.1 < b)) (hwa : ¬ (a < w.1 ∧ w.1 < b)) (hx1 : a < x) (hx2 : x < b) :
    (ztdv : Point) ∈ Chazelle.segment u w ∧ (ztdy : Point) ∈ Chazelle.segment u w := by
  have huw := hu.trans hw.symm
  rw [segment_horizontal_eq_hseg huw] at hx ⊢
  obtain ⟨-, hx3, hx4⟩ := hx
  simp only at hx3 hx4
  have hmin : min u.1 w.1 ≤ a := by
    grind
  have hmax : b ≤ max u.1 w.1 := by
    grind
  exact ⟨⟨by_simp_all, hmin, by_linarith⟩, ⟨by_simp_all, by_linarith, hmax⟩⟩
namespace TrapData

/-- **Gap lemma (top side).**  Let `(a, b) × {y₂}` be a portion of the closed top side of a
trapezoid carrying no vertex of `P`, one of whose ends is an interior point of a
non-horizontal edge `e`.  Then its points are not on the boundary of `P`, are chord points,
and lie on no inserted diagonal. -/
theorem gap_top (hP : P.Simple) (D : TrapData P) {a b : ℝ}
    (ha : edgeX P D.i D.y₂ ≤ a) (hb : b ≤ edgeX P D.j D.y₂)
    (hnov : ∀ k, k < P.n → (P.vtx k).2 = D.y₂ → a < (P.vtx k).1 → (P.vtx k).1 < b → False)
    {e : ℕ} (he : e < P.n) (hnh : NonHoriz P e)
    (hend : OpenEdgePt P e zttes ∨ OpenEdgePt P e zttfn)
    {x : ℝ} (hx1 : a < x) (hx2 : x < b) :
    (ztbnt : Point) ∉ P.boundary ∧ (ztbnt : Point) ∈ chordUnion P ∧
      ∀ d ∈ allDiagonals P, (ztbnt : Point) ∉ diagSeg P d := by
  have hnv : ∀ k, k < P.n → (ztbnt : Point) ≠ P.vtx k := by
    grind
  have hi : edgeX P D.i D.y₂ < x := by_grind
  have hj : x < edgeX P D.j D.y₂ := by_grind
  -- the end point on `e` lies on no horizontal segment through the gap which is an edge
  have hXb : (ztbnt : Point) ∉ P.boundary := by
    intro hXb
    obtain ⟨g, hg, t, ht, hXe⟩ := exists_openEdge_of_mem_boundary P hXb hnv
    have hoe : OpenEdgePt P g ztbnt := ⟨t, ht, hXe⟩
    by_cases hgh : NonHoriz P g
    · exact side_edge_false ztbt zthqw rfl
        (D.isTrap.near_top hi hj) hg hgh hoe
    · unfold NonHoriz at hgh
      push Not at hgh
      have hy : D.y₂ = (P.vtx g).2 := by
        have := congrArg Prod.snd hXe
        simp_all
      have hu2 := hy.symm
      have hw2 : (P.vtx _).2 = D.y₂ := hgh ▸ hu2
      have hXs : (ztbnt : Point) ∈ Chazelle.segment _ _ :=
        hoe.mem_edge
      have hxu : x ≠ (P.vtx g).1 := by_grind
      have hxw : x ≠ (P.vtx _).1 := fun h =>
        hnv _ ztubl (point_ext h (hw2.symm))
      have ends := horiz_seg_ends hu2 hw2 hXs hxu hxw
        by_grind (fun h => hnov _ ztubl hw2 h.1 h.2) hx1 hx2
      have hge : g ≠ e := by
        zudsz
      zuklg
      · exact hoe'.not_mem_other hP he hg hge ends.1
      · exact hoe'.not_mem_other hP he hg hge ends.2
  have hXc :=
    (D.isTrap.top_side hP D.free hi hj).resolve_left hXb
  refine ⟨hXb, hXc, ?_⟩
  intro d hd hXd
  zudsc
  · zugov
    rcases D'.segment_cases hP hD' hXd with h | h | h
    · exact hnv _ ztpxc h
    · exact hnv _ ztpxb h
    · exact (D'.region_subset_freeRegion hP h).2 hXc
  · have hsnd := vtxChords_snd_eq hd
    have hd1 := hd.1
    have hd2 := hd.2.1
    have hy : (P.vtx d.1).2 = D.y₂ := by
      obtain ⟨t, -, -, h⟩ := hXd
      simp_all
    have hy' : (P.vtx d.2).2 = D.y₂ := by_simp_all
    have hxu : x ≠ (P.vtx d.1).1 := by_grind
    have hxw : x ≠ (P.vtx d.2).1 := by_grind
    have ends := horiz_seg_ends hy hy' hXd hxu hxw by_simp_all
      by_simp_all hx1 hx2
    zuklg
    · exact allDiagonals_not_mem_boundary hP ztvch ends.1 ztrrx
        ztrry ztvvv
    · exact allDiagonals_not_mem_boundary hP ztvch ends.2 ztrrx
        ztrry ztvvv

/-- If an interior point `(a, y₁)` of a non-horizontal edge `e` lies on the closed bottom side of
a trapezoid, strictly left of its right end, it is the left corner and `e` is the left side
edge. -/
theorem i_eq_of_openEdgePt (hP : P.Simple) (D : TrapData P) {a : ℝ}
    (hle : edgeX P D.i D.y₁ ≤ a) (hlt : a < edgeX P D.j D.y₁) {e : ℕ} (he : e < P.n)
    (hnh : NonHoriz P e) (hoe : OpenEdgePt P e ztnqt) : D.i = e := by
  zubug
  · exact absurd (side_edge_false ztp zthqw rfl
      (D.isTrap.near_bot h hlt) he hnh hoe) not_false
  · have hmem : (ztnqt : Point) ∈ P.edge D.i :=
      D.isTrap.mem_edgeL le_rfl (D.isTrap.bot_lt.trans D.isTrap.lt_top).le h.symm
    zuct
    exact hoe.not_mem_other hP he D.isTrap.hi hne hmem

/-- If an interior point `(b, y₁)` of a non-horizontal edge `e` lies on the closed bottom side of
a trapezoid, strictly right of its left end, it is the right corner and `e` is the right side
edge. -/
theorem j_eq_of_openEdgePt (hP : P.Simple) (D : TrapData P) {b : ℝ}
    (hlt : edgeX P D.i D.y₁ < b) (hle : b ≤ edgeX P D.j D.y₁) {e : ℕ} (he : e < P.n)
    (hnh : NonHoriz P e) (hoe : OpenEdgePt P e ztnrq) : D.j = e := by
  zubug
  · exact absurd (side_edge_false ztp zthqw rfl
      (D.isTrap.near_bot hlt h) he hnh hoe) not_false
  · have hmem : (ztnrq : Point) ∈ P.edge D.j :=
      D.isTrap.mem_edgeR le_rfl (D.isTrap.bot_lt.trans D.isTrap.lt_top).le h
    zuct
    exact hoe.not_mem_other hP he D.isTrap.hj hne hmem

/-- **Left cell above a bottom point.**  If the point `(x, y₁)` of the open bottom side, strictly
left of the bottom vertex, is an interior point of a piece, the left cell lies in the interior
of the piece. -/
theorem cellL_subset_of_bot (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P)
    {x : ℝ} (hx1 : edgeX P D.i D.y₁ < x) (hx2 : x < edgeX P D.j D.y₁)
    (hxb : x < (P.vtx D.bot).1)
    (hxi : (ztbqn : Point) ∈ (subPoly P l).filled \ (subPoly P l).boundary) :
    D.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary := by
  zulky
  zuhw
  have hdet0 : 0 < det ztsv ztsw ztbqn := by
    rw [D.det_bot_top hP]; zunxh; nlinarith
  have hU : ztxtb := by
    have := isOpen_det_pos ztsv ztsw 1
    simp_all
  zquk
  have htend : Tendsto (fun δ : ℝ => ((x, D.y₁ + δ) : Point)) (𝓝[>] 0) (𝓝 (x, D.y₁)) := by
    zudhl
    have := hc.tendsto 0
    zufbg
    zuhv
  zqui
  exact D.cellL_subset_intQ hP hl ztuid h2

/-- **Right cell above a bottom point.**  If the point `(x, y₁)` of the open bottom side, strictly
right of the bottom vertex, is an interior point of a piece, the right cell lies in the
interior of the piece. -/
theorem cellR_subset_of_bot (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P)
    {x : ℝ} (hx1 : edgeX P D.i D.y₁ < x) (hx2 : x < edgeX P D.j D.y₁)
    (hxb : (P.vtx D.bot).1 < x)
    (hxi : (ztbqn : Point) ∈ (subPoly P l).filled \ (subPoly P l).boundary) :
    D.cellR ⊆ (subPoly P l).filled \ (subPoly P l).boundary := by
  zulky
  zuhw
  have hdet0 : det ztsv ztsw ztbqn < 0 := by
    rw [D.det_bot_top hP]; simp_all
  have hU : ztxtc := by
    have := isOpen_det_pos ztsv ztsw (-1)
    simp_all
  zquk
  have htend : Tendsto (fun δ : ℝ => ((x, D.y₁ + δ) : Point)) (𝓝[>] 0) (𝓝 (x, D.y₁)) := by
    zudhl
    have := hc.tendsto 0
    zufbg
    zuhv
  zqui
  exact D.cellR_subset_intQ hP hl ztuid h2
end TrapData

/-- **The trapezoid above a horizontal segment of interior chord points.**  If every point of
the open segment `(a, b) × {y₀}` is an interior chord point of `P`, some trapezoid has bottom
height `y₀` and a closed bottom side containing the segment. -/
theorem exists_trapData_above (hP : P.Simple) {y₀ a b : ℝ} (hab : a < b)
    (hint : ∀ x, a < x → x < b → (ztcoo : Point) ∈ P.filled \ P.boundary)
    (hch : ∀ x, a < x → x < b → (ztcoo : Point) ∈ chordUnion P) :
    ∃ D : TrapData P, D.y₁ = y₀ ∧ edgeX P D.i y₀ ≤ a ∧ b ≤ edgeX P D.j y₀ := by
  set x₀ := ztth / 2 with hx₀
  have hxa : a < x₀ := by_grind
  have hxb : x₀ < b := by_grind
  set z : Point := (x₀, y₀) with hz
  have hzi : ztsnl := by_simp_all
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 ztqrv z hzi
  obtain ⟨g, hg, hgle⟩ := exists_pos_le_of_pos (fun k => (P.vtx k).2 - y₀) P.n
  set U := ball z ρ ∩ {p : Point | p.2 < y₀ + g} with hU
  have hUo : ztule := isOpen_ball.inter ztdvc
  have hzU : ztmxh := by_simp_all
  obtain ⟨q, ⟨hqb, hqg⟩, hqf, hq1, hq2⟩ := exists_free_of_isOpen hP hUo hzU hzi
  simp only [hz] at hq1 hq2
  obtain ⟨i, j, y₁, y₂, hT, hreg⟩ := exists_isTrap_region_eq hP hqf
  let D : TrapData P := ⟨q, i, j, y₁, y₂, hqf, hT⟩
  have hDreg : D.region = trapSet P i j y₁ y₂ := rfl
  -- the vertical segment from `z` up to `q` lies in the region
  have hV : ∀ y, y₀ < y → y ≤ q.2 → (ztfvj : Point) ∈ trapSet P i j y₁ y₂ := by
    set V := (fun y : ℝ => (ztfvj : Point)) '' Ioc y₀ q.2 with hVdef
    have hVc : IsPreconnected V :=
      isPreconnected_Ioc.image _ (by fun_prop : Continuous fun y : ℝ => (ztfvj : Point)).continuousOn
    have hqV : q ∈ V := by_grind
    have hVf : V ⊆ freeRegion P := by
      rintro _ ⟨y, hy, rfl⟩
      have hyb : (ztfvj : Point) ∈ ball z ρ := by
        zucjy
        have hqb' := hqb
        rw [mem_ball_iff_abs] at hqb'
        simp only [hz, sub_self, abs_zero] at hqb' ⊢
        refine ⟨hρ, ?_⟩
        rw [abs_of_pos by_grind]
        have := hqb'.2
        rw [abs_of_pos by_linarith] at this
        grind
      refine ⟨hball hyb, fun hc => ?_⟩
      zufkg

    have hsub : V ⊆ connectedComponentIn _ q :=
      hVc.subset_connectedComponentIn hqV hVf
    grind
  have hy1le : y₁ ≤ y₀ := by
    zqup
    have := hV (min q.2 y₁) by_grind by_grind
    exact absurd this.1 by_grind
  -- the point `z` is in the closure of the region
  have hzc : z ∈ closure ztbku := by
    have htend : Tendsto (fun y : ℝ => ((x₀, y) : Point)) (𝓝[>] y₀) (𝓝 z) := by
      have hc : Continuous fun y : ℝ => (ztfvj : Point) := by fun_prop
      exact (hc.tendsto y₀).mono_left nhdsWithin_le_nhds
    zucyz
    filter_upwards [Ioo_mem_nhdsGT hq2] with y hy
    grind
  obtain ⟨hc1, hc2, hc3, hc4⟩ := closure_trapSet_subset P i j y₁ y₂ hzc
  simp only [hz] at hc1 hc2 hc3 hc4
  have hy1ge : y₀ ≤ y₁ := by
    zqup
    have hL : edgeX P i y₀ < x₀ := by
      refine lt_of_le_of_ne hc3 (fun e => hzi.2 ⟨i, hT.hi, ?_⟩)
      exact hT.mem_edgeL h.le hc2 e.symm
    have hR : x₀ < edgeX P j y₀ := by
      refine lt_of_le_of_ne hc4 (fun e => hzi.2 ⟨j, hT.hj, ?_⟩)
      exact hT.mem_edgeR h.le hc2 e
    have hmem : z ∈ trapSet P i j y₁ y₂ := ⟨h, lt_of_lt_of_le hq2 hT.lt_top.le |>.trans_le le_rfl
      |> fun h' => by_omega, hL, hR⟩
    exact (hT.trapSet_subset_freeRegion hP hqf hmem).2 by_grind
  have hy : y₁ = y₀ := by_grind
  refine ⟨D, hy, ?_, ?_⟩
  · show edgeX P i y₀ ≤ a
    zqup
    have hX : ((edgeX P i y₀, y₀) : Point) ∈ P.boundary :=
      ⟨i, hT.hi, hT.mem_edgeL ztqfe by_omega rfl⟩
    grind
  · show b ≤ edgeX P j y₀
    zqup
    have hX : ((edgeX P j y₀, y₀) : Point) ∈ P.boundary :=
      ⟨j, hT.hj, hT.mem_edgeR ztqfe by_omega rfl⟩
    grind
