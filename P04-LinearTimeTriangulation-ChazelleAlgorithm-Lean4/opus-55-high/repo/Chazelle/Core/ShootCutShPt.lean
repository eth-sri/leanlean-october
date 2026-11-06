module

public import Chazelle.MacT
public import Chazelle.Core.ShootCutCore2
public import Chazelle.Core.ShootCutLoop2
public import Chazelle.Core.DownPhaseDrvTPiece
public import Chazelle.Core.NFBuildArcs
public import Chazelle.Core.DownPhaseRegionBox
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.DownPhaseDrvRExtSpec
public import Chazelle.Core.SpecNF

section
set_option hygiene false
local macro "zqbfy" : tactic => `(tactic| (rw [Model.pos_snd hne]
                                           obtain ⟨h', rfl⟩ : ztfeb := ztdqr
                                           rfl))
local macro "zqbfz" : tactic => `(tactic| (exec_block
                                           all_goals first | omega | skip))
local macro "zqbga" : tactic => `(tactic| obtain ⟨c', k, ex, hk, pr⟩ := ptTopV_exec c hE)
set_option hygiene true

/-!
# WP-G, part 40: the point record of a walk position (`ptKey`)

The ray-shooter compares the points of walk positions of a chain model with the origin of the
ray: abscissae and ordinates.  The primitive `ptKey` (calling convention of the sweep primitives,
`SweepPrim.prim_meets`) takes a walk position `x = (e, h)` of `chainModel C` (`50201`, `50202`)
and returns in `50210 …` a **point record** of its point `z`:

* `50210 … 50213`: an abscissa record of `z.1` (`SweepPrim.AbsRec`);
* `50214`, `50215`: an **ordinate record** of `z.2` (`HRec`): kind `0` (`-R`), `2` (`R`), or `1`
  and a vertex of `Q` at the height of `z` (`|z.2| < R`);
* `50216 … 50219`: flag `1` and a symbolic point of `Q` whose point is `z` (for a vertex of the
  chain and a point inside a tour edge), or flag `0` (the box and the slit).

The input may be a vertex of the box (height code `0`), or any position of the walk proper
strictly inside the height range of the box.
-/
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
open Chazelle.Chain (sidePt)
@[expose] public section
def HRec (P : Polygon) (c : Config) (r : ℕ) (y R : ℝ) : Prop :=
  ztllu ∨ ztmhb ∨
    (c.nreg r = 1 ∧ |y| < R ∧ c.nreg ztgu < P.n ∧ y = ((Qof P).vtx (c.nreg ztgu)).2)

/-- **A symbolic record** at `r`: flag `1` and a symbolic point of `Q` whose point is `z`. -/
def FRec (P : Polygon) (c : Config) (r : ℕ) (z : Point) : Prop :=
  c.nreg r = 1 → ∃ s : SymPt, SymPtIn c ztgu s ∧ s.Lt P.n ∧ s.eval zta = z

/-- The point record of `z` at `50210`. -/
def PtRec (P : Polygon) (c : Config) (z : Point) (R : ℝ) : Prop :=
  AbsRec P c 50210 z.1 R ∧ HRec P c 50214 z.2 R ∧ FRec P c 50216 z
theorem absRec_copy' {P : Polygon} {c c' : Config} {r r' : ℕ} {x R : ℝ} (h : AbsRec P c r x R)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg ztcwh = c.nreg ztgu)
    (h2 : c'.nreg ztcwi = c.nreg ztbcu) (h3 : c'.nreg ztkdl = c.nreg ztkdd) :
    AbsRec P c' r' x R := by
  zufk

  · simp_all
  · simp_all
  · zuia

/-! ## The machine -/

/-- The ordinate kind and the symbolic flag of a box vertex. -/
def hyV (k : ℕ) : Stmt := block [.constN 50214 k, .constN 50216 0]

/-- A vertex of the box on the line of the slit (`0` or `5`). -/
def ptTopV : Stmt := .seq absTop (hyV 2)

/-- A box corner: constant abscissa and ordinate kinds. -/
def hxy (x y : ℕ) : Stmt := block [.constN 50210 x, .constN 50214 y, .constN 50216 0]

/-- The vertices of the box (`e < 6`, code `0`). -/
def ptBoxV : Stmt :=
  .ifLtN 50201 50032 ptTopV
    (.ifLtN 50201 50082 (hxy 0 2)
      (.ifLtN 50201 50083 (hxy 0 0)
        (.ifLtN 50201 50084 (hxy 2 0)
          (.ifLtN 50201 50085 (hxy 2 2) ptTopV))))

/-- A position inside a vertical edge of the box block (`1`, `3`, `5`). -/
def ptBoxS : Stmt :=
  .seq (block [.constN 50214 1, .subN 50215 50202 50032, .constN 50216 0])
    (.ifLtN 50201 50082 ztbki
      ztzae)

/-- A vertex of the tour. -/
def ptVtx : Stmt :=
  .seq ztbdp (.seq ztqxt
    (.seq (block [.constN 50210 1, .copyN 50217 50211, .copyN 50218 50212, .copyN 50219 50213,
        .constN 50216 1, .constN 50214 1])
      (.ifLtN 50211 50032 ztovq ztovr)))

/-- The ordinate of a position inside a walk edge, and its symbolic flag. -/
def hyI (f : ℕ) : Stmt := block [.constN 50214 1, .subN 50215 50202 50032, .constN 50216 f]

/-- Inside a tour edge. -/
def ptTour : Stmt :=
  .seq absTour (.seq (hyI 1)
    (block (copies [ztstw, ztstx, ztsty])))

/-- Inside a tour edge or the up-slit edge. -/
def ptInt : Stmt :=
  .seq ztiri
    (.ifLtN 50120 50143 ptTour (.seq absTop (hyI 0)))

/-- **The primitive `ptKey`.** -/
def ptKey : Stmt :=
  .seq pHead (.ifLtN 50201 50081 (.ifLtN 50202 50032 ptBoxV ptBoxS) (classify .skip ptVtx ptInt))
theorem wr_ptKey : wr Bprim ptKey = true := by_decide

/-! ## The box vertices -/
variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain}
variable (c : Config)
theorem hyV_exec (hw : WordsBounded W c) (hW : 3 ≤ W) {k : ℕ} (hk : k ≤ 2) :
    ∃ c' k', Exec P W (hyV k) c c' k' ∧ k' = 2 ∧ c'.nreg 50214 = k ∧ c'.nreg 50216 = 0 ∧
      ∀ r, r ≠ 50214 → r ≠ 50216 → c'.nreg r = c.nreg r := by
  unfold hyV
  zqbfz
  simp_all
theorem abs_top_lt (C : Chain) : |C.top.1| < C.radius :=
  lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set C.top_mem_set).1 C.coordBound_lt_radius

/-- The point of a box vertex. -/
theorem pos_box_vtx (C : Chain) (Q : Polygon) (e : ℕ) :
    (chainModel C).pos Q ztjy = (C.sideWalk C.sideBeta).vtx e := by
  rw [pos_eq_sidePt, show (chainModel C).param Q ztjy = 0 from rfl,
    Chazelle.Chain.sidePt_zero]; rfl
theorem ptTopV_exec (hE : CEnv P W H C c) :
    ∃ c' k, Exec P W ptTopV c c' k ∧ k ≤ 27 * H.length + 47 ∧
      PtRec P c' ztnka C.radius := by
  obtain ⟨c₁, k₁, e₁, hk₁, a₁⟩ := absTop_exec c hE
  obtain ⟨c₂, k₂, e₂, hk₂, y₂, f₂, r₂⟩ := hyV_exec (P := P) c₁ e₁.wb_right (by have := hE.hW; omega)
    (k := 2) by_norm_num
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, absRec_copy' a₁ by_simp_all
    by_simp_all by_simp_all by_simp_all,
    Or.inr by_simp_all, fun h => by_omega⟩
theorem hxy_exec (hw : WordsBounded W c) (hW : 3 ≤ W) {x y : ℕ} (hx : x = 0 ∨ x = 2)
    (hy : y = 0 ∨ y = 2) {pt : Point} (hR : 0 < C.radius) (px0 : x = 0 → pt.1 = -C.radius)
    (px2 : x = 2 → pt.1 = C.radius) (py0 : y = 0 → pt.2 = -C.radius)
    (py2 : y = 2 → pt.2 = C.radius) :
    ∃ c' k, Exec P W (hxy x y) c c' k ∧ k = 3 ∧ PtRec P c' pt C.radius := by
  obtain ⟨c', k, ex, hk, v0, v4, v6⟩ : ∃ c' k, Exec P W (hxy x y) c c' k ∧ k = 3 ∧
      c'.nreg 50210 = x ∧ c'.nreg 50214 = y ∧ c'.nreg 50216 = 0 := by
    unfold hxy
    zqbfz
    simp
  refine ⟨c', k, ex, hk, ztfwn, ?_, fun h => by_omega⟩
  · grind
  · zukmr
    · zudxj
    · zulen
theorem ptBoxV_exec (hE : CEnv P W H C c) {e : ℕ} (h01 : c.nreg 50201 = e)
    (he : e < 6) :
    ∃ c' k, Exec P W ptBoxV c c' k ∧ k ≤ 27 * H.length + 60 ∧
      PtRec P c' ((C.sideWalk C.sideBeta).vtx e) C.radius := by
  zubo
  zuol
  zuyv
  have W3 : ztpik := by_omega
  unfold ptBoxV
  have v1 := C.sideWalk_vtx_one C.sideBeta
  have v2 := C.sideWalk_vtx_two C.sideBeta
  have v3 := C.sideWalk_vtx_three C.sideBeta
  have v4 := C.sideWalk_vtx_four C.sideBeta
  by_cases h0 : e < 1
  · obtain rfl : e = 0 := by_omega
    zqbga
    exact ⟨c', _, .ifLtN_true (by zuonw; omega) ex, by_omega, by
      tauto⟩
  have t0 : ¬ c.nreg 50201 < c.nreg 50032 := by zuonw; omega
  zujsq
  · zukkf
    obtain ⟨c', k, ex, hk, pr⟩ := hxy_exec c hw W3 ztp
      ztbt (pt := (C.sideWalk C.sideBeta).vtx 1) hR by_simp_all
      by_omega by_omega by_simp_all
    exact ⟨c', _, .ifLtN_false t0 (.ifLtN_true ztdlv ex), by_omega, pr⟩
  have t1 : ¬ c.nreg 50201 < c.nreg 50082 := by rw [h01, hE.r82]; omega
  by_cases h3 : e < 3
  · obtain rfl : e = 2 := by_omega
    obtain ⟨c', k, ex, hk, pr⟩ := hxy_exec c hw W3 ztp
      ztp (pt := (C.sideWalk C.sideBeta).vtx 2) hR by_simp_all
      by_omega by_simp_all by_omega
    exact ⟨c', _, .ifLtN_false t0 (.ifLtN_false t1 (.ifLtN_true (by zuonx; omega)
      ex)), by_omega, pr⟩
  have t2 : ¬ c.nreg 50201 < c.nreg 50083 := by zuonx; omega
  zujss
  · zukkg
    obtain ⟨c', k, ex, hk, pr⟩ := hxy_exec c hw W3 ztbt
      ztp (pt := (C.sideWalk C.sideBeta).vtx 3) hR by_omega
      by_simp_all by_simp_all by_omega
    exact ⟨c', _, .ifLtN_false t0 (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_true
      ztfpk ex))), by_omega, pr⟩
  have t3 : ¬ c.nreg 50201 < c.nreg 50084 := by rw [h01, hE.r84]; omega
  by_cases h5 : e < 5
  · obtain rfl : e = 4 := by_omega
    obtain ⟨c', k, ex, hk, pr⟩ := hxy_exec c hw W3 ztbt
      ztbt (pt := (C.sideWalk C.sideBeta).vtx 4) hR by_omega
      by_simp_all by_omega by_simp_all
    exact ⟨c', _, .ifLtN_false t0 (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
      (.ifLtN_true (by zuony; omega) ex)))), by_omega, pr⟩
  have t4 : ¬ c.nreg 50201 < c.nreg 50085 := by zuony; omega
  zukke
  zqbga
  exact ⟨c', _, .ifLtN_false t0 (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
    (.ifLtN_false t4 ex)))), by_omega, by_tauto⟩

/-! ## Positions inside a vertical edge of the box block -/

/-- A positive parameter: the point is not a box vertex. -/
theorem box_param_pos' (C : Chain) (Q : Polygon) {e hc : ℕ} (he : e < 6)
    (hp : 0 ≤ (chainModel C).param Q ztev)
    (hy : |((chainModel C).pos Q ⟨e, hc⟩).2| < C.radius) :
    0 < (chainModel C).param Q ztev := by
  zuklw
  · zubh
  · exfalso
    have hv : (chainModel C).pos Q ztev = (chainModel C).W.vtx e := by
      rw [pos_eq_sidePt, ← h, Chazelle.Chain.sidePt_zero]
    zvmyq at hy
    rcases walk_vtx_box C (q := e) by_omega with h1 | h1 <;> zvmwp at hy
    · grind
    grind
theorem ptBoxS_exec (hE : CEnv P W H C c) {e hc : ℕ} (h01 : c.nreg 50201 = e)
    (h02 : c.nreg 50202 = hc) (he : e < 6) (hc1 : 1 ≤ hc) (hhn : hc ≤ P.n)
    (hp : 0 ≤ (chainModel C).param zta ztev)
    (hy : |((chainModel C).pos zta ⟨e, hc⟩).2| < C.radius) :
    ∃ c' k, Exec P W ptBoxS c c' k ∧ k ≤ 27 * H.length + 60 ∧
      PtRec P c' ztwtg C.radius := by
  zubo
  zuol
  zuyv
  have hpos := box_param_pos' C _ he hp hy
  have hne := ne_of_param_pos hpos
  -- the ordinate
  have hY : ztwrc := by
    zqbfy
  obtain ⟨c₁, k₁, e₁, hk₁, o14, o15, o16, r₁⟩ : ∃ c₁ k₁, Exec P W (block [.constN 50214 1,
      .subN 50215 50202 50032, .constN 50216 0]) c c₁ k₁ ∧ k₁ = 3 ∧ c₁.nreg 50214 = 1 ∧
      c₁.nreg 50215 = hc - 1 ∧ c₁.nreg 50216 = 0 ∧
      ∀ r, r ≠ 50214 → r ≠ 50215 → r ≠ 50216 → c₁.nreg r = c.nreg r := by
    zqbfz
    refine ⟨rfl, by config_simp, ?_, by config_simp, fun r h1 h2 h3 => ?_⟩
    · config_simp; rw [h02, hE.r32]
    simp_all
  have hE₁ := hE.frame (exec_frameB e₁ (B := fun r => r == 50214 ||
    r == 50215 || r == 50216) by_decide) e₁.wb_right by_decide
  have q01 : c₁.nreg 50201 = e := by_simp_all
  have hHR : ∀ c' : Config, (∀ r, 50214 ≤ r → r < 50217 → c'.nreg r = c₁.nreg r) →
      HRec P c' 50214 ((chainModel C).pos _ ztev).2 C.radius ∧
        FRec P c' 50216 ztwtg := fun c' hk =>
    ⟨Or.inr (Or.inr ⟨by_simp_all, hy,
      by grind,
      by simp_all⟩),
     fun h => by_simp_all⟩
  obtain ⟨-, b1, -, b3, -, b5, -⟩ := C.sidePt_box C.sideBeta
    ztwtf
  have hpt : (chainModel C).pos _ ztev =
      sidePt ztcs e ztwtf := rfl
  have hnot : e ≠ 0 ∧ e ≠ 2 ∧ e ≠ 4 := by
    refine ⟨fun h => hne ?_, fun h => hne ?_, fun h => hne ?_⟩ <;> subst h <;>
      exact box_horizontal C by_norm_num
  zujsq
  · zukkf
    have e₂ := Exec.constN (P := P) e₁.wb_right 50210 0 by_omega
    refine ⟨_, _, .seq e₁ (.ifLtN_true ztfpp e₂), by_omega,
      ⟨hR, Or.inl ⟨by_simp, by_grind⟩⟩, hHR _ fun r h1 h2 => by zumzy; zumya⟩
  zujss
  · zukkg
    have e₂ := Exec.constN (P := P) e₁.wb_right 50210 2 by_omega
    refine ⟨_, _, .seq e₁ (.ifLtN_false ztfpp
      (.ifLtN_true ztlij e₂)), by_omega,
      ⟨hR, Or.inr (Or.inl ⟨by_simp, by_grind⟩)⟩, hHR _ fun r h1 h2 => by zumzy; zumya⟩
  zukke
  obtain ⟨c₂, k₂, e₂, hk₂, a₂⟩ := absTop_exec c₁ hE₁
  have f₂ := exec_frameB e₂ (B := fun r => Btv 50211 r || r == 50120 || r == 50210)
    by_decide
  refine ⟨c₂, _, .seq e₁ (.ifLtN_false ztfpp
    (.ifLtN_false ztlij e₂)), by_omega, by_grind,
    hHR _ fun r h1 h2 => f₂.1 r (by interval_cases r <;> decide)⟩

/-! ## Tour vertices -/

/-- The height index of a symbolic point. -/
def hIdx : SymPt → ℕ
  | .vtx k => k
  | .onEdge _ h => h
theorem hIdx_lt {n : ℕ} {s : SymPt} (h : s.Lt n) : hIdx s < n := by
  cases s with
  | vtx k => exact h
  | onEdge e h' => exact h.2
theorem hIdx_snd (Q : Polygon) (s : SymPt) : (s.eval Q).2 = (Q.vtx (hIdx s)).2 := by
  cases s <;> rfl
theorem ptVtx_exec (hE : CEnv P W H C c) {e hc : ℕ} (h01 : c.nreg 50201 = e)
    (he6 : 6 ≤ e) (hen : e < 2 * C.m + 7) (hpar : (chainModel C).param zta ztev = 0) :
    ∃ c' k, Exec P W ptVtx c c' k ∧ k ≤ 27 * H.length + 60 ∧
      PtRec P c' ztwtg C.radius ∧ c'.nreg 50216 = 1 := by
  zuol
  zuiu
  zumz
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp, -⟩ := tvLoad_exec _ hE₁ (i := e - 6)
    zteqd by_omega (dst := 50211) by_norm_num
  have hv : ztwnq := by
    zubab
  have hmem : ztxpk := by
    zuday
  zuljm
  have hlt := C.coordBound_lt_radius
  have s32 := hE₂.r32
  obtain ⟨c₃, k₃, e₃, hk₃, q10, q17, q18, q19, q16, q14, r₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.constN 50210 1, .copyN 50217 50211, .copyN 50218 50212, .copyN 50219 50213,
        .constN 50216 1, .constN 50214 1]) c₂ c₃ k₃ ∧ k₃ = 6 ∧ c₃.nreg 50210 = 1 ∧
      c₃.nreg 50217 = c₂.nreg 50211 ∧ c₃.nreg 50218 = c₂.nreg 50212 ∧
      c₃.nreg 50219 = c₂.nreg 50213 ∧ c₃.nreg 50216 = 1 ∧ c₃.nreg 50214 = 1 ∧
      ∀ r, r ≠ 50210 → r ≠ 50217 → r ≠ 50218 → r ≠ 50219 → r ≠ 50216 → r ≠ 50214 →
        c₃.nreg r = c₂.nreg r := by
    zuja
    zqbfz
    simp_all
  have g : ∀ r, 50211 ≤ r → r < 50214 → c₃.nreg r = c₂.nreg r := by_grind
  have isp₃ := symPtIn_of_eq isp by_omega
  have fsp₃ := NFLoc.symPtIn_copy isp q17 q18 q19
  have c32 : ztusc := by_grind
  zuboe
  -- the height index
  obtain ⟨c₄, k₄, e₄, hk₄, q15, r₄⟩ : ∃ c₄ k₄, Exec P W (.ifLtN 50211 50032
      ztovq ztovr) c₃ c₄ k₄ ∧ k₄ ≤ 3 ∧
      c₄.nreg 50215 = hIdx sp ∧ ∀ r, r ≠ 50215 → c₄.nreg r = c₃.nreg r := by
    cases sp with
    | vtx k =>
      obtain ⟨i0, i1⟩ := isp₃
      exact ⟨_, _, .ifLtN_true by_omega ztrjg, by_norm_num,
        by simp [i1, hIdx], fun r hr => by zumwy⟩
    | onEdge e' h' =>
      obtain ⟨i0, i1, i2⟩ := isp₃
      exact ⟨_, _, .ifLtN_false by_omega ztrjg, by_norm_num,
        by simp [i2, hIdx], fun r hr => by zumwy⟩
  refine ⟨c₄, _, .seq e₁ ztcb, by_omega, ⟨⟨C.radius_pos, Or.inr (Or.inr
    ⟨by_grind, by_grind, sp,
      symPtIn_of_eq isp₃ by_grind, lsp, by_grind⟩)⟩,
    Or.inr (Or.inr ⟨by_grind, by_grind,
      by rw [q15]; exact hIdx_lt lsp, by rw [q15, hv, ← vsp, hIdx_snd]⟩),
    fun _ => ⟨sp, symPtIn_of_eq fsp₃ by_grind, lsp, by_grind⟩⟩,
    by grind⟩

/-! ## Positions inside a tour edge or the up-slit edge -/
theorem hyI_exec (hw : WordsBounded W c) (hW : 3 ≤ W) (h32 : c.nreg 50032 = 1)
    {f : ℕ} (hf : f ≤ 1) :
    ∃ c' k, Exec P W (hyI f) c c' k ∧ k = 3 ∧ c'.nreg 50214 = 1 ∧
      c'.nreg 50215 = c.nreg 50202 - 1 ∧ c'.nreg 50216 = f ∧
      ∀ r, r ≠ 50214 → r ≠ 50215 → r ≠ 50216 → c'.nreg r = c.nreg r := by
  unfold hyI
  zqbfz
  simp_all

/-- **The symbolic point inside a tour edge.** -/
theorem absTour_exec' (hE : CEnv P W H C c) (hreg : HostRegular P.n H) {i hc : ℕ}
    (h20 : c.nreg 50120 = i) (h02 : c.nreg 50202 = hc) (hi : i < 2 * C.m)
    (ht : 0 < (chainModel C).param zta ztcbx) (hhn : hc ≤ P.n) :
    ∃ c' k, Exec P W absTour c c' k ∧ k ≤ 60 * H.length + 150 ∧ c'.nreg 50210 = 1 ∧
      c'.nreg 50202 = hc ∧ c'.nreg 50032 = 1 ∧ ∃ E, E < P.n ∧
        SymPtIn c' 50211 (.onEdge E ztzk) ∧
        (SymPt.onEdge E ztzk).eval zta = (chainModel C).pos zta ztcbx := by
  zuol
  zuhxc

  zubnw
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, s₁, i₁, l₁, v₁, x₁⟩ := tvLoad_exec c hE (i := i) h20
    hi.le (dst := 50130) by_norm_num
  zue
  have e₃ := Exec.addN (P := P) w₂ 50120 50120 50032
    (by rw [f₂.1 _ by_decide, h20, hE₂.r32]; omega)
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50120 _ }
    with hc₃
  zucls
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, s₂, i₂, l₂, v₂, x₂⟩ := tvLoad_exec c₃ hE₃ (i := i + 1)
    (by zumwr; simp [f₂.1 _ (by decide : Btv 50130 50120 = false) ▸ h20, hE₂.r32])
    by_omega (dst := 50136) by_norm_num
  have i₁' := symPtIn_keep (symPtIn_of_eq i₁ fun j h1 h2 => by
    zumwr; zunbj) f₄
    by_decide
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, r₅⟩ := edgeIdxS_exec (P := P) c₄ e₄.wb_right by_omega
    hE₄.r32 i₁' i₂ l₁ l₂
  have q02 : ztlyi := by
    zuwy
    zulro
    rw [upd_other _ _ _ by_decide, f₂.1 _ by_decide, h02]
  have q32 : ztlyh := by
    zubqc
  obtain ⟨hEi, hx⟩ := tour_abs hE.hG hE.hP hreg hNn hi x₁ x₂ l₁ l₂ v₁ v₂ ht
  have hc1 : ztixw := by
    zuzn
    · simp_all
    omega
  obtain ⟨c₆, k₆, e₆, hk₆, q⟩ : ∃ c₆ k₆, Exec P W outE c₅ c₆ k₆ ∧ k₆ = 4 ∧
      (c₆.nreg 50210 = 1 ∧ SymPtIn c₆ 50211 ztyoc ∧
        c₆.nreg 50202 = hc ∧ c₆.nreg 50032 = 1) := by
    zumtu
    zudpp
    exec_block
    all_goals try omega
    refine ⟨rfl, by config_simp, ⟨by config_simp, by_simp_all, ?_⟩, ?_, ?_⟩
    · simp_all
    · simp_all
    simp_all
  obtain ⟨q10, q11, q02', q32'⟩ := q
  -- the ordinate of the point
  zubkn
  have hY : ((chainModel C).pos zta ztcbx).2 = ((Qof P).vtx ztzk).2 := by
    zqbfy
  refine ⟨c₆, _, .seq e₂ (.seq e₃ ztxjw), by_omega, q10, q02', q32', _, hEi,
    q11, ?_⟩
  ext
  · simp_all
  · rw [hY]; rfl
theorem ptInt_exec (hE : CEnv P W H C c) (hreg : HostRegular P.n H) {e hc : ℕ}
    (h01 : c.nreg 50201 = e) (h02 : c.nreg 50202 = hc) (he6 : 6 ≤ e) (hen : e < 2 * C.m + 7)
    (ht : 0 < (chainModel C).param zta ztev) (ht1 : (chainModel C).param zta ztev < 1)
    (hhn : hc ≤ P.n) :
    ∃ c' k, Exec P W ptInt c c' k ∧ k ≤ 60 * H.length + 200 ∧
      PtRec P c' ztwtg C.radius ∧
      (e < 2 * C.m + 6 → c'.nreg 50216 = 1) := by
  zuol
  zubb
  zubo
  zudym

  zubnw
  zubkn
  have hc1 : ztixw := by
    zuzn
    · simp_all
    omega
  have hY : ztwrc := by
    zqbfy
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.subN 50120 50201 50081,
      .addN 50143 50053 50053]) c c₁ k₁ ∧ k₁ = 2 ∧ (c₁.nreg 50120 = e - 6 ∧
        c₁.nreg 50143 = 2 * C.m ∧ ∀ r, r ≠ 50120 → r ≠ 50143 → c₁.nreg r = c.nreg r) := by
    zuyv
    exec_block
    · config_simp; rw [hE.r53]; omega
    · refine ⟨rfl, by config_simp; zunqk, by config_simp; zunkz; ring,
        by simp_all⟩
  zucxx
  have hE₁ := hE.keep e₁.wb_right
    (exec_frameB e₁ (B := fun r => r == 50120 || r == 50143) by_decide).2.2.1
    ztwxf
  have q02 : c₁.nreg 50202 = hc := by_simp_all
  zugjo
  · obtain ⟨c₂, k₂, e₂, hk₂, o10, o02, o32, E, hE', o11, hv⟩ := absTour_exec' c₁ hE₁ hreg q20 q02 hlt by_simp_all hhn
    rw [show e - 6 + 6 = e by omega] at hv
    obtain ⟨c₃, k₃, e₃, hk₃, y14, y15, y16, r₃⟩ := hyI_exec c₂ e₂.wb_right by_omega
      o32 le_rfl
    have o11' : SymPtIn c₃ 50211 _ :=
      symPtIn_of_eq o11 by_grind
    obtain ⟨c₄, e₄, v₄, f₄⟩ := copies_exec [ztstw, ztstx,
      ztsty] c₃ e₃.wb_right by_decide by_decide
    zvmwt at v₄
    obtain ⟨v17, v18, v19⟩ := v₄
    have k₄ : ∀ r, r ≠ 50217 → r ≠ 50218 → r ≠ 50219 → c₄.nreg r = c₃.nreg r := fun r h1 h2 h3 =>
      f₄.1 r (by simp [h1, h2, h3])
    have hmem : ztyky := by
      have hei : e = e - 6 + 6 := by_omega
      zudam

    zuljm
    zumds
    have o11'' : SymPtIn c₄ 50211 _ :=
      symPtIn_of_eq o11' fun j h1 h2 => k₄ j by_omega by_omega by_omega
    have lt : (SymPt.onEdge E ztzk).Lt P.n := ⟨hE', by_omega⟩
    refine ⟨c₄, _, .seq e₁ (.ifLtN_true by_omega ztcb),
      by simp only [List.length_cons, List.length_nil]; omega,
      ⟨⟨hR, by_grind⟩,
      Or.inr by_grind,
      fun _ => ⟨_, NFLoc.symPtIn_copy o11' v17 v18 v19, lt, hv⟩⟩,
      by grind⟩
  · zucgp

    have f₂ := exec_frameB e₂ (B := fun r => Btv 50211 r || r == 50120 || r == 50210)
      by_decide
    have o02 : c₂.nreg 50202 = hc := by rw [f₂.1 _ by_decide, q02]
    have o32 : c₂.nreg 50032 = 1 := by rw [f₂.1 _ by_decide, hE₁.r32]
    obtain ⟨c₃, k₃, e₃, hk₃, y14, y15, y16, r₃⟩ := hyI_exec c₂ e₂.wb_right by_omega
      o32 (f := 0) by_norm_num
    -- the point on the up-slit edge
    zulta
    obtain ⟨-, -, -, -, -, -, e6⟩ := C.sidePt_box C.sideBeta
      _
    have hpt : (chainModel C).pos zta zthly =
        (C.top.1, C.top.2 + (chainModel C).param zta zthly *
          ztox) := by
      rw [pos_eq_sidePt]; exact e6
    zubnz
    have htop' := (abs_le.1 (C.abs_le_coordBound_of_mem_set C.top_mem_set).2).1
    zumds
    have hy : |((chainModel C).pos zta ⟨2 * C.m + 6, hc⟩).2| < C.radius := by
      rw [hpt, abs_lt]
      zueop
    refine ⟨c₃, _, .seq e₁ (.ifLtN_false by_omega ztcr),
      by omega, ⟨?_, Or.inr by_grind,
      fun h => by_omega⟩, by_grind⟩
    zubil
    exact absRec_copy' hrec by_grind
      by_grind by_grind
      by_grind

/-! ## The contract -/

/-- The input condition of `ptKey`: a position of the walk proper, a box vertex or strictly inside
the height range of the box, and a regular host. -/
def PtIn (P : Polygon) (_ : ℕ) (C : Chain) (c : Config) : Prop :=
  c.nreg 50201 < (chainModel C).W.n ∧
    ProperPos ztc zta P.n ztbce ∧
    (c.nreg 50202 = 0 ∨
      |((chainModel C).pos (Qof P) ⟨c.nreg 50201, c.nreg 50202⟩).2| < C.radius) ∧
    ∀ H', HostAt c.nmem ztzdq H' → HostRegular P.n H'

/-- The output condition of `ptKey`. -/
def PtOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  PtRec P c' ztyms C.radius ∧
    (6 ≤ c.nreg 50201 → (c.nreg 50201 < 2 * C.m + 6 ∨
      (chainModel C).param zta ztbce = 0) → c'.nreg 50216 = 1)

/-- **Contract of `ptKey`** (at most `15800` steps). -/
theorem ptKey_meets : Meets ptKey primBands (PrimPre PtIn) (PrimPost PtOut)
    (fun _ _ => 15800) := by
  refine prim_meets by_simp_all wr_ptKey ?_
  intro P W H C c₀ c hC hE ⟨hen, ⟨hp0, hp1, hhn⟩, hy, hreg⟩ hinp
  zudpd
  zuet
  zubgf
  zuhq

  set e := c₀.nreg 50201
  set hc := c₀.nreg 50202
  zujsu
  · have t0 : c.nreg 50201 < c.nreg 50081 := by zuonz; exact h6
    by_cases hh : hc < 1
    · have hc0 : hc = 0 := by_omega
      obtain ⟨c', k, ex, hk, pr⟩ := ptBoxV_exec c hE i01 h6
      refine ⟨c', _, .ifLtN_true t0 (.ifLtN_true ztktz ex), by_omega, ?_⟩
      zujfw
      show PtRec P c' ((chainModel C).pos _ ztev) C.radius
      rw [hc0, pos_box_vtx]; exact pr
    · have hy' : ztxib := by
        simp_all
      obtain ⟨c', k, ex, hk, pr⟩ := ptBoxS_exec c hE i01 i02 h6 by_omega hhn hp0 hy'
      exact ⟨c', _, .ifLtN_true t0 (.ifLtN_false ztktz ex), by_omega,
        pr, by_simp_all⟩
  · have t0 : ¬ c.nreg 50201 < c.nreg 50081 := by zuonz; exact h6
    have hen' : ztpoj := by_omega
    -- the ordinate is inside the box
    have hy' : ztxib := by
      rcases hy with h | h
      · have hv : ztwnq := by
          show (chainModel C).pos _ ztev = _
          rw [show hc = 0 from h, pos_box_vtx, show e - 6 + 6 = e by omega]; rfl
        have hmem : ztxpk := by
          zuday
        zueyk
        zuhuj
      omega
    obtain ⟨c', k, ex, hk, pr⟩ := classify_exec (Kb := 0)
      (R := fun c' => PtRec P c' _ C.radius ∧
        (6 ≤ e → (e < 2 * C.m + 6 ∨ (chainModel C).param zta ztev = 0) →
          c'.nreg 50216 = 1)) c₀ c hE hinp hen
      hp0 hp1 hhn hy'
      (fun _ _ _ _ he _ => absurd he h6)
      (fun c₂ hE₂ g₂ h6' hpar => by
        obtain ⟨c', k, ex, hk, pr, fl⟩ := ptVtx_exec c₂ hE₂ ztdop
          h6' hen' hpar
        exact ⟨c', k, ex, hk, pr, by_omega⟩)
      (fun c₂ hE₂ g₂ _ h6' hpos => by
        obtain ⟨c', k, ex, hk, pr, fl⟩ := ptInt_exec c₂ hE₂ hregH
          ztdop ztlpk h6' hen'
          hpos hp1 hhn
        refine ⟨c', k, ex, hk, pr, fun _ h => fl ?_⟩
        grind)
    exact ⟨c', _, .ifLtN_false t0 ex, by_omega, pr⟩
end
end ShootCut
end Chazelle.Core
end
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
@[expose] public section
def K1 : ℕ := 140401

/-- **A weak abscissa record**: like `AbsRec`, but the symbolic kind allows `|x| ≤ R`. -/
def AbsRecW (P : Polygon) (c : Config) (r : ℕ) (x R : ℝ) : Prop :=
  0 < R ∧ (ztllt ∨ ztmha ∨
    (c.nreg r = 1 ∧ |x| ≤ R ∧ ∃ s : SymPt, SymPtIn c ztgu s ∧ s.Lt P.n ∧ (s.eval zta).1 = x))
theorem AbsRec.weak {P : Polygon} {c : Config} {r : ℕ} {x R : ℝ} (h : AbsRec P c r x R) :
    AbsRecW P c r x R := by
  zuchy
  refine ztfwn
  grind
theorem AbsRecW.kind {P : Polygon} {c : Config} {r : ℕ} {x R : ℝ} (h : AbsRecW P c r x R) :
    c.nreg r ≤ 2 := by
  zucin
theorem AbsRecW.bounds {P : Polygon} {c : Config} {r : ℕ} {x R : ℝ} (h : AbsRecW P c r x R) :
    -R ≤ x ∧ x ≤ R := by
  zuchy
  grind

/-- A weak record describes one abscissa once the registers are fixed. -/
theorem AbsRecW.copy {P : Polygon} {c c' : Config} {r r' : ℕ} {x R : ℝ} (h : AbsRecW P c r x R)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg ztcwh = c.nreg ztgu)
    (h2 : c'.nreg ztcwi = c.nreg ztbcu) (h3 : c'.nreg ztkdl = c.nreg ztkdd) :
    AbsRecW P c' r' x R := by
  zufk

  · simp_all
  · simp_all
  · zuia

/-! ## Abscissae -/

/-- **The bit `x_a < x_b`.** -/
def xLess (a b dst : ℕ) : Stmt :=
  .ifLtN a K1 ztzak
    (.ifLtN K1 a ztbfs
      (.ifLtN b K1 ztbfs
        (.ifLtN K1 b ztcgm (kbit ztdf ztds ztdf 0 dst))))
variable {P : Polygon} {W : ℕ}
theorem bit_const (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) (dst v : ℕ) (hv : v ≤ 1)
    {p : Prop} (hp : v = 1 ↔ p) :
    BitIs ({ c with nreg := upd c.nreg dst v } : Config) dst p ∧
      Exec P W (.instr (.constN dst v)) c { c with nreg := upd c.nreg dst v } 1 :=
  ⟨⟨by_simp_all, by_simp_all⟩, Exec.constN hw dst v by_omega⟩
theorem xLess_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {a b dst : ℕ} (ha : 10500 ≤ a) (hb : 10500 ≤ b) (hdst : 10500 ≤ dst) (h1 : c.nreg K1 = 1)
    {xa xb R : ℝ} (hA : AbsRecW P c a xa R) (hB : AbsRecW P c b xb R)
    (hok : xa ≠ xb ∨ ((c.nreg a = 1 → |xa| < R) ∧ (c.nreg b = 1 → |xb| < R))) :
    ∃ c' k, Exec P W (xLess a b dst) c c' k ∧ k ≤ 250 ∧ BitIs c' dst (xa < xb) ∧
      FrameB ztdks c c' := by
  have hR := hA.1
  zudzw

  have bA := hA.bounds
  have bB := hB.bounds
  have fr : ∀ v, FrameB ztdks c ({ c with nreg := upd c.nreg dst v } : Config) := fun v =>
    ⟨fun r hr => by
      zuggr
      simp_all, by_simp_all, rfl, rfl, rfl⟩
  unfold xLess
  zuhrx
  · have ka : c.nreg a = 0 := by_omega
    have hxa : xa = -R := by
      rcases hA.2 with ⟨_, h⟩ | ⟨h', _⟩ | ⟨h', _⟩ <;> [exact h; omega; omega]
    zucfi
    · have hxb : ztuvb := by
        zublj
      obtain ⟨bt, ex⟩ := bit_const c hw by_omega dst 0 by_norm_num
        (p := xa < xb) by_simp_all
      exact ztfzc
    · have hlt : xa < xb := by
        rcases hB.2 with ⟨h', _⟩ | ⟨_, h⟩ | ⟨_, hx, s, -, -, -⟩
        · omega
        · simp_all
        grind
      obtain ⟨bt, ex⟩ := bit_const c hw by_omega dst 1 le_rfl
        ⟨fun _ => hlt, by_omega⟩
      exact ztfzb
  zuhry
  · have hxa : xa = R := by
      rcases hA.2 with ⟨h', _⟩ | ⟨_, h⟩ | ⟨h', _⟩ <;> [omega; exact h; omega]
    obtain ⟨bt, ex⟩ := bit_const c hw by_omega dst 0 by_norm_num (p := xa < xb)
      by_simp_all
    exact ztfza
  have ka : c.nreg a = 1 := by_omega
  obtain ⟨-, hxa, sa, isa, lsa, vsa⟩ : c.nreg a = 1 ∧ |xa| ≤ R ∧ ∃ s : SymPt, SymPtIn c (a + 1) s ∧
      s.Lt P.n ∧ (s.eval zta).1 = xa := by
    rcases hA.2 with ⟨h', _⟩ | ⟨h', _⟩ | h <;> [omega; omega; exact h]
  zucfi
  · have hxb : ztuvb := by
      zublj
    obtain ⟨bt, ex⟩ := bit_const c hw by_omega dst 0 by_norm_num (p := xa < xb)
      by_simp_all
    exact ztfag
  zuhsb
  · have hxb : xb = R := by
      rcases hB.2 with ⟨h', _⟩ | ⟨_, h⟩ | ⟨h', _⟩ <;> [omega; exact h; omega]
    have hlt : xa < xb := by
      grind
    obtain ⟨bt, ex⟩ := bit_const c hw by_omega dst 1 le_rfl
      ⟨fun _ => hlt, by_omega⟩
    exact ⟨_, _, .ifLtN_false a0 ztjdi,
      by norm_num, bt, fr 1⟩
  obtain ⟨-, -, sb, isb, lsb, vsb⟩ : c.nreg b = 1 ∧ |xb| ≤ R ∧ ∃ s : SymPt, SymPtIn c (b + 1) s ∧
      s.Lt P.n ∧ (s.eval zta).1 = xb := by
    rcases hB.2 with ⟨h', _⟩ | ⟨h', _⟩ | h <;> [omega; omega; exact h]
  obtain ⟨c', k, ex, hk, f, b₁, t⟩ := kbit_exec (op := 0) (dst := dst) hG hW c hw by_omega
    by_omega by_omega hdst by_norm_num lsa lsb lsa isa isb isa
  refine ⟨c', _, .ifLtN_false a0 ztjdh,
    by omega, ztugf, f⟩
  rw [t]; show (sa.eval _).1 < (sb.eval _).1 ↔ _; simp_all

/-! ## Ordinates -/

/-- **An ordinate record with a slot** at `r`: kind `0` (`-R`), `2` (`R`), or `1` and, at `r + 1`,
the symbolic vertex (`0`, index) of `Q` at height `y`, `|y| < R`. -/
def HRecS (P : Polygon) (c : Config) (r : ℕ) (y R : ℝ) : Prop :=
  ztllu ∨ ztmhb ∨
    (c.nreg r = 1 ∧ |y| < R ∧ c.nreg ztgu = 0 ∧ c.nreg ztbcu < P.n ∧
      y = ((Qof P).vtx (c.nreg ztbcu)).2)
variable {c : Config} {r : ℕ} {y R : ℝ}
theorem HRecS.kind (h : HRecS P c r y R) : c.nreg r ≤ 2 := by
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
theorem HRecS.bounds (hR : 0 < R) (h : HRecS P c r y R) :
    -R ≤ y ∧ y ≤ R := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, hy, -⟩
  · grind
  · grind
  grind
theorem HRecS.copy {c c' : Config} {r r' : ℕ} {y R : ℝ} (h : HRecS P c r y R)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg ztcwh = c.nreg ztgu)
    (h2 : c'.nreg ztcwi = c.nreg ztbcu) : HRecS P c' r' y R := by
  rcases h with ⟨k, hy⟩ | ⟨k, hy⟩ | ⟨k, hy, hz, hl, he⟩
  · zudxj
  · zulen
  · zulen

/-- **The bit `y_a < y_b`.** -/
def hLess (a b dst : ℕ) : Stmt :=
  .ifLtN a K1 ztzak
    (.ifLtN K1 a ztbfs
      (.ifLtN b K1 ztbfs
        (.ifLtN K1 b ztcgm (kbit ztdf ztds ztdf 1 dst))))
theorem hLess_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {a b dst : ℕ} (ha : 10500 ≤ a) (hb : 10500 ≤ b) (hdst : 10500 ≤ dst) (h1 : c.nreg K1 = 1)
    {ya yb R : ℝ} (hR : 0 < R) (hA : HRecS P c a ya R) (hB : HRecS P c b yb R) :
    ∃ c' k, Exec P W (hLess a b dst) c c' k ∧ k ≤ 250 ∧ BitIs c' dst (ya < yb) ∧
      FrameB ztdks c c' := by
  zudzw

  have bA := hA.bounds hR
  have bB := hB.bounds hR
  have fr : ∀ v, FrameB ztdks c ({ c with nreg := upd c.nreg dst v } : Config) := fun v =>
    ⟨fun r hr => by
      zuggr
      simp_all, by_simp_all, rfl, rfl, rfl⟩
  unfold hLess
  zuhrx
  · have hya : ztuvc := by
      zublg
    zucfi
    · have hyb : ztpqo := by
        zukn
      obtain ⟨bt, ex⟩ := bit_const c hw by_omega dst 0 by_norm_num
        (p := ya < yb) by_simp_all
      exact ztfzc
    · have hlt : ya < yb := by
        rcases hB with ⟨h', _⟩ | ⟨_, h⟩ | ⟨_, hy, -⟩
        · omega
        · simp_all
        grind
      obtain ⟨bt, ex⟩ := bit_const c hw by_omega dst 1 le_rfl
        ⟨fun _ => hlt, by_omega⟩
      exact ztfzb
  zuhry
  · have hya : ya = R := by
      zublh
    obtain ⟨bt, ex⟩ := bit_const c hw by_omega dst 0 by_norm_num (p := ya < yb)
      by_simp_all
    exact ztfza
  obtain ⟨-, hya, za, la, vya⟩ : c.nreg a = 1 ∧ |ya| < R ∧ c.nreg (a + 1) = 0 ∧
      c.nreg ztvj < P.n ∧ ya = ((Qof P).vtx ztzeb).2 := by
    zubxy
  zucfi
  · have hyb : ztpqo := by
      zukn
    obtain ⟨bt, ex⟩ := bit_const c hw by_omega dst 0 by_norm_num (p := ya < yb)
      by_simp_all
    exact ztfag
  zuhsb
  · have hyb : yb = R := by
      zubli
    obtain ⟨bt, ex⟩ := bit_const c hw by_omega dst 1 le_rfl (p := ya < yb)
      by_grind
    exact ⟨_, _, .ifLtN_false a0 ztjdi,
      by norm_num, bt, fr 1⟩
  obtain ⟨-, -, zb, lb, vyb⟩ : c.nreg b = 1 ∧ |yb| < R ∧ c.nreg (b + 1) = 0 ∧
      c.nreg ztub < P.n ∧ yb = ((Qof P).vtx ztwzr).2 := by
    zubxz
  have isa : SymPtIn c _ (.vtx ztzeb) := ⟨za, rfl⟩
  have isb : SymPtIn c _ (.vtx ztwzr) := ⟨zb, rfl⟩
  obtain ⟨c', k, ex, hk, f, b₁, t⟩ := kbit_exec (op := 1) (dst := dst) hG hW c hw by_omega
    by_omega by_omega hdst by_norm_num ztlsz
    (show (SymPt.vtx _).Lt P.n from lb) ztlsz isa isb isa
  refine ⟨c', _, .ifLtN_false a0 ztjdh,
    by omega, ztugf, f⟩
  rw [t, vya, vyb]; rfl

/-- **The bit `y_a = y_b`.** -/
def hEq (a b dst : ℕ) : Stmt :=
  .ifLtN a b ztbfs
    (.ifLtN b a ztbfs
      (.ifLtN a K1 ztcgm
        (.ifLtN K1 a ztcgm
          (.ifLtN ztvj ztub ztbfs
            (.ifLtN ztub ztvj ztbfs ztcgm)))))
theorem hEq_exec (hG : GoodEnv P) (hW : 1 ≤ W) (c : Config) (hw : WordsBounded W c)
    {a b dst : ℕ} (h1 : c.nreg K1 = 1) {ya yb R : ℝ} (hR : 0 < R) (hA : HRecS P c a ya R)
    (hB : HRecS P c b yb R) :
    ∃ c' k, Exec P W (hEq a b dst) c c' k ∧ k ≤ 20 ∧ BitIs c' dst (ya = yb) ∧
      c' = { c with nreg := upd c.nreg dst (c'.nreg dst) } := by
  zudzw

  zulhu
  zuc
  have fin : ∀ v, v ≤ 1 → (v = 1 ↔ ya = yb) → ∃ c₂, Exec P W _ c c₂ 1 ∧
      BitIs c₂ dst _ ∧ c₂ = { c with nreg := upd c.nreg dst (c₂.nreg dst) } :=
    fun v hv hp => ⟨_, Exec.constN hw dst v by_omega, (bit_const (P := P) c hw hW dst v hv hp).1,
      by simp⟩
  -- different kinds: different ordinates
  have kdiff : c.nreg a ≠ c.nreg b → ya ≠ yb := fun hk he => by
    rcases hA with ⟨ka, hya⟩ | ⟨ka, hya⟩ | ⟨ka, hya, -⟩ <;>
      rcases hB with ⟨kb, hyb⟩ | ⟨kb, hyb⟩ | ⟨kb, hyb, -⟩ <;>
      first | omega | skip
    all_goals first
      | (rw [hya, hyb] at he; linarith)
      | (rw [hya] at he; zvndl at hyb; zvncj at hyb; linarith [hyb.1, hyb.2])
      | (rw [hyb] at he; zvmxm at hya; zvncj at hya; linarith [hya.1, hya.2])
  by_cases t1 : c.nreg a < c.nreg b
  · zutf
    exact ⟨c₂, _, .ifLtN_true t1 e, by_norm_num, bt, h⟩
  by_cases t2 : c.nreg b < c.nreg a
  · zutf
    exact ⟨c₂, _, .ifLtN_false t1 ztspq, by_norm_num, bt, h⟩
  have hk : c.nreg a = c.nreg b := by_omega
  by_cases t3 : c.nreg a < c.nreg K1
  · have hya : ztuvc := by
      zublg
    have hyb : ztpqo := by
      zukn
    zueam
    exact ⟨c₂, _, .ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_true t3 e)), by_norm_num, bt, h⟩
  by_cases t4 : c.nreg K1 < c.nreg a
  · have hya : ya = R := by
      zublh
    have hyb : yb = R := by
      zubli
    zueam
    exact ⟨c₂, _, .ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3 (.ifLtN_true t4 e))),
      by norm_num, bt, h⟩
  obtain ⟨-, -, -, la, vya⟩ : c.nreg a = 1 ∧ |ya| < R ∧ c.nreg (a + 1) = 0 ∧
      c.nreg ztvj < P.n ∧ ya = ((Qof P).vtx ztzeb).2 := by
    zubxy
  obtain ⟨-, -, -, lb, vyb⟩ : c.nreg b = 1 ∧ |yb| < R ∧ c.nreg (b + 1) = 0 ∧
      c.nreg ztub < P.n ∧ yb = ((Qof P).vtx ztwzr).2 := by
    zubxz
  have hiff : ya = yb ↔ c.nreg ztvj = c.nreg ztub := by
    rw [vya, vyb]
    constructor
    · zufhz
      zuct
      exact hD _ _ by_omega by_omega hne he
    simp_all
  by_cases t5 : c.nreg ztvj < c.nreg ztub
  · zutf
    exact ⟨c₂, _, .ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3 (.ifLtN_false t4
      (.ifLtN_true t5 e)))), by_norm_num, bt, h⟩
  by_cases t6 : c.nreg ztub < c.nreg ztvj
  · zutf
    exact ⟨c₂, _, .ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3 (.ifLtN_false t4
      (.ifLtN_false t5 (.ifLtN_true t6 e))))), by_norm_num, bt, h⟩
  obtain ⟨c₂, e, bt, h⟩ := fin 1 le_rfl ⟨fun _ => hiff.2 by_omega, fun _ => rfl⟩
  exact ⟨c₂, _, .ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3 (.ifLtN_false t4
    (.ifLtN_false t5 (.ifLtN_false t6 e))))), by_norm_num, bt, h⟩
end
end ShootCut
@[expose] public section
open Set
open Chazelle.Geometry (lerp lerp_fst lerp_snd)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
namespace ShootCut
open Classical in
/-- **The decision tree of the machine** on a segment. -/
noncomputable def edgeSel (eUV zU zV aU aV nearU mid aX : Prop) : ℕ :=
  if eUV then (if zU then (if aU then (if nearU then 1 else 2) else 0) else 0)
  else if zU then (if aU then 1 else 0)
  else if zV then (if aV then 2 else 0)
  else if mid then (if aX then 3 else 0) else 0

/-- The abscissa of the selected point. -/
def selX (U V X : Point) : ℕ → ℝ
  | 1 => U.1
  | 2 => V.1
  | 3 => X.1
  | _ => 0

/-- **Correctness of the decision tree.** -/
theorem edge_cand {U V z X : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hzS : z ∉ seg U V)
    (hX : zthdb ∨ zthdc → X ∈ seg U V ∧ X.2 = z.2) :
    let sel := edgeSel (U.2 = V.2) (z.2 = U.2) (z.2 = V.2) ztzaq
      ztzar (σ * U.1 ≤ σ * V.1)
      (zthdb ∨ zthdc) (0 < σ * ztdtq)
    Cand ztevj z σ (if sel = 0 then 0 else 1) (selX U V X sel) := by
  intro sel
  classical
  have e0 : ∀ f : ℕ, ∀ x : ℝ, Cand ztevj z σ 0 x → Cand ztevj z σ 0 (selX U V X f) :=
    fun _ _ h => ⟨fun h' => absurd h' by_norm_num, h.2⟩
  by_cases hUV : U.2 = V.2
  · zujug
    · have hc := seg_on hσ hUV hzU hzS
      zuhsu
      · by_cases hn : σ * U.1 ≤ σ * V.1
        · zucaj
          zvmwk; simp only [one_ne_zero, ↓reduceIte, selX]
          simp_all
        · zucak
          zvmwk; simp only [OfNat.ofNat_ne_zero, ↓reduceIte, selX]
          simp_all
      · have : ztlbf := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; grind
        grind
    · zueb
      zugfm
      exact e0 0 0 (seg_off hUV hzU 0)
  -- ends at different heights
  zujug
  · have hc := seg_at hσ hUV (U_mem_seg U V) hzU.symm
    zuhsu
    · zucaj
      zubza
    · zueb
      grind
  by_cases hzV : z.2 = V.2
  · have hc := seg_at hσ hUV (V_mem_seg U V) hzV.symm
    by_cases hA : 0 < σ * zteok
    · zucak
      zubza
    · zueb
      grind
  by_cases hmid : zthdb ∨ zthdc
  · obtain ⟨hXS, hXy⟩ := hX hmid
    have hc := seg_at hσ hUV hXS hXy
    by_cases hA : 0 < σ * ztdtq
    · have : sel = 3 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; simp_all
      zubza
    · zueb
      grind
  · zueb
    zugfm
    refine e0 0 0 (seg_out ?_ 0)
    grind

/-- **The position at the height of `z` inside a sub-segment of a walk edge.** -/
theorem mid_pos (M : Model) (Q : Polygon) {p h : ℕ} {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hβ : β ≤ 1)
    (hmid : ((lerp ztpr ztoa α).2 < (Q.vtx h).2 ∧
        (Q.vtx h).2 < (lerp ztpr ztoa β).2) ∨
      ((lerp ztpr ztoa β).2 < (Q.vtx h).2 ∧
        (Q.vtx h).2 < (lerp ztpr ztoa α).2)) :
    M.pos Q ztdw ∈ seg ztzmp ztzmq ∧
      (M.pos Q ztdw).2 = (Q.vtx h).2 ∧ 0 < M.param Q ztdw ∧
      M.param Q ztdw < 1 := by
  set a := M.wa p
  set b := M.wb p
  have hne : a.2 ≠ b.2 := by
    zufhz
    zujoo
    grind
  have hd : ztmuc := sub_ne_zero.2 ztnr
  have hpar : M.param Q ztdw = ztmyg / ztti := by
    show ztgrq = _
    grind
  set t := M.param Q ztdw
  have hpos : M.pos Q ztdw = lerp a b t := rfl
  have hty : a.2 + t * ztti = (Q.vtx h).2 := by_simp_all
  -- `t` strictly between `α` and `β`
  zujoo
  have hαt : α < t ∧ t < β := by
    rcases lt_or_gt_of_ne hd with hs | hs
    · zuejy
      · zufeq
      · zuinp
        zueop
    · zuejy
      · zuinp
        zueop
      · zufeq
  refine ⟨?_, by_simp_all, by_grind, by_grind⟩
  rw [hpos, ← subSeg_eq_seg M p hαβ]
  exact ⟨t, hαt.1.le, hαt.2.le, rfl⟩
end ShootCut
end
end Chazelle.Core
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
@[expose] public section
structure ShEnv (P : Polygon) (W : ℕ) (H : Host) (C : Chain) (z : Point) (σ : ℝ) (c : Config) :
    Prop where
  hG : GoodEnv P
  hW : hostWords P.n ≤ W
  hD : ChainDescAt c.nmem ztfgq zta H C
  hwf : ChainWF P ztm c.nmem ztfgq
  hreg : ∀ H', HostAt c.nmem ztbagb H' → HostRegular P.n H'
  k1 : c.nreg K1 = 1
  ox : AbsRecW P c 140230 z.1 C.radius
  oy : HRecS P c 140234 z.2 C.radius
  sig : c.nreg 140241 ≤ 1 ∧ ztmfs
  hσ : σ = 1 ∨ σ = -1

/-- The registers the environment reads. -/
def envR (r : ℕ) : Prop :=
  r = 140403 ∨ r = K1 ∨ (140230 ≤ r ∧ r < 140237) ∨ r = 140241 ∨ r = ALLOC

/-- **The environment survives** any step that keeps its registers and the memory. -/
theorem ShEnv.keep {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}
    {c c' : Config} (h : ShEnv P W H C z σ c) (hm : c'.nmem = c.nmem)
    (hr : ∀ r, envR r → c'.nreg r = c.nreg r) : ShEnv P W H C z σ c' := by
  have e403 := hr 140403 ztp
  have eA := hr ALLOC by_tauto
  refine ⟨h.hG, h.hW, by zuonu; exact h.hD, by rw [hm, e403, eA]; exact h.hwf,
    by zuonu; exact h.hreg, by rw [hr K1 by_tauto]; exact h.k1,
    h.ox.copy ztetf ztetf
      ztetf ztetf,
    h.oy.copy ztetf ztetf
      ztetf, ?_, h.hσ⟩
  rw [hr 140241 by_tauto]; exact h.sig
theorem ShEnv.frame {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}
    {c c' : Config} {B : ℕ → Bool} (h : ShEnv P W H C z σ c) (hf : FrameB B c c')
    (hB : ∀ r, envR r → B r = false) : ShEnv P W H C z σ c' :=
  h.keep hf.2.2.1 fun r hr => hf.1 r ztfsg

/-! ## Loading a point record -/

/-- The point record of the walk position `(e, h)` into `B … B + 10`. -/
def ptLoad (e h B : ℕ) : Stmt :=
  .seq (block (copies [ztsti, ztstj, ztstl]))
    (.seq ptKey (.seq (block (copies [ztsve, ztpvv, ztpvx, ztpvz,
      ztpwa, ztpwb, ztpwc, ztpwd, ztpwe,
      ztpvw])) (.instr (.constN (B + 5) 0))))

/-- The registers written by `ptLoad _ _ B`. -/
def Bld (B r : ℕ) : Bool := Bprim r || decide ztdfd || decide (B ≤ r ∧ r < B + 11)

/-- The point record of `z` at `B`. -/
def PtRecB (P : Polygon) (c : Config) (B : ℕ) (z : Point) (R : ℝ) : Prop :=
  AbsRec P c B z.1 R ∧ HRecS P c ztow z.2 R ∧ FRec P c ztlw z
variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}

/-- The facts of the environment that loading a point record needs. -/
structure LdEnv (P : Polygon) (W : ℕ) (H : Host) (C : Chain) (c : Config) : Prop where
  hG : GoodEnv P
  hW : hostWords P.n ≤ W
  hD : ChainDescAt c.nmem ztfgq zta H C
  hwf : ChainWF P ztm c.nmem ztfgq
  hreg : ∀ H', HostAt c.nmem ztbagb H' → HostRegular P.n H'
theorem ShEnv.ld {c : Config} (E : ShEnv P W H C z σ c) : LdEnv P W H C c :=
  ⟨E.hG, E.hW, E.hD, E.hwf, E.hreg⟩
variable (c : Config)
theorem ptLoad_exec' (hw : WordsBounded W c) (E : LdEnv P W H C c)
    {e h B : ℕ} (he : 140000 ≤ e ∧ e < 150000) (hh : 140000 ≤ h ∧ h < 150000)
    (hB : 140000 ≤ B ∧ B + 11 ≤ 150000)
    (hen : c.nreg e < (chainModel C).W.n)
    (hp : ProperPos ztc zta P.n ztkv)
    (hy : c.nreg h = 0 ∨
      |((chainModel C).pos (Qof P) ⟨c.nreg e, c.nreg h⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + 15800 ≤ W) :
    ∃ c' k, Exec P W ztlrw c c' k ∧ k ≤ 15820 ∧
      PtRecB P c' B ztymv C.radius ∧
      FrameB ztuwt c c' ∧
      (6 ≤ c.nreg e → (c.nreg e < 2 * C.m + 6 ∨
        (chainModel C).param zta ztkv = 0) → c'.nreg (B + 7) = 1) := by
  obtain ⟨c₁, e₁, v₁, k₁, rr₁, m₁, rm₁, o₁⟩ := copies_exec (P := P)
    [ztsti, ztstj, ztstl] c hw by_grind by_simp
  zutx
  obtain ⟨v00, v01, v02⟩ := v₁
  have k₁' : ∀ r, ¬ ztdfd → c₁.nreg r = c.nreg r := fun r hr =>
    k₁ r (by first | (simp; done) | (simp; omega))
  zuhwk
  have hW' := E.hW
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, -⟩ := ptKey_meets P W c₁ e₁.wb_right
    ⟨E.hG, E.hW, by rw [hA₁, m₁, v00]; exact E.hwf, H, C, by zunqj; exact E.hD,
      ⟨by_omega, by_simp_all, by_simp_all,
        by zunqj; exact E.hreg⟩⟩ by_simp_all
  replace hk₂ : k₂ ≤ 15800 := hk₂
  have pr' := post₂ H C (by zunqj; exact E.hD)
  have pr : PtRec P c₂ ((chainModel C).pos zta ztrbr) C.radius :=
    pr'.1
  have fl : 6 ≤ c.nreg e → (c.nreg e < 2 * C.m + 6 ∨
      (chainModel C).param zta ztkv = 0) → c₂.nreg 50216 = 1 := by
    have := pr'.2; grind
  rw [v01, v02] at pr
  obtain ⟨ax, hy', fr⟩ := pr
  have F₂ := exec_frameB e₂ wr_ptKey
  -- the copies
  obtain ⟨c₃, e₃, v₃, k₃, rr₃, m₃, rm₃, o₃⟩ := copies_exec (P := P) [ztsve, ztpvv,
    ztpvx, ztpvz, ztpwa, ztpwb, ztpwc,
    ztpwd, ztpwe, ztpvw] c₂ e₂.wb_right (by first | (simp; done) | (simp; omega))
    by_simp
  zvmwt at v₃
  obtain ⟨w0, w1, w2, w3, w4, w6, w7, w8, w9, w10⟩ := v₃
  have e₄ := Exec.constN (P := P) e₃.wb_right zter 0 by_omega
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg (B + 5) 0 } with hc₄
  have g₄ : ∀ r, r ≠ B + 5 → c₄.nreg r = c₃.nreg r := fun r hr => by
    zunbf; zunif
  have ex : Exec P W ztlrw c c₄ (3 + (k₂ + (10 + 1))) := by
    unfold ptLoad
    exact .seq e₁ ztcb
  refine ⟨c₄, _, ex, by_omega, ztcg, ?_, fun h1 h2 => by_grind⟩
  · exact absRec_copy' ax by_grind by_grind
      by_grind by_grind
  · have n4 : c₄.nreg ztow = c₂.nreg 50214 := by_grind
    have n5 : c₄.nreg (B + 4 + 1) = 0 := by zunbf; simp
    have n6 : c₄.nreg (B + 4 + 2) = c₂.nreg 50215 := by
      grind
    rcases hy' with ⟨k, hv⟩ | ⟨k, hv⟩ | ⟨k, hv, hl, he'⟩
    · exact Or.inl ztryy
    · exact Or.inr (Or.inl ztryy)
    · exact Or.inr (Or.inr ⟨n4.trans k, hv, n5, by_grind, by_grind⟩)
  · intro h7
    have n7 : c₄.nreg ztlw = c₂.nreg 50216 := by_grind
    obtain ⟨s, hs, hl, hv⟩ := fr by_omega
    refine ⟨s, NFLoc.symPtIn_copy hs ?_ ?_ ?_, hl, hv⟩
    · grind
    · grind
    grind
  · refine ztcxw
    · zuggs
      rw [g₄ r by_omega, k₃ r (by first | (simp; done) | (simp; omega)), F₂.1 r hr.1.1, k₁' r hr.1.2]
    · zuggs
      show c₃.rreg r = c.rreg r
      rw [rr₃, F₂.2.1 r hr.1.1, rr₁]
    · show c₃.nmem = c.nmem; zunyf
    · show c₃.rmem = c.rmem; rw [rm₃, F₂.2.2.2.1, rm₁]
    · show c₃.output = c.output; rw [o₃, F₂.2.2.2.2, o₁]
theorem ptLoad_exec (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {e h B : ℕ} (he : 140000 ≤ e ∧ e < 150000) (hh : 140000 ≤ h ∧ h < 150000)
    (hB : 140000 ≤ B ∧ B + 11 ≤ 150000)
    (hen : c.nreg e < (chainModel C).W.n)
    (hp : ProperPos ztc zta P.n ztkv)
    (hy : c.nreg h = 0 ∨
      |((chainModel C).pos (Qof P) ⟨c.nreg e, c.nreg h⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + 15800 ≤ W) :
    ∃ c' k, Exec P W ztlrw c c' k ∧ k ≤ 15820 ∧
      PtRecB P c' B ztymv C.radius ∧
      FrameB ztuwt c c' := by
  obtain ⟨c', k, ex, hk, pr, fr, -⟩ := ptLoad_exec' c hw E.ld he hh hB hen hp hy hroom
  grind
end
end ShootCut
end Chazelle.Core
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
@[expose] public section
def CandAt (P : Polygon) (C : Chain) (c : Config) (b : ℕ) (S : Set Point) (z : Point) (σ : ℝ) :
    Prop :=
  c.nreg b ≤ 1 ∧ (c.nreg b ≠ 1 → NoHit S z σ) ∧
    (c.nreg b = 1 → ∃ x : ℝ, AbsRec P c ztds x C.radius ∧ FirstHit S z σ ztewx ∧
      ProperPos ztc zta P.n ztbgg ∧
      c.nreg ztnrm < (chainModel C).W.n ∧
      (chainModel C).pos zta ztbgg = ztewp)
theorem FrameB.wk {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → B' r = true) : FrameB B' c c' :=
  ⟨fun r hr => h.1 r by_grind,
    fun r hr => h.2.1 r by_grind,
    h.2.2⟩

/-- One register update is framed by any set containing the register. -/
theorem frameB_upd {B : ℕ → Bool} (c : Config) {r : ℕ} (v : ℕ) (hB : B r = true) :
    FrameB B c ({ c with nreg := upd c.nreg r v } : Config) :=
  ⟨fun r' hr' => by
    have : r' ≠ r := fun h => by_simp_all
    simp_all, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The registers written by the segment machine. -/
def Bedge (r : ℕ) : Bool :=
  Bprim r || decide ztdfd || decide (140220 ≤ r ∧ r < 140227) ||
    decide (140262 ≤ r ∧ r < 140330)
theorem Bedge_env (r : ℕ) (h : envR r) : Bedge r = false := by
  zufdg
  simp only [Bedge, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not, K1, ALLOC] at h ⊢
  omega
variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}

/-! ## Leaves -/

/-- No candidate. -/
def cand0 : Stmt := .instr (.constN 140220 0)
variable (c : Config)
theorem cand0_exec (hw : WordsBounded W c) {S : Set Point} (h : NoHit S z σ) :
    ∃ c' k, Exec P W cand0 c c' k ∧ k = 1 ∧ CandAt P C c' 140220 S z σ ∧
      FrameB Bedge c c' := by
  refine ⟨_, _, Exec.constN hw 140220 0 by_omega, rfl,
    ⟨by_simp, fun _ => h, fun h' => by_simp_all⟩, frameB_upd c 0 by_decide⟩

/-- The candidate from the record at `A` and the position in `e`, `h`. -/
def candFrom (A e h : ℕ) : Stmt :=
  .seq (block (copies [ztsrs, ztpsu, ztpsv, ztpsw,
    ztsrt, ztsru])) (.instr (.constN 140220 1))
theorem candFrom_exec (hw : WordsBounded W c) (hW1 : 1 ≤ W) {A e h : ℕ}
    (hA : A + 4 ≤ 140221 ∨ 140227 ≤ A) (he : e < 140221 ∨ 140227 ≤ e)
    (hh : h < 140221 ∨ 140227 ≤ h) {S : Set Point} {x : ℝ}
    (hx : AbsRec P c A x C.radius) (hF : FirstHit S z σ ztewx)
    (hp : ProperPos ztc zta P.n ztkv)
    (hen : c.nreg e < (chainModel C).W.n)
    (hpos : (chainModel C).pos zta ztkv = ztewp) :
    ∃ c' k, Exec P W ztrnc c c' k ∧ k = 7 ∧ CandAt P C c' 140220 S z σ ∧
      FrameB Bedge c c' := by
  obtain ⟨c₁, e₁, v₁, k₁, rr₁, m₁, rm₁, o₁⟩ := copies_exec (P := P) [ztsrs,
    ztpsu, ztpsv, ztpsw, ztsrt, ztsru] c hw
    ztbaw by_simp
  zutx
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := v₁
  have e₂ := Exec.constN (P := P) e₁.wb_right 140220 1 hW1
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 140220 1 } with hc₂
  have g : ∀ r, r ≠ 140220 → c₂.nreg r = c₁.nreg r := fun r hr => by zumxp; zumwy
  refine ⟨c₂, _, .seq e₁ e₂, rfl, ⟨by_rfl, fun h' => by_tauto, fun _ =>
    ⟨x, absRec_copy' hx by_grind by_grind
      by_grind by_grind, hF,
      by grind,
      by grind,
      by grind⟩⟩, ?_⟩
  refine ⟨fun r hr => ?_, fun r _ => by_grind, by
    omega, by_omega,
    by omega⟩
  simp only [Bedge, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
  rw [g r by_omega, k₁ r ztbaw]

/-! ## Ahead of the origin -/

/-- The bit "the point of the record at `A` is ahead of the origin". -/
def aheadT (A dst : ℕ) : Stmt := .ifLtN 140241 K1 (xLess A 140230 dst) (xLess 140230 A dst)
theorem aheadT_exec (hw : WordsBounded W c) (E : ShEnv P W H C z σ c) {A dst : ℕ}
    (hA : 10500 ≤ A) (hdst : 10500 ≤ dst) {x : ℝ} (hx : AbsRec P c A x C.radius)
    (hne : x ≠ z.1) :
    ∃ c' k, Exec P W (aheadT A dst) c c' k ∧ k ≤ 252 ∧ BitIs c' dst (0 < σ * ztudv) ∧
      FrameB ztdks c c' := by
  zubfx
  unfold aheadT
  zudxb
  · have hσ : ztgbb := by
      zufzo
      · have := E.sig.2.2 h; rw [E.k1] at hs; omega
      omega
    obtain ⟨c', k, ex, hk, bt, f⟩ := xLess_exec E.hG hW c hw hA by_norm_num hdst E.k1 ztuwf
      E.ox (Or.inl hne)
    refine ztich
    simp_all
  · zucmy
    obtain ⟨c', k, ex, hk, bt, f⟩ := xLess_exec E.hG hW c hw by_norm_num hA hdst E.k1 E.ox
      ztuwf (Or.inl ztnr)
    refine zticg
    simp_all

/-- The bit "`V` is nearer than `U`" (the negation of `σ U.1 ≤ σ V.1`). -/
def nearT (dst : ℕ) : Stmt := .ifLtN 140241 K1 (xLess 140270 140281 dst) (xLess 140281 140270 dst)
theorem nearT_exec (hw : WordsBounded W c) (E : ShEnv P W H C z σ c) {dst : ℕ}
    (hdst : 10500 ≤ dst) {xU xV : ℝ} (hU : AbsRec P c 140270 xU C.radius)
    (hV : AbsRec P c 140281 xV C.radius) :
    ∃ c' k, Exec P W (nearT dst) c c' k ∧ k ≤ 252 ∧ BitIs c' dst (¬ σ * xU ≤ σ * xV) ∧
      FrameB ztdks c c' := by
  zubfx
  have st : ztdro :=
    fun {r} {x} h hk => by
      zubhs
  unfold nearT
  zudxb
  · have hσ : ztgbb := by
      zufzo
      · have := E.sig.2.2 h; rw [E.k1] at hs; omega
      omega
    obtain ⟨c', k, ex, hk, bt, f⟩ := xLess_exec E.hG hW c hw by_norm_num by_norm_num hdst E.k1
      ztuwd ztuwe (Or.inr ⟨st hU, st hV⟩)
    refine ztich
    simp_all
  · zucmy
    obtain ⟨c', k, ex, hk, bt, f⟩ := xLess_exec E.hG hW c hw by_norm_num by_norm_num hdst E.k1
      ztuwe ztuwd (Or.inr ⟨st hV, st hU⟩)
    refine zticg
    simp_all
end
end ShootCut
end Chazelle.Core
namespace Chazelle.Core
namespace DrvT
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sidePt IsHChordIn)
open Chazelle.Visibility (hseg)
open BuildRegions (famOf)

/-- The triples `(h, lp, rp)` of the chord records of a normal form. -/
def triplesOf (N : NF) : List zte := N.chords.map fun r => ztlm

/-- **The output of the filter.** -/
def transL (li : Bool) (n c₀ : ℕ) (L₀ : List zte) : List zte :=
  (L₀.filter ztbdh).map (trT n c₀)
theorem transL_length_le (li : Bool) (n c₀ : ℕ) (L₀ : List zte) :
    (transL li n c₀ L₀).length ≤ L₀.length := by
  unfold transL; grind
variable (M : Model)
/-- The chords of the computed normal form are the chords of the list. -/
theorem F_buildNF (Q : Polygon) (L : List zte) (E : List ℕ) :
    (BuildNF.buildNF M Q L E).F M Q = famOf M Q L := by
  zubcj
  simp only [NF.F, BuildNF.buildNF, List.mem_map, List.mem_range, famOf]
  constructor
  · zubsg
    exact ztpey
  · zuod
    zuve
    refine ztexo
    have : ztxpo := by
      simp_all
    unfold BuildNF.chordRec
    zubk
    rfl

/-- **Two chords of a domain containing the same nondegenerate segment are equal.** -/
theorem chord_eq_of_sub {D : Set Point} {y₁ a₁ b₁ y₂ a₂ b₂ y a b : ℝ}
    (h₁ : IsHChordIn D y₁ a₁ b₁) (h₂ : IsHChordIn D y₂ a₂ b₂) (hab : a < b)
    (s₁ : hseg y a b ⊆ hseg y₁ a₁ b₁) (s₂ : hseg y a b ⊆ hseg y₂ a₂ b₂) :
    hseg y₁ a₁ b₁ = hseg y₂ a₂ b₂ := by
  obtain ⟨ey₁, ha₁, hb₁⟩ := hseg_sub hab.le s₁
  obtain ⟨ey₂, ha₂, hb₂⟩ := hseg_sub hab.le s₂
  have hm : (ztwsj : Point) ∈ hseg y a b := ztbci
  rcases Chazelle.Chain.hchordIn_inter h₁ h₂ (s₁ hm) (s₂ hm) with ⟨e1, e2, e3⟩ | ⟨hp, -⟩
  · simp_all
  grind
variable {P : Polygon} {C : Chain} {N : NF}

/-- The record of a triple has the chord and attachment of the record. -/
theorem recOf_triple (Q : Polygon) (r : CRec) :
    (recOf ztlm).toSet M Q = r.toSet M Q := rfl

/-- **The records of a valid chain normal form.** -/
theorem triples_props {Q : Polygon} (hN : IsNF ztc Q N) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ triplesOf N) :
    x.1 < Q.n ∧ (recOf x).toSet ztc Q ∈ (chainModel C).Adm ∧
      (recOf x).Attached ztc Q ∧
      (recOf x).toSet ztc Q ∈ N.F ztc Q := by
  obtain ⟨hFam, -, hatt, reg, -, -, -, -, -, hh, -⟩ := hN
  unfold triplesOf at hx
  zufyz
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  have hci : ztpks := by
    zudly
    simp_all
  have hmem : N.chords[i].toSet _ Q ∈ N.F ztc Q :=
    ⟨_, List.getElem_mem hi, rfl⟩
  refine ⟨?_, hFam.2.1 hmem, ?_, hmem⟩
  · have := hh i hi; simp_all
  · have := hatt i hi; rw [hci] at this; tauto

/-- The chain chords of the records are pairwise distinct. -/
theorem nodup_triples_toSet {Q : Polygon} (hN : IsNF ztc Q N) :
    ((triplesOf N).map fun x => (recOf x).toSet ztc Q).Nodup := by
  obtain ⟨-, hdist, -⟩ := hN
  unfold triplesOf
  zuczm
  zuigo

  simp only [List.getElem_map, Function.comp] at hij
  have e1 : ztmto := by
    zudly
    grind
  have e2 : ztmtp := by
    zudly
    grind
  have := hdist i.1 j.1 ztjqz
    ztjqz (by zvmws; tauto)
  omega

/-- **The number of chords** of a valid normal form is its number of records. -/
theorem ncard_F {M : Model} {Q : Polygon} {N : NF}
    (hdist : ∀ i i', i < N.nChords → i' < N.nChords →
      (N.chord i).toSet M Q = (N.chord i').toSet M Q → i = i') :
    (N.F M Q).ncard = N.chords.length := by
  have hF : N.F M Q = {c | c ∈ N.chords.map fun r => r.toSet M Q} := by
    zubcj
    simp only [NF.F, mem_ofPred_eq, List.mem_map]
    grind
  have hnd : (N.chords.map fun r => r.toSet M Q).Nodup := by
    zuigo

    simp only [List.getElem_map] at hij
    have e1 : ztmto := by
      zudly
      grind
    have e2 : ztmtp := by
      zudly
      grind
    exact Fin.ext (hdist i.1 j.1 (by unfold NF.nChords; grind)
      ztjqz by_simp_all)
  rw [hF, show {c | c ∈ N.chords.map fun r => r.toSet M Q} =
      ((N.chords.map fun r => r.toSet M Q).toFinset : Set _) by
    ext c; simp, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map]
section filt
variable {Q : Polygon}
variable (hQ : Q.Simple) (T : Trans.Top Q C) (hD : Trans.DistinctH Q) {li : Bool}
  (hli : li = true ↔ Mountain.LeftInside Q)
include hQ T hD hli

/-- **(T-R1) The chords of the filtered list are the pieces.** -/
theorem famOf_transL (hN : IsNF ztc Q N) :
    famOf ztd Q ztzhi =
      Trans.pieces Q ztwjh := by
  zucwk
  zubb
  have hh' := hD C.m 0 by_omega by_omega by_omega
  zufsm
  constructor
  · rintro ⟨x', hx', rfl⟩
    zubmq

    zudiy
    obtain ⟨h1, h2, h3, h4⟩ := triples_props hN hxm
    zubbv
    exact ⟨hA, _, h4, hsub⟩
  · rintro ⟨hdA, c, ⟨r, hr, rfl⟩, hdc⟩
    have hxm : ztlm ∈ triplesOf N := List.mem_map.2 by_grind
    zubrj
    rw [← recOf_triple] at hdc
    cases hk : keepT li Q.n _ ztlm with
    | false => exact (rec_dropped hQ T hD hli h1 h2 h3 hk hdA hdc).elim
    | true =>
      zubbv
      zudrt
      zvmyh at hsub hdc
      have := Trans.one_piece hQ T hh' hch hdA hA hdc hsub
      refine ⟨_, ?_, this⟩
      unfold transL
      zubfo

/-- **(T-R2) The filtered list is a valid chord list of the interior model.** -/
theorem chordTriplesOK_transL (hN : IsNF ztc Q N)
    (hFam : (interiorModel Q).ChordFamily Q (Trans.pieces Q ztwjh)) :
    ChordTriplesOK ztd Q ztzhi := by
  zucwk
  zubb
  zudfi
  · have := famOf_transL hQ T hD hli hN
    unfold famOf at this
    simp_all
  · unfold transL
    zuczm
    refine List.Nodup.map_on (fun x hx x' hx' hxx => ?_)
      ((List.Nodup.of_map _ ztvzz).filter _)
    zudiy
    obtain ⟨hxm', hk'⟩ := List.mem_filter.1 hx'
    zubrj
    obtain ⟨h1', h2', h3', -⟩ := triples_props hN hxm'
    zubbv
    obtain ⟨hA', hsub', -⟩ := rec_kept hQ T hD hli h1' h2' h3' hk'
    simp only [Function.comp] at hxx
    rw [hxx] at hsub
    zudrt
    obtain ⟨y', a', b', hch', -, hcab'⟩ := h2'
    obtain ⟨y'', a'', b'', hch'', hd⟩ := hA'
    zvnej at hsub hsub'
    zvmyh at hsub
    rw [hcab'] at hsub'
    have heq := chord_eq_of_sub hch hch' hch''.lt hsub hsub'
    refine List.inj_on_of_nodup_map ztvzz hxm hxm' ?_
    simp_all
  · intro x' hx'
    zubmq

    zudiy
    zubrj
    exact (rec_kept hQ T hD hli h1 h2 h3 hk).2.2
  · intro x' hx'
    zubmq

    obtain ⟨hxm, -⟩ := List.mem_filter.1 hx
    exact (triples_props hN hxm).1
end filt

/-! ## The math of the transition -/

/-- **The math of the transition**: from the canonical normal form of the top chain, the
filtered list is a valid interior chord list whose family has degree `≤ 4` and weight
`≤ 2^(⌈βp⌉+12)`, with at most as many chords as the normal form, which satisfies the count of
Lemma 2.3. -/
theorem trans_math (hG : GoodEnv P) (hC : TopChain P C)
    (hN : IsCanonicalNF ztc zta N ztmow 4) {li : Bool}
    (hli : li = true ↔ Mountain.LeftInside zta) :
    ChordTriplesOK ztwiq zta ztxyd ∧
      (interiorModel zta).DegLe
        ztbaqe 4 ∧
      (interiorModel zta).Semigranular
        ztbaqe
        (2 ^ ztzjs) ∧
      (transL li P.n ztpe ztddq).length ≤ (N.F ztc zta).ncard ∧
      (N.F ztc zta).ncard * (gradeGran ztcdz + 1) ≤
        840 * (2 * ztch + 1) := by
  zurr
  zubp
  have T : Trans.Top _ C := ⟨hC.1, hC.2.1, by zvmxq; exact hC.2.2⟩
  zudyf
  have hP : C.P.Simple := by zuowh; exact hQ
  obtain ⟨hNF, hdeg, hgran, hdec⟩ := hN
  have hFam0 : (chainModel C).ChordFamily C.P ztwjq := by
    zuowh; exact hNF.1
  obtain ⟨hFam, hdegP, hwtP, -⟩ := Trans.transition hQ T hD hFam0 hgran.1 hdeg
  have hfam := famOf_transL hQ T hD hli hNF
  zulrd
  refine ⟨chordTriplesOK_transL hQ T hD hli hNF hFam, by_simp_all, ?_, ?_, ?_⟩
  · rw [hfam]
    zucne
    refine (hwtP U hU).trans ?_
    have := DownStep.gamma1_le ztcdz
    unfold DownStep.gamma1 at this
    unfold topGran
    grind
  · rw [ncard_F hNF.2.1]
    have := transL_length_le li (Qof P).n ztpe ztddq
    unfold triplesOf at this; rw [List.length_map] at this
    tauto
  · have := DownMath.trans_count hP ⟨hNF, hdeg, hgran, hdec⟩
    zubdb
    unfold topGran at this
    have hm : ztsaw := by have := hC.2.2; omega
    omega
end
end DrvT
end Chazelle.Core
namespace Chazelle.Core
namespace DownMath
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost
variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **The start of a cyclic interval**: if `x` is not in `(a, b)` but the gap `(x, y)` is, then
`x = a`. -/
theorem cyc_start {n : ℝ} {a b x y : ℝ} (hxy : x ≠ y) (hx0 : 0 ≤ x) (hxn : x < n)
    (hy0 : 0 ≤ y) (hyn : y < n) (_ha0 : 0 ≤ a) (_han : a < n)
    (hsub : ∀ z, 0 ≤ z → z < n → sideInArc x y z → sideInArc a b z)
    (hnot : ¬ sideInArc a b x) : x = a := by
  -- a point of the gap just after `x`, below any given bound `u > x`
  have hpt : ∀ u, x < u → ∃ z, x < z ∧ z < u ∧ 0 ≤ z ∧ z < n ∧ sideInArc a b z := by
    zubgt
    zujeo
    · refine ⟨(x + min u y) / 2, ?_, ?_, ?_, ?_, ?_⟩
      · grind
      · grind
      · grind
      · grind
      · apply hsub _ by_grind by_grind
        zujv
    · refine ⟨(x + min u n) / 2, ?_, ?_, ?_, ?_, ?_⟩
      · grind
      · grind
      · grind
      · grind
      · apply hsub _ by_grind
          by_grind
        zujv
  zuluy
  zuul
  · zuhpr
    zuct
    zuto
    · grind
    grind
  · zuhps
    zudrw
    zuct
    have hxa : x < a := by_grind
    grind

/-- The length of the group of host keys of arc `t`: its `d t + 1` keys from the start to the
key before the next group, plus the junction. -/
def grpLen (d J : ℕ → ℕ) (t : ℕ) : ℕ := d t + 1 + J t

/-- The offset of group `t`: the sum of the lengths of the groups before it. -/
def grpOff (d J : ℕ → ℕ) (t : ℕ) : ℕ := ∑ s ∈ Finset.range t, grpLen d J s
theorem grpOff_succ (d J : ℕ → ℕ) (t : ℕ) : grpOff d J ztbx = grpOff d J t + grpLen d J t := by
  unfold grpOff; rw [Finset.sum_range_succ]
section
variable (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
  (hR : R ∈ (interiorModel Q).regions S)
include hQ hFam hne hR
variable {j : ℕ}
/-- **An arc gap at a cut starts an arc of `R`.** -/
theorem start_of_arcGap (hj : j < nk ztd S R)
    (hA : ArcGap ztd S R j)
    (hcut : (interiorModel Q).IsCut S ztxxh) :
    ∃ b, (interiorModel Q).IsArc S R ztxxh b := by
  zuceu

  zulk
  zubnm
  zufin
  zuiaj
  have hbx := hostKeys_bounds (hk_mem hM hFam.2.1 hFam.1 hj)
  have hby := hostKeys_bounds (hk_mem hM hFam.2.1 hFam.1 hsj)
  have e := cyc_start (hk_succ_ne hM hFam.2.1 hFam.1 by_omega hj) hbx.1 hbx.2 hby.1 hby.2
    harc.1 harc.2.1 hsub (fun h => harc.2.2.2.2.2.1 _ h hcut)
  grind

/-- **The start of an arc starts an arc gap.** -/
theorem arcGap_of_start (hj : j < nk ztd S R) {b : ℝ}
    (harc : (interiorModel Q).IsArc S R ztxxh b) :
    ArcGap ztd S R j := by
  zubwf
  zudrn
  have := hk_inj hM hFam.2.1 hFam.1 hD.hil hj hD.hl
  zumo
  have h := arcData_gap hQ hFam hne hR harc hD hD.hd0
  rwa [add_zero, Nat.mod_eq_of_lt hD.hil] at h

/-- **The arcs of `R` in cyclic order** (see the module doc). -/
theorem arcs_cycle (hdh : DistinctHeights Q) {k : ℕ} (hk1 : 0 < k) (a b : ℕ → ℝ)
    (harc : ∀ t, t < k → (interiorModel Q).IsArc S R ztqdm ztqds)
    (hsort : ∀ t t', t < t' → t' < k → a t < a t')
    (hcomp : ∀ a' b', (interiorModel Q).IsArc S R a' b' → ∃ t, t < k ∧ a t = a' ∧ b t = b') :
    ∃ i d J : ℕ → ℕ,
      (∀ t, t < k → ArcData ztd S R ztqdm ztqds ztvww (d t)) ∧
      (∀ t, t < k → (J t = 0 ↔
        ArcGap ztd S R (ztetk % nk ztd S R))) ∧
      (∀ t, t < k → J t ≤ 1) ∧
      (∀ t, t < k → i t = i 0 + grpOff d J t) ∧
      grpOff d J k = nk ztd S R := by
  classical
  zuhm
  zuhoe
  zulk
  zubl

  zubnm
  have hAD : ∀ t, t < k → ∃ i d, ArcData I S R ztqdm ztqds i d :=
    fun t ht => arc_keys hM hF hfin hne hR by_simp_all
  choose! i d hD using hAD
  set J : ℕ → ℕ := fun t => if ArcGap I S R ztzzp then 0 else 1 with hJ
  have hJ0 : ∀ t, (J t = 0 ↔ ArcGap I S R ztzzp) := by
    simp_all
  have hJ1 : ∀ t, J t ≤ 1 := by intro t; simp only [hJ]; split_ifs <;> omega
  -- the start indices increase
  have hil : ∀ t, t < k → i t < N := fun t ht => (hD t ht).hil
  have hmono : ∀ t t', t < t' → t' < k → i t < i t' := by
    intro t t' htt ht'
    zufm
    zubuf
    · have := hk_strictMono hM hF hfin h (hil t by_omega)
      rw [(hD t' ht').hl, (hD t by_omega).hl] at this
      grind
    · have := hsort t t' htt ht'
      rw [← (hD t' ht').hl, ← (hD t by_omega).hl, h] at this
      simp_all
  have hi0 : ∀ t, t < k → i 0 ≤ i t := by
    zucj
    rcases Nat.eq_zero_or_pos t with rfl | h
    · omega
    grind
  -- an arc start is an arc gap
  have hstartA : ∀ s, s < k → ArcGap I S R (i s) := by
    zugg
    exact arcGap_of_start hQ hFam hne hR by_simp_all (by rw [(hD s hs).hl]; tauto)
  -- the facts after the end of arc `t`
  have hafter : ∀ t, t < k →
      ChordGap I S R (ztjyo % N) ∧
      (∃ s, s < k ∧ i s = (i t + grpLen d J t) % N) ∧
      (∀ j, 0 < j → j < grpLen d J t → ∀ s, s < k → i s ≠ ztrsg % N) := by
    zucj
    have hDt := hD t ht
    set m := ztjyo % N with hm
    have hmN : m < N := Nat.mod_lt _ by_omega
    have hbm := hDt.hr
    obtain ⟨c, ⟨hc, htc⟩, pc, tc, hAc, hec⟩ := hM.exists_exit_at_end hF hfin hne hR (harc t ht)
    have hx : ztlyl := ⟨c, hc, htc, pc, tc, hAc, by_grind⟩
    have hprev : prevIdx N m = ztzmg % N := by
      have e : m = (ztzmg % N + 1) % N := by
        rw [hm, Nat.mod_add_mod, show i t + ztlmv + 1 = i t + d t by have := hDt.hd0; omega]
      zvmwe; exact prevIdx_succ ztcv
    have hAp : ArcGap I S R (prevIdx N m) := by
      rw [hprev]; exact arcData_gap hQ hFam hne hR by_grind hDt (by have := hDt.hd0; omega)
    obtain ⟨hCm, hnext⟩ := end_chord hQ hFam hne hR hmN hx hAp
    set q₁ := ztbl % N with hq₁
    have hq₁N : q₁ < N := Nat.mod_lt _ by_omega
    have hq₁e : q₁ = ztetk % N := by_grind
    obtain ⟨pz, tz, hAz, hez⟩ := hnext c hc htc pc tc hAc by_grind
    have hcut₁ : I.IsCut S (hk I S R q₁) := ztkjp
    -- no arc start at the end
    have hnot_m : ∀ s, s < k → i s ≠ m := by
      intro s hs he
      exact not_arc_and_chord hM hF hfin by_omega hmN by_grind hCm
    -- no arc start inside the arc
    have hnot_in : ∀ j, 0 < j → j < d t → ∀ s, s < k → i s ≠ ztrsg % N := by
      intro j hj0 hjd s hs he
      have hin := (hDt.inner j hj0 hjd).2
      rw [← he, (hD s hs).hl] at hin
      exact (harc t ht).2.2.2.2.2.1 _ hin (WalkAx.arc_cuts hne (harc s hs)).1
    by_cases hA₁ : ArcGap I S R q₁
    · -- the next key starts the next arc
      have hJt : J t = 0 := by_grind
      obtain ⟨b', hb'⟩ := start_of_arcGap hQ hFam hne hR hq₁N hA₁ hcut₁
      zudjb

      · have := hk_inj hM hF hfin zttnr hq₁N ztirl
        rw [this, hq₁e]; unfold grpLen; zuowt; congr 1
      · zubwz

        · zuitm
        · rw [show j = d t by omega]; exact hnot_m s' hs'
    · -- a junction
      have hJt : J t = 1 := by
        grind
      have hCp : ChordGap I S R (prevIdx N q₁) := by rw [hq₁, prevIdx_succ hmN]; omega
      obtain ⟨-, hA₂⟩ := junction hQ hFam hne hR hdh hq₁N hCp hA₁
      have hC₁ :=
        (gap_cases hM hF hfin hne hR by_omega hq₁N).resolve_left hA₁
      obtain ⟨c'', hc'', -, p₂, -, t₂, -, hA₂', -, he₂, -⟩ := hC₁
      have hq₂N : (q₁ + 1) % N < N := Nat.mod_lt _ by_omega
      have hcut₂ : I.IsCut S _ := ⟨c'', hc'', p₂, t₂, hA₂', he₂⟩
      obtain ⟨b', hb'⟩ := start_of_arcGap hQ hFam hne hR hq₂N hA₂ hcut₂
      zudjb

      · have := hk_inj hM hF hfin zttnr hq₂N ztirl
        rw [this, hq₁e, Nat.mod_add_mod]; unfold grpLen; zuowt; congr 1
      · zubwz

        · zuitm
        · rcases (show j = d t ∨ j = d t + 1 by omega) with rfl | rfl
          · exact hnot_m s' hs'
          grind
  -- the offsets
  have hstep : ∀ t, t < k → (t + 1 < k → i t + grpLen d J t = i ztbx) ∧
      (t + 1 = k → i t + grpLen d J t = i 0 + N) := by
    zucj
    obtain ⟨-, ⟨s, hs, his⟩, hnone⟩ := hafter t ht
    have hdN := (hD t ht).hdN
    have hG : grpLen d J t ≤ N + 1 := by unfold grpLen; have := hJ1 t; omega
    -- the next start is not `i 0` strictly inside the group
    have hle : i t + grpLen d J t ≤ i 0 + N := by
      zufm
      have hj0 : 0 < i 0 + N - i t := by have := hil t ht; omega
      apply hnone _ hj0 by_omega 0 hk1
      rw [show i t + (i 0 + N - i t) = i 0 + N by have := hil t ht; omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt zttnq]
    constructor
    · intro ht1
      -- the next start is `i (t + 1)`
      have hlt : i t + grpLen d J t < i 0 + N := by
        zubug
        · zubh
        · zuhcx

          have h2 := hil _ ht1
          zuiqv
          rw [show i t + ztqrd = i ztbx by omega, Nat.mod_eq_of_lt h2]
      have hgN : i t + grpLen d J t < N ∨ N ≤ i t + grpLen d J t := by_omega
      rcases hgN with hgN | hgN
      · zujhg
        -- `s` is after `t`, and no start lies in between
        have hst : t < s := by
          zufm
          zubuf
          · have := hmono s t h ht; omega
          · subst h; unfold grpLen at his; omega
        rcases (show s = t + 1 ∨ t + 1 < s by omega) with rfl | hs1
        · omega
        · zuhcx

          have h2 := hmono _ s hs1 hs
          zuiqv
          rw [show i t + ztqrd = i ztbx by omega,
            Nat.mod_eq_of_lt by_omega]
      · exfalso
        zujyc
        rw [show i t + grpLen d J t = ztlpw + N by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt by_omega] at his
        have := hi0 s hs
        omega
    · intro ht1
      zubug
      · exfalso
        -- the next start would come after the last one
        rcases Nat.lt_or_ge _ N with hgN | hgN
        · zujhg
          have hst : t < s := by
            by_contra h'; push Not at h'
            rcases h'.lt_or_eq with h' | h'
            · have := hmono s t h' ht; omega
            · subst h'; unfold grpLen at his; omega
          omega
        · zujyc
          rw [show i t + grpLen d J t = ztlpw + N by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt by_omega] at his
          have := hi0 s hs
          omega
      omega
  have hoff : ∀ t, t < k → i t = i 0 + grpOff d J t := by
    zucj
    induction t with
    | zero => simp [grpOff]
    | succ t ih =>
      rw [grpOff_succ, ← Nat.add_assoc, ← ih by_omega]
      exact ((hstep t by_omega).1 ht).symm
  refine ⟨i, d, J, hD, by_grind, by_grind, hoff, ?_⟩
  zugqg
  have h1 := (hstep k' by_omega).2 rfl
  rw [hoff k' by_omega] at h1
  rw [grpOff_succ]
  omega
end
end
end DownMath
end Chazelle.Core
namespace Chazelle.Core
namespace DownMath
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost
open BuildNF (buildNF wposOf gapStarts)
variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-- A **chord position** of `N`: an end (`lpos` or `rpos`) of one of its chord records. -/
def ChordPos (N : NF) (x : WPos) : Prop :=
  ∃ i, i < N.nChords ∧ (x = (N.chord i).lpos ∨ x = (N.chord i).rpos)

/-! ## Chord positions -/
section
variable {M : Model} {N : NF}

/-- **A chord position is an attachment of its chord**, at the height of its height vertex. -/
theorem chordPos_attach (hN : IsNF M Q N) {i : ℕ} (hi : i < N.nChords) {x : WPos}
    (hx : x = (N.chord i).lpos ∨ x = (N.chord i).rpos) :
    (N.chord i).toSet M Q ∈ N.F M Q ∧
      SideAttach M.W ztdef x.edge ztbyt ∧
      M.key Q x = x.edge + M.param Q x ∧ x.hgt = (N.chord i).h + 1 ∧ (N.chord i).h < Q.n ∧
      (sidePt M.W x.edge ztbyt).2 = (Q.vtx (N.chord i).h).2 := by
  obtain ⟨-, -, hatt, reg, -, -, -, -, -, hh, -⟩ := hN
  have hmem : ztdjo := ⟨N.chord i, by
    unfold NF.chord; rw [List.getD_eq_getElem _ _ hi]; grind, rfl⟩
  have hA : SideAttach M.W ztdef x.edge ztbyt := by
    zudsl
    · exact (hatt i hi).1
    · exact (hatt i hi).2
  refine ⟨hmem, hA, rfl, by rcases hx with rfl | rfl <;> rfl, hh i hi, ?_⟩
  have := hA.2.2.2.1
  exact this.1
end

/-! ## The region records of `buildNF` -/
theorem isNF_build (hQ : Q.Simple) (hL : ChordTriplesOK ztd Q L)
    (hperm : E.Perm ztct)
    (hsort : E.Pairwise ztwxw) :
    IsNF ztd Q ztwkc :=
  (BuildNF.isNF_goodModel ztmby hL hperm hsort).1
theorem nChords_build (hQ : Q.Simple) (hL : ChordTriplesOK ztd Q L)
    (hperm : E.Perm ztct)
    (hsort : E.Pairwise ztwxw) :
    (buildNF ztd Q L E).nChords = L.length := by
  have := (BuildNF.isNF_goodModel ztmby hL hperm hsort).2.1
  have h := congrArg List.length this
  simpa [NF.nChords] using h
variable {r : ℕ}
/-- The arcs of region `r` of `buildNF` in record order. -/
theorem region_arcs_build (_hK : 0 < L.length) (hr : r < L.length + 1) :
    ((buildNF ztd Q L E).region r).arcs =
      BuildNF.regArcs ztd Q L E r := by
  zujqc

/-- **The arcs of a region are listed in increasing record order.** -/
theorem region_arcs_sorted (hK : 0 < L.length) (hr : r < L.length + 1) :
    ((buildNF ztd Q L E).region r).arcs.Pairwise ztfvn := by
  rw [region_arcs_build hK hr]
  exact (List.pairwise_lt_range).filter _

/-- **The ends of an arc record are chord positions.** -/
theorem arc_pos (hQ : Q.Simple) (hL : ChordTriplesOK ztd Q L)
    (hperm : E.Perm ztct)
    (hsort : E.Pairwise ztwxw) (hK : 0 < L.length) {j : ℕ}
    (hj : j < (buildNF ztd Q L E).arcs.length) :
    ChordPos ztwkc ((buildNF ztd Q L E).arc j).s ∧
      ChordPos ztwkc ((buildNF ztd Q L E).arc j).e := by
  set N := buildNF ztd Q L E
  zugmy
  have hlen : N.arcs.length = (gapStarts ztd Q L E).length := by
    zuewm
  have hj' : ztxfh := hlen ▸ hj
  have harc := DownDrv.buildNF_arc (M := interiorModel Q) (Q := Q) (E := E) hK hj'
  have hE : ztgtx := by zunoj
  set m := (gapStarts ztd Q L E).getD j 0 with hm
  have hmE : m < E.length := by
    have hmem : m ∈ gapStarts ztd Q L E := by
      simp_all
    exact (BuildNF.Input.mem_gapStarts.1 hmem).1
  have hpos : ∀ u, u < E.length → ChordPos N (wposOf L (E.getD u 0)) := by
    zubgt
    have hc : E.getD u 0 < 2 * L.length := by
      rw [List.getD_eq_getElem _ _ hu]
      exact List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem hu))
    have hc' : E.getD u 0 / 2 < L.length := by_omega
    refine ⟨E.getD u 0 / 2, hnc ▸ hc', ?_⟩
    have hchord : N.chord ztpxl = BuildNF.chordRec ztd Q L E
        ztpxl := by
      zudly
      show ((List.range L.length).map (BuildNF.chordRec ztd Q L E)).getD _ _ = _
      simp_all
    zuowu
    zulci
    split_ifs
    · tauto
    tauto
  have he : N.arc j = _ := harc
  constructor
  · simp_all
  · rw [show (N.arc j).e = wposOf L ztwkh by rw [he]]
    exact hpos _ ztcv
end
end DownMath
end Chazelle.Core
namespace Chazelle.Core
namespace DownMath
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost
open BuildNF (buildNF)
open DrvR (ivB qE atVtx partner)
variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-! ## Chord positions -/
section
variable {M : Model} {N : NF}

/-- **Chord positions with the same key are equal** (distinct heights). -/
theorem chordPos_eq (hN : IsNF M Q N) (hdh : DistinctHeights Q) {x x' : WPos}
    (hx : ChordPos N x) (hx' : ChordPos N x') (hk : M.key Q x = M.key Q x') : x = x' := by
  zucxv
  obtain ⟨i', hi', hxi'⟩ := hx'
  zucxh
  obtain ⟨-, hA', ek', eh', hh', hy'⟩ := chordPos_attach hN hi' hxi'
  zucpq

  have hyy : (Q.vtx (N.chord i).h).2 = (Q.vtx (N.chord i').h).2 := by
    simp_all
  have hhh : (N.chord i).h = (N.chord i').h := by
    by_contra hne; exact hdh _ _ hh hh' hne hyy
  cases x; cases x'
  simp_all

/-- **The two ends of a chord record have distinct keys.** -/
theorem chordPos_ne (hN : IsNF M Q N) (hM : WalkAx M) {i : ℕ} (hi : i < N.nChords) :
    M.key Q (N.chord i).lpos ≠ M.key Q (N.chord i).rpos := by
  zuibt
  obtain ⟨hmem, hA, ek, -, -, -⟩ := chordPos_attach hN hi ztp
  obtain ⟨-, hA', ek', -, -, -⟩ := chordPos_attach hN hi ztbt
  zucpq

  have hP : M.pos Q (N.chord i).lpos = M.pos Q (N.chord i).rpos := by
    zuckw
  have hF := hN.1.2.1 hmem
  obtain ⟨a, b, hab, hcab, -⟩ := hM.ends _ hF
  have ha : a ∈ (N.chord i).toSet M Q := by zvmyh; exact Geometry.left_mem_segment _ _
  have hb : b ∈ (N.chord i).toSet M Q := by zvmyh; exact Geometry.right_mem_segment _ _
  unfold CRec.toSet at ha hb
  rw [hP] at ha hb
  apply hab
  obtain ⟨ha2, ha1, ha1'⟩ := ha
  obtain ⟨hb2, hb1, hb1'⟩ := hb
  grind
end

/-- **`DrvR.atVtx` tests that a chord position is at a walk vertex** (distinct heights). -/
theorem atVtx_iff {N : NF} (hN : IsNF ztd Q N) (hdh : DistinctHeights Q)
    {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) {x : WPos} (hx : ChordPos N x) :
    atVtx li Q.n x = true ↔
      (interiorModel Q).key Q x = ⌊(interiorModel Q).key Q x⌋₊ := by
  zucxv
  zucxh
  have hp : x.edge < Q.n := walk_n Q ▸ hA.1
  zucmb
  zunhp
  unfold atVtx
  rw [decide_eq_true_iff, eh, Nat.add_sub_cancel]
  constructor
  · zuq
    have hpar : ztmrk := by
      have e : (interiorModel Q).param Q x =
          if ((interiorModel Q).wa x.edge).2 = ((interiorModel Q).wb x.edge).2 then 0
          else ((Q.vtx (N.chord i).h).2 - ((interiorModel Q).wa x.edge).2) /
            (((interiorModel Q).wb x.edge).2 - ((interiorModel Q).wa x.edge).2) := by
        unfold Model.param; rw [eh]
      zui
      split_ifs
      · rfl
      · zvmwc; unfold Model.wa; rw [hW, walk_vtx hli hp, sub_self, zero_div]
    simp_all
  · zuq
    have hp0 : ztmrk := by_linarith
    rw [hp0, Chazelle.Chain.sidePt_zero, hW, walk_vtx hli hp] at hy
    zuct
    exact hdh _ _ hh ztjyy hne hy.symm

/-- **`DrvR.partner` returns the other end of an exit chord record** attached at `x`. -/
theorem partner_spec {N : NF} {r : ℕ} {x : WPos}
    (hxc : ∃ i ∈ (N.region r).chords, x = (N.chord i).lpos ∨ x = (N.chord i).rpos) :
    ∃ i ∈ (N.region r).chords,
      (x = (N.chord i).lpos ∧ partner N r x = (N.chord i).rpos) ∨
        (x = (N.chord i).rpos ∧ partner N r x = (N.chord i).lpos) := by
  obtain ⟨i, hi, hx⟩ := hxc
  set p : ℕ → Bool := fun i => decide ztdee with hp
  have hsome : ((N.region r).chords.find? p).isSome := by
    grind
  obtain ⟨i₀, h₀⟩ := Option.isSome_iff_exists.1 hsome
  have hpi := List.find?_some h₀
  have hmi := List.mem_of_find?_eq_some h₀
  simp only [hp, decide_eq_true_eq] at hpi
  refine ⟨i₀, hmi, ?_⟩
  unfold partner
  grind

/-! ## The arcs of a region record -/

/-- **The arcs of region `r` of `buildNF`**: arcs of `reg r`, sorted by start key, complete. -/
theorem regArcs_facts (hQ : Q.Simple) (hL : ChordTriplesOK ztd Q L)
    (hperm : E.Perm ztct)
    (hsort : E.Pairwise ztwxw) (hK : 0 < L.length)
    {reg : ℕ → Set Point}
    (hregs : Restore.NFRegs ztd Q ztwkc reg) {r : ℕ}
    (hr : r < (buildNF ztd Q L E).nRegions) :
    let N := buildNF ztd Q L E
    let as := (N.region r).arcs
    (∀ t, t < as.length → as.getD t 0 < N.arcs.length ∧
      (interiorModel Q).IsArc ztwjs ztcz
        ((interiorModel Q).key Q (N.arc ztctt).s)
        ((interiorModel Q).key Q (N.arc ztctt).e)) ∧
    (∀ t t', t < t' → t' < as.length →
      (interiorModel Q).key Q (N.arc ztctt).s <
        (interiorModel Q).key Q (N.arc ztnri).s) ∧
    (∀ a b, (interiorModel Q).IsArc ztwjs ztcz a b →
      ∃ t, t < as.length ∧ (interiorModel Q).key Q (N.arc ztctt).s = a ∧
        (interiorModel Q).key Q (N.arc ztctt).e = b) := by
  intro N as
  obtain ⟨-, -, ⟨hA1, hA2, hA3, hA4⟩, -⟩ := hregs
  have hN := isNF_build (E := E) hQ hL hperm hsort
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, hseq⟩, -, -⟩ := hN
  have hnr : ztmwo := by
    have : (buildNF ztd Q L E).nRegions = L.length + 1 := by
      zuggb
    omega
  have hsorted : as.Pairwise ztfvn := region_arcs_sorted hK hnr
  have hget : ∀ t (ht : t < as.length), as.getD t 0 = as[t]'ht := fun t ht =>
    List.getD_eq_getElem _ _ ht
  have hmem : ∀ t, t < as.length → as.getD t 0 < N.arcs.length ∧
      (N.arc ztctt).reg = r := by
    zucj
    rw [hget t ht]
    exact (hA4 r hr _).1 ztpzq
  refine ⟨fun t ht => ?_, fun t t' htt ht' => ?_, fun a b hab => ?_⟩
  · grind
  · obtain ⟨hj, hreg⟩ := hmem t by_omega
    obtain ⟨hj', hreg'⟩ := hmem t' ht'
    have hlt : as.getD t 0 < as.getD t' 0 := by
      rw [hget t by_omega, hget t' ht']
      exact List.pairwise_iff_getElem.1 hsorted t t' by_omega ht' htt
    have hle : (interiorModel Q).key Q (N.arc ztctt).s ≤
        (interiorModel Q).key Q (N.arc ztnri).s := by
      have := List.pairwise_iff_getElem.1 hseq ztctt ztnri
        ztlgn
        ztlgn hlt
      simpa [DownDrv.buildNF_seq] using this
    grind
  · obtain ⟨j, hj, hreg, hs, he⟩ := hA3 r hr a b hab
    have hjm : j ∈ as := (hA4 r hr j).2 ⟨hj, hreg⟩
    obtain ⟨t, ht, htj⟩ := List.getElem_of_mem hjm
    grind
end
end DownMath
end Chazelle.Core
namespace Chazelle.Core
namespace DownMath
@[expose] public section
open Set
open DownHost
open DrvR (ivB qE atVtx partner ptI runCnt runItems arcItems walkItems regHost)
variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-! ## Representing lists -/

/-- **The list `L` represents the host keys of `R` from index `i` on.** -/
def RepFrom (li : Bool) (Q : Polygon) (S : Set ztf) (R : Set Point) (L : List SymPt)
    (i : ℕ) : Prop :=
  ∀ j, j < L.length → RepPt li Q S R (zteti % nk ztd S R) ztxkc
theorem repFrom_nil (li : Bool) (i : ℕ) : RepFrom li Q S R [] i := fun j hj => by_simp_all
variable {li : Bool}
theorem repFrom_single {s : SymPt} {i : ℕ}
    (h : RepPt li Q S R (i % nk ztd S R) s) : RepFrom li Q S R [s] i := by
  zun
  simp_all
theorem repFrom_append {L L' : List SymPt} {i : ℕ} (h : RepFrom li Q S R L i)
    (h' : RepFrom li Q S R L' (i + L.length)) : RepFrom li Q S R ztrjv i := by
  zun
  rw [List.length_append] at hj
  rcases Nat.lt_or_ge j L.length with hjL | hjL
  · rw [List.getD_append _ _ _ _ hjL]; exact h j hjL
  · rw [List.getD_append_right _ _ _ _ hjL]
    have := h' (j - L.length) by_omega
    simp_all

/-- The length of the group of host keys of arc `t`: its `d t + 1` keys from the start to the
key before the next group, plus the junction. -/
theorem repFrom_flatMap (G : ℕ → List SymPt) (d J : ℕ → ℕ) (i : ℕ) (k : ℕ)
    (hG : ∀ t, t < k → RepFrom li Q S R (G t) (i + grpOff d J t) ∧ (G t).length = grpLen d J t) :
    RepFrom li Q S R ((List.range k).flatMap G) i ∧
      ((List.range k).flatMap G).length = grpOff d J k := by
  induction k with
  | zero => exact ⟨repFrom_nil li i, by_rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih fun t ht => hG t by_omega
    obtain ⟨h3, h4⟩ := hG k by_omega
    zunxz
    refine ⟨repFrom_append h1 by_simp_all, ?_⟩
    rw [List.length_append, h2, h4, grpOff_succ]
theorem repFrom_rotate {L : List SymPt} {i : ℕ}
    (hL : L.length = nk ztd S R) (h : RepFrom li Q S R L i) (m : ℕ) :
    RepFrom li Q S R (L.rotate m) ztjym := by
  zun
  rw [List.length_rotate] at hj
  have hpos : ztmsl := by_omega
  have hjm := h (zttpw % L.length) ztnnk
  rw [List.getD_eq_getElem _ _ by_simp_all, List.getElem_rotate,
    ← List.getD_eq_getElem _ ztga ztnnk]
  have e : (i + zttpw % L.length) % nk ztd S R =
      (i + m + j) % nk ztd S R := by
    rw [hL, Nat.add_mod_mod]; grind
  simp_all

/-! ## The points of the driver's host in walk order -/

/-- The points of a host item in walk order. -/
def wpts (li : Bool) (n : ℕ) (it : HostItem) : List SymPt :=
  if li then it.pts n else (it.pts n).reverse

/-- **The points of `regHost`**: the walk-order points of the walk items, reversed if `¬ li`. -/
theorem regHost_pts (li : Bool) (n : ℕ) (N : NF) (r : ℕ) :
    (regHost li n N r).pts n =
      if li then (walkItems li n N r).flatMap ztewi
      else ((walkItems li n N r).flatMap ztewi).reverse := by
  unfold regHost Host.pts
  cases li
  · zuma
    rw [List.reverse_flatMap]
    zucr
    funext it
    simp [wpts]
  rfl
theorem wpts_pt (li : Bool) (n : ℕ) (x : SymPt) : wpts li n (.pt x) = [x] := by
  unfold wpts; cases li <;> zunjr

/-! ## Runs -/

/-- `(y + n - 1 - x) mod n` for `y ≡ x + c (mod n)`: the arithmetic of `runCnt`. -/
theorem runCnt_arith {n x c y : ℕ} (hx : x < n) (hc : 1 ≤ c) (hcn : c ≤ n)
    (hy : y = ztojz % n) : (y + n - 1 - x) % n = c - 1 := by
  zugzx

  · rw [Nat.mod_eq_of_lt h, show x + c + n - 1 - x = ztnwe + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt by_omega]
  · have e : ztehq := by
      zul
    rw [e, show x + c - n + n - 1 - x = c - 1 by omega, Nat.mod_eq_of_lt by_omega]

/-- The points of a run of `c` walk vertices from `x + 1` on, in walk order. -/
theorem run_wpts {li : Bool} {n x c : ℕ} (_hn : 0 < n) (hx : x < n) (hc : c < n) (hc0 : 0 < c) :
    let items : List HostItem := if li then [.run (zthf % n) ztnwe]
      else [.run (n - 1 - ztojz % n) ztnwe]
    (items.flatMap ztewi).length = c ∧
      ∀ m, m < c → (items.flatMap ztewi).getD m ztga =
        .vtx (ivB li n (ztzyn % n)) := by
  intro items
  cases li
  · -- clockwise: the run is reversed
    simp only [items, Bool.false_eq_true, ite_false, List.flatMap_singleton, wpts, HostItem.pts]
    refine ztomo
    rw [List.getD_eq_getElem _ _ by_grind, List.getElem_reverse]
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    zucr
    unfold ivB
    zuma
    rw [show c - 1 + 1 - 1 - m = c - 1 - m by omega]
    -- `(n - 1 - (x + c) % n + (c - 1 - m)) % n = n - 1 - (x + (m + 1)) % n`
    by_cases h1 : x + c < n
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (show x + ztbl < n by omega),
        Nat.mod_eq_of_lt by_omega]
      omega
    · have e1 : ztehq := by
        zul
      zukd
      by_cases h2 : x + ztbl < n
      · rw [Nat.mod_eq_of_lt h2, show n - 1 - (x + c - n) + (c - 1 - m) = (n - 2 - x - m) + n
          by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
        omega
      · have e2 : ztzyn % n = x + ztbl - n := by
          zul
        rw [e2, Nat.mod_eq_of_lt by_omega]
        omega
  · simp only [items, ite_true, List.flatMap_singleton, wpts, HostItem.pts]
    refine ztomo
    rw [List.getD_eq_getElem _ _ by_grind]
    zufay
    zucr
    unfold ivB
    grind
end
end DownMath
end Chazelle.Core
namespace Chazelle.Core
namespace DownMath
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost
open BuildNF (buildNF)
open DrvR (ivB qE atVtx partner ptI runCnt runItems arcItems walkItems regHost)

/-- **The setting of a region record of `buildNF`** (the hypotheses of `DrvR.HostR1Spec`). -/
structure RegCtx (Q : Polygon) (L : List zte) (E : List ℕ) (reg : ℕ → Set Point)
    (r : ℕ) : Prop where
  hQ : Q.Simple
  hdh : DistinctHeights Q
  hL : ChordTriplesOK ztd Q L
  hperm : E.Perm ztct
  hsort : E.Pairwise ztwxw
  hK : 0 < L.length
  hregs : Restore.NFRegs ztd Q ztwkc reg
  hr : r < (buildNF ztd Q L E).nRegions

/-- The symbolic point inside `DrvR.ptI`. -/
def ptSym (li : Bool) (n : ℕ) (x : WPos) (isEnd : Bool) : SymPt :=
  .onEdge ztefn ztzs
theorem ptI_eq (li : Bool) (n : ℕ) (x : WPos) (isEnd : Bool) :
    ptI li n x isEnd = .pt (ptSym li n x isEnd) := rfl
variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point} {r : ℕ}

/-- An arc end is preceded by an arc gap. -/
theorem arcGap_prev_of_end {S : Set ztf} {R : Set Point} (hQ : Q.Simple)
    (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
    (hR : R ∈ (interiorModel Q).regions S) {i : ℕ} (hi : i < nk ztd S R) {a : ℝ}
    (harc : (interiorModel Q).IsArc S R a ztwln) :
    ArcGap ztd S R ztbajx := by
  zuok
  zukh
  zudrn
  have hidx := hk_inj hM hFam.2.1 hFam.1 ztcv hi hD.hr
  zuixv
  have e : prevIdx ztwiy i = ztyrb % nk ztd S R := by
    have h1 : i = (ztyrb % nk ztd S R + 1) % nk ztd S R := by
      grind
    zvmwp; exact prevIdx_succ ztcv
  zui
  exact arcData_gap hQ hFam hne hR harc hD by_omega

/-- **The symbolic point of a chord position represents its host key**, when `isEnd` marks
exactly the vertex keys after an arc gap. -/
theorem ptSym_rep {N : NF} {R : Set Point} (hN : IsNF ztd Q N)
    (hdh : DistinctHeights Q) {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) {x : WPos}
    (hx : ChordPos N x) {i : ℕ}
    (hki : hk ztd ztwjs R i = (interiorModel Q).key Q x)
    (hex : hk ztd ztwjs R i ∈
      exitKeys ztd ztwjs R)
    {isEnd : Bool}
    (hend : (interiorModel Q).key Q x = ⌊(interiorModel Q).key Q x⌋₊ →
      (isEnd = true ↔ ArcGap ztd ztwjs R
        (prevIdx (nk ztd ztwjs R) i))) :
    RepPt li Q ztwjs R i (ptSym li Q.n x isEnd) := by
  zucxl
  obtain ⟨-, hA, ek, eh, hh, hy⟩ := chordPos_attach hN hc hxc
  have hfl : ⌊(interiorModel Q).key Q x⌋₊ = x.edge := by zunhp
  right
  refine ⟨hex, x.hgt - 1, by_omega, ?_, ?_⟩
  · rw [hki, ek, hostPt_eq _ hA.2.1 hA.2.2.1, eh, Nat.add_sub_cancel]; simp_all
  · rw [hki]
    by_cases hb : (isEnd && atVtx li Q.n x) = true
    · zuixn
      simp only [Bool.and_eq_true] at hb'
      have hint := (atVtx_iff hN hdh hli ztrbf).1 hb'.2
      left
      refine ⟨hint, (hend hint).1 hb'.1, ?_⟩
      zumua
    · right
      refine ⟨fun ⟨hint, hAp⟩ => hb ?_, ?_⟩
      · zuhos
        exact ⟨(hend hint).2 hAp, (atVtx_iff hN hdh hli ztrbf).2 hint⟩
      · zumua
end
end DownMath
end Chazelle.Core
namespace Chazelle.Core
namespace DownMath
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost
open DrvR (partner)
variable {Q : Polygon} {N : NF} {R : Set Point} {r : ℕ}

/-- Three attachment keys of one chord, two of them distinct, the third distinct from the first:
the third is the second. -/
theorem attach_third {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {x y z : ℝ}
    (hx : x ∈ DownDrv.attachKeys M c) (hy : y ∈ DownDrv.attachKeys M c)
    (hz : z ∈ DownDrv.attachKeys M c) (hxy : x ≠ y) (hzx : z ≠ x) : z = y := by
  obtain ⟨k₁, k₂, hsub⟩ := DownDrv.attachKeys_sub hM hc
  grind
variable (hQ : Q.Simple) (hdh : DistinctHeights Q) (hN : IsNF (interiorModel Q) Q N)
  (hne : (N.F ztd Q).Nonempty)
  (hR : R ∈ (interiorModel Q).regions ztwjs)
  (hRC : ∀ i, i ∈ (N.region r).chords ↔
    i < N.nChords ∧ TouchesIn (interiorModel Q).D ztwtd R)

/-- A chord of `N.F` is a chord record. -/
theorem chord_of_mem {c : Set Point} (hc : c ∈ N.F ztd Q) :
    ∃ i, i < N.nChords ∧ c = (N.chord i).toSet ztd Q := by
  obtain ⟨rc, hrc, rfl⟩ := hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrc
  exact ⟨i, hi, by unfold NF.chord; simp_all⟩
include hQ hdh hN hne hR hRC in
/-- **The end of an arc is an end of an exit chord record of the region.** -/
theorem exit_record {x : WPos} (hx : ChordPos N x) {a : ℝ}
    (harc : (interiorModel Q).IsArc ztwjs R a ztgwc) :
    ∃ i ∈ (N.region r).chords, x = (N.chord i).lpos ∨ x = (N.chord i).rpos := by
  zuok
  obtain ⟨c, ⟨hc, ht⟩, p, t, hA, he⟩ := hM.exists_exit_at_end hN.1.2.1 hN.1.1 hne hR harc
  obtain ⟨i, hi, rfl⟩ := chord_of_mem hc
  refine ⟨i, (hRC i).2 ztoog, ?_⟩
  obtain ⟨-, hAl, ekl, -, -, -⟩ := chordPos_attach hN hi ztp
  obtain ⟨-, hAr, ekr, -, -, -⟩ := chordPos_attach hN hi ztbt
  have hxk : (interiorModel Q).key Q x ∈ DownDrv.attachKeys ztd
      ztwtd := ⟨p, t, hA, he⟩
  have hlk : (interiorModel Q).key Q (N.chord i).lpos ∈ DownDrv.attachKeys ztd
      ztwtd := ⟨_, _, hAl, ekl⟩
  have hrk : (interiorModel Q).key Q (N.chord i).rpos ∈ DownDrv.attachKeys ztd
      ztwtd := ⟨_, _, hAr, ekr⟩
  have hlr := chordPos_ne hN hM hi
  by_cases hxl : (interiorModel Q).key Q x = (interiorModel Q).key Q (N.chord i).lpos
  · exact Or.inl (chordPos_eq hN hdh hx ⟨i, hi, Or.inl rfl⟩ hxl)
  · have := attach_third hM ztvtm hlk hrk hxk hlr hxl
    exact Or.inr (chordPos_eq hN hdh hx ⟨i, hi, Or.inr rfl⟩ this)
include hQ hdh hN hne hR hRC in
/-- **`DrvR.partner` at the end of an arc**: a chord position whose key is the host key after the
end, which is an exit key. -/
theorem partner_key {x : WPos} (hx : ChordPos N x) {m : ℕ}
    (hm : m < nk ztd ztwjs R)
    (hkm : hk ztd ztwjs R m = (interiorModel Q).key Q x)
    {a : ℝ}
    (harc : (interiorModel Q).IsArc ztwjs R a ztgwc) :
    ChordPos N ztczv ∧
      (interiorModel Q).key Q ztczv =
        hk ztd ztwjs R
          ztbals ∧
      hk ztd ztwjs R
          ztbals ∈
        exitKeys ztd ztwjs R := by
  zuok
  have h3 := three_le_nk hQ hN.1 hne hR
  obtain ⟨i₀, hi₀, hcases⟩ := partner_spec (exit_record hQ hdh hN hne hR hRC hx harc)
  obtain ⟨hi₀n, ht₀⟩ := (hRC i₀).1 hi₀
  set c₀ := (N.chord i₀).toSet ztd Q with hc₀
  obtain ⟨hc₀S, hAl, ekl, -, -, -⟩ := chordPos_attach hN hi₀n ztp
  obtain ⟨-, hAr, ekr, -, -, -⟩ := chordPos_attach hN hi₀n ztbt
  -- the chord is attached at `x` and at the partner
  obtain ⟨hAx, hAp, ekx, ekp, hxp⟩ : ∃ (_ : SideAttach (interiorModel Q).W c₀ x.edge
        ((interiorModel Q).param Q x))
      (_ : SideAttach (interiorModel Q).W c₀ (partner N r x).edge
        ((interiorModel Q).param Q ztczv)),
      (interiorModel Q).key Q x = x.edge + (interiorModel Q).param Q x ∧
      (interiorModel Q).key Q ztczv =
        (partner N r x).edge + (interiorModel Q).param Q ztczv ∧
      (interiorModel Q).key Q x ≠ (interiorModel Q).key Q ztczv := by
    rcases hcases with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
    · zvohk; exact ⟨hAl, hAr, ekl, ekr, chordPos_ne hN hM hi₀n⟩
    · zvohk; exact ⟨hAr, hAl, ekr, ekl, (chordPos_ne hN hM hi₀n).symm⟩
  have hpos : ChordPos N ztczv := by
    rcases hcases with ⟨-, hp⟩ | ⟨-, hp⟩
    · exact ⟨i₀, hi₀n, Or.inr hp⟩
    · exact ⟨i₀, hi₀n, Or.inl hp⟩
  -- after the end: the chord continues to the next host key
  have hex : hk ztd ztwjs R m ∈
      exitKeys ztd ztwjs R :=
    ⟨c₀, hc₀S, ht₀, _, _, hAx, by_simp_all⟩
  have hAp' := DownMath.arcGap_prev_of_end hQ hN.1 hne hR hm (by rw [hkm]; omega)
  obtain ⟨-, hnext⟩ := end_chord hQ hN.1 hne hR hm hex hAp'
  obtain ⟨p', t', hA', he'⟩ := hnext c₀ hc₀S ht₀ _ _ hAx by_grind
  have hz : hk ztd ztwjs R
      ztbals =
      (interiorModel Q).key Q ztczv := by
    apply attach_third hM (hN.1.2.1 hc₀S) ⟨_, _, hAx, ekx⟩ ⟨_, _, hAp, ekp⟩ ⟨p', t', hA', he'⟩
      hxp
    rw [← hkm]
    exact (hk_succ_ne hM hN.1.2.1 hN.1.1 by_omega hm).symm
  exact ⟨hpos, hz.symm, ⟨c₀, hc₀S, ht₀, p', t', hA', he'⟩⟩
end
end DownMath
end Chazelle.Core
namespace Chazelle.Core
namespace DownMath
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost
open DrvR (ivB qE atVtx partner ptI runCnt runItems arcItems walkItems regHost)
variable {Q : Polygon} {N : NF} {R : Set Point} {r : ℕ}

/-- `(y + n - x) mod n = c` for `y = (x + c) mod n`. -/
theorem runCnt_arith2 {n x c y : ℕ} (hx : x < n) (hcn : c < n) (hy : y = ztojz % n) :
    (y + n - x) % n = c := by
  zugzx

  · rw [Nat.mod_eq_of_lt h, show x + c + n - x = c + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hcn]
  · have e : ztehq := by
      zul
    rw [e, show x + c - n + n - x = c by omega, Nat.mod_eq_of_lt hcn]

/-- The points of an arc group. -/
def grpPts (li : Bool) (n : ℕ) (N : NF) (r : ℕ) (xs xe xn : WPos) : List SymPt :=
  [ptSym li n xs false] ++ (runItems li n xs xe).flatMap ztewi ++ [ptSym li n xe true] ++
    (if partner N r xe = xn then [] else [ptSym li n ztftt false])
variable (hQ : Q.Simple) (hdh : DistinctHeights Q) (hN : IsNF (interiorModel Q) Q N)
  (hne : (N.F ztd Q).Nonempty)
  (hR : R ∈ (interiorModel Q).regions ztwjs)
  (hRC : ∀ i, i ∈ (N.region r).chords ↔
    i < N.nChords ∧ TouchesIn (interiorModel Q).D ztwtd R)
include hQ hdh hN hne hR hRC in
/-- **The points of one arc group represent its host keys.** -/
theorem group_rep {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) {xs xe xn : WPos}
    (hxs : ChordPos N xs) (hxe : ChordPos N xe) (hxn : ChordPos N xn)
    (harc : (interiorModel Q).IsArc ztwjs R ztmze
      ztmzd)
    {i₁ d₁ J₁ : ℕ}
    (hD : ArcData ztd ztwjs R ztmze
      ztmzd i₁ d₁)
    (_hJ : J₁ = 0 ↔ ArcGap ztd ztwjs R
      (ztjyz % nk ztd ztwjs R))
    (hJ1 : J₁ ≤ 1)
    (hnext : (interiorModel Q).key Q xn = hk ztd ztwjs R
      ((i₁ + d₁ + 1 + J₁) % nk ztd ztwjs R)) :
    RepFrom li Q ztwjs R (grpPts li Q.n N r xs xe xn) i₁ ∧
      (grpPts li Q.n N r xs xe xn).length = d₁ + 1 + J₁ ∧
      ((runItems li Q.n xs xe).flatMap ztcwx).length = d₁ - 1 ∧
      ChordGap ztd ztwjs R
        (zttpu % nk ztd ztwjs R) ∧
      ChordPos N ztftt := by
  zuhm
  zuiny
  zudkv
  zulk
  zuhws
  zuyn
  zuert
  zumdn
  zuixv
  zumdi
  obtain ⟨hinner, hend, hdn⟩ := arc_run hQ hFam hne hR hdh harc hD
  -- floors of the record positions
  have hfl : ∀ {x : WPos}, ChordPos N x → ⌊I.key Q x⌋₊ = x.edge ∧ x.edge < Q.n := by
    zuh
    zucxl
    obtain ⟨-, hA, ek, -, -, -⟩ := chordPos_attach hN hc hxc
    exact ⟨by zunhp, walk_n Q ▸ hA.1⟩
  obtain ⟨hfls, hes⟩ := hfl hxs
  obtain ⟨hfle, hee⟩ := hfl hxe
  -- the start
  have hstart : RepPt li Q S R i₁ (ptSym li Q.n xs false) := by
    apply ptSym_rep hN hdh hli hxs hD.hl
    · obtain ⟨c, ⟨hc, ht⟩, p, t, hA, he⟩ := hM.exists_exit_at_start hFam.2.1 hFam.1 hne hR harc
      exact ⟨c, hc, ht, p, t, hA, by zuoef; exact he⟩
    · zuhge
      constructor
      · simp
      · intro hB
        exfalso
        have hA := arcGap_of_start hQ hFam hne hR hil (by zuoef; omega)
        obtain ⟨c, ⟨hc, ht⟩, p, t, hA', he⟩ := hM.exists_exit_at_start hFam.2.1 hFam.1 hne hR harc
        exact not_arcGap_both hQ hFam hne hR hil ⟨c, hc, ht, p, t, hA', by zuoef; exact he⟩
          hA hB
  -- the end
  set m := zttpu % K with hm
  have hmK : m < K := Nat.mod_lt _ by_omega
  have hkm : hk I S R m = I.key Q xe := hD.hr
  have harc' : I.IsArc S R (I.key Q xs) (hk I S R m) := by_simp_all
  have hAprev := arcGap_prev_of_end hQ hFam hne hR hmK harc'
  have hexe : ztlyl := by
    obtain ⟨c, ⟨hc, ht⟩, p, t, hA, he⟩ := hM.exists_exit_at_end hFam.2.1 hFam.1 hne hR harc
    exact ⟨c, hc, ht, p, t, hA, by_grind⟩
  have hendR : RepPt li Q S R m (ptSym li Q.n xe true) :=
    ptSym_rep hN hdh hli hxe hkm hexe fun _ => ⟨fun _ => hAprev, fun _ => rfl⟩
  -- the run
  have hcnt : runCnt li Q.n xs xe = d₁ - 1 := by
    unfold runCnt
    rcases hend with ⟨hint, hfr⟩ | ⟨hni, hfr⟩
    · have hat : atVtx li Q.n xe = true := (atVtx_iff hN hdh hli hxe).2 hint
      rw [ite_eq_left hat, add_zero, ← hfls, ← hfle]
      exact runCnt_arith by_omega by_omega hdn hfr
    · have hat : atVtx li Q.n xe = false := by
        zumv
        exact hni ((atVtx_iff hN hdh hli hxe).1 by_simp_all)
      rw [ite_eq_right by_simp_all, ← hfls, ← hfle,
        show ⌊I.key Q xe⌋₊ + 1 + Q.n - 1 = ⌊I.key Q xe⌋₊ + Q.n by omega]
      exact runCnt_arith2 by_omega by_omega hfr
  have hrun : RepFrom li Q S R ((runItems li Q.n xs xe).flatMap ztcwx) (i₁ + 1) ∧
      ((runItems li Q.n xs xe).flatMap ztcwx).length = d₁ - 1 := by
    unfold runItems
    zumna
    by_cases hd1 : d₁ - 1 = 0
    · rw [ite_eq_left hd1]
      exact ⟨repFrom_nil li _, by simp [hd1]⟩
    · rw [ite_eq_right hd1]
      obtain ⟨hlen, hget⟩ := run_wpts (li := li) by_omega hes (show d₁ - 1 < Q.n by omega)
        by_omega
      refine ⟨fun j hj => ?_, hlen⟩
      rw [hlen] at hj
      have hgj := hget j hj
      rw [hgj]
      have hidx : (i₁ + 1 + j) % K = ztzwi % K := by ring_nf
      zujiz
      have hv := hinner ztl by_omega by_omega
      left
      zujx
      · obtain ⟨⟨k, hk'⟩, hin⟩ := hD.inner ztl by_omega by_omega
        refine ⟨k, ?_, hk', I.key Q xs, I.key Q xe, harc, ?_⟩
        · have := hostKeys_bounds (hk_mem hM hFam.2.1 hFam.1 (Nat.mod_lt ztzwi
            (show 0 < K by omega)))
          rw [hk'] at this
          exact_mod_cast this.2
        grind
      · rw [hv, Nat.floor_natCast, hfls]
  -- the junction
  have hq₁m : ztjyz % K = ztbl % K := by_grind
  obtain ⟨hpos, hpkey, hpex⟩ := partner_key hQ hdh hN hne hR hRC hxe hmK hkm harc
  obtain ⟨hCm, -⟩ := end_chord hQ hFam hne hR hmK hexe hAprev
  have hjunc : RepFrom li Q S R
      (if partner N r xe = xn then [] else [ptSym li Q.n ztftt false]) ztjyz ∧
      (if partner N r xe = xn then [] else [ptSym li Q.n ztftt false]).length = J₁ := by
    by_cases hJ0 : J₁ = 0
    · have hpx : partner N r xe = xn := by
        apply chordPos_eq hN hdh hpos hxn
        rw [hpkey, hnext, hJ0, add_zero, hq₁m]
      rw [ite_eq_left hpx]
      exact ⟨repFrom_nil _ _, by simp [hJ0]⟩
    · have hJ1' : J₁ = 1 := by_omega
      have hpx : partner N r xe ≠ xn := by
        zuq
        have e1 : I.key Q xn = hk I S R ((ztbl % K + 1) % K) := by
          rw [hnext, hJ1', ← hq₁m, Nat.mod_add_mod]
        have e2 : I.key Q ztftt = hk I S R (ztbl % K) := hpkey
        zuktn
        exact hk_succ_ne hM hFam.2.1 hFam.1 by_omega ztcv (e2.symm.trans e1)
      rw [ite_eq_right hpx]
      refine ⟨repFrom_single ?_, by simp [hJ1']⟩
      rw [hq₁m]
      apply ptSym_rep hN hdh hli hpos hpkey.symm hpex
      zuhge
      constructor
      · simp
      · intro hB
        rw [prevIdx_succ hmK] at hB
        exact absurd hCm fun hC => not_arc_and_chord hM hFam.2.1 hFam.1 by_omega hmK hB hC
  -- assembly
  obtain ⟨hrunR, hrunL⟩ := hrun
  obtain ⟨hjR, hjL⟩ := hjunc
  have hA1 : RepFrom li Q S R [ptSym li Q.n xs false] i₁ :=
    repFrom_single (by rw [Nat.mod_eq_of_lt hil]; omega)
  have hA2 := repFrom_append hA1 by_omega
  have hA3 := repFrom_append hA2 (L' := [ptSym li Q.n xe true]) (repFrom_single (by
    rw [List.length_append, hrunL, List.length_singleton,
      show i₁ + (1 + zttji) = i₁ + d₁ by omega]
    omega))
  have hA4 := repFrom_append hA3 (by
    simp only [List.length_append, hrunL, List.length_singleton]
    rw [show i₁ + (1 + zttji + 1) = i₁ + d₁ + 1 by omega]
    omega)
  refine ⟨hA4, ?_, hrunL, hCm, hpos⟩
  unfold grpPts
  rw [List.length_append, List.length_append, List.length_append, hrunL, hjL]
  zulak
end
end DownMath
end Chazelle.Core
namespace Chazelle.Core
namespace DownMath
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost
open BuildNF (buildNF)
open DrvR (ivB qE atVtx partner ptI runCnt runItems arcItems walkItems regHost)

/-- **Rotating a cyclic concatenation.** -/
theorem flatMap_rot {α : Type*} (A B : ℕ → List α) {k : ℕ} (hk : 0 < k) :
    (List.range k).flatMap ztbamx =
      ((List.range k).flatMap ztfrv).rotate (A 0).length := by
  set f : ℕ → List α := fun t => A (t % k) with hf
  have key : ∀ m, (List.range m).flatMap ztlov ++ f m =
      f 0 ++ (List.range m).flatMap ztyey := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_singleton,
        List.flatMap_singleton, List.append_assoc, List.append_assoc, ← List.append_assoc ztvqf,
        ← List.append_assoc _ (f m ++ B m)]
      rw [← List.append_assoc, ih]
      simp only [List.append_assoc]
  have h1 : (List.range k).flatMap ztlov =
      (List.range k).flatMap ztfrv := by
    apply List.flatMap_congr
    zucj
    zudtp
    simp only [hf, Nat.mod_eq_of_lt ht]
  have h2 : (List.range k).flatMap ztyey =
      (List.range k).flatMap ztbamx := rfl
  have hk0 : f k = A 0 := by_simp_all
  have hf0 : f 0 = A 0 := by_rfl
  have e := key k
  rw [h1, h2, hk0, hf0] at e
  -- the concatenation starts with `A 0`
  zugqg
  obtain ⟨W', hW'⟩ : ∃ W', (List.range (k' + 1)).flatMap (fun t => A t ++ B t) = A 0 ++ W' := by
    rw [List.range_succ_eq_map, List.flatMap_cons]
    simp
  simp_all
variable {Q : Polygon}
/-- **Every region has an arc.** -/
theorem exists_arc {S : Set ztf} {R : Set Point} (hQ : Q.Simple)
    (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
    (hR : R ∈ (interiorModel Q).regions S) : ∃ a b, (interiorModel Q).IsArc S R a b := by
  zuok
  obtain ⟨p, t, hp, ht0, ht1, hnc, hfac⟩ := DownHost.exists_faces_nc hM hFam.2.1 hFam.1 hR
  obtain ⟨X, hX, l, r', harc, hin⟩ := hM.arc_around hFam.2.1 hFam.1 hne hnc
  have hfacX := harc.2.2.2.2.2.2 p t hp ht0 ht1 hin
  have hXR : ztpli := by
    obtain ⟨δ, h1, h2⟩ := (hfacX.and hfac).exists
    zubba
    · zubh
    grind
  grind

/-- The walk-order points of one arc's items. -/
theorem arcItems_wpts (li : Bool) (n : ℕ) (N : NF) (r jp j : ℕ) :
    (arcItems li n N r jp j).flatMap ztewi =
      (if partner N r (N.arc jp).e = (N.arc j).s then []
        else [ptSym li n ztglf false]) ++
      ([ptSym li n (N.arc j).s false] ++
        (runItems li n (N.arc j).s (N.arc j).e).flatMap ztewi ++
        [ptSym li n (N.arc j).e true]) := by
  zumrp
  simp only [List.flatMap_append, ptI_eq, List.flatMap_singleton, wpts_pt, List.append_assoc]
  zucr
  split_ifs <;> simp [wpts_pt]

/-- **The walk-order points of the driver's host** represent the host keys of the region
cyclically, `nk` of them, starting right after a chord gap; and the host is well formed. -/
theorem walk_rep {L : List zte} {E : List ℕ} {reg : ℕ → Set Point}
    {r : ℕ} (X : RegCtx Q L E reg r) {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) :
    ∃ i0 g : ℕ,
      RepFrom li Q ztwkr ztcz
        ((walkItems li Q.n ztwkc r).flatMap ztcwx) i0 ∧
      ((walkItems li Q.n ztwkc r).flatMap ztcwx).length =
        nk ztd ztwkr ztcz ∧
      g < nk ztd ztwkr ztcz ∧
      ChordGap ztd ztwkr ztcz g ∧
      ztbs % nk ztd ztwkr ztcz
        = i0 % nk ztd ztwkr ztcz
      ∧ HostWF Q.n (walkItems li Q.n ztwkc r) := by
  zudbj
  zuhm
  zuiny
  set R := reg r with hRdef
  zudkv
  zuhxd

  have hN : ztuld := isNF_build X.hQ X.hL X.hperm X.hsort
  zuhws
  have hnc : ztpku := nChords_build X.hQ X.hL X.hperm X.hsort
  have hne : S.Nonempty :=
    ⟨_, (chordPos_attach hN ztitl ztp).1⟩
  have hR : ztulz := X.hregs.1.1 r X.hr
  have hRC := (X.hregs.2.2.2 r X.hr).1
  zulk
  zuyn
  zuert
  obtain ⟨hAarc, hAsort, hAcomp⟩ := regArcs_facts (E := E) X.hQ X.hL X.hperm X.hsort X.hK
    X.hregs X.hr
  set as := (N.region r).arcs with has
  set k := as.length with hkdef
  set xs : ℕ → WPos := fun t => (N.arc ztctt).s with hxs
  set xe : ℕ → WPos := fun t => (N.arc ztctt).e with hxe
  have hk1 : ztkzl := by
    obtain ⟨a, b, hab⟩ := exists_arc hQ hFam hne hR
    obtain ⟨t, ht, -⟩ := hAcomp a b hab
    omega
  obtain ⟨i, d, J, hD, hJ0, hJ1, hoff, htot⟩ := arcs_cycle hQ hFam hne hR hdh hk1
    (fun t => I.key Q ztfja) (fun t => I.key Q ztdpw) (fun t ht => (hAarc t ht).2) hAsort
    (fun a b h => by
      tauto)
  have hpos : ∀ t, t < k → ChordPos N ztfja ∧ ChordPos N ztdpw := fun t ht =>
    arc_pos X.hQ X.hL X.hperm X.hsort X.hK (hAarc t ht).1
  have hil : ∀ t, t < k → i t < K := fun t ht => (hD t ht).hil
  -- the next start
  have hnext : ∀ t, t < k → I.key Q ztbanj = hk I S R ((i t + d t + 1 + J t) % K) := by
    zucj
    have hst : i t + d t + 1 + J t = i 0 + grpOff d J ztbx := by
      rw [grpOff_succ, hoff t ht]; unfold grpLen; ring
    by_cases ht1 : t + 1 < k
    · rw [Nat.mod_eq_of_lt ht1, hst, ← hoff ztbx ht1, Nat.mod_eq_of_lt (hil ztbx ht1)]
      exact (hD ztbx ht1).hl.symm
    · have hkt : t + 1 = k := by_omega
      rw [hkt, Nat.mod_self, hst, hkt, htot, Nat.add_mod_right, Nat.mod_eq_of_lt zttnq]
      exact (hD 0 hk1).hl.symm
  -- the groups
  have hgrp : ∀ t, t < k →
      RepFrom li Q S R (grpPts li Q.n N r ztfja ztdpw ztbanj) ztvww ∧
      (grpPts li Q.n N r ztfja ztdpw ztbanj).length = d t + 1 + J t ∧
      ((runItems li Q.n ztfja ztdpw).flatMap ztcwx).length = d t - 1 ∧
      ChordGap I S R (ztjyo % K) ∧ ChordPos N ztzni := fun t ht =>
    group_rep hQ hdh hN hne hR hRC hli (hpos t ht).1 (hpos t ht).2
      (hpos _ (Nat.mod_lt _ hk1)).1 (hAarc t ht).2 (hD t ht) (hJ0 t ht) (hJ1 t ht) (hnext t ht)
  -- the cyclic list from the first arc
  set A : ℕ → List SymPt := fun t => [ptSym li Q.n ztfja false] ++
    (runItems li Q.n ztfja ztdpw).flatMap ztcwx ++ [ptSym li Q.n ztdpw true] with hA
  set B : ℕ → List SymPt := fun t => if partner N r ztdpw = xs ztwsg then []
    else [ptSym li Q.n ztzni false] with hB
  have hGAB : ∀ t, grpPts li Q.n N r ztfja ztdpw ztbanj = A t ++ B t :=
    fun t => rfl
  obtain ⟨hWrep, hWlen⟩ := repFrom_flatMap (li := li) (Q := Q) (S := S) (R := R)
    ztfrv d J (i 0) k fun t ht => by
      obtain ⟨h1, h2, -⟩ := hgrp t ht
      rw [← hGAB, ← hoff t ht]
      exact ztwo
  rw [htot] at hWlen
  -- the driver's list is a rotation
  have hWP : (walkItems li Q.n N r).flatMap ztcwx =
      ((List.range k).flatMap fun t => A t ++ B t).rotate (A 0).length := by
    rw [← flatMap_rot A B hk1]
    unfold walkItems
    rw [List.flatMap_assoc]
    apply List.flatMap_congr
    zucj
    rw [arcItems_wpts]
  have hA0 : (A 0).length = d 0 + 1 := by
    obtain ⟨-, -, h3', -⟩ := hgrp 0 hk1
    simp only [hA, List.length_append, List.length_singleton, h3']
    have := (hD 0 hk1).hd0
    omega
  refine ⟨i 0 + (A 0).length, (i 0 + d 0) % K, ?_, ?_, Nat.mod_lt _ by_omega,
    (hgrp 0 hk1).2.2.2.1, ?_, ?_⟩
  · rw [hWP]; exact repFrom_rotate hWlen hWrep _
  · rw [hWP, List.length_rotate, hWlen]
  · rw [Nat.mod_add_mod, hA0, Nat.add_assoc]
  · -- well formed
    zujbe
    unfold walkItems at hit
    rw [← has, ← hkdef] at hit
    obtain ⟨t, ht, hit⟩ := List.mem_flatMap.1 hit
    zudtp
    have hp0 := hpos t ht
    have hp1 := hpos _ ztypn
    have hpp := (hgrp t ht).2.2.2.2
    have hptI : ∀ (x : WPos) (b : Bool), ChordPos N x →
        (match ptI li Q.n x b with
          | .run a ℓ => a < Q.n ∧ ℓ < Q.n
          | .pt x => x.Lt Q.n) := by
      intro x b hx
      zucxl
      obtain ⟨-, hAx, -, eh, hh, -⟩ := chordPos_attach hN hc hxc
      have hxn : x.edge < Q.n := walk_n Q ▸ hAx.1
      show qE li Q.n _ < Q.n ∧ x.hgt - 1 < Q.n
      refine ⟨qE_lt li ?_, by_omega⟩
      split_ifs
      · zuisr
      omega
    unfold arcItems at hit
    simp only [List.mem_append, List.mem_singleton] at hit
    rcases hit with ((hj | rfl) | hrun) | rfl
    · split_ifs at hj with hpe
      · simp at hj
      · zvojs at hj
        subst hj
        exact hptI _ _ hpp
    · exact hptI _ _ (hpos _ ztypn).1
    · unfold runItems at hrun
      have hxn : (N.arc ztbant).s.edge < Q.n := by
        obtain ⟨c, hc, hxc⟩ := hp1.1
        obtain ⟨-, hAx, -, -, -, -⟩ := chordPos_attach hN hc hxc
        exact walk_n Q ▸ hAx.1
      have hcn : runCnt li Q.n (N.arc ztbant).s
          (N.arc ztbant).e < Q.n := Nat.mod_lt _ by_omega
      split_ifs at hrun with h0 h1
      · simp at hrun
      · zuhka
        exact ⟨Nat.mod_lt _ by_omega, by_omega⟩
      · zuhka
        omega
    · exact hptI _ _ (hpos _ ztypn).2
end
end DownMath
end Chazelle.Core
namespace Chazelle.Core
namespace DownMath
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost Mir
variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- The walk points of a mirrored walk. -/
theorem hostPt_mir (hQ : Q.Simple) {x' : ℝ} (hx0 : 0 ≤ x') (hxn : x' < (interiorModel Q).W.n) :
    hostPt (interiorModel Q.mir).W x' =
      mir (hostPt (interiorModel Q).W (rk (interiorModel Q).W.n ztnv x')) := by
  zuepz
  zubkm

  set p := ⌊x'⌋₊ with hp
  set t := x' - ⌊x'⌋₊ with ht
  have ht0 : 0 ≤ t := by zvnup; linarith [Nat.floor_le hx0]
  have ht1 : t < 1 := by zvnup; linarith [Nat.lt_floor_add_one x']
  have hpn : p < (interiorModel Q).W.n := by
    have : (p : ℝ) < (interiorModel Q).W.n := by_grind
    simp_all
  have hx : x' = p + t := by_simp_all
  have hkey := posMir_key hc hpn ht0 ht1
  obtain ⟨b1, b2, b3⟩ := posMir_bounds (c := Q.n - 1) (p' := p) hn ht0 ht1
  have hs := h.walk.sidePt_mir hpn t
  have e1 : hostPt (interiorModel Q.mir).W x' = sidePt (interiorModel Q.mir).W p t := by
    rfl
  rw [e1, hs, hx, ← hkey, hostPt_eq _ b2 b3]
section
variable (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
  (hR : R ∈ (interiorModel Q).regions S)
include hQ hFam hne hR
omit hQ hFam hne hR in
/-- **Host keys of the mirrored region are the reflected host keys.** -/
theorem hostKeys_mir (hQ : Q.Simple) (_hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
    (_hR : R ∈ (interiorModel Q).regions S) {x' : ℝ} (hx0 : 0 ≤ x')
    (hxn : x' < (interiorModel Q).W.n) :
    x' ∈ hostKeys ztcvu ztbks zttm ↔
      rk (interiorModel Q).W.n ztnv x' ∈ hostKeys ztd S R := by
  zuepz
  zuixo
  have hrk := rk_bounds hc hx0 hxn
  have hT : ∀ c : Set Point, TouchesIn (interiorModel Q.mir).D ztodo zttm ↔
      TouchesIn (interiorModel Q).D c R := by
    intro c; rw [h.D]; exact touchesIn_mir
  have hnat : ∀ k : ℕ, k < (interiorModel Q).W.n →
      ∃ k' : ℕ, k' < (interiorModel Q).W.n ∧ rk (interiorModel Q).W.n ztnv k = k' := by
    zugf
    exact ⟨_, Nat.mod_lt _ h.walk.n_pos, rk_nat hc hk⟩
  constructor
  · rintro (⟨c', hc', ht', p', t', hA', rfl⟩ | ⟨k, hk, rfl, a', b', harc', hin'⟩)
    · -- an exit key
      left
      have hp := h.n_eq ▸ hA'.1
      have hA'' : SideAttach (interiorModel Q.mir).W (mir '' (mir '' c')) p' t' := by
        zumpg
      rw [h.walk.sideAttach_mir hp hA'.2.1 hA'.2.2.1] at hA''
      refine ⟨mir '' c', mem_mirF.1 hc', ?_, _, _, hA'', ?_⟩
      · rw [← hT, image_mir_image_mir]; omega
      · rw [posMir_key hc hp hA'.2.1 hA'.2.2.1]
    · -- a vertex key
      right
      have hk' : k < (interiorModel Q).W.n := by_simp_all
      have ha0 := harc'.1
      have han := harc'.2.1
      have hb0 := harc'.2.2.1
      have hbn := harc'.2.2.2.1
      rw [h.n_eq] at han hbn
      rw [h.isArc hne R ha0 han hb0 hbn] at harc'
      obtain ⟨k', hk'n, hkk⟩ := hnat k hk'
      refine ⟨k', hk'n, hkk, _, _, harc', ?_⟩
      zulrc
      exact (sideInArc_rk hc ha0 han hb0 hbn ztqal by_omega).1 hin'
  · rintro (⟨c, hc', ht, p, t, hA, hx⟩ | ⟨k, hk, hkx, a, b, harc, hin⟩)
    · -- an exit key
      left
      zukel
      have hA'' : SideAttach (interiorModel Q).W (mir '' ztodo) p t := by
        zumpg
      rw [h.walk.symm.sideAttach_mir hp hA.2.1 hA.2.2.1] at hA''
      refine ⟨mir '' c, image_mem_mirF.2 hc', by_simp_all, _, _, hA'', ?_⟩
      rw [posMir_key h.walk.symm.c_lt hp hA.2.1 hA.2.2.1, h.n_eq, ← hx, rk_rk hc hx0 hxn]
    · -- a vertex key
      right
      obtain ⟨k', hk'n, hkk⟩ := hnat k hk
      have hx' : x' = k' := by rw [← rk_rk hc hx0 hxn, hkx, hkk]
      zuhxy

      zumdb
      have hbn := harc.2.2.2.1
      obtain ⟨ra0, ran⟩ := rk_bounds hc ha0 han
      obtain ⟨rb0, rbn⟩ := rk_bounds hc hb0 hbn
      refine ⟨k', h.n_eq ▸ hk'n, hx', rk (interiorModel Q).W.n ztnv b,
        rk (interiorModel Q).W.n ztnv a, ?_, ?_⟩
      · rw [h.isArc hne R rb0 rbn ra0 ran, rk_rk hc hb0 hbn, rk_rk hc ha0 han]
        omega
      · zulrc
        exact (sideInArc_rk hc ha0 han hb0 hbn ztqal by_simp_all).1 hin

/-- **The sorted host keys of the mirrored region**: the reflected host keys of `R` in reversed
order, rotated (`a` the number of host keys `≤ c`). -/
theorem hk_mir : ∃ a, nk ztcvu ztbks zttm = nk ztd S R ∧
    a ≤ nk ztd S R ∧
    ∀ j, j < nk ztd S R →
      hk ztcvu ztbks zttm j =
        rk (interiorModel Q).W.n ztnv (hk ztd S R
          ((a + nk ztd S R - 1 - j) % nk ztd S R)) := by
  classical
  zuhm
  set I' := interiorModel Q.mir with hI'
  zudkv
  set n := I.W.n with hn
  set c := Q.n - 1 with hcdef
  zuepz
  have hc : c < n := h.walk.c_lt
  zulk
  zubl

  zuyn
  have hb : ∀ i, i < K → 0 ≤ hk I S R i ∧ hk I S R i < n := fun i hi =>
    hostKeys_bounds ztzl
  -- the number of host keys `≤ c`
  have hex : ∃ i, K ≤ i ∨ (c : ℝ) < hk I S R i := ⟨K, Or.inl le_rfl⟩
  set a := Nat.find hex with ha
  have haK : a ≤ K := Nat.find_min' hex (Or.inl le_rfl)
  have hlow : ∀ i, i < a → hk I S R i ≤ c := by
    zug
    have := Nat.find_min hex hi
    grind
  have hhigh : ∀ i, a ≤ i → i < K → (c : ℝ) < hk I S R i := by
    intro i hai hi
    rcases Nat.find_spec hex with h1 | h1
    · omega
    · rcases hai.lt_or_eq with h2 | h2
      · exact lt_trans h1 (hk_strictMono hM hF hfin h2 hi)
      grind
  -- the index map
  set σ : ℕ → ℕ := fun j => zteom % K with hσ
  have hσlo : ∀ j, j < a → σ j = a - 1 - j := by
    zun
    zulsd
    rw [show a + K - 1 - j = ztqdl + K by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt by_omega]
  have hσhi : ∀ j, a ≤ j → j < K → σ j = a + K - 1 - j := by
    intro j hj hjK
    zulsd
    zuey
  have hσlt : ∀ j, j < K → σ j < K := fun j _ => Nat.mod_lt _ by_omega
  have hσσ : ∀ i, i < K → σ (σ i) = i := by
    zug
    by_cases hia : i < a
    · rw [hσlo i hia, hσlo _ by_omega]; omega
    · rw [hσhi i by_omega hi, hσhi _ by_omega by_omega]; omega
  -- the reflected keys
  have hrklo : ∀ i, i < a → rk n c ztjxy = c - hk I S R i := by
    intro i hi; unfold rk; grind
  have hrkhi : ∀ i, a ≤ i → i < K → rk n c ztjxy = c - hk I S R i + n := by
    intro i hai hi; unfold rk; grind
  set L' : List ℝ := (List.range K).map fun j => rk n c ztmle with hL'
  have hL'len : L'.length = K := by zuows
  have hL'get : ∀ j, j < K → L'.getD j 0 = rk n c ztmle := by
    zun
    zujgp
    zuows
  -- strictly increasing
  have hcn : ztfzx := by exact_mod_cast hc
  have hmono : ∀ j j', j < j' → j' < K → L'.getD j 0 < L'.getD j' 0 := by
    intro j j' hjj hj'
    rw [hL'get j by_omega, hL'get j' hj']
    by_cases h1 : j' < a
    · rw [hσlo j by_omega, hσlo j' h1, hrklo _ by_omega, hrklo _ by_omega]
      have := hk_strictMono (U := R) hM hF hfin (show a - 1 - j' < a - 1 - j by omega) by_omega
      linarith
    · by_cases h2 : j < a
      · rw [hσlo j h2, hσhi j' by_omega hj', hrklo _ by_omega,
          hrkhi _ by_omega by_omega]
        have := (hb ztqdl by_omega).1
        have := (hb (a + K - 1 - j') by_omega).2
        linarith
      · rw [hσhi j by_omega by_omega, hσhi j' by_omega hj', hrkhi _ by_omega by_omega,
          hrkhi _ by_omega by_omega]
        have := hk_strictMono (U := R) hM hF hfin (show a + K - 1 - j' < a + K - 1 - j by omega)
          by_omega
        linarith
  -- the same elements
  have hmem : ∀ x, x ∈ L' ↔ x ∈ hostKeys I' ztbks zttm := by
    zugop
    constructor
    · zuetb
      zufyo
      zukpq
      have hb' := hb _ zttox
      obtain ⟨r0, rn⟩ := rk_bounds hc hb'.1 hb'.2
      rw [hostKeys_mir hQ hFam hne hR r0 rn, rk_rk hc hb'.1 hb'.2]
      exact hk_mem hM hF hfin zttox
    · zuetb
      zuliq
      have hxb := hostKeys_bounds hx
      rw [h.n_eq] at hxb
      have := (hostKeys_mir hQ hFam hne hR hxb.1 hxb.2).1 hx
      obtain ⟨i, hi, hie⟩ := exists_hk hM hF hfin this
      refine List.mem_map.2 ⟨σ i, List.mem_range.2 (hσlt i hi), ?_⟩
      rw [hσσ i hi, hie, rk_rk hc hxb.1 hxb.2]
  -- `L'` is the sorted host key list
  have hfin' : (hostKeys I' ztbks zttm).Finite := by
    zuliq
    have hFam' := (h.chordFamily Q S).2 hFam
    exact hostKeys_finite hM' hFam'.2.1 hFam'.1
  have hsortL' : L'.Pairwise ztfvn := by
    zumlo
    zukjo
    have := hmono j j' hjj by_omega
    rwa [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at this
  have heq : hostKeyList I' ztbks zttm = L' := by
    rw [hostKeyList_eq hfin']
    apply List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h1 h2)
      (Finset.pairwise_sort _ _) (hsortL'.imp le_of_lt)
    rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) hsortL'.nodup]
    zugop
    rw [Finset.mem_sort, Set.Finite.mem_toFinset, hmem]
  refine ⟨a, ?_, haK, fun j hj => ?_⟩
  · unfold nk; rw [heq, hL'len]
  · have e : hk I' _ _ j = (hostKeyList I' ztbks zttm).getD j 0 := rfl
    rw [e, heq, hL'get j hj]
omit hFam hne hR in
/-- **Chord gaps correspond**: the gap of the mirrored region between the reflected keys of
`hk (g + 1)` and `hk g` is a chord gap. -/
theorem chordGap_mir {g : ℕ} (hC : ChordGap ztd S R g) {j : ℕ}
    (h1 : hk ztcvu ztbks zttm j =
      rk (interiorModel Q).W.n ztnv (hk ztd S R (ztbs % nk ztd S R)))
    (h2 : hk ztcvu ztbks zttm
        (ztl % nk ztcvu ztbks zttm) =
      rk (interiorModel Q).W.n ztnv (hk ztd S R g)) :
    ChordGap ztcvu ztbks zttm j := by
  zuepz
  zuixo
  have hn := h.walk.n_pos
  obtain ⟨c0, hc0, p, p', t, t', hA, hA', e1, e2, hne'⟩ := hC
  -- the mirrored attachment of a position
  have hmir : ∀ (q : ℕ) (s : ℝ), SideAttach (interiorModel Q).W c0 q s →
      SideAttach (interiorModel Q.mir).W (mir '' c0) (posMir (interiorModel Q).W.n ztnv q s).1
        (posMir (interiorModel Q).W.n ztnv q s).2 ∧
      ((posMir (interiorModel Q).W.n ztnv q s).1 : ℝ) +
        (posMir (interiorModel Q).W.n ztnv q s).2 = rk (interiorModel Q).W.n ztnv ztej ∧
      sidePt (interiorModel Q.mir).W (posMir (interiorModel Q).W.n ztnv q s).1
        (posMir (interiorModel Q).W.n ztnv q s).2 = mir (sidePt (interiorModel Q).W q s) := by
    intro q s hAq
    obtain ⟨b1, b2, b3⟩ := posMir_bounds (c := Q.n - 1) (p' := q) hn hAq.2.1 hAq.2.2.1
    have hpp := posMir_posMir hc hAq.1 hAq.2.2.1
    refine ⟨?_, posMir_key hc hAq.1 hAq.2.1 hAq.2.2.1, ?_⟩
    · rw [h.walk.sideAttach_mir b1 b2 b3, hpp]; omega
    · rw [h.walk.sidePt_mir b1, hpp]
  obtain ⟨hB', hk', hs'⟩ := hmir p' t' hA'
  obtain ⟨hB, hk0, hs⟩ := hmir p t hA
  refine ⟨mir '' c0, image_mem_mirF.2 hc0, _, _, _, _, hB', hB, ?_, ?_, ?_⟩
  · simp_all
  · simp_all
  · rw [hs', hs]; exact fun e => hne' (mir_injective e).symm
end
end
end DownMath
end Chazelle.Core
namespace Chazelle.Core
namespace DownMath
@[expose] public section
open Set
open DownHost Mir
variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- `x mod K` for `x < 3 K`. -/
theorem mod3_cases {x K : ℕ} (hK : 0 < K) (hx : x < 3 * K) :
    x % K < K ∧ (x % K = x ∨ x % K + K = x ∨ x % K + 2 * K = x) := by
  refine ⟨Nat.mod_lt _ hK, ?_⟩
  by_cases h1 : x < K
  · exact Or.inl (Nat.mod_eq_of_lt h1)
  · by_cases h2 : x < 2 * K
    · zuhl
      zuzu
    · zulw
      rw [Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_sub_mod by_omega,
        Nat.mod_eq_of_lt by_omega]; omega
theorem idx_I1 {K a i k : ℕ} (hK : 0 < K) (ha : a ≤ K) (hi : i < K) (hk : k < K) :
    (a + K - 1 - (ztdlk % K + k) % K) % K = ztzwe % K := by
  have e1 := mod3_cases hK ztecs
  generalize ztdlk % K = s at e1 ⊢
  have e2 := mod3_cases hK (show s + k < 3 * K by omega)
  generalize ztnj % K = u at e2 ⊢
  zujxj
  have e4 := mod3_cases hK (show i + ztcgr < 3 * K by omega)
  generalize (a + K - 1 - u) % K = v at e3 ⊢
  generalize ztzwe % K = w at e4 ⊢
  omega
variable {K a i g : ℕ}
theorem idx_I2 (hK : 0 < K) (ha : a ≤ K) (hi : i < K) (hg : g < K)
    (hgi : ztbs % K = i) :
    (a + K - 1 - ztysr % K) % K = ztbs % K := by
  zujxb
  rw [hgi] at e0 ⊢
  zubiz

  zujxj
  grind
theorem idx_I3 (hK : 0 < K) (ha : a ≤ K) (hi : i < K) (hg : g < K)
    (hgi : ztbs % K = i) :
    (a + K - 1 - (ztysr % K + 1) % K) % K = g := by
  zujxb
  rw [hgi] at e0
  zubiz

  have e3 := mod3_cases hK (show u + 1 < 3 * K by omega)
  generalize ztcol % K = u' at e3 ⊢
  have e4 := mod3_cases hK (show a + K - 1 - u' < 3 * K by omega)
  generalize (a + K - 1 - u') % K = v at e4 ⊢
  omega

/-- **`ExtractOK` depends on the chain only through its model.** -/
theorem extractOK_of_model {C C' : Chain} (h : chainModel C = chainModel C')
    (hE : DownDrv.ExtractOK Q S R C') : DownDrv.ExtractOK Q S R C := by
  obtain ⟨h1, h2, h3, h4⟩ := hE
  zudfi
  · grind
  · simp_all
  · simp_all
  simp_all

/-- **Counterclockwise extraction** for a chain from index `0` of the host polygon rotated by `i0`,
the host key before `i0` being a chord gap. -/
theorem extractOK_rot (X : Extract.Ctx Q S R) {g i0 : ℕ} (hg : g < nk ztd S R)
    (hgc : ChordGap ztd S R g)
    (hgi : ztbs % nk ztd S R = i0 % nk ztd S R) {C : Chain}
    (hP : C.P = (hostPoly Q S R).rotate i0) (hs : C.s = 0) (hm : C.m + 1 = C.P.n) :
    DownDrv.ExtractOK Q S R C := by
  zueqg

  have hPn : C.P.n = K := by rw [hP, Existence.n_rotate, hostPoly_n]
  refine extractOK_of_model (C' := hostChain Q S R g h3) ?_ (DownDrv.extractOK_host X hg hgc)
  zulof
  · rw [hostChain_m]; omega
  · show C.P.vtx ztbaay = (hostPoly Q S R).vtx ((ztbs % K + k) % (hostPoly Q S R).n)
    rw [hs, zero_add, hPn, hostPoly_n, hP, Existence.vtx_rotate _ _ (by zuown; exact Nat.mod_lt _ by_omega),
      hostPoly_n, hgi, Nat.add_mod_mod, Nat.mod_add_mod]
  · rw [hP, coordBound_rotate]
    rfl

/-- **Clockwise extraction** for a chain from index `0` of the reversed rotated host polygon
(`C.P.vtx k = hostPoly.vtx (i0 + (K - 1 - k))`), through the mirror. -/
theorem extractOK_rev (X : Extract.Ctx Q S R) {g i0 : ℕ} (hg : g < nk ztd S R)
    (hgc : ChordGap ztd S R g)
    (hgi : ztbs % nk ztd S R = i0 % nk ztd S R) {C : Chain}
    (hPn : C.P.n = nk ztd S R)
    (hPv : ∀ k, k < nk ztd S R → C.P.vtx k =
      (hostPoly Q S R).vtx ((i0 + (nk ztd S R - 1 - k)) % nk ztd S R))
    (hPs : C.P.Simple) (hs : C.s = 0) (hm : C.m + 1 = C.P.n) :
    DownDrv.ExtractOK Q S R C := by
  zueqg

  have hK0 : ztmsk := by_omega
  obtain ⟨a, hnk'0, haK0, hk'0⟩ := hk_mir X.hQ X.hFam X.hne X.hR
  have haK : a ≤ K := haK0
  have hk' : ∀ j, j < K → hk ztcvu ztbks zttm j =
      rk (interiorModel Q).W.n ztnv (hk ztd S R ztzzl) := hk'0
  set K' := nk ztcvu ztbks zttm with hK'
  have hnk' : K' = K := hnk'0
  set i₀ := i0 % K with hi₀
  have hi₀K : i₀ < K := Nat.mod_lt _ hK0
  set s' := (a + K - i₀) % K with hs'
  set g' := (s' + K - 1) % K with hg'
  have hs'K : s' < K := Nat.mod_lt _ hK0
  have hg'K : g' < K := Nat.mod_lt _ hK0
  have X' := DownDrv.ctx_mir X
  have h := modelMir_interior X.hQ
  zuixo
  zuixi
  -- the mirrored host polygon at a reflected index
  have hvtx' : ∀ j, j < K → (hostPoly Q.mir ztbks zttm).vtx j =
      mir ((hostPoly Q S R).vtx ztzzl) := by
    zun
    have hσ : zteom % K < K := Nat.mod_lt _ hK0
    have hb := hostKeys_bounds (hk_mem (walkAx_interiorModel X.hQ) X.hFam.2.1 X.hFam.1 hσ)
    obtain ⟨r0, rn⟩ := rk_bounds hc hb.1 hb.2
    rw [hostPoly_vtx by_omega, hk' j hj, hostPt_mir X.hQ r0 rn,
      rk_rk hc hb.1 hb.2, hostPoly_vtx hσ]
  -- the mirrored chain is a rotation of the mirrored host polygon
  have hPm : C.mir.P = (hostPoly Q.mir ztbks zttm).rotate s' := by
    apply poly_eq_of_vtx
    · rw [chainMir_P, mir_n, Existence.n_rotate, hostPoly_n, hPn, ← hK', hnk']
    · zugf
      rw [chainMir_P, mir_n, hPn] at hk
      have e1 : (i0 + ztcgr) % K = ztzwh % K := by_grind
      have e2 : (a + K - 1 - (s' + k) % K) % K = ztzwh % K := by
        rw [hs']; exact idx_I1 hK0 haK hi₀K hk
      rw [chainMir_P, mir_vtx, hPv k hk,
        Existence.vtx_rotate _ _ (by zunvk; exact hk),
        hostPoly_n, ← hK', hnk', hvtx' _ zttay, e2, e1]
  -- the chord gap of the mirrored region
  have hgc' : ChordGap ztcvu ztbks zttm g' := by
    have hgi' : ztbs % K = i₀ := hgi
    apply chordGap_mir X.hQ hgc
    · have e : (a + K - 1 - g') % K = ztbs % K := by
        zuojr; exact idx_I2 hK0 haK hi₀K hg hgi'
      grind
    · have e : (a + K - 1 - ztjww % K) % K = g := by
        zuojr; exact idx_I3 hK0 haK hi₀K hg hgi'
      show hk ztcvu ztbks zttm (ztjww % K') = _
      rw [hnk', hk' _ zttay, e]
  have hg'K' : g' < nk ztcvu ztbks zttm := by
    omega
  -- extraction for the mirrored chain
  have hE' := DownDrv.extractOK_host X' hg'K' hgc'
  refine DownDrv.extractOK_of_mir X.hQ hPs (extractOK_of_model ?_ hE')
  zulof
  · rw [chainMir_m, hostChain_m, ← hK', hnk']; omega
  · show C.mir.P.vtx ((C.mir.s + k) % C.mir.P.n) =
      (hostPoly Q.mir ztbks zttm).vtx
        ((ztjww % K' + k) % (hostPoly Q.mir ztbks zttm).n)
    have hsm : C.mir.s = 0 := hs
    have hg1 : ztjww % K = s' := by
      rw [hg', Nat.mod_add_mod, show s' + K - 1 + 1 = s' + K by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hs'K]
    rw [hsm, zero_add, hPm, Existence.n_rotate, hostPoly_n, ← hK', hnk',
      Existence.vtx_rotate _ _ (by zunvk; exact Nat.mod_lt _ hK0), hostPoly_n,
      ← hK', hnk', hg1, Nat.add_mod_mod]
  · rw [hPm, coordBound_rotate]
    rfl
