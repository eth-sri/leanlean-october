module

public import Chazelle.Core.FuseAsmPtStage
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 16000000

/-!
# WP-F fusion assembly, part 19: the cap query

* `capS`: `capPrim` on the whole chain at the shared vertex (`k = m₁`, read from the descriptor
  of `C₁`); its four answers are saved in `70140 … 70143` (`capS_exec`).
* `capB D K`: the point query at the walk position `(6 + tpos Cᵢ k, code)` of the chain of the
  descriptor in `D` (`k` in register `K`, the code in `70142`, the direction in `70143`)
  (`capB_exec`).
* `capQ₀`, `capQ₁`: the cap query of side `0` (if the shared vertex is an extremum whose nearer
  arm is `w`) and of side `1` (nearer arm `u`) (`capQ₀_exec`, `capQ₁_exec`).
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK SweepPrim WalkEmbed MergeAsm

@[expose] public section

theorem capOrigin_snd (J : Merge.Junction) (hgen : SharedGeneric J) :
    (capOrigin J).2 = (capNear J).2 := by
  obtain ⟨g1, g2, -⟩ := hgen
  have hf : (capFar J).2 - (sharedV J).2 ≠ 0 := by
    unfold capFar; split_ifs
    · exact sub_ne_zero.2 g2
    · exact sub_ne_zero.2 g1
  unfold capOrigin
  rw [Geometry.lerp_snd]
  field_simp
  ring

/-- The point query at a walk position of the chain of the descriptor in `D`. -/
def capB (D K : ℕ) : Stmt :=
  .seq (block [.copyN 50200 D, .copyN 50110 K]) (.seq tposS
    (.seq (block [.copyN 50202 70142, .copyN 50203 70143, .subN 70124 70142 70105]) ptQ))

/-- The cost bound of `capB`. -/
def capBCost : ℕ := 35100

theorem capB_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) {D K : ℕ} (_hD : 70000 ≤ D ∧ D < 70100)
    (hK : 70000 ≤ K ∧ K < 70200)
    (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg D)) (J : Merge.Junction) (i : ℕ)
    {H : Host} (hC : ChainDescAt c.nmem (c.nreg D) (Qof P) H (sideChain J i))
    (hP : J.P.Simple) {kk code ρ : ℕ} (hk : c.nreg K = kk) (hkk : kk ≤ (sideChain J i).m)
    (h42 : c.nreg 70142 = code) (h1c : 1 ≤ code) (hcn : code ≤ P.n) (h43 : c.nreg 70143 = ρ)
    {z : Point}
    (hgeo : (chainModel (sideChain J i)).pos (Qof P) ⟨6 + tpos (sideChain J i) kk, code⟩ = z ∧
      0 ≤ (chainModel (sideChain J i)).param (Qof P) ⟨6 + tpos (sideChain J i) kk, code⟩ ∧
      (chainModel (sideChain J i)).param (Qof P) ⟨6 + tpos (sideChain J i) kk, code⟩ < 1 ∧
      z ∈ (sideChain J i).set)
    (hhv : ((Qof P).vtx (code - 1)).2 = z.2)
    (h05 : c.nreg 70105 = 1) (h08 : c.nreg 70108 = 0)
    {LB : ℕ} {pre : List (ℕ × ℕ × ℕ)}
    (hA : c.nreg ALLOC = LB + 3 * pre.length) (h28 : c.nreg 70128 = pre.length)
    (hL : ChordListAt c.nmem LB pre) (hroom : c.nreg ALLOC + capBCost ≤ W)
    (hcW : pre.length + 2 ≤ W) :
    ∃ c' k l, Exec P W (capB D K) c c' k ∧ k ≤ capBCost ∧ 3 * l.length ≤ k ∧ l.length ≤ 1 ∧
      c'.nreg ALLOC = LB + 3 * (pre ++ l).length ∧
      c'.nreg 70128 = (pre ++ l).length ∧
      ChordListAt c'.nmem LB (pre ++ l) ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, Bpt r = false → c'.nreg r = c.nreg r) ∧ (∀ r, BR r = false → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      PtAns J (Qof P) i z (dirOf ρ) l := by
  set C := sideChain J i with hCdef
  obtain ⟨hB5, hwf'⟩ := hwf
  have hm := chain_m_le ⟨hB5, hwf'⟩ hC
  have hn : (Qof P).n = P.n := shear_n _ _
  unfold hostWords at hHW
  have hmW : 2 * C.m + 7 ≤ W := by omega
  obtain ⟨X, hX⟩ : ∃ X, c.nreg D = X := ⟨_, rfl⟩
  rw [hX] at hC hB5 hwf'
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50200 D, .copyN 50110 K])
      c c₁ k₁ ∧ k₁ = 2 ∧
      (c₁.nreg 50200 = X ∧ c₁.nreg 50110 = kk ∧
        (∀ r, r ≠ 50200 → r ≠ 50110 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    exec_block
    refine ⟨rfl, ?_, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other,
      hX, hk]
  obtain ⟨q00, q10, qr₁, qm₁, qrr₁, qrm₁, qo₁⟩ := q
  have w₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, q21, F₂⟩ := tposS_exec (P := P) c₁ w₁ (by rwx [q00, qm₁])
    q10 hkk (by rwo [q00]) hmW
  have w₂ := e₂.wb_right
  have r42 : c₂.nreg 70142 = code := by
    rw [F₂.1 _ (by decide), qr₁ _ (by decide) (by decide), h42]
  have r43 : c₂.nreg 70143 = ρ := by
    rw [F₂.1 _ (by decide), qr₁ _ (by decide) (by decide), h43]
  have r05 : c₂.nreg 70105 = 1 := by
    rw [F₂.1 _ (by decide), qr₁ _ (by decide) (by decide), h05]
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 50202 70142,
      .copyN 50203 70143, .subN 70124 70142 70105]) c₂ c₃ k₃ ∧ k₃ = 3 ∧
      (c₃.nreg 50202 = code ∧ c₃.nreg 50203 = ρ ∧ c₃.nreg 70124 = code - 1 ∧
        (∀ r, r ≠ 50202 → r ≠ 50203 → r ≠ 70124 → c₃.nreg r = c₂.nreg r) ∧
        c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output) := by
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 a3 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other,
      r42, r43, r05]
  obtain ⟨q32, q33, q24, qr₃, qm₃, qrr₃, qrm₃, qo₃⟩ := q
  have w₃ := e₃.wb_right
  have m₃ : c₃.nmem = c.nmem := by rw [qm₃, F₂.2.2.1, qm₁]
  have k₃r : ∀ r, Bpt r = false → c₃.nreg r = c.nreg r := fun r hr => by
    have hr' := hr
    simp only [Bpt, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
      at hr'
    rw [qr₃ r (by omega) (by omega) (by omega), F₂.1 r (btp_of hr),
      qr₁ r (by omega) (by omega)]
  have k₃rr : ∀ r, BR r = false → c₃.rreg r = c.rreg r := fun r hr => by
    rw [qrr₃, F₂.2.1 r (br_tp hr), qrr₁]
  have a₃ : c₃.nreg ALLOC = c.nreg ALLOC := by
    rw [qr₃ _ (by decide) (by decide) (by decide), F₂.1 _ (by decide),
      qr₁ _ (by decide) (by decide)]
  have r300 : c₃.nreg 50200 = X := by
    rw [qr₃ _ (by decide) (by decide) (by decide), F₂.1 _ (by decide), q00]
  have r301 : c₃.nreg 50201 = 6 + tpos C kk := by
    rw [qr₃ _ (by decide) (by decide) (by decide), q21]
  have r328 : c₃.nreg 70128 = pre.length := by
    rw [qr₃ _ (by decide) (by decide) (by decide), F₂.1 _ (by decide),
      qr₁ _ (by decide) (by decide), h28]
  obtain ⟨hpos, hp0, hp1, hzs⟩ := hgeo
  have hPC : C.P.Simple := by rwx [hCdef, sideChain_P]
  obtain ⟨c₄, k₄, l, e₄, hk₄, hk₄', hl, a₄, n₄, L₄, m₄, r₄, rr₄, rm₄, o₄, res⟩ :=
    ptQ_exec (P := P) c₃ w₃ hG (by ufo hostWords)
      (by rw [r300, a₃, m₃]; exact ⟨hB5, hwf'⟩) (by rwx [r300, m₃])
      ⟨⟨by rw [r301]; exact vpos_edge C kk, ⟨by rwx [r301, q32],
        by rwx [r301, q32], by rw [q32]; show code ≤ P.n; exact hcn⟩,
        by rw [r301, q32, hpos]; exact abs_snd_lt_radius C hzs⟩, hPC, hmW⟩
      (by rw [k₃r _ (by decide), h05]) (by rw [k₃r _ (by decide), h08])
      (by rw [a₃, hA]) r328 (by rwx [m₃])
      (by ruo [a₃] capBCost at hroom) (by rwo [q24]) (by omega)
  rw [r301, q32, q33, q24] at res
  have ex : Exec P W (capB D K) c c₄ (k₁ + (k₂ + (k₃ + k₄))) :=
    .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have hvn : code - 1 < (Qof P).n := by rwo [hn]
  have hcode : code = code - 1 + 1 := by omega
  refine ⟨c₄, _, l, ex, by ufo capBCost, by omega, hl, a₄, n₄, L₄,
    fun a ha => ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [m₄ a (by rwx [a₃]), m₃]
  · have hr' := hr
    simp only [Bpt, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
      at hr'
    rw [r₄ r (bprim_of hr) (by omega) (by omega) (by omega), k₃r r hr]
  · rw [rr₄ r (br_prim hr), k₃rr r hr]
  · rw [rm₄, qrm₃, F₂.2.2.2.1, qrm₁]
  · rw [o₄, qo₃, F₂.2.2.2.2, qo₁]
  · exact ptAns_of_res J P i hP res hpos hzs hhv hvn

/-! ## The cap data -/

/-- `capPrim` on the whole chain at the shared vertex, answers saved in `70140 … 70143`. -/
def capS : Stmt :=
  .seq (block [.copyN 50200 70002, .constN 70131 2, .addN 70132 70000 70131, .loadN 70126 70132,
      .copyN 50201 70126])
    (.seq capPrim (block [.copyN 70140 50210, .copyN 70141 50211, .copyN 70142 50212,
      .copyN 70143 50213]))

/-- The registers written by `capS`. -/
def Bcs (r : ℕ) : Bool := Bprim r || r == 50200 || r == 50201 || r == 70126 || r == 70131 ||
  r == 70132 || decide (70140 ≤ r ∧ r < 70144)

theorem bprim_of_bcs {r : ℕ} (h : Bcs r = false) : Bprim r = false := by
  simp only [Bcs, Bool.or_eq_false_iff] at h; exact h.1.1.1.1.1.1

/-- The cap data in the registers. -/
structure CapRegs (P : Polygon) (J : Merge.Junction) (c : Config) : Prop where
  m1 : c.nreg 70126 = J.m₁
  ext : BitIs c 70140 (SharedExtremum J)
  near : SharedExtremum J → BitIs c 70141 (NearU J)
  code1 : 1 ≤ c.nreg 70142
  coden : c.nreg 70142 ≤ P.n
  ht : SharedExtremum J → ((Qof P).vtx (c.nreg 70142 - 1)).2 = (capNear J).2
  dir : SharedExtremum J → BitIs c 70143 (¬ (capNear J).1 < (capOrigin J).1)

theorem CapRegs.keep {P : Polygon} {J : Merge.Junction} {c c' : Config} (h : CapRegs P J c)
    (hr : ∀ r, (r = 70126 ∨ (70140 ≤ r ∧ r < 70144)) → c'.nreg r = c.nreg r) :
    CapRegs P J c' :=
  ⟨by rw [hr _ (by norm_num)]; exact h.m1,
    h.ext.of_eq (hr _ (by norm_num)),
    fun hx => (h.near hx).of_eq (hr _ (by norm_num)),
    by rw [hr _ (by norm_num)]; exact h.code1,
    by rw [hr _ (by norm_num)]; exact h.coden,
    fun hx => by rw [hr _ (by norm_num)]; exact h.ht hx,
    fun hx => (h.dir hx).of_eq (hr _ (by norm_num))⟩

theorem capS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (J : Merge.Junction) (hgen : SharedGeneric J) {H H' : Host}
    (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 70002))
    (hCw : ChainDescAt c.nmem (c.nreg 70002) (Qof P) H J.whole)
    (hC0 : ChainDescAt c.nmem (c.nreg 70000) (Qof P) H' J.left)
    (hX0 : c.nreg 70000 + 5 ≤ W) (hroom : c.nreg ALLOC + 10200 ≤ W) :
    ∃ c' k, Exec P W capS c c' k ∧ k ≤ 10200 ∧ CapRegs P J c' ∧ c'.nmem = c.nmem ∧
      (∀ r, Bcs r = false → c'.nreg r = c.nreg r) ∧ (∀ r, BR r = false → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨X, hX⟩ : ∃ X, c.nreg 70002 = X := ⟨_, rfl⟩
  obtain ⟨X0, hX0'⟩ : ∃ X, c.nreg 70000 = X := ⟨_, rfl⟩
  rw [hX] at hwf hCw
  rw [hX0'] at hC0 hX0
  have hm2  := hC0.2.2.2.1
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50200 70002, .constN 70131 2,
      .addN 70132 70000 70131, .loadN 70126 70132, .copyN 50201 70126]) c c₁ k₁ ∧ k₁ = 5 ∧
      (c₁.nreg 50200 = X ∧ c₁.nreg 70126 = J.m₁ ∧ c₁.nreg 50201 = J.m₁ ∧
        (∀ r, r ≠ 50200 → r ≠ 50201 → r ≠ 70126 → r ≠ 70131 → r ≠ 70132 →
          c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    exec_block
    all_goals try omega
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hX0']; omega)
    refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 a3 a4 a5 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hX, hX0']
    all_goals exact hm2
  obtain ⟨q00, q26, q01, qr₁, qm₁, qrr₁, qrm₁, qo₁⟩ := q
  have w₁ := e₁.wb_right
  have a₁ : c₁.nreg ALLOC = c.nreg ALLOC := qr₁ _ (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hm1 := J.one_le_m₁
  have hm2' := J.one_le_m₂
  obtain ⟨c₂, k₂, e₂, hk₂, hout, F₂⟩ := primRun capPrim_meets wr_capPrim c₁ w₁ hG hHW
    (by rwx [q00, a₁, qm₁]) (by rwx [q00, qm₁])
    (show 1 ≤ c₁.nreg 50201 ∧ c₁.nreg 50201 + 1 ≤ J.whole.m by
      rw [q01]; exact ⟨hm1, by show J.m₁ + 1 ≤ J.m₁ + J.m₂; omega⟩)
    (by rwo [a₁])
  simp only [CapOut] at hout
  rw [q01] at hout
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hout
  have w₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 70140 50210,
      .copyN 70141 50211, .copyN 70142 50212, .copyN 70143 50213]) c₂ c₃ k₃ ∧ k₃ = 4 ∧
      (c₃.nreg 70140 = c₂.nreg 50210 ∧ c₃.nreg 70141 = c₂.nreg 50211 ∧
        c₃.nreg 70142 = c₂.nreg 50212 ∧ c₃.nreg 70143 = c₂.nreg 50213 ∧
        (∀ r, r ≠ 70140 → r ≠ 70141 → r ≠ 70142 → r ≠ 70143 → c₃.nreg r = c₂.nreg r) ∧
        c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output) := by
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other]
  obtain ⟨t40, t41, t42, t43, qr₃, qm₃, qrr₃, qrm₃, qo₃⟩ := q
  have ex : Exec P W capS c c₃ (k₁ + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  refine ⟨c₃, _, ex, by omega, ⟨?_, o1.of_eq t40, fun hx => (o2 hx).of_eq t41,
    by rwx [t42], by rwx [t42], fun hx => by rw [t42]; exact o5 hx,
    fun hx => (o6 hx hgen.2.2).of_eq t43⟩, by rw [qm₃, F₂.2.2.1, qm₁], fun r hr => ?_,
    fun r hr => ?_, by rw [qrm₃, F₂.2.2.2.1, qrm₁], by rw [qo₃, F₂.2.2.2.2, qo₁]⟩
  · rw [qr₃ _ (by decide) (by decide) (by decide) (by decide), frameB_reg F₂ (by omega), q26]
  · have hr' := hr
    simp only [Bcs, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne] at hr'
    rw [qr₃ r (by omega) (by omega) (by omega) (by omega), F₂.1 r (bprim_of_bcs hr),
      qr₁ r (by omega) (by omega) (by omega) (by omega) (by omega)]
  · rw [qrr₃, F₂.2.1 r (br_prim hr), qrr₁]

/-- The cap query of side `0`. -/
def capQ₀ : Stmt := .ifLtN 70108 70140 (.ifLtN 70141 70105 (capB 70000 70126) .skip) .skip

/-- The cap query of side `1`. -/
def capQ₁ : Stmt := .ifLtN 70108 70140 (.ifLtN 70108 70141 (capB 70001 70108) .skip) .skip

theorem capQ₀_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (J : Merge.Junction) (hP : J.P.Simple) (hgen : SharedGeneric J)
    {H : Host} (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 70000))
    (hC : ChainDescAt c.nmem (c.nreg 70000) (Qof P) H J.left) (hR : CapRegs P J c)
    (h05 : c.nreg 70105 = 1) (h08 : c.nreg 70108 = 0)
    {LB : ℕ} {pre : List (ℕ × ℕ × ℕ)}
    (hA : c.nreg ALLOC = LB + 3 * pre.length) (h28 : c.nreg 70128 = pre.length)
    (hL : ChordListAt c.nmem LB pre) (hroom : c.nreg ALLOC + capBCost ≤ W)
    (hcW : pre.length + 2 ≤ W) :
    ∃ c' k l, Exec P W capQ₀ c c' k ∧ k ≤ capBCost + 4 ∧ 3 * l.length ≤ k ∧ l.length ≤ 1 ∧
      c'.nreg ALLOC = LB + 3 * (pre ++ l).length ∧
      c'.nreg 70128 = (pre ++ l).length ∧
      ChordListAt c'.nmem LB (pre ++ l) ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, Bpt r = false → c'.nreg r = c.nreg r) ∧ (∀ r, BR r = false → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (SharedExtremum J → ¬ NearU J → PtAns J (Qof P) 0 (capOrigin J) (capDir J) l) ∧ (¬ (SharedExtremum J ∧ ¬ NearU J) → l = []) := by
  have e40 := hR.ext
  by_cases hx : c.nreg 70140 = 1
  · have hX : SharedExtremum J := e40.2.1 hx
    have e41 := hR.near hX
    have hlt1 : c.nreg 70108 < c.nreg 70140 := by rwo [h08, hx]
    by_cases hu : c.nreg 70141 = 1
    · have hU : NearU J := e41.2.1 hu
      have hlt2 : ¬ c.nreg 70141 < c.nreg 70105 := by rwo [hu, h05]
      refine ⟨c, _, [], .ifLtN_true hlt1 (.ifLtN_false hlt2 (.skip hw)),
        by ufo capBCost, by simp, by simp, by simpa using hA, by simpa using h28,
        by simpa using hL, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl,
        fun _ h => absurd hU h, fun _ => rfl⟩
    · have hU : ¬ NearU J := fun h => hu (e41.2.2 h)
      have h41 : c.nreg 70141 = 0 := by have := e41.1; omega
      have hlt2 : c.nreg 70141 < c.nreg 70105 := by rwo [h41, h05]
      obtain ⟨h1c, hcn, hht⟩ := And.intro hR.code1 (And.intro hR.coden (hR.ht hX))
      have hh  := hht
      have hgeo := capPos₀ J (Qof P) hgen hX hU hh
      rw [show c.nreg 70142 - 1 + 1 = c.nreg 70142 by omega] at hgeo
      obtain ⟨c', k, l, e, hk, hk', hl, a', n', L', m', r', rr', rm', o', hans⟩ :=
        capB_exec (P := P) c hw hG hHW (D := 70000) (K := 70126) (by norm_num) (by norm_num)
          hwf J 0 hC hP (kk := J.m₁) hR.m1 (by show J.m₁ ≤ J.m₁; exact le_rfl) rfl h1c hcn rfl
          (z := capOrigin J) hgeo
          (by rwx [capOrigin_snd J hgen]) h05 h08 hA h28 hL hroom hcW
      rw [capDir_eq J (hR.dir hX)] at hans
      exact ⟨c', _, l, .ifLtN_true hlt1 (.ifLtN_true hlt2 e), by omega, by omega, hl, a', n', L', m',
        r', rr',
        rm', o', fun _ _ => hans, fun h => absurd ⟨hX, hU⟩ h⟩
  · have hX : ¬ SharedExtremum J := fun h => hx (e40.2.2 h)
    have hlt1 : ¬ c.nreg 70108 < c.nreg 70140 := by have := e40.1; rwo [h08]
    refine ⟨c, _, [], .ifLtN_false hlt1 (.skip hw), by ufo capBCost, by simp, by simp,
      by simpa using hA, by simpa using h28, by simpa using hL, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, fun h => absurd h hX, fun _ => rfl⟩

theorem capQ₁_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (J : Merge.Junction) (hP : J.P.Simple) (hgen : SharedGeneric J)
    {H : Host} (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 70001))
    (hC : ChainDescAt c.nmem (c.nreg 70001) (Qof P) H J.right) (hR : CapRegs P J c)
    (h05 : c.nreg 70105 = 1) (h08 : c.nreg 70108 = 0)
    {LB : ℕ} {pre : List (ℕ × ℕ × ℕ)}
    (hA : c.nreg ALLOC = LB + 3 * pre.length) (h28 : c.nreg 70128 = pre.length)
    (hL : ChordListAt c.nmem LB pre) (hroom : c.nreg ALLOC + capBCost ≤ W)
    (hcW : pre.length + 2 ≤ W) :
    ∃ c' k l, Exec P W capQ₁ c c' k ∧ k ≤ capBCost + 4 ∧ 3 * l.length ≤ k ∧ l.length ≤ 1 ∧
      c'.nreg ALLOC = LB + 3 * (pre ++ l).length ∧
      c'.nreg 70128 = (pre ++ l).length ∧
      ChordListAt c'.nmem LB (pre ++ l) ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, Bpt r = false → c'.nreg r = c.nreg r) ∧ (∀ r, BR r = false → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (SharedExtremum J → NearU J → PtAns J (Qof P) 1 (capOrigin J) (capDir J) l) ∧ (¬ (SharedExtremum J ∧ NearU J) → l = []) := by
  have e40 := hR.ext
  by_cases hx : c.nreg 70140 = 1
  · have hX : SharedExtremum J := e40.2.1 hx
    have e41 := hR.near hX
    have hlt1 : c.nreg 70108 < c.nreg 70140 := by rwo [h08, hx]
    by_cases hu : c.nreg 70141 = 1
    · have hU : NearU J := e41.2.1 hu
      have hlt2 : c.nreg 70108 < c.nreg 70141 := by rwo [hu, h08]
      obtain ⟨h1c, hcn, hht⟩ := And.intro hR.code1 (And.intro hR.coden (hR.ht hX))
      have hh  := hht
      have hgeo := capPos₁ J (Qof P) hgen hX hU hh
      rw [show c.nreg 70142 - 1 + 1 = c.nreg 70142 by omega] at hgeo
      obtain ⟨c', k, l, e, hk, hk', hl, a', n', L', m', r', rr', rm', o', hans⟩ :=
        capB_exec (P := P) c hw hG hHW (D := 70001) (K := 70108) (by norm_num) (by norm_num)
          hwf J 1 hC hP (kk := 0) h08 (Nat.zero_le _) rfl h1c hcn rfl
          (z := capOrigin J) hgeo
          (by rwx [capOrigin_snd J hgen]) h05 h08 hA h28 hL hroom hcW
      rw [capDir_eq J (hR.dir hX)] at hans
      exact ⟨c', _, l, .ifLtN_true hlt1 (.ifLtN_true hlt2 e), by omega, by omega, hl, a', n', L', m',
        r', rr',
        rm', o', fun _ _ => hans, fun h => absurd ⟨hX, hU⟩ h⟩
    · have hU : ¬ NearU J := fun h => hu (e41.2.2 h)
      have h41 : c.nreg 70141 = 0 := by have := e41.1; omega
      have hlt2 : ¬ c.nreg 70108 < c.nreg 70141 := by rwo [h41, h08]
      refine ⟨c, _, [], .ifLtN_true hlt1 (.ifLtN_false hlt2 (.skip hw)),
        by ufo capBCost, by simp, by simp, by simpa using hA, by simpa using h28,
        by simpa using hL, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl,
        fun _ h => absurd h hU, fun _ => rfl⟩
  · have hX : ¬ SharedExtremum J := fun h => hx (e40.2.2 h)
    have hlt1 : ¬ c.nreg 70108 < c.nreg 70140 := by have := e40.1; rwo [h08]
    refine ⟨c, _, [], .ifLtN_false hlt1 (.skip hw), by ufo capBCost, by simp, by simp,
      by simpa using hA, by simpa using h28, by simpa using hL, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, fun h => absurd h hX, fun _ => rfl⟩

end

end FuseAsm

end Chazelle.Core
