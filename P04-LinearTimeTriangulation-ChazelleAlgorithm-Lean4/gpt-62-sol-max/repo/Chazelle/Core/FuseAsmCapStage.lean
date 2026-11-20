module

meta import Chazelle.Programs.RamEval

public import Chazelle.Programs.RamSimp

public import Chazelle.Core.FuseAsmPtStage

/-!
# WP-F fusion assembly, part 19: the cap query

* `capS`: `capPrim` on the whole chain at the shared vertex (`k = m₁`, read from the descriptor
  of `C₁`); its four answers are saved in `70140 … 70143` (`capS_exec`).
* `capB D K`: the point query at the walk position `(6 + tpos Cᵢ k, code)` of the chain of the
  descriptor in `D` (`k` in register `K`, the code in `70142`, the direction in `70143`)
  (`capB_exec`).
* `capQ₀`, `capQ₁`: the cap query of side `0` (if the shared vertex is an extremum whose nearer
  arm is `w`) and of side `1` (nearer arm `u`) (`capQ_exec`).
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
  simp_all

/-- The point query at a walk position of the chain of the descriptor in `D`. -/
def capB (D K : ℕ) : Stmt :=
  .seq (block [.copyN 50200 D, .copyN 50110 K]) (.seq tposS
    (.seq (block [.copyN 50202 70142, .copyN 50203 70143, .subN 70124 70142 70105]) ptQ))

/-- The cost bound of `capB`. -/
@[ram_layout] def capBCost : ℕ := 35100

set_option maxHeartbeats 16000000 in
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
      ChordListAt c'.nmem LB (pre ++ l) ∧ (MemEqBelow (c.nreg ALLOC) c'.nmem c.nmem) ∧
      (∀ r, Bpt r = false → c'.nreg r = c.nreg r) ∧ (∀ r, BR r = false → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      PtAns J (Qof P) i z (dirOf ρ) l := by
  set C := sideChain J i with hCdef
  obtain ⟨hB5, hwf'⟩ := hwf
  have hm := chain_m_le ⟨hB5, hwf'⟩ hC
  have hn : (Qof P).n = P.n := shear_n _ _
  unfold hostWords at hHW
  have hmW : 2 * C.m + 7 ≤ W := by omega
  obtain ⟨X, hX⟩ := exists_eq' (a' := c.nreg D)
  rw [hX] at hC hB5 hwf'
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50200 D, .copyN 50110 K])
      c c₁ k₁ ∧ k₁ = 2 ∧
      (c₁.nreg 50200 = X ∧ c₁.nreg 50110 = kk ∧
        (∀ r, r ≠ 50200 → r ≠ 50110 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    ram_exec
  obtain ⟨q00, q10, qr₁, qm₁, qrr₁, qrm₁, qo₁⟩ := q
  have w₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, q21, F₂⟩ := tposS_exec (P := P) c₁ w₁ (by rwa [q00, qm₁])
    q10 hkk (by rw [q00]; omega) hmW
  have w₂ := e₂.wb_right
  have r42 : c₂.nreg 70142 = code := by
    frame_finish
  have r43 : c₂.nreg 70143 = ρ := by
    frame_finish
  have r05 : c₂.nreg 70105 = 1 := by
    frame_finish
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
    ram_rw [qr₃ r, F₂.1 r (btp_of hr),
      qr₁ r]
  have k₃rr : ∀ r, BR r = false → c₃.rreg r = c.rreg r := fun r hr => by
    rw [qrr₃, F₂.2.1 r (br_tp hr), qrr₁]
  have a₃ : c₃.nreg ALLOC = c.nreg ALLOC := by
    frame_finish
  have r300 : c₃.nreg 50200 = X := by
    frame_finish
  have r301 : c₃.nreg 50201 = 6 + tpos C kk := by
    frame_finish
  have r328 : c₃.nreg 70128 = pre.length := by
    frame_finish
  obtain ⟨hpos, hp0, hp1, hzs⟩ := hgeo
  have hPC : C.P.Simple := by rwa [hCdef, sideChain_P]
  obtain ⟨c₄, k₄, l, e₄, hk₄, hk₄', hl, a₄, n₄, L₄, m₄, r₄, rr₄, rm₄, o₄, res⟩ :=
    ptQ_exec (P := P) c₃ w₃ hG (by reg_omega)
      (by rw [r300, a₃, m₃]; exact ⟨hB5, hwf'⟩) (by rwa [r300, m₃])
      ⟨⟨by rw [r301]; exact vpos_edge C kk, ⟨by rwa [r301, q32],
        by rwa [r301, q32], by ram_finish⟩,
        by rw [r301, q32, hpos]; exact abs_snd_lt_radius C hzs⟩, hPC, hmW⟩
      (by ram_rw [k₃r, h05]) (by ram_rw [k₃r, h08])
      (by rw [a₃, hA]) r328 (by rwa [m₃])
      (by rw [a₃]; unfold capBCost at hroom; omega) (by rw [q24]; omega) (by omega)
  rw [r301, q32, q33, q24] at res
  have ex : Exec P W (capB D K) c c₄ (k₁ + (k₂ + (k₃ + k₄))) :=
    (by ram_path)
  have hvn : code - 1 < (Qof P).n := by rw [hn]; omega
  
  refine ⟨c₄, _, l, ex, by reg_omega, by omega, hl, a₄, n₄, L₄,
    fun a ha => ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [m₄ a (by rwa [a₃]), m₃]
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
  ⟨by ram_rw [hr]; exact h.m1,
    h.ext.of_eq (hr _ (by norm_num)),
    fun hx => (h.near hx).of_eq (hr _ (by norm_num)),
    by ram_rw [hr]; exact h.code1,
    by ram_rw [hr]; exact h.coden,
    fun hx => by ram_rw [hr]; exact h.ht hx,
    fun hx => (h.dir hx).of_eq (hr _ (by norm_num))⟩

set_option maxHeartbeats 8000000 in
theorem capS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (J : Merge.Junction) (hgen : SharedGeneric J) {H H' : Host}
    (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 70002))
    (hCw : ChainDescAt c.nmem (c.nreg 70002) (Qof P) H J.whole)
    (hC0 : ChainDescAt c.nmem (c.nreg 70000) (Qof P) H' J.left)
    (hX0 : c.nreg 70000 + 5 ≤ W) (hroom : c.nreg ALLOC + 10200 ≤ W) :
    ∃ c' k, Exec P W capS c c' k ∧ k ≤ 10200 ∧ CapRegs P J c' ∧ c'.nmem = c.nmem ∧
      (∀ r, Bcs r = false → c'.nreg r = c.nreg r) ∧ (∀ r, BR r = false → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨X, hX⟩ := exists_eq' (a' := c.nreg 70002)
  obtain ⟨X0, hX0'⟩ := exists_eq' (a' := c.nreg 70000)
  rw [hX] at hwf hCw
  rw [hX0'] at hC0 hX0
  have hm2 := hC0.2.2.2.1
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
    simp_all
  obtain ⟨q00, q26, q01, qr₁, qm₁, qrr₁, qrm₁, qo₁⟩ := q
  have w₁ := e₁.wb_right
  have a₁ : c₁.nreg ALLOC = c.nreg ALLOC := (ram_app% (qr₁ _ ?_ ?_ ?_
    ?_ ?_))
  have hm1 := J.one_le_m₁
  have hm2' := J.one_le_m₂
  obtain ⟨c₂, k₂, e₂, hk₂, hout, F₂⟩ := primRun capPrim_meets wr_capPrim c₁ w₁ hG hHW
    (by rwa [q00, a₁, qm₁]) (by rwa [q00, qm₁])
    (show 1 ≤ c₁.nreg 50201 ∧ c₁.nreg 50201 + 1 ≤ J.whole.m by
      simp_all <;> omega)
    (by rw [a₁]; omega)
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
    ram_exec
  obtain ⟨t40, t41, t42, t43, qr₃, qm₃, qrr₃, qrm₃, qo₃⟩ := q
  have ex : Exec P W capS c c₃ (k₁ + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  refine ⟨c₃, _, ex, by omega, ⟨?_, o1.of_eq t40, fun hx => (o2 hx).of_eq t41,
    by rwa [t42], by rwa [t42], fun hx => by rw [t42]; exact o5 hx,
    fun hx => (o6 hx hgen.2.2).of_eq t43⟩, by rw [qm₃, F₂.2.2.1, qm₁], fun r hr => ?_,
    fun r hr => ?_, by rw [qrm₃, F₂.2.2.2.1, qrm₁], by rw [qo₃, F₂.2.2.2.2, qo₁]⟩
  · frame_finish
  · have hr' := hr
    simp only [Bcs, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne] at hr'
    ram_rw [(ram_app% (qr₃ r ?_ ?_ ?_ ?_)), F₂.1 r (bprim_of_bcs hr),
      qr₁ r]
  · rw [qrr₃, F₂.2.1 r (br_prim hr), qrr₁]

/-- The descriptor and shared-vertex position registers for the cap query. -/
abbrev capDesc (right : Bool) : ℕ := if right then 70001 else 70000
abbrev capIndex (right : Bool) : ℕ := if right then 70108 else 70126

abbrev capLo (right : Bool) : ℕ := if right then 70108 else 70141
abbrev capHi (right : Bool) : ℕ := if right then 70141 else 70105

/-- Run the cap query only for the side whose arm is farther from the shared vertex. -/
def capQuery (right : Bool) : Stmt :=
  .ifLtN 70108 70140 (.ifLtN (capLo right) (capHi right)
    (capB (capDesc right) (capIndex right)) .skip) .skip

abbrev capQ₀ : Stmt := capQuery false
abbrev capQ₁ : Stmt := capQuery true

/-- Which arm is nearer, as required by the cap query for the given side. -/
abbrev CapNear (J : Merge.Junction) (right : Bool) : Prop := if right then NearU J else ¬ NearU J

set_option maxHeartbeats 8000000 in
theorem capQ_exec {P : Polygon} {W : ℕ} {right : Bool} (c : Config) (hw : WordsBounded W c)
    (hG : GoodEnv P) (hHW : hostWords P.n ≤ W) (J : Merge.Junction) (hP : J.P.Simple)
    (hgen : SharedGeneric J) {H : Host} (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg (capDesc right)))
    (hC : ChainDescAt c.nmem (c.nreg (capDesc right)) (Qof P) H (sideChain J right.toNat))
    (hR : CapRegs P J c) (h05 : c.nreg 70105 = 1) (h08 : c.nreg 70108 = 0)
    {LB : ℕ} {pre : List (ℕ × ℕ × ℕ)}
    (hA : c.nreg ALLOC = LB + 3 * pre.length) (h28 : c.nreg 70128 = pre.length)
    (hL : ChordListAt c.nmem LB pre) (hroom : c.nreg ALLOC + capBCost ≤ W)
    (hcW : pre.length + 2 ≤ W) :
    ∃ c' k l, Exec P W (capQuery right) c c' k ∧ k ≤ capBCost + 4 ∧ 3 * l.length ≤ k ∧ l.length ≤ 1 ∧
      c'.nreg ALLOC = LB + 3 * (pre ++ l).length ∧ c'.nreg 70128 = (pre ++ l).length ∧
      ChordListAt c'.nmem LB (pre ++ l) ∧ MemEqBelow (c.nreg ALLOC) c'.nmem c.nmem ∧
      (∀ r, Bpt r = false → c'.nreg r = c.nreg r) ∧ (∀ r, BR r = false → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (SharedExtremum J → CapNear J right → PtAns J (Qof P) right.toNat (capOrigin J) (capDir J) l) ∧
      (¬ (SharedExtremum J ∧ CapNear J right) → l = []) := by
  have hgate : c.nreg 70108 < c.nreg 70140 ↔ SharedExtremum J := by
    obtain ⟨h, e⟩ := hR.ext
    exact (show c.nreg 70108 < c.nreg 70140 ↔ c.nreg 70140 = 1 by omega).trans e
  have hside (hx : SharedExtremum J) :
      c.nreg (capLo right) < c.nreg (capHi right) ↔ CapNear J right := by
    obtain ⟨h, e⟩ := hR.near hx
    cases right
    · exact (show c.nreg 70141 < c.nreg 70105 ↔ c.nreg 70141 ≠ 1 by omega).trans (not_congr e)
    · exact (show c.nreg 70108 < c.nreg 70141 ↔ c.nreg 70141 = 1 by omega).trans e
  by_cases h : SharedExtremum J ∧ CapNear J right
  · obtain ⟨hx, hu⟩ := h
    let C := sideChain J right.toNat
    let k := if right then 0 else J.m₁
    have hk : c.nreg (capIndex right) = k := by cases right; exact hR.m1; exact h08
    have hkk : k ≤ C.m := by cases right; exact le_rfl; exact Nat.zero_le _
    have hi := hR.code1
    have hh := hR.ht hx
    let p : WPos := ⟨6 + tpos C k, c.nreg 70142⟩
    have hgeo : (chainModel C).pos (Qof P) p = capOrigin J ∧
        0 ≤ (chainModel C).param (Qof P) p ∧ (chainModel C).param (Qof P) p < 1 ∧
        capOrigin J ∈ C.set := by
      have he : c.nreg 70142 - 1 + 1 = c.nreg 70142 := by omega
      cases right
      · have hp := capPos₀ J (Qof P) hgen hx hu hh
        rw [he] at hp
        exact hp
      · have hp := capPos₁ J (Qof P) hgen hx hu hh
        rw [he] at hp
        exact hp
    obtain ⟨c', k', l, e, hk', hl, hlen, a', n', L', m', r', rr', rm', o', hans⟩ :=
      capB_exec (P := P) c hw hG hHW (by cases right <;> decide) (by cases right <;> decide)
        hwf J right.toNat hC hP hk hkk rfl hi hR.coden rfl hgeo
        (hh.trans (capOrigin_snd J hgen).symm) h05 h08 hA h28 hL hroom hcW
    rw [capDir_eq J (hR.dir hx)] at hans
    exact ⟨c', _, l, .ifLtN_true (hgate.2 hx) (.ifLtN_true ((hside hx).2 hu) e), by omega,
      by omega, hlen, a', n', L', m', r', rr', rm', o', fun _ _ => hans, fun h => (h ⟨hx, hu⟩).elim⟩
  · obtain ⟨k, e, hk⟩ : ∃ k, Exec P W (capQuery right) c c k ∧ k ≤ 4 := by
      by_cases hx : SharedExtremum J
      · exact ⟨_, .ifLtN_true (hgate.2 hx) (.ifLtN_false (fun ht => h ⟨hx, (hside hx).1 ht⟩)
          (.skip hw)), by decide⟩
      · exact ⟨_, .ifLtN_false (fun ht => hx (hgate.1 ht)) (.skip hw), by decide⟩
    exact ⟨c, k, [], e, by omega, by simp, by simp, by simpa using hA, by simpa using h28,
      by simpa using hL, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl,
      fun hx hu => (h ⟨hx, hu⟩).elim, fun _ => rfl⟩

end

end FuseAsm

end Chazelle.Core
