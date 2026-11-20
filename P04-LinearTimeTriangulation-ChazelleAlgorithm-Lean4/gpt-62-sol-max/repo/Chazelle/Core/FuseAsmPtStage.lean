module

public import Chazelle.Machine.FrameFields

meta import Chazelle.Programs.RamEval

public import Chazelle.Programs.RamSimp

public import Chazelle.Core.FuseAsmPtRam
public import Chazelle.Core.MergeAsmDesc

/-!
# WP-F fusion assembly, part 18: the vertex queries

`vtxPts D off`: for the chain `C` of the descriptor whose address is in register `D` and the
vertex `k` stored at `D + off` (`off = 2`: the last vertex `m`; `off = 3`: the top), the point
queries at `C.vertex k` in both directions (`vtxPts_exec`).
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK SweepPrim WalkEmbed MergeAsm

@[expose] public section

/-- **From the outcome of `ptQ` to the answer of a point query.** -/
theorem ptAns_of_res (J : Merge.Junction) (P : Polygon) (i : ℕ) (hP : J.P.Simple)
    {e h ρ hv : ℕ} {l : List (ℕ × ℕ × ℕ)} (hres : PtRes P (sideChain J i) e h ρ hv l) {z : Point}
    (hz : (chainModel (sideChain J i)).pos (Qof P) ⟨e, h⟩ = z) (hzs : z ∈ (sideChain J i).set)
    (hhv : ((Qof P).vtx hv).2 = z.2) (hvn : hv < (Qof P).n) :
    PtAns J (Qof P) i z (dirOf ρ) l := by
  rcases hres with ⟨rfl, hno⟩ | ⟨e', h', rfl, harr⟩
  · rw [hz] at hno
    exact ptAns_none J (Qof P) hP i hzs ((sideChain J i).snd_le_top_of_mem_set hzs) hno
  · rw [hz] at harr
    exact ptAns_some J (Qof P) i harr hhv hvn ((sideChain J i).snd_le_top_of_mem_set hzs)

theorem dirOf_one : dirOf 1 = 1 := by simp [dirOf]

theorem dirOf_zero : dirOf 0 = -1 := by simp [dirOf]

/-- The registers that the point queries may write outside the primitive bands. -/
def Bpt (r : ℕ) : Bool := Bprim r || decide (50200 ≤ r ∧ r < 50210) ||
  decide (70120 ≤ r ∧ r < 70126) || decide (70127 ≤ r ∧ r < 70140) || r == ALLOC

/-- The real registers that the point queries may write. -/
def BR (r : ℕ) : Bool := Bprim r || Btp r

theorem br_prim {r : ℕ} (h : BR r = false) : Bprim r = false := by
  simp only [BR, Bool.or_eq_false_iff] at h; exact h.1

theorem br_tp {r : ℕ} (h : BR r = false) : Btp r = false := by
  simp only [BR, Bool.or_eq_false_iff] at h; exact h.2

theorem bprim_of {r : ℕ} (h : Bpt r = false) : Bprim r = false := by
  simp only [Bpt, Bool.or_eq_false_iff] at h; exact h.1.1.1.1

theorem btp_of {r : ℕ} (h : Bpt r = false) : Btp r = false := by
  simp only [Bpt, Bprim, Btp, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
    at h ⊢
  omega

/-- The vertex queries at the vertex stored at `D + off`. -/
def vtxPts (D off : ℕ) : Stmt :=
  .seq (block [.copyN 50200 D, .constN 70131 off, .addN 70132 D 70131, .loadN 70125 70132,
      .copyN 50201 70125])
    (.seq hvPrim (.seq (block [.copyN 70124 50210, .copyN 50110 70125]) (.seq tposS
      (.seq (block [.constN 50202 0, .constN 50203 1]) (.seq ptQ
        (.seq (block [.constN 50203 0]) ptQ))))))

/-- The cost bound of `vtxPts`. -/
@[ram_layout] def vtxCost : ℕ := 74000

set_option maxHeartbeats 16000000 in
theorem vtxPts_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) {D off : ℕ} (hD : 70000 ≤ D ∧ D < 70100) (hoff : off ≤ 4)
    (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg D)) (J : Merge.Junction) (i : ℕ)
    {H : Host} (hC : ChainDescAt c.nmem (c.nreg D) (Qof P) H (sideChain J i))
    (hP : J.P.Simple) {kk : ℕ} (hk : c.nmem (c.nreg D + off) = kk)
    (hkk : kk ≤ (sideChain J i).m) (h05 : c.nreg 70105 = 1) (h08 : c.nreg 70108 = 0)
    {LB : ℕ} {pre : List (ℕ × ℕ × ℕ)}
    (hA : c.nreg ALLOC = LB + 3 * pre.length) (h28 : c.nreg 70128 = pre.length)
    (hL : ChordListAt c.nmem LB pre) (hroom : c.nreg ALLOC + vtxCost ≤ W)
    (hcW : pre.length + 2 ≤ W) :
    ∃ c' k l₁ l₀, Exec P W (vtxPts D off) c c' k ∧ k ≤ vtxCost ∧
      3 * (l₁.length + l₀.length) ≤ k ∧ l₁.length ≤ 1 ∧
      l₀.length ≤ 1 ∧
      c'.nreg ALLOC = LB + 3 * (pre ++ l₁ ++ l₀).length ∧
      c'.nreg 70128 = (pre ++ l₁ ++ l₀).length ∧
      ChordListAt c'.nmem LB (pre ++ l₁ ++ l₀) ∧ (MemEqBelow (c.nreg ALLOC) c'.nmem c.nmem) ∧
      (∀ r, Bpt r = false → c'.nreg r = c.nreg r) ∧ (∀ r, BR r = false → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      PtAns J (Qof P) i ((sideChain J i).vertex kk) 1 l₁ ∧
      PtAns J (Qof P) i ((sideChain J i).vertex kk) (-1) l₀ := by
  set C := sideChain J i with hCdef
  obtain ⟨hB5, hwf'⟩ := hwf
  have hm := chain_m_le ⟨hB5, hwf'⟩ hC
  have hn : (Qof P).n = P.n := shear_n _ _
  unfold hostWords at hHW
  have hmW : 2 * C.m + 7 ≤ W := by omega
  obtain ⟨X, hX⟩ := exists_eq' (a' := c.nreg D)
  rw [hX] at hC hk hB5 hwf'
  -- the vertex index
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50200 D, .constN 70131 off,
      .addN 70132 D 70131, .loadN 70125 70132, .copyN 50201 70125]) c c₁ k₁ ∧ k₁ = 5 ∧
      (c₁.nreg 50200 = X ∧ c₁.nreg 70125 = kk ∧ c₁.nreg 50201 = kk ∧
        (∀ r, r ≠ 50200 → r ≠ 50201 → r ≠ 70125 → r ≠ 70131 → r ≠ 70132 →
          c₁.nreg r = c.nreg r) ∧
        Machine.NatRegFrame c c₁) := by
    exec_block
    all_goals try omega
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hX]; omega)
    refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 a3 a4 a5 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals frame_finish
    all_goals exact hk
  obtain ⟨q00, q26, q01, qr₁, qm₁, qrr₁, qrm₁, qo₁⟩ := q
  have w₁ := e₁.wb_right
  have a₁ : c₁.nreg ALLOC = c.nreg ALLOC := (ram_app% (qr₁ _ ?_ ?_ ?_
    ?_ ?_))
  -- the height of the vertex
  obtain ⟨c₂, k₂, e₂, hk₂, ⟨hv₁, hv₂⟩, F₂⟩ := primRun hvPrim_meets wr_hvPrim c₁ w₁ hG
    (by reg_omega) (by rw [q00, a₁, qm₁]; exact ⟨hB5, hwf'⟩)
    (by rwa [q00, qm₁]) (show c₁.nreg 50201 ≤ C.m by rwa [q01])
    (by rw [a₁]; unfold vtxCost at hroom; omega)
  rw [q01] at hv₂
  have w₂ := e₂.wb_right
  obtain ⟨hv, hhv⟩ := exists_eq' (a' := c₂.nreg 50210)
  rw [hhv] at hv₁ hv₂
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 70124 50210,
      .copyN 50110 70125]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
      (c₃.nreg 70124 = hv ∧ c₃.nreg 50110 = kk ∧
        (∀ r, r ≠ 70124 → r ≠ 50110 → c₃.nreg r = c₂.nreg r) ∧
        Machine.NatRegFrame c₂ c₃) := by
    have r26 : c₂.nreg 70125 = kk := by ram_rw [frameB_reg F₂, q26]
    ram_exec
  obtain ⟨q24, q10, qr₃, qm₃, qrr₃, qrm₃, qo₃⟩ := q
  have w₃ := e₃.wb_right
  have m₃ : c₃.nmem = c.nmem := by rw [qm₃, F₂.2.2.1, qm₁]
  have r00 : c₃.nreg 50200 = X := by
    frame_finish
  -- the walk position
  obtain ⟨c₄, k₄, e₄, hk₄, q41, F₄⟩ := tposS_exec (P := P) c₃ w₃ (by rwa [r00, m₃])
    q10 hkk (by rw [r00]; omega) hmW
  have w₄ := e₄.wb_right
  obtain ⟨c₅, k₅, e₅, hk₅, q⟩ : ∃ c₅ k₅, Exec P W (block [.constN 50202 0, .constN 50203 1])
      c₄ c₅ k₅ ∧ k₅ = 2 ∧
      (c₅.nreg 50202 = 0 ∧ c₅.nreg 50203 = 1 ∧
        (∀ r, r ≠ 50202 → r ≠ 50203 → c₅.nreg r = c₄.nreg r) ∧
        Machine.NatRegFrame c₄ c₅) := by
    ram_exec
  obtain ⟨q52, q53, qr₅, qm₅, qrr₅, qrm₅, qo₅⟩ := q
  have w₅ := e₅.wb_right
  have m₅ : c₅.nmem = c.nmem := by rw [qm₅, F₄.2.2.1, m₃]
  -- registers kept from `c` to `c₅`
  have k₅r : ∀ r, Bpt r = false → c₅.nreg r = c.nreg r := fun r hr => by
    have hr' := hr
    simp only [Bpt, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
      at hr'
    ram_rw [qr₅ r, F₄.1 r (btp_of hr), qr₃ r,
      F₂.1 r (bprim_of hr), qr₁ r]
  have k₅rr : ∀ r, BR r = false → c₅.rreg r = c.rreg r := fun r hr => by
    rw [qrr₅, F₄.2.1 r (br_tp hr), qrr₃, F₂.2.1 r (br_prim hr), qrr₁]
  have a₅ : c₅.nreg ALLOC = c.nreg ALLOC := by
    ram_post [qr₅, F₄.1, qr₃, frameB_alloc F₂, a₁]
  have r500 : c₅.nreg 50200 = X := by
    frame_finish
  have r501 : c₅.nreg 50201 = 6 + tpos C kk := by frame_finish
  have r524 : c₅.nreg 70124 = hv := by
    frame_finish
  have r528 : c₅.nreg 70128 = pre.length := by
    ram_rw [qr₅, F₄.1, qr₃,
      frameB_reg F₂, qr₁,
      h28]
  -- the geometry of the query
  have hvpos : (chainModel C).pos (Qof P) ⟨6 + tpos C kk, 0⟩ = C.vertex kk := vpos C _ hkk
  have hzs := C.vertex_mem_set hkk
  have hPC : C.P.Simple := by rwa [hCdef, sideChain_P]
  have hin : ∀ c' : Config, c'.nreg 50201 = 6 + tpos C kk → c'.nreg 50202 = 0 →
      ArrIn P W C c' := fun c' h1 h2 => ⟨⟨by rw [h1]; exact vpos_edge C kk,
      ⟨by ram_finish, by rw [h1, h2]; exact zero_lt_one,
        by rw [h2]; exact Nat.zero_le _⟩,
      by rw [h1, h2, hvpos]; exact abs_snd_lt_radius C hzs⟩, hPC, hmW⟩
  -- direction `1`
  obtain ⟨c₆, k₆, l₁, e₆, hk₆, hk₆', hl₁, a₆, n₆, L₆, m₆, r₆, rr₆, rm₆, o₆, res₁⟩ :=
    ptQ_exec (P := P) c₅ w₅ hG (by reg_omega)
      (by rw [r500, a₅, m₅]; exact ⟨hB5, hwf'⟩) (by rwa [r500, m₅])
      (hin c₅ r501 q52) (by ram_rw [k₅r, h05]) (by ram_rw [k₅r, h08])
      (by rw [a₅, hA]) r528 (by rwa [m₅])
      (by rw [a₅]; unfold vtxCost at hroom; omega) (by rw [r524]; omega)
      (by omega)
  rw [r501, q52, q53, r524] at res₁
  have w₆ := e₆.wb_right
  obtain ⟨c₇, k₇, e₇, hk₇, q73, qr₇, qm₇, qrr₇, qrm₇, qo₇⟩ : ∃ c₇ k₇, Exec P W
      (block [.constN 50203 0]) c₆ c₇ k₇ ∧ k₇ = 1 ∧ c₇.nreg 50203 = 0 ∧
      (Machine.NRegEqExcept 50203 c₆ c₇) ∧
      Machine.NatRegFrame c₆ c₇ := by
    ram_exec
  have w₇ := e₇.wb_right
  have k67 : ∀ r, Bprim r = false → r ≠ 70128 → r ≠ 70129 → r ≠ ALLOC → r ≠ 50203 →
      c₇.nreg r = c₅.nreg r := fun r h1 h2 h3 h4 h5 => by rw [qr₇ r h5, r₆ r h1 h2 h3 h4]
  have a₇ : c₇.nreg ALLOC = LB + 3 * (pre ++ l₁).length := by ram_rw [qr₇, a₆]
  -- direction `0`
  obtain ⟨c₈, k₈, l₀, e₈, hk₈, hk₈', hl₀, a₈, n₈, L₈, m₈, r₈, rr₈, rm₈, o₈, res₀⟩ :=
    ptQ_exec (P := P) c₇ w₇ hG (by reg_omega)
      (by
        rw [(ram_app% (k67 50200 ?_ ?_ ?_ ?_ ?_)), r500, qm₇]
        exact chainWF_copy ⟨hB5, hwf'⟩ hC (fun a ha => by rw [m₆ a (by rwa [a₅]), m₅])
          (fun j hj => by rw [m₆ _ (by rw [a₅]; omega), m₅])
          (by rw [a₇, List.length_append]; omega) (by rw [a₇, List.length_append]; omega))
      (by
        rw [(ram_app% (k67 50200 ?_ ?_ ?_ ?_ ?_)), r500, qm₇]
        obtain ⟨-, -, hEb, -⟩ := hwf' H C hC
        exact chainDescAt_copy hC hEb (fun a ha => by rw [m₆ a (by rwa [a₅]), m₅])
          (fun j hj => by rw [m₆ _ (by rw [a₅]; omega), m₅]))
      (hin c₇ (by ram_post)
        (by frame_finish))
      (by frame_finish [k67, k₅r, h05])
      (by frame_finish [k67, k₅r, h08])
      a₇ (by ram_rw [qr₇, n₆]) (by rwa [qm₇])
      (by rw [a₇]; unfold vtxCost at hroom; rw [List.length_append]; omega)
      (by rw [(ram_app% (k67 70124 ?_ ?_ ?_ ?_ ?_)), r524]; omega)
      (by rw [List.length_append]; omega)
  rw [(ram_app% (k67 50201 ?_ ?_ ?_ ?_ ?_)),
    (ram_app% (k67 50202 ?_ ?_ ?_ ?_ ?_)),
    (ram_app% (k67 70124 ?_ ?_ ?_ ?_ ?_)), r501, q52, r524, q73]
    at res₀
  have ex : Exec P W (vtxPts D off) c c₈
      (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + k₈))))))) :=
    (by ram_path)
  have hvn : hv < (Qof P).n := by rwa [hn]
  refine ⟨c₈, _, l₁, l₀, ex, by reg_omega, by omega, hl₁, hl₀, a₈, n₈, L₈,
    fun a ha => ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₈ a (by rw [a₇, List.length_append]; rw [hA] at ha; omega), qm₇,
      m₆ a (by rwa [a₅]), m₅]
  · have hr' := hr
    simp only [Bpt, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
      at hr'
    ram_rw [r₈ r (bprim_of hr), qr₇ r,
      r₆ r (bprim_of hr), k₅r r hr]
  · rw [rr₈ r (br_prim hr), qrr₇, rr₆ r (br_prim hr), k₅rr r hr]
  · rw [rm₈, qrm₇, rm₆, qrm₅, F₄.2.2.2.1, qrm₃, F₂.2.2.2.1, qrm₁]
  · rw [o₈, qo₇, o₆, qo₅, F₄.2.2.2.2, qo₃, F₂.2.2.2.2, qo₁]
  · rw [← dirOf_one]
    exact ptAns_of_res J P i hP res₁ hvpos hzs (by rw [hv₂]) hvn
  · rw [← dirOf_zero]
    exact ptAns_of_res J P i hP res₀ hvpos hzs (by rw [hv₂]) hvn

end

end FuseAsm

end Chazelle.Core
