module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvRMgA
public import Chazelle.Core.DownPhaseDrvRPlD

/-!
# Down-phase driver (RAM side): merges on a region host, the top of the union

`mgTop`: from the descriptors of two consecutive sub-chains `C₁ = ⟨H.poly Q, 0, m₁⟩` (at
`r219110 + 1`) and `C₂` (at `r219114 + 1`) of the host `H` (handle `r219100`), the top index and
the orientation bit of their union (`L41.whole_topIdx`, `L41.whole_sideBeta`): one height
comparison of the two tops (host points loaded by `NFLoc.hostPt`, compared by the kernel bit
`SweepPrim.kbit`), result in `r219138`, `r219139` (`mgTop_exec`).

Registers (band `bDownDrv`): `219100` `HB`, `219101` the number of points, `219107` the number
of items, `219110` `MD₁`, `219112` `m₁`, `219114` `MD₂`, constants `219140 … 219146` (`0 … 6`),
scratch `219120 … 219139`; band `bLocate`: `NFLoc`'s host registers.
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs BuildRam SignK

@[expose] public section

/-- The tops and bits of the two parts; the host environment of `hostPt`. -/
def mgLoad : Stmt :=
  block [.addN 219126 219110 219144, .loadN 219120 219126,
    .addN 219126 219110 219145, .loadN 219123 219126,
    .addN 219126 219114 219144, .loadN 219127 219126,
    .addN 219121 219112 219127,
    .addN 219126 219114 219145, .loadN 219125 219126,
    .copyN 50060 219100, .copyN 50061 219107, .constN 50067 1, .constN 50068 2, .constN 50069 3,
    .constN 50052 0, .copyN 50087 219101, .copyN 50091 219120]

/-- The two top points. -/
def mgPts : Stmt :=
  .seq NFLoc.hostPt
    (.seq (block [.copyN 219130 50046, .copyN 219131 50047, .copyN 219132 50048,
        .copyN 50091 219121])
      (.seq NFLoc.hostPt (block [.copyN 219133 50046, .copyN 219134 50047, .copyN 219135 50048])))

/-- The top and the bit of the union (the right part's if its top is strictly higher). -/
def mgSel : Stmt :=
  .ifLtN 219136 219141 (block [.copyN 219138 219120, .copyN 219139 219123])
    (block [.copyN 219138 219121, .copyN 219139 219125])

/-- **The top of the union.** -/
def mgTop : Stmt :=
  .seq mgLoad (.seq mgPts (.seq (SweepPrim.kbit 219130 219133 219130 1 219136) mgSel))

/-- The constants of the merge steps. -/
structure MgConst (c : Config) : Prop where
  r40 : c.nreg 219140 = 0
  r41 : c.nreg 219141 = 1
  r42 : c.nreg 219142 = 2
  r43 : c.nreg 219143 = 3
  r44 : c.nreg 219144 = 4
  r45 : c.nreg 219145 = 5
  r46 : c.nreg 219146 = 6

/-- The registers `mgTop` writes. -/
def Btop (r : ℕ) : Bool :=
  decide (219120 ≤ r ∧ r ≤ 219139) || decide (10000 ≤ r ∧ r < 10500) ||
    decide (50040 ≤ r ∧ r ≤ 50099)

section exec

variable {P : Polygon} {W : ℕ}

theorem frameB_up {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B' r = false → B r = false) : FrameB B' c c' :=
  by grind [Chazelle.Core.SignK.FrameB]

theorem pts_getD_of_get? {l : List SymPt} {i : ℕ} {sp : SymPt} (h : l[i]? = some sp) :
    l.getD i (.vtx 0) = sp := by
  simp_all

set_option maxHeartbeats 4000000 in
/-- **The top of the union** of two consecutive sub-chains of the host. -/
theorem mgTop_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) (hK : MgConst c) {H : Host} {HB NP ma : ℕ} {C1 C2 : Chain}
    (h00 : c.nreg 219100 = HB) (h01 : c.nreg 219101 = NP) (h07 : c.nreg 219107 = H.length)
    (h12 : c.nreg 219112 = ma) (hHA : HostAt c.nmem HB H) (hwf : HostWF P.n H)
    (hHok : H.length ≤ 64) (hHB : HB + 3 * H.length + 4 ≤ W) (hNP : NP = (H.pts P.n).length)
    (hd1 : ChainDescAt c.nmem (c.nreg 219110 + 1) (Qof P) H C1)
    (hd2 : ChainDescAt c.nmem (c.nreg 219114 + 1) (Qof P) H C2)
    (hs1 : C1.s = 0) (hm1 : C1.m = ma) (hs2 : C2.s = ma) (hlen : ma + C2.m + 1 ≤ NP)
    (hWa : c.nreg 219110 + 6 ≤ W) (hWb : c.nreg 219114 + 6 ≤ W) :
    ∃ c' k, Exec P W mgTop c c' k ∧ k ≤ 60 * H.length + 330 ∧
      c'.nreg 219138 = (if (C2.top).2 ≤ (C1.top).2 then C1.topIdx else C1.m + C2.topIdx) ∧
      c'.nreg 219139 = (if (C2.top).2 ≤ (C1.top).2 then c.nmem (c.nreg 219110 + 5)
        else c.nmem (c.nreg 219114 + 5)) ∧
      FrameB Btop c c' := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hhw : hostWords P.n = 256 * P.n + 16 := rfl
  have hW3 : P.n + 3 ≤ W := by omega
  have hNW : 2 * NP ≤ W := by
    have h1 := Host.pts_length_le hwf
    have h2 : H.length * P.n ≤ 64 * P.n := Nat.mul_le_mul_right _ hHok
    rw [hNP]; omega
  have hn3 : 3 ≤ P.n := hG.1.1
  have hn0 : 0 < P.n := by omega
  have hLt := NFLoc.hostWF_pts hwf hn0
  set D1 := c.nreg 219110 with hD1
  set D2 := c.nreg 219114 with hD2
  have t1 : c.nmem (D1 + 1 + 3) = C1.topIdx := hd1.2.2.2.2.1
  have t2 : c.nmem (D2 + 1 + 3) = C2.topIdx := hd2.2.2.2.2.1
  have ht1 : C1.topIdx ≤ ma := hm1 ▸ C1.topIdx_le
  have ht2 : C2.topIdx ≤ C2.m := C2.topIdx_le
  -- the loads and the host environment
  obtain ⟨c₁, k₁, e₁, hk₁, v20, v23, v21, v25, E₁, s52, n87, k91, g₁⟩ : ∃ c₁ k₁, Exec P W mgLoad c c₁ k₁ ∧
      k₁ = 17 ∧ c₁.nreg 219120 = C1.topIdx ∧ c₁.nreg 219123 = c.nmem (D1 + 5) ∧
      c₁.nreg 219121 = ma + C2.topIdx ∧ c₁.nreg 219125 = c.nmem (D2 + 5) ∧
      NFLoc.HostEnv W HB H.length c.nmem c₁ ∧ c₁.nreg 50052 = 0 ∧ c₁.nreg 50087 = NP ∧
      c₁.nreg 50091 = C1.topIdx ∧ FrameB Btop c c₁ := by
    have q44 := hK.r44; have q45 := hK.r45
    have hD1W : D1 + 4 ≤ W := by omega
    have t1' : c.nmem (D1 + 4) = C1.topIdx := by rw [show D1 + 4 = D1 + 1 + 3 by ring]; exact t1
    have t2' : c.nmem (D2 + 4) = C2.topIdx := by rw [show D2 + 4 = D2 + 1 + 3 by ring]; exact t2
    obtain ⟨c₁, k₁, e₁, hk₁, v20, v23, v21, v25, v60, v61, v67, v68, v69, s52, n87, k91, m₁⟩ :
        ∃ c₁ k₁, Exec P W mgLoad c c₁ k₁ ∧ k₁ = 17 ∧ c₁.nreg 219120 = C1.topIdx ∧
        c₁.nreg 219123 = c.nmem (D1 + 5) ∧ c₁.nreg 219121 = ma + C2.topIdx ∧
        c₁.nreg 219125 = c.nmem (D2 + 5) ∧ c₁.nreg 50060 = HB ∧ c₁.nreg 50061 = H.length ∧
        c₁.nreg 50067 = 1 ∧ c₁.nreg 50068 = 2 ∧ c₁.nreg 50069 = 3 ∧ c₁.nreg 50052 = 0 ∧
        c₁.nreg 50087 = NP ∧ c₁.nreg 50091 = C1.topIdx ∧ c₁.nmem = c.nmem := by
      unfold mgLoad
      exec_block
      all_goals try (config_simp; (try simp only [← hD1, ← hD2, q44, q45, h12, h00, h07, h01, t1', t2']); omega)
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> config_simp <;>
        (try simp only [← hD1, ← hD2, q44, q45, h12, h00, h07, h01, t1', t2'])
    refine ⟨c₁, k₁, e₁, hk₁, v20, v23, v21, v25, ⟨e₁.wb_right, v60, v61, v67, v68, v69, m₁⟩, s52,
      n87, k91, exec_frameB e₁ (by decide)⟩
  
  -- the first top point
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, E₂, sp₁, hsp₁, in₁⟩ := NFLoc.hostPt_exec (P := P) c₁ E₁ hHA hwf
    (by omega) (by omega) (by omega) s52 (by rw [n87, hNP]) k91 (by omega) (by omega)
  have g₂ : ∀ r, NFLoc.Bhost r = false → c₂.nreg r = c₁.nreg r := f₂.1
  obtain ⟨c₃, k₃, e₃, hk₃, a₃, k91', g₃, m₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN 219130 50046, .copyN 219131 50047, .copyN 219132 50048,
        .copyN 50091 219121]) c₂ c₃ k₃ ∧ k₃ = 4 ∧ SymPtIn c₃ 219130 sp₁ ∧
      c₃.nreg 50091 = ma + C2.topIdx ∧
      (∀ r, ¬ (219130 ≤ r ∧ r ≤ 219132) → r ≠ 50091 → c₃.nreg r = c₂.nreg r) ∧
      c₃.nmem = c₂.nmem := by
    have hw₂ := e₂.wb_right
    have q21 : c₂.nreg 219121 = ma + C2.topIdx := by rw [g₂ _ (by decide), v21]
    exec_block
    refine ⟨rfl, NFLoc.symPtIn_copy in₁ (by config_simp) (by config_simp) (by config_simp),
      by config_simp; exact q21, fun r h1 h2 => ?_, rfl⟩
    simp only [Machine.upd_apply]
    split_ifs <;> first | rfl | omega
  have E₃ : NFLoc.HostEnv W HB H.length c.nmem c₃ :=
    ⟨e₃.wb_right, by rw [g₃ _ (by omega) (by omega), E₂.h60], by rw [g₃ _ (by omega) (by omega), E₂.h61],
      by rw [g₃ _ (by omega) (by omega), E₂.h67], by rw [g₃ _ (by omega) (by omega), E₂.h68],
      by rw [g₃ _ (by omega) (by omega), E₂.h69], by rw [m₃, E₂.mem]⟩
  have s52' : c₃.nreg 50052 = 0 := by rw [g₃ _ (by omega) (by omega), g₂ _ (by decide), s52]
  have n87' : c₃.nreg 50087 = NP := by rw [g₃ _ (by omega) (by omega), g₂ _ (by decide), n87]
  -- the second top point
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, E₄, sp₂, hsp₂, in₂⟩ := NFLoc.hostPt_exec (P := P) c₃ E₃ hHA hwf
    (by omega) (by omega) (by omega) s52' (by rw [n87', hNP]) k91' (by omega) (by omega)
  have g₄ : ∀ r, NFLoc.Bhost r = false → c₄.nreg r = c₃.nreg r := f₄.1
  have a₄ : SymPtIn c₄ 219130 sp₁ := NFLoc.symPtIn_copy a₃ (g₄ _ (by decide)) (g₄ _ (by decide))
    (g₄ _ (by decide))
  obtain ⟨c₅, k₅, e₅, hk₅, a₅, b₅, g₅, m₅⟩ : ∃ c₅ k₅, Exec P W
      (block [.copyN 219133 50046, .copyN 219134 50047, .copyN 219135 50048]) c₄ c₅ k₅ ∧
      k₅ = 3 ∧ SymPtIn c₅ 219130 sp₁ ∧ SymPtIn c₅ 219133 sp₂ ∧
      (∀ r, ¬ (219133 ≤ r ∧ r ≤ 219135) → c₅.nreg r = c₄.nreg r) ∧ c₅.nmem = c₄.nmem := by
    have hw₄ := e₄.wb_right
    exec_block
    refine ⟨rfl, NFLoc.symPtIn_copy a₄ (by config_simp) (by config_simp) (by config_simp),
      NFLoc.symPtIn_copy in₂ (by config_simp) (by config_simp) (by config_simp), fun r h1 => ?_, rfl⟩
    simp only [Machine.upd_apply]
    split_ifs <;> first | rfl | omega
  -- the comparison
  have l₁ : sp₁.Lt P.n := hLt _ (List.mem_of_getElem? hsp₁)
  have l₂ : sp₂.Lt P.n := hLt _ (List.mem_of_getElem? hsp₂)
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, b6le, b6⟩ := SweepPrim.kbit_exec (P := P) hG hW3 c₅ e₅.wb_right
    (a := 219130) (b := 219133) (d := 219130) (op := 1) (dst := 219136) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) l₁ l₂ l₁ a₅ b₅ a₅
  -- the two tops are the loaded points
  have top1 : C1.top = sp₁.eval (Qof P) := by
    unfold Chain.top
    rw [DownMath.chain_vertex_host hd1.2.1, hs1, hQn, pts_getD_of_get? hsp₁]
  have top2 : C2.top = sp₂.eval (Qof P) := by
    have h2 := pts_getD_of_get? hsp₂
    rw [Nat.zero_add] at h2
    unfold Chain.top
    rw [DownMath.chain_vertex_host hd2.2.1, hs2, hQn, h2]
  have hbit : c₆.nreg 219136 = 1 ↔ ¬ (C2.top).2 ≤ (C1.top).2 := by
    rw [b6, top1, top2]; simp only [SignTest, not_le]
  -- the selection
  have q20 : c₆.nreg 219120 = C1.topIdx := by
    rw [f₆.1 _ (by decide), g₅ _ (by omega), g₄ _ (by decide), g₃ _ (by omega) (by omega),
      g₂ _ (by decide), v20]
  have q21 : c₆.nreg 219121 = ma + C2.topIdx := by
    rw [f₆.1 _ (by decide), g₅ _ (by omega), g₄ _ (by decide), g₃ _ (by omega) (by omega),
      g₂ _ (by decide), v21]
  have q23 : c₆.nreg 219123 = c.nmem (D1 + 5) := by
    rw [f₆.1 _ (by decide), g₅ _ (by omega), g₄ _ (by decide), g₃ _ (by omega) (by omega),
      g₂ _ (by decide), v23]
  have q25 : c₆.nreg 219125 = c.nmem (D2 + 5) := by
    rw [f₆.1 _ (by decide), g₅ _ (by omega), g₄ _ (by decide), g₃ _ (by omega) (by omega),
      g₂ _ (by decide), v25]
  have q41 : c₆.nreg 219141 = 1 := by
    rw [f₆.1 _ (by decide), g₅ _ (by omega), g₄ _ (by decide), g₃ _ (by omega) (by omega),
      g₂ _ (by decide), g₁.1 _ (by decide), hK.r41]
  have hw₆ := e₆.wb_right
  obtain ⟨c₇, k₇, e₇, hk₇, o38, o39, f₇⟩ : ∃ c₇ k₇, Exec P W mgSel c₆ c₇ k₇ ∧ k₇ ≤ 4 ∧
      c₇.nreg 219138 = (if (C2.top).2 ≤ (C1.top).2 then C1.topIdx else C1.m + C2.topIdx) ∧
      c₇.nreg 219139 = (if (C2.top).2 ≤ (C1.top).2 then c.nmem (D1 + 5) else c.nmem (D2 + 5)) ∧
      FrameB Btop c₆ c₇ := by
    by_cases hc : (C2.top).2 ≤ (C1.top).2
    · have h0 : c₆.nreg 219136 < c₆.nreg 219141 := by
        rw [q41]; have : c₆.nreg 219136 ≠ 1 := fun h => hbit.1 h hc; omega
      obtain ⟨c₇, k₇, e₇, hk₇, w38, w39⟩ : ∃ c₇ k₇, Exec P W
          (block [.copyN 219138 219120, .copyN 219139 219123]) c₆ c₇ k₇ ∧ k₇ = 2 ∧
          c₇.nreg 219138 = C1.topIdx ∧ c₇.nreg 219139 = c.nmem (D1 + 5) := by
        exec_block
        refine ⟨rfl, ?_, ?_⟩ <;> config_simp <;> (try simp only [q20, q23])
      have ex7 : Exec P W mgSel c₆ c₇ (k₇ + 1) := .ifLtN_true h0 e₇
      refine ⟨c₇, k₇ + 1, ex7, by omega, by rw [w38, ite_eq_left hc],
        by rw [w39, ite_eq_left hc], exec_frameB ex7 (by decide)⟩
    · have h0 : ¬ c₆.nreg 219136 < c₆.nreg 219141 := by
        rw [q41]; have := hbit.2 hc; omega
      obtain ⟨c₇, k₇, e₇, hk₇, w38, w39⟩ : ∃ c₇ k₇, Exec P W
          (block [.copyN 219138 219121, .copyN 219139 219125]) c₆ c₇ k₇ ∧ k₇ = 2 ∧
          c₇.nreg 219138 = ma + C2.topIdx ∧ c₇.nreg 219139 = c.nmem (D2 + 5) := by
        exec_block
        refine ⟨rfl, ?_, ?_⟩ <;> config_simp <;> (try simp only [q21, q25])
      have ex7 : Exec P W mgSel c₆ c₇ (k₇ + 2) := .ifLtN_false h0 e₇
      refine ⟨c₇, k₇ + 2, ex7, by omega, by rw [w38, ite_eq_right hc, hm1],
        by rw [w39, ite_eq_right hc], exec_frameB ex7 (by decide)⟩
  refine ⟨c₇, k₁ + (k₂ + (k₃ + (k₄ + k₅)) + (k₆ + k₇)), ?_, ?_, o38, o39, ?_⟩
  · exact .seq e₁ (.seq (.seq e₂ (.seq e₃ (.seq e₄ e₅))) (.seq e₆ e₇))
  · omega
  · have F3 : FrameB Btop c₂ c₃ := exec_frameB e₃ (by decide)
    have F5 : FrameB Btop c₄ c₅ := exec_frameB e₅ (by decide)
    have hb : ∀ r, Btop r = false → NFLoc.Bhost r = false := fun r hr => by
      simp only [Btop, NFLoc.Bhost, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega
    have hk : ∀ r, Btop r = false → SweepPrim.Bkb 219136 r = false := fun r hr => by
      simp only [Btop, SweepPrim.Bkb, WalkKey.Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        beq_eq_false_iff_ne, ne_eq] at hr ⊢; omega
    exact g₁.trans ((frameB_up f₂ hb).trans (F3.trans ((frameB_up f₄ hb).trans
      (F5.trans ((frameB_up f₆ hk).trans f₇)))))

end exec

end

end DrvR

end Chazelle.Core
