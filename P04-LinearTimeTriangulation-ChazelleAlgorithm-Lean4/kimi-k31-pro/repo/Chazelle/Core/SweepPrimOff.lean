module

public import Chazelle.Core.SweepPrimJun
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics
public import Chazelle.ConfigTactics

/-!
# Sweep RAM primitives (WP-D2), part 13: `offCmp`

design-merge-v2 §9.6 item 6: the order of the offsets `off n g (key x)` of two proper positions
`x`, `y` of `chainModel C` from a walk vertex `g`.  The offset of a proper position is
`dOf n g x.edge + param x` (`off_key'`), so the order is lexicographic in the rotated edge index
and the parameter (`off_lt_iff`); on one non-horizontal edge the parameters compare like the
heights, in the direction of the edge (`Model.key_lt_key_iff_of_same_edge`), which is one
direction code (`dirAt`) and two sign-kernel height tests.  The height of a position is that of
vertex `h` of `Q` for the code `h + 1`, and that of the start vertex of its edge (a tour vertex)
for the code `0`.
-/

namespace Chazelle.Core

namespace SweepPrim

open Machine Machine.Stmt Programs SignK WalkKey NFLoc WalkEmbed

@[expose] public section

/-! ## Mathematics -/

/-- **The offset of a proper position.** -/
theorem off_pos (M : Model) (Q : Polygon) {g : ℕ} (hg : g < M.W.n) {x : WPos}
    (hx : x.edge < M.W.n) (h0 : 0 ≤ M.param Q x) (h1 : M.param Q x < 1) :
    off M.W.n g (M.key Q x) = dOf M.W.n g x.edge + M.param Q x :=
  off_key' hg hx h0 h1

theorem dOf_inj {n g p q : ℕ} (hg : g < n) (hp : p < n) (hq : q < n) (h : dOf n g p = dOf n g q) :
    p = q := by
  rw [← add_dOf hg hp, ← add_dOf hg hq, h]

/-- **The order of the offsets** of two proper positions. -/
theorem off_lt_iff (M : Model) (Q : Polygon) {g : ℕ} (hg : g < M.W.n) {x y : WPos}
    (hx : x.edge < M.W.n) (hx0 : 0 ≤ M.param Q x) (hx1 : M.param Q x < 1)
    (hy : y.edge < M.W.n) (hy0 : 0 ≤ M.param Q y) (hy1 : M.param Q y < 1) :
    off M.W.n g (M.key Q x) < off M.W.n g (M.key Q y) ↔
      dOf M.W.n g x.edge < dOf M.W.n g y.edge ∨
        (x.edge = y.edge ∧ M.param Q x < M.param Q y) := by
  rw [off_pos M Q hg hx hx0 hx1, off_pos M Q hg hy hy0 hy1]
  constructor
  · intro h
    rcases lt_trichotomy (dOf M.W.n g x.edge) (dOf M.W.n g y.edge) with h' | h' | h'
    · exact Or.inl h'
    · refine Or.inr ⟨dOf_inj hg hx hy h', ?_⟩
      rwli [h'] at h
    · exfalso
      have : (dOf M.W.n g y.edge : ℝ) + 1 ≤ dOf M.W.n g x.edge := by exact_mod_cast h'
      linarith
  · rintro (h | ⟨h, h'⟩)
    · have : (dOf M.W.n g x.edge : ℝ) + 1 ≤ dOf M.W.n g y.edge := by exact_mod_cast h
      linarith
    · rwli [h]

/-- The parameters of two positions on one edge compare like their keys. -/
theorem param_lt_iff_same_edge (M : Model) (Q : Polygon) {x y : WPos} (he : x.edge = y.edge) :
    M.param Q x < M.param Q y ↔
      (dirCode M x.edge = 1 ∧ M.hgtY Q x < M.hgtY Q y) ∨
        (dirCode M x.edge = 2 ∧ M.hgtY Q y < M.hgtY Q x) := by
  by_cases hh : (M.wa x.edge).2 = (M.wb x.edge).2
  · have hy : (M.wa y.edge).2 = (M.wb y.edge).2 := he ▸ hh
    rw [Model.param_horizontal hh, Model.param_horizontal hy]
    have : dirCode M x.edge = 0 := by urs dirCode [hh]
    rws [this]
  · have hk := Model.key_lt_key_iff_of_same_edge (M := M) (Q := Q) he hh
    unfold Model.key at hk
    rw [he, add_lt_add_iff_left] at hk
    rw [← he] at hk
    rw [hk]
    unfold dirCode
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨by rw [ite_eq_left h1], h2⟩
      · exact Or.inr ⟨by rw [ite_eq_right (not_lt.2 h1.le), ite_eq_left h1], h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left
        refine ⟨?_, h2⟩
        by_contra hc
        rw [ite_eq_right hc] at h1
        split_ifs at h1; omega
      · right
        have hn : ¬ (M.wa x.edge).2 < (M.wb x.edge).2 := fun h => by rwo [ite_eq_left h] at h1
        rw [ite_eq_right hn] at h1
        refine ⟨?_, h2⟩
        by_contra hc
        rw [ite_eq_right hc] at h1
        omega


/-! ## The machine -/

/-- The height of the position `(50201, 50202)` as a symbolic point in `50130`: the tour vertex
`e - 6` for the code `0`, the vertex `h - 1` of `Q` otherwise. -/
def yLoadX : Stmt :=
  .ifLtN 50202 50032 (.seq (.instr (.subN 50120 50201 50081)) (tvLoad 50130))
    (block [.constN 50130 0, .subN 50131 50202 50032])

theorem yLoadX_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {e h : ℕ} (he : c.nreg 50201 = e) (hh : c.nreg 50202 = h)
    (h0 : h = 0 → 6 ≤ e ∧ e < 2 * C.m + 7) (hhn : h ≤ P.n) :
    ∃ c' k, Exec P W yLoadX c c' k ∧ k ≤ 27 * H.length + 45 ∧ CEnv P W H C c' ∧
      (∀ r, (50200 ≤ r ∨ (10500 ≤ r ∧ r < 50000)) → c'.nreg r = c.nreg r) ∧
      (∀ r, 50130 ≤ r → r < 50139 → (r < 50130 ∨ 50132 < r) → c'.nreg r = c.nreg r) ∧
      ∃ s : SymPt, SymPtIn c' 50130 s ∧ s.Lt P.n ∧
        (s.eval (Qof P)).2 = (chainModel C).hgtY (Qof P) ⟨e, h⟩ := by
  have hw := hE.wb
  unfold yLoadX
  by_cases hc : h < 1
  · have h00 : h = 0 := by omega
    obtain ⟨h6, hen⟩ := h0 h00
    have e₁ := Exec.subN (P := P) hw 50120 50201 50081
    have hE₁ : CEnv P W H C _ := hE.step e₁ (by decide)
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp, -⟩ := tvLoad_exec _ hE₁ (i := e - 6)
      (by simp [he, hE.r81]) (by omega) (dst := 50130) (by norm_num)
    refine ⟨c₂, _, .ifLtN_true (by rwx [hh, hE.r32]) (e₁.seq e₂), by omega, hE₂,
      fun r hr => ?_, fun r h1 h2 h3 => ?_, sp, isp, lsp, ?_⟩
    · rw [f₂.1 r (by first | (sio [Btv, Btvi, Bhost]))]
      simp; rw [upd_other _ _ _ (by omega)]
    · rw [f₂.1 r (by first | (sio [Btv, Btvi, Bhost]))]
      simp; rw [upd_other _ _ _ (by omega)]
    · rwr [vsp, h00, show e - 6 + 6 = e by omega]
  · refine spec_ifLtN_false (by rwx [hh, hE.r32]) ?_
    exec_block
    all_goals try omega
    refine ⟨by omega, ?_, fun r hr => ?_, fun r h1 h2 h3 => ?_, .vtx (h - 1), ⟨by config_simp,
      ?_⟩, by show h - 1 < P.n; omega, ?_⟩
    · exact hE.keep ‹_› rfl (fun r hr => by
        simp [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        simp [upd]; split_ifs <;> first | rfl | omega)
    · simp [upd]; split_ifs <;> first | rfl | omega
    · simp [upd]; split_ifs <;> first | rfl | omega
    · config_simp; rw [hh, hE.r32]
    · obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      rfl

/-- The height of the position `(50203, 50204)` as a symbolic point in `50136`: the tour vertex
`e - 6` for the code `0`, the vertex `h - 1` of `Q` otherwise. -/
def yLoadY : Stmt :=
  .ifLtN 50204 50032 (.seq (.instr (.subN 50120 50203 50081)) (tvLoad 50136))
    (block [.constN 50136 0, .subN 50137 50204 50032])

theorem yLoadY_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {e h : ℕ} (he : c.nreg 50203 = e) (hh : c.nreg 50204 = h)
    (h0 : h = 0 → 6 ≤ e ∧ e < 2 * C.m + 7) (hhn : h ≤ P.n) :
    ∃ c' k, Exec P W yLoadY c c' k ∧ k ≤ 27 * H.length + 45 ∧ CEnv P W H C c' ∧
      (∀ r, (50200 ≤ r ∨ (10500 ≤ r ∧ r < 50000)) → c'.nreg r = c.nreg r) ∧
      (∀ r, 50130 ≤ r → r < 50139 → (r < 50136 ∨ 50138 < r) → c'.nreg r = c.nreg r) ∧
      ∃ s : SymPt, SymPtIn c' 50136 s ∧ s.Lt P.n ∧
        (s.eval (Qof P)).2 = (chainModel C).hgtY (Qof P) ⟨e, h⟩ := by
  have hw := hE.wb
  unfold yLoadY
  by_cases hc : h < 1
  · have h00 : h = 0 := by omega
    obtain ⟨h6, hen⟩ := h0 h00
    have e₁ := Exec.subN (P := P) hw 50120 50203 50081
    have hE₁ : CEnv P W H C _ := hE.step e₁ (by decide)
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp, -⟩ := tvLoad_exec _ hE₁ (i := e - 6)
      (by simp [he, hE.r81]) (by omega) (dst := 50136) (by norm_num)
    refine ⟨c₂, _, .ifLtN_true (by rwx [hh, hE.r32]) (e₁.seq e₂), by omega, hE₂,
      fun r hr => ?_, fun r h1 h2 h3 => ?_, sp, isp, lsp, ?_⟩
    · rw [f₂.1 r (by first | (sio [Btv, Btvi, Bhost]))]
      simp; rw [upd_other _ _ _ (by omega)]
    · rw [f₂.1 r (by first | (sio [Btv, Btvi, Bhost]))]
      simp; rw [upd_other _ _ _ (by omega)]
    · rwr [vsp, h00, show e - 6 + 6 = e by omega]
  · refine spec_ifLtN_false (by rwx [hh, hE.r32]) ?_
    exec_block
    all_goals try omega
    refine ⟨by omega, ?_, fun r hr => ?_, fun r h1 h2 h3 => ?_, .vtx (h - 1), ⟨by config_simp,
      ?_⟩, by show h - 1 < P.n; omega, ?_⟩
    · exact hE.keep ‹_› rfl (fun r hr => by
        simp [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        simp [upd]; split_ifs <;> first | rfl | omega)
    · simp [upd]; split_ifs <;> first | rfl | omega
    · simp [upd]; split_ifs <;> first | rfl | omega
    · config_simp; rw [hh, hE.r32]
    · obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      rfl


/-- Output two bits. -/
def offOut (a b : ℕ) : Stmt := block [.constN 50210 a, .constN 50211 b]

/-- The height comparison on one walk edge: the two height bits, swapped for a descending edge. -/
def offHgt : Stmt :=
  .seq yLoadX (.seq yLoadY (.seq (kbit 50130 50136 50130 1 50150)
    (.seq (kbit 50136 50130 50136 1 50151)
      (.ifLtN 50032 10502 (block [.copyN 50210 50151, .copyN 50211 50150])
        (block [.copyN 50210 50150, .copyN 50211 50151])))))

/-- Both positions on one walk edge: its direction code, then `offHgt` unless horizontal. -/
def offSame : Stmt :=
  .seq (.instr (.copyN 50002 50201)) (.seq dirAt (.ifLtN 10502 50032 (offOut 0 0) offHgt))

/-- The rotated edge indices `50142`, `50144` (with `50143 = n - g`). -/
def offHead : Stmt :=
  .seq (block [.addN 50140 50053 50053, .addN 50140 50140 50081, .addN 50140 50140 50032,
      .subN 50143 50140 50205])
    (.seq (candR 50201 50205 50143 50142) (candR 50203 50205 50143 50144))

/-- **`offCmp`** (positions `(50201, 50202)`, `(50203, 50204)`, base vertex `50205`): the bits of
`off x < off y` (`50210`) and `off y < off x` (`50211`). -/
def offCore : Stmt :=
  .seq offHead (.ifLtN 50142 50144 (offOut 1 0) (.ifLtN 50144 50142 (offOut 0 1) offSame))

/-- **The primitive `offCmp`.** -/
def offCmp : Stmt := .seq pHead offCore

theorem wr_offCmp : wr Bprim offCmp = true := by decide

/-- The machine offset of a walk vertex. -/
theorem dOf_eq {n g p : ℕ} (hg : g < n) (hp : p < n) :
    (if p < g then p + (n - g) else p - g) = dOf n g p := by
  unfold dOf
  split_ifs with h
  · rwo [Nat.mod_eq_of_lt (by omega)]
  · rw [show p + n - g = (p - g) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- The input condition of `offCmp`: two proper positions of the walk and a walk vertex; a
position with height code `0` is a vertex of the tour or of the up-slit edge (`6 ≤ e`); the walk
indices within the word bound. -/
def OffIn (P : Polygon) (W : ℕ) (C : Chain) (c : Config) : Prop :=
  c.nreg 50201 < (chainModel C).W.n ∧ c.nreg 50203 < (chainModel C).W.n ∧
    c.nreg 50205 < (chainModel C).W.n ∧
    ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg 50201, c.nreg 50202⟩ ∧
    ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg 50203, c.nreg 50204⟩ ∧
    (c.nreg 50202 = 0 → 6 ≤ c.nreg 50201) ∧ (c.nreg 50204 = 0 → 6 ≤ c.nreg 50203) ∧
    2 * C.m + 7 ≤ W

/-- The output condition of `offCmp`. -/
def OffOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  let M := chainModel C
  let ox := off M.W.n (c.nreg 50205) (M.key (Qof P) ⟨c.nreg 50201, c.nreg 50202⟩)
  let oy := off M.W.n (c.nreg 50205) (M.key (Qof P) ⟨c.nreg 50203, c.nreg 50204⟩)
  BitIs c' 50210 (ox < oy) ∧ BitIs c' 50211 (oy < ox)

theorem offOut_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {a b : ℕ}
    (ha : a ≤ 1) (hb : b ≤ 1) (hW : 1 ≤ W) {p q : Prop} (hp : a = 1 ↔ p) (hq : b = 1 ↔ q) :
    ∃ c' k, Exec P W (offOut a b) c c' k ∧ k = 2 ∧ BitIs c' 50210 p ∧ BitIs c' 50211 q := by
  unfold offOut
  exec_block
  all_goals try omega
  exact ⟨rfl, ⟨by cso, by config_simp; exact hp⟩,
    ⟨by cso, by config_simp; exact hq⟩⟩

/-- **Contract of `offCmp`** (at most `11000` steps). -/
theorem offCmp_meets : Meets offCmp primBands (PrimPre OffIn) (PrimPost OffOut)
    (fun _ _ => 11000) := by
  refine prim_meets (K := 10200) (fun _ => id) wr_offCmp ?_
  intro P W H C c₀ c _hC hE ⟨hx, hy, hg, ⟨hx0, hx1, hxn⟩, ⟨hy0, hy1, hyn⟩, hx6, hy6, hWm⟩ hinp
  unfold OffOut
  dsimp
  have i01 := hinp 50201 (by norm_num) (by norm_num)
  have i02 := hinp 50202 (by norm_num) (by norm_num)
  have i03 := hinp 50203 (by norm_num) (by norm_num)
  have i04 := hinp 50204 (by norm_num) (by norm_num)
  have i05 := hinp 50205 (by norm_num) (by norm_num)
  set px := c₀.nreg 50201
  set qx := c₀.nreg 50202
  set py := c₀.nreg 50203
  set qy := c₀.nreg 50204
  set g := c₀.nreg 50205
  set M := chainModel C with hM
  have hn : M.W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hlen := hE.hlen
  have hW := hE.hW
  set x : WPos := ⟨px, qx⟩
  set y : WPos := ⟨py, qy⟩
  have hlt := off_lt_iff M (Qof P) hg (x := x) (y := y) hx hx0 hx1 hy hy0 hy1
  have hgt := off_lt_iff M (Qof P) hg (x := y) (y := x) hy hy0 hy1 hx hx0 hx1
  change _ ↔ dOf M.W.n g px < dOf M.W.n g py ∨ (px = py ∧ _) at hlt
  change _ ↔ dOf M.W.n g py < dOf M.W.n g px ∨ (py = px ∧ _) at hgt
  -- the rotated edge indices
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.addN 50140 50053 50053,
      .addN 50140 50140 50081, .addN 50140 50140 50032, .subN 50143 50140 50205]) c c₁ k₁ ∧
      k₁ = 4 ∧ (c₁.nreg 50140 = M.W.n ∧ c₁.nreg 50143 = M.W.n - g ∧
        ∀ r, r ≠ 50140 → r ≠ 50143 → c₁.nreg r = c.nreg r) := by
    have hw := hE.wb
    exec_block
    all_goals try (config_simp; rwo [hE.r53])
    all_goals try (config_simp; rwo [hE.r53, hE.r81])
    all_goals try (config_simp; rwo [hE.r53, hE.r81, hE.r32])
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => by simp [h1, h2]⟩
    · config_simp; rwring [hE.r53, hE.r81, hE.r32, hn]
    · config_simp; rw [hE.r53, hE.r81, hE.r32, hn, i05]; ring_nf
  obtain ⟨q40, q43, r₁⟩ := q
  have hE₁ : CEnv P W H C c₁ := hE.keep e₁.wb_right
    (exec_frameB e₁ (B := fun r => r == 50140 || r == 50143) (by decide)).2.2.1
    (fun r hr => r₁ r (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide)))
  obtain ⟨c₂, k₂, e₂, hk₂, v42, r₂⟩ := candR_exec (P := P) (j := 50201) (s := 50205) (d := 50143)
    (dst := 50142) c₁ e₁.wb_right (by
      rw [r₁ _ (by decide) (by decide), r₁ _ (by decide) (by decide), q43, i01, i05]
      intro h; omega)
  obtain ⟨c₃, k₃, e₃, hk₃, v44, r₃⟩ := candR_exec (P := P) (j := 50203) (s := 50205) (d := 50143)
    (dst := 50144) c₂ e₂.wb_right (by
      rw [r₂ _ (by decide), r₂ _ (by decide), r₂ _ (by decide), r₁ _ (by decide) (by decide),
        r₁ _ (by decide) (by decide), q43, i03, i05]
      intro h; omega)
  have d42 : c₃.nreg 50142 = dOf M.W.n g px := by
    rw [r₃ _ (by decide), v42, r₁ _ (by decide) (by decide), r₁ _ (by decide) (by decide), q43,
      i01, i05, dOf_eq hg hx]
  have d44 : c₃.nreg 50144 = dOf M.W.n g py := by
    rw [v44, r₂ _ (by decide), r₂ _ (by decide), r₂ _ (by decide), r₁ _ (by decide) (by decide),
      r₁ _ (by decide) (by decide), q43, i03, i05, dOf_eq hg hy]
  have hE₃ : CEnv P W H C c₃ := hE₁.keep e₃.wb_right
    (by rw [(exec_frameB e₃ (B := fun r => r == 50144) (by simp [candR, wr, wrOK])).2.2.1,
      (exec_frameB e₂ (B := fun r => r == 50142) (by simp [candR, wr, wrOK])).2.2.1])
    (fun r hr => by rw [r₃ r (ne_of_mem_of_not_mem hr (by decide)),
      r₂ r (ne_of_mem_of_not_mem hr (by decide))])
  have g3 : ∀ r, 50200 ≤ r → r < 50210 → c₃.nreg r = c₀.nreg r := fun r h1 h2 => by
    rw [r₃ r (by omega), r₂ r (by omega), r₁ r (by omega) (by omega), hinp r h1 h2]
  have eH : Exec P W offHead c c₃ (k₁ + (k₂ + k₃)) := e₁.seq (e₂.seq e₃)
  by_cases hd1 : c₃.nreg 50142 < c₃.nreg 50144
  · rw [d42, d44] at hd1
    obtain ⟨c₄, k₄, e₄, hk₄, b0, b1⟩ := offOut_exec (P := P) c₃ e₃.wb_right (a := 1) (b := 0)
      le_rfl (by omega) (by omega) (p := off M.W.n g (M.key (Qof P) x) < off M.W.n g
        (M.key (Qof P) y)) (q := off M.W.n g (M.key (Qof P) y) < off M.W.n g (M.key (Qof P) x))
      (by rw [hlt]; simp [hd1]) (by
        rw [hgt]; constructor
        · intro h; omega
        · rintro (h | ⟨h, -⟩)
          · omega
          · rwo [h] at hd1)
    exact ⟨c₄, _, .seq eH (.ifLtN_true (by rwx [d42, d44]) e₄),
      by omega, b0, b1⟩
  have t1  := hd1
  rw [d42, d44] at hd1
  by_cases hd2 : c₃.nreg 50144 < c₃.nreg 50142
  · rw [d42, d44] at hd2
    obtain ⟨c₄, k₄, e₄, hk₄, b0, b1⟩ := offOut_exec (P := P) c₃ e₃.wb_right (a := 0) (b := 1)
      (by omega) le_rfl (by omega) (p := off M.W.n g (M.key (Qof P) x) < off M.W.n g
        (M.key (Qof P) y)) (q := off M.W.n g (M.key (Qof P) y) < off M.W.n g (M.key (Qof P) x))
      (by
        rw [hlt]; constructor
        · intro h; omega
        · rintro (h | ⟨h, -⟩)
          · omega
          · rwo [h] at hd2)
      (by rw [hgt]; simp [hd2])
    exact ⟨c₄, _, .seq eH (.ifLtN_false t1
      (.ifLtN_true (by rwx [d42, d44]) e₄)), by omega, b0, b1⟩
  have t2  := hd2
  rw [d42, d44] at hd2
  -- the same walk edge
  have hpq : px = py := dOf_inj hg hx hy (by omega)
  have hlt' : off M.W.n g (M.key (Qof P) x) < off M.W.n g (M.key (Qof P) y) ↔
      M.param (Qof P) x < M.param (Qof P) y := by
    rw [hlt]; constructor
    · rintro (h | ⟨-, h⟩)
      · omega
      · exact h
    · intro h; exact Or.inr ⟨hpq, h⟩
  have hgt' : off M.W.n g (M.key (Qof P) y) < off M.W.n g (M.key (Qof P) x) ↔
      M.param (Qof P) y < M.param (Qof P) x := by
    rw [hgt]; constructor
    · rintro (h | ⟨-, h⟩)
      · omega
      · exact h
    · intro h; exact Or.inr ⟨hpq.symm, h⟩
  have hpx := param_lt_iff_same_edge M (Qof P) (x := x) (y := y) hpq
  have hpy := param_lt_iff_same_edge M (Qof P) (x := y) (y := x) hpq.symm
  rw [hlt', hpx]
  rw [hgt', hpy]
  simp [x, y] at hpq ⊢
  rw [← hpq]
  -- the direction of the edge
  have e₄ := Exec.copyN (P := P) e₃.wb_right 50002 50201
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg 50002 (c₃.nreg 50201) } with hc₄
  have hE₄ : CEnv P W H C c₄ := hE₃.frame (exec_frameB e₄ (B := fun r => r == 50002)
    (by decide)) e₄.wb_right (by decide)
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, hE₅, d₅⟩ := dirAt_exec c₄ hE₄ (e := px)
    (by show upd c₃.nreg 50002 (c₃.nreg 50201) 50002 = px
        rw [upd_same]; exact g3 50201 (by norm_num) (by norm_num)) (by omega)
  rw [← hM] at d₅
  have g5 : ∀ r, 50200 ≤ r → r < 50210 → c₅.nreg r = c₀.nreg r := fun r h1 h2 => by
    rw [f₅.1 r (by sio only [Bdir, Bool.or_eq_false_iff, decide_eq_false_iff_not]), hc₄]
    simp
    rw [upd_other _ _ _ (by omega), g3 r h1 h2]
  have hdl := dirCode_le_two M px
  by_cases hd0 : c₅.nreg 10502 < c₅.nreg 50032
  · rw [hE₅.r32, d₅] at hd0
    have h0 : dirCode M px = 0 := by omega
    obtain ⟨c₆, k₆, e₆, hk₆, b0, b1⟩ := offOut_exec (P := P) c₅ e₅.wb_right (a := 0) (b := 0)
      (by omega) (by omega) (by omega)
      (p := (dirCode M px = 1 ∧ M.hgtY (Qof P) ⟨px, qx⟩ < M.hgtY (Qof P) ⟨px, qy⟩) ∨
        (dirCode M px = 2 ∧ M.hgtY (Qof P) ⟨px, qy⟩ < M.hgtY (Qof P) ⟨px, qx⟩))
      (q := (dirCode M px = 1 ∧ M.hgtY (Qof P) ⟨px, qy⟩ < M.hgtY (Qof P) ⟨px, qx⟩) ∨
        (dirCode M px = 2 ∧ M.hgtY (Qof P) ⟨px, qx⟩ < M.hgtY (Qof P) ⟨px, qy⟩))
      (by rws [h0]) (by rws [h0])
    exact ⟨c₆, _, .seq eH (.ifLtN_false t1 (.ifLtN_false t2
      (.seq e₄ (.seq e₅ (.ifLtN_true (by rwo [hE₅.r32, d₅]) e₆))))), by omega, b0, b1⟩
  have t3  := hd0
  rw [hE₅.r32, d₅] at hd0
  -- the heights
  obtain ⟨c₆, k₆, e₆, hk₆, hE₆, f6a, f6b, sx, ix, lx, vx⟩ := yLoadX_exec c₅ hE₅
    (g5 50201 (by norm_num) (by norm_num)) (g5 50202 (by norm_num) (by norm_num))
    (fun h => ⟨hx6 h, by omega⟩) hxn
  obtain ⟨c₇, k₇, e₇, hk₇, hE₇, f7a, f7b, sy, iy, ly, vy⟩ := yLoadY_exec c₆ hE₆
    (e := px) (h := qy)
    ((f6a _ (by omega)).trans ((g5 50203 (by norm_num) (by norm_num)).trans hpq.symm))
    ((f6a _ (by omega)).trans (g5 50204 (by norm_num) (by norm_num)))
    (fun h => ⟨by rw [hpq]; exact hy6 h, by omega⟩) hyn
  have ix₇ : SymPtIn c₇ 50130 sx := symPtIn_of_eq ix fun j h1 h2 => f7b j (by omega) (by omega)
    (by omega)
  obtain ⟨c₈, k₈, e₈, hk₈, f₈, b₈, t₈⟩ := kbit_exec (op := 1) (dst := 50150) hE.hG hW c₇
    e₇.wb_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) lx ly lx
    ix₇ iy ix₇
  have ix₈ := symPtIn_keep ix₇ f₈ (by intro j h1 h2; interval_cases j <;> decide)
  have iy₈ := symPtIn_keep iy f₈ (by intro j h1 h2; interval_cases j <;> decide)
  obtain ⟨c₉, k₉, e₉, hk₉, f₉, b₉, t₉⟩ := kbit_exec (op := 1) (dst := 50151) hE.hG hW c₈
    e₈.wb_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ly lx ly
    iy₈ ix₈ iy₈
  have p10502 : c₉.nreg 10502 = dirCode M px := by
    rw [f₉.1 _ (by decide), f₈.1 _ (by decide), f7a _ (by omega), f6a _ (by omega), d₅]
  have p32 : c₉.nreg 50032 = 1 := (hE₇.frame f₈ e₈.wb_right (by decide) |>.frame f₉
    e₉.wb_right (by decide)).r32
  have B50 : BitIs c₉ 50150 (M.hgtY (Qof P) ⟨px, qx⟩ < M.hgtY (Qof P) ⟨px, qy⟩) := by
    have := BitIs.keep ⟨b₈, t₈⟩ f₉ (by decide)
    simp [SignTest] at this
    rw [vx, vy] at this; exact this
  have B51 : BitIs c₉ 50151 (M.hgtY (Qof P) ⟨px, qy⟩ < M.hgtY (Qof P) ⟨px, qx⟩) := by
    have : BitIs c₉ 50151 _ := ⟨b₉, t₉⟩
    simp [SignTest] at this
    rw [vx, vy] at this; exact this
  have w₉ := e₉.wb_right
  by_cases hd2' : c₉.nreg 50032 < c₉.nreg 10502
  · rw [p32, p10502] at hd2'
    have h2 : dirCode M px = 2 := by omega
    obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, q⟩ : ∃ c₁₀ k₁₀, Exec P W (block [.copyN 50210 50151,
        .copyN 50211 50150]) c₉ c₁₀ k₁₀ ∧ k₁₀ = 2 ∧ c₁₀.nreg 50210 = c₉.nreg 50151 ∧
        c₁₀.nreg 50211 = c₉.nreg 50150 := by
      exec_block; exact ⟨rfl, by config_simp, by config_simp⟩
    obtain ⟨q10, q11⟩ := q
    have eF : Exec P W (.ifLtN 50032 10502 (block [.copyN 50210 50151, .copyN 50211 50150])
        (block [.copyN 50210 50150, .copyN 50211 50151])) c₉ c₁₀ _ := .ifLtN_true (show c₉.nreg 50032 < c₉.nreg 10502 by rwo [p32, p10502]) e₁₀
    have eAll : Exec P W offCore c c₁₀ _ := .seq eH (.ifLtN_false t1 (.ifLtN_false t2
      (.seq e₄ (.seq e₅ (.ifLtN_false t3 (e₆.seq (e₇.seq (e₈.seq (e₉.seq eF)))))))))
    refine ⟨c₁₀, _, eAll, by omega, ?_, ?_⟩
    · refine (B51.of_eq q10).congr ?_; rws [h2]
    · refine (B50.of_eq q11).congr ?_; rws [h2]
  · rw [p32, p10502] at hd2'
    have h1 : dirCode M px = 1 := by omega
    obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, q⟩ : ∃ c₁₀ k₁₀, Exec P W (block [.copyN 50210 50150,
        .copyN 50211 50151]) c₉ c₁₀ k₁₀ ∧ k₁₀ = 2 ∧ c₁₀.nreg 50210 = c₉.nreg 50150 ∧
        c₁₀.nreg 50211 = c₉.nreg 50151 := by
      exec_block; exact ⟨rfl, by config_simp, by config_simp⟩
    obtain ⟨q10, q11⟩ := q
    have eF : Exec P W (.ifLtN 50032 10502 (block [.copyN 50210 50151, .copyN 50211 50150])
        (block [.copyN 50210 50150, .copyN 50211 50151])) c₉ c₁₀ _ := .ifLtN_false (show ¬ c₉.nreg 50032 < c₉.nreg 10502 by rwo [p32, p10502]) e₁₀
    have eAll : Exec P W offCore c c₁₀ _ := .seq eH (.ifLtN_false t1 (.ifLtN_false t2
      (.seq e₄ (.seq e₅ (.ifLtN_false t3 (e₆.seq (e₇.seq (e₈.seq (e₉.seq eF)))))))))
    refine ⟨c₁₀, _, eAll, by omega, ?_, ?_⟩
    · refine (B50.of_eq q10).congr ?_; rws [h1]
    · refine (B51.of_eq q11).congr ?_; rws [h1]

end

end SweepPrim

end Chazelle.Core
