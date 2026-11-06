module

public import Chazelle.Core.SweepPrimCls

/-!
# Sweep RAM primitives (WP-D2), part 10: abscissae of walk positions (`absKey`, `absCmp`)

`absLt` of design-merge-v2 §9.6 item 4 (the `a ∈ e` test, the before-the-endpoint test, ordering
hits along a ray) compares the abscissae of two walk positions, possibly of different chain
models of one host.  It is split in two primitives:

* `absKey`: for a walk position `x` of `chainModel C`, an **abscissa record** (`AbsRec`): kind
  `0` (the abscissa is `-radius`: the left side of the box), `2` (`+radius`: the right side), or
  `1` and a symbolic point of `Qof P` with the same abscissa (a vertex of the chain, the top of the
  chain for a point of the slit, or the point `onEdge E h` of the edge `E` of `Q` carrying the
  host edge, for a point inside a tour edge at the height of vertex `h`).
* `absCmp`: the bit `x₁ < x₂` of two abscissa records (one sign-kernel test at most).

The edge `E` (`hostEdgeIdx`) is read off the two host points of the tour edge (regular hosts,
`HostRegular`: consecutive host points are both on the line of one edge of `Q`,
`hostEdge_onLine`).
-/

namespace Chazelle.Core

namespace SweepPrim

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideE sideLeft sidePt)

@[expose] public section

/-! ## The line of an edge of `Q` -/

/-- The point lies on the line of edge `E` of `Q` (as a graph over the height). -/
def OnLine (Q : Polygon) (E : ℕ) (p : Point) : Prop := p.1 = Visibility.edgeX Q E p.2

theorem onLine_lerp {Q : Polygon} {E : ℕ} {a b : Point} (ha : OnLine Q E a) (hb : OnLine Q E b)
    (t : ℝ) : OnLine Q E (Geometry.lerp a b t) := by
  unfold OnLine Visibility.edgeX Visibility.xAt at *
  simp only [Geometry.lerp_fst, Geometry.lerp_snd]
  rw [ha, hb]; ring

theorem onLine_left (Q : Polygon) (E : ℕ) : OnLine Q E (Q.vtx E) := by
  unfold OnLine Visibility.edgeX; rw [Visibility.xAt_left]

theorem onLine_right {Q : Polygon} {E : ℕ} (h : (Q.vtx E).2 ≠ (Q.vtx ((E + 1) % Q.n)).2) :
    OnLine Q E (Q.vtx ((E + 1) % Q.n)) := by
  unfold OnLine Visibility.edgeX; rw [Visibility.xAt_right h]

theorem onLine_onEdge (Q : Polygon) (E h : ℕ) : OnLine Q E ((SymPt.onEdge E h).eval Q) := rfl

/-- **The edge of `Q` of a host edge**, as the machine reads it off the two host points. -/
def hostEdgeIdx (n : ℕ) : SymPt → SymPt → ℕ
  | .onEdge e _, _ => e
  | .vtx _, .onEdge e _ => e
  | .vtx i, .vtx j => if j = (i + 1) % n then i else j

theorem hostEdgeOK_symm {n : ℕ} {s₁ s₂ : SymPt} (h : HostEdgeOK n s₁ s₂) : HostEdgeOK n s₂ s₁ := by
  cases s₁ <;> cases s₂ <;> simp only [HostEdgeOK] at h ⊢ <;> omega

theorem edge_heights_ne {Q : Polygon} (hD : DistinctHeights Q) (hn : 2 ≤ Q.n) {E : ℕ}
    (hE : E < Q.n) : (Q.vtx E).2 ≠ (Q.vtx ((E + 1) % Q.n)).2 := by
  refine hD _ _ hE (Nat.mod_lt _ (by omega)) ?_
  intro h
  rcases Nat.lt_or_ge (E + 1) Q.n with h' | h'
  · rw [Nat.mod_eq_of_lt h'] at h; omega
  · rw [show E + 1 = Q.n by omega, Nat.mod_self] at h; omega

/-- **Both ends of a non-horizontal host edge lie on the line of the edge `hostEdgeIdx`.** -/
theorem hostEdge_onLine {Q : Polygon} (hD : DistinctHeights Q) (hn : 2 ≤ Q.n) {s₁ s₂ : SymPt}
    (hl₁ : s₁.Lt Q.n) (hl₂ : s₂.Lt Q.n) (hok : HostEdgeOK Q.n s₁ s₂)
    (hnh : (s₁.eval Q).2 ≠ (s₂.eval Q).2) :
    hostEdgeIdx Q.n s₁ s₂ < Q.n ∧ OnLine Q (hostEdgeIdx Q.n s₁ s₂) (s₁.eval Q) ∧
      OnLine Q (hostEdgeIdx Q.n s₁ s₂) (s₂.eval Q) := by
  cases s₁ with
  | onEdge e h =>
    cases s₂ with
    | vtx j =>
      simp only [HostEdgeOK, hostEdgeIdx, SymPt.Lt, SymPt.eval] at hok hl₁ hl₂ ⊢
      refine ⟨hl₁.1, onLine_onEdge Q e h, ?_⟩
      rcases hok with rfl | rfl
      · exact onLine_left Q j
      · exact onLine_right (edge_heights_ne hD hn hl₁.1)
    | onEdge e' h' =>
      simp only [HostEdgeOK, hostEdgeIdx, SymPt.Lt, SymPt.eval] at hok hl₁ hl₂ hnh ⊢
      rcases hok with rfl | rfl
      · exact absurd rfl hnh
      · exact ⟨hl₁.1, onLine_onEdge Q e h, onLine_onEdge Q e h'⟩
  | vtx i =>
    cases s₂ with
    | onEdge e h =>
      simp only [HostEdgeOK, hostEdgeIdx, SymPt.Lt, SymPt.eval] at hok hl₁ hl₂ ⊢
      refine ⟨hl₂.1, ?_, onLine_onEdge Q e h⟩
      rcases hok with rfl | rfl
      · exact onLine_left Q i
      · exact onLine_right (edge_heights_ne hD hn hl₂.1)
    | vtx j =>
      simp only [HostEdgeOK, hostEdgeIdx, SymPt.Lt, SymPt.eval] at hok hl₁ hl₂ ⊢
      by_cases hj : j = (i + 1) % Q.n
      · rw [ite_eq_left hj]
        refine ⟨hl₁, onLine_left Q i, ?_⟩
        rw [hj]; exact onLine_right (edge_heights_ne hD hn hl₁)
      · rw [ite_eq_right hj]
        have hi : i = (j + 1) % Q.n := by rcases hok with h | h; exacts [absurd h hj, h]
        refine ⟨hl₂, ?_, onLine_left Q j⟩
        rw [hi]; exact onLine_right (edge_heights_ne hD hn hl₂)

/-- The heights of `Qof P` are distinct in a good environment. -/
theorem distinct_Qof {P : Polygon} (hG : GoodEnv P) : DistinctHeights (Qof P) :=
  (goodShear_epsOf hG.2).2.1

/-! ## Abscissa records -/

/-- **An abscissa record** at `r`: kind `0` (`x = -R`), `2` (`x = R`), or `1` and a symbolic
point of `Qof P` in range at `r + 1` with abscissa `x`, `|x| < R`. -/
def AbsRec (P : Polygon) (c : Config) (r : ℕ) (x R : ℝ) : Prop :=
  0 < R ∧ ((c.nreg r = 0 ∧ x = -R) ∨ (c.nreg r = 2 ∧ x = R) ∨
    (c.nreg r = 1 ∧ |x| < R ∧ ∃ s : SymPt, SymPtIn c (r + 1) s ∧ s.Lt P.n ∧ (s.eval (Qof P)).1 = x))


/-! ## The point inside a tour edge -/

theorem getD_of_getElem? {α : Type} {l : List α} {q : ℕ} {a d : α} (h : l[q]? = some a) :
    l.getD q d = a := by
  rw [List.getD_eq_getElem?_getD, h]; rfl

/-- **The abscissa of a point inside a tour edge** is that of the point `onEdge E (h - 1)` of the
edge `E = hostEdgeIdx` of `Q` carrying the host edge. -/
theorem tour_abs {P : Polygon} (hG : GoodEnv P) {H : Host} {C : Chain} (_hCP : C.P = H.poly (Qof P))
    (hreg : HostRegular P.n H) (hNn : C.P.n = (H.pts P.n).length) {i : ℕ} (hi : i < 2 * C.m)
    {s₁ s₂ : SymPt}
    (h1 : (H.pts P.n)[(C.s + C.sideIdx C.sideBeta i) % (H.pts P.n).length]? = some s₁)
    (h2 : (H.pts P.n)[(C.s + C.sideIdx C.sideBeta (i + 1)) % (H.pts P.n).length]? = some s₂)
    (hl₁ : s₁.Lt P.n) (hl₂ : s₂.Lt P.n)
    (hv₁ : s₁.eval (Qof P) = (chainModel C).W.vtx (i + 6))
    (hv₂ : s₂.eval (Qof P) = (chainModel C).W.vtx ((i + 1) + 6)) {hc : ℕ}
    (ht : 0 < (chainModel C).param (Qof P) ⟨i + 6, hc⟩) :
    hostEdgeIdx P.n s₁ s₂ < P.n ∧
      ((chainModel C).pos (Qof P) ⟨i + 6, hc⟩).1 =
        ((SymPt.onEdge (hostEdgeIdx P.n s₁ s₂) (hc - 1)).eval (Qof P)).1 := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hn3 : 3 ≤ P.n := hG.1.1
  set N := (H.pts P.n).length
  have hN0 : 0 < N := by rw [← hNn]; exact C.n_pos
  set L := H.pts P.n
  -- the host edge
  have hok : HostEdgeOK P.n s₁ s₂ := by
    have hstep := C.sideTour_step C.sideBeta i
    have hmod : ∀ a, ((a % N) + 1) % N = (a + 1) % N := fun a => by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rcases hstep with h | h
    · have := hreg ((C.s + C.sideIdx C.sideBeta i) % N) (Nat.mod_lt _ hN0)
      rwa [getD_of_getElem? h1, hmod, show C.s + C.sideIdx C.sideBeta i + 1 =
        C.s + C.sideIdx C.sideBeta (i + 1) by omega, getD_of_getElem? h2] at this
    · have := hreg ((C.s + C.sideIdx C.sideBeta (i + 1)) % N) (Nat.mod_lt _ hN0)
      rw [getD_of_getElem? h2, hmod, show C.s + C.sideIdx C.sideBeta (i + 1) + 1 =
        C.s + C.sideIdx C.sideBeta i by omega, getD_of_getElem? h1] at this
      exact hostEdgeOK_symm this
  -- the walk edge
  have hwa : (chainModel C).wa (i + 6) = s₁.eval (Qof P) := hv₁.symm
  have hwb : (chainModel C).wb (i + 6) = s₂.eval (Qof P) := by
    rw [hv₂]; show (C.sideWalk C.sideBeta).vtx ((i + 6 + 1) % (C.sideWalk C.sideBeta).n) = _
    rw [C.sideWalk_next_tour _ hi]; rfl
  have hne := ne_of_param_pos ht
  rw [hwa, hwb] at hne
  have hD := distinct_Qof hG
  rw [← hQn] at hok hl₁ hl₂ ⊢
  obtain ⟨hE, hon₁, hon₂⟩ := hostEdge_onLine hD (by omega) hl₁ hl₂ hok hne
  refine ⟨hE, ?_⟩
  have hpos : OnLine (Qof P) (hostEdgeIdx (Qof P).n s₁ s₂) ((chainModel C).pos (Qof P) ⟨i + 6, hc⟩) := by
    show OnLine _ _ (Geometry.lerp ((chainModel C).wa (i + 6)) ((chainModel C).wb (i + 6)) _)
    rw [hwa, hwb]; exact onLine_lerp hon₁ hon₂ _
  rw [hpos]
  have hne' : ((chainModel C).wa (i + 6)).2 ≠ ((chainModel C).wb (i + 6)).2 := by
    rwa [hwa, hwb]
  rw [Model.pos_snd (Q := Qof P) (x := ⟨i + 6, hc⟩) hne']
  have hc1 : 1 ≤ hc := by
    rcases Nat.eq_zero_or_pos hc with rfl | h
    · exact absurd (show (chainModel C).param (Qof P) ⟨i + 6, 0⟩ = 0 from rfl) (ne_of_gt ht)
    · exact h
  obtain ⟨h', rfl⟩ : ∃ h', hc = h' + 1 := ⟨hc - 1, by omega⟩
  rfl


/-! ## The machine: the edge of a host edge -/

/-- The edge `hostEdgeIdx n s₁ s₂` of the host points in the slots `50130` and `50136` into
`50142` (scratch `50140`, `50141`). -/
def edgeIdxS : Stmt :=
  .ifLtN 50130 50032
    (.ifLtN 50136 50032
      (.seq (block [.addN 50140 50131 50032, .inputSize 50141])
        (.seq (.ifLtN 50140 50141 .skip (.instr (.constN 50140 0)))
          (.ifLtN 50140 50137 (.instr (.copyN 50142 50137))
            (.ifLtN 50137 50140 (.instr (.copyN 50142 50137)) (.instr (.copyN 50142 50131))))))
      (.instr (.copyN 50142 50137)))
    (.instr (.copyN 50142 50131))

theorem edgeIdxS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (hW : P.n + 1 ≤ W) (h32 : c.nreg 50032 = 1) {s₁ s₂ : SymPt} (h1 : SymPtIn c 50130 s₁)
    (h2 : SymPtIn c 50136 s₂) (hl₁ : s₁.Lt P.n) (hl₂ : s₂.Lt P.n) :
    ∃ c' k, Exec P W edgeIdxS c c' k ∧ k ≤ 12 ∧ c'.nreg 50142 = hostEdgeIdx P.n s₁ s₂ ∧
      ∀ r, r ≠ 50140 → r ≠ 50141 → r ≠ 50142 → c'.nreg r = c.nreg r := by
  unfold edgeIdxS
  cases s₁ with
  | onEdge e h =>
    obtain ⟨k1, k2, -⟩ := h1
    refine spec_ifLtN_false (by rw [k1, h32]; omega) (spec_instr (Exec.copyN hw _ _)
      fun _ => ⟨by omega, by simp [k2, hostEdgeIdx], fun r h1 h2 h3 => by simp [h3]⟩)
  | vtx i =>
    obtain ⟨k1, k2⟩ := h1
    refine spec_ifLtN_true (by rw [k1, h32]; omega) ?_
    cases s₂ with
    | onEdge e h =>
      obtain ⟨j1, j2, -⟩ := h2
      refine spec_ifLtN_false (by rw [j1, h32]; omega) (spec_instr (Exec.copyN hw _ _)
        fun _ => ⟨by omega, by simp [j2, hostEdgeIdx], fun r h1 h2 h3 => by simp [h3]⟩)
    | vtx j =>
      obtain ⟨j1, j2⟩ := h2
      have k2' : c.nreg 50131 = i := k2
      have j2' : c.nreg 50137 = j := j2
      simp only [SymPt.Lt] at hl₁ hl₂
      have e₁ := Exec.addN (P := P) hw 50140 50131 50032 (by rw [k2', h32]; omega)
      set c₁ : Config := { c with nreg := upd c.nreg 50140 (c.nreg 50131 + c.nreg 50032) }
        with hc₁
      have w₁ := e₁.wb_right
      have e₂ := Exec.inputSize (P := P) w₁ 50141 (by omega)
      set c₂ : Config := { c₁ with nreg := upd c₁.nreg 50141 P.n } with hc₂
      have w₂ := e₂.wb_right
      have q40 : c₂.nreg 50140 = i + 1 := by rw [hc₂, hc₁]; simp [k2', h32]
      have q41 : c₂.nreg 50141 = P.n := by rw [hc₂]; simp
      have r₂ : ∀ r, r ≠ 50140 → r ≠ 50141 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
        rw [hc₂, hc₁]; simp [h1, h2]
      obtain ⟨c₃, k₃, e₃, hk₃, q40', r₃⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 50140 50141 .skip
          (.instr (.constN 50140 0))) c₂ c₃ k₃ ∧ k₃ ≤ 3 ∧ c₃.nreg 50140 = (i + 1) % P.n ∧
          ∀ r, r ≠ 50140 → c₃.nreg r = c₂.nreg r := by
        by_cases hl : i + 1 < P.n
        · exact spec_ifLtN_true (by rwa [q40, q41]) (spec_skip w₂
            ⟨by omega, by rw [q40, Nat.mod_eq_of_lt hl], fun _ _ => rfl⟩)
        · refine spec_ifLtN_false (by rwa [q40, q41]) (spec_instr (Exec.constN w₂ _ _
            (by omega)) fun _ => ⟨by omega, ?_, fun r hr => by simp [hr]⟩)
          simp only [upd_same]
          rw [show i + 1 = P.n by omega, Nat.mod_self]
      have w₃ := e₃.wb_right
      have j3 : c₃.nreg 50137 = j := by rw [r₃ _ (by decide), r₂ _ (by decide) (by decide), j2']
      have i3 : c₃.nreg 50131 = i := by rw [r₃ _ (by decide), r₂ _ (by decide) (by decide), k2']
      have eb : Exec P W (block [.addN 50140 50131 50032, .inputSize 50141]) c c₂ 2 :=
        Exec.block_cons e₁ (Exec.block_cons e₂ (Exec.block_nil w₂))
      have t1 : c.nreg 50136 < c.nreg 50032 := by rw [j1, h32]; omega
      have fin : ∀ a, a = 50137 ∨ a = 50131 → ∃ c₄, Exec P W (.instr (.copyN 50142 a)) c₃ c₄ 1 ∧
          c₄.nreg 50142 = c₃.nreg a ∧ ∀ r, r ≠ 50140 → r ≠ 50141 → r ≠ 50142 →
            c₄.nreg r = c.nreg r := fun a ha =>
        ⟨_, Exec.copyN w₃ _ _, by simp, fun r h1 h2 h3 => by
          simp only [upd_other _ _ _ h3]; rw [r₃ r h1, r₂ r h1 h2]⟩
      by_cases ha : (i + 1) % P.n < j
      · have t2 : c₃.nreg 50140 < c₃.nreg 50137 := by rwa [q40', j3]
        obtain ⟨c₄, e₄, v₄, r₄⟩ := fin 50137 (Or.inl rfl)
        refine ⟨c₄, _, .ifLtN_true t1 (.seq eb (.seq e₃ (.ifLtN_true t2 e₄))), by omega, ?_, r₄⟩
        rw [v₄, j3]; simp only [hostEdgeIdx]; rw [ite_eq_right (by omega)]
      have t2 : ¬ c₃.nreg 50140 < c₃.nreg 50137 := by rwa [q40', j3]
      by_cases hb : j < (i + 1) % P.n
      · have t3 : c₃.nreg 50137 < c₃.nreg 50140 := by rwa [q40', j3]
        obtain ⟨c₄, e₄, v₄, r₄⟩ := fin 50137 (Or.inl rfl)
        refine ⟨c₄, _, .ifLtN_true t1 (.seq eb (.seq e₃ (.ifLtN_false t2 (.ifLtN_true t3 e₄)))),
          by omega, ?_, r₄⟩
        rw [v₄, j3]; simp only [hostEdgeIdx]; rw [ite_eq_right (by omega)]
      · have t3 : ¬ c₃.nreg 50137 < c₃.nreg 50140 := by rwa [q40', j3]
        obtain ⟨c₄, e₄, v₄, r₄⟩ := fin 50131 (Or.inr rfl)
        refine ⟨c₄, _, .ifLtN_true t1 (.seq eb (.seq e₃ (.ifLtN_false t2 (.ifLtN_false t3 e₄)))),
          by omega, ?_, r₄⟩
        rw [v₄, i3]; simp only [hostEdgeIdx]; rw [ite_eq_left (by omega)]


/-! ## The machine: `absKey` -/

/-- Output the point `onEdge (50142) (h - 1)`. -/
def outE : Stmt :=
  block [.constN 50210 1, .constN 50211 1, .copyN 50212 50142, .subN 50213 50202 50032]
/-- The abscissa of the top of the chain (a point of the slit). -/
def absTop : Stmt :=
  .seq (.instr (.constN 50120 0)) (.seq (tvLoad 50211) (.instr (.constN 50210 1)))
/-- The box block: the left side, the right side, or the slit. -/
def absBox : Stmt :=
  .ifLtN 50201 50082 (.instr (.constN 50210 0))
    (.ifLtN 50201 50084 (.instr (.constN 50210 2)) absTop)
/-- A tour vertex. -/
def absVtx : Stmt :=
  .seq (.instr (.subN 50120 50201 50081)) (.seq (tvLoad 50211) (.instr (.constN 50210 1)))
/-- Inside a tour edge. -/
def absTour : Stmt :=
  .seq (tvLoad 50130) (.seq (.instr (.addN 50120 50120 50032)) (.seq (tvLoad 50136)
    (.seq edgeIdxS outE)))
/-- Inside a tour edge or the up-slit edge. -/
def absInt : Stmt :=
  .seq (block [.subN 50120 50201 50081, .addN 50143 50053 50053])
    (.ifLtN 50120 50143 absTour absTop)

/-- **The primitive `absKey`.** -/
def absKey : Stmt := .seq pHead (classify absBox absVtx absInt)

theorem wr_absKey : wr Bprim absKey = true := by decide

theorem absTop_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) :
    ∃ c' k, Exec P W absTop c c' k ∧ k ≤ 27 * H.length + 45 ∧
      AbsRec P c' 50210 C.top.1 C.radius := by
  have e₁ := Exec.constN (P := P) hE.wb 50120 0 (by omega)
  have hE₁ : CEnv P W H C _ := hE.step e₁ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp, -⟩ := tvLoad_exec _ hE₁ (i := 0)
    (by simp) (by omega) (dst := 50211) (by norm_num)
  have e₃ := Exec.constN (P := P) e₂.wb_right 50210 1 (by have := hE.hW; omega)
  refine ⟨_, _, .seq e₁ (.seq e₂ e₃), by omega, C.radius_pos, Or.inr (Or.inr ⟨by simp,
    C.abs_top_fst_lt_radius, sp, symPtIn_of_eq isp fun j h1 h2 => by simp [show j ≠ 50210 by
      omega], lsp, ?_⟩)⟩
  rw [vsp, zero_add, walk_vtx_six]

theorem absBox_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {e hc : ℕ} (h01 : c.nreg 50201 = e)
    (hd : c.nreg 10502 = dirCode (chainModel C) e) (he : e < 6)
    (ht : 0 < (chainModel C).param (Qof P) ⟨e, hc⟩) :
    ∃ c' k, Exec P W absBox c c' k ∧ k ≤ 27 * H.length + 50 ∧
      AbsRec P c' 50210 ((chainModel C).pos (Qof P) ⟨e, hc⟩).1 C.radius := by
  have hne := ne_of_param_pos ht
  have hdir : dirCode (chainModel C) e ≠ 0 := by
    unfold dirCode; split_ifs with h1 h2
    · omega
    · omega
    · exact absurd (le_antisymm (not_lt.1 h2) (not_lt.1 h1)) hne
  rw [chain_dirCode_small C he] at hdir
  have hR := C.radius_pos
  have hW := hE.hW
  obtain ⟨-, e1, -, e3, -, e5, -⟩ := C.sidePt_box C.sideBeta ((chainModel C).param (Qof P) ⟨e, hc⟩)
  have hpos : (chainModel C).pos (Qof P) ⟨e, hc⟩ =
      sidePt (C.sideWalk C.sideBeta) e ((chainModel C).param (Qof P) ⟨e, hc⟩) := rfl
  by_cases h1 : e < 2
  · have he1 : e = 1 := by split_ifs at hdir <;> omega
    subst he1
    refine ⟨_, _, .ifLtN_true (by rw [h01, hE.r82]; omega) (Exec.constN hE.wb _ _ (by omega)),
      by omega, hR, Or.inl ⟨by simp, ?_⟩⟩
    rw [hpos, e1]
  by_cases h3 : e < 4
  · have he3 : e = 3 := by split_ifs at hdir <;> omega
    subst he3
    refine ⟨_, _, .ifLtN_false (by rw [h01, hE.r82]; omega) (.ifLtN_true
      (by rw [h01, hE.r84]; omega) (Exec.constN hE.wb _ _ (by omega))), by omega, hR,
      Or.inr (Or.inl ⟨by simp, ?_⟩)⟩
    rw [hpos, e3]
  · have he5 : e = 5 := by split_ifs at hdir <;> omega
    subst he5
    obtain ⟨c', k', ex, hk, hrec⟩ := absTop_exec c hE
    refine ⟨c', _, .ifLtN_false (by rw [h01, hE.r82]; omega) (.ifLtN_false
      (by rw [h01, hE.r84]; omega) ex), by omega, ?_⟩
    rwa [hpos, e5]

theorem absVtx_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {e hc : ℕ} (h01 : c.nreg 50201 = e) (he6 : 6 ≤ e)
    (hen : e < 2 * C.m + 7) (hpar : (chainModel C).param (Qof P) ⟨e, hc⟩ = 0) :
    ∃ c' k, Exec P W absVtx c c' k ∧ k ≤ 27 * H.length + 45 ∧
      AbsRec P c' 50210 ((chainModel C).pos (Qof P) ⟨e, hc⟩).1 C.radius := by
  have e₁ := Exec.subN (P := P) hE.wb 50120 50201 50081
  have hE₁ : CEnv P W H C _ := hE.step e₁ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp, -⟩ := tvLoad_exec _ hE₁ (i := e - 6)
    (by simp [h01, hE.r81]) (by omega) (dst := 50211) (by norm_num)
  have e₃ := Exec.constN (P := P) e₂.wb_right 50210 1 (by have := hE.hW; omega)
  have hv : (chainModel C).pos (Qof P) ⟨e, hc⟩ = (chainModel C).W.vtx (e - 6 + 6) := by
    rw [pos_eq_sidePt, hpar, Chazelle.Chain.sidePt_zero, show e - 6 + 6 = e by omega]
  have hmem : (chainModel C).W.vtx (e - 6 + 6) ∈ C.set := by
    rw [walk_vtx_tour C (by omega)]; exact C.vertex_mem_set (C.sideIdx_le _ _)
  refine ⟨_, _, .seq e₁ (.seq e₂ e₃), by omega, C.radius_pos, Or.inr (Or.inr ⟨by simp, ?_,
    sp, symPtIn_of_eq isp fun j h1 h2 => by simp [show j ≠ 50210 by omega], lsp, ?_⟩)⟩
  · rw [hv]
    exact lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hmem).1 C.coordBound_lt_radius
  · rw [vsp, hv]


theorem absInt_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) (hreg : HostRegular P.n H) {e hc : ℕ} (h01 : c.nreg 50201 = e)
    (h02 : c.nreg 50202 = hc) (he6 : 6 ≤ e) (hen : e < 2 * C.m + 7)
    (ht : 0 < (chainModel C).param (Qof P) ⟨e, hc⟩) (ht1 : (chainModel C).param (Qof P) ⟨e, hc⟩ < 1)
    (hhn : hc ≤ P.n) :
    ∃ c' k, Exec P W absInt c c' k ∧ k ≤ 60 * H.length + 200 ∧
      AbsRec P c' 50210 ((chainModel C).pos (Qof P) ⟨e, hc⟩).1 C.radius := by
  have hW := hE.hW
  have hNW := hE.NW
  have hNn := hE.n_eq
  have hmN := C.m_lt
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.subN 50120 50201 50081,
      .addN 50143 50053 50053]) c c₁ k₁ ∧ k₁ = 2 ∧ (c₁.nreg 50120 = e - 6 ∧
        c₁.nreg 50143 = 2 * C.m ∧ ∀ r, r ≠ 50120 → r ≠ 50143 → c₁.nreg r = c.nreg r) := by
    have hw := hE.wb
    exec_block
    · config_simp; rw [hE.r53]; omega
    · refine ⟨rfl, by config_simp; rw [h01, hE.r81], by config_simp; rw [hE.r53]; ring,
        fun r h1 h2 => by simp [h1, h2]⟩
  obtain ⟨q20, q43, r₁⟩ := q
  have hE₁ : CEnv P W H C c₁ := hE.keep e₁.wb_right
    (exec_frameB e₁ (B := fun r => r == 50120 || r == 50143) (by decide)).2.2.1
    (fun r hr => r₁ r (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide)))
  by_cases hlt : e - 6 < 2 * C.m
  · set i := e - 6
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, s₁, i₁, l₁, v₁, x₁⟩ := tvLoad_exec c₁ hE₁ (i := i) q20
      hlt.le (dst := 50130) (by norm_num)
    have w₂ := e₂.wb_right
    have e₃ := Exec.addN (P := P) w₂ 50120 50120 50032
      (by rw [f₂.1 _ (by decide), q20, hE₂.r32]; omega)
    set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50120 (c₂.nreg 50120 + c₂.nreg 50032) }
      with hc₃
    have hE₃ : CEnv P W H C c₃ := hE₂.step e₃ (by decide)
    obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, s₂, i₂, l₂, v₂, x₂⟩ := tvLoad_exec c₃ hE₃ (i := i + 1)
      (by rw [hc₃]; simp [f₂.1 _ (by decide : Btv 50130 50120 = false) ▸ q20, hE₂.r32])
      (by omega) (dst := 50136) (by norm_num)
    have i₁' : SymPtIn c₄ 50130 s₁ := symPtIn_keep (symPtIn_of_eq i₁ fun j h1 h2 => by
      rw [hc₃]; simp [show j ≠ 50120 by omega]) f₄
      (by intro j h1 h2; interval_cases j <;> decide)
    obtain ⟨c₅, k₅, e₅, hk₅, v₅, r₅⟩ := edgeIdxS_exec (P := P) c₄ e₄.wb_right (by omega)
      hE₄.r32 i₁' i₂ l₁ l₂
    have q02 : c₅.nreg 50202 = hc := by
      rw [r₅ _ (by decide) (by decide) (by decide), f₄.1 _ (by decide), hc₃]
      simp only
      rw [upd_other _ _ _ (by decide), f₂.1 _ (by decide), r₁ _ (by decide) (by decide), h02]
    have q32 : c₅.nreg 50032 = 1 := by
      rw [r₅ _ (by decide) (by decide) (by decide), hE₄.r32]
    obtain ⟨hEi, hx⟩ := tour_abs hE.hG hE.hP hreg hNn hlt x₁ x₂ l₁ l₂ v₁ v₂
      (hc := hc) (by rwa [show i + 6 = e by omega])
    have hc1 : 1 ≤ hc := by
      rcases Nat.eq_zero_or_pos hc with rfl | h
      · exact absurd (show (chainModel C).param (Qof P) ⟨e, 0⟩ = 0 from rfl) (ne_of_gt ht)
      · exact h
    obtain ⟨c₆, k₆, e₆, hk₆, q⟩ : ∃ c₆ k₆, Exec P W outE c₅ c₆ k₆ ∧ k₆ = 4 ∧
        (c₆.nreg 50210 = 1 ∧ SymPtIn c₆ 50211 (.onEdge (hostEdgeIdx P.n s₁ s₂) (hc - 1))) := by
      unfold outE
      have hw₅ := e₅.wb_right
      exec_block
      all_goals try omega
      refine ⟨rfl, by config_simp, by config_simp, by config_simp; exact v₅, ?_⟩
      config_simp; rw [q02, q32]
    obtain ⟨q10, q11⟩ := q
    have ex : Exec P W absInt c c₆ (k₁ + (k₂ + (1 + (k₄ + (k₅ + k₆))) + 1)) :=
      .seq e₁ (.ifLtN_true (by rwa [q20, q43]) (.seq e₂ (.seq e₃ (.seq e₄
        (.seq e₅ e₆)))))
    have hmem : (chainModel C).pos (Qof P) ⟨e, hc⟩ ∈ C.set := by
      have hei : e = i + 6 := by omega
      rw [pos_eq_sidePt]
      rw [hei] at ht ht1 ⊢
      exact C.sideWalk_tour_pt_mem _ hlt.le (fun h => absurd h (by omega)) ht.le ht1
    refine ⟨c₆, _, ex, by have := hE.hlen; omega, C.radius_pos, Or.inr (Or.inr ⟨q10,
      lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hmem).1 C.coordBound_lt_radius,
      _, q11, ⟨hEi, by omega⟩, ?_⟩)⟩
    rw [show e = i + 6 by omega, hx]
  · have he' : e = 2 * C.m + 6 := by omega
    obtain ⟨c₂, k₂, e₂, hk₂, hrec⟩ := absTop_exec c₁ hE₁
    refine ⟨c₂, _, .seq e₁ (.ifLtN_false (by rwa [q20, q43]) e₂), by omega, ?_⟩
    subst he'
    obtain ⟨-, -, -, -, -, -, e6⟩ := C.sidePt_box C.sideBeta
      ((chainModel C).param (Qof P) ⟨2 * C.m + 6, hc⟩)
    rw [pos_eq_sidePt, show (chainModel C).W = C.sideWalk C.sideBeta from rfl]
    simp only
    rwa [e6]


/-! ## The contracts -/

/-- The input condition of `absKey`: that of `leftSec` and a regular host. -/
def AbsKeyIn (P : Polygon) (W : ℕ) (C : Chain) (c : Config) : Prop :=
  LeftIn P W C c ∧ ∀ H', HostAt c.nmem (c.nmem (c.nreg 50200)) H' → HostRegular P.n H'

/-- The output condition of `absKey`: an abscissa record of the point of `(e, h)`, with the radius
of the chain's box. -/
def AbsKeyOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  AbsRec P c' 50210 ((chainModel C).pos (Qof P) ⟨c.nreg 50201, c.nreg 50202⟩).1 C.radius

/-- **Contract of `absKey`** (at most `16700` steps). -/
theorem absKey_meets : Meets absKey primBands (PrimPre AbsKeyIn) (PrimPost AbsKeyOut)
    (fun _ _ => 16700) := by
  refine prim_meets (K := 15900) (fun r h => h) wr_absKey ?_
  intro P W H C c₀ c hC hE ⟨⟨hen, ⟨hp0, hp1, hhn⟩, hy⟩, hreg⟩ hinp
  have hregH := hreg H hC.1
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hlen := hE.hlen
  obtain ⟨c', k, ex, hk, hr⟩ := classify_exec (Kb := 27 * H.length + 50)
    (Kv := 27 * H.length + 45) (Ki := 60 * H.length + 200)
    (R := fun c' => AbsRec P c' 50210 ((chainModel C).pos (Qof P)
      ⟨c₀.nreg 50201, c₀.nreg 50202⟩).1 C.radius) c₀ c hE hinp hen hp0 hp1 hhn hy
    (fun c₂ hE₂ g₂ d₂ he hpos => absBox_exec c₂ hE₂ (g₂ 50201 (by norm_num) (by norm_num)) d₂ he
      hpos)
    (fun c₂ hE₂ g₂ h6 hpar => absVtx_exec c₂ hE₂ (g₂ 50201 (by norm_num) (by norm_num)) h6
      (by omega) hpar)
    (fun c₂ hE₂ g₂ _ h6 hpos => absInt_exec c₂ hE₂ hregH (g₂ 50201 (by norm_num) (by norm_num))
      (g₂ 50202 (by norm_num) (by norm_num)) h6 (by omega) hpos hp1 hhn)
  exact ⟨c', k, ex, by omega, hr⟩

/-- **`absCmp`**: the bit `x₁ < x₂` of the abscissa records at `50201` and `50205` into `50210`. -/
def absCmp : Stmt :=
  .seq (.instr (.constN 50032 1))
    (.ifLtN 50201 50032
      (.ifLtN 50205 50032 (.instr (.constN 50210 0)) (.instr (.constN 50210 1)))
      (.ifLtN 50032 50201 (.instr (.constN 50210 0))
        (.ifLtN 50205 50032 (.instr (.constN 50210 0))
          (.ifLtN 50032 50205 (.instr (.constN 50210 1))
            (kbit 50202 50206 50202 0 50210)))))

theorem wr_absCmp : wr Bprim absCmp = true := by decide

/-- The kind of an abscissa record is `0`, `1` or `2`. -/
theorem AbsRec.kind {P : Polygon} {c : Config} {r : ℕ} {x R : ℝ} (h : AbsRec P c r x R) :
    c.nreg r ≤ 2 := by
  rcases h.2 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega

theorem AbsRec.le {P : Polygon} {c : Config} {r : ℕ} {x R : ℝ} (h : AbsRec P c r x R) :
    -R ≤ x ∧ x ≤ R := by
  obtain ⟨hR, h⟩ := h
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, hx, -⟩
  · constructor <;> linarith
  · constructor <;> linarith
  · exact ⟨(abs_lt.1 hx).1.le, (abs_lt.1 hx).2.le⟩

/-- **Contract of `absCmp`** (at most `260` steps): for any abscissa records of `x₁`, `x₂` with a
common radius, the bit of `x₁ < x₂`. -/
theorem absCmp_meets : Meets absCmp primBands
    (fun P W c => GoodEnv P ∧ P.n + 3 ≤ W ∧
      ∃ x₁ x₂ R : ℝ, AbsRec P c 50201 x₁ R ∧ AbsRec P c 50205 x₂ R)
    (fun P c c' => ∀ x₁ x₂ R : ℝ, AbsRec P c 50201 x₁ R → AbsRec P c 50205 x₂ R →
      BitIs c' 50210 (x₁ < x₂))
    (fun _ _ => 260) := by
  intro P W c hw ⟨hG, hW, y₁, y₂, R₀, hy₁, hy₂⟩ hroom
  have e₁ := Exec.constN (P := P) hw 50032 1 (by omega)
  set c₁ : Config := { c with nreg := upd c.nreg 50032 1 } with hc₁
  have w₁ := e₁.wb_right
  have r₁ : ∀ r, r ≠ 50032 → c₁.nreg r = c.nreg r := fun r hr => by rw [hc₁]; simp [hr]
  have p₁ : c₁.nreg 50032 = 1 := by rw [hc₁]; simp
  have k₁ := hy₁.kind
  have k₂ := hy₂.kind
  -- the answer as a function of the kinds, when it does not need the kernel
  have fin : ∀ v, v ≤ 1 → (∀ x₁ x₂ R : ℝ, AbsRec P c 50201 x₁ R → AbsRec P c 50205 x₂ R →
      (v = 1 ↔ x₁ < x₂)) → ∃ c₂, Exec P W (.instr (.constN 50210 v)) c₁ c₂ 1 ∧
      ∀ x₁ x₂ R : ℝ, AbsRec P c 50201 x₁ R → AbsRec P c 50205 x₂ R →
        BitIs c₂ 50210 (x₁ < x₂) := fun v hv hvt =>
    ⟨_, Exec.constN w₁ _ _ (by omega), fun x₁ x₂ R h₁ h₂ =>
      ⟨by simp [hv], by simp only [upd_same]; exact hvt x₁ x₂ R h₁ h₂⟩⟩
  have frame : ∀ c₂ k, Exec P W absCmp c c₂ k → Frame primBands c c₂ k := fun c₂ k ex =>
    frame_of_frameB (exec_frameB ex wr_absCmp) (fun r hr => Bprim_band r hr) _
  have u01 : c₁.nreg 50201 = c.nreg 50201 := r₁ _ (by decide)
  have u05 : c₁.nreg 50205 = c.nreg 50205 := r₁ _ (by decide)
  by_cases a0 : c.nreg 50201 < 1
  · have t0 : c₁.nreg 50201 < c₁.nreg 50032 := by rwa [u01, p₁]
    by_cases b0 : c.nreg 50205 < 1
    · obtain ⟨c₂, e₂, h₂⟩ := fin 0 (by omega) (fun x₁ x₂ R h₁ h₂ => by
        rcases h₁.2 with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> [skip; omega; omega]
        rcases h₂.2 with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> [skip; omega; omega]
        simp)
      have ex : Exec P W absCmp c c₂ _ :=
        .seq e₁ (.ifLtN_true t0 (.ifLtN_true (by rwa [u05, p₁]) e₂))
      exact ⟨c₂, _, ex, by show _ ≤ 260; omega, h₂, frame _ _ ex⟩
    · obtain ⟨c₂, e₂, h₂⟩ := fin 1 le_rfl (fun x₁ x₂ R h₁ h₂ => by
        have hR := h₁.1
        rcases h₁.2 with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> [skip; omega; omega]
        rcases h₂.2 with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨-, hx, -⟩
        · omega
        · simp; linarith
        · simp; linarith [(abs_lt.1 hx).1])
      have ex : Exec P W absCmp c c₂ _ :=
        .seq e₁ (.ifLtN_true t0 (.ifLtN_false (by rwa [u05, p₁]) e₂))
      exact ⟨c₂, _, ex, by show _ ≤ 260; omega, h₂, frame _ _ ex⟩
  have t0 : ¬ c₁.nreg 50201 < c₁.nreg 50032 := by rwa [u01, p₁]
  by_cases a2 : 1 < c.nreg 50201
  · obtain ⟨c₂, e₂, h₂⟩ := fin 0 (by omega) (fun x₁ x₂ R h₁ h₂ => by
      rcases h₁.2 with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨h, -⟩ <;> [omega; skip; omega]
      have := h₂.le
      simp; linarith)
    have ex : Exec P W absCmp c c₂ _ :=
      .seq e₁ (.ifLtN_false t0 (.ifLtN_true (by rwa [u01, p₁]) e₂))
    exact ⟨c₂, _, ex, by show _ ≤ 260; omega, h₂, frame _ _ ex⟩
  have t1 : ¬ c₁.nreg 50032 < c₁.nreg 50201 := by rwa [u01, p₁]
  by_cases b0 : c.nreg 50205 < 1
  · obtain ⟨c₂, e₂, h₂⟩ := fin 0 (by omega) (fun x₁ x₂ R h₁ h₂ => by
      rcases h₂.2 with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> [skip; omega; omega]
      have := h₁.le
      simp; linarith)
    have ex : Exec P W absCmp c c₂ _ :=
      .seq e₁ (.ifLtN_false t0 (.ifLtN_false t1 (.ifLtN_true (by rwa [u05, p₁]) e₂)))
    exact ⟨c₂, _, ex, by show _ ≤ 260; omega, h₂, frame _ _ ex⟩
  have t2 : ¬ c₁.nreg 50205 < c₁.nreg 50032 := by rwa [u05, p₁]
  by_cases b2 : 1 < c.nreg 50205
  · obtain ⟨c₂, e₂, h₂⟩ := fin 1 le_rfl (fun x₁ x₂ R h₁ h₂ => by
      have hR := h₁.1
      rcases h₂.2 with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨h, -⟩ <;> [omega; skip; omega]
      rcases h₁.2 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hx, -⟩ <;> [omega; omega; skip]
      simp; linarith [(abs_lt.1 hx).2])
    have ex : Exec P W absCmp c c₂ _ :=
      .seq e₁ (.ifLtN_false t0 (.ifLtN_false t1 (.ifLtN_false t2
        (.ifLtN_true (by rwa [u05, p₁]) e₂))))
    exact ⟨c₂, _, ex, by show _ ≤ 260; omega, h₂, frame _ _ ex⟩
  have t3 : ¬ c₁.nreg 50032 < c₁.nreg 50205 := by rwa [u05, p₁]
  -- both are symbolic points
  obtain ⟨-, h₁⟩ := hy₁
  obtain ⟨-, h₂⟩ := hy₂
  rcases h₁ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, s₁, i₁, l₁, -⟩ <;> [omega; omega; skip]
  rcases h₂ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, s₂, i₂, l₂, -⟩ <;> [omega; omega; skip]
  have i₁' : SymPtIn c₁ 50202 s₁ := symPtIn_of_eq i₁ fun j h1 h2 => r₁ j (by omega)
  have i₂' : SymPtIn c₁ 50206 s₂ := symPtIn_of_eq i₂ fun j h1 h2 => r₁ j (by omega)
  obtain ⟨c₂, k₂', e₂, hk₂, f₂, b₂, t₂⟩ := kbit_exec (op := 0) (dst := 50210) hG hW c₁ w₁
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) l₁ l₂ l₁ i₁' i₂' i₁'
  have ex : Exec P W absCmp c c₂ _ :=
    .seq e₁ (.ifLtN_false t0 (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3 e₂))))
  refine ⟨c₂, _, ex, by show _ ≤ 260; omega, fun x₁ x₂ R h₁ h₂ => ⟨b₂, ?_⟩, frame _ _ ex⟩
  rw [t₂]
  simp only [SignTest]
  obtain ⟨-, h₁⟩ := h₁
  obtain ⟨-, h₂⟩ := h₂
  rcases h₁ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, s₁', i₁'', -, v₁⟩ <;> [omega; omega; skip]
  rcases h₂ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, s₂', i₂'', -, v₂⟩ <;> [omega; omega; skip]
  rw [symPtIn_unique i₁ i₁'', symPtIn_unique i₂ i₂'', v₁, v₂]

end

end SweepPrim

end Chazelle.Core
