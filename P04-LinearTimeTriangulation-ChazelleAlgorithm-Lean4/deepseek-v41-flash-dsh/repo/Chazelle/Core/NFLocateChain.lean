module

public import Chazelle.Golf

public import Chazelle.Core.NFLocateHost

/-!
# Double identification: the direction of the query edge, chain model (WP-C, target 2)

The walk of the chain model `chainModel C` is `C.sideWalk C.sideBeta`: edges `0 … 4` along the
box, `5` down the slit, `6 … 2m + 5` the tour of the double boundary from the top vertex, `2m + 6`
up the slit.  The directions of the box and slit edges are constants (`chain_dirCode_small`,
`chain_dirCode_last`: box corners at heights `± radius`, the slit top at `radius`, the top vertex
below it).  For a tour edge `6 + i` the two walk vertices are the chain vertices
`sideIdx β i = sideE m j` and `sideIdx β (i + 1) = sideE m (j + 1)`, `j = (S + i) mod 2m`,
`S = sideS β` (`T` or `2m - T` for the top index `T` of the descriptor), i.e. the host points of
indices `(s + k) mod N` (`chain_dirCode_tour`); `chainDir` computes them with `NFLocateHost`
and compares their heights with `dirTail`.

The descriptor must be well formed (`chainDir_exec`): host within the word bound and
well formed (`HostWF`), start `C.s < N` for the number `N` of host points, `2 N ≤ W` (all index
arithmetic stays below the word bound).
-/

namespace Chazelle.Core

namespace NFLoc

open Machine Machine.Stmt Programs SignK WalkKey
open Chazelle.Chain (sideE)

@[expose] public section

/-! ## The walk of the chain model -/

section walk
variable (C : Chain)

theorem dirOf_lt {a b : ℝ} (h : a < b) : dirOf a b = 1 := by
  unfold dirOf; Ξ ite_eq_left h

theorem dirOf_gt {a b : ℝ} (h : b < a) : dirOf a b = 2 := by
  unfold dirOf; Ξ ite_eq_right (not_lt.2 h.le), ite_eq_left h

theorem dirOf_self (a : ℝ) : dirOf a a = 0 := by
  unfold dirOf; Ξ ite_eq_right (lt_irrefl a), ite_eq_right (lt_irrefl a)

/-- The walk vertex heights of the box and slit edges. -/
theorem chain_dirCode_small {e : ℕ} (he : e < 6) :
    dirCode (chainModel C) e = if e = 1 ∨ e = 5 then 2 else if e = 3 then 1 else 0 := by
  have hr := C.radius_pos
  have ht := C.top_snd_lt_radius
  have hn := C.sideWalk_n C.sideBeta
  have hs : C.slitTop.2 = C.radius := rfl
  have h6 : (C.sideWalk C.sideBeta).vtx 6 = C.top := by
    Ξ show (6 : ℕ) = 0 + 6 from rfl, C.sideWalk_vtx_tour _ (⋄), C.sideTour_zero
  Ξ dirCode_eq
  ϴ Model.wa, Model.wb, chainModel, hn
  interval_cases e
  · Ξ Nat.mod_eq_of_lt (⋄), C.sideWalk_vtx_zero, C.sideWalk_vtx_one, hs
    exact dirOf_self _
  · Ξ Nat.mod_eq_of_lt (⋄), C.sideWalk_vtx_one, C.sideWalk_vtx_two
    exact dirOf_gt (by show -C.radius < C.radius; linarith)
  · Ξ Nat.mod_eq_of_lt (⋄), C.sideWalk_vtx_two, C.sideWalk_vtx_three
    exact dirOf_self _
  · Ξ Nat.mod_eq_of_lt (⋄), C.sideWalk_vtx_three, C.sideWalk_vtx_four
    exact dirOf_lt (by show -C.radius < C.radius; linarith)
  · Ξ Nat.mod_eq_of_lt (⋄), C.sideWalk_vtx_four, C.sideWalk_vtx_five, hs
    exact dirOf_self _
  · Ξ Nat.mod_eq_of_lt (⋄), C.sideWalk_vtx_five, h6, hs
    exact dirOf_gt ht

/-- The closing edge goes up the slit. -/
theorem chain_dirCode_last : dirCode (chainModel C) (2 * C.m + 6) = 1 := by
  have ht := C.top_snd_lt_radius
  Ξ dirCode_eq
  ϴ Model.wa, Model.wb, chainModel
  Ξ C.sideWalk_vtx_wrap, C.sideWalk_vtx_tour _ le_rfl, C.sideTour_two_m
  exact dirOf_lt ht

/-- The walk vertices of a tour edge. -/
theorem chain_dirCode_tour {i : ℕ} (hi : i < 2 * C.m) :
    dirCode (chainModel C) (i + 6) =
      dirOf (C.vertex (C.sideIdx C.sideBeta i)).2 (C.vertex (C.sideIdx C.sideBeta (i + 1))).2 := by
  Ξ dirCode_eq
  ϴ Model.wa, Model.wb, chainModel
  rw [C.sideWalk_n, Nat.mod_eq_of_lt (⋄), show i + 6 + 1 = (i + 1) + 6 by ring,
    C.sideWalk_vtx_tour _ (⋄), C.sideWalk_vtx_tour _ (⋄)]
  rfl

/-- The tour position of step `i`, by one conditional subtraction. -/
theorem tour_mod {S i m : ℕ} (hS : S ≤ 2 * m) (hi : i < 2 * m) :
    (S + i) % (2 * m) = if i < 2 * m - S then S + i else i - (2 * m - S) := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt (⋄)
  · Ξ Nat.mod_eq_sub_mod (⋄), Nat.mod_eq_of_lt (⋄)
    omega

/-- The tour vertex index by one comparison. -/
theorem sideE_eq (m j : ℕ) : sideE m j = if m < j then 2 * m - j else j := by
  unfold sideE; split_ifs <;> omega

/-- **The chain vertices at the ends of tour edge `i`**. -/
theorem sideIdx_pair (i : ℕ) :
    C.sideIdx C.sideBeta i = sideE C.m ((C.sideS C.sideBeta + i) % (2 * C.m)) ∧
      C.sideIdx C.sideBeta (i + 1) = sideE C.m ((C.sideS C.sideBeta + i) % (2 * C.m) + 1) :=
  ⟨C.sideIdx_eq _ _, C.sideIdx_succ _ _⟩

/-- A vertex of the chain is the host point of index `(s + k) mod N`. -/
theorem chain_vertex_host {Q : Polygon} {H : Host} (hP : C.P = H.poly Q) (k : ℕ) {sp : SymPt}
    (hsp : (H.pts Q.n)[(C.s + k) % C.P.n]? = some sp) : C.vertex k = sp.eval Q := by
  unfold Chain.vertex Chain.edgeIdx
  generalize (C.s + k) % C.P.n = q at hsp ⊢
  Ξ hP
  unfold Host.poly Polygon.vtx
  Ξ List.getD_eq_getElem?_getD, List.getElem?_map, hsp
  rfl

end walk

/-! ## The program -/

/-- Read the chain descriptor at `lr 0 + 1`: host handle (`lr 60`), start `s` (`lr 52`), edges
`m` (`lr 53`), top index `T` (`lr 54`), orientation bit (`lr 55`); constants `1 … 6`. -/
def chHead : Stmt := block [.constN 50032 1, .addN 50050 50000 50032, .loadN 50060 50050,
  .addN 50050 50050 50032, .loadN 50052 50050, .addN 50050 50050 50032, .loadN 50053 50050,
  .addN 50050 50050 50032, .loadN 50054 50050, .addN 50050 50050 50032, .loadN 50055 50050,
  .constN 50082 2, .constN 50083 3, .constN 50084 4, .constN 50085 5, .constN 50081 6]

/-- Set the direction code. -/
def setDir (v : ℕ) : Stmt := .instr (.constN 10502 v)

/-- The box and slit edges `0 … 5`. -/
def smallDir : Stmt :=
  .ifLtN 50002 50032 (setDir 0) (.ifLtN 50002 50082 (setDir 2) (.ifLtN 50002 50083 (setDir 0)
    (.ifLtN 50002 50084 (setDir 1) (.ifLtN 50002 50085 (setDir 0) (setDir 2)))))

/-- The chain vertex indices `k₁ = sideE m j` (`lr 78`), `k₂ = sideE m (j + 1)` (`lr 79`) of
tour edge `i = lr 56`, `j = (S + i) mod 2m`. -/
def chIdx : Stmt :=
  .seq (block [.addN 50058 50053 50053])
    (.seq (.ifLtN 50055 50032 (.instr (.subN 50059 50058 50054))
        (.ifLtN 50032 50055 (.instr (.subN 50059 50058 50054)) (.instr (.copyN 50059 50054))))
      (.seq (.instr (.subN 50089 50058 50059))
        (.seq (.ifLtN 50056 50089 (.instr (.addN 50077 50059 50056))
            (.instr (.subN 50077 50056 50089)))
          (.seq (.ifLtN 50053 50077 (.instr (.subN 50078 50058 50077))
              (.instr (.copyN 50078 50077)))
            (.seq (.instr (.addN 50090 50077 50032))
              (.ifLtN 50053 50090 (.instr (.subN 50079 50058 50090))
                (.instr (.copyN 50079 50090))))))))

/-- The host point of index `(s + lr 91) mod N` (`N` in `lr 87`) into `lr 46 … lr 48`. -/
def hostPt : Stmt :=
  .seq (.instr (.addN 50071 50052 50091))
    (.seq (.ifLtN 50071 50087 .skip (.instr (.subN 50071 50071 50087))) lookStmt)

/-- A tour edge: the two host points, then the height comparison. -/
def chGeneral : Stmt :=
  .seq chIdx (.seq cntStmt (.seq (block [.copyN 50087 50063, .copyN 50091 50078])
    (.seq hostPt (.seq (block [.copyN 50040 50046, .copyN 50041 50047, .copyN 50042 50048,
        .copyN 50091 50079])
      (.seq hostPt (.seq (block [.copyN 50043 50046, .copyN 50044 50047, .copyN 50045 50048])
        dirTail))))))

/-- **The direction procedure of the chain model.** -/
def chainDir : Stmt :=
  .seq chHead (.ifLtN 50002 50081 smallDir
    (.seq (block [.subN 50056 50002 50081, .subN 50057 50056 50053])
      (.ifLtN 50057 50053 chGeneral (setDir 1))))

theorem wr_chainDir : wr Bdir chainDir = true := ⌖

theorem wr_hostPt : wr Bhost hostPt = true := ⌖

/-- The host point of index `(s + k) mod N`. -/
theorem hostPt_exec {P : Polygon} {W Hh s k : ℕ} {H : Host} {m : ℕ → ℕ} (c : Config)
    (E : HostEnv W Hh H.length m c) (hH : HostAt m Hh H) (hwf : HostWF P.n H) (hW : P.n ≤ W)
    (haW : Hh + 3 * H.length + 4 ≤ W) (hNW : 2 * (H.pts P.n).length ≤ W)
    (h52 : c.nreg 50052 = s) (h87 : c.nreg 50087 = (H.pts P.n).length) (h91 : c.nreg 50091 = k)
    (hs : s < (H.pts P.n).length) (hk : k < (H.pts P.n).length) :
    ∃ c' k', Exec P W hostPt c c' k' ∧ k' ≤ 27 * H.length + 9 ∧ FrameB Bhost c c' ∧
      HostEnv W Hh H.length m c' ∧
      ∃ sp, (H.pts P.n)[(s + k) % (H.pts P.n).length]? = some sp ∧ SymPtIn c' 50046 sp := by
  have hw := E.wb
  set N := (H.pts P.n).length
  have e₁ := Exec.addN (P := P) hw 50071 50052 50091 (by rw [h52, h91]; omega)
  have w₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, h71, E₂⟩ : ∃ c₂ k₂, Exec P W
      (.ifLtN 50071 50087 .skip (.instr (.subN 50071 50071 50087)))
      { c with nreg := upd c.nreg 50071 (c.nreg 50052 + c.nreg 50091) } c₂ k₂ ∧ k₂ ≤ 3 ∧
      c₂.nreg 50071 = (s + k) % N ∧ HostEnv W Hh H.length m c₂ := by
    by_cases hlt : s + k < N
    · refine spec_ifLtN_true (by config_simp; rw [h52, h91, h87]; exact hlt)
        (spec_skip w₁ ⟨⋄, by config_simp; rw [h52, h91, Nat.mod_eq_of_lt hlt], ?_⟩)
      exact ⟨w₁, by config_simp; exact E.h60, by config_simp; exact E.h61,
        by config_simp; exact E.h67, by config_simp; exact E.h68, by config_simp; exact E.h69,
        E.mem⟩
    · refine spec_ifLtN_false (by config_simp; rw [h52, h91, h87]; exact hlt)
        (spec_instr (Exec.subN w₁ _ _ _) fun w₂ => ⟨⋄, ?_, ?_⟩)
      · config_simp
        Ξ h52, h91, h87, Nat.mod_eq_sub_mod (⋄), Nat.mod_eq_of_lt (⋄)
      · exact ⟨w₂, by config_simp; exact E.h60, by config_simp; exact E.h61,
          by config_simp; exact E.h67, by config_simp; exact E.h68, by config_simp; exact E.h69,
          E.mem⟩
  have hpN : (s + k) % N < N := Nat.mod_lt _ (⋄)
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, E₃, -, sp, hsp, hin⟩ := look_exec (P := P) c₂ E₂ h71 hH hwf hW haW
    (⋄) hpN
  have ex : Exec P W hostPt c c₃ (1 + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  exact ⟨c₃, _, ex, ⋄, exec_frameB ex wr_hostPt, E₃, sp, hsp, hin⟩

/-- **The chain vertex indices of tour edge `i`.** -/
theorem chIdx_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {m T b i : ℕ}
    (h32 : c.nreg 50032 = 1) (h53 : c.nreg 50053 = m) (h54 : c.nreg 50054 = T)
    (h55 : c.nreg 50055 = b) (h56 : c.nreg 50056 = i) (hi : i < 2 * m) (hT : T ≤ m)
    (h2m : 2 * m ≤ W) :
    ∃ c' k, Exec P W chIdx c c' k ∧ k ≤ 20 ∧
      c'.nreg 50078 = sideE m (((if b = 1 then T else 2 * m - T) + i) % (2 * m)) ∧
      c'.nreg 50079 = sideE m (((if b = 1 then T else 2 * m - T) + i) % (2 * m) + 1) ∧
      FrameB (Bl [50058, 50059, 50089, 50077, 50078, 50090, 50079]) c c' := by
  set S := (if b = 1 then T else 2 * m - T) with hS
  have hS2 : S ≤ 2 * m := by rw [hS]; split_ifs <;> omega
  -- `2m`
  have e₁ := Exec.addN (P := P) hw 50058 50053 50053 (by rw [h53]; omega)
  set c₁ : Config := { c with nreg := upd c.nreg 50058 (c.nreg 50053 + c.nreg 50053) } with hc₁
  have w₁ := e₁.wb_right
  have q58 : c₁.nreg 50058 = 2 * m := by rw [hc₁]; config_simp; rw [h53]; ring
  have q : ∀ r, r ≠ 50058 → c₁.nreg r = c.nreg r := fun r hr => by rw [hc₁]; simp [hr]
  -- `S`
  obtain ⟨c₂, k₂, e₂, hk₂, q59, r₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 50055 50032
      (.instr (.subN 50059 50058 50054))
      (.ifLtN 50032 50055 (.instr (.subN 50059 50058 50054)) (.instr (.copyN 50059 50054))))
      c₁ c₂ k₂ ∧ k₂ ≤ 5 ∧ c₂.nreg 50059 = S ∧ ∀ r, r ≠ 50059 → c₂.nreg r = c₁.nreg r := by
    have b32 : c₁.nreg 50032 = 1 := by rw [q _ (⋄), h32]
    have b55 : c₁.nreg 50055 = b := by rw [q _ (⋄), h55]
    have b54 : c₁.nreg 50054 = T := by rw [q _ (⋄), h54]
    by_cases h0 : b < 1
    · refine spec_ifLtN_true (by rw [b55, b32]; exact h0)
        (spec_instr (Exec.subN w₁ _ _ _) fun _ => ⟨⋄, ?_, fun r hr => by simp [hr]⟩)
      config_simp; rw [q58, b54, hS, ite_eq_right (⋄)]
    · refine spec_ifLtN_false (by rw [b55, b32]; exact h0) ?_
      by_cases h2 : 1 < b
      · refine spec_ifLtN_true (by rw [b55, b32]; exact h2)
          (spec_instr (Exec.subN w₁ _ _ _) fun _ => ⟨⋄, ?_, fun r hr => by simp [hr]⟩)
        config_simp; rw [q58, b54, hS, ite_eq_right (⋄)]
      · refine spec_ifLtN_false (by rw [b55, b32]; exact h2)
          (spec_instr (Exec.copyN w₁ _ _) fun _ => ⟨⋄, ?_, fun r hr => by simp [hr]⟩)
        config_simp; rw [b54, hS, ite_eq_left (⋄)]
  have w₂ := e₂.wb_right
  have g := fun r (h1 : r ≠ 50059) (h2 : r ≠ 50058) => (r₂ r h1).trans (q r h2)
  -- `2m - S`, `j`
  have e₃ := Exec.subN (P := P) w₂ 50089 50058 50059
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50089 (c₂.nreg 50058 - c₂.nreg 50059) }
    with hc₃
  have w₃ := e₃.wb_right
  have t89 : c₃.nreg 50089 = 2 * m - S := by
    rw [hc₃]; config_simp; rw [q59, r₂ _ (⋄), q58]
  have t : ∀ r, r ≠ 50089 → c₃.nreg r = c₂.nreg r := fun r hr => by rw [hc₃]; simp [hr]
  have t56 : c₃.nreg 50056 = i := by rw [t _ (⋄), g _ (by omega) (by omega), h56]
  have t59 : c₃.nreg 50059 = S := by rw [t _ (⋄), q59]
  obtain ⟨c₄, k₄, e₄, hk₄, j4, r₄⟩ : ∃ c₄ k₄, Exec P W (.ifLtN 50056 50089
      (.instr (.addN 50077 50059 50056)) (.instr (.subN 50077 50056 50089))) c₃ c₄ k₄ ∧
      k₄ ≤ 3 ∧ c₄.nreg 50077 = (S + i) % (2 * m) ∧ ∀ r, r ≠ 50077 → c₄.nreg r = c₃.nreg r := by
    Ξ tour_mod hS2 hi
    by_cases hc : i < 2 * m - S
    · refine spec_ifLtN_true (by rw [t56, t89]; exact hc) (spec_instr (Exec.addN w₃ _ _ _
        (by rw [t59, t56]; omega)) fun _ => ⟨⋄, ?_, fun r hr => by simp [hr]⟩)
      config_simp; rw [t59, t56, ite_eq_left hc]
    · refine spec_ifLtN_false (by rw [t56, t89]; exact hc) (spec_instr (Exec.subN w₃ _ _ _)
        fun _ => ⟨⋄, ?_, fun r hr => by simp [hr]⟩)
      config_simp; rw [t89, t56, ite_eq_right hc]
  have w₄ := e₄.wb_right
  set j := (S + i) % (2 * m) with hj
  have hjm : j < 2 * m := Nat.mod_lt _ (⋄)
  have u53 : c₄.nreg 50053 = m := by
    rw [r₄ _ (⋄), t _ (by omega), g _ (by omega) (by omega), h53]
  have u58 : c₄.nreg 50058 = 2 * m := by
    rw [r₄ _ (⋄), t _ (by omega), r₂ _ (by omega), q58]
  have u32 : c₄.nreg 50032 = 1 := by
    rw [r₄ _ (⋄), t _ (by omega), g _ (by omega) (by omega), h32]
  -- `k₁`
  obtain ⟨c₅, k₅, e₅, hk₅, k78, r₅⟩ : ∃ c₅ k₅, Exec P W (.ifLtN 50053 50077
      (.instr (.subN 50078 50058 50077)) (.instr (.copyN 50078 50077))) c₄ c₅ k₅ ∧
      k₅ ≤ 3 ∧ c₅.nreg 50078 = sideE m j ∧ ∀ r, r ≠ 50078 → c₅.nreg r = c₄.nreg r := by
    Ξ sideE_eq
    by_cases hc : m < j
    · refine spec_ifLtN_true (by rw [u53, j4]; exact hc) (spec_instr (Exec.subN w₄ _ _ _)
        fun _ => ⟨⋄, ?_, fun r hr => by simp [hr]⟩)
      config_simp; rw [u58, j4, ite_eq_left hc]
    · refine spec_ifLtN_false (by rw [u53, j4]; exact hc) (spec_instr (Exec.copyN w₄ _ _)
        fun _ => ⟨⋄, ?_, fun r hr => by simp [hr]⟩)
      config_simp; rw [j4, ite_eq_right hc]
  have w₅ := e₅.wb_right
  have e₆ := Exec.addN (P := P) w₅ 50090 50077 50032
    (by rw [r₅ _ (⋄), r₅ _ (by omega), j4, u32]; omega)
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg 50090 (c₅.nreg 50077 + c₅.nreg 50032) }
    with hc₆
  have w₆ := e₆.wb_right
  have v90 : c₆.nreg 50090 = j + 1 := by
    rw [hc₆]; config_simp; rw [r₅ _ (⋄), r₅ _ (by omega), j4, u32]
  have v : ∀ r, r ≠ 50090 → c₆.nreg r = c₅.nreg r := fun r hr => by rw [hc₆]; simp [hr]
  have v53 : c₆.nreg 50053 = m := by rw [v _ (⋄), r₅ _ (by omega), u53]
  have v58 : c₆.nreg 50058 = 2 * m := by rw [v _ (⋄), r₅ _ (by omega), u58]
  -- `k₂`
  obtain ⟨c₇, k₇, e₇, hk₇, k79, r₇⟩ : ∃ c₇ k₇, Exec P W (.ifLtN 50053 50090
      (.instr (.subN 50079 50058 50090)) (.instr (.copyN 50079 50090))) c₆ c₇ k₇ ∧
      k₇ ≤ 3 ∧ c₇.nreg 50079 = sideE m (j + 1) ∧ ∀ r, r ≠ 50079 → c₇.nreg r = c₆.nreg r := by
    Ξ sideE_eq
    by_cases hc : m < j + 1
    · refine spec_ifLtN_true (by rw [v53, v90]; exact hc) (spec_instr (Exec.subN w₆ _ _ _)
        fun _ => ⟨⋄, ?_, fun r hr => by simp [hr]⟩)
      config_simp; rw [v58, v90, ite_eq_left hc]
    · refine spec_ifLtN_false (by rw [v53, v90]; exact hc) (spec_instr (Exec.copyN w₆ _ _)
        fun _ => ⟨⋄, ?_, fun r hr => by simp [hr]⟩)
      config_simp; rw [v90, ite_eq_right hc]
  have ex : Exec P W chIdx c c₇ ((1 + 0) + (k₂ + (1 + (k₄ + (k₅ + (1 + k₇)))))) :=
    .seq (.seq e₁ (.skip w₁)) (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇)))))
  refine ⟨c₇, _, ex, ⋄, by rw [r₇ _ (by omega), v _ (by omega), k78], k79,
    exec_frameB ex (⌖)⟩

/-- The box and slit edges. -/
theorem smallDir_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W)
    (h32 : c.nreg 50032 = 1) (h82 : c.nreg 50082 = 2) (h83 : c.nreg 50083 = 3)
    (h84 : c.nreg 50084 = 4) (h85 : c.nreg 50085 = 5) (he : c.nreg 50002 < 6) :
    ∃ c' k, Exec P W smallDir c c' k ∧ k ≤ 12 ∧
      c'.nreg 10502 = (if c.nreg 50002 = 1 ∨ c.nreg 50002 = 5 then 2
        else if c.nreg 50002 = 3 then 1 else 0) := by
  unfold smallDir setDir
  set e := c.nreg 50002 with he'
  have fin : ∀ v, v ≤ 2 → ∀ k : ℕ, k ≤ 10 → (if e = 1 ∨ e = 5 then 2 else if e = 3 then 1 else 0) = v →
      ∃ c' k', Exec P W (.instr (.constN 10502 v)) c c' k' ∧ k' + k ≤ 12 ∧
        c'.nreg 10502 = (if e = 1 ∨ e = 5 then 2 else if e = 3 then 1 else 0) :=
    fun v hv k hk hval => ⟨_, 1, Exec.constN hw _ _ (⋄), ⋄,
      by config_simp; exact hval.symm⟩
  by_cases t0 : e < 1
  · obtain ⟨c', k', ex, hk, hr⟩ := fin 0 (⋄) 1 (⋄) (by split_ifs <;> omega)
    exact ⟨c', k' + 1, .ifLtN_true (by rw [h32]; exact t0) ex, ⋄, hr⟩
  by_cases t1 : e < 2
  · obtain ⟨c', k', ex, hk, hr⟩ := fin 2 (⋄) 3 (⋄) (by split_ifs <;> omega)
    exact ⟨c', k' + 1 + 2, .ifLtN_false (by rw [h32]; exact t0)
      (.ifLtN_true (by rw [h82]; exact t1) ex), ⋄, hr⟩
  by_cases t2 : e < 3
  · obtain ⟨c', k', ex, hk, hr⟩ := fin 0 (⋄) 5 (⋄) (by split_ifs <;> omega)
    exact ⟨c', k' + 1 + 2 + 2, .ifLtN_false (by rw [h32]; exact t0)
      (.ifLtN_false (by rw [h82]; exact t1) (.ifLtN_true (by rw [h83]; exact t2) ex)),
      ⋄, hr⟩
  by_cases t3 : e < 4
  · obtain ⟨c', k', ex, hk, hr⟩ := fin 1 (⋄) 7 (⋄) (by split_ifs <;> omega)
    exact ⟨c', k' + 1 + 2 + 2 + 2, .ifLtN_false (by rw [h32]; exact t0)
      (.ifLtN_false (by rw [h82]; exact t1) (.ifLtN_false (by rw [h83]; exact t2)
        (.ifLtN_true (by rw [h84]; exact t3) ex))), ⋄, hr⟩
  by_cases t4 : e < 5
  · obtain ⟨c', k', ex, hk, hr⟩ := fin 0 (⋄) 9 (⋄) (by split_ifs <;> omega)
    exact ⟨c', k' + 1 + 2 + 2 + 2 + 2, .ifLtN_false (by rw [h32]; exact t0)
      (.ifLtN_false (by rw [h82]; exact t1) (.ifLtN_false (by rw [h83]; exact t2)
        (.ifLtN_false (by rw [h84]; exact t3) (.ifLtN_true (by rw [h85]; exact t4) ex)))),
      ⋄, hr⟩
  · obtain ⟨c', k', ex, hk, hr⟩ := fin 2 (⋄) 10 (⋄) (by split_ifs <;> omega)
    exact ⟨c', k' + 2 + 2 + 2 + 2 + 2, .ifLtN_false (by rw [h32]; exact t0)
      (.ifLtN_false (by rw [h82]; exact t1) (.ifLtN_false (by rw [h83]; exact t2)
        (.ifLtN_false (by rw [h84]; exact t3) (.ifLtN_false (by rw [h85]; exact t4) ex)))),
      ⋄, hr⟩

/-- **A tour edge**: the two host points and their height comparison. -/
theorem chGeneral_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {H : Host} {Hh s m T b i : ℕ} (hH : HostAt c.nmem Hh H)
    (hwf : HostWF P.n H) (haW : Hh + 3 * H.length + 4 ≤ W)
    (hNW : 2 * (H.pts P.n).length ≤ W) (hs : s < (H.pts P.n).length)
    (hmN : m < (H.pts P.n).length) (hT : T ≤ m) (hi : i < 2 * m)
    (h32 : c.nreg 50032 = 1) (h60 : c.nreg 50060 = Hh) (h52 : c.nreg 50052 = s)
    (h53 : c.nreg 50053 = m) (h54 : c.nreg 50054 = T) (h55 : c.nreg 50055 = b)
    (h56 : c.nreg 50056 = i) :
    ∃ c' k, Exec P W chGeneral c c' k ∧ k ≤ 70 * H.length + 560 ∧
      ∃ sp₁ sp₂ : SymPt,
        (H.pts P.n)[(s + sideE m (((if b = 1 then T else 2 * m - T) + i) % (2 * m))) %
          (H.pts P.n).length]? = some sp₁ ∧
        (H.pts P.n)[(s + sideE m (((if b = 1 then T else 2 * m - T) + i) % (2 * m) + 1)) %
          (H.pts P.n).length]? = some sp₂ ∧
        c'.nreg 10502 = dirOf (sp₁.eval (Qof P)).2 (sp₂.eval (Qof P)).2 := by
  set N := (H.pts P.n).length with hNdef
  have hn0 : 0 < P.n := by have := hG.1.1; omega
  have hLt := hostWF_pts hwf hn0
  -- indices
  obtain ⟨c₁, k₁, e₁, hk₁, k78, k79, f₁⟩ := chIdx_exec (P := P) c hw h32 h53 h54 h55 h56 hi hT
    (⋄)
  have w₁ := e₁.wb_right
  set j := ((if b = 1 then T else 2 * m - T) + i) % (2 * m) with hj
  have hjm : j < 2 * m := Nat.mod_lt _ (⋄)
  have hk1 : sideE m j ≤ m := Chain.sideE_le (⋄)
  have hk2 : sideE m (j + 1) ≤ m := Chain.sideE_le (⋄)
  have g₁ := fun r (hr : Bl [50058, 50059, 50089, 50077, 50078, 50090, 50079] r = false) =>
    f₁.1 r hr
  -- the count
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, n63, E₂⟩ := cnt_exec (P := P) (n := P.n) c₁ w₁
    (by rw [f₁.2.2.1]; exact hH) ((g₁ _ (⌖)).trans h60) haW (by omega)
  have g₂ := fun r (hr : Bhost r = false) => f₂.1 r hr
  -- first point
  obtain ⟨c₃, k₃, e₃, hk₃, q87, q91, r₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN 50087 50063, .copyN 50091 50078]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
      c₃.nreg 50087 = N ∧ c₃.nreg 50091 = sideE m j ∧
      ∀ r, r ≠ 50087 → r ≠ 50091 → c₃.nreg r = c₂.nreg r := by
    have hw₂ := e₂.wb_right
    exec_block
    refine ⟨rfl, by config_simp; exact n63, ?_, fun r h1 h2 => ⊚ h1, h2⟩
    config_simp; rw [g₂ _ (⌖), k78]
  have E₃ : HostEnv W Hh H.length c.nmem c₃ :=
    ⟨e₃.wb_right, by rw [r₃ _ (⋄) (by omega), E₂.h60],
      by rw [r₃ _ (⋄) (by omega), E₂.h61], by rw [r₃ _ (by omega) (by omega), E₂.h67],
      by rw [r₃ _ (⋄) (by omega), E₂.h68], by rw [r₃ _ (by omega) (by omega), E₂.h69],
      by rw [(exec_frameB e₃ (B := Bl [50087, 50091]) (⌖)).2.2.1, E₂.mem,
        f₁.2.2.1]⟩
  have s₃ : c₃.nreg 50052 = s := by
    rw [r₃ _ (⋄) (by omega), g₂ _ (by decide), g₁ _ (by decide), h52]
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, E₄, sp₁, hsp₁, in₁⟩ := hostPt_exec (P := P) c₃ E₃ hH hwf
    (⋄) haW hNW s₃ q87 q91 hs (by omega)
  have g₄ := fun r (hr : Bhost r = false) => f₄.1 r hr
  -- second point
  obtain ⟨c₅, k₅, e₅, hk₅, a₅, q91', r₅⟩ : ∃ c₅ k₅, Exec P W
      (block [.copyN 50040 50046, .copyN 50041 50047, .copyN 50042 50048, .copyN 50091 50079])
      c₄ c₅ k₅ ∧ k₅ = 4 ∧ SymPtIn c₅ 50040 sp₁ ∧ c₅.nreg 50091 = sideE m (j + 1) ∧
      ∀ r, r ≠ 50040 → r ≠ 50041 → r ≠ 50042 → r ≠ 50091 → c₅.nreg r = c₄.nreg r := by
    have hw₄ := e₄.wb_right
    exec_block
    refine ⟨rfl, symPtIn_copy in₁ (by config_simp) (by config_simp) (by config_simp), ?_,
      fun r h1 h2 h3 h4 => ⊚ h1, h2, h3, h4⟩
    config_simp
    rw [g₄ _ (⌖), r₃ _ (by omega) (by omega), g₂ _ (by decide), k79]
  have E₅ : HostEnv W Hh H.length c.nmem c₅ :=
    ⟨e₅.wb_right, by rw [r₅ _ (⋄) (by omega) (by omega) (by omega), E₄.h60],
      by rw [r₅ _ (⋄) (by omega) (by omega) (by omega), E₄.h61],
      by rw [r₅ _ (⋄) (by omega) (by omega) (by omega), E₄.h67],
      by rw [r₅ _ (⋄) (by omega) (by omega) (by omega), E₄.h68],
      by rw [r₅ _ (⋄) (by omega) (by omega) (by omega), E₄.h69],
      by rw [(exec_frameB e₅ (B := Bl [50040, 50041, 50042, 50091]) (⌖)).2.2.1,
        E₄.mem]⟩
  have s₅ : c₅.nreg 50052 = s := by
    rw [r₅ _ (⋄) (by omega) (by omega) (by omega), g₄ _ (by decide), s₃]
  have n₅ : c₅.nreg 50087 = N := by
    rw [r₅ _ (⋄) (by omega) (by omega) (by omega), g₄ _ (by decide), q87]
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, -, sp₂, hsp₂, in₂⟩ := hostPt_exec (P := P) c₅ E₅ hH hwf
    (⋄) haW hNW s₅ n₅ q91' hs (by omega)
  have a₆ : SymPtIn c₆ 50040 sp₁ := symPtIn_copy a₅ (f₆.1 _ (⌖)) (f₆.1 _ (by decide))
    (f₆.1 _ (⌖))
  obtain ⟨c₇, k₇, e₇, hk₇, a₇, b₇⟩ : ∃ c₇ k₇, Exec P W
      (block [.copyN 50043 50046, .copyN 50044 50047, .copyN 50045 50048]) c₆ c₇ k₇ ∧ k₇ = 3 ∧
      SymPtIn c₇ 50040 sp₁ ∧ SymPtIn c₇ 50043 sp₂ := by
    have hw₆ := e₆.wb_right
    exec_block
    exact ⟨rfl, symPtIn_copy a₆ (by config_simp) (by config_simp) (by config_simp),
      symPtIn_copy in₂ (by config_simp) (by config_simp) (by config_simp)⟩
  have l₁ : sp₁.Lt P.n := hLt _ (List.mem_of_getElem? hsp₁)
  have l₂ : sp₂.Lt P.n := hLt _ (List.mem_of_getElem? hsp₂)
  obtain ⟨c₈, k₈, e₈, hk₈, -, d₈⟩ := dirTail_exec (P := P) hG hW c₇ e₇.wb_right l₁ l₂ a₇ b₇
  refine ⟨c₈, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈)))))), ?_,
    sp₁, sp₂, hsp₁, hsp₂, d₈⟩
  omega

/-- **The direction procedure of the chain model** (at most `70 |H| + 600` steps). -/
theorem chainDir_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {H : Host} {C : Chain}
    (hC : ChainDescAt c.nmem (c.nreg 50000 + 1) (Qof P) H C)
    (hDW : c.nreg 50000 + 6 ≤ W) (hHW : c.nmem (c.nreg 50000 + 1) + 3 * H.length + 4 ≤ W)
    (hwf : HostWF P.n H) (hs : C.s < C.P.n) (hNW : 2 * C.P.n ≤ W)
    (he : c.nreg 50002 < 2 * C.m + 7) :
    ∃ c' k, Exec P W chainDir c c' k ∧ k ≤ 70 * H.length + 600 ∧ FrameB Bdir c c' ∧
      c'.nreg 10502 = dirCode (chainModel C) (c.nreg 50002) := by
  set D := c.nreg 50000 with hD
  set e := c.nreg 50002 with he'
  obtain ⟨hHost, hP, hs', hm', hT', hb'⟩ := hC
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hNlen : C.P.n = (H.pts P.n).length := by
    Ξ hP, ← hQn
    show ((H.pts (Qof P).n).map (SymPt.eval (Qof P))).length = _
    Ξ List.length_map
  have hmN := C.m_lt
  have hT := C.topIdx_le
  have hm1 := C.one_le
  -- the header
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W chHead c c₁ k₁ ∧ k₁ = 16 ∧
      (c₁.nreg 50032 = 1 ∧ c₁.nreg 50060 = c.nmem (D + 1) ∧ c₁.nreg 50052 = C.s ∧
        c₁.nreg 50053 = C.m ∧ c₁.nreg 50054 = C.topIdx ∧ c₁.nreg 50055 = c.nmem (D + 5) ∧
        c₁.nreg 50081 = 6 ∧ c₁.nreg 50082 = 2 ∧ c₁.nreg 50083 = 3 ∧ c₁.nreg 50084 = 4 ∧
        c₁.nreg 50085 = 5 ∧ c₁.nreg 50002 = e ∧ c₁.nmem = c.nmem) := by
    unfold chHead
    exec_block
    all_goals try omega
    all_goals try (config_simp; omega)
    refine ⟨rfl, ?_⟩
    config_simp
    exact ⟨rfl, hs', hm', hT', rfl, rfl⟩
  obtain ⟨q32, q60, q52, q53, q54, q55, q81, q82, q83, q84, q85, q02, qm⟩ := q
  have w₁ := e₁.wb_right
  by_cases hsm : e < 6
  · obtain ⟨c₂, k₂, e₂, hk₂, d₂⟩ := smallDir_exec (P := P) c₁ w₁ (⋄) q32 q82 q83 q84 q85
      (by rw [q02]; exact hsm)
    have ex : Exec P W chainDir c c₂ (k₁ + (k₂ + 1)) :=
      .seq e₁ (.ifLtN_true (by rw [q02, q81]; exact hsm) e₂)
    refine ⟨c₂, _, ex, ⋄, exec_frameB ex wr_chainDir, ?_⟩
    Ξ d₂, q02, chain_dirCode_small C hsm
  -- the tour and the closing edge
  obtain ⟨c₂, k₂, e₂, hk₂, q56, q57, r₂⟩ : ∃ c₂ k₂, Exec P W
      (block [.subN 50056 50002 50081, .subN 50057 50056 50053]) c₁ c₂ k₂ ∧ k₂ = 2 ∧
      c₂.nreg 50056 = e - 6 ∧ c₂.nreg 50057 = e - 6 - C.m ∧
      ∀ r, r ≠ 50056 → r ≠ 50057 → c₂.nreg r = c₁.nreg r := by
    exec_block
    refine ⟨rfl, by config_simp; rw [q02, q81], by config_simp; rw [q02, q81, q53],
      fun r h1 h2 => ⊚ h1, h2⟩
  have w₂ := e₂.wb_right
  have p53 : c₂.nreg 50053 = C.m := Ρ r₂ _ (⋄) (⋄), q53
  by_cases hg : e - 6 - C.m < C.m
  · have hi : e - 6 < 2 * C.m := ⋄
    have hH₂ : HostAt c₂.nmem (c.nmem (D + 1)) H := by
      have f₂ := exec_frameB e₂ (B := Bl [50056, 50057]) (⌖)
      rw [f₂.2.2.1, qm]; exact hHost
    obtain ⟨c₃, k₃, e₃, hk₃, sp₁, sp₂, hsp₁, hsp₂, d₃⟩ := chGeneral_exec (P := P) hG hW c₂ w₂
      hH₂ hwf hHW (by rw [← hNlen]; exact hNW) (by rw [← hNlen]; exact hs)
      (by rw [← hNlen]; exact hmN) hT hi (Ρ r₂ _ (⋄) (⋄), q32)
      (Ρ r₂ _ (⋄) (⋄), q60) (Ρ r₂ _ (⋄) (⋄), q52) p53
      (Ρ r₂ _ (⋄) (⋄), q54) (Ρ r₂ _ (⋄) (⋄), q55) q56
    have ex : Exec P W chainDir c c₃ (k₁ + (k₂ + (k₃ + 1) + 2)) :=
      .seq e₁ (.ifLtN_false (by rw [q02, q81]; exact hsm)
        (.seq e₂ (.ifLtN_true (by rw [q57, p53]; exact hg) e₃)))
    refine ⟨c₃, _, ex, ⋄, exec_frameB ex wr_chainDir, ?_⟩
    Ξ d₃, show e = (e - 6) + 6 by omega, chain_dirCode_tour C hi
    obtain ⟨i1, i2⟩ := sideIdx_pair C (e - 6)
    have hS : (if c.nmem (D + 5) = 1 then C.topIdx else 2 * C.m - C.topIdx) =
        C.sideS C.sideBeta := by
      unfold Chain.sideS
      by_cases hb : C.sideBeta = true
      · Ξ ite_eq_left (hb'.2 hb), ite_eq_left hb
      · Ξ ite_eq_right (mt hb'.1 hb), ite_eq_right hb
    Ξ' hS, ← hNlen, ← i1 at hsp₁
    Ξ' hS, ← hNlen, ← i2 at hsp₂
    rw [chain_vertex_host C hP _ (by rw [hQn]; exact hsp₁),
      chain_vertex_host C hP _ (by rw [hQn]; exact hsp₂)]
  · have hlast : e = 2 * C.m + 6 := ⋄
    have ex : Exec P W chainDir c { c₂ with nreg := upd c₂.nreg 10502 1 } (k₁ + (k₂ + (1 + 2) + 2)) :=
      .seq e₁ (.ifLtN_false (by rw [q02, q81]; exact hsm)
        (.seq e₂ (.ifLtN_false (by rw [q57, p53]; exact hg) (Exec.constN w₂ _ _ (⋄)))))
    refine ⟨_, _, ex, ⋄, exec_frameB ex wr_chainDir, ?_⟩
    config_simp
    Ξ hlast, chain_dirCode_last

end

end NFLoc

end Chazelle.Core
