module

public import Chazelle.Golf

public import Chazelle.Core.ShotListTop

/-!
# Shooting at a list of arcs with holes (shared with WP-E): the contract

`shotList sh R` shoots the horizontal ray from an origin at a list of arcs of a chain model, with
the walk edges through the origin removed ("holes"), using the ray shooter `sh`, and reports the
first hit.  It is shared by the sweep (WP-D) and the restoration (WP-E): both shoot from walk
points into the arcs of a region.

## Registers (a block `R … R + 299` in one band of the caller, `RegsOK R`)

| register | content |
|---|---|
| `R` | model descriptor of the chain model (kind `0`, the chain descriptor at `R + 1`) |
| `R + 1`, `R + 2` | base `AB` and number `K` of the arcs: four words each (start edge, start height code, end edge, end height code) |
| `R + 3 … R + 5` | the origin (an `Origin`, `OriginIn`) |
| `R + 6` | the direction code (`dirOf`) |
| `R + 7`, `R + 8` | the weight bound `γ` and the context handle of the shooter |
| `R + 9` | the number `H ≤ 3` of holes |
| `R + 10 … R + 15` | the holes: pairs of walk vertices `(x, y)`, the open key interval `(x, y)` |
| `R + 20` | output: `1` iff there is a hit |
| `R + 21`, `R + 22` | output: the hit position |

Registers `R + 16 … R + 299` are scratch; the oracle bands may change (the shooter, the
primitives).  The arcs are read below the allocator; nothing is allocated except by the shooter.

## Contract (`shotList_meets`)

Precondition (`ShotPre`): the shooter's context with room for `γ`, a well-formed chain model
descriptor, arcs with good ends (`PieceOK`: normalised positions — height code `0` exactly for
parameter `0` — in range, each a walk vertex or an inner point) of weight `≤ γ`, proper holes in
range, the origin as for `ShooterOK` with `|y| < radius`, and **every position of the origin's
point inside an arc lies in an open hole** (`avoid`).

Postcondition (`ShotPost`): there is a set `A` with `loSet ⊆ A ⊆ hiSet` (the arcs outside the
closed holes, the arcs) such that the flag and the hit describe the first hit of the ray on `A`
(`FirstHit`, proper hit position in range) or its absence (`NoHit`).

Cost `(K + 1) · (16 F γ + 500000)`, bands `insert (bandOf R) oracleBands`.  The shooter is
required (`ShooterOK`, which bounds the edge of its hits since amendment G9).
-/

namespace Chazelle.Core

namespace ShotList

open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Chain (sideInArc)
open Chazelle.Visibility (rayPt)

@[expose] public section

/-! ## The program -/

/-- A block of constants `dst := v`. -/
def consts (l : List (ℕ × ℕ)) : List Instr := l.map fun p => .constN p.1 p.2

/-- The constants of the wrapper. -/
def initConsts (R : ℕ) : List (ℕ × ℕ) :=
  [(R + 30, 0), (R + 31, 1), (R + 32, 2), (R + 33, 3), (R + 20, 0), (R + 28, 0), (R + 37, 4)]

/-- Constants, the chain descriptor address, the output flag, the arc counter and pointer. -/
def shInit (R : ℕ) : Stmt :=
  .seq (block (copies [(R + 36, R + 1), (R + 34, R)]))
    (.seq (block (consts (initConsts R))) (.seq (.instr (.addN (R + 34) (R + 34) (R + 31)))
      (.ifLtN (R + 6) (R + 31) (.instr (.constN (R + 35) 0))
        (.ifLtN (R + 31) (R + 6) (.instr (.constN (R + 35) 0)) (.instr (.constN (R + 35) 1))))))

/-- Load the current arc into the registers of level `0`. -/
def loadArc (R : ℕ) : Stmt :=
  block [.loadN (R + 40) (R + 36), .addN (R + 38) (R + 36) (R + 31), .loadN (R + 41) (R + 38),
    .addN (R + 38) (R + 38) (R + 31), .loadN (R + 42) (R + 38), .addN (R + 38) (R + 38) (R + 31),
    .loadN (R + 43) (R + 38)]

/-- Advance to the next arc. -/
def stepArc (R : ℕ) : Stmt := block [.addN (R + 28) (R + 28) (R + 31), .addN (R + 36) (R + 36) (R + 37)]

/-- **The wrapper**: shoot at every arc, cut by the holes, and keep the first hit. -/
def shotList (sh : Stmt) (R : ℕ) : Stmt :=
  .seq (shInit R) (.whileLtN (R + 28) (R + 2) (.seq (loadArc R) (.seq (levF sh R 3 0) (stepArc R))))

/-! ## The contract -/

/-- **The origin avoids the arcs outside the holes**: every position of the origin's point with
a key in an arc lies in an open hole. -/
def Avoid (M : Model) (Q : Polygon) (m : ℕ → ℕ) (A K : ℕ) (hs : List (WPos × WPos)) (z : Point) :
    Prop :=
  ∀ p : ℕ, ∀ t : ℝ, p < M.W.n → 0 ≤ t → t ≤ 1 → Geometry.lerp (M.wa p) (M.wb p) t = z →
    ∀ j < K, CIn (M.key Q (arcAt m A j).1) (M.key Q (arcAt m A j).2) (p + t) →
      ∃ g ∈ hs, sideInArc (M.key Q g.1) (M.key Q g.2) (p + t)

/-- **The precondition of the wrapper.** -/
def ShotPre (X : MemCtx) (Ok : Polygon → Model → Prop) (R : ℕ) (P : Polygon) (W : ℕ)
    (c : Config) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧
    X.holds P c.nmem (c.nreg (R + 8)) (c.nreg ALLOC) ∧
    c.nreg (R + 7) ≤ X.cap P c.nmem (c.nreg (R + 8)) ∧
    ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg R) ∧ c.nmem (c.nreg R) = 0 ∧
    c.nreg (R + 1) + 4 * c.nreg (R + 2) ≤ c.nreg ALLOC ∧ c.nreg (R + 9) ≤ 3 ∧
    ∃ H C, ChainDescAt c.nmem (c.nreg R + 1) (Qof P) H C ∧
      (∀ H', HostAt c.nmem (c.nmem (c.nreg R + 1)) H' → HostRegular P.n H') ∧
      Ok P (chainModel C) ∧ 2 * C.m + 7 ≤ W ∧
      (∀ j < c.nreg (R + 2), PieceOK (chainModel C) (Qof P) P.n (arcAt c.nmem (c.nreg (R + 1)) j) ∧
        (chainModel C).arcWt ((chainModel C).key (Qof P) (arcAt c.nmem (c.nreg (R + 1)) j).1)
          ((chainModel C).key (Qof P) (arcAt c.nmem (c.nreg (R + 1)) j).2) ≤ c.nreg (R + 7)) ∧
      (∀ j < c.nreg (R + 9), c.nreg (R + 10 + 2 * j) < (chainModel C).W.n ∧
        c.nreg (R + 11 + 2 * j) < (chainModel C).W.n ∧
        c.nreg (R + 10 + 2 * j) ≠ c.nreg (R + 11 + 2 * j)) ∧
      ∃ o : Origin, OriginIn c (R + 3) o ∧ o.Lt P.n (chainModel C) ∧
        ((∃ q, o = .walk ⟨q, 0⟩) ∨ ((chainModel C).InnerPt (o.eval (chainModel C) (Qof P)) ∧
          ∀ x, o = .walk x → ProperPos (chainModel C) (Qof P) P.n x)) ∧
        |(o.eval (chainModel C) (Qof P)).2| < C.radius ∧
        Avoid (chainModel C) (Qof P) c.nmem (c.nreg (R + 1)) (c.nreg (R + 2)) (holeList c R)
          (o.eval (chainModel C) (Qof P))

/-- **The postcondition of the wrapper.** -/
def ShotPost (R : ℕ) (P : Polygon) (c c' : Config) : Prop :=
  ∀ (M : Model) (o : Origin), ModelDescAt c.nmem (c.nreg R) (Qof P) M → OriginIn c (R + 3) o →
    c'.nreg (R + 20) ≤ 1 ∧
    ∃ A : Set Point,
      loSet M (Qof P) c.nmem (c.nreg (R + 1)) (c.nreg (R + 2)) (holeList c R) ⊆ A ∧
      A ⊆ hiSet M (Qof P) c.nmem (c.nreg (R + 1)) (c.nreg (R + 2)) ∧
      (c'.nreg (R + 20) = 1 → ∃ t, FirstHit A (o.eval M (Qof P)) (dirOf (c.nreg (R + 6))) t ∧
        ProperPos M (Qof P) P.n ⟨c'.nreg (R + 21), c'.nreg (R + 22)⟩ ∧
        c'.nreg (R + 21) < M.W.n ∧
        M.pos (Qof P) ⟨c'.nreg (R + 21), c'.nreg (R + 22)⟩ =
          rayPt (o.eval M (Qof P)) (dirOf (c.nreg (R + 6))) t) ∧
      (c'.nreg (R + 20) ≠ 1 → NoHit A (o.eval M (Qof P)) (dirOf (c.nreg (R + 6))))

/-- The cost of the wrapper. -/
def shotCost (Fg K : ℕ) : ℕ := (K + 1) * (16 * Fg + 500000)


/-! ## Execution of the blocks -/

/-- The block `R + 20 … R + 39`. -/
def Bmid (R : ℕ) (r : ℕ) : Bool := decide (R + 20 ≤ r ∧ r < R + 40)

/-- **A block of constants** with distinct targets. -/
theorem consts_exec {P : Polygon} {W : ℕ} : ∀ (l : List (ℕ × ℕ)) (c : Config), WordsBounded W c →
    (∀ p ∈ l, p.2 ≤ W) → (l.map Prod.fst).Nodup →
    ∃ c', Exec P W (block (consts l)) c c' l.length ∧ (∀ p ∈ l, c'.nreg p.1 = p.2) ∧
      FrameB (fun r => (l.map Prod.fst).contains r) c c'
  | [], c, hw, _, _ => ⟨c, Exec.block_nil hw, by simp, FrameB.refl _ _⟩
  | (a, v) :: l, c, hw, hv, hnd => by
    have e₁ := Exec.constN (P := P) hw a v (hv _ (List.mem_cons_self))
    have hnd' := List.nodup_cons.1 hnd
    obtain ⟨c', e, h1, h2⟩ := consts_exec l _ e₁.wb_right
      (fun p hp => hv p (List.mem_cons_of_mem _ hp)) hnd'.2
    refine ⟨c', Exec.block_cons e₁ e, fun p hp => ?_, ?_⟩
    · rcases List.mem_cons.1 hp with rfl | hp
      · rw [h2.1 _ (by simpa using hnd'.1)]; simp
      · exact h1 p hp
    · refine ⟨fun r hr => ?_, fun r _ => by rw [h2.2.1 r (by simp_all)], h2.2.2⟩
      simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        at hr
      rw [h2.1 r (by simpa using hr.2)]; simp [upd, hr.1]

/-- **The initialisation.** -/
theorem shInit_exec {P : Polygon} {W : ℕ} {R : ℕ} (c : Config) (hw : WordsBounded W c)
    (hW : 4 ≤ W) (hD : c.nreg R + 1 ≤ W) :
    ∃ c' k, Exec P W (shInit R) c c' k ∧ k ≤ 20 ∧
      c'.nreg (R + 30) = 0 ∧ c'.nreg (R + 31) = 1 ∧ c'.nreg (R + 32) = 2 ∧
      c'.nreg (R + 33) = 3 ∧ c'.nreg (R + 34) = c.nreg R + 1 ∧ c'.nreg (R + 20) = 0 ∧
      c'.nreg (R + 28) = 0 ∧ c'.nreg (R + 36) = c.nreg (R + 1) ∧ c'.nreg (R + 37) = 4 ∧
      BitIs c' (R + 35) (c.nreg (R + 6) = 1) ∧ FrameB (Bmid R) c c' := by
  obtain ⟨c₁, e₁, v₁, f₁⟩ := copies_run (P := P) [(R + 36, R + 1), (R + 34, R)] c hw
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) q (rfl | rfl) <;> simp)
    (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at v₁
  obtain ⟨a36, a34⟩ := v₁
  obtain ⟨c₂, e₂, v₂, f₂⟩ := consts_exec (P := P) (initConsts R) c₁ e₁.wb_right
    (by simp only [initConsts, List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp <;> omega)
    (by simp [initConsts])
  simp only [initConsts, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₂
  obtain ⟨b30, b31, b32, b33, b20, b28, b37⟩ := v₂
  have k2 := f₂.1
  have c34 : c₂.nreg (R + 34) = c.nreg R := by rw [k2 _ (by simp [initConsts]), a34]
  have c36 : c₂.nreg (R + 36) = c.nreg (R + 1) := by rw [k2 _ (by simp [initConsts]), a36]
  have r6 : c₂.nreg (R + 6) = c.nreg (R + 6) := by
    rw [k2 _ (by simp [initConsts]), f₁.1 _ (by simp)]
  have e₃ := Exec.addN (P := P) e₂.wb_right (R + 34) (R + 34) (R + 31) (by rw [c34, b31]; exact hD)
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg (R + 34) (c₂.nreg (R + 34) + c₂.nreg (R + 31)) }
    with hc₃
  have w₃ := e₃.wb_right
  have k3 : ∀ r, r ≠ R + 34 → c₃.nreg r = c₂.nreg r := fun r hr => by rw [hc₃]; simp [upd, hr]
  have d34 : c₃.nreg (R + 34) = c.nreg R + 1 := by rw [hc₃]; simp [upd, c34, b31]
  have F₃ : FrameB (Bmid R) c c₃ :=
    ((frameB_mono f₁ (fun r hr => by simp at hr; simp [Bmid]; omega)).trans
      (frameB_mono f₂ (fun r hr => by simp [initConsts] at hr; simp [Bmid]; omega))).trans
      (frameB_mono (exec_frameB e₃ (show wr (Bone (R + 34)) _ = true by simp [wr, wrOK, Bone]))
        (fun r hr => by simp [Bone] at hr; simp [Bmid, hr]))
  have fin : ∀ v, v ≤ 1 → (v = 1 ↔ c.nreg (R + 6) = 1) → ∃ c' k, Exec P W
      (.instr (.constN (R + 35) v)) c₃ c' k ∧ k = 1 ∧ c'.nreg (R + 30) = 0 ∧
      c'.nreg (R + 31) = 1 ∧ c'.nreg (R + 32) = 2 ∧ c'.nreg (R + 33) = 3 ∧
      c'.nreg (R + 34) = c.nreg R + 1 ∧ c'.nreg (R + 20) = 0 ∧ c'.nreg (R + 28) = 0 ∧
      c'.nreg (R + 36) = c.nreg (R + 1) ∧ c'.nreg (R + 37) = 4 ∧
      BitIs c' (R + 35) (c.nreg (R + 6) = 1) ∧ FrameB (Bmid R) c₃ c' := fun v hv hb => by
    have e := Exec.constN (P := P) w₃ (R + 35) v (by omega)
    refine ⟨_, 1, e, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩,
      exec_frameB e (by simp [wr, wrOK, Bmid])⟩ <;> simp only [upd_same]
    all_goals first
      | exact hv | exact hb
      | (rw [upd_other _ _ _ (by omega), k3 _ (by omega)]; assumption)
      | (rw [upd_other _ _ _ (by omega)]; exact d34)
  unfold shInit
  have ex₃ : Exec P W (.seq (block (copies [(R + 36, R + 1), (R + 34, R)]))
      (.seq (block (consts (initConsts R))) (.instr (.addN (R + 34) (R + 34) (R + 31))))) c c₃ _ :=
    .seq e₁ (.seq e₂ e₃)
  have r6' : c₃.nreg (R + 6) = c.nreg (R + 6) := by rw [k3 _ (by omega), r6]
  have o31 : c₃.nreg (R + 31) = 1 := by rw [k3 _ (by omega), b31]
  by_cases g1 : c₃.nreg (R + 6) < c₃.nreg (R + 31)
  · obtain ⟨c', k, e, hk, rest⟩ := fin 0 (by omega) (by rw [← r6']; omega)
    exact ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ (.ifLtN_true g1 e))), by simp [initConsts]; omega,
      rest.1, rest.2.1, rest.2.2.1, rest.2.2.2.1, rest.2.2.2.2.1, rest.2.2.2.2.2.1,
      rest.2.2.2.2.2.2.1, rest.2.2.2.2.2.2.2.1, rest.2.2.2.2.2.2.2.2.1, rest.2.2.2.2.2.2.2.2.2.1,
      F₃.trans rest.2.2.2.2.2.2.2.2.2.2⟩
  by_cases g2 : c₃.nreg (R + 31) < c₃.nreg (R + 6)
  · obtain ⟨c', k, e, hk, rest⟩ := fin 0 (by omega) (by rw [← r6']; omega)
    exact ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ (.ifLtN_false g1 (.ifLtN_true g2 e)))),
      by simp [initConsts]; omega, rest.1, rest.2.1, rest.2.2.1, rest.2.2.2.1, rest.2.2.2.2.1,
      rest.2.2.2.2.2.1, rest.2.2.2.2.2.2.1, rest.2.2.2.2.2.2.2.1, rest.2.2.2.2.2.2.2.2.1,
      rest.2.2.2.2.2.2.2.2.2.1, F₃.trans rest.2.2.2.2.2.2.2.2.2.2⟩
  · obtain ⟨c', k, e, hk, rest⟩ := fin 1 le_rfl (by rw [← r6']; omega)
    exact ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ (.ifLtN_false g1 (.ifLtN_false g2 e)))),
      by simp [initConsts]; omega, rest.1, rest.2.1, rest.2.2.1, rest.2.2.2.1, rest.2.2.2.2.1,
      rest.2.2.2.2.2.1, rest.2.2.2.2.2.2.1, rest.2.2.2.2.2.2.2.1, rest.2.2.2.2.2.2.2.2.1,
      rest.2.2.2.2.2.2.2.2.2.1, F₃.trans rest.2.2.2.2.2.2.2.2.2.2⟩


/-- **Loading the current arc.** -/
theorem loadArc_exec {P : Polygon} {W : ℕ} {R : ℕ} (c : Config) (hw : WordsBounded W c)
    (h31 : c.nreg (R + 31) = 1) (hA : c.nreg (R + 36) + 3 ≤ W) :
    ∃ c' k, Exec P W (loadArc R) c c' k ∧ k = 7 ∧
      pieceR c' (R + 40) = arcAt c.nmem (c.nreg (R + 36)) 0 ∧
      FrameB (fun r => decide (R + 38 ≤ r ∧ r < R + 44)) c c' := by
  set a := c.nreg (R + 36)
  have e₁ := Exec.loadN (P := P) hw (R + 40) (R + 36)
  set c₁ : Config := { c with nreg := upd c.nreg (R + 40) (c.nmem a) } with hc₁
  have r₁ : ∀ r, r ≠ R + 40 → c₁.nreg r = c.nreg r := fun r h => by rw [hc₁]; Θ upd, h
  have e₂ := Exec.addN (P := P) e₁.wb_right (R + 38) (R + 36) (R + 31)
    (by rw [r₁ _ (⋄), r₁ _ (⋄), h31]; omega)
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg (R + 38) (c₁.nreg (R + 36) + c₁.nreg (R + 31)) }
    with hc₂
  have r₂ : ∀ r, r ≠ R + 38 → c₂.nreg r = c₁.nreg r := fun r h => by rw [hc₂]; Θ upd, h
  have v₂ : c₂.nreg (R + 38) = a + 1 := by
    rw [hc₂]; simp only [upd_same]; Ξ r₁ _ (⋄), r₁ _ (⋄), h31
  have e₃ := Exec.loadN (P := P) e₂.wb_right (R + 41) (R + 38)
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg (R + 41) (c₂.nmem (c₂.nreg (R + 38))) } with hc₃
  have r₃ : ∀ r, r ≠ R + 41 → c₃.nreg r = c₂.nreg r := fun r h => by rw [hc₃]; Θ upd, h
  have e₄ := Exec.addN (P := P) e₃.wb_right (R + 38) (R + 38) (R + 31)
    (by rw [r₃ _ (⋄), r₃ _ (⋄), v₂, r₂ _ (⋄), r₁ _ (⋄), h31]; omega)
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg (R + 38) (c₃.nreg (R + 38) + c₃.nreg (R + 31)) }
    with hc₄
  have r₄ : ∀ r, r ≠ R + 38 → c₄.nreg r = c₃.nreg r := fun r h => by rw [hc₄]; Θ upd, h
  have v₄ : c₄.nreg (R + 38) = a + 2 := by
    rw [hc₄]; ϴ upd_same
    Ξ r₃ _ (⋄), r₃ _ (⋄), v₂, r₂ _ (⋄), r₁ _ (⋄), h31
  have e₅ := Exec.loadN (P := P) e₄.wb_right (R + 42) (R + 38)
  set c₅ : Config := { c₄ with nreg := upd c₄.nreg (R + 42) (c₄.nmem (c₄.nreg (R + 38))) } with hc₅
  have r₅ : ∀ r, r ≠ R + 42 → c₅.nreg r = c₄.nreg r := fun r h => by rw [hc₅]; Θ upd, h
  have e₆ := Exec.addN (P := P) e₅.wb_right (R + 38) (R + 38) (R + 31)
    (by rw [r₅ _ (⋄), r₅ _ (⋄), v₄, r₄ _ (⋄), r₃ _ (⋄),
      r₂ _ (⋄), r₁ _ (⋄), h31]; omega)
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg (R + 38) (c₅.nreg (R + 38) + c₅.nreg (R + 31)) }
    with hc₆
  have r₆ : ∀ r, r ≠ R + 38 → c₆.nreg r = c₅.nreg r := fun r h => by rw [hc₆]; Θ upd, h
  have v₆ : c₆.nreg (R + 38) = a + 3 := by
    rw [hc₆]; ϴ upd_same
    rw [r₅ _ (⋄), r₅ _ (⋄), v₄, r₄ _ (⋄), r₃ _ (⋄),
      r₂ _ (⋄), r₁ _ (⋄), h31]
  have e₇ := Exec.loadN (P := P) e₆.wb_right (R + 43) (R + 38)
  set c₇ : Config := { c₆ with nreg := upd c₆.nreg (R + 43) (c₆.nmem (c₆.nreg (R + 38))) } with hc₇
  have r₇ : ∀ r, r ≠ R + 43 → c₇.nreg r = c₆.nreg r := fun r h => by rw [hc₇]; Θ upd, h
  have ex : Exec P W (loadArc R) c c₇ 7 := by
    unfold loadArc
    exact Exec.block_cons e₁ (Exec.block_cons e₂ (Exec.block_cons e₃ (Exec.block_cons e₄
      (Exec.block_cons e₅ (Exec.block_cons e₆ (Exec.block_cons e₇ (Exec.block_nil e₇.wb_right)))))))
  have m : c₇.nmem = c.nmem := rfl
  refine ⟨c₇, 7, ex, rfl, ?_, exec_frameB ex (⊚ loadArc, wr, block, wrOK)⟩
  ϴ pieceR, posR, arcAt, Nat.mul_zero, Nat.add_zero, Prod.mk.injEq, WPos.mk.injEq
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [r₇ _ (⋄), r₆ _ (⋄), r₅ _ (⋄), r₄ _ (⋄), r₃ _ (⋄),
      r₂ _ (⋄), hc₁]; simp
  · Ξ r₇ _ (⋄), r₆ _ (⋄), r₅ _ (⋄), r₄ _ (⋄), hc₃
    simp only [upd_same]; Ξ v₂
  · rw [r₇ _ (⋄), r₆ _ (⋄), hc₅]; simp only [upd_same]; Ξ v₄
  · rw [hc₇]; simp only [upd_same]; Ξ v₆

/-- **Advancing to the next arc.** -/
theorem stepArc_exec {P : Polygon} {W : ℕ} {R : ℕ} (c : Config) (hw : WordsBounded W c)
    (h31 : c.nreg (R + 31) = 1) (h37 : c.nreg (R + 37) = 4) (hj : c.nreg (R + 28) + 1 ≤ W)
    (hA : c.nreg (R + 36) + 4 ≤ W) :
    ∃ c' k, Exec P W (stepArc R) c c' k ∧ k = 2 ∧ c'.nreg (R + 28) = c.nreg (R + 28) + 1 ∧
      c'.nreg (R + 36) = c.nreg (R + 36) + 4 ∧
      FrameB (fun r => r == R + 28 || r == R + 36) c c' := by
  have e₁ := Exec.addN (P := P) hw (R + 28) (R + 28) (R + 31) (by rw [h31]; exact hj)
  set c₁ : Config := { c with nreg := upd c.nreg (R + 28) (c.nreg (R + 28) + c.nreg (R + 31)) }
    with hc₁
  have r₁ : ∀ r, r ≠ R + 28 → c₁.nreg r = c.nreg r := fun r h => by rw [hc₁]; Θ upd, h
  have e₂ := Exec.addN (P := P) e₁.wb_right (R + 36) (R + 36) (R + 37)
    (by rw [r₁ _ (⋄), r₁ _ (⋄), h37]; exact hA)
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg (R + 36) (c₁.nreg (R + 36) + c₁.nreg (R + 37)) }
    with hc₂
  have ex : Exec P W (stepArc R) c c₂ 2 := by
    unfold stepArc
    exact Exec.block_cons e₁ (Exec.block_cons e₂ (Exec.block_nil e₂.wb_right))
  refine ⟨c₂, 2, ex, rfl, ?_, ?_, exec_frameB ex (⊚ stepArc, wr, block, wrOK)⟩
  · rw [hc₂]; ϴ upd, show R + 28 ≠ R + 36 by omega, ↓reduceIte
    rw [hc₁]; Θ upd, h31
  · rw [hc₂]; simp only [upd_same]; Ξ r₁ _ (⋄), r₁ _ (⋄), h37


/-! ## Facts for the main theorem -/

/-- An origin is determined by its registers. -/
theorem originIn_unique {c : Config} {r : ℕ} {o o' : Origin} (h : OriginIn c r o)
    (h' : OriginIn c r o') : o = o' := by
  cases o with
  | sym p =>
    cases o' with
    | sym p' =>
      cases p with
      | vtx i =>
        cases p' with
        | vtx i' => have := h.2.symm.trans h'.2; Θ this
        | onEdge e k => exact absurd (h.1.symm.trans h'.1) (✓)
      | onEdge e k =>
        cases p' with
        | vtx i' => exact absurd (h.1.symm.trans h'.1) (✓)
        | onEdge e' k' =>
          have e1 := h.2.1.symm.trans h'.2.1
          have e2 := h.2.2.symm.trans h'.2.2
          Θ e1, e2
    | walk x =>
      cases p with
      | vtx i => exact absurd (h.1.symm.trans h'.1) (✓)
      | onEdge e k => exact absurd (h.1.symm.trans h'.1) (✓)
  | walk x =>
    cases o' with
    | sym p' =>
      cases p' with
      | vtx i => exact absurd (h.1.symm.trans h'.1) (✓)
      | onEdge e k => exact absurd (h.1.symm.trans h'.1) (✓)
    | walk x' =>
      obtain ⟨e, hh⟩ := x
      obtain ⟨e', hh'⟩ := x'
      have e1 := h.2.1.symm.trans h'.2.1
      have e2 := h.2.2.symm.trans h'.2.2
      simp only at e1 e2
      Θ e1, e2

/-- Registers of the caller's block have its band. -/
theorem band_block {R : ℕ} (hR : RegsOK R) {r : ℕ} (h1 : R ≤ r) (h2 : r < R + 300) :
    bandOf r = bandOf R := by
  unfold RegsOK at hR; unfold bandOf; omega

end

end ShotList

end Chazelle.Core
