module

public import Chazelle.Core.ShootCutShOrgM
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.MiscTactics
public import Chazelle.ConfigTactics

/-!
# WP-G, part 55: the origin of the ray on the RAM

`orig` sets up the shooting environment (`ShEnv`) from the inputs of the ray-shooter: the constant
`K1`, the chain descriptor address `140403`, the direction bit `140241`, and the point record of
the origin `z` (`140230 …`: abscissa, height, symbolic point).  It also decides how the kind-1
pieces are queried (`OrgOK`): with a query origin (`140237 = 1`, origin in `140238 …`, related to
`z` by `QRel`), or not at all (`140237 = 0`: no point of the chain is hit).

* a symbolic origin is its own query origin;
* a walk origin is loaded by `ptLoad`; then its symbolic point (if any) is the query origin, a
  point on the side of the box behind the ray gives the box query origin, and the other
  positions (the side ahead of the ray, the top and bottom lines, the slit) see no point of the
  chain.
-/


namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim

@[expose] public section

/-! ## The programs -/

/-- The constant `K1`, the descriptor address and the direction bit. -/
def oInit : Stmt := .seq (block [.constN K1 1, .addN 140403 140000 K1])
  (ifEq 140008 K1 (.instr (.constN 140241 1)) (.instr (.constN 140241 0)))

/-- A symbolic origin: its record and its query origin. -/
def oSym : Stmt := .seq (block [.constN 140230 1, .copyN 140231 140005, .copyN 140232 140006,
    .copyN 140233 140007, .constN 140234 1, .constN 140235 0, .constN 140237 1,
    .copyN 140238 140005, .copyN 140239 140006, .copyN 140240 140007])
  (.ifLtN 140005 K1 (.instr (.copyN 140236 140006)) (.instr (.copyN 140236 140007)))

/-- No query. -/
def qk0 : Stmt := .instr (.constN 140237 0)

/-- The box query origin at the height of the origin. -/
def oBox : Stmt := block [.constN 140237 1, .constN 140238 2, .copyN 140239 140236]

/-- A walk origin on a side of the box or in the slit. -/
def oSide : Stmt := .ifLtN 140230 K1 (.ifLtN 140241 K1 qk0 oBox)
  (.ifLtN K1 140230 (.ifLtN 140241 K1 oBox qk0) qk0)

/-- The query decision for a walk origin. -/
def oFix : Stmt := .ifLtN 140234 K1 qk0 (.ifLtN K1 140234 qk0 (ifEq 140237 K1 .skip oSide))

/-- A walk origin. -/
def oWalk : Stmt := .seq (ptLoad 140006 140007 140230) oFix

/-- **The origin of the ray.** -/
def orig : Stmt := .seq oInit (.ifLtN K1 140005 oWalk oSym)

/-- The registers written by `orig`. -/
def Borg (r : ℕ) : Bool := Bld 140230 r || r == 140401 || r == 140403 || r == 140241

theorem wr_orig : wr Borg orig = true := by decide

/-! ## The query decision -/

/-- **The query decision** for the kind-1 pieces. -/
structure OrgOK (P : Polygon) (C : Chain) (z : Point) (σ : ℝ) (c : Config) : Prop where
  qk : c.nreg 140237 ≤ 1
  q0 : c.nreg 140237 = 0 → ∀ S : Set Point, (∀ x ∈ S, InC C x) → NoHit S z σ
  q1 : c.nreg 140237 = 1 → c.nreg 140234 = 1 ∧
    ∃ o, QOriginIn c 140238 o ∧ o.Lt P.n ∧ QRel P C σ z o

variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}

theorem OrgOK.keep {c c' : Config} (h : OrgOK P C z σ c)
    (hr : ∀ r, 140234 ≤ r → r < 140241 → c'.nreg r = c.nreg r) : OrgOK P C z σ c' := by
  have e37 := hr 140237 (by norm_num) (by norm_num)
  refine ⟨by rw [e37]; exact h.qk, fun h0 => h.q0 (by rwx [← e37]), fun h1 => ?_⟩
  obtain ⟨a, o, ho, hl, hq⟩ := h.q1 (by rwx [← e37])
  exact ⟨by rw [hr _ (by norm_num) (by norm_num)]; exact a, o,
    qOriginIn_of_eq ho fun j h1 h2 => hr j (by omega) (by omega), hl, hq⟩

theorem orgOK_zero {c : Config} (h : c.nreg 140237 = 0)
    (hN : ∀ S : Set Point, (∀ x ∈ S, InC C x) → NoHit S z σ) : OrgOK P C z σ c :=
  ⟨by rwo [h], fun _ => hN, fun h' => by rw [h] at h'; exact absurd h' (by norm_num)⟩

theorem orgOK_one {c : Config} (h : c.nreg 140237 = 1) (h34 : c.nreg 140234 = 1)
    (hq : ∃ o, QOriginIn c 140238 o ∧ o.Lt P.n ∧ QRel P C σ z o) : OrgOK P C z σ c :=
  ⟨by rw [h], fun h' => by rw [h] at h'; exact absurd h' (by norm_num), fun _ => ⟨h34, hq⟩⟩

theorem dirOf_cases (v : ℕ) : dirOf v = 1 ∨ dirOf v = -1 := by
  unfold dirOf; split_ifs <;> simp

/-! ## The pieces -/

theorem oInit_exec (c : Config) (hw : WordsBounded W c) (hMD : c.nreg 140000 + 1 ≤ W) :
    ∃ c' k, Exec P W oInit c c' k ∧ k ≤ 10 ∧ c'.nreg K1 = 1 ∧
      c'.nreg 140403 = c.nreg 140000 + 1 ∧ c'.nreg 140241 ≤ 1 ∧
      (c'.nreg 140241 = 1 ↔ dirOf (c.nreg 140008) = 1) ∧
      (∀ r, r ≠ 140401 → r ≠ 140403 → r ≠ 140241 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  obtain ⟨c₁, k₁, e₁, hk₁, a1, a3, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.constN K1 1, .addN 140403 140000 K1]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 140401 = 1 ∧
      c₁.nreg 140403 = c.nreg 140000 + 1 ∧
      (∀ r, r ≠ 140401 → r ≠ 140403 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    simp only [K1]
    exec_block
    all_goals first | omega | (config_simp; omega) | skip
    refine ⟨rfl, by config_simp, by config_simp, fun r h1 h2 => ?_, rfl⟩
    simp only [upd]; split_ifs <;> first | rfl | omega
  have w₁ := e₁.wb_right
  have b08 : c₁.nreg 140008 = c.nreg 140008 := r₁ _ (by norm_num) (by norm_num)
  obtain ⟨c₂, k₂, e₂, hk₂, v41, r₂, m₂⟩ := ifEq_exec (P := P) (W := W) (a := 140008) (b := K1)
    (T := .instr (.constN 140241 1)) (E := .instr (.constN 140241 0)) c₁ (K := 1)
    (R := fun c' => (c'.nreg 140241 = if c.nreg 140008 = 1 then 1 else 0) ∧
      (∀ r, r ≠ 140241 → c'.nreg r = c₁.nreg r) ∧ c'.nmem = c₁.nmem)
    (fun h => ⟨_, _, Exec.constN w₁ 140241 1 (by have := w₁; omega), le_rfl,
      by simp only [Config.nreg_mk, upd_same]; rw [ite_eq_left (by rwx [← b08, h])],
      fun r hr => by simp [upd_other _ _ _ hr], rfl⟩)
    (fun h => by
      have hne : c.nreg 140008 ≠ 1 := fun h' => h (by rw [b08, h']; exact a1.symm)
      exact ⟨_, _, Exec.constN w₁ 140241 0 (Nat.zero_le _), le_rfl,
        by simp only [Config.nreg_mk, upd_same]; rw [ite_eq_right hne],
        fun r hr => by simp [upd_other _ _ _ hr], rfl⟩)
  refine ⟨c₂, k₁ + k₂, by unfold oInit; exact .seq e₁ e₂, by omega, ?_, ?_, ?_, ?_,
    fun r h1 h2 h3 => by rw [r₂ r h3, r₁ r h1 h2], by rw [m₂, m₁]⟩
  · show c₂.nreg 140401 = 1; rw [r₂ _ (by norm_num), a1]
  · rw [r₂ _ (by norm_num), a3]
  · rw [v41]; splao
  · rw [v41]; by_cases hd : c.nreg 140008 = 1 <;> simp [dirOf, hd] <;> norm_num

theorem oSym_exec (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W) (h1 : c.nreg K1 = 1)
    {s : SymPt}
    (hs : SymPtIn c 140005 s) :
    ∃ c' k, Exec P W oSym c c' k ∧ k ≤ 20 ∧ c'.nreg 140230 = 1 ∧ SymPtIn c' 140231 s ∧
      c'.nreg 140234 = 1 ∧ c'.nreg 140235 = 0 ∧ c'.nreg 140236 = hIdx s ∧
      c'.nreg 140237 = 1 ∧ SymPtIn c' 140238 s ∧
      (∀ r, (r < 140230 ∨ 140241 ≤ r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  have h1' : c.nreg 140401 = 1 := h1
  obtain ⟨c₁, k₁, e₁, hk₁, a30, a31, a32, a33, a34, a35, a37, a38, a39, a40, r₁, m₁⟩ :
      ∃ c₁ k₁, Exec P W (block [.constN 140230 1, .copyN 140231 140005, .copyN 140232 140006,
        .copyN 140233 140007, .constN 140234 1, .constN 140235 0, .constN 140237 1,
        .copyN 140238 140005, .copyN 140239 140006, .copyN 140240 140007]) c c₁ k₁ ∧
      k₁ = 10 ∧ c₁.nreg 140230 = 1 ∧ c₁.nreg 140231 = c.nreg 140005 ∧
      c₁.nreg 140232 = c.nreg 140006 ∧ c₁.nreg 140233 = c.nreg 140007 ∧
      c₁.nreg 140234 = 1 ∧ c₁.nreg 140235 = 0 ∧ c₁.nreg 140237 = 1 ∧
      c₁.nreg 140238 = c.nreg 140005 ∧ c₁.nreg 140239 = c.nreg 140006 ∧
      c₁.nreg 140240 = c.nreg 140007 ∧
      (∀ r, (r < 140230 ∨ 140236 = r ∨ 140241 ≤ r) → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
      by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
      fun r hr => ?_, rfl⟩
    simp only [upd]; split_ifs <;> first | rfl | omega
  have w₁ := e₁.wb_right
  have b1 : c₁.nreg 140401 = 1 := by rw [r₁ _ (by omega), h1']
  have b05 : c₁.nreg 140005 = c.nreg 140005 := r₁ _ (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, v36, r₂, m₂⟩ : ∃ c₂ k₂, Exec P W
      (.ifLtN 140005 K1 (.instr (.copyN 140236 140006)) (.instr (.copyN 140236 140007))) c₁ c₂ k₂ ∧
      k₂ ≤ 3 ∧ c₂.nreg 140236 = hIdx s ∧ (∀ r, r ≠ 140236 → c₂.nreg r = c₁.nreg r) ∧
      c₂.nmem = c₁.nmem := by
    cases s with
    | vtx i =>
      obtain ⟨i0, i1⟩ := hs
      refine ⟨_, _, .ifLtN_true (by show c₁.nreg 140005 < c₁.nreg 140401; rwo [b05, i0, b1])
        (Exec.copyN w₁ _ _), by norm_num, ?_, fun r hr => by simp [hr], rfl⟩
      simp only [Config.nreg_mk, upd_same, hIdx]; rw [r₁ _ (by omega), i1]
    | onEdge e h =>
      obtain ⟨i0, i1, i2⟩ := hs
      refine ⟨_, _, .ifLtN_false (by show ¬ c₁.nreg 140005 < c₁.nreg 140401; rwo [b05, i0, b1])
        (Exec.copyN w₁ _ _), by norm_num, ?_, fun r hr => by simp [hr], rfl⟩
      simp only [Config.nreg_mk, upd_same, hIdx]; rw [r₁ _ (by omega), i2]
  have g₂ : ∀ r, r ≠ 140236 → c₂.nreg r = c₁.nreg r := r₂
  refine ⟨c₂, k₁ + k₂, by unfold oSym; exact .seq e₁ e₂, by omega, by rw [g₂ _ (by omega), a30],
    NFLoc.symPtIn_copy hs (by rw [g₂ _ (by omega), a31]) (by rw [g₂ _ (by omega), a32])
      (by rw [g₂ _ (by omega), a33]),
    by rw [g₂ _ (by omega), a34], by rw [g₂ _ (by omega), a35], v36, by rw [g₂ _ (by omega), a37],
    NFLoc.symPtIn_copy hs (by rw [g₂ _ (by omega), a38]) (by rw [g₂ _ (by omega), a39])
      (by rw [g₂ _ (by omega), a40]),
    fun r hr => by rw [g₂ r (by omega), r₁ r (by omega)], by rw [m₂, m₁]⟩

theorem wr_oFix : wr (fun r => r == 140237 || r == 140238 || r == 140239) oFix = true := by
  decide

theorem qk0_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W qk0 c c' k ∧ k ≤ 1 ∧ c'.nreg 140237 = 0 := by
  exact ⟨_, _, Exec.constN hw 140237 0 (Nat.zero_le _), le_rfl, by simp⟩

theorem oBox_exec (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W) :
    ∃ c' k, Exec P W oBox c c' k ∧ k ≤ 3 ∧ c'.nreg 140237 = 1 ∧ c'.nreg 140238 = 2 ∧
      c'.nreg 140239 = c.nreg 140236 ∧ c'.nreg 140234 = c.nreg 140234 := by
  unfold oBox
  exec_block
  all_goals first | omega | skip
  exact ⟨by norm_num, by config_simp, by config_simp, by config_simp, by config_simp⟩

/-- **The query decision for a walk origin**, from its point record. -/
theorem oFix_exec (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W) (h1 : c.nreg K1 = 1)
    (hσ : σ = 1 ∨ σ = -1) (hsig : c.nreg 140241 ≤ 1 ∧ (c.nreg 140241 = 1 ↔ σ = 1))
    (hrec : PtRecB P c 140230 z C.radius)
    (hsl : c.nreg 140237 ≠ 1 → |z.1| < C.radius → |z.2| < C.radius → C.top.2 < z.2) :
    ∃ c' k, Exec P W oFix c c' k ∧ k ≤ 30 ∧ OrgOK P C z σ c' ∧
      FrameB (fun r => r == 140237 || r == 140238 || r == 140239) c c' := by
  have h1' : c.nreg 140401 = 1 := h1
  have hR := C.radius_pos
  obtain ⟨ax, hy, hf⟩ := hrec
  suffices H : ∃ c' k, Exec P W oFix c c' k ∧ k ≤ 30 ∧ OrgOK P C z σ c' by
    obtain ⟨c', k, ex, hk, ok⟩ := H
    exact ⟨c', k, ex, hk, ok, exec_frameB ex wr_oFix⟩
  -- no query
  have noq : (∀ S : Set Point, (∀ x ∈ S, InC C x) → NoHit S z σ) →
      ∀ {s : Stmt}, (∀ {c' k}, Exec P W qk0 c c' k → ∃ k', Exec P W s c c' k' ∧ k' ≤ k + 5) →
      ∃ c' k, Exec P W s c c' k ∧ k ≤ 30 ∧ OrgOK P C z σ c' := fun hN s hs => by
    obtain ⟨c', k, ex, hk, v⟩ := qk0_exec (P := P) c hw
    obtain ⟨k', ex', hk'⟩ := hs ex
    exact ⟨c', k', ex', by omega, orgOK_zero v hN⟩
  unfold oFix
  -- the height of the origin
  rcases hy with ⟨k0, hy0⟩ | ⟨k2, hy2⟩ | ⟨k1, hyR, h35, h36, hyv⟩
  · have hN : ∀ S : Set Point, (∀ x ∈ S, InC C x) → NoHit S z σ := fun S hS =>
      noHit_ext (by rw [hy0, abs_neg, abs_of_pos hR]) hS
    have u1 : c.nreg 140234 < c.nreg 140401 := by rwo [k0, h1']
    exact noq hN fun ex => ⟨_, .ifLtN_true u1 ex, by omega⟩
  · have hN : ∀ S : Set Point, (∀ x ∈ S, InC C x) → NoHit S z σ := fun S hS =>
      noHit_ext (by rw [hy2, abs_of_pos hR]) hS
    have u1 : ¬ c.nreg 140234 < c.nreg 140401 := by rwo [k2, h1']
    have u2 : c.nreg 140401 < c.nreg 140234 := by rwo [k2, h1']
    exact noq hN fun ex => ⟨_, .ifLtN_false u1 (.ifLtN_true u2 ex), by omega⟩
  have t1 : ¬ c.nreg 140234 < c.nreg K1 := by rwo [k1, h1]
  have t2 : ¬ c.nreg K1 < c.nreg 140234 := by rwo [k1, h1]
  obtain ⟨c', k, ex, hk, ok⟩ : ∃ c' k, Exec P W (ifEq 140237 K1 .skip oSide) c c' k ∧ k ≤ 20 + 4 ∧
      OrgOK P C z σ c' := by
    refine ifEq_exec (P := P) (W := W) c (K := 20) (fun hq => ?_) (fun hq => ?_)
    · -- a symbolic point
      have hq' : c.nreg 140237 = 1 := by rw [hq, h1]
      obtain ⟨s, hs, hl, hv⟩ := hf hq'
      exact ⟨c, 0, .skip hw, by omega, orgOK_one hq' k1 ⟨.sym s, hs, hl, hv⟩⟩
    · have hq' : c.nreg 140237 ≠ 1 := by rw [h1] at hq; exact hq
      unfold oSide
      obtain ⟨hRx, ak⟩ := ax
      rcases ak with ⟨a0, hx0⟩ | ⟨a2, hx2⟩ | ⟨a1, hx1, -⟩
      · have t : c.nreg 140230 < c.nreg K1 := by rwo [a0, h1]
        by_cases hs1 : σ = 1
        · have tb : ¬ c.nreg 140241 < c.nreg K1 := by
            rwo [h1, hsig.2.2 hs1]
          obtain ⟨c', k, ex, hk, v37, v38, v39, v34⟩ := oBox_exec (P := P) c hw hW
          refine ⟨c', _, .ifLtN_true t (.ifLtN_false tb ex), by omega,
            orgOK_one v37 (by rw [v34, k1]) ⟨.box (c.nreg (140234 + 2)), ⟨v38, v39⟩, h36, ?_⟩⟩
          ext
          · rwring [hx0, hs1]
          · exact hyv
        · have hsm : σ = -1 := hσ.resolve_left hs1
          have tb : c.nreg 140241 < c.nreg K1 := by
            rw [h1]
            have : c.nreg 140241 ≠ 1 := fun h => hs1 (hsig.2.1 h)
            omega
          have hN : ∀ S : Set Point, (∀ x ∈ S, InC C x) → NoHit S z σ := fun S hS =>
            noHit_ahead_side hσ (by rwring [hx0, hsm]) hS
          obtain ⟨c', k, ex, hk, v⟩ := qk0_exec (P := P) c hw
          exact ⟨c', _, .ifLtN_true t (.ifLtN_true tb ex), by omega, orgOK_zero v hN⟩
      · have t : ¬ c.nreg 140230 < c.nreg K1 := by rwo [a2, h1]
        have t' : c.nreg K1 < c.nreg 140230 := by rwo [a2, h1]
        by_cases hs1 : σ = 1
        · have tb : ¬ c.nreg 140241 < c.nreg K1 := by
            rwo [h1, hsig.2.2 hs1]
          have hN : ∀ S : Set Point, (∀ x ∈ S, InC C x) → NoHit S z σ := fun S hS =>
            noHit_ahead_side hσ (by rwring [hx2, hs1]) hS
          obtain ⟨c', k, ex, hk, v⟩ := qk0_exec (P := P) c hw
          exact ⟨c', _, .ifLtN_false t (.ifLtN_true t' (.ifLtN_false tb ex)), by omega,
            orgOK_zero v hN⟩
        · have hsm : σ = -1 := hσ.resolve_left hs1
          have tb : c.nreg 140241 < c.nreg K1 := by
            rw [h1]
            have : c.nreg 140241 ≠ 1 := fun h => hs1 (hsig.2.1 h)
            omega
          obtain ⟨c', k, ex, hk, v37, v38, v39, v34⟩ := oBox_exec (P := P) c hw hW
          refine ⟨c', _, .ifLtN_false t (.ifLtN_true t' (.ifLtN_true tb ex)), by omega,
            orgOK_one v37 (by rw [v34, k1]) ⟨.box (c.nreg (140234 + 2)), ⟨v38, v39⟩, h36, ?_⟩⟩
          ext
          · rwring [hx2, hsm]
          · exact hyv
      · -- inside the slit
        have t : ¬ c.nreg 140230 < c.nreg K1 := by rwo [a1, h1]
        have t' : ¬ c.nreg K1 < c.nreg 140230 := by rwo [a1, h1]
        have hab := hsl hq' hx1 hyR
        have hN : ∀ S : Set Point, (∀ x ∈ S, InC C x) → NoHit S z σ := fun S hS =>
          noHit_above hab hS
        obtain ⟨c', k, ex, hk, v⟩ := qk0_exec (P := P) c hw
        exact ⟨c', _, .ifLtN_false t (.ifLtN_false t' ex), by omega, orgOK_zero v hN⟩
  exact ⟨c', _, .ifLtN_false t1 (.ifLtN_false t2 ex), by omega, ok⟩

/-! ## The origin -/

/-- **The origin of the ray**: the shooting environment and the query decision. -/
theorem orig_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (hD : ChainDescAt c.nmem (c.nreg 140000 + 1) (Qof P) H C)
    (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 140000 + 1))
    (hreg : ∀ H', HostAt c.nmem (c.nmem (c.nreg 140000 + 1)) H' → HostRegular P.n H')
    {o : Origin} (hoIn : OriginIn c 140005 o) (hoLt : o.Lt P.n (chainModel C))
    (hoK : (∃ p, o = .walk ⟨p, 0⟩) ∨ ((chainModel C).InnerPt (o.eval (chainModel C) (Qof P)) ∧
      ∀ x, o = .walk x → ProperPos (chainModel C) (Qof P) P.n x))
    (hroom : c.nreg ALLOC + 15800 ≤ W) (hMD : c.nreg 140000 + 1 ≤ W) :
    ∃ c' k, Exec P W orig c c' k ∧ k ≤ 16000 ∧
      ShEnv P W H C (o.eval (chainModel C) (Qof P)) (dirOf (c.nreg 140008)) c' ∧
      OrgOK P C (o.eval (chainModel C) (Qof P)) (dirOf (c.nreg 140008)) c' ∧
      FrameB Borg c c' ∧ c'.nreg 140403 = c.nreg 140000 + 1 := by
  have hW2 : 2 ≤ W := by ufo hostWords at hW
  have hR := C.radius_pos
  have hn : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  set z := o.eval (chainModel C) (Qof P) with hz
  set σ := dirOf (c.nreg 140008) with hσd
  have hσ : σ = 1 ∨ σ = -1 := dirOf_cases _
  obtain ⟨c₁, k₁, e₁, hk₁, b1, b403, b41, b41', r₁, m₁⟩ := oInit_exec (P := P) c hw hMD
  have w₁ := e₁.wb_right
  have k₁' : ∀ r, 140000 ≤ r → r < 140010 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    r₁ r (by omega) (by omega) (by omega)
  have bA : c₁.nreg ALLOC = c.nreg ALLOC := r₁ _ (by decide) (by decide) (by decide)
  have L : LdEnv P W H C c₁ := ⟨hG, hW, by rwx [m₁, b403],
    by rwx [m₁, b403, bA], by rwx [m₁, b403]⟩
  have ex₀ : ∀ {c' k}, Exec P W (.ifLtN K1 140005 oWalk oSym) c₁ c' k →
      Exec P W orig c c' (k₁ + k) := fun ex => by unfold orig; exact .seq e₁ ex
  cases o with
  | sym s =>
    have hs : SymPtIn c 140005 s := hoIn
    have hs₁ : SymPtIn c₁ 140005 s := symPtIn_of_eq hs fun j h1 h2 => k₁' j (by omega) (by omega)
    have hin : (chainModel C).InnerPt z := by
      rcases hoK with ⟨p, hp⟩ | ⟨h, -⟩
      · exact absurd hp (by simp)
      · exact h
    have hb := innerPt_bounds C hin
    have t : ¬ c₁.nreg K1 < c₁.nreg 140005 := by
      rw [b1]
      cases s with
      | vtx i => rwo [hs₁.1]
      | onEdge e h => rwo [hs₁.1]
    obtain ⟨c₂, k₂, e₂, hk₂, a30, a31, a34, a35, a36, a37, a38, r₂, m₂⟩ :=
      oSym_exec (P := P) c₁ w₁ hW2 b1 hs₁
    have ex := ex₀ (.ifLtN_false t e₂)
    have hl : s.Lt P.n := hoLt
    have hzs : z = s.eval (Qof P) := rfl
    have k2 : ∀ r, 140241 ≤ r → c₂.nreg r = c₁.nreg r := fun r h => r₂ r (Or.inr h)
    refine ⟨c₂, _, ex, by omega, ⟨hG, hW, ?_, ?_, ?_, ?_, ⟨hR, Or.inr (Or.inr ⟨a30, hb.2, s, a31, hl,
      by rw [hzs]⟩)⟩, Or.inr (Or.inr ⟨a34, hb.1, a35, by rw [a36]; exact hIdx_lt hl,
      by rw [a36, hzs]; exact hIdx_snd _ s⟩), ?_, hσ⟩,
      orgOK_one a37 a34 ⟨.sym s, a38, hl, by show s.eval (Qof P) = z; rw [hzs]⟩,
      exec_frameB ex wr_orig, by rw [k2 _ (by norm_num), b403]⟩
    · rw [m₂, k2 140403 (by norm_num)]; exact L.hD
    · rw [m₂, r₂ ALLOC (Or.inl (by decide)), k2 140403 (by norm_num)]; exact L.hwf
    · rw [m₂, k2 140403 (by norm_num)]; exact L.hreg
    · show c₂.nreg 140401 = 1; rwx [k2 _ (by norm_num)]
    · rw [k2 _ le_rfl]; exact ⟨b41, b41'⟩
  | walk x =>
    obtain ⟨o5, o6, o7⟩ : c.nreg 140005 = 2 ∧ c.nreg (140005 + 1) = x.edge ∧
        c.nreg (140005 + 2) = x.hgt := hoIn
    have t : c₁.nreg K1 < c₁.nreg 140005 := by rwo [b1, k₁' _ (by norm_num) (by norm_num), o5]
    have q6 : c₁.nreg 140006 = x.edge := by rwx [k₁' _ (by norm_num) (by norm_num)]
    have q7 : c₁.nreg 140007 = x.hgt := by rwx [k₁' _ (by norm_num) (by norm_num)]
    have hxe : x.edge < (chainModel C).W.n := hoLt.1
    have hxP : ProperPos (chainModel C) (Qof P) P.n x := by
      rcases hoK with ⟨p, hp⟩ | ⟨-, h⟩
      · cases hp
        exact ⟨le_of_eq rfl, by show (0 : ℝ) < 1; norm_num, Nat.zero_le _⟩
      · exact h x rfl
    have hxy : x.hgt = 0 ∨ |((chainModel C).pos (Qof P) x).2| < C.radius := by
      rcases hoK with ⟨p, hp⟩ | ⟨h, -⟩
      · cases hp; exact Or.inl rfl
      · exact Or.inr (innerPt_bounds C h).1
    have hzx : z = (chainModel C).pos (Qof P) x := rfl
    obtain ⟨c₂, k₂, e₂, hk₂, rec₂, f₂, fl₂⟩ := ptLoad_exec' (P := P) (W := W)
      (e := 140006) (h := 140007) (B := 140230) c₁ w₁ L (by norm_num) (by norm_num) (by norm_num)
      (by rwx [q6]) (by rwx [q6, q7]) (by rwx [q6, q7])
      (by rwx [bA])
    rw [q6, q7, ← hzx] at rec₂
    rw [q6, q7] at fl₂
    have kb : ∀ r, Bld 140230 r = false → c₂.nreg r = c₁.nreg r := f₂.1
    have g1 : c₂.nreg K1 = 1 := by rwx [kb _ (by decide)]
    have g41 : c₂.nreg 140241 = c₁.nreg 140241 := kb _ (by decide)
    have hsl : c₂.nreg (140230 + 7) ≠ 1 → |z.1| < C.radius → |z.2| < C.radius →
        C.top.2 < z.2 := fun hf hx hy => by
      rw [hzx] at hx hy ⊢
      refine walk_above C hxP (by rwx [← hn]) hx hy fun h => hf (fl₂ h.1 ?_)
      rcases h.2 with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    obtain ⟨c₃, k₃, e₃, hk₃, ok, f₃⟩ := oFix_exec (P := P) (C := C) (z := z) (σ := σ) c₂
      e₂.wb_right hW2 g1 hσ ⟨by rwx [g41], by rwx [g41]⟩ rec₂ hsl
    have ex := ex₀ (.ifLtN_true t (.seq e₂ e₃))
    have k3 : ∀ r, r ≠ 140237 → r ≠ 140238 → r ≠ 140239 → c₃.nreg r = c₂.nreg r :=
      fun r h1 h2 h3 => f₃.1 r (by simp [h1, h2, h3])
    have m₃ : c₃.nmem = c.nmem := by rw [f₃.2.2.1, f₂.2.2.1, m₁]
    have g403 : c₃.nreg 140403 = c.nreg 140000 + 1 := by
      rw [k3 _ (by norm_num) (by norm_num) (by norm_num), kb _ (by decide), b403]
    have gA : c₃.nreg ALLOC = c.nreg ALLOC := by
      rw [k3 _ (by decide) (by decide) (by decide), kb _ (by decide), bA]
    obtain ⟨ax, hy, -⟩ := rec₂
    refine ⟨c₃, _, ex, by omega, ⟨hG, hW, by rwx [m₃, g403],
      by rwx [m₃, g403, gA], by rwx [m₃, g403], ?_, ?_, ?_, ?_, hσ⟩,
      ok, exec_frameB ex wr_orig, g403⟩
    · show c₃.nreg 140401 = 1
      rwx [k3 _ (by norm_num) (by norm_num) (by norm_num)]
    · exact AbsRecW.copy (r' := 140230) (AbsRec.weak ax) (k3 _ (by norm_num) (by norm_num) (by norm_num))
        (k3 _ (by norm_num) (by norm_num) (by norm_num))
        (k3 _ (by norm_num) (by norm_num) (by norm_num))
        (k3 _ (by norm_num) (by norm_num) (by norm_num))
    · exact HRecS.copy (r' := 140234) hy (k3 _ (by norm_num) (by norm_num) (by norm_num))
        (k3 _ (by norm_num) (by norm_num) (by norm_num))
        (k3 _ (by norm_num) (by norm_num) (by norm_num))
    · rw [k3 _ (by norm_num) (by norm_num) (by norm_num), g41]; exact ⟨b41, b41'⟩

end

end ShootCut

end Chazelle.Core
