module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvRPlA
public import Mathlib.Data.List.GetD

/-!
# Down-phase driver (RAM side): the leaf planner, part 2 (one run item)

`plRun` writes the leaves `runLeaves n C p a ℓ` of a run item (`a = r219010`, `ℓ = r219011`,
host offset `p = r219007`): nothing if `ℓ < 3`, else one or two chunk loops (`plRun_exec`).

Extra registers: `219001` `n`, `219019 = 2`, `219026 = n - 1`, scratch `219022 … 219025`.
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs BuildRam

@[expose] public section

/-- The leaves of one host item at host offset `p`. -/
def itemLeaves (n C p : ℕ) : HostItem → List (ℕ × ℕ × ℕ)
  | .run a ℓ => runLeaves n C p a ℓ
  | .pt _ => []

theorem hostLeaves_append (n C : ℕ) : ∀ (H₁ H₂ : Host) (p : ℕ),
    hostLeaves n C p (H₁ ++ H₂) = hostLeaves n C p H₁ ++ hostLeaves n C (p + (H₁.pts n).length) H₂
  | [], H₂, p => by aesop
  | .run a ℓ :: H₁, H₂, p => by
    simp only [List.cons_append, hostLeaves, hostLeaves_append n C H₁ H₂, List.append_assoc]
    grind [DownMath.pts_cons, List.length_append, DownMath.run_pts_length]
  | .pt x :: H₁, H₂, p => by
    simp only [List.cons_append, hostLeaves, hostLeaves_append n C H₁ H₂]
    grind [DownMath.pts_cons, List.length_append, HostItem.pts]

theorem hostLeaves_single (n C p : ℕ) (it : HostItem) :
    hostLeaves n C p [it] = itemLeaves n C p it := by
  cases it <;> simp [hostLeaves, itemLeaves]

/-- A chord list written in two parts. -/
theorem clAt_append {m : ℕ → ℕ} {A : ℕ} {L L₂ : List (ℕ × ℕ × ℕ)}
    (h₁ : ChordListAt m A L) (h₂ : ChordListAt m (A + 3 * L.length) L₂) :
    ChordListAt m A (L ++ L₂) := by
  intro i hi
  rw [List.length_append] at hi
  rcases Nat.lt_or_ge i L.length with h | h
  · ram_grind
  · ram_all <;> ram_grind

/-- A chord list survives memory changes outside its words. -/
theorem clAt_congr {m m' : ℕ → ℕ} {A : ℕ} {L : List (ℕ × ℕ × ℕ)} (h : ChordListAt m A L)
    (hm : ∀ x, A ≤ x → x < A + 3 * L.length → m' x = m x) : ChordListAt m' A L := by
  core_grind

/-- The wrap-around case: two chunk loops around the edge `v_{n-1} v_0`. -/
def plRunW : Stmt :=
  .seq (block [.subN 219014 219026 219022])
    (.seq plCh
      (.seq (block [.subN 219025 219001 219022, .addN 219012 219007 219018,
          .addN 219012 219012 219025, .copyN 219013 219017, .subN 219014 219023 219025])
        plCh))

/-- `u = (a + 1) mod n`, `L = ℓ - 2`, `u + L`, `s = p + 1`, `a := u`. -/
def plRunPre : Stmt :=
  .seq (block [.addN 219022 219010 219018])
    (.seq (.ifLtN 219022 219001 .skip (.instr (.constN 219022 0)))
      (block [.subN 219023 219011 219019, .addN 219024 219022 219023,
        .addN 219012 219007 219018, .copyN 219013 219022]))

/-- **The leaves of a run item.** -/
def plRun : Stmt :=
  .ifLtN 219011 219020 .skip
    (.seq plRunPre (.ifLtN 219024 219001 (.seq (.instr (.copyN 219014 219023)) plCh) plRunW))

/-- The registers `plRun` writes. -/
def Brun (r : ℕ) : Bool := Bch r || decide (219022 ≤ r ∧ r ≤ 219025)

section exec

variable {P : Polygon} {W : ℕ}

/-- The common hypotheses of the planner steps: constants and the chunk size. -/
structure PlConst (n C : ℕ) (d : Config) : Prop where
  r01 : d.nreg 219001 = n
  r02 : d.nreg 219002 = C
  r17 : d.nreg 219017 = 0
  r18 : d.nreg 219018 = 1
  r19 : d.nreg 219019 = 2
  r20 : d.nreg 219020 = 3
  r26 : d.nreg 219026 = n - 1

theorem PlConst.keep {n C : ℕ} {d d' : Config} (h : PlConst n C d)
    (hk : ∀ r, (r = 219001 ∨ r = 219002 ∨ (219017 ≤ r ∧ r ≤ 219020) ∨ r = 219026) →
      d'.nreg r = d.nreg r) : PlConst n C d' :=
  by core_grind

theorem brun_const {r : ℕ} (h : r = 219001 ∨ r = 219002 ∨ (219017 ≤ r ∧ r ≤ 219020) ∨ r = 219026) :
    Brun r = false := by
  core_grind

set_option maxHeartbeats 4000000 in
/-- **The leaves of a run item** are written at the pointer. -/
theorem plRun_exec {n C : ℕ} (hC : 1 ≤ C) (hn : 2 ≤ n) (d : Config) (hw : WordsBounded W d)
    (hK : PlConst n C d) {a ℓ p k ptr : ℕ} (h10 : d.nreg 219010 = a) (h11 : d.nreg 219011 = ℓ)
    (h07 : d.nreg 219007 = p) (h16 : d.nreg 219016 = ptr) (h04 : d.nreg 219004 = k)
    (ha : a < n) (hℓ : ℓ < n) (hWp : p + ℓ + n + 1 ≤ W)
    (hWt : ptr + 3 * (runLeaves n C p a ℓ).length ≤ W)
    (hWk : k + (runLeaves n C p a ℓ).length ≤ W) :
    ∃ d' j, Exec P W plRun d d' j ∧ j ≤ 15 * (runLeaves n C p a ℓ).length + 40 ∧
      d'.nreg 219016 = ptr + 3 * (runLeaves n C p a ℓ).length ∧
      d'.nreg 219004 = k + (runLeaves n C p a ℓ).length ∧
      ChordListAt d'.nmem ptr (runLeaves n C p a ℓ) ∧
      (∀ x, (x < ptr ∨ ptr + 3 * (runLeaves n C p a ℓ).length ≤ x) → d'.nmem x = d.nmem x) ∧
      FrameM Brun d d' := by
  by_cases h3 : ℓ < 3
  · have hrl : runLeaves n C p a ℓ = [] := by grind [runLeaves]
    rw [hrl]
    refine ⟨d, 0 + 1, .ifLtN_true (by ram_grind) (.skip hw), by simp,
      by simp [h16], by simp [h04], fun i hi => by simp at hi, fun _ _ => rfl, FrameM.refl _ _⟩
  -- `u = (a + 1) % n`, `L = ℓ - 2`
  have hu : (a + 1) % n = if a + 1 < n then a + 1 else 0 := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    grind [Nat.mod_self]
  set u := (a + 1) % n with hud
  have hun : u < n := Nat.mod_lt _ (by omega)
  obtain ⟨d₁, j₁, e₁, hj₁, v22, v23, v24, v12, v13, g₁, m₁⟩ : ∃ d₁ j₁, Exec P W
      plRunPre d d₁ j₁ ∧ j₁ ≤ 8 ∧
      d₁.nreg 219022 = u ∧ d₁.nreg 219023 = ℓ - 2 ∧ d₁.nreg 219024 = u + (ℓ - 2) ∧
      d₁.nreg 219012 = p + 1 ∧ d₁.nreg 219013 = u ∧
      (∀ r, ¬ (219012 ≤ r ∧ r ≤ 219013) → ¬ (219022 ≤ r ∧ r ≤ 219024) → d₁.nreg r = d.nreg r) ∧
      d₁.nmem = d.nmem := by
    have e₁ := Exec.addN (P := P) hw 219022 219010 219018 (by ram_grind)
    set c₁ : Config := { d with nreg := upd d.nreg 219022 (d.nreg 219010 + d.nreg 219018) } with hc₁
    have q22 : c₁.nreg 219022 = a + 1 := by rw [hc₁]; config_simp; rw [h10, hK.r18]
    have q : ∀ r, r ≠ 219022 → c₁.nreg r = d.nreg r := fun r hr => by ram_simp
    unfold plRunPre
    obtain ⟨c₂, j₂, e₂, hj₂, q22', q', qm⟩ : ∃ c₂ j₂, Exec P W
        (.ifLtN 219022 219001 .skip (.instr (.constN 219022 0))) c₁ c₂ j₂ ∧ j₂ ≤ 3 ∧
        c₂.nreg 219022 = u ∧ (∀ r, r ≠ 219022 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem := by
      by_cases hlt : a + 1 < n
      · refine ⟨c₁, 0 + 1, .ifLtN_true (by ram_grind)
          (.skip e₁.wb_right), by omega, by ram_grind, fun _ _ => rfl, rfl⟩
      · refine ⟨_, 1 + 2, .ifLtN_false (by rw [q22, q _ (by decide), hK.r01]; exact hlt)
          (Exec.constN (P := P) e₁.wb_right 219022 0 (by omega)), by omega, ?_,
          fun r hr => by simp [hr], rfl⟩
        simp_all
    have w₂ := e₂.wb_right
    have b11 : c₂.nreg 219011 = ℓ := by ram_simp
    have b19 : c₂.nreg 219019 = 2 := by rw [q' _ (by decide), q _ (by decide), hK.r19]
    have b07 : c₂.nreg 219007 = p := by ram_simp
    have b18 : c₂.nreg 219018 = 1 := by ram_grind
    obtain ⟨c₃, j₃, e₃, hj₃, w23, w24, w12, w13, g₃, m₃⟩ : ∃ c₃ j₃, Exec P W
        (block [.subN 219023 219011 219019, .addN 219024 219022 219023,
          .addN 219012 219007 219018, .copyN 219013 219022]) c₂ c₃ j₃ ∧ j₃ = 4 ∧
        c₃.nreg 219023 = ℓ - 2 ∧ c₃.nreg 219024 = u + (ℓ - 2) ∧ c₃.nreg 219012 = p + 1 ∧
        c₃.nreg 219013 = u ∧
        (∀ r, ¬ (219012 ≤ r ∧ r ≤ 219013) → r ≠ 219023 → r ≠ 219024 → c₃.nreg r = c₂.nreg r) ∧
        c₃.nmem = c₂.nmem := by
      exec_block
      all_goals try (config_simp; omega)
      refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl⟩ <;> config_simp <;>
        (try simp only [b11, b19, q22', b07, b18])
      try simp only [Config.nreg_mk]
      rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ h3, Machine.upd_other _ _ _ h2]
    refine ⟨c₃, (1 + 0) + (j₂ + j₃), .seq (.seq e₁ (.skip e₁.wb_right)) (.seq e₂ e₃), by omega, ?_,
      w23, w24, w12, w13, ?_, ?_⟩
    · rw [g₃ _ (by omega) (by omega) (by omega)]; exact q22'
    · ram_simp
    grind
  have w₁ := e₁.wb_right
  have kK : PlConst n C d₁ := hK.keep fun r hr => g₁ r (by omega) (by omega)
  have k07 : d₁.nreg 219007 = p := by grind
  have k16 : d₁.nreg 219016 = ptr := by grind
  have k04 : d₁.nreg 219004 = k := by grind
  have hf₁ : FrameM Brun d d₁ := ⟨fun r hr => g₁ r (by
      simp only [Brun, Bch, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr; omega) (by
      grind [Brun, Bch, Bool.or_eq_false_iff, decide_eq_false_iff_not]),
    (exec_frameM e₁ (by decide : wrM Brun plRunPre = true)).2.1,
    (exec_frameM e₁ (by decide : wrM Brun plRunPre = true)).2.2.1,
    (exec_frameM e₁ (by decide : wrM Brun plRunPre = true)).2.2.2⟩
  by_cases hnw : u + (ℓ - 2) < n
  · -- no wrap-around: one chunk loop
    have hrl : runLeaves n C p a ℓ = chunks C (p + 1) u (ℓ - 2) := by
      grind [runLeaves]
    rw [hrl] at hWt hWk ⊢
    have e₂ := Exec.copyN (P := P) w₁ 219014 219023
    set d₂ : Config := { d₁ with nreg := upd d₁.nreg 219014 (d₁.nreg 219023) } with hd₂
    have g₂ : ∀ r, r ≠ 219014 → d₂.nreg r = d₁.nreg r := fun r hr => by rw [hd₂]; simp [hr]
    have kK₂ : PlConst n C d₂ := kK.keep fun r hr => g₂ r (by omega)
    obtain ⟨d', j₃, e₃, hj₃, c16, c04, cL, cm, cf⟩ := plCh_exec (P := P) hC (ℓ - 2) d₂ (p + 1) u k
      ptr e₂.wb_right kK₂.r02 (by rw [hd₂]; simp [v23]) (by ram_simp)
      (by rw [g₂ _ (by decide), v13]) (by ram_simp)
      (by ram_simp) kK₂.r17 kK₂.r18 kK₂.r20 (by omega) (by omega) hWt hWk
    have ex : Exec P W plRun d d' (j₁ + (1 + j₃ + 1) + 2) :=
      .ifLtN_false (by rw [h11, hK.r20]; exact h3)
        (.seq e₁ (.ifLtN_true (by rw [v24, kK.r01]; exact hnw) (.seq e₂ e₃)))
    refine ⟨d', _, ex, by omega, c16, c04,
      cL, fun x hx => by ram_simp, ?_⟩
    exact hf₁.trans ((exec_frameM e₂ (by decide : wrM Brun (.instr (.copyN 219014 219023)) = true)).trans
      ⟨fun r hr => cf.1 r (by grind [Brun, Bool.or_eq_false_iff]),
        fun r hr => cf.2.1 r (by grind [Brun, Bool.or_eq_false_iff]),
        cf.2.2.1, cf.2.2.2⟩)
  · -- wrap-around: two chunk loops
    have hL1 : n - 1 - u + 1 + (ℓ - 2 - (n - u)) = ℓ - 2 := by omega
    have hrl : runLeaves n C p a ℓ = chunks C (p + 1) u (n - 1 - u) ++
        chunks C (p + 1 + (n - u)) 0 (ℓ - 2 - (n - u)) := by
      grind [runLeaves]
    set ch₁ := chunks C (p + 1) u (n - 1 - u) with hch₁
    set ch₂ := chunks C (p + 1 + (n - u)) 0 (ℓ - 2 - (n - u)) with hch₂
    rw [hrl, List.length_append] at hWt hWk ⊢
    -- the first segment
    have e₂ := Exec.subN (P := P) w₁ 219014 219026 219022
    set d₂ : Config := { d₁ with nreg := upd d₁.nreg 219014 (d₁.nreg 219026 - d₁.nreg 219022) }
      with hd₂
    have g₂ : ∀ r, r ≠ 219014 → d₂.nreg r = d₁.nreg r := fun r hr => by rw [hd₂]; simp [hr]
    have kK₂ : PlConst n C d₂ := kK.keep fun r hr => g₂ r (by omega)
    obtain ⟨d₃, j₃, e₃, hj₃, c16, c04, cL, cm, cf⟩ := plCh_exec (P := P) hC (n - 1 - u) d₂
      (p + 1) u k ptr e₂.wb_right kK₂.r02 (by rw [hd₂]; simp [kK.r26, v22])
      (by ram_simp) (by rw [g₂ _ (by decide), v13])
      (by ram_simp) (by ram_simp) kK₂.r17 kK₂.r18 kK₂.r20
      (by omega) (by omega) (by grind) (by grind)
    rw [← hch₁] at c16 c04 cL cm hj₃
    have g₃ : ∀ r, Bch r = false → d₃.nreg r = d₂.nreg r := cf.1
    have kK₃ : PlConst n C d₃ := kK₂.keep fun r hr => g₃ r (by
      simp only [Bch, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
    have t07 : d₃.nreg 219007 = p := by
      ram_simp
    have t22 : d₃.nreg 219022 = u := by rw [g₃ _ (by decide), g₂ _ (by decide), v22]
    have t23 : d₃.nreg 219023 = ℓ - 2 := by rw [g₃ _ (by decide), g₂ _ (by decide), v23]
    -- the arguments of the second segment
    obtain ⟨d₄, j₄, e₄, hj₄, s12, s13, s14, s16, s04, gs, ms⟩ : ∃ d₄ j₄, Exec P W
        (block [.subN 219025 219001 219022, .addN 219012 219007 219018,
          .addN 219012 219012 219025, .copyN 219013 219017, .subN 219014 219023 219025])
        d₃ d₄ j₄ ∧ j₄ = 5 ∧ d₄.nreg 219012 = p + 1 + (n - u) ∧ d₄.nreg 219013 = 0 ∧
        d₄.nreg 219014 = ℓ - 2 - (n - u) ∧ d₄.nreg 219016 = ptr + 3 * ch₁.length ∧
        d₄.nreg 219004 = k + ch₁.length ∧
        (∀ r, ¬ (219012 ≤ r ∧ r ≤ 219014) → r ≠ 219025 → d₄.nreg r = d₃.nreg r) ∧
        d₄.nmem = d₃.nmem := by
      have q01 := kK₃.r01; have q18 := kK₃.r18; have q17 := kK₃.r17
      have e := e₃.wb_right
      exec_block
      all_goals try (config_simp; omega)
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl⟩ <;> config_simp <;>
        (try simp only [q01, t22, t07, q18, q17, t23, c16, c04])
      first | rfl | (simp only [Machine.upd_apply]; split_ifs <;> omega)
    have kK₄ : PlConst n C d₄ := kK₃.keep fun r hr => gs r (by omega) (by omega)
    obtain ⟨d', j₅, e₅, hj₅, c16', c04', cL', cm', cf'⟩ := plCh_exec (P := P) hC
      (ℓ - 2 - (n - u)) d₄ (p + 1 + (n - u)) 0 (k + ch₁.length) (ptr + 3 * ch₁.length)
      e₄.wb_right kK₄.r02 s14 s12 s13 s16 s04 kK₄.r17 kK₄.r18 kK₄.r20 (by omega) (by omega)
      (by grind) (by grind)
    rw [← hch₂] at c16' c04' cL' cm' hj₅
    have exW : Exec P W plRunW d₁ d' ((1 + 0) + (j₃ + (j₄ + j₅))) :=
      .seq (.seq e₂ (.skip e₂.wb_right)) (.seq e₃ (.seq e₄ e₅))
    have ex : Exec P W plRun d d' (j₁ + ((1 + 0) + (j₃ + (j₄ + j₅)) + 2) + 2) :=
      .ifLtN_false (by rw [h11, hK.r20]; exact h3)
        (.seq e₁ (.ifLtN_false (by rw [v24, kK.r01]; exact hnw) exW))
    refine ⟨d', _, ex, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · refine clAt_append (clAt_congr cL fun x h1 h2 => ?_) ?_
      · rw [cm' x (Or.inl h2), ms]
      · exact cL'
    · intro x hx
      rw [cm' x (by omega), ms, cm x (by omega)]
      grind
    · have f₂ := exec_frameM e₂ (by decide : wrM Brun (.instr (.subN 219014 219026 219022)) = true)
      have f₄ := exec_frameM e₄ (by decide : wrM Brun
        (block [.subN 219025 219001 219022, .addN 219012 219007 219018,
          .addN 219012 219012 219025, .copyN 219013 219017, .subN 219014 219023 219025]) = true)
      have up : ∀ {x y : Config}, FrameM Bch x y → FrameM Brun x y := fun h =>
        ⟨fun r hr => h.1 r (by simp only [Brun, Bool.or_eq_false_iff] at hr; exact hr.1),
          fun r hr => h.2.1 r (by simp only [Brun, Bool.or_eq_false_iff] at hr; exact hr.1),
          h.2.2.1, h.2.2.2⟩
      exact hf₁.trans (f₂.trans ((up cf).trans (f₄.trans (up cf'))))

end exec

end

end DrvR

end Chazelle.Core
