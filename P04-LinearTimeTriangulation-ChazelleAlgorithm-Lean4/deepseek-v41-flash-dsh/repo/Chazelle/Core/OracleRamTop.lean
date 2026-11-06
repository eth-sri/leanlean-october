module

public import Chazelle.Golf

public import Chazelle.Core.OracleRamMain

/-!
# Lemma 3.6 (WP-H), RAM part 15: the top test, the degenerate start, and the phases after loading

* `topS`: the ray above the top vertex misses the chain (answer `0`, done flag `120053`).
* `degS`: the ray starts along a chord: the answer is the far end of the chord (a point of the
  chain, class `1`: flag `1` and the edge of `Q` in `120124`; a side of the box: flag `0`).
* `restS`: the phases after loading: `topS`, then (if not done) the chord search, `degS`, and (if
  not done) `mainS`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK SearchR WalkKey NFLoc
open OracleQ

@[expose] public section

/-- **The top test.** -/
def topS : Stmt :=
  .seq (sgnS 1 (.vtx 120022) (.vtx 120023) (.vtx 120022))
    (.ifLtN 120012 10010 (block [.constN 120005 0, .constN 120053 1]) (.instr (.constN 120053 0)))

/-- **The answer of a degenerate start.** -/
def degS : Stmt :=
  .ifLtN 120012 120140
    (.ifLtN 120012 120143
      (.seq (block [.copyN 120120 120142, .copyN 120121 120023])
        (.seq xpS
          (.seq (.ifLtN 120122 120011 (.instr (.constN 120005 0))
              (.ifLtN 120122 120048 (block [.constN 120005 1, .copyN 120006 120124])
                (.instr (.constN 120005 0))))
            (.instr (.constN 120053 1)))))
      .skip)
    .skip

/-- **The phases after loading.** -/
def restS : Stmt :=
  .seq topS (.ifLtN 120053 120011
    (.seq chordSearchS (.seq chordPostS (.seq degS (.ifLtN 120053 120011 mainS .skip)))) .skip)

/-- The index read off a symbolic point (the edge of an edge point, the vertex of a vertex). -/
def symIdx : SymPt → ℕ
  | .vtx i => i
  | .onEdge e _ => e

/-- **The top test.** -/
theorem topS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {V : QV} (hv : QVOK P C V) (htv : V.tv < P.n) (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) :
    ∃ c' k, Exec P W topS c c' k ∧ k ≤ 250 ∧
      FrameB (fun r => Bk r || decide (r = 120005) || decide (r = 120053)) c c' ∧
      c'.nreg 120053 ≤ 1 ∧
      (c'.nreg 120053 = 1 ↔ ((Qof P).vtx V.tv).2 < ((Qof P).vtx V.hz).2) ∧
      (c'.nreg 120053 = 1 → c'.nreg 120005 = 0) := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, s₁⟩ := sgnS_exec (P := P) hG (⋄) 1 (⊛)
    (.vtx 120022) (.vtx 120023) (.vtx 120022) c hw (⌖) (⌖) (⌖) rfl rfl rfl
    (show c.nreg 120022 < P.n by rw [hq.tv]; exact htv)
    (show c.nreg 120023 < P.n by rw [hq.hz]; exact hv.hz_lt)
    (show c.nreg 120022 < P.n by rw [hq.tv]; exact htv)
  simp only [SignTest, SymPt.eval, hq.tv, hq.hz] at s₁
  have hz₁ : c₁.nreg 120012 = 0 := (f₁.1 _ (⌖)).trans hq.zero
  have w₁ := e₁.wb_right
  suffices H : ∃ c' k, Exec P W (.ifLtN 120012 10010 (block [.constN 120005 0, .constN 120053 1])
      (.instr (.constN 120053 0))) c₁ c' k ∧ k ≤ 4 ∧
      FrameB (fun r => decide (r = 120005) || decide (r = 120053)) c₁ c' ∧ c'.nreg 120053 ≤ 1 ∧
      (c'.nreg 120053 = 1 ↔ c₁.nreg 10010 = 1) ∧ (c'.nreg 120053 = 1 → c'.nreg 120005 = 0) by
    obtain ⟨c', k, ex, hk, f, h1, h2, h3⟩ := H
    refine ⟨c', _, .seq e₁ ex, ⋄, (FrameB.mono f₁ fun r hr => ⊚ hr).trans
      (FrameB.mono f fun r hr => by
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
        rcases hr with hr | hr <;> simp [hr]), h1, by rw [h2]; exact s₁, h3⟩
  by_cases hb : c₁.nreg 10010 = 1
  · obtain ⟨c₂, k₂, e₂, hk₂, v₂⟩ : ∃ c₂ k₂, Exec P W (block [.constN 120005 0, .constN 120053 1])
        c₁ c₂ k₂ ∧ k₂ = 2 ∧ c₂.nreg 120005 = 0 ∧ c₂.nreg 120053 = 1 := by
      exec_block
      · omega
      · omega
      · exact ⟨rfl, by config_simp, by config_simp⟩
    refine ⟨c₂, _, .ifLtN_true (by rw [hz₁, hb]; omega) e₂, ⋄,
      exec_frameB e₂ (⌖), ⋄, by rw [v₂.2]; simp [hb], fun _ => v₂.1⟩
  · have hb0 : c₁.nreg 10010 = 0 := ⋄
    obtain ⟨c₂, e₂, v₂, -⟩ := const_exec (P := P) w₁ 120053 0 (⋄)
    refine ⟨c₂, _, .ifLtN_false (by rw [hz₁, hb0]; omega) e₂, ⋄,
      exec_frameB e₂ (⌖), ⋄, by rw [v₂]; simp [hb], fun h => ⋄⟩

theorem symIdx_of_in {c : Config} {p : SymPt} (h : SymPtIn c 120123 p) :
    c.nreg 120124 = symIdx p := by
  cases p with
  | vtx i => exact h.2
  | onEdge e h' => exact h.2.1

/-- The registers written by `degS`. -/
def BDg (r : ℕ) : Bool :=
  BX r || decide (120120 ≤ r ∧ r ≤ 120121) || decide (r = 120005) || decide (r = 120006) ||
    decide (r = 120053)

theorem wr_degS : wr BDg degS = true := ⌖

/-- **The answer of a degenerate start.** -/
theorem degS_exec {P : Polygon} {W : ℕ} (hW : 8 * P.n + 32 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c)
    {found deg : Prop} {far : ℕ} (h140 : c.nreg 120140 ≤ 1) (h140' : c.nreg 120140 = 1 ↔ found)
    (h142 : found → c.nreg 120142 = far) (h143 : found → c.nreg 120143 ≤ 1)
    (h143' : found → (c.nreg 120143 = 1 ↔ deg)) :
    ∃ c' k, Exec P W degS c c' k ∧ k ≤ 60 ∧ FrameB BDg c c' ∧
      (¬ (found ∧ deg) → ∀ r, c'.nreg r = c.nreg r) ∧
      (found ∧ deg → c'.nreg 120053 = 1 ∧
        (xpClass far = 1 → c'.nreg 120005 = 1 ∧ c'.nreg 120006 = symIdx (xpSym C V P.n far V.hz)) ∧
        (xpClass far ≠ 1 → c'.nreg 120005 = 0)) := by
  suffices H : ∃ c' k, Exec P W degS c c' k ∧ k ≤ 60 ∧
      (¬ (found ∧ deg) → ∀ r, c'.nreg r = c.nreg r) ∧
      (found ∧ deg → c'.nreg 120053 = 1 ∧
        (xpClass far = 1 → c'.nreg 120005 = 1 ∧ c'.nreg 120006 = symIdx (xpSym C V P.n far V.hz)) ∧
        (xpClass far ≠ 1 → c'.nreg 120005 = 0)) by
    obtain ⟨c', k, ex, hk, h1, h2⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex wr_degS, h1, h2⟩
  unfold degS
  by_cases hf : found
  swap
  · have : c.nreg 120140 = 0 := by have := mt h140'.1 hf; omega
    exact ⟨c, _, .ifLtN_false (by rw [hq.zero, this]; omega) (.skip hw), ⋄,
      fun _ _ => rfl, fun h => absurd h.1 hf⟩
  have hf1 : c.nreg 120140 = 1 := h140'.2 hf
  by_cases hd : deg
  swap
  · have : c.nreg 120143 = 0 := by have := h143 hf; have := mt (h143' hf).1 hd; omega
    exact ⟨c, _, .ifLtN_true (by rw [hq.zero, hf1]; omega)
      (.ifLtN_false (by rw [hq.zero, this]; omega) (.skip hw)), ⋄,
      fun _ _ => rfl, fun h => absurd h.2 hd⟩
  have hd1 : c.nreg 120143 = 1 := (h143' hf).2 hd
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 120120 120142, .copyN 120121 120023])
      c c₁ k₁ ∧ k₁ = 2 ∧ (c₁.nreg 120120 = far ∧ c₁.nreg 120121 = V.hz ∧
        ∀ r, r ≠ 120120 → r ≠ 120121 → c₁.nreg r = c.nreg r) := by
    exec_block
    exact ⟨rfl, by config_simp; exact h142 hf, by config_simp; exact hq.hz,
      fun r h1 h2 => by config_simp; upd_solve⟩
  obtain ⟨x120, x121, r₁⟩ := v₁
  have hq₁ : QConst P V c₁ := hq.congr fun r h1 h2 => r₁ r (⋄) (⋄)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, v₂, s₂⟩ := xpS_exec (P := P) (⋄) hv c₁ e₁.wb_right hq₁
  rw [x120] at v₂
  rw [x120, x121] at s₂
  have hq₂ : QConst P V c₂ := hq₁.frame f₂ fun r h1 h2 => by
    simp only [BX, decide_eq_false_iff_not, not_and, not_le]; omega
  have w₂ := e₂.wb_right
  have hcl := xpClass_le far
  -- the answer
  obtain ⟨c₃, k₃, e₃, hk₃, a₃, b₃⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 120122 120011 (.instr (.constN 120005 0))
      (.ifLtN 120122 120048 (block [.constN 120005 1, .copyN 120006 120124])
        (.instr (.constN 120005 0)))) c₂ c₃ k₃ ∧ k₃ ≤ 5 ∧
      (xpClass far = 1 → c₃.nreg 120005 = 1 ∧ c₃.nreg 120006 = symIdx (xpSym C V P.n far V.hz)) ∧
      (xpClass far ≠ 1 → c₃.nreg 120005 = 0) := by
    by_cases h0 : xpClass far = 0
    · obtain ⟨c₃, e₃, v₃, -⟩ := const_exec (P := P) w₂ 120005 0 (⋄)
      exact ⟨c₃, _, .ifLtN_true (by rw [v₂, hq₂.one, h0]; omega) e₃, ⋄,
        fun h => absurd h (⋄), fun _ => v₃⟩
    by_cases h1 : xpClass far = 1
    · obtain ⟨c₃, k₃, e₃, hk₃, v₃⟩ : ∃ c₃ k₃, Exec P W (block [.constN 120005 1,
          .copyN 120006 120124]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ c₃.nreg 120005 = 1 ∧
          c₃.nreg 120006 = c₂.nreg 120124 := by
        exec_block
        · omega
        · exact ⟨rfl, by config_simp, by config_simp⟩
      exact ⟨c₃, _, .ifLtN_false (by rw [v₂, hq₂.one, h1]; omega)
        (.ifLtN_true (by rw [v₂, hq₂.two, h1]; omega) e₃), ⋄,
        fun _ => ⟨v₃.1, by rw [v₃.2]; exact symIdx_of_in (s₂ h1)⟩, fun h => absurd h1 h⟩
    · obtain ⟨c₃, e₃, v₃, -⟩ := const_exec (P := P) w₂ 120005 0 (⋄)
      exact ⟨c₃, _, .ifLtN_false (by rw [v₂, hq₂.one]; omega)
        (.ifLtN_false (by rw [v₂, hq₂.two]; omega) e₃), ⋄,
        fun h => absurd h h1, fun _ => v₃⟩
  obtain ⟨c₄, e₄, v₄, r₄⟩ := const_exec (P := P) e₃.wb_right 120053 1 (⋄)
  refine ⟨c₄, _, .ifLtN_true (by rw [hq.zero, hf1]; omega) (.ifLtN_true (by rw [hq.zero, hd1]; omega)
    (.seq e₁ (.seq e₂ (.seq e₃ e₄)))), ⋄, fun h => absurd ⟨hf, hd⟩ h, fun _ => ⟨v₄, ?_, ?_⟩⟩
  · intro h; rw [r₄ _ (⌖), r₄ _ (⌖)]; exact a₃ h
  · intro h; rw [r₄ _ (⌖)]; exact b₃ h

/-- The registers written by `restS`. -/
def BRest (r : ℕ) : Bool :=
  Bk r || decide (r = 120005) || decide (r = 120053) || BCS r || BCP r || BDg r || BMain r

open Classical in
theorem selOf_congr {C : Chain} {V : QV} {bD : Option ℕ} {f f' : Prop} {w w' : ℕ} {cb cb' : Prop}
    (hf : f ↔ f') (hw : f → w = w') (hcb : f → (cb ↔ cb')) :
    selOf C V bD f w cb = selOf C V bD f' w' cb' := by
  unfold selOf
  by_cases h : f
  · have h' : f' := hf.1 h
    Ξ hw h, propext (hcb h), propext hf
  · have h' : ¬ f' := fun x => h (hf.2 x)
    Ξ ite_eq_right (fun x => h x.1), ite_eq_right (fun x => h' x.1)

/-- The partition point of the chord search. -/
def PartC (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (t : ℕ) : Prop :=
  t ≤ V.K ∧ (∀ j, j < t → chPr P C V m (chAt m V j) = true) ∧
    (t < V.K → chPr P C V m (chAt m V t) = false)

open Classical in
/-- The four walk positions of the main phase, for the partition point `t` and the hit `bD`. -/
noncomputable def mainPos (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (t : ℕ)
    (bD : Option ℕ) : ℕ × ℕ × ℕ × ℕ :=
  posOf V P.n (selOf C V bD (FoundC V m t) (nearC V m t) (CBof P C V bD (nearC V m t)))

end

end OracleR

end Chazelle.Core
