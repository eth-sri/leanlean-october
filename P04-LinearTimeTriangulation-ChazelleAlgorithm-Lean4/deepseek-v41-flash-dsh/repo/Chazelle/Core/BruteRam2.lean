module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.BruteRam1

/-!
# WP-K on the RAM, part 2: the orientation bit and the descriptor

* `bitS`: the orientation bit `sideBeta` of the chain (`0` if the top is the first vertex, else
  six sign tests and a boolean combination computed with `+` and truncated `-`: `x ∧ y = x + y - 1`,
  `x ∨ y = x + y - (x + y - 1)`, `¬ x = 1 - x`);
* `sS`: the tour start `S = sideS sideBeta`;
* `descS`: the host `Host.whole n` at `A₀` and the model descriptor at `A₀ + 4`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace Brute

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- The whole host describes the polygon itself. -/
theorem poly_whole (Q : Polygon) (hQ : 1 ≤ Q.n) : (Host.whole Q.n).poly Q = Q := by
  cases Q with
  | mk l =>
    unfold Host.poly Host.whole Host.pts HostItem.pts
    ϴ List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, zero_add
    congr 1
    have hn : (⟨l⟩ : Polygon).n = l.length := rfl
    have hQ' := hQ
    Ξ hn
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      ϴ List.getElem_map, List.getElem_range, Function.comp
      ϴ' List.length_map, List.length_range at h1
      Ξ Nat.mod_eq_of_lt (⋄)
      ϴ SymPt.eval, Polygon.vtx
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl

/-! ## The boolean combination of the orientation bit -/

/-- `bit := (d₊ ∧ bx ∧ ax) ∨ (¬d₊ ∧ ¬d₀ ∧ (bx ∨ ax)) ∨ (d₀ ∧ by ∧ bx) ∨ (d₀ ∧ by')`, from the
bits `d₊ = 63, d₀ = 64, bx = 65, ax = 66, by = 67, by' = 68`. -/
def logicB : Stmt :=
  .seq (andS 180069 180063 180065) (.seq (andS 180069 180069 180066)
  (.seq (notS 180070 180063) (.seq (notS 180071 180064) (.seq (andS 180070 180070 180071)
  (.seq (orS 180071 180065 180066 180072) (.seq (andS 180070 180070 180071)
  (.seq (andS 180071 180064 180067) (.seq (andS 180071 180071 180065)
  (.seq (andS 180072 180064 180068) (.seq (orS 180073 180069 180070 180074)
  (.seq (orS 180073 180073 180071 180074) (orS 180014 180073 180072 180074))))))))))))

/-- The write set of `logicB`. -/
def Blog (r : ℕ) : Bool := decide (180069 ≤ r ∧ r < 180075) || decide (r = 180014)

theorem fr1 {d : ℕ} {c c' : Config} (F : FrameB (fun r => decide (r = d)) c c') {q : ℕ}
    (hq : q ≠ d) : c'.nreg q = c.nreg q := F.1 q (by simpa using hq)

theorem fr2 {d t : ℕ} {c c' : Config} (F : FrameB (fun r => decide (r = d ∨ r = t)) c c') {q : ℕ}
    (hq : q ≠ d) (hq' : q ≠ t) : c'.nreg q = c.nreg q := F.1 q (⊚ hq, hq')

theorem frLog1 {d : ℕ} (hd : Blog d = true) {c c' : Config}
    (F : FrameB (fun r => decide (r = d)) c c') : FrameB Blog c c' :=
  frameB_mono F fun r hr => by
    simp only [decide_eq_false_iff_not]; rintro rfl; Ξ' hd at hr; exact Bool.noConfusion hr

theorem frLog2 {d t : ℕ} (hd : Blog d = true) (ht : Blog t = true) {c c' : Config}
    (F : FrameB (fun r => decide (r = d ∨ r = t)) c c') : FrameB Blog c c' :=
  frameB_mono F fun r hr => by
    ϴ decide_eq_false_iff_not, not_or
    refine ⟨?_, ?_⟩ <;> rintro rfl <;> simp_all

theorem and_bit {x y : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) :
    x + y - 1 ≤ 1 ∧ (x + y - 1 = 1 ↔ x = 1 ∧ y = 1) := ⋄

theorem or_bit {x y : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) :
    (x + y) - (x + y - 1) ≤ 1 ∧ ((x + y) - (x + y - 1) = 1 ↔ x = 1 ∨ y = 1) := ⋄

theorem not_bit {x : ℕ} (hx : x ≤ 1) : 1 - x ≤ 1 ∧ (1 - x = 1 ↔ x = 0) := ⋄

theorem logicB_exec {P : Polygon} {W : ℕ} (hW : 8 ≤ W) (c : Config) (hw : WordsBounded W c)
    (h11 : c.nreg 180011 = 1) (b63 : c.nreg 180063 ≤ 1) (b64 : c.nreg 180064 ≤ 1)
    (b65 : c.nreg 180065 ≤ 1) (b66 : c.nreg 180066 ≤ 1) (b67 : c.nreg 180067 ≤ 1)
    (b68 : c.nreg 180068 ≤ 1) :
    ∃ c' k, Exec P W logicB c c' k ∧ k = 28 ∧ FrameB Blog c c' ∧
      c'.nreg 180014 ≤ 1 ∧
      (c'.nreg 180014 = 1 ↔
        (c.nreg 180063 = 1 ∧ c.nreg 180065 = 1 ∧ c.nreg 180066 = 1) ∨
        (c.nreg 180063 = 0 ∧ c.nreg 180064 = 0 ∧ (c.nreg 180065 = 1 ∨ c.nreg 180066 = 1)) ∨
        (c.nreg 180064 = 1 ∧ c.nreg 180067 = 1 ∧ c.nreg 180065 = 1) ∨
        (c.nreg 180064 = 1 ∧ c.nreg 180068 = 1)) := by
  have W2 : 2 ≤ W := ⋄
  -- A = d₊ ∧ bx ∧ ax
  obtain ⟨c1, k1, e1, hk1, v1, F1⟩ := andS_exec (P := P) W2 c hw (d := 180069) (x := 180063)
    (y := 180065) (⌖) h11 b63 b65
  have B1 := and_bit b63 b65
  Ξ' ← v1 at B1
  have o1 : c1.nreg 180011 = 1 := Ρ fr1 F1 (⌖), h11
  have a66 : c1.nreg 180066 = c.nreg 180066 := fr1 F1 (⌖)
  obtain ⟨c2, k2, e2, hk2, v2, F2⟩ := andS_exec (P := P) W2 c1 e1.wb_right (d := 180069)
    (x := 180069) (y := 180066) (⌖) o1 B1.1 (by rw [a66]; exact b66)
  have B2 := and_bit B1.1 (show c1.nreg 180066 ≤ 1 by rw [a66]; exact b66)
  Ξ' ← v2, a66, B1.2 at B2
  have o2 : c2.nreg 180011 = 1 := Ρ fr1 F2 (⌖), o1
  have r63 : c2.nreg 180063 = c.nreg 180063 := Ρ fr1 F2 (⌖), fr1 F1 (⌖)
  -- B = ¬d₊ ∧ ¬d₀ ∧ (bx ∨ ax)
  obtain ⟨c3, k3, e3, hk3, v3, F3⟩ := notS_exec (P := P) c2 e2.wb_right (d := 180070)
    (x := 180063) (⌖) o2
  have B3 := not_bit (show c2.nreg 180063 ≤ 1 by rw [r63]; exact b63)
  Ξ' ← v3, r63 at B3
  have o3 : c3.nreg 180011 = 1 := Ρ fr1 F3 (⌖), o2
  have r64 : c3.nreg 180064 = c.nreg 180064 := by
    Ξ fr1 F3 (⌖), fr1 F2 (⌖), fr1 F1 (⌖)
  obtain ⟨c4, k4, e4, hk4, v4, F4⟩ := notS_exec (P := P) c3 e3.wb_right (d := 180071)
    (x := 180064) (⌖) o3
  have B4 := not_bit (show c3.nreg 180064 ≤ 1 by rw [r64]; exact b64)
  Ξ' ← v4, r64 at B4
  have o4 : c4.nreg 180011 = 1 := Ρ fr1 F4 (⌖), o3
  have r70 : c4.nreg 180070 = c3.nreg 180070 := fr1 F4 (⌖)
  obtain ⟨c5, k5, e5, hk5, v5, F5⟩ := andS_exec (P := P) W2 c4 e4.wb_right (d := 180070)
    (x := 180070) (y := 180071) (⌖) o4 (by rw [r70]; exact B3.1) B4.1
  have B5 := and_bit (show c4.nreg 180070 ≤ 1 by rw [r70]; exact B3.1) B4.1
  Ξ' ← v5, r70, B3.2, B4.2 at B5
  have o5 : c5.nreg 180011 = 1 := Ρ fr1 F5 (⌖), o4
  have r65 : c5.nreg 180065 = c.nreg 180065 := by
    rw [fr1 F5 (⌖), fr1 F4 (⌖), fr1 F3 (⌖), fr1 F2 (⌖),
      fr1 F1 (⌖)]
  have r66 : c5.nreg 180066 = c.nreg 180066 := by
    Ξ fr1 F5 (⌖), fr1 F4 (⌖), fr1 F3 (⌖), fr1 F2 (⌖), a66
  obtain ⟨c6, k6, e6, hk6, v6, F6⟩ := orS_exec (P := P) W2 c5 e5.wb_right (d := 180071)
    (x := 180065) (y := 180066) (t := 180072) (⌖) (⌖) (⌖) o5
    (by rw [r65]; exact b65) (by rw [r66]; exact b66)
  have B6 := or_bit (show c5.nreg 180065 ≤ 1 by rw [r65]; exact b65)
    (show c5.nreg 180066 ≤ 1 by rw [r66]; exact b66)
  Ξ' ← v6, r65, r66 at B6
  have o6 : c6.nreg 180011 = 1 := Ρ fr2 F6 (⌖) (⌖), o5
  have r70' : c6.nreg 180070 = c5.nreg 180070 := fr2 F6 (⌖) (⌖)
  obtain ⟨c7, k7, e7, hk7, v7, F7⟩ := andS_exec (P := P) W2 c6 e6.wb_right (d := 180070)
    (x := 180070) (y := 180071) (⌖) o6 (by rw [r70']; exact B5.1) B6.1
  have B7 := and_bit (show c6.nreg 180070 ≤ 1 by rw [r70']; exact B5.1) B6.1
  Ξ' ← v7, r70', B5.2, B6.2 at B7
  have o7 : c7.nreg 180011 = 1 := Ρ fr1 F7 (⌖), o6
  -- C = d₀ ∧ by ∧ bx
  have s64 : c7.nreg 180064 = c.nreg 180064 := by
    rw [fr1 F7 (⌖), fr2 F6 (⌖) (⌖), fr1 F5 (⌖),
      fr1 F4 (⌖), r64]
  have s67 : c7.nreg 180067 = c.nreg 180067 := by
    rw [fr1 F7 (⌖), fr2 F6 (⌖) (⌖), fr1 F5 (⌖),
      fr1 F4 (⌖), fr1 F3 (⌖), fr1 F2 (⌖), fr1 F1 (⌖)]
  obtain ⟨c8, k8, e8, hk8, v8, F8⟩ := andS_exec (P := P) W2 c7 e7.wb_right (d := 180071)
    (x := 180064) (y := 180067) (⌖) o7 (by rw [s64]; exact b64) (by rw [s67]; exact b67)
  have B8 := and_bit (show c7.nreg 180064 ≤ 1 by rw [s64]; exact b64)
    (show c7.nreg 180067 ≤ 1 by rw [s67]; exact b67)
  Ξ' ← v8, s64, s67 at B8
  have o8 : c8.nreg 180011 = 1 := Ρ fr1 F8 (⌖), o7
  have s65 : c8.nreg 180065 = c.nreg 180065 := by
    Ξ fr1 F8 (⌖), fr1 F7 (⌖), fr2 F6 (⌖) (⌖), r65
  obtain ⟨c9, k9, e9, hk9, v9, F9⟩ := andS_exec (P := P) W2 c8 e8.wb_right (d := 180071)
    (x := 180071) (y := 180065) (⌖) o8 B8.1 (by rw [s65]; exact b65)
  have B9 := and_bit B8.1 (show c8.nreg 180065 ≤ 1 by rw [s65]; exact b65)
  Ξ' ← v9, s65, B8.2 at B9
  have o9 : c9.nreg 180011 = 1 := Ρ fr1 F9 (⌖), o8
  -- D = d₀ ∧ by'
  have t64 : c9.nreg 180064 = c.nreg 180064 := by
    Ξ fr1 F9 (⌖), fr1 F8 (⌖), s64
  have t68 : c9.nreg 180068 = c.nreg 180068 := by
    rw [fr1 F9 (⌖), fr1 F8 (⌖), fr1 F7 (⌖),
      fr2 F6 (⌖) (⌖), fr1 F5 (⌖), fr1 F4 (⌖), fr1 F3 (⌖),
      fr1 F2 (⌖), fr1 F1 (⌖)]
  obtain ⟨c10, k10, e10, hk10, v10, F10⟩ := andS_exec (P := P) W2 c9 e9.wb_right (d := 180072)
    (x := 180064) (y := 180068) (⌖) o9 (by rw [t64]; exact b64) (by rw [t68]; exact b68)
  have B10 := and_bit (show c9.nreg 180064 ≤ 1 by rw [t64]; exact b64)
    (show c9.nreg 180068 ≤ 1 by rw [t68]; exact b68)
  Ξ' ← v10, t64, t68 at B10
  have o10 : c10.nreg 180011 = 1 := Ρ fr1 F10 (⌖), o9
  -- the disjunction
  have x69 : c10.nreg 180069 = c2.nreg 180069 := by
    rw [fr1 F10 (⌖), fr1 F9 (⌖), fr1 F8 (⌖), fr1 F7 (⌖),
      fr2 F6 (⌖) (⌖), fr1 F5 (⌖), fr1 F4 (⌖), fr1 F3 (⌖)]
  have x70 : c10.nreg 180070 = c7.nreg 180070 := by
    Ξ fr1 F10 (⌖), fr1 F9 (⌖), fr1 F8 (⌖)
  have x71 : c10.nreg 180071 = c9.nreg 180071 := fr1 F10 (⌖)
  obtain ⟨c11, k11, e11, hk11, v11, F11⟩ := orS_exec (P := P) W2 c10 e10.wb_right (d := 180073)
    (x := 180069) (y := 180070) (t := 180074) (⌖) (⌖) (⌖) o10
    (by rw [x69]; exact B2.1) (by rw [x70]; exact B7.1)
  have B11 := or_bit (show c10.nreg 180069 ≤ 1 by rw [x69]; exact B2.1)
    (show c10.nreg 180070 ≤ 1 by rw [x70]; exact B7.1)
  Ξ' ← v11, x69, x70, B2.2, B7.2 at B11
  have o11 : c11.nreg 180011 = 1 := Ρ fr2 F11 (⌖) (⌖), o10
  have y71 : c11.nreg 180071 = c9.nreg 180071 := by
    Ξ fr2 F11 (⌖) (⌖), x71
  obtain ⟨c12, k12, e12, hk12, v12, F12⟩ := orS_exec (P := P) W2 c11 e11.wb_right (d := 180073)
    (x := 180073) (y := 180071) (t := 180074) (⌖) (⌖) (⌖) o11
    B11.1 (by rw [y71]; exact B9.1)
  have B12 := or_bit B11.1 (show c11.nreg 180071 ≤ 1 by rw [y71]; exact B9.1)
  Ξ' ← v12, y71, B11.2, B9.2 at B12
  have o12 : c12.nreg 180011 = 1 := Ρ fr2 F12 (⌖) (⌖), o11
  have y72 : c12.nreg 180072 = c10.nreg 180072 := by
    Ξ fr2 F12 (⌖) (⌖), fr2 F11 (⌖) (⌖)
  obtain ⟨c13, k13, e13, hk13, v13, F13⟩ := orS_exec (P := P) W2 c12 e12.wb_right (d := 180014)
    (x := 180073) (y := 180072) (t := 180074) (⌖) (⌖) (⌖) o12
    B12.1 (by rw [y72]; exact B10.1)
  have B13 := or_bit B12.1 (show c12.nreg 180072 ≤ 1 by rw [y72]; exact B10.1)
  Ξ' ← v13, y72, B12.2, B10.2 at B13
  have ex : Exec P W logicB c c13 (k1 + (k2 + (k3 + (k4 + (k5 + (k6 + (k7 + (k8 + (k9 + (k10 +
      (k11 + (k12 + k13)))))))))))) := .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6
    (.seq e7 (.seq e8 (.seq e9 (.seq e10 (.seq e11 (.seq e12 e13)))))))))))
  refine ⟨c13, _, ex, by subst_vars; rfl, ?_, B13.1, ?_⟩
  · have G1 := frLog1 (⌖) F1
    have G2 := frLog1 (⌖) F2
    have G3 := frLog1 (⌖) F3
    have G4 := frLog1 (⌖) F4
    have G5 := frLog1 (⌖) F5
    have G6 := frLog2 (⌖) (⌖) F6
    have G7 := frLog1 (⌖) F7
    have G8 := frLog1 (⌖) F8
    have G9 := frLog1 (⌖) F9
    have G10 := frLog1 (⌖) F10
    have G11 := frLog2 (⌖) (⌖) F11
    have G12 := frLog2 (⌖) (⌖) F12
    have G13 := frLog2 (⌖) (⌖) F13
    exact (((((((((((G1.trans G2).trans G3).trans G4).trans G5).trans G6).trans G7).trans
      G8).trans G9).trans G10).trans G11).trans G12).trans G13
  · rw [B13.2]; ϴ and_assoc, or_assoc

/-! ## The orientation bit -/

/-- The six tests and the combination (top index `T > 0`). -/
def bitGen : Stmt :=
  .seq (block [.addN 180060 180000 180013, .subN 180061 180060 180011, .addN 180062 180060 180011])
    (.seq (.ifLtN 180062 180010 .skip (.instr (.constN 180062 0)))
    (.seq (testS 2 (.v 180061) (.v 180060) (.v 180062) 180063)
    (.seq (testS 3 (.v 180061) (.v 180060) (.v 180062) 180064)
    (.seq (testS 0 (.v 180060) (.v 180062) (.v 180060) 180065)
    (.seq (testS 0 (.v 180061) (.v 180060) (.v 180060) 180066)
    (.seq (testS 1 (.v 180060) (.v 180062) (.v 180060) 180067)
    (.seq (testS 1 (.v 180062) (.v 180060) (.v 180060) 180068) logicB)))))))

/-- The orientation bit. -/
def bitS : Stmt := .ifLtN 180028 180013 bitGen (.instr (.constN 180014 0))

/-- The write set of `bitS`: the kernel and `180014`, `180060 … 180074`. -/
def Bbit (r : ℕ) : Bool := Bk r || decide (r = 180014 ∨ (180060 ≤ r ∧ r < 180075))

theorem frame_test_bit {d : ℕ} (hd : 180060 ≤ d ∧ d < 180075) :
    ∀ r, Bbit r = false → Bt d r = false := by
  intro r hr
  unfold Bbit at hr; unfold Bt
  ϴ' Bool.or_eq_false_iff, decide_eq_false_iff_not at hr ⊢
  exact ⟨hr.1, ⋄⟩

/-- A test on three vertices held in registers. -/
theorem testV_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {op : ℕ}
    (hop : op ≤ 3) {r₁ r₂ r₃ d : ℕ} (h₁ : r₁ < 10000 ∨ 10500 ≤ r₁) (h₂ : r₂ < 10000 ∨ 10500 ≤ r₂)
    (h₃ : r₃ < 10000 ∨ 10500 ≤ r₃) (c : Config) (hw : WordsBounded W c) {x₁ x₂ x₃ : ℕ}
    (e₁ : c.nreg r₁ = x₁) (e₂ : c.nreg r₂ = x₂) (e₃ : c.nreg r₃ = x₃) (l₁ : x₁ < P.n)
    (l₂ : x₂ < P.n) (l₃ : x₃ < P.n) :
    ∃ c' k, Exec P W (testS op (.v r₁) (.v r₂) (.v r₃) d) c c' k ∧ k ≤ 245 ∧
      FrameB (Bt d) c c' ∧ c'.nreg d ≤ 1 ∧
      (c'.nreg d = 1 ↔ SignTest op ((Qof P).vtx x₁) ((Qof P).vtx x₂) ((Qof P).vtx x₃)) := by
  obtain ⟨c', k, e, hk, F, b, hb⟩ := testS_exec (P := P) hG hW hop (x := .v r₁) (y := .v r₂)
    (z := .v r₃) (d := d) h₁ h₂ h₃ c hw (by simp only [Src.pt, SymPt.Lt]; omega)
    (by simp only [Src.pt, SymPt.Lt]; omega) (by simp only [Src.pt, SymPt.Lt]; omega)
  ϴ' Src.pt, SymPt.eval, e₁, e₂, e₃ at hb
  exact ⟨c', k, e, hk, F, b, hb⟩

theorem bt_keep {d r : ℕ} {c c' : Config} (F : FrameB (Bt d) c c') (hr : r < 10000 ∨ 10500 ≤ r)
    (hd : r ≠ d) : c'.nreg r = c.nreg r := by
  apply F.1
  unfold Bt Bk
  ϴ Bool.or_eq_false_iff, decide_eq_false_iff_not
  omega

theorem bit_of {x : ℕ} {p : Prop} (hb : x ≤ 1) (h : x = 1 ↔ p) : (x = 0 ↔ ¬ p) := by
  constructor
  · intro h0 hp; have := h.2 hp; omega
  · intro hn; by_contra h0; exact hn (h.1 (⋄))

/-- The orientation bit in terms of the sign tests of `bitGen`. -/
theorem sideBeta_tests {P : Polygon} (hG : GoodEnv P) {C : Chain} (hC : C.P = Qof P)
    (hsn : C.s + C.m + 1 ≤ P.n) (hT0 : 0 < C.topIdx) :
    C.sideBeta = true ↔
      (0 < det ((Qof P).vtx (C.s + C.topIdx - 1)) ((Qof P).vtx (C.s + C.topIdx))
          ((Qof P).vtx ((C.s + C.topIdx + 1) % P.n)) ∧
        ((Qof P).vtx (C.s + C.topIdx)).1 < ((Qof P).vtx ((C.s + C.topIdx + 1) % P.n)).1 ∧
        ((Qof P).vtx (C.s + C.topIdx - 1)).1 < ((Qof P).vtx (C.s + C.topIdx)).1) ∨
      (¬ 0 < det ((Qof P).vtx (C.s + C.topIdx - 1)) ((Qof P).vtx (C.s + C.topIdx))
          ((Qof P).vtx ((C.s + C.topIdx + 1) % P.n)) ∧
        ¬ det ((Qof P).vtx (C.s + C.topIdx - 1)) ((Qof P).vtx (C.s + C.topIdx))
          ((Qof P).vtx ((C.s + C.topIdx + 1) % P.n)) = 0 ∧
        (((Qof P).vtx (C.s + C.topIdx)).1 < ((Qof P).vtx ((C.s + C.topIdx + 1) % P.n)).1 ∨
          ((Qof P).vtx (C.s + C.topIdx - 1)).1 < ((Qof P).vtx (C.s + C.topIdx)).1)) ∨
      (det ((Qof P).vtx (C.s + C.topIdx - 1)) ((Qof P).vtx (C.s + C.topIdx))
          ((Qof P).vtx ((C.s + C.topIdx + 1) % P.n)) = 0 ∧
        ((Qof P).vtx (C.s + C.topIdx)).2 < ((Qof P).vtx ((C.s + C.topIdx + 1) % P.n)).2 ∧
        ((Qof P).vtx (C.s + C.topIdx)).1 < ((Qof P).vtx ((C.s + C.topIdx + 1) % P.n)).1) ∨
      (det ((Qof P).vtx (C.s + C.topIdx - 1)) ((Qof P).vtx (C.s + C.topIdx))
          ((Qof P).vtx ((C.s + C.topIdx + 1) % P.n)) = 0 ∧
        ((Qof P).vtx ((C.s + C.topIdx + 1) % P.n)).2 < ((Qof P).vtx (C.s + C.topIdx)).2) := by
  have hDH : DistinctHeights C.P := by rw [hC]; exact (goodShear_epsOf hG.2).2.1
  have hn : C.P.n = P.n := by rw [hC]; exact shear_n _ _
  have hT := C.topIdx_le
  have eA : C.vertex (C.topIdx - 1) = (Qof P).vtx (C.s + C.topIdx - 1) := by
    have h1 : C.s + (C.topIdx - 1) < C.P.n := by rw [hn]; omega
    have h2 : C.s + (C.topIdx - 1) = C.s + C.topIdx - 1 := ⋄
    Ξ vertex_eq h1, h2, hC
  have eT : C.top = (Qof P).vtx (C.s + C.topIdx) := by
    have h1 : C.s + C.topIdx < C.P.n := by rw [hn]; omega
    show C.vertex C.topIdx = _
    Ξ vertex_eq h1, hC
  have eB : C.vertex (C.topIdx + 1) = (Qof P).vtx ((C.s + C.topIdx + 1) % P.n) := by
    show C.P.vtx ((C.s + (C.topIdx + 1)) % C.P.n) = _
    Ξ ← Nat.add_assoc, hn, hC
  Ξ sideBeta_iff (C := C) hDH hT0, eA, eT, eB
  constructor
  · rintro (h | ⟨h1, h3⟩ | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨not_lt.2 h1.le, h1.ne, h3⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | ⟨h1, h2, h3⟩ | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨lt_of_le_of_ne (not_lt.1 h1) h2, h3⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))


/-- **The orientation bit** for a top vertex other than the first. -/
theorem bitGen_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (hW8 : 8 ≤ W)
    {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) (hT0 : 0 < C.topIdx) (c : Config)
    (hw : WordsBounded W c) (h0 : c.nreg 180000 = C.s) (h10 : c.nreg 180010 = P.n)
    (h11 : c.nreg 180011 = 1) (h13 : c.nreg 180013 = C.topIdx) :
    ∃ c' k, Exec P W bitGen c c' k ∧ k ≤ 1600 ∧ FrameB Bbit c c' ∧ c'.nreg 180014 ≤ 1 ∧
      (c'.nreg 180014 = 1 ↔ C.sideBeta = true) := by
  have hDH : DistinctHeights C.P := by rw [hC]; exact (goodShear_epsOf hG.2).2.1
  have hn : C.P.n = P.n := by rw [hC]; exact shear_n _ _
  have hT := C.topIdx_le
  set T := C.topIdx with hTd
  set a := C.s with had
  -- the three indices
  obtain ⟨c₁, k₁, e₁, hk₁, q60, q61, q62, R₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 180060 180000 180013,
      .subN 180061 180060 180011, .addN 180062 180060 180011]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 180060 = a + T ∧ c₁.nreg 180061 = a + T - 1 ∧ c₁.nreg 180062 = a + T + 1 ∧
      FrameB (fun r => decide (180060 ≤ r ∧ r < 180063)) c c₁ := by
    exec_block
    · config_simp; rw [h0, h13]; omega
    · config_simp; rw [h0, h13, h11]; omega
    · refine ⟨rfl, ?_, ?_, ?_, ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩⟩
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        Ξ h0, h13
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        Ξ h0, h13, h11
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        Ξ h0, h13, h11
      · ϴ' decide_eq_false_iff_not at hr
        simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
  have w₁ := e₁.wb_right
  have k10 : c₁.nreg 180010 = P.n := Ρ R₁.1 _ (⌖), h10
  have k11 : c₁.nreg 180011 = 1 := Ρ R₁.1 _ (⌖), h11
  -- the index after the top, modulo `n`
  set qb := (a + T + 1) % P.n with hqb
  have hqbn : qb < P.n := Nat.mod_lt _ (⋄)
  obtain ⟨c₂, k₂, e₂, hk₂, q62', R₂⟩ : ∃ c₂ k₂, Exec P W
      (.ifLtN 180062 180010 .skip (.instr (.constN 180062 0))) c₁ c₂ k₂ ∧ k₂ ≤ 3 ∧
      c₂.nreg 180062 = qb ∧ FrameB (fun r => decide (r = 180062)) c₁ c₂ := by
    by_cases hlt : a + T + 1 < P.n
    · refine ⟨_, _, .ifLtN_true (by rw [q62, k10]; exact hlt) (.skip w₁), ⋄, ?_,
        FrameB.refl _ _⟩
      Ξ q62, hqb, Nat.mod_eq_of_lt hlt
    · have hq : a + T + 1 = P.n := ⋄
      refine ⟨_, _, .ifLtN_false (by rw [q62, k10]; exact hlt)
        (Exec.constN w₁ 180062 0 (⋄)), le_refl _, ?_, ⟨fun r hr => ?_, fun r _ => rfl,
        rfl, rfl, rfl⟩⟩
      · Θ hqb, hq
      · ϴ' decide_eq_false_iff_not at hr
        Θ hr
  have w₂ := e₂.wb_right
  have p60 : c₂.nreg 180060 = a + T := Ρ R₂.1 _ (⌖), q60
  have p61 : c₂.nreg 180061 = a + T - 1 := Ρ R₂.1 _ (⌖), q61
  have lt60 : a + T < P.n := ⋄
  have lt61 : a + T - 1 < P.n := ⋄
  -- six tests
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, b63, t63⟩ := testV_exec (P := P) hG hW (op := 2) (⋄)
    (r₁ := 180061) (r₂ := 180060) (r₃ := 180062) (d := 180063) (Or.inr (⋄))
    (Or.inr (⋄)) (Or.inr (⋄)) c₂ w₂ p61 p60 q62' lt61 lt60 hqbn
  have p60₃ : c₃.nreg 180060 = a + T := Ρ bt_keep F₃ (Or.inr (⋄)) (⋄), p60
  have p61₃ : c₃.nreg 180061 = a + T - 1 := Ρ bt_keep F₃ (Or.inr (⋄)) (⋄), p61
  have p62₃ : c₃.nreg 180062 = qb := Ρ bt_keep F₃ (Or.inr (⋄)) (⋄), q62'
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, b64, t64⟩ := testV_exec (P := P) hG hW (op := 3) (⋄)
    (r₁ := 180061) (r₂ := 180060) (r₃ := 180062) (d := 180064) (Or.inr (⋄))
    (Or.inr (⋄)) (Or.inr (⋄)) c₃ e₃.wb_right p61₃ p60₃ p62₃ lt61 lt60 hqbn
  have p60₄ : c₄.nreg 180060 = a + T := Ρ bt_keep F₄ (Or.inr (⋄)) (⋄), p60₃
  have p61₄ : c₄.nreg 180061 = a + T - 1 := by
    Ξ bt_keep F₄ (Or.inr (⋄)) (⋄), p61₃
  have p62₄ : c₄.nreg 180062 = qb := Ρ bt_keep F₄ (Or.inr (⋄)) (⋄), p62₃
  obtain ⟨c₅, k₅, e₅, hk₅, F₅, b65, t65⟩ := testV_exec (P := P) hG hW (op := 0) (⋄)
    (r₁ := 180060) (r₂ := 180062) (r₃ := 180060) (d := 180065) (Or.inr (⋄))
    (Or.inr (⋄)) (Or.inr (⋄)) c₄ e₄.wb_right p60₄ p62₄ p60₄ lt60 hqbn lt60
  have p60₅ : c₅.nreg 180060 = a + T := Ρ bt_keep F₅ (Or.inr (⋄)) (⋄), p60₄
  have p61₅ : c₅.nreg 180061 = a + T - 1 := by
    Ξ bt_keep F₅ (Or.inr (⋄)) (⋄), p61₄
  have p62₅ : c₅.nreg 180062 = qb := Ρ bt_keep F₅ (Or.inr (⋄)) (⋄), p62₄
  obtain ⟨c₆, k₆, e₆, hk₆, F₆, b66, t66⟩ := testV_exec (P := P) hG hW (op := 0) (⋄)
    (r₁ := 180061) (r₂ := 180060) (r₃ := 180060) (d := 180066) (Or.inr (⋄))
    (Or.inr (⋄)) (Or.inr (⋄)) c₅ e₅.wb_right p61₅ p60₅ p60₅ lt61 lt60 lt60
  have p60₆ : c₆.nreg 180060 = a + T := Ρ bt_keep F₆ (Or.inr (⋄)) (⋄), p60₅
  have p62₆ : c₆.nreg 180062 = qb := Ρ bt_keep F₆ (Or.inr (⋄)) (⋄), p62₅
  obtain ⟨c₇, k₇, e₇, hk₇, F₇, b67, t67⟩ := testV_exec (P := P) hG hW (op := 1) (⋄)
    (r₁ := 180060) (r₂ := 180062) (r₃ := 180060) (d := 180067) (Or.inr (⋄))
    (Or.inr (⋄)) (Or.inr (⋄)) c₆ e₆.wb_right p60₆ p62₆ p60₆ lt60 hqbn lt60
  have p60₇ : c₇.nreg 180060 = a + T := Ρ bt_keep F₇ (Or.inr (⋄)) (⋄), p60₆
  have p62₇ : c₇.nreg 180062 = qb := Ρ bt_keep F₇ (Or.inr (⋄)) (⋄), p62₆
  obtain ⟨c₈, k₈, e₈, hk₈, F₈, b68, t68⟩ := testV_exec (P := P) hG hW (op := 1) (⋄)
    (r₁ := 180062) (r₂ := 180060) (r₃ := 180060) (d := 180068) (Or.inr (⋄))
    (Or.inr (⋄)) (Or.inr (⋄)) c₇ e₇.wb_right p62₇ p60₇ p60₇ hqbn lt60 lt60
  -- bits in `c₈`
  have B63 : c₈.nreg 180063 = c₃.nreg 180063 := by
    rw [bt_keep F₈ (Or.inr (⋄)) (⋄), bt_keep F₇ (Or.inr (⋄)) (⋄),
      bt_keep F₆ (Or.inr (⋄)) (⋄), bt_keep F₅ (Or.inr (⋄)) (⋄),
      bt_keep F₄ (Or.inr (⋄)) (⋄)]
  have B64 : c₈.nreg 180064 = c₄.nreg 180064 := by
    rw [bt_keep F₈ (Or.inr (⋄)) (⋄), bt_keep F₇ (Or.inr (⋄)) (⋄),
      bt_keep F₆ (Or.inr (⋄)) (⋄), bt_keep F₅ (Or.inr (⋄)) (⋄)]
  have B65 : c₈.nreg 180065 = c₅.nreg 180065 := by
    rw [bt_keep F₈ (Or.inr (⋄)) (⋄), bt_keep F₇ (Or.inr (⋄)) (⋄),
      bt_keep F₆ (Or.inr (⋄)) (⋄)]
  have B66 : c₈.nreg 180066 = c₆.nreg 180066 := by
    Ξ bt_keep F₈ (Or.inr (⋄)) (⋄), bt_keep F₇ (Or.inr (⋄)) (⋄)
  have B67 : c₈.nreg 180067 = c₇.nreg 180067 := bt_keep F₈ (Or.inr (⋄)) (⋄)
  have K11 : c₈.nreg 180011 = 1 := by
    rw [bt_keep F₈ (Or.inr (⋄)) (⋄), bt_keep F₇ (Or.inr (⋄)) (⋄),
      bt_keep F₆ (Or.inr (⋄)) (⋄), bt_keep F₅ (Or.inr (⋄)) (⋄),
      bt_keep F₄ (Or.inr (⋄)) (⋄), bt_keep F₃ (Or.inr (⋄)) (⋄),
      R₂.1 _ (⌖), k11]
  obtain ⟨c₉, k₉, e₉, hk₉, F₉, b14, t14⟩ := logicB_exec (P := P) hW8 c₈ e₈.wb_right K11
    (by rw [B63]; exact b63) (by rw [B64]; exact b64) (by rw [B65]; exact b65)
    (by rw [B66]; exact b66) (by rw [B67]; exact b67) b68
  Ξ' B63, B64, B65, B66, B67 at t14
  have ex : Exec P W bitGen c c₉ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + (k₈ + k₉)))))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉)))))))
  refine ⟨c₉, _, ex, ⋄, ?_, b14, ?_⟩
  · have G1 : FrameB Bbit c c₁ := frameB_mono R₁ fun r hr => by
      unfold Bbit at hr; ϴ' Bool.or_eq_false_iff, decide_eq_false_iff_not at hr ⊢; omega
    have G2 : FrameB Bbit c₁ c₂ := frameB_mono R₂ fun r hr => by
      unfold Bbit at hr; ϴ' Bool.or_eq_false_iff, decide_eq_false_iff_not at hr ⊢; omega
    have G9 : FrameB Bbit c₈ c₉ := frameB_mono F₉ fun r hr => by
      unfold Bbit at hr; unfold Blog
      ϴ' Bool.or_eq_false_iff, decide_eq_false_iff_not at hr ⊢; omega
    exact (((((((G1.trans G2).trans (frameB_mono F₃ (frame_test_bit (⋄)))).trans
      (frameB_mono F₄ (frame_test_bit (⋄)))).trans
      (frameB_mono F₅ (frame_test_bit (⋄)))).trans
      (frameB_mono F₆ (frame_test_bit (⋄)))).trans
      (frameB_mono F₇ (frame_test_bit (⋄)))).trans
      (frameB_mono F₈ (frame_test_bit (⋄)))).trans G9
  · ϴ' SignTest at t63 t64 t65 t66 t67 t68
    Ξ t14, sideBeta_tests hG hC hsn hT0
    have n63 := bit_of b63 t63
    have n64 := bit_of b64 t64
    Ξ n63, n64, t63, t64, t65, t66, t67, t68

end

end Brute

end Chazelle.Core
