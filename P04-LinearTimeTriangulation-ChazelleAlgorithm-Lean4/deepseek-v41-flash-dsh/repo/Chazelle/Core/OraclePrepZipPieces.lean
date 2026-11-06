module

public import Chazelle.Golf

public import Chazelle.Core.OraclePrepZipMath

/-!
# Lemma 3.6 (WP-H), preprocessing part 9: the pieces of the zipper on the RAM

* `arcPosS`: the walk position of an end of the arc at spine position `p` (`110203`), offset
  `o` (`110204`: `1` the start, `3` the end), into `110100`, `110101`;
* `eqS`: the flag of two equal keys (walk edges `110212`, `110210`, codes `110103`, `110211`);
* `adjS d`: the arc before (`d`) or after (`¬ d`) the located arc `120170` when the flag is set;
* `normS`: the normalised pair of `110299` and `110214` and its flag.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ

@[expose] public section

/-- **The walk position of an end of the arc at a spine position.** -/
def arcPosS : Stmt :=
  block [.addN 110200 120046 110203, .loadN 110201 110200, .addN 110202 110201 110201,
    .addN 110202 110202 110202, .addN 110202 110202 110201, .addN 110202 110202 120044,
    .addN 110202 110202 110204, .loadN 110100 110202, .addN 110202 110202 120011,
    .loadN 110101 110202]

theorem arcPosS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {AB SB A p o : ℕ}
    (hAB : c.nreg 120044 = AB) (hSB : c.nreg 120046 = SB) (h1 : c.nreg 120011 = 1)
    (hp : c.nreg 110203 = p) (hpA : p < A) (ho : c.nreg 110204 = o) (ho3 : o ≤ 3)
    (hj : c.nmem (SB + p) < A) (hSW : SB + A ≤ W) (hAW : AB + 5 * A ≤ W) :
    ∃ c' k, Exec P W arcPosS c c' k ∧ k = 10 ∧
      FrameB (fun r => decide (r = 110100 ∨ r = 110101 ∨ (110200 ≤ r ∧ r ≤ 110202))) c c' ∧
      c'.nreg 110100 = c.nmem (AB + 5 * c.nmem (SB + p) + o) ∧
      c'.nreg 110101 = c.nmem (AB + 5 * c.nmem (SB + p) + o + 1) := by
  obtain ⟨c', k, e, hk, v1, v2⟩ : ∃ c' k, Exec P W arcPosS c c' k ∧ k = 10 ∧
      c'.nreg 110100 = c.nmem (AB + 5 * c.nmem (SB + p) + o) ∧
      c'.nreg 110101 = c.nmem (AB + 5 * c.nmem (SB + p) + o + 1) := by
    unfold arcPosS
    exec_block
    · rw [hSB, hp]; omega
    · config_simp; rw [hSB, hp]; omega
    · config_simp; rw [hSB, hp]; omega
    · config_simp; rw [hSB, hp]; omega
    · config_simp; rw [hSB, hp, hAB]; omega
    · config_simp; rw [hSB, hp, hAB, ho]; omega
    · config_simp; rw [hSB, hp, hAB, ho, h1]; omega
    · refine ⟨rfl, ?_, ?_⟩
      · config_simp; rw [hSB, hp, hAB, ho]; congr 1; ring
      · config_simp; rw [hSB, hp, hAB, ho, h1]; congr 1; ring
  exact ⟨c', k, e, hk, exec_frameB e (⌖), v1, v2⟩

/-- The flag of equal keys into `110213`. -/
def eqS : Stmt :=
  ifEq 110212 110210 (ifEq 110103 110211 (.instr (.constN 110213 1)) (.instr (.constN 110213 0)))
    (.instr (.constN 110213 0))

theorem eqS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W eqS c c' k ∧ k ≤ 9 ∧ FrameB (fun r => decide (r = 110213)) c c' ∧
      c'.nreg 110213 = (if c.nreg 110212 = c.nreg 110210 ∧ c.nreg 110103 = c.nreg 110211
        then 1 else 0) := by
  have hwr : wr (fun r => decide (r = 110213)) eqS = true := ⌖
  suffices H : ∃ c' k, Exec P W eqS c c' k ∧ k ≤ 9 ∧
      c'.nreg 110213 = (if c.nreg 110212 = c.nreg 110210 ∧ c.nreg 110103 = c.nreg 110211
        then 1 else 0) by
    obtain ⟨c', k, e, hk, v⟩ := H
    exact ⟨c', k, e, hk, exec_frameB e hwr, v⟩
  unfold eqS
  by_cases h1 : c.nreg 110212 = c.nreg 110210
  · by_cases h2 : c.nreg 110103 = c.nreg 110211
    · exact ⟨_, _, ifEq_eq_exec h1 (ifEq_eq_exec h2 (Exec.constN hw 110213 1 hW)), ⋄,
        by rw [ite_eq_left ⟨h1, h2⟩]; config_simp⟩
    · obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (P := P) (W := W) (S := .instr (.constN 110213 1)) h2
        (Exec.constN hw 110213 0 (Nat.zero_le _))
      exact ⟨_, _, ifEq_eq_exec h1 e', ⋄, by rw [ite_eq_right (fun h => h2 h.2)]; config_simp⟩
  · obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (P := P) (W := W)
      (S := ifEq 110103 110211 (.instr (.constN 110213 1)) (.instr (.constN 110213 0))) h1
      (Exec.constN hw 110213 0 (Nat.zero_le _))
    exact ⟨_, _, e', ⋄, by rw [ite_eq_right (fun h => h1 h.1)]; config_simp⟩

/-- The arc before (`true`) or after (`false`) the located arc, when the flag is set, into
`110214`. -/
def adjS : Bool → Stmt
  | true => ifEq 110213 120011
      (.ifLtN 120012 120170 (.instr (.subN 110214 120170 120011))
        (.instr (.subN 110214 120030 120011)))
      (.instr (.copyN 110214 120170))
  | false => ifEq 110213 120011
      (.seq (.instr (.addN 110214 120170 120011))
        (.ifLtN 110214 120030 .skip (.instr (.constN 110214 0))))
      (.instr (.copyN 110214 120170))

/-- The adjusted arc. -/
def adjN (d : Bool) (A q e : ℕ) : ℕ :=
  if e = 1 then (if d then predP A q else succP A q) else q

theorem adjS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (d : Bool) {A : ℕ}
    (h1 : c.nreg 120011 = 1) (h0 : c.nreg 120012 = 0) (hA : c.nreg 120030 = A)
    (hq : c.nreg 120170 < A) (hW : A + 1 ≤ W) :
    ∃ c' k, Exec P W (adjS d) c c' k ∧ k ≤ 12 ∧ FrameB (fun r => decide (r = 110214)) c c' ∧
      c'.nreg 110214 = adjN d A (c.nreg 120170) (c.nreg 110213) := by
  have hwr : wr (fun r => decide (r = 110214)) (adjS d) = true := by cases d <;> decide
  suffices H : ∃ c' k, Exec P W (adjS d) c c' k ∧ k ≤ 12 ∧
      c'.nreg 110214 = adjN d A (c.nreg 120170) (c.nreg 110213) by
    obtain ⟨c', k, e, hk, v⟩ := H
    exact ⟨c', k, e, hk, exec_frameB e hwr, v⟩
  obtain ⟨q, hqd⟩ : ∃ q, c.nreg 120170 = q := ⟨_, rfl⟩
  rw [hqd] at hq ⊢
  unfold adjN
  by_cases he : c.nreg 110213 = 1
  · have he' : c.nreg 110213 = c.nreg 120011 := Ρ he, h1
    Ξ ite_eq_left he
    cases d
    · ϴ Bool.false_eq_true, ite_false
      unfold adjS
      have e1 := Exec.addN (P := P) hw 110214 120170 120011 (by rw [hqd, h1]; omega)
      have w1 := e1.wb_right
      unfold succP
      by_cases hs : q + 1 < A
      · have ht : ({ c with nreg := upd c.nreg 110214 (c.nreg 120170 + c.nreg 120011) } :
            Config).nreg 110214 < ({ c with nreg := upd c.nreg 110214 (c.nreg 120170 +
            c.nreg 120011) } : Config).nreg 120030 := by config_simp; rw [hqd, h1, hA]; exact hs
        exact ⟨_, _, ifEq_eq_exec he' (.seq e1 (.ifLtN_true ht (.skip w1))), ⋄,
          by rw [ite_eq_left hs]; config_simp; rw [hqd, h1]⟩
      · have ht : ¬ ({ c with nreg := upd c.nreg 110214 (c.nreg 120170 + c.nreg 120011) } :
            Config).nreg 110214 < ({ c with nreg := upd c.nreg 110214 (c.nreg 120170 +
            c.nreg 120011) } : Config).nreg 120030 := by config_simp; rw [hqd, h1, hA]; exact hs
        exact ⟨_, _, ifEq_eq_exec he' (.seq e1 (.ifLtN_false ht
          (Exec.constN w1 110214 0 (Nat.zero_le _)))), ⋄,
          by rw [ite_eq_right hs]; config_simp⟩
    · ϴ ite_true
      unfold adjS predP
      by_cases hz : q = 0
      · have ht : ¬ c.nreg 120012 < c.nreg 120170 := by rw [h0, hqd, hz]; exact Nat.lt_irrefl 0
        exact ⟨_, _, ifEq_eq_exec he' (.ifLtN_false ht (Exec.subN hw 110214 120030 120011)),
          ⋄, by rw [ite_eq_left hz]; config_simp; rw [hA, h1]⟩
      · have ht : c.nreg 120012 < c.nreg 120170 := by rw [h0, hqd]; omega
        exact ⟨_, _, ifEq_eq_exec he' (.ifLtN_true ht (Exec.subN hw 110214 120170 120011)),
          ⋄, by rw [ite_eq_right hz]; config_simp; rw [hqd, h1]⟩
  · have he' : c.nreg 110213 ≠ c.nreg 120011 := by rw [h1]; exact he
    Ξ ite_eq_right he
    cases d <;>
    · unfold adjS
      obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (P := P) (W := W) he' (Exec.copyN hw 110214 120170)
      exact ⟨_, _, e', ⋄, by config_simp; exact hqd⟩

/-- The normalised pair of `110299` and `110214`: minimum `110291`, maximum `110292`, flag
`110290` (`1` iff the minimum plus two is at most the maximum). -/
def normS : Stmt :=
  .seq (.ifLtN 110299 110214 (block [.copyN 110291 110299, .copyN 110292 110214])
      (block [.copyN 110291 110214, .copyN 110292 110299]))
    (.seq (.instr (.addN 110215 110291 120011))
      (.ifLtN 110215 110292 (.instr (.constN 110290 1)) (.instr (.constN 110290 0))))

theorem normS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    (h1 : c.nreg 120011 = 1) (hW : c.nreg 110299 + 1 ≤ W) (hW' : c.nreg 110214 + 1 ≤ W) :
    ∃ c' k, Exec P W normS c c' k ∧ k ≤ 12 ∧
      FrameB (fun r => decide (110290 ≤ r ∧ r ≤ 110292) || decide (r = 110215)) c c' ∧
      (normP (c.nreg 110299) (c.nreg 110214) = none → c'.nreg 110290 = 0) ∧
      ∀ x, normP (c.nreg 110299) (c.nreg 110214) = some x →
        c'.nreg 110290 = 1 ∧ c'.nreg 110291 = x.1 ∧ c'.nreg 110292 = x.2 := by
  have hwr : wr (fun r => decide (110290 ≤ r ∧ r ≤ 110292) || decide (r = 110215)) normS = true := by
    decide
  obtain ⟨a, ha⟩ : ∃ a, c.nreg 110299 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, c.nreg 110214 = b := ⟨_, rfl⟩
  rw [ha, hb]; rw [ha] at hW; rw [hb] at hW'
  -- the ordered pair
  obtain ⟨c₁, k₁, e₁, hk₁, v1, v2, r₁⟩ : ∃ c₁ k₁, Exec P W (.ifLtN 110299 110214
      (block [.copyN 110291 110299, .copyN 110292 110214])
      (block [.copyN 110291 110214, .copyN 110292 110299])) c c₁ k₁ ∧ k₁ ≤ 4 ∧
      c₁.nreg 110291 = min a b ∧ c₁.nreg 110292 = max a b ∧
      (∀ r, r ≠ 110291 → r ≠ 110292 → c₁.nreg r = c.nreg r) := by
    by_cases h : a < b
    · have ht : c.nreg 110299 < c.nreg 110214 := by rw [ha, hb]; exact h
      refine spec_ifLtN_true ht ?_
      exec_block
      refine ⟨⋄, ?_, ?_, fun r h1 h2 => ?_⟩
      · config_simp; rw [ha, min_eq_left h.le]
      · config_simp; rw [hb, max_eq_right h.le]
      · config_simp; upd_solve
    · have ht : ¬ c.nreg 110299 < c.nreg 110214 := by rw [ha, hb]; exact h
      refine spec_ifLtN_false ht ?_
      exec_block
      refine ⟨⋄, ?_, ?_, fun r h1 h2 => ?_⟩
      · config_simp; rw [hb, min_eq_right (⋄)]
      · config_simp; rw [ha, max_eq_left (⋄)]
      · config_simp; upd_solve
  have w₁ := e₁.wb_right
  have g1 : c₁.nreg 120011 = 1 := by rw [r₁ _ (⌖) (by decide), h1]
  have e₂ := Exec.addN (P := P) w₁ 110215 110291 120011 (by
    rw [v1, g1]; have := min_le_left a b; omega)
  have w₂ := e₂.wb_right
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 110215 (c₁.nreg 110291 + c₁.nreg 120011) }
    with hc₂
  have x15 : c₂.nreg 110215 = min a b + 1 := by rw [hc₂]; config_simp; rw [v1, g1]
  have x92 : c₂.nreg 110292 = max a b := by rw [hc₂]; config_simp; exact v2
  have x91 : c₂.nreg 110291 = min a b := by rw [hc₂]; config_simp; exact v1
  by_cases hf : min a b + 2 ≤ max a b
  · have ht : c₂.nreg 110215 < c₂.nreg 110292 := by rw [x15, x92]; omega
    have ex := Exec.seq e₁ (Exec.seq e₂ (Exec.ifLtN_true (e := .instr (.constN 110290 0)) ht
      (Exec.constN w₂ 110290 1 (⋄))))
    refine ⟨_, _, ex, ⋄, exec_frameB ex hwr, fun hn => ?_, fun x hx => ?_⟩
    · unfold normP at hn; rw [ite_eq_left hf] at hn; cases hn
    · unfold normP at hx; rw [ite_eq_left hf] at hx; cases hx
      refine ⟨by config_simp, ?_, ?_⟩
      · config_simp; exact x91
      · config_simp; exact x92
  · have ht : ¬ c₂.nreg 110215 < c₂.nreg 110292 := by rw [x15, x92]; omega
    have ex := Exec.seq e₁ (Exec.seq e₂ (Exec.ifLtN_false (t := .instr (.constN 110290 1)) ht
      (Exec.constN w₂ 110290 0 (Nat.zero_le _))))
    refine ⟨_, _, ex, ⋄, exec_frameB ex hwr, fun _ => by config_simp, fun x hx => ?_⟩
    unfold normP at hx; rw [ite_eq_right hf] at hx; cases hx

end

end OracleR

end Chazelle.Core
