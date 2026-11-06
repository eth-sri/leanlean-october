module

public meta import Chazelle.Arithmetic

public import Chazelle.Final.Transfer
public import Chazelle.Final.RamPieceTri
public import Chazelle.Final.RamSplit

/-!
# The orientation sign on the RAM

`orientStmt` computes `orient Q` for the geometry polygon `Q` related to the input `P` by a shear
(`Chazelle.Core.ShearRel`) into the real register `100`, in time linear in `n`: it finds a
`(y, x)`-lexicographically smallest vertex `k` of `P` (which is one of `Q`, `YlexAgree`) and sets
`rreg 100 := 1` if the corner determinant `det v_{k-1} v_k v_{k+1}` is positive (the same for `P`
and `Q`, `det_shearPt`), `-1` otherwise (`orient_eq_of_ylexMin`).

Registers written: natural `230 … 236`, real `100` and `230 … 243`.
-/

namespace Chazelle.Final

open Machine Machine.Stmt Programs
open Chazelle.EarClip (detInto detInto_exec)
open Chazelle.Mountain (ylexLT ylexLE orient)
open Chazelle.Core (shear shear_vtx det_shearPt ShearRel YlexAgree)

@[expose] public section

/-- One step of the minimum scan: `if ylexLT (vtx i) (vtx best) then best := i; i := i + 1`. -/
def orMinBody : Stmt :=
  .seq (block [.readX 230 232, .readY 231 232, .readX 232 231, .readY 233 231])
    (.seq (ylexTest 230 231 232 233 (.instr (.copyN 231 232)) .skip) (.instr (.addN 232 232 233)))

/-- The minimum scan over `i = 1 … n - 1`. -/
def orMinLoop : Stmt := .whileLtN 232 230 orMinBody

/-- `prev := (best + n - 1) % n`, `next := (best + 1) % n`, the corner determinant into
`rreg 240`, and the sign into `rreg 100`. -/
def orSign : Stmt :=
  .seq (block [.constN 235 0])
    (.seq (.ifLtN 235 231 (.instr (.subN 234 231 233)) (.instr (.subN 234 230 233)))
      (.seq (block [.addN 236 231 233])
        (.seq (.ifLtN 236 230 .skip (.instr (.constN 236 0)))
          (.seq (block [.readX 234 234, .readY 235 234, .readX 236 231, .readY 237 231,
              .readX 238 236, .readY 239 236])
            (.seq (detInto 240 241 242 234 235 236 237 238 239)
              (.seq (block [.constR 100 (-1), .constR 243 0])
                (.ifLtR 243 240 (.instr (.constR 100 1)) .skip)))))))

/-- **The orientation program.** -/
def orientStmt : Stmt :=
  .seq (block [.inputSize 230, .constN 231 0, .constN 232 1, .constN 233 1])
    (.seq orMinLoop orSign)

section Orient

variable {P : Polygon} {W : ℕ}

/-- The invariant of the minimum scan. -/
def OrInv (P : Polygon) (W : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ 1 ≤ c.nreg 232 ∧ c.nreg 232 ≤ P.n ∧ c.nreg 231 < c.nreg 232 ∧
    c.nreg 230 = P.n ∧ c.nreg 233 = 1 ∧
    (∀ i < c.nreg 232, ¬ ylexLT (P.vtx i) (P.vtx (c.nreg 231))) ∧
    (∀ r, (r < 231 ∨ 232 < r) → c.nreg r = c₀.nreg r) ∧
    (∀ r, (r < 230 ∨ 233 < r) → c.rreg r = c₀.rreg r) ∧
    c.nmem = c₀.nmem ∧ c.rmem = c₀.rmem ∧ c.output = c₀.output

/-- One iteration of the minimum scan preserves `OrInv`. -/
theorem orMinBody_inv {c₀ c : Config} (hI : OrInv P W c₀ c) (ht : c.nreg 232 < c.nreg 230) :
    ∃ c' k, Exec P W orMinBody c c' k ∧ OrInv P W c₀ c' ∧ k ≤ 12 ∧
      P.n - c'.nreg 232 < P.n - c.nreg 232 := by
  classical
  obtain ⟨hw, h1, hle, hlt, h230, h233, hmin, hfn, hfr, hnm, hrm, hout⟩ := hI
  rw [h230] at ht
  unfold orMinBody
  refine spec_seq ?_
  exec_block
  refine spec_name fun c₁ hc₁ => ?_
  have hw₁ : WordsBounded W c₁ := by simp_all
  have e1 : c₁.nreg = c.nreg := by rw [hc₁]
  have ex : (c₁.rreg 230, c₁.rreg 231) = P.vtx (c.nreg 232) := by simp_all
  have ey : (c₁.rreg 232, c₁.rreg 233) = P.vtx (c.nreg 231) := by simp_all
  have hupd : ∃ c₂ k₂, Exec P W (ylexTest 230 231 232 233 (.instr (.copyN 231 232)) .skip) c₁ c₂ k₂ ∧
      k₂ ≤ 1 + 6 ∧ (c₂.nreg 231 = if ylexLT (P.vtx (c.nreg 232)) (P.vtx (c.nreg 231))
        then c.nreg 232 else c.nreg 231) ∧ (∀ r, r ≠ 231 → c₂.nreg r = c.nreg r) ∧
        c₂.rreg = c₁.rreg ∧ c₂.nmem = c₁.nmem ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    refine ylexTest_exec c₁ (fun h => ?_) (fun h => ?_)
    · rw [ex, ey] at h
      refine ⟨_, 1, Exec.copyN hw₁ 231 232, le_rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; grind
      · config_simp; rw [Machine.upd_other _ _ _ hr, e1]
    · rw [ex, ey] at h
      refine ⟨c₁, 0, Exec.skip hw₁, by omega, ?_, fun r _ => by rw [e1], rfl, rfl, rfl, rfl⟩
      grind
  refine spec_seq (spec_use hupd ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨h231, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩
  have e232 : c₂.nreg 232 = c.nreg 232 := hfn₂ 232 (by decide)
  have e233 : c₂.nreg 233 = 1 := by grind
  refine spec_instr (Exec.addN hw₂ 232 232 233 (by ram_grind))
    fun hw₃ => ?_
  refine ⟨⟨hw₃, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_⟩,
    by omega, ?_⟩
  · omega_nf
  · omega_nf
  · config_simp; grind
  · ram_simp
  · ram_simp
  · config_simp at hi
    rw [e232, e233] at hi
    config_simp
    grind [Chazelle.Mountain.ylexLT, Chazelle.WordsBounded]
  · ram_simp
  · config_simp
    rw [hfr₂, hc₁]; config_simp
    rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]
    grind
  · grind
  · grind
  · grind
  · omega_nf

/-- **Spec of the orientation program**: with `Q` simple and related to `P` by a shear, cost
`≤ 14 n + 45`, and `rreg 100 = orient Q`; only the natural registers `230 … 236` and the real
registers `100`, `230 … 243` change. -/
theorem orientStmt_exec {Q : Polygon} (hPQ : ShearRel P Q) (hQ : Q.Simple) (c : Config)
    (hc : WordsBounded W c) (hW : P.n ≤ W) :
    ∃ c' k, Exec P W orientStmt c c' k ∧ k ≤ 14 * P.n + 45 ∧ c'.rreg 100 = orient Q ∧
      (∀ r, (r < 230 ∨ 236 < r) → c'.nreg r = c.nreg r) ∧
      (∀ r, r ≠ 100 → (r < 230 ∨ 243 < r) → c'.rreg r = c.rreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨ε, -, hQe, hag⟩ := hPQ
  have hn3 : 3 ≤ Q.n := hQ.1
  have hQn : Q.n = P.n := by rw [hQe]; exact Chazelle.Core.shear_n ε P
  
  unfold orientStmt
  refine spec_seq ?_
  exec_block
  · exact hW
  · omega
  · omega
  · omega
  refine spec_name fun c₁ hc₁ => ?_
  have hI₀ : OrInv P W c₁ c₁ := by
    refine ⟨by simp_all, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl⟩
    · ram_simp
    · simp_all +zetaDelta <;> omega
    · simp_all
    · ram_simp
    · ram_simp
    · rw [hc₁] at hi ⊢; config_simp at hi; config_simp
      have : i = 0 := by omega
      subst this
      exact Chazelle.Mountain.ylexLT_irrefl _
  obtain ⟨c₂, k₂, ex₂, ⟨hw₂, -, hle₂, hlt₂, h230₂, h233₂, hmin₂, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩,
    hexit₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (OrInv P W c₁) (fun d => P.n - d.nreg 232) 12
      (fun _ h => h.1) (fun d hd ht => orMinBody_inv hd ht) hI₀
  unfold orMinLoop
  refine spec_seq ⟨c₂, k₂, ex₂, ?_⟩
  rw [h230₂] at hexit₂
  
  set k := c₂.nreg 231 with hk
  have hkn : k < P.n := by omega
  have hminP : ∀ i < P.n, ¬ ylexLT (P.vtx i) (P.vtx k) := fun i hi => hmin₂ i (by omega)
  -- the sign
  unfold orSign
  refine spec_seq ?_
  exec_block
  · omega
  refine spec_name fun c₃ hc₃ => ?_
  have hw₃ : WordsBounded W c₃ := by grind
  have r3 : ∀ r, r ≠ 235 → c₃.nreg r = c₂.nreg r := by
    intro r hr; rw [hc₃]; config_simp; exact Machine.upd_other _ _ _ hr
  have hprev : ∃ c₄ k₄, Exec P W (.ifLtN 235 231 (.instr (.subN 234 231 233))
      (.instr (.subN 234 230 233))) c₃ c₄ k₄ ∧ k₄ ≤ 3 ∧
      c₄.nreg 234 = (k + P.n - 1) % P.n ∧ (∀ r, r ≠ 234 → c₄.nreg r = c₃.nreg r) ∧
      c₄.rreg = c₃.rreg ∧ c₄.nmem = c₃.nmem ∧ c₄.rmem = c₃.rmem ∧ c₄.output = c₃.output := by
    have e235 : c₃.nreg 235 = 0 := by ram_simp
    by_cases hk0 : 0 < k
    · refine spec_ifLtN_true (by grind)
        (spec_instr (Exec.subN hw₃ 234 231 233) fun _ => ?_)
      refine ⟨by omega, ?_, fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩
      config_simp
      rw [r3 231 (by decide), r3 233 (by decide), h233₂, ← hk,
        show k + P.n - 1 = (k - 1) + P.n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · refine spec_ifLtN_false (by grind)
        (spec_instr (Exec.subN hw₃ 234 230 233) fun _ => ?_)
      refine ⟨by omega, ?_, fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩
      config_simp
      rw [r3 230 (by decide), r3 233 (by decide), h233₂, h230₂,
        show k = 0 by omega, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  refine spec_seq (spec_use hprev ?_)
  rintro c₄ k₄ hk₄ hw₄ ⟨h234, hfn₄, hfr₄, hnm₄, hrm₄, hout₄⟩
  have r4 : ∀ r, r ≠ 234 → r ≠ 235 → c₄.nreg r = c₂.nreg r := fun r a b => by
    rw [hfn₄ r a, r3 r b]
  refine spec_seq ?_
  exec_block
  · rw [r4 231 (by decide) (by decide), r4 233 (by decide) (by decide), h233₂]; omega
  refine spec_name fun c₅ hc₅ => ?_
  have hw₅ : WordsBounded W c₅ := by grind
  have hnext : ∃ c₆ k₆, Exec P W (.ifLtN 236 230 .skip (.instr (.constN 236 0))) c₅ c₆ k₆ ∧
      k₆ ≤ 3 ∧ c₆.nreg 236 = (k + 1) % P.n ∧ (∀ r, r ≠ 236 → c₆.nreg r = c₅.nreg r) ∧
      c₆.rreg = c₅.rreg ∧ c₆.nmem = c₅.nmem ∧ c₆.rmem = c₅.rmem ∧ c₆.output = c₅.output := by
    have e236 : c₅.nreg 236 = k + 1 := by
      rw [hc₅]; config_simp; rw [r4 231 (by decide) (by decide), r4 233 (by decide) (by decide),
        h233₂]
    have e230 : c₅.nreg 230 = P.n := by
      rw [hc₅]; ram_simp 
    by_cases hk1 : k + 1 < P.n
    · refine spec_ifLtN_true (by omega) (spec_skip hw₅ ?_)
      exact ⟨by omega, by rw [e236, Nat.mod_eq_of_lt hk1], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    · refine spec_ifLtN_false (by omega)
        (spec_instr (Exec.constN hw₅ 236 0 (Nat.zero_le _)) fun _ => ?_)
      refine ⟨by omega, ?_, fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩
      config_simp
      rw [show k + 1 = P.n by omega, Nat.mod_self]
  refine spec_seq (spec_use hnext ?_)
  rintro c₆ k₆ hk₆ hw₆ ⟨h236, hfn₆, hfr₆, hnm₆, hrm₆, hout₆⟩
  have e234₆ : c₆.nreg 234 = (k + P.n - 1) % P.n := by
    rw [hfn₆ 234 (by decide), hc₅]; config_simp; exact h234
  have e231₆ : c₆.nreg 231 = k := by
    rw [hfn₆ 231 (by decide), hc₅]; config_simp; rw [r4 231 (by decide) (by decide)]
  refine spec_seq ?_
  exec_block
  refine spec_name fun c₇ hc₇ => ?_
  have hw₇ : WordsBounded W c₇ := by grind
  refine spec_seq (spec_use (detInto_exec (P := P) 240 241 242 234 235 236 237 238 239
    (by decide) (by decide) (by decide)
    (fun r hr => by omega) c₇ hw₇) ?_)
  rintro c₈ k₈ hk₈ hw₈ ⟨hdet, hfr₈, hn₈, hnm₈, hrm₈, hout₈⟩
  have hdetv : c₈.rreg 240 = det (P.vtx ((k + P.n - 1) % P.n)) (P.vtx k)
      (P.vtx ((k + 1) % P.n)) := by
    rw [hdet, hc₇]; config_simp; grind
  refine spec_seq ?_
  exec_block
  refine spec_name fun c₉ hc₉ => ?_
  have hw₉ : WordsBounded W c₉ := by grind
  have e243 : c₉.rreg 243 = 0 := by rw [hc₉]; config_simp; simp
  have e240 : c₉.rreg 240 = c₈.rreg 240 := by rw [hc₉]; config_simp
  -- the orientation of `Q`
  have hkQ : k < Q.n := by omega
  have hminQ : ∀ i < Q.n, ylexLE (Q.vtx k) (Q.vtx i) := by
    intro i hi
    have h1 : ¬ ylexLT (Q.vtx i) (Q.vtx k) := fun h =>
      hminP i (by omega) ((hag i k (by omega) (by omega)).2 h)
    rcases Chazelle.Mountain.ylexLT_trichotomy (Q.vtx k) (Q.vtx i) with h | h | h
    · exact Chazelle.Mountain.ylexLE_of_ylexLT h
    · rw [h]; exact Chazelle.Mountain.ylexLE_refl _
    grind
  have hdetQ : det (Q.vtx ((k + Q.n - 1) % Q.n)) (Q.vtx k) (Q.vtx ((k + 1) % Q.n)) =
      det (P.vtx ((k + P.n - 1) % P.n)) (P.vtx k) (P.vtx ((k + 1) % P.n)) := by
    rw [hQn, hQe, shear_vtx, shear_vtx, shear_vtx, det_shearPt]
  have hor := orient_eq_of_ylexMin hQ hkQ hminQ (σ := if 0 < det (P.vtx ((k + P.n - 1) % P.n))
    (P.vtx k) (P.vtx ((k + 1) % P.n)) then 1 else -1) (by rw [hdetQ])
  have hfr_all : ∀ r, r ≠ 100 → (r < 230 ∨ 243 < r) → c₉.rreg r = c.rreg r := by
    intro r h100 hr
    rw [hc₉]; config_simp
    rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ h100,
      hfr₈ r (by omega) (by omega) (by omega), hc₇]
    config_simp
    rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega), hfr₆, hc₅]
    config_simp
    rw [hfr₄, hc₃]
    config_simp
    rw [hfr₂ r (by omega), hc₁]
  have hfn_all : ∀ r, (r < 230 ∨ 236 < r) → c₉.nreg r = c.nreg r := by
    intro r hr
    rw [hc₉]; config_simp; rw [hn₈, hc₇]; config_simp
    rw [hfn₆ r (by omega), hc₅]; config_simp
    rw [Machine.upd_other _ _ _ (by omega), r4 r (by omega) (by omega), hfn₂ r (by omega), hc₁]
    config_simp
    rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]
  have hmem9 : c₉.nmem = c.nmem := by
    grind
  have hrm9 : c₉.rmem = c.rmem := by
    grind
  have hout9 : c₉.output = c.output := by
    grind
  have hk₂' : k₂ ≤ 14 * P.n := by
    have e : c₁.nreg 232 = 1 := by ram_simp
    omega
  by_cases hpos : 0 < det (P.vtx ((k + P.n - 1) % P.n)) (P.vtx k) (P.vtx ((k + 1) % P.n))
  · refine spec_ifLtR_true (by grind)
      (spec_instr (Exec.constR hw₉ 100 1) fun _ => ?_)
    refine ⟨by omega, ?_, fun r hr => ?_, fun r h1 hr => ?_, ?_, ?_, ?_⟩
    · config_simp; grind
    · config_simp; exact hfn_all r hr
    · config_simp; rw [Machine.upd_other _ _ _ h1]; exact hfr_all r h1 hr
    all_goals omega
  · refine spec_ifLtR_false (by grind) (spec_skip hw₉ ?_)
    refine ⟨by omega, ?_, hfn_all, hfr_all, hmem9, hrm9, hout9⟩
    rw [hor, ite_eq_right hpos, hc₉]; config_simp; simp

end Orient

end

end Chazelle.Final
