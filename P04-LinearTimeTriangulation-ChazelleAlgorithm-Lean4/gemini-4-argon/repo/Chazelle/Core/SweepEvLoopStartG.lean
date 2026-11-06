module

public import Chazelle.Core.SweepEvLoopStartL

/-!
# The sweep (WP-D), stage 3: the start of the event loop (task L0, RAM part 5: the log record)

`stores a rs`: store the registers `rs` at the address in `a`, `a + 1`, …; `stLog`: the first log
record `(kE, kH, kN, kL … kL + 3)` at `lB`, `lC := 1`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-- Store the registers `rs` at consecutive addresses from the value of `a`. -/
def stores (a : ℕ) : List ℕ → Stmt
  | [] => .skip
  | r :: rs => .seq (.instr (.storeN a r)) (.seq (.instr (.addN a a K1)) (stores a rs))

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

set_option maxHeartbeats 4000000 in
/-- **Consecutive stores.** -/
theorem stores_irs (hK : Consts c₀) {a : ℕ} (ha : IScr a) :
    ∀ (rs : List ℕ) (c : Config), IInv W c₀ c → c₀.nreg ALLOC ≤ c.nreg a → (∀ r ∈ rs, r ≠ a) →
      c.nreg a + rs.length ≤ W →
      IRS P W c₀ (stores a rs) c (2 * rs.length) (fun c' => c'.nreg a = c.nreg a + rs.length ∧
        (∀ q, q ≠ a → c'.nreg q = c.nreg q) ∧
        ∀ x, c'.nmem x = if c.nreg a ≤ x ∧ x < c.nreg a + rs.length then
          c.nreg (rs.getD (x - c.nreg a) 0) else c.nmem x)
  | [], c, hI, _, _, _ => IRS.skip hI ⟨by simp, fun _ _ => rfl, fun x => by
      rw [ite_eq_right (by simp)]⟩
  | r :: rs, c, hI, hA, hr, hW => by
    have hra : r ≠ a := hr r List.mem_cons_self
    refine IRS.seq (K₁ := 1) (K₂ := 1 + 2 * rs.length) (IRS.store (v := r) hI hA) ?_ |>.mono
      (by simp; omega) (fun _ h => h)
    rintro c₁ hI₁ - - rfl
    set c₁ : Config := { c with nmem := upd c.nmem (c.nreg a) (c.nreg r) } with hc₁
    have hk1 : c₁.nreg K1 = 1 := (hK.fix hI₁).2.1
    have hk1' : c.nreg K1 = 1 := hk1
    have ea : c₁.nreg a = c.nreg a := rfl
    refine IRS.seq (K₁ := 1) (K₂ := 2 * rs.length) (IRS.instr1 (i := .addN a a K1) hI₁
      ⟨ha, by show c₁.nreg a + c₁.nreg K1 ≤ W; rw [hk1, ea]; simp only [List.length_cons] at hW
              omega⟩) ?_
    rintro c₂ hI₂ - - rfl
    have v2 : ({ c₁ with nreg := regI c₁.nmem (.addN a a K1) c₁.nreg } : Config).nreg a =
        c.nreg a + 1 := by simp [regI, hk1', hc₁]
    have o2 : ∀ q, q ≠ a →
        ({ c₁ with nreg := regI c₁.nmem (.addN a a K1) c₁.nreg } : Config).nreg q = c.nreg q :=
      fun q hq => by simp [regI, upd_other _ _ _ hq, hc₁]
    refine (stores_irs hK ha rs _ hI₂ (by rw [v2]; omega)
      (fun r' hr' => hr r' (List.mem_cons_of_mem _ hr')) (by rw [v2]; simp at hW; omega)).mono
      le_rfl ?_
    rintro c' ⟨e1, e2, e3⟩
    rw [v2] at e1 e3
    refine ⟨by rw [e1]; simp; omega, fun q hq => by rw [e2 q hq, o2 q hq], fun x => ?_⟩
    rw [e3 x]
    simp only [List.length_cons]
    by_cases hx : c.nreg a + 1 ≤ x ∧ x < c.nreg a + 1 + rs.length
    · rw [ite_eq_left hx, ite_eq_left (by omega)]
      have hidx : x - c.nreg a = (x - (c.nreg a + 1)) + 1 := by omega
      rw [hidx, List.getD_cons_succ]
      have hmem : rs.getD (x - (c.nreg a + 1)) 0 ∈ rs := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
      exact o2 _ (hr _ (List.mem_cons_of_mem _ hmem))
    · rw [ite_eq_right hx]
      show upd c.nmem (c.nreg a) (c.nreg r) x = _
      by_cases hx0 : x = c.nreg a
      · subst hx0
        rw [upd_same, ite_eq_left (by omega), Nat.sub_self, List.getD_cons_zero]
      · rw [upd_other _ _ _ hx0, ite_eq_right (by omega)]

/-- The registers of the log record. -/
def lsLogRegs : List ℕ := [kE, kH, kN, kL, kL + 1, kL + 2, kL + 3]

/-- **The first log record.** -/
def stLog : Stmt := .seq (.instr (.copyN zX lB)) (.seq (stores zX lsLogRegs) (.instr (.constN lC 1)))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem stLog_irs (hK : Consts c₀) (hI : IInv W c₀ c) (hlB : c₀.nreg ALLOC ≤ c.nreg lB)
    (hroom : c.nreg lB + 7 ≤ W) :
    IRS P W c₀ stLog c 16 (fun c' => c'.nreg lC = 1 ∧
      (∀ q, q ≠ zX → q ≠ lC → c'.nreg q = c.nreg q) ∧
      (∀ x, x < c.nreg lB ∨ c.nreg lB + 7 ≤ x → c'.nmem x = c.nmem x) ∧
      c'.nmem (c.nreg lB) = c.nreg kE ∧ c'.nmem (c.nreg lB + 1) = c.nreg kH ∧
      c'.nmem (c.nreg lB + 2) = c.nreg kN ∧
      ∀ i, i < 4 → c'.nmem (c.nreg lB + 3 + i) = c.nreg (kL + i)) := by
  have hzX : IScr zX := iscr_sw (by simp [zX, sw]) (by simp [zX, sw])
  refine IRS.seq (K₁ := 1) (K₂ := 14 + 1) (IRS.instr1 (i := .copyN zX lB) hI hzX) ?_ |>.mono
    (by norm_num) (fun _ h => h)
  rintro c₁ hI₁ - - rfl
  have v1 : ({ c with nreg := regI c.nmem (.copyN zX lB) c.nreg } : Config).nreg zX = c.nreg lB := by
    simp [regI]
  have o1 : ∀ q, q ≠ zX → ({ c with nreg := regI c.nmem (.copyN zX lB) c.nreg } : Config).nreg q =
      c.nreg q := fun q hq => by simp [regI, upd_other _ _ _ hq]
  have hne : ∀ r ∈ lsLogRegs, r ≠ zX := by
    intro r hr; simp only [lsLogRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [kE, kH, kN, kL, zX, sw]
  refine IRS.seq (K₁ := 14) (K₂ := 1) (stores_irs hK hzX lsLogRegs _ hI₁ (by rwa [v1]) hne
    (by rw [v1]; simp [lsLogRegs]; omega)) ?_
  rintro c₂ hI₂ - - ⟨e1, e2, e3⟩
  rw [v1] at e3
  refine (IRS.instr1 (i := .constN lC 1) hI₂ ⟨iscr_sw (by simp [lC, sw]) (by simp [lC, sw]),
    by omega⟩).mono le_rfl ?_
  rintro c' rfl
  have hlen : lsLogRegs.length = 7 := rfl
  have val : ∀ k, k < 7 → c₂.nmem (c.nreg lB + k) = c.nreg (lsLogRegs.getD k 0) := by
    intro k hk
    rw [e3, ite_eq_left (by rw [hlen]; omega), Nat.add_sub_cancel_left, o1 _ ?_]
    rw [List.getD_eq_getElem _ _ (by rwa [hlen])]
    exact hne _ (List.getElem_mem _)
  refine ⟨by simp [regI], fun q h1 h2 => ?_, fun x hx => ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · simp only [regI]
    rw [upd_other _ _ _ h2, e2 q h1, o1 q h1]
  · show c₂.nmem x = _
    rw [e3, ite_eq_right (by rw [hlen]; omega)]
  · show c₂.nmem _ = _; have := val 0 (by norm_num); simpa [lsLogRegs] using this
  · show c₂.nmem _ = _; have := val 1 (by norm_num); simpa [lsLogRegs] using this
  · show c₂.nmem _ = _; have := val 2 (by norm_num); simpa [lsLogRegs] using this
  · show c₂.nmem _ = _
    have := val (3 + i) (by omega)
    rw [← Nat.add_assoc] at this
    rw [this]
    interval_cases i <;> simp [lsLogRegs]

end

end SweepEv

end Chazelle.Core
