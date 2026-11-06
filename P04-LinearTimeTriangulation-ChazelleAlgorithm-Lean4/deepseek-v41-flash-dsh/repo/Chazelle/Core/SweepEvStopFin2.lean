module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvStopTasks3

/-!
# The sweep (WP-D), stage 2, the finish of a stop origin: storing a list of registers (RAM)

`slfStSeq x vs`: store the registers `vs` at consecutive addresses from the address register `x`
(which is advanced); `slfStSeq_irs`.
-/

namespace Chazelle.Core

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim SweepRam

@[expose] public section

/-- Store the registers `vs` at `x, x + 1, …`. -/
def slfStSeq (x : ℕ) : List ℕ → Stmt
  | [] => .skip
  | v :: vs => .seq (.instr (.storeN x v)) (.seq (block [.addN x x K1]) (slfStSeq x vs))

variable {P : Polygon} {W : ℕ} {c₀ : Config}

set_option maxHeartbeats 4000000 in
/-- **Storing a list of registers.** -/
theorem slfStSeq_irs {x : ℕ} (hx : IScr x) (hK1x : K1 ≠ x) : ∀ (vs : List ℕ) {c : Config},
    IInv W c₀ c → c.nreg K1 = 1 → (∀ v ∈ vs, v ≠ x) → c₀.nreg ALLOC ≤ c.nreg x →
    c.nreg x + vs.length ≤ W →
    IRS P W c₀ (slfStSeq x vs) c (2 * vs.length) (fun c' =>
      (∀ i, i < vs.length → c'.nmem (c.nreg x + i) = c.nreg (vs.getD i 0)) ∧
      (∀ a, (a < c.nreg x ∨ c.nreg x + vs.length ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ x → c'.nreg r = c.nreg r) ∧ c'.nreg x = c.nreg x + vs.length)
  | [], c, hI, _, _, _, _ => IRS.skip hI ⟨fun i hi => absurd hi (by simp), fun _ _ => rfl,
      fun _ _ => rfl, by simp⟩
  | v :: vs, c, hI, hk1, hvx, hA, hW => by
    have hvx' : v ≠ x := hvx v List.mem_cons_self
    have hvs : ∀ w ∈ vs, w ≠ x := fun w hw => hvx w (List.mem_cons_of_mem _ hw)
    simp only [List.length_cons] at hW ⊢
    refine IRS.mono (K := 1 + (1 + 2 * vs.length)) (IRS.seq (IRS.store hI hA) ?_) (by omega)
      (fun _ h => h)
    rintro c₁ hI₁ - - rfl
    refine IRS.seq (K₁ := 1) (K₂ := 2 * vs.length) (IRS.block [.addN x x K1] hI₁
      ⟨⟨hx, by simp only; rw [hk1]; omega⟩, trivial⟩) ?_
    rintro c₂ hI₂ - - hc2
    have r2x : c₂.nreg x = c.nreg x + 1 := by
      rw [hc2]; simp only [regB, regI, upd_same]; rw [hk1]
    have r2o : ∀ r, r ≠ x → c₂.nreg r = c.nreg r := fun r hr => by
      rw [hc2]; simp only [regB, regI]; rw [upd_other _ _ _ hr]
    have m2 : c₂.nmem = upd c.nmem (c.nreg x) (c.nreg v) := by rw [hc2]
    refine (slfStSeq_irs hx hK1x vs hI₂ (by rw [r2o _ hK1x]; exact hk1) hvs
      (by rw [r2x]; omega) (by rw [r2x]; omega)).mono le_rfl ?_
    rintro c' ⟨h1, h2, h3, h4⟩
    refine ⟨fun i hi => ?_, fun a ha => ?_, fun r hr => by rw [h3 r hr, r2o r hr], by
      rw [h4, r2x]; ring⟩
    · rcases i with _ | j
      · rw [h2 _ (Or.inl (by rw [r2x]; omega)), m2]
        simp
      · have := h1 j (by omega)
        have hmem : vs.getD j 0 ∈ vs := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
          exact List.getElem_mem _
        rw [r2x, r2o _ (hvs _ hmem)] at this
        simp only [List.getD_cons_succ]
        rw [show c.nreg x + (j + 1) = c.nreg x + 1 + j by ring, this]
    · rw [h2 _ (by rw [r2x]; omega), m2, upd_other _ _ _ (by omega)]

/-! ## Emitting a raw record -/

/-- The finish registers: the offset bits `slfO … slfO + 7`, the anchor flag, the label count and
labels, the address register. -/
def slfO : ℕ := sw 4054
def slfA : ℕ := sw 4062
def slfN : ℕ := sw 4063
def slfL0 : ℕ := sw 4065
def slfL1 : ℕ := sw 4066
def slfX : ℕ := sw 4100

/-- The address of the next raw record. -/
def slfAddrL : List Instr :=
  [.copyN slfX gRB, .addN slfX slfX gRC, .addN slfX slfX gRC, .addN slfX slfX gRC,
    .addN slfX slfX gRC, .addN slfX slfX gRC, .addN slfX slfX gRC, .addN slfX slfX gRC,
    .addN slfX slfX gRC, .addN slfX slfX gRC, .addN slfX slfX gRC, .addN slfX slfX gRC]

/-- The words of a raw record: position, leaving code, code, auxiliary data. -/
def slfWords (pe ph dc : ℕ) : List ℕ := [pe, ph, dc, oKd, oKk, oB, slfA, slfN, slfL0, slfL1, oPar]

/-- **Emit a raw record** `(pe, ph, dc, …)` at `gRB + 11 gRC` and count it. -/
def slfEmit (pe ph dc : ℕ) : Stmt :=
  .seq (block slfAddrL) (.seq (slfStSeq slfX (slfWords pe ph dc)) (block [.addN gRC gRC K1]))

theorem slfAddrL_val (m f : ℕ → ℕ) :
    regB m slfAddrL f slfX = f gRB + 11 * f gRC ∧ ∀ q, q ≠ slfX → regB m slfAddrL f q = f q := by
  have hB : gRB ≠ slfX := by unfold gRB slfX sw; omega
  have hC : gRC ≠ slfX := by unfold gRC slfX sw; omega
  refine ⟨?_, fun q hq => regB_other _ _ _ (fun i hi => by
    simp only [slfAddrL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dstI] <;> exact fun h => hq h.symm)⟩
  ϴ slfAddrL, regB, regI, upd_same, upd_other _ _ _ hC
  ring

set_option maxHeartbeats 8000000 in
/-- **Emitting a raw record.** -/
theorem slfEmit_irs {pe ph dc : ℕ} (hpe : pe ≠ slfX) (hph : ph ≠ slfX) (hdc : dc ≠ slfX)
    {c : Config} (hI : IInv W c₀ c) (hk1 : c.nreg K1 = 1) (hA : c₀.nreg ALLOC ≤ c.nreg gRB)
    (hW : c.nreg gRB + 11 * (c.nreg gRC + 1) ≤ W) :
    IRS P W c₀ (slfEmit pe ph dc) c (12 + 2 * 11 + 1) (fun c' =>
      (∀ i, i < 11 → c'.nmem (c.nreg gRB + 11 * c.nreg gRC + i) =
        c.nreg ((slfWords pe ph dc).getD i 0)) ∧
      (∀ a, (a < c.nreg gRB + 11 * c.nreg gRC ∨ c.nreg gRB + 11 * c.nreg gRC + 11 ≤ a) →
        c'.nmem a = c.nmem a) ∧
      c'.nreg gRC = c.nreg gRC + 1 ∧ (∀ r, r ≠ slfX → r ≠ gRC → c'.nreg r = c.nreg r)) := by
  have hsX : IScr slfX := iscr_sw' (⊛) (by norm_num)
  have hsC : IScr gRC := iscr_sw' (⊛) (by norm_num)
  have hB : gRB ≠ slfX := by unfold gRB slfX sw; omega
  have hC : gRC ≠ slfX := by unfold gRC slfX sw; omega
  have hK1X : K1 ≠ slfX := by unfold K1 slfX sw; omega
  have hK1C : K1 ≠ gRC := by unfold K1 gRC sw; omega
  have hok : okB W c.nmem slfAddrL c.nreg := by
    ϴ slfAddrL, okB, okI, regI, upd_same, upd_other _ _ _ hC
    refine ⟨hsX, ⟨hsX, ⋄⟩, ⟨hsX, by omega⟩, ⟨hsX, by omega⟩, ⟨hsX, by omega⟩,
      ⟨hsX, ⋄⟩, ⟨hsX, by omega⟩, ⟨hsX, by omega⟩, ⟨hsX, by omega⟩, ⟨hsX, by omega⟩,
      ⟨hsX, ⋄⟩, ⟨hsX, by omega⟩, trivial⟩
  obtain ⟨va, vo⟩ := slfAddrL_val c.nmem c.nreg
  refine IRS.seq (K₁ := 12) (K₂ := 2 * 11 + 1) (IRS.block slfAddrL hI hok) ?_
  rintro c₁ hI₁ - - hc1
  have a1 : c₁.nreg slfX = c.nreg gRB + 11 * c.nreg gRC := by rw [hc1]; exact va
  have o1 : ∀ q, q ≠ slfX → c₁.nreg q = c.nreg q := fun q hq => by rw [hc1]; exact vo q hq
  have m1 : c₁.nmem = c.nmem := Ρ hc1
  have hws : ∀ v ∈ slfWords pe ph dc, v ≠ slfX := by
    intro v hv
    simp only [slfWords, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | (simp only [oKd, oKk, oB, slfA, slfN, slfL0, slfL1, oPar, slfX, sw]; omega)
  refine IRS.seq (K₁ := 2 * 11) (K₂ := 1) (slfStSeq_irs hsX hK1X (slfWords pe ph dc) hI₁
    (by rw [o1 _ hK1X]; exact hk1) hws (by rw [a1]; omega)
    (by rw [a1]; simp only [slfWords, List.length_cons, List.length_nil]; omega)) ?_
  rintro c₂ hI₂ - - ⟨s1, s2, s3, s4⟩
  have c2C : c₂.nreg gRC = c.nreg gRC := Ρ s3 _ hC, o1 _ hC
  have c2K : c₂.nreg K1 = 1 := by rw [s3 _ hK1X, o1 _ hK1X]; exact hk1
  refine (IRS.block [.addN gRC gRC K1] hI₂ ⟨⟨hsC, by rw [c2C, c2K]; omega⟩, trivial⟩).mono
    (✓) ?_
  rintro c₃ hc3
  have m3 : c₃.nmem = c₂.nmem := Ρ hc3
  simp only [slfWords, List.length_cons, List.length_nil] at s1 s2
  refine ⟨fun i hi => ?_, fun a ha => ?_, ?_, fun r hr1 hr2 => ?_⟩
  · Ξ m3, ← a1, s1 i hi, o1 _ ?_
    · rfl
    · have hm : (slfWords pe ph dc).getD i 0 ∈ slfWords pe ph dc := by
        Ξ List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [slfWords]; omega)
        exact List.getElem_mem _
      exact hws _ hm
  · Ξ m3, s2 a (by rw [a1]; omega), m1
  · rw [hc3]; simp only [regB, regI, upd_same]; rw [c2C, c2K]
  · rw [hc3]; simp only [regB, regI]; rw [upd_other _ _ _ hr2, s3 _ hr1, o1 _ hr1]

end

end SweepEv

end Chazelle.Core
