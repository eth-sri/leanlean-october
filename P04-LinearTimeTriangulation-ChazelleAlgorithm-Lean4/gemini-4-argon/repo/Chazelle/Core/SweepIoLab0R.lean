module

public import Chazelle.Core.SweepIoLab0M

/-!
# The sweep RAM (WP-D), answers: the label candidates of a side-0 query, the slots

The region list of the label shot ends with twelve **slots**: for the log entries `e` in
`eR0, eR1, eR2` and the label places `k = 0 … 3`, the label `l_k` of the log record `e` if
`e < E` and `k < n_e`, otherwise the first word of the list (a region of the gap part).

* `slotS e k`: one slot, stored at the allocator (`put1`);
* `slot_irs`: its run step, the value `slotVal`.
-/

namespace Chazelle.Core

namespace SweepIo

namespace Lab0

open Machine Machine.Stmt Programs SweepRam SweepPrim

@[expose] public section

/-! ## Registers -/

def eR0 : ℕ := sw 4030
def eR1 : ℕ := sw 4031
def eR2 : ℕ := sw 4032
def sV : ℕ := sw 4033
def sA : ℕ := sw 4034
def sX : ℕ := sw 4035
def sN : ℕ := sw 4036
def sE : ℕ := sw 4037

/-! ## A slot -/

/-- The address of the labels of the log record `e` (`sA`) and its label count (`sN`). -/
def addrL (e : ℕ) : List Instr :=
  [.copyN sE e, .addN sA sE sE, .addN sA sA sA, .addN sA sA sE, .addN sA sA sE, .addN sA sA sE,
    .addN sA sA (sw 300), .addN sX sA K2, .loadN sN sX, .addN sA sA K3]

/-- The label at place `k`. -/
def labL (k : ℕ) : List Instr := [.addN sA sA k, .loadN sV sA]

/-- Store `sV` at the allocator. -/
def put1 : Stmt := block [.storeN ALLOC sV, .addN ALLOC ALLOC K1]

/-- **One slot.** -/
def slotS (e k : ℕ) : Stmt :=
  .seq (block [.loadN sV gL])
    (.seq (.ifLtN e (sw 301) (.seq (block (addrL e)) (.ifLtN k sN (block (labL k)) .skip)) .skip)
      put1)

/-- The value of a slot. -/
def slotVal (m : ℕ → ℕ) (AL E g e k : ℕ) : ℕ :=
  if e < E ∧ k < m (AL + 7 * e + 2) then m (AL + 7 * e + 3 + k) else g

/-- The cost of a slot. -/
def slotK : ℕ := 19

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem put1_irs (hI : IInv W c₀ c) (hK : Consts c) (hroom : c.nreg ALLOC + 1 ≤ W) :
    IRS P W c₀ put1 c 2 (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 1 ∧
      (∀ r, r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (c.nreg ALLOC) (c.nreg sV)) := by
  have k1 : c.nreg 240611 = 1 := hK.2.1
  have hw := hI.hw
  have hroom' : c.nreg 9999 + 1 ≤ W := hroom
  have ex : ∃ c' k, Exec P W (block [.storeN 9999 244033, .addN 9999 9999 240611]) c c' k ∧
      k = 2 ∧ c'.nreg 9999 = c.nreg 9999 + 1 ∧
      (∀ r, r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (c.nreg 9999) (c.nreg 244033) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, ?_, fun r hr => ?_, ?_, rfl, rfl, rfl⟩
    · config_simp; omega
    · config_simp
      simp only [upd, ite_eq_right hr]
    · config_simp
  obtain ⟨c', k, ex, hk, h1, h2, h3, h4, h5, h6⟩ := ex
  refine IRS.ofExec hI ex (by omega) (fun r _ hr => h2 r hr) h4 (fun a ha => ?_) h5 h6
    (by show c.nreg 9999 ≤ c'.nreg 9999; omega) (by show c'.nreg 9999 ≤ c.nreg 9999 + k; omega)
    ⟨h1, h2, h3⟩
  rw [h3]
  have h0 : c₀.nreg 9999 ≤ c.nreg 9999 := hI.hA
  have ha' : a < c₀.nreg 9999 := ha
  simp only [upd]
  rw [ite_eq_right (by omega)]

/-- The registers of a slot. -/
def SlotW (r : ℕ) : Prop := r = sV ∨ r = sA ∨ r = sX ∨ r = sN ∨ r = sE

theorem addrL_val (m f : ℕ → ℕ) (e : ℕ) (hk2 : f K2 = 2) (hk3 : f K3 = 3) :
    regB m (addrL e) f sA = f (sw 300) + 7 * f e + 3 ∧
    regB m (addrL e) f sN = m (f (sw 300) + 7 * f e + 2) := by
  have hk2' : f 240615 = 2 := hk2
  have hk3' : f 240616 = 3 := hk3
  simp only [addrL, regB, regI, upd, sA, sX, sN, sE, K2, K3, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, hk2', hk3']
  exact ⟨by ring, congrArg m (by ring)⟩

theorem addrL_other (m f : ℕ → ℕ) (e : ℕ) {q : ℕ} (hq : ¬ SlotW q) : regB m (addrL e) f q = f q :=
  regB_other m (addrL e) f (fun i hi => by
    simp only [addrL, List.mem_cons, List.not_mem_nil, or_false] at hi
    unfold SlotW at hq
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;>
      intro h <;> subst h <;> simp at hq)

theorem addrL_ok (m f : ℕ → ℕ) (e : ℕ) (hk2 : f K2 = 2) (hk3 : f K3 = 3)
    (hb : f (sw 300) + 7 * f e + 3 ≤ W) : okB W m (addrL e) f := by
  have hk2' : f 240615 = 2 := hk2
  have hk3' : f 240616 = 3 := hk3
  have hb' : f 240300 + 7 * f e + 3 ≤ W := hb
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (240000 + j) := fun j h1 h2 =>
    iscr_sw (by omega) (by omega)
  simp only [addrL, okB, okI, regI, upd, sA, sX, sN, sE, K2, K3, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, hk2', hk3']
  exact ⟨s 4037 (by norm_num) (by norm_num), ⟨s 4034 (by norm_num) (by norm_num), by omega⟩,
    ⟨s 4034 (by norm_num) (by norm_num), by omega⟩, ⟨s 4034 (by norm_num) (by norm_num), by omega⟩,
    ⟨s 4034 (by norm_num) (by norm_num), by omega⟩, ⟨s 4034 (by norm_num) (by norm_num), by omega⟩,
    ⟨s 4034 (by norm_num) (by norm_num), by omega⟩, ⟨s 4035 (by norm_num) (by norm_num), by omega⟩,
    s 4036 (by norm_num) (by norm_num), ⟨s 4034 (by norm_num) (by norm_num), by omega⟩, trivial⟩

theorem labL_val (m f : ℕ → ℕ) (k : ℕ) :
    regB m (labL k) f sV = m (f sA + f k) := by
  simp only [labL, regB, regI, upd, sA, sV, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]

theorem labL_other (m f : ℕ → ℕ) (k : ℕ) {q : ℕ} (hq : ¬ SlotW q) : regB m (labL k) f q = f q :=
  regB_other m (labL k) f (fun i hi => by
    simp only [labL, List.mem_cons, List.not_mem_nil, or_false] at hi
    unfold SlotW at hq
    rcases hi with rfl | rfl <;> simp only [dstI] <;> intro h <;> subst h <;> simp at hq)

theorem labL_ok (m f : ℕ → ℕ) (k : ℕ) (hb : f sA + f k ≤ W) : okB W m (labL k) f := by
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (240000 + j) := fun j h1 h2 =>
    iscr_sw (by omega) (by omega)
  simp only [labL, okB, okI, sA, sV, sw] at hb ⊢
  exact ⟨⟨s 4034 (by norm_num) (by norm_num), hb⟩, s 4033 (by norm_num) (by norm_num), trivial⟩

set_option maxHeartbeats 1000000 in
/-- **One slot**: its value is stored at the allocator. -/
theorem slot_irs (hI : IInv W c₀ c) (hK : Consts c₀) {e k : ℕ} (he : ¬ SlotW e) (hk : ¬ SlotW k)
    (hk3 : c.nreg k ≤ 3) (hAL : c.nreg (sw 300) + 7 * c.nreg (sw 301) ≤ W)
    (hroom : c.nreg ALLOC + slotK ≤ W) :
    IRS P W c₀ (slotS e k) c slotK (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 1 ∧
      (∀ r, ¬ SlotW r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (c.nreg ALLOC) (slotVal c.nmem (c.nreg (sw 300)) (c.nreg (sw 301))
        (c.nmem (c.nreg gL)) (c.nreg e) (c.nreg k))) := by
  have nW : ∀ q, (q = ALLOC ∨ q = gL ∨ q = sw 300 ∨ q = sw 301 ∨ q = K1 ∨ q = K2 ∨ q = K3) →
      ¬ SlotW q := by
    intro q hq h
    unfold SlotW at h
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases h with h | h | h | h | h <;> simp [ALLOC, gL, K1, K2, K3, sV, sA, sX, sN, sE, sw] at h
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (240000 + j) := fun j h1 h2 =>
    iscr_sw (by omega) (by omega)
  set v := slotVal c.nmem (c.nreg (sw 300)) (c.nreg (sw 301)) (c.nmem (c.nreg gL)) (c.nreg e)
    (c.nreg k) with hv
  unfold slotS slotK
  unfold slotK at hroom
  refine IRS.seq (K₁ := 1) (K₂ := 16 + 2)
    (IRS.block [.loadN sV gL] hI ⟨s 4033 (by norm_num) (by norm_num), trivial⟩) ?_
  rintro c₁ hI₁ hA₁ hA₁' rfl
  set c₁ : Config := { c with nreg := regB c.nmem [.loadN sV gL] c.nreg } with hc₁
  have v1 : c₁.nreg sV = c.nmem (c.nreg gL) := by
    simp only [hc₁, regB, regI, upd, sV, sw]; simp
  have o1 : ∀ q, ¬ SlotW q → c₁.nreg q = c.nreg q := fun q hq =>
    regB_other _ _ _ (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi; simp only [dstI]; intro h; subst h; exact hq (Or.inl rfl))
  have hK₁ := hK.fix hI₁
  refine IRS.seq (K₁ := 16) (K₂ := 2) (Q₁ := fun c₂ => c₂.nreg sV = v ∧
      (∀ q, ¬ SlotW q → c₂.nreg q = c.nreg q) ∧ c₂.nmem = c.nmem) ?_ ?_
  · refine IRS.ite (K := 14) (fun hlt => ?_) (fun hlt => ?_)
    · rw [o1 e he, o1 _ (nW _ (by simp))] at hlt
      have hb : c₁.nreg (sw 300) + 7 * c₁.nreg e + 3 ≤ W := by
        rw [o1 e he, o1 _ (nW _ (by simp))]; omega
      refine IRS.seq (K₁ := 10) (K₂ := 4)
        (IRS.block (addrL e) hI₁ (addrL_ok _ _ e hK₁.2.2.2.2.2.1
          hK₁.2.2.2.2.2.2 hb)) ?_
      rintro c₃ hI₃ hA₃ hA₃' rfl
      set c₃ : Config := { c₁ with nreg := regB c₁.nmem (addrL e) c₁.nreg }
      obtain ⟨a1, a2⟩ := addrL_val c₁.nmem c₁.nreg e hK₁.2.2.2.2.2.1
        hK₁.2.2.2.2.2.2
      have o3 : ∀ q, ¬ SlotW q → c₃.nreg q = c.nreg q := fun q hq => by
        show regB c₁.nmem (addrL e) c₁.nreg q = c.nreg q
        rw [addrL_other _ _ e hq, o1 q hq]
      have m3 : c₃.nmem = c.nmem := rfl
      have eA : c₃.nreg sA = c.nreg (sw 300) + 7 * c.nreg e + 3 := by
        show regB c₁.nmem (addrL e) c₁.nreg sA = _
        rw [a1, o1 e he, o1 _ (nW _ (by simp))]
      have eN : c₃.nreg sN = c.nmem (c.nreg (sw 300) + 7 * c.nreg e + 2) := by
        show regB c₁.nmem (addrL e) c₁.nreg sN = _
        rw [a2, o1 e he, o1 _ (nW _ (by simp))]
      refine IRS.ite (K := 2) (fun hlt' => ?_) (fun hlt' => ?_)
      · rw [o3 k hk, eN] at hlt'
        refine (IRS.block (labL k) hI₃ (labL_ok _ _ k (by rw [eA, o3 k hk]; omega))).mono
          (by simp [labL]) ?_
        rintro _ rfl
        refine ⟨?_, fun q hq => ?_, rfl⟩
        · show regB c₃.nmem (labL k) c₃.nreg sV = v
          rw [labL_val, eA, o3 k hk, hv]
          unfold slotVal
          rw [ite_eq_left ⟨hlt, hlt'⟩]
        · show regB c₃.nmem (labL k) c₃.nreg q = c.nreg q
          rw [labL_other _ _ k hq, o3 q hq]
      · rw [o3 k hk, eN] at hlt'
        refine IRS.skip hI₃ ⟨?_, o3, m3⟩
        show regB c₁.nmem (addrL e) c₁.nreg sV = v
        rw [regB_other _ _ _ (fun i hi => by
          simp only [addrL, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [dstI, sV, sA, sX, sN, sE, sw]), v1, hv]
        unfold slotVal
        rw [ite_eq_right (fun h => hlt' h.2)]
    · rw [o1 e he, o1 _ (nW _ (by simp))] at hlt
      refine IRS.skip hI₁ ⟨?_, o1, rfl⟩
      rw [v1, hv]
      unfold slotVal
      rw [ite_eq_right (fun h => hlt h.1)]
  · rintro c₂ hI₂ hA₂ hA₂' ⟨v2, o2, m2⟩
    have hK₂ := hK.fix hI₂
    have eA2 : c₂.nreg ALLOC = c.nreg ALLOC := o2 _ (nW _ (by simp))
    refine (put1_irs hI₂ hK₂ (by rw [eA2]; omega)).mono le_rfl ?_
    rintro c' ⟨p1, p2, p3⟩
    refine ⟨by rw [p1, eA2], fun r hr hrA => by rw [p2 r hrA, o2 r hr], ?_⟩
    rw [p3, m2, eA2, v2]

/-! ## The twelve slots -/

/-- A list of slots. -/
def slotsOf : List (ℕ × ℕ) → Stmt
  | [] => .skip
  | p :: l => .seq (slotS p.1 p.2) (slotsOf l)

/-- The slots of the label shot: the entries `eR0, eR1, eR2`, the places `0 … 3`. -/
def slotPairs : List (ℕ × ℕ) :=
  [(eR0, K0), (eR0, K1), (eR0, K2), (eR0, K3), (eR1, K0), (eR1, K1), (eR1, K2), (eR1, K3),
    (eR2, K0), (eR2, K1), (eR2, K2), (eR2, K3)]

theorem slotVal_congr {m m' : ℕ → ℕ} {AL E g e k : ℕ} (hk : k ≤ 3)
    (h : ∀ a, a < AL + 7 * E → m' a = m a) :
    slotVal m' AL E g e k = slotVal m AL E g e k := by
  unfold slotVal
  by_cases he : e < E
  · rw [h _ (by omega), h _ (by omega)]
  · simp [he]

set_option maxHeartbeats 1000000 in
/-- **A list of slots**: the values in order at the allocator. -/
theorem slots_irs : ∀ (l : List (ℕ × ℕ)) {c : Config}, IInv W c₀ c → Consts c₀ →
    (∀ p ∈ l, ¬ SlotW p.1 ∧ ¬ SlotW p.2 ∧ p.1 ≠ ALLOC ∧ p.2 ≠ ALLOC ∧ c.nreg p.2 ≤ 3) →
    c.nreg (sw 300) + 7 * c.nreg (sw 301) ≤ c.nreg ALLOC → c.nreg gL < c.nreg ALLOC →
    c.nreg ALLOC + slotK * l.length ≤ W →
    IRS P W c₀ (slotsOf l) c (slotK * l.length) (fun c' =>
      c'.nreg ALLOC = c.nreg ALLOC + l.length ∧
      (∀ r, ¬ SlotW r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      ∀ i, i < l.length → c'.nmem (c.nreg ALLOC + i) =
        slotVal c.nmem (c.nreg (sw 300)) (c.nreg (sw 301)) (c.nmem (c.nreg gL))
          (c.nreg (l.getD i (0, 0)).1) (c.nreg (l.getD i (0, 0)).2))
  | [], c, hI, _, _, _, _, _ => IRS.skip hI ⟨by simp, fun _ _ _ => rfl, fun _ _ => rfl,
      fun i hi => by simp at hi⟩
  | p :: l, c, hI, hK, hl, hAL, hgL, hroom => by
    obtain ⟨he, hk, -, -, hk3⟩ := hl p List.mem_cons_self
    have hAW : c.nreg ALLOC ≤ W := hI.hw.1 _
    simp only [List.length_cons] at hroom ⊢
    refine (IRS.seq (K₁ := slotK) (K₂ := slotK * l.length)
      (slot_irs hI hK he hk hk3 (by omega) (by nlinarith)) ?_).mono (by ring_nf; omega)
      (fun _ h => h)
    rintro c₁ hI₁ hA₁ hA₁' ⟨e1, o1, m1⟩
    have nW : ∀ q, (q = ALLOC ∨ q = gL ∨ q = sw 300 ∨ q = sw 301) → ¬ SlotW q := by
      intro q hq h
      unfold SlotW at h
      rcases hq with rfl | rfl | rfl | rfl <;>
        rcases h with h | h | h | h | h <;> simp [ALLOC, gL, sV, sA, sX, sN, sE, sw] at h
    have r300 : c₁.nreg (sw 300) = c.nreg (sw 300) :=
      o1 _ (nW _ (by simp)) (by unfold ALLOC sw; omega)
    have r301 : c₁.nreg (sw 301) = c.nreg (sw 301) :=
      o1 _ (nW _ (by simp)) (by unfold ALLOC sw; omega)
    have rgL : c₁.nreg gL = c.nreg gL := o1 _ (nW _ (by simp)) (by unfold ALLOC gL sw; omega)
    have hmlow : ∀ a, a < c.nreg ALLOC → c₁.nmem a = c.nmem a := fun a ha => by
      rw [m1]; simp only [upd]; rw [ite_eq_right (by omega)]
    have hl' : ∀ q ∈ l, ¬ SlotW q.1 ∧ ¬ SlotW q.2 ∧ q.1 ≠ ALLOC ∧ q.2 ≠ ALLOC ∧
        c₁.nreg q.2 ≤ 3 := fun q hq => by
      obtain ⟨a, b, d, f, g⟩ := hl q (List.mem_cons_of_mem _ hq)
      exact ⟨a, b, d, f, by rwa [o1 _ b f]⟩
    refine (slots_irs l hI₁ hK hl' (by rw [r300, r301, e1]; omega) (by rw [rgL, e1]; omega)
      (by rw [e1]; nlinarith)).mono le_rfl ?_
    rintro c' ⟨f1, f2, f3, f4⟩
    refine ⟨by rw [f1, e1]; ring, fun r hr hrA => by rw [f2 r hr hrA, o1 r hr hrA],
      fun a ha => by rw [f3 a (by omega), hmlow a ha], fun i hi => ?_⟩
    rcases i with _ | i
    · rw [f3 _ (by omega), m1]
      simp only [upd, add_zero, ite_true, List.getD_cons_zero]
    · have hi' : i < l.length := by simp at hi; omega
      rw [show c.nreg ALLOC + (i + 1) = c₁.nreg ALLOC + i by rw [e1]; ring, f4 i hi',
        r300, r301, rgL, hmlow _ hgL]
      simp only [List.getD_cons_succ]
      have hmem : l.getD i (0, 0) ∈ l := by
        rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem _
      obtain ⟨a, b, d, f, g⟩ := hl _ (List.mem_cons_of_mem _ hmem)
      rw [o1 _ a d, o1 _ b f]
      exact slotVal_congr g (fun a ha => hmlow a (by omega))

end

end Lab0

end SweepIo

end Chazelle.Core
