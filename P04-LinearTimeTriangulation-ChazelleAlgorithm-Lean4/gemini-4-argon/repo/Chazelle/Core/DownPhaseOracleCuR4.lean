module

public import Chazelle.Core.DownPhaseOracleCuR3

/-!
# WP-M (E7-B, RAM part 18): the assembly of the answer of the interior cutter

`asmC`: the output list at the allocator `O`: for the slots `0 … 3` in order, if recorded, its
pieces copied and translated (`asmK k`, `cpLoop`) to `O + 1 …`; then the number of pieces at `O`,
the answer register `150010 := O`, and the allocator past the list (`finC`).

* `AsmSt`: the invariant of the assembly (the pieces of the slots copied so far);
* `asmC_exec`: the output list holds the translated pieces of the recorded slots, oldest first,
  the memory below `O` is unchanged, and the frame is that of the interior oracles.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim

@[expose] public section

/-! ## The programs -/

/-- The start of the assembly: the output list at the allocator. -/
def asmInit : Stmt := block [.copyN 170221 9999, .addN 170222 170221 170011, .constN 170223 0]

/-- The fields of slot `k` and the start of its copy. -/
def asmSet (k : ℕ) : Stmt :=
  block [.copyN 170230 (170201 + 5 * k), .copyN 170231 (170202 + 5 * k),
    .copyN 170232 (170203 + 5 * k), .copyN 170233 (170204 + 5 * k), .addN 170234 170230 170011,
    .constN 170235 0]

/-- Copy the pieces of slot `k` if it is recorded. -/
def asmK (k : ℕ) : Stmt := .ifLtN (170200 + 5 * k) 170011 .skip (.seq (asmSet k) cpLoop)

/-- The end: the number of pieces, the answer register, the allocator. -/
def finC : Stmt := block [.storeN 170221 170223, .copyN 150010 170221, .copyN 9999 170222]

/-- **The assembly of the answer.** -/
def asmC : Stmt :=
  .seq asmInit (.seq (asmK 0) (.seq (asmK 1) (.seq (asmK 2) (.seq (asmK 3) finC))))

/-- The registers the copies of the assembly write. -/
def Basm (r : ℕ) : Bool := decide (r = 170222 ∨ r = 170223 ∨ (170230 ≤ r ∧ r < 170238))

theorem wrM_asmSet (k : ℕ) : BuildRam.wrM Basm (asmSet k) = true := rfl

/-! ## The invariant -/

/-- **The assembly so far**: the pieces of the slots `sls` copied and translated from `O + 1`
on, counted in `170223`, the output pointer in `170222`, the memory up to `O` unchanged. -/
structure AsmSt (m₀ : ℕ → ℕ) (n O : ℕ) (sls : List Slot) (c : Config) : Prop where
  r21 : c.nreg 170221 = O
  r22 : c.nreg 170222 = O + 1 + 7 * (sls.flatMap (slotPcs m₀ n)).length
  r23 : c.nreg 170223 = (sls.flatMap (slotPcs m₀ n)).length
  lo : ∀ a, a < O + 1 → c.nmem a = m₀ a
  out : ∀ j (hj : j < (sls.flatMap (slotPcs m₀ n)).length) f, f < 7 →
    c.nmem (O + 1 + 7 * j + f) = pcW ((sls.flatMap (slotPcs m₀ n))[j]'hj) f

theorem slotPcs_length (m : ℕ → ℕ) (n : ℕ) (sl : Slot) : (slotPcs m n sl).length = sl.q := by
  simp [slotPcs]

/-- **One more slot copied.** -/
theorem AsmSt.step {m₀ : ℕ → ℕ} {n O : ℕ} {sls : List Slot} {sl : Slot} {c c' : Config}
    (h : AsmSt m₀ n O sls c) (r21 : c'.nreg 170221 = O)
    (r22 : c'.nreg 170222 = c.nreg 170222 + 7 * sl.q)
    (r23 : c'.nreg 170223 = c.nreg 170223 + sl.q)
    (hlo : ∀ a, a < c.nreg 170222 → c'.nmem a = c.nmem a)
    (hout : ∀ j, j < sl.q → ∀ f, f < 7 →
      c'.nmem (c.nreg 170222 + 7 * j + f) = pcW (trPcR n sl.u₀ sl.g₀ (rdPc m₀ sl.L j)) f) :
    AsmSt m₀ n O (sls ++ [sl]) c' := by
  have e : (sls ++ [sl]).flatMap (slotPcs m₀ n) = sls.flatMap (slotPcs m₀ n) ++ slotPcs m₀ n sl := by
    simp
  have hl : ((sls ++ [sl]).flatMap (slotPcs m₀ n)).length =
      (sls.flatMap (slotPcs m₀ n)).length + sl.q := by
    rw [e, List.length_append, slotPcs_length]
  have h22 := h.r22
  refine ⟨r21, by rw [hl, r22, h.r22]; ring, by rw [hl, r23, h.r23], fun a ha => ?_,
    fun j hj f hf => ?_⟩
  · rw [hlo a (by omega)]; exact h.lo a ha
  · have hj' := hj
    rw [hl] at hj'
    have hget : ((sls ++ [sl]).flatMap (slotPcs m₀ n))[j]'hj =
        (sls.flatMap (slotPcs m₀ n) ++ slotPcs m₀ n sl)[j]'(by rwa [← e]) := by
      simp only [e]
    rw [hget]
    by_cases hjl : j < (sls.flatMap (slotPcs m₀ n)).length
    · rw [List.getElem_append_left hjl, hlo _ (by omega)]
      exact h.out j hjl f hf
    · push Not at hjl
      rw [List.getElem_append_right hjl]
      have hi : j - (sls.flatMap (slotPcs m₀ n)).length < sl.q := by omega
      have := hout _ hi f hf
      rw [show c.nreg 170222 + 7 * (j - (sls.flatMap (slotPcs m₀ n)).length) + f =
        O + 1 + 7 * j + f by rw [h22]; omega] at this
      rw [this]
      simp [slotPcs]

/-- The slots recorded among the first `k` are among the first `K ≥ k`. -/
theorem slotsOf_prefix {c : Config} {k : ℕ} : ∀ {K : ℕ}, k ≤ K →
    ∃ l, slotsOf c K = slotsOf c k ++ l
  | 0, hk => ⟨[], by rw [show k = 0 by omega]; simp⟩
  | K + 1, hk => by
    rcases hk.lt_or_eq with hk | hk
    · obtain ⟨l, hl⟩ := slotsOf_prefix (c := c) (k := k) (K := K) (by omega)
      exact ⟨l ++ (if c.nreg (170200 + 5 * K) = 1 then [slotAt c K] else []),
        by simp only [slotsOf, hl, List.append_assoc]⟩
    · exact ⟨[], by rw [hk]; simp⟩

theorem flat_le {c : Config} {m : ℕ → ℕ} {n k K : ℕ} (hk : k ≤ K) :
    ((slotsOf c k).flatMap (slotPcs m n)).length ≤ ((slotsOf c K).flatMap (slotPcs m n)).length := by
  obtain ⟨l, hl⟩ := slotsOf_prefix (c := c) hk
  rw [hl, List.flatMap_append, List.length_append]
  omega

theorem mem_slotsOf_of {c : Config} {k : ℕ} (hf : c.nreg (170200 + 5 * k) = 1) :
    ∀ {K : ℕ}, k < K → slotAt c k ∈ slotsOf c K
  | 0, hk => absurd hk (by omega)
  | K + 1, hk => by
    simp only [slotsOf, List.mem_append]
    rcases (show k < K ∨ k = K by omega) with h | rfl
    · exact Or.inl (mem_slotsOf_of hf h)
    · right; simp [hf]

theorem SlotsOK.mem {P : Polygon} {m : ℕ → ℕ} {E Hγ e₁ : ℕ} :
    ∀ {V : ℝ} {sls : List Slot} {V' : ℝ}, SlotsOK P m E Hγ e₁ V sls V' →
      ∀ sl ∈ sls, ∃ Va Vb, SlotOK P m E Hγ e₁ Va Vb sl
  | _, [], _, _, _, h => by simp at h
  | V, s :: sls, _, ⟨V₁, h1, h2⟩, sl, hsl => by
    rcases List.mem_cons.1 hsl with rfl | hsl
    · exact ⟨V, V₁, h1⟩
    · exact SlotsOK.mem h2 sl hsl

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ}

/-- **The copy of slot `k`.** -/
theorem asmK_exec (k : ℕ) (hk : k < 4) (c : Config) (hw : WordsBounded W c) {c₀ : Config}
    {n O Hγ e₁ : ℕ} (hA : AsmSt c₀.nmem n O (slotsOf c₀ k) c)
    (hsl : ∀ r, 170200 ≤ r → r < 170220 → c.nreg r = c₀.nreg r)
    (h10 : c.nreg 170010 = n) (h11 : c.nreg 170011 = 1)
    (hbit : c₀.nreg (170200 + 5 * k) ≤ 1)
    (hok : c₀.nreg (170200 + 5 * k) = 1 → ∃ Va Vb, SlotOK P c₀.nmem O Hγ e₁ Va Vb (slotAt c₀ k))
    (hn : n = (Qof P).n) (hnW : 2 * n ≤ W)
    (hroom : O + 1 + 7 * ((slotsOf c₀ (k + 1)).flatMap (slotPcs c₀.nmem n)).length ≤ W) :
    ∃ c' k', Exec P W (asmK k) c c' k' ∧
      k' + 42 * ((slotsOf c₀ k).flatMap (slotPcs c₀.nmem n)).length ≤
        42 * ((slotsOf c₀ (k + 1)).flatMap (slotPcs c₀.nmem n)).length + 12 ∧
      7 * ((slotsOf c₀ (k + 1)).flatMap (slotPcs c₀.nmem n)).length ≤
        7 * ((slotsOf c₀ k).flatMap (slotPcs c₀.nmem n)).length + k' ∧
      AsmSt c₀.nmem n O (slotsOf c₀ (k + 1)) c' ∧ BuildRam.FrameM Basm c c' := by
  have hsucc : slotsOf c₀ (k + 1) = slotsOf c₀ k ++
      (if c₀.nreg (170200 + 5 * k) = 1 then [slotAt c₀ k] else []) := rfl
  have h0 : c.nreg (170200 + 5 * k) = c₀.nreg (170200 + 5 * k) := hsl _ (by omega) (by omega)
  by_cases hf : c₀.nreg (170200 + 5 * k) = 1
  · -- the slot is recorded: copy it
    have hlt : ¬ c.nreg (170200 + 5 * k) < c.nreg 170011 := by rw [h0, hf, h11]; omega
    obtain ⟨Va, Vb, hs⟩ := hok hf
    obtain ⟨hu, hLE, hq, hq1, hed⟩ := slotOK_edges hs
    set sl := slotAt c₀ k
    have e : slotsOf c₀ (k + 1) = slotsOf c₀ k ++ [sl] := by rw [hsucc, ite_eq_left hf]
    have hlen : ((slotsOf c₀ (k + 1)).flatMap (slotPcs c₀.nmem n)).length =
        ((slotsOf c₀ k).flatMap (slotPcs c₀.nmem n)).length + sl.q := by
      rw [e, List.flatMap_append, List.length_append, List.flatMap_singleton, slotPcs_length]
    have f1 : c.nreg (170201 + 5 * k) = sl.L := hsl _ (by omega) (by omega)
    have f2 : c.nreg (170202 + 5 * k) = sl.q := hsl _ (by omega) (by omega)
    have f3 : c.nreg (170203 + 5 * k) = sl.g₀ := hsl _ (by omega) (by omega)
    have f4 : c.nreg (170204 + 5 * k) = sl.u₀ := hsl _ (by omega) (by omega)
    have h22 := hA.r22
    have h23 := hA.r23
    -- the fields
    obtain ⟨c₁, k₁, e₁, hk₁, a30, a31, a32, a33, a34, a35, ar, am⟩ : ∃ c₁ k₁,
        Exec P W (asmSet k) c c₁ k₁ ∧ k₁ = 6 ∧ c₁.nreg 170230 = sl.L ∧ c₁.nreg 170231 = sl.q ∧
        c₁.nreg 170232 = sl.g₀ ∧ c₁.nreg 170233 = sl.u₀ ∧ c₁.nreg 170234 = sl.L + 1 ∧
        c₁.nreg 170235 = 0 ∧ (∀ r, (r < 170230 ∨ 170236 ≤ r) → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem := by
      unfold asmSet
      exec_block
      · config_simp; rw [f1, h11]; omega
      · omega
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl⟩
      · config_simp; exact f1
      · config_simp; simp only [upd]; split_ifs <;> first | omega | exact f2
      · config_simp; simp only [upd]; split_ifs <;> first | omega | exact f3
      · config_simp; simp only [upd]; split_ifs <;> first | omega | exact f4
      · config_simp; rw [f1, h11]
      · config_simp
      · config_simp; simp only [upd]; split_ifs <;> first | rfl | omega
    have F₁ := BuildRam.exec_frameM e₁ (wrM_asmSet k)
    have w₁ := e₁.wb_right
    -- the copy
    obtain ⟨c₂, k₂, e₂, hk₂, hk₂', d22, d23, dlo, dout, F₂⟩ := cpLoop_exec (P := P) c₁ w₁
      (n := n) (L := sl.L) (q := sl.q) (g₀ := sl.g₀) (u₀ := sl.u₀) (O := O)
      ((ar _ (by omega)).trans h10) ((ar _ (by omega)).trans h11) a31 a32 a33 a34 a35 hLE
      (by rw [ar _ (by omega), h22]; omega) (by rw [ar _ (by omega), h22]; omega)
      (by rw [ar _ (by omega), h23]; omega) (by rwa [hn]) hnW
      (fun i hi => by
        obtain ⟨b1, b2⟩ := hed i hi
        rw [am, hA.lo _ (by omega), hA.lo _ (by omega), hn]
        exact ⟨b1, b2⟩)
    have F₂' : BuildRam.FrameM Basm c₁ c₂ := frameM_mono F₂ (fun r hr => by
      simp only [Bcp, Basm, decide_eq_true_eq] at hr ⊢; omega)
    have q21 : c₂.nreg 170221 = O := by rw [F₂.1 _ (by decide), ar _ (by omega)]; exact hA.r21
    have q22 : c₁.nreg 170222 = c.nreg 170222 := ar _ (by omega)
    have q23 : c₁.nreg 170223 = c.nreg 170223 := ar _ (by omega)
    have hA' : AsmSt c₀.nmem n O (slotsOf c₀ k ++ [sl]) c₂ := hA.step q21
      (by rw [d22, q22]) (by rw [d23, q23])
      (fun a ha => by rw [dlo a (by rwa [q22]), am])
      (fun j hj f hf => by
        rw [← q22, dout j hj f hf, rdPc_congr (m := c₀.nmem) (m' := c₁.nmem) (E := O + 1)
          (fun a ha => by rw [am]; exact hA.lo a ha) (by omega)])
    refine ⟨c₂, _, .ifLtN_false hlt (.seq e₁ e₂), by rw [hlen]; omega, by rw [hlen]; omega,
      by rwa [e], (frameM_mono F₁ (fun r hr => hr)).trans F₂'⟩
  · -- the slot is free
    have hf0 : c₀.nreg (170200 + 5 * k) = 0 := by omega
    have hlt : c.nreg (170200 + 5 * k) < c.nreg 170011 := by rw [h0, hf0, h11]; omega
    have e : slotsOf c₀ (k + 1) = slotsOf c₀ k := by rw [hsucc, ite_eq_right hf, List.append_nil]
    refine ⟨c, _, .ifLtN_true hlt (.skip hw), by rw [e]; omega, by rw [e]; omega,
      by rwa [e], BuildRam.FrameM.refl _ _⟩

end exec

end

end IOrc

end Chazelle.Core
