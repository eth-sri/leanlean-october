module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.OraclePrepClus

/-!
# Lemma 3.6 (WP-H), preprocessing part 25: the list of `D*`, the order by label, the ranks

* `dlS`: the flagged nodes `v < μ` (`FL[v] = 1`) in increasing order at the allocator (`60100`),
  their number in `60102` (an emission loop, `dlS_exec`);
* `ordS`: the nodes sorted by label (`sortCore` with both keys `LAB`, base in `60007`);
* `rkS`: the ranks `RK[ORD[i]] := i` (`60110`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleBook OracleBook.BookData

@[expose] public section

/-! ## The list of `D*` -/

/-- The flagged nodes as pairs `(v, v)`. -/
def flφ (m : ℕ → ℕ) (FL : ℕ) (v : ℕ) : Option (ℕ × ℕ) := if m (FL + v) = 1 then some (v, v) else none

/-- The body: the flag of node `60103`. -/
def flBody : Stmt :=
  .seq (block [.addN 60107 130004 60103, .loadN 60107 60107])
    (.ifLtN 60107 120011 (.instr (.constN 60104 0))
      (.ifLtN 120011 60107 (.instr (.constN 60104 0))
        (block [.constN 60104 1, .copyN 60105 60103])))

/-- The registers written by `flBody`. -/
def BFl (r : ℕ) : Bool := decide (r = 60104 ∨ r = 60105 ∨ r = 60107)

theorem flBody_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {FL v : ℕ}
    (hFL : c.nreg 130004 = FL) (hv : c.nreg 60103 = v) (h1 : c.nreg 120011 = 1)
    (hW : FL + v ≤ W) :
    ∃ c' k, Exec P W flBody c c' k ∧ k ≤ 8 ∧ FrameB BFl c c' ∧
      (flφ c.nmem FL v = none → c'.nreg 60104 = 0) ∧
      ∀ x, flφ c.nmem FL v = some x → c'.nreg 60104 = 1 ∧ c'.nreg 60105 = x.1 ∧
        c'.nreg 60105 = x.2 := by
  have hwr : wr BFl flBody = true := ⌖
  suffices H : ∃ c' k, Exec P W flBody c c' k ∧ k ≤ 8 ∧
      (flφ c.nmem FL v = none → c'.nreg 60104 = 0) ∧
      ∀ x, flφ c.nmem FL v = some x → c'.nreg 60104 = 1 ∧ c'.nreg 60105 = x.1 ∧
        c'.nreg 60105 = x.2 by
    obtain ⟨c', k, ex, hk, a, b⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, a, b⟩
  obtain ⟨c₁, k₁, e₁, hk₁, v7, R₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 60107 130004 60103, .loadN 60107 60107]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 60107 = c.nmem (FL + v) ∧ (∀ r, r ≠ 60107 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    · rw [hFL, hv]; exact hW
    · refine ⟨rfl, by config_simp; rw [hFL, hv], fun r hr => ?_, rfl⟩
      config_simp; ϴ upd_apply, ite_eq_right hr
  have hW1 : 1 ≤ W := by have := hw.1 120011; Ξ' h1 at this; exact this
  have w₁ := e₁.wb_right
  have g1 : c₁.nreg 120011 = 1 := Ρ R₁ _ (⌖), h1
  have gv : c₁.nreg 60103 = v := Ρ R₁ _ (⌖), hv
  unfold flφ
  by_cases hf : c.nmem (FL + v) = 1
  · ϴ hf, ite_true, reduceCtorEq, false_imp_iff, Option.some.injEq, true_and
    obtain ⟨c₂, k₂, e₂, hk₂, a, b⟩ : ∃ c₂ k₂, Exec P W (block [.constN 60104 1, .copyN 60105 60103])
        c₁ c₂ k₂ ∧ k₂ = 2 ∧ c₂.nreg 60104 = 1 ∧ c₂.nreg 60105 = v := by
      exec_block
      · omega
      · exact ⟨rfl, by config_simp, by config_simp; exact gv⟩
    refine ⟨c₂, _, .seq e₁ (.ifLtN_false (by rw [v7, g1, hf]; omega)
      (.ifLtN_false (by rw [v7, g1, hf]; omega) e₂)), ⋄, fun x hx => ?_⟩
    subst hx; exact ⟨a, b, b⟩
  · ϴ hf, ite_false, forall_const, reduceCtorEq, false_imp_iff, and_true
    rcases Nat.lt_or_gt_of_ne hf with h | h
    · have e₂ := Exec.constN (P := P) w₁ 60104 0 (Nat.zero_le _)
      exact ⟨_, _, .seq e₁ (.ifLtN_true (by rw [v7, g1]; exact h) e₂), ⋄,
        by config_simp⟩
    · have e₂ := Exec.constN (P := P) w₁ 60104 0 (Nat.zero_le _)
      exact ⟨_, _, .seq e₁ (.ifLtN_false (by rw [v7, g1]; omega)
        (.ifLtN_true (by rw [v7, g1]; exact h) e₂)), ⋄, by config_simp⟩

/-- **The list of `D*`.** -/
def dlS : Stmt :=
  .seq (block [.copyN 60100 9999, .addN 60101 60100 60034, .addN 9999 60101 60034,
      .constN 60102 0])
    (emitS 60103 60034 120011 60104 60105 60105 60100 60101 60102 60106 flBody)

theorem dlS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {μ FL A₀ : ℕ}
    (hμ : c.nreg 60034 = μ) (hFL : c.nreg 130004 = FL) (h1 : c.nreg 120011 = 1)
    (hAl : c.nreg 9999 = A₀) (hFA : FL + μ ≤ A₀) (hW : A₀ + 2 * μ ≤ W) :
    ∃ c' k, Exec P W dlS c c' k ∧ k ≤ μ * 18 + 7 ∧
      (∀ r, (r < 60100 ∨ 60107 < r) → r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      (∀ r, BFl r = false → c'.rreg r = c.rreg r) ∧
      (∀ a, a < A₀ → c'.nmem a = c.nmem a) ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 9999 = A₀ + 2 * μ ∧ c'.nreg 60100 = A₀ ∧
      c'.nreg 60102 = (emitted (flφ c.nmem FL) μ).length ∧
      PairsAt c'.nmem A₀ (A₀ + μ) (emitted (flφ c.nmem FL) μ) := by
  obtain ⟨c₁, k₁, e₁, hk₁, a100, a101, a99, a102, K₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.copyN 60100 9999, .addN 60101 60100 60034, .addN 9999 60101 60034,
        .constN 60102 0]) c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 60100 = A₀ ∧ c₁.nreg 60101 = A₀ + μ ∧
      c₁.nreg 9999 = A₀ + 2 * μ ∧ c₁.nreg 60102 = 0 ∧
      (∀ r, r ≠ 60100 → r ≠ 60101 → r ≠ 9999 → r ≠ 60102 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · config_simp; rw [hAl, hμ]; omega
    · config_simp; rw [hAl, hμ]; omega
    · omega
    · refine ⟨rfl, by config_simp; exact hAl, by config_simp; rw [hAl, hμ],
        by config_simp; rw [hAl, hμ]; ring, by config_simp, fun r a b d e => ?_, rfl, rfl, rfl, rfl⟩
      config_simp; simp only [upd_apply]
      rw [ite_eq_right e, ite_eq_right d, ite_eq_right b, ite_eq_right a]
  let J : Config → Prop := fun d => d.nreg 130004 = FL ∧ d.nreg 120011 = 1 ∧
    ∀ a, a < A₀ → d.nmem a = c.nmem a
  obtain ⟨c', k, ex, hk, r', rr', cnt, pairs, mem, rm, o, -⟩ := emitS_exec (P := P) (W := W)
    (ri := 60103) (rn := 60034) (r1 := 120011) (rf := 60104) (rv1 := 60105) (rv2 := 60105)
    (rR1 := 60100) (rR2 := 60101) (rc := 60102) (rt := 60106) (body := flBody) (B := BFl)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (R1 := A₀) (R2 := A₀ + μ) (c₀ := 0) (n := μ) (κ := 8) J
    (fun d d' hJd hr hm => ⟨by rw [hr _ (by decide) (by decide) (by decide) (by decide)]; exact hJd.1,
      by rw [hr _ (by decide) (by decide) (by decide) (by decide)]; exact hJd.2.1,
      fun a ha => by rw [hm a (Or.inl (by omega))]; exact hJd.2.2 a ha⟩)
    (flφ c.nmem FL)
    (fun i d hi hJd hwd hri => by
      obtain ⟨d', k, ex, hk, F, a, b⟩ := flBody_exec (P := P) hwd hJd.1 hri hJd.2.1 (by omega)
      have e : flφ d.nmem FL i = flφ c.nmem FL i := by
        unfold flφ; rw [hJd.2.2 _ (by omega)]
      exact ⟨d', k, ex, hk, F, by rw [← e]; exact a, by rw [← e]; exact b⟩)
    e₁.wb_right ⟨by rw [K₁ _ (by decide) (by decide) (by decide) (by decide), hFL],
      by rw [K₁ _ (by decide) (by decide) (by decide) (by decide), h1], fun a _ => by rw [m₁]⟩
    (by rw [K₁ _ (by decide) (by decide) (by decide) (by decide), hμ])
    (by rw [K₁ _ (by decide) (by decide) (by decide) (by decide), h1]) a100 a101 a102
    (by omega) (by omega)
  simp only [Nat.add_zero, Nat.zero_add] at cnt pairs mem
  refine ⟨c', _, .seq e₁ ex, by omega, fun r hr h9 => ?_, fun r hr => by rw [rr' r hr, rr₁],
    fun a ha => by rw [mem a (Or.inl ha), m₁], by rw [rm, rm₁], by rw [o, o₁], ?_, ?_, cnt, pairs⟩
  · rw [r' r (by unfold BFl; simp only [decide_eq_false_iff_not]; omega) (by omega) (by omega)
      (by omega), K₁ r (by omega) (by omega) h9 (by omega)]
  · rw [r' _ (by decide) (by decide) (by decide) (by decide), a99]
  · rw [r' _ (by decide) (by decide) (by decide) (by decide), a100]

/-- **The facts of the list of `D*`.** -/
theorem dl_facts (m : ℕ → ℕ) (FL μ : ℕ) :
    (∀ i, i < (emitted (flφ m FL) μ).length →
      ((emitted (flφ m FL) μ).getD i (0, 0)).1 < μ ∧
        m (FL + ((emitted (flφ m FL) μ).getD i (0, 0)).1) = 1) ∧
    (∀ v, v < μ → m (FL + v) = 1 → ∃ i, i < (emitted (flφ m FL) μ).length ∧
      ((emitted (flφ m FL) μ).getD i (0, 0)).1 = v) ∧
    (emitted (flφ m FL) μ).length = ((Finset.range μ).filter fun v => m (FL + v) = 1).card := by
  set L := emitted (flφ m FL) μ with hL
  have hφ : ∀ j x, flφ m FL j = some x → x = (j, j) ∧ m (FL + j) = 1 := fun j x h => by
    unfold flφ at h; split_ifs at h with h'
    · exact ⟨(Option.some.inj h).symm, h'⟩
  refine ⟨fun i hi => ?_, fun v hv hf => ?_, ?_⟩
  · obtain ⟨j, hj, e⟩ := mem_emitted.1 (getD_mem hi)
    obtain ⟨rfl', h'⟩ := hφ j _ e
    rw [rfl']; exact ⟨hj, h'⟩
  · have : (v, v) ∈ L := mem_emitted.2 ⟨v, hv, by unfold flφ; rw [ite_eq_left hf]⟩
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem this
    exact ⟨i, hi, Ρ NFLoc.getD_of_lt _ hi, e⟩
  · have hnd : L.Nodup := emitted_nodup (fun i x h => Ρ (hφ i x h).1) μ
    Ξ ← List.toFinset_card_of_nodup hnd
    rw [show L.toFinset = ((Finset.range μ).filter fun v => m (FL + v) = 1).image (fun v => (v, v))
      by
        ext x
        ϴ List.mem_toFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_range
        constructor
        · intro hx
          obtain ⟨j, hj, e⟩ := mem_emitted.1 hx
          obtain ⟨rfl', h'⟩ := hφ j _ e
          exact ⟨j, ⟨hj, h'⟩, rfl'.symm⟩
        · rintro ⟨j, ⟨hj, h'⟩, rfl⟩
          exact mem_emitted.2 ⟨j, hj, by unfold flφ; rw [ite_eq_left h']⟩]
    exact Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)

/-! ## The order by label and the ranks -/

/-- The inputs of the sort by label. -/
def ordPrep : Stmt := block [.copyN 60004 130005, .copyN 60005 130005, .copyN 60006 60034]

/-- The body of the ranks: address `RK + ORD[i]`, value `i`. -/
def rkBody : Stmt :=
  block [.addN 60111 60007 60112, .loadN 60111 60111, .addN 60113 60110 60111, .copyN 60114 60112]

/-- **The ranks.** -/
def rkS : Stmt := .seq (allocS 60110 60034) (scatS 60112 60034 120011 60113 60114 rkBody)

/-- **The list of `D*`, the order by label and the ranks.** -/
def ordStage : Stmt := .seq dlS (.seq ordPrep (.seq sortCore rkS))

/-- The facts of the order stage. -/
structure OrdFacts (m : ℕ → ℕ) (μ FL LAB DL nD ORD RK : ℕ) : Prop where
  dl : ∀ i, i < nD → m (DL + i) < μ ∧ m (FL + m (DL + i)) = 1
  dl_all : ∀ v, v < μ → m (FL + v) = 1 → ∃ i, i < nD ∧ m (DL + i) = v
  nD_eq : nD = ((Finset.range μ).filter fun v => m (FL + v) = 1).card
  ord_lt : ∀ i, i < μ → m (ORD + i) < μ
  ord_inj : ∀ i j, i < μ → j < μ → m (ORD + i) = m (ORD + j) → i = j
  ord_rk : ∀ u, u < μ → m (RK + u) < μ ∧ m (ORD + m (RK + u)) = u
  ord_sorted : ∀ i j, i ≤ j → j < μ → m (LAB + m (ORD + i)) ≤ m (LAB + m (ORD + j))

/-- The facts survive memories agreeing below a bound above all the arrays. -/
theorem OrdFacts.mono {m m' : ℕ → ℕ} {μ FL LAB DL nD ORD RK X : ℕ}
    (h : OrdFacts m μ FL LAB DL nD ORD RK) (hX : ∀ a, a < X → m' a = m a)
    (hFL : FL + μ ≤ X) (hLAB : LAB + μ ≤ X) (hDL : DL + nD ≤ X) (hORD : ORD + μ ≤ X)
    (hRK : RK + μ ≤ X) : OrdFacts m' μ FL LAB DL nD ORD RK where
  dl i hi := by
    rw [hX _ (⋄)]; obtain ⟨a, b⟩ := h.dl i hi; rw [hX _ (⋄)]; exact ⟨a, b⟩
  dl_all v hv hf := by
    Ξ' hX _ (⋄) at hf
    obtain ⟨i, hi, e⟩ := h.dl_all v hv hf
    exact ⟨i, hi, by rw [hX _ (⋄)]; exact e⟩
  nD_eq := by
    rw [h.nD_eq]; congr 1; ext v
    ϴ Finset.mem_filter, Finset.mem_range
    constructor
    · rintro ⟨hv, e⟩; exact ⟨hv, by rw [hX _ (⋄)]; exact e⟩
    · rintro ⟨hv, e⟩; exact ⟨hv, by rw [← hX _ (⋄)]; exact e⟩
  ord_lt i hi := by rw [hX _ (⋄)]; exact h.ord_lt i hi
  ord_inj i j hi hj e := by
    Ξ' hX _ (⋄), hX _ (⋄) at e; exact h.ord_inj i j hi hj e
  ord_rk u hu := by
    obtain ⟨a, b⟩ := h.ord_rk u hu
    rw [hX _ (⋄), hX _ (⋄)]; exact ⟨a, b⟩
  ord_sorted i j hij hj := by
    have a := h.ord_lt i (⋄)
    have b := h.ord_lt j hj
    Ξ hX (ORD + i) (⋄), hX (ORD + j) (⋄), hX _ (⋄), hX _ (⋄)
    exact h.ord_sorted i j hij hj

theorem rkBody_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {ORD RK i : ℕ}
    (h7 : c.nreg 60007 = ORD) (h10 : c.nreg 60110 = RK) (hi : c.nreg 60112 = i)
    (hb1 : ORD + i ≤ W) (hb2 : RK + c.nmem (ORD + i) ≤ W) :
    ∃ c' k, Exec P W rkBody c c' k ∧ k ≤ 4 ∧
      FrameB (fun r => decide (r = 60111 ∨ r = 60113 ∨ r = 60114)) c c' ∧
      c'.nreg 60113 = RK + c.nmem (ORD + i) ∧ c'.nreg 60114 = i := by
  have hwr : wr (fun r => decide (r = 60111 ∨ r = 60113 ∨ r = 60114)) rkBody = true := ⌖
  suffices H : ∃ c' k, Exec P W rkBody c c' k ∧ k ≤ 4 ∧
      c'.nreg 60113 = RK + c.nmem (ORD + i) ∧ c'.nreg 60114 = i by
    obtain ⟨c', k, ex, hk, a, b⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, a, b⟩
  unfold rkBody
  exec_block
  · rw [h7, hi]; exact hb1
  · config_simp; rw [h7, hi, h10]; exact hb2
  · exact ⟨⋄, by config_simp; rw [h7, hi, h10], by config_simp; exact hi⟩

theorem rkS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {μ ORD A : ℕ}
    (h7 : c.nreg 60007 = ORD) (hμ : c.nreg 60034 = μ) (h1 : c.nreg 120011 = 1)
    (hAl : c.nreg 9999 = A) (hOA : ORD + μ ≤ A) (hW : A + μ ≤ W)
    (hlt : ∀ t, t < μ → c.nmem (ORD + t) < μ) :
    ∃ c' k, Exec P W rkS c c' k ∧ k ≤ μ * 8 + 5 ∧
      (∀ r, (r < 60110 ∨ 60114 < r) → r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 60110 ∨ 60114 < r) → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 60110 = A ∧ c'.nreg 9999 = A + μ ∧
      c'.nmem = scat c.nmem (fun i => A + c.nmem (ORD + i)) (fun i => i) μ := by
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, rr₁, a10, a99⟩ := allocS_exec (P := P) hw (rb := 60110) (rn := 60034)
    (A := A) (n := μ) (by decide) hAl hμ (by decide) hW
  have hm₁ : c₁.nmem = c.nmem := F₁.2.2.1
  obtain ⟨c', k, ex, hk, r', rr', mm, rm, o, -, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 60112) (rn := 60034) (r1 := 120011) (ra := 60113) (rv := 60114) (body := rkBody)
    (B := fun r => decide (r = 60111 ∨ r = 60113 ∨ r = 60114)) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun d => d.nreg 60007 = ORD ∧ d.nreg 60110 = A ∧ ∀ a, a < A → d.nmem a = c.nmem a) A
    (fun d d' hJ hr hm => ⟨by rw [hr _ (by decide) (by decide)]; exact hJ.1,
      by rw [hr _ (by decide) (by decide)]; exact hJ.2.1,
      fun a ha => by rw [hm a ha]; exact hJ.2.2 a ha⟩)
    (n := μ) (κ := 4) (fun i => A + c.nmem (ORD + i)) (fun i => i) (fun i _ => by omega)
    (fun i d hi hJd hwd hri => by
      have e : d.nmem (ORD + i) = c.nmem (ORD + i) := hJd.2.2 _ (by omega)
      obtain ⟨d', k, ex, hk, F, v1, v2⟩ := rkBody_exec (P := P) hwd hJd.1 hJd.2.1 hri (by omega)
        (by rw [e]; have := hlt i hi; omega)
      exact ⟨d', k, ex, hk, F, by rw [v1, e], v2⟩)
    e₁.wb_right ⟨by rw [F₁.1 _ (by decide), h7], a10, fun a _ => by rw [hm₁]⟩
    (by rw [F₁.1 _ (by decide), hμ]) (by rw [F₁.1 _ (by decide), h1]) (by omega)
  refine ⟨c', _, .seq e₁ ex, by nlinarith, fun r hr h9 => ?_, ?_, by rw [rm, F₁.2.2.2.1],
    by rw [o, F₁.2.2.2.2], by rw [r' _ (by decide) (by decide), a10],
    by rw [r' _ (by decide) (by decide), a99], by rw [mm, hm₁]⟩
  · rw [r' r (by simp only [decide_eq_false_iff_not]; omega) (by omega),
      F₁.1 r (by simp only [decide_eq_false_iff_not]; omega)]
  · intro r hr
    rw [rr' r (by simp only [decide_eq_false_iff_not]; omega), rr₁]

/-- The band-`6` registers kept by `ordStage`. -/
def OKeep (r : ℕ) : Prop :=
  r < 60004 ∨ (60008 ≤ r ∧ r ≤ 60015) ∨ (60021 ≤ r ∧ r ≤ 60099) ∨ 60115 ≤ r


theorem ordStage_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {μ FL LAB A₀ : ℕ} (hμ : c.nreg 60034 = μ) (hFL : c.nreg 130004 = FL)
    (hLAB : c.nreg 130005 = LAB) (h1 : c.nreg 120011 = 1) (hAl : c.nreg ALLOC = A₀)
    (hFA : FL + μ ≤ A₀) (hLA : LAB + μ ≤ A₀)
    (hroom : A₀ + 4 * μ + SortR.sortCost 20 μ ≤ W) :
    ∃ c' k, Exec P W ordStage c c' k ∧ k ≤ 40 * μ + SortR.sortCost 20 μ + 40 ∧
      FrameN dBands c c' ∧ A₀ ≤ c'.nreg ALLOC ∧
      c'.nreg ALLOC ≤ A₀ + 4 * μ + SortR.sortCost 20 μ ∧
      (∀ r, bandOf r = 6 → OKeep r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < A₀ → c'.nmem a = c.nmem a) ∧
      c'.nreg 60100 + c'.nreg 60102 ≤ c'.nreg ALLOC ∧ c'.nreg 60007 + μ ≤ c'.nreg ALLOC ∧
      c'.nreg 60110 + μ ≤ c'.nreg ALLOC ∧
      OrdFacts c'.nmem μ FL LAB (c'.nreg 60100) (c'.nreg 60102) (c'.nreg 60007) (c'.nreg 60110) := by
  have hAL : ALLOC = 9999 := rfl
  have hAl' : c.nreg 9999 = A₀ := hAl
  -- 1. the list of `D*`
  obtain ⟨c₁, k₁, e₁, hk₁, r₁, rr₁, mem₁, rm₁, o₁, a99, a100, cnt, pairs⟩ :=
    dlS_exec (P := P) hw hμ hFL h1 hAl' hFA (by have := SortR.sortCost_ge 20 μ; omega)
  set L := emitted (flφ c.nmem FL) μ with hL
  have hLlen : L.length ≤ μ := emitted_length_le _ _
  -- 2. the inputs of the sort
  have b130005 : c₁.nreg 130005 = LAB := by rw [r₁ _ (by omega) (by omega), hLAB]
  have b60034 : c₁.nreg 60034 = μ := by rw [r₁ _ (by omega) (by omega), hμ]
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, w4, w5, w6⟩ : ∃ c₂ k₂, Exec P W ordPrep c₁ c₂ k₂ ∧ k₂ = 3 ∧
      FrameB (fun r => decide (60004 ≤ r ∧ r ≤ 60006)) c₁ c₂ ∧ c₂.nreg 60004 = LAB ∧
      c₂.nreg 60005 = LAB ∧ c₂.nreg 60006 = μ := by
    have hwr : wr (fun r => decide (60004 ≤ r ∧ r ≤ 60006)) ordPrep = true := by decide
    suffices H : ∃ c₂ k₂, Exec P W ordPrep c₁ c₂ k₂ ∧ k₂ = 3 ∧ c₂.nreg 60004 = LAB ∧
        c₂.nreg 60005 = LAB ∧ c₂.nreg 60006 = μ by
      obtain ⟨c₂, k₂, ex, hk, a, b, d⟩ := H
      exact ⟨c₂, k₂, ex, hk, exec_frameB ex hwr, a, b, d⟩
    have w₁ := e₁.wb_right
    unfold ordPrep
    exec_block
    exact ⟨rfl, by config_simp; exact b130005, by config_simp; exact b130005,
      by config_simp; exact b60034⟩
  have hm₂ : c₂.nmem = c₁.nmem := F₂.2.2.1
  have c99 : c₂.nreg 9999 = A₀ + 2 * μ := by rw [F₂.1 _ (by decide), a99]
  have c1 : c₂.nreg 120011 = 1 := by rw [F₂.1 _ (by decide), r₁ _ (by omega) (by omega), h1]
  -- 3. the sort
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, al3a, al3b, R₃, sb₁, sb₂, hsort, hsurj, hlt⟩ :=
    sortCore_exec (P := P) e₂.wb_right (Z1 := LAB) (Z2 := LAB) (n := μ) (A₀ := A₀ + 2 * μ)
      w4 w5 w6 c1 c99 (by omega) (by omega) (by omega)
  rw [hAL] at al3a al3b
  set ORD := c₃.nreg 60007 with hORD
  set A₃ := c₃.nreg 9999 with hA₃
  have mem₃ : ∀ a, a < A₀ + 2 * μ → c₃.nmem a = c₁.nmem a := fun a ha => by
    rw [F₃.2.2.1 a (by rw [hAL, c99]; exact ha), hm₂]
  -- 4. the ranks
  have d34 : c₃.nreg 60034 = μ := by
    rw [R₃ _ (by unfold bandOf; norm_num) (by decide) (by decide) (by decide) (by decide),
      F₂.1 _ (by decide), b60034]
  have d1 : c₃.nreg 120011 = 1 := by
    rw [F₃.1 _ (by simp [dBands, bSort, bDecomp, bOPrep, bandOf]) (by decide), c1]
  obtain ⟨c₄, k₄, e₄, hk₄, r₄, rr₄, rm₄, o₄, v110, v99, mm₄⟩ := rkS_exec (P := P) e₃.wb_right
    (ORD := ORD) (A := A₃) rfl d34 d1 rfl sb₂ (by omega) hlt
  have below₄ : ∀ a, a < A₃ → c₄.nmem a = c₃.nmem a := fun a ha => by
    rw [mm₄, scat_below (fun i _ => by omega) ha]
  have ex : Exec P W ordStage c c₄ _ := .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have K6 : ∀ r, bandOf r = 6 → OKeep r → c₄.nreg r = c.nreg r := fun r hr hk => by
    unfold OKeep at hk; unfold bandOf at hr
    rw [r₄ r (by omega) (by omega), R₃ r (by unfold bandOf; omega) (by omega) (by omega) (by omega)
      (by omega), F₂.1 r (by simp only [decide_eq_false_iff_not]; omega),
      r₁ r (by omega) (by omega)]
  have g100 : c₄.nreg 60100 = A₀ := by
    rw [r₄ _ (by omega) (by omega), R₃ _ (by unfold bandOf; norm_num) (by decide) (by decide)
      (by decide) (by decide), F₂.1 _ (by decide), a100]
  have g102 : c₄.nreg 60102 = L.length := by
    rw [r₄ _ (by omega) (by omega), R₃ _ (by unfold bandOf; norm_num) (by decide) (by decide)
      (by decide) (by decide), F₂.1 _ (by decide), cnt]
  have g7 : c₄.nreg 60007 = ORD := r₄ _ (by omega) (by omega)
  have mem : ∀ a, a < A₀ → c₄.nmem a = c.nmem a := fun a ha => by
    rw [below₄ a (by omega), mem₃ a (by omega), mem₁ a ha]
  have hDL : ∀ i, i < L.length → c₄.nmem (A₀ + i) = (L.getD i (0, 0)).1 := fun i hi => by
    rw [below₄ _ (by omega), mem₃ _ (by omega)]; exact (pairs i hi).1
  have hORDm : ∀ t, t < μ → c₄.nmem (ORD + t) = c₃.nmem (ORD + t) := fun t ht =>
    below₄ _ (by omega)
  obtain ⟨D1, D2, D3⟩ := dl_facts c.nmem FL μ
  refine ⟨c₄, _, ex, ?_, ?_, ?_, ?_, K6, mem, ?_, ?_, ?_, ?_⟩
  · have := SortR.sortCost_ge 20 μ; omega
  · -- the frame
    have B6 : ∀ r, (decide (bandOf r = 6) || decide (r = 9999)) = true →
        bandOf r ∈ dBands ∨ r = ALLOC := fun r hr => by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
      rcases hr with h | h
      · left; simp [dBands, bDecomp, h]
      · right; exact h
    have FA : FrameN dBands c c₂ := PF.frameN (B := fun r => decide (bandOf r = 6) || decide (r = 9999))
      ⟨fun r hr => by
        have := b6_ne hr
        rw [F₂.1 r (by simp only [decide_eq_false_iff_not]; omega), r₁ r (by omega) this.1],
      fun r hr => by
        have := b6_ne hr
        rw [F₂.2.1 r (by simp only [decide_eq_false_iff_not]; omega),
          rr₁ r (by unfold BFl; simp only [decide_eq_false_iff_not]; omega)],
      fun a ha => by rw [hAL, hAl'] at ha; rw [hm₂, mem₁ a ha],
      fun a _ => by rw [F₂.2.2.2.1, rm₁], by rw [F₂.2.2.2.2, o₁]⟩ B6
      (by rw [hAL, F₂.2.1 _ (by decide), rr₁ _ (by decide)])
    have FC : FrameN dBands c₃ c₄ := PF.frameN (B := fun r => decide (bandOf r = 6) || decide (r = 9999))
      ⟨fun r hr => by
        have := b6_ne hr
        exact r₄ r (by omega) this.1,
      fun r hr => by
        have := b6_ne hr
        exact rr₄ r (by omega),
      fun a ha => by rw [hAL] at ha; exact below₄ a ha,
      fun a _ => by rw [rm₄], by rw [o₄]⟩ B6 (by rw [hAL]; exact rr₄ _ (by omega))
    exact (FA.trans F₃ (by rw [hAL, hAl', c99]; omega)).trans FC
      (by rw [hAL, hAl']; omega)
  · rw [hAL, v99]; omega
  · rw [hAL, v99]; omega
  · rw [g100, g102, hAL, v99]; omega
  · rw [g7, hAL, v99]; omega
  · rw [v110, hAL, v99]
  · rw [g100, g102, g7, v110]
    have hFLm : ∀ v, v < μ → c₄.nmem (FL + v) = c.nmem (FL + v) := fun v hv => mem _ (by omega)
    have hinj : ∀ t t', t < μ → t' < μ → c₃.nmem (ORD + t) = c₃.nmem (ORD + t') → t = t' :=
      fun t t' ht ht' e => inj_of_surj hlt hsurj ht ht' e
    exact
      { dl := fun i hi => by
          rw [hDL i hi, hFLm _ (D1 i hi).1]; exact D1 i hi
        dl_all := fun v hv hf => by
          rw [hFLm v hv] at hf
          obtain ⟨i, hi, e⟩ := D2 v hv hf
          exact ⟨i, hi, by rw [hDL i hi, e]⟩
        nD_eq := by
          rw [D3]; congr 1; ext v
          simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨hv, e⟩; exact ⟨hv, by rw [hFLm v hv]; exact e⟩
          · rintro ⟨hv, e⟩; exact ⟨hv, by rw [← hFLm v hv]; exact e⟩
        ord_lt := fun i hi => by rw [hORDm i hi]; exact hlt i hi
        ord_inj := fun i j hi hj e => by
          rw [hORDm i hi, hORDm j hj] at e; exact hinj i j hi hj e
        ord_rk := fun u hu => by
          obtain ⟨t, ht, e⟩ := hsurj u hu
          have : c₄.nmem (A₃ + u) = t := by
            rw [mm₄, ← e]
            exact scat_at (g := fun i => A₃ + c₃.nmem (ORD + i)) ht
              fun j hj htj e' => by
                try simp only at e'
                have := hinj j t hj ht (by omega)
                omega
          rw [this, hORDm t ht]; exact ⟨ht, e⟩
        ord_sorted := fun i j hij hj => by
          have hs := hsort i j hij hj
          have ai := hlt i (by omega)
          have aj := hlt j hj
          rw [hORDm i (by omega), hORDm j hj, below₄ (LAB + c₃.nmem (ORD + i)) (by omega),
            below₄ (LAB + c₃.nmem (ORD + j)) (by omega)]
          simp only at hs
          rw [F₃.2.2.1 (LAB + c₃.nmem (ORD + i)) (by rw [hAL, c99]; omega),
            F₃.2.2.1 (LAB + c₃.nmem (ORD + j)) (by rw [hAL, c99]; omega)]
          unfold PLe at hs; simp only at hs; omega }

end

end OracleR

end Chazelle.Core
