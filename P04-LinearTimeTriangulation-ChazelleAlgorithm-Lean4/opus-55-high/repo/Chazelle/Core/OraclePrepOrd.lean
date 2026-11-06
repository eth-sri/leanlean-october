module

public import Chazelle.MacT
public import Chazelle.Core.OraclePrepZipSp3
public import Chazelle.Core.SpecNF
public import Chazelle.Core.OracleQueryExec

namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleBook OracleBook.BookData
@[expose] public section
def flφ (m : ℕ → ℕ) (FL : ℕ) (v : ℕ) : Option ztw := if m ztcen = 1 then some ztoji else none

/-- The body: the flag of node `60103`. -/
def flBody : Stmt :=
  .seq ztjox
    (.ifLtN 60107 120011 ztoue
      (.ifLtN 120011 60107 ztoue
        (block [.constN 60104 1, .copyN 60105 60103])))

/-- The registers written by `flBody`. -/
def BFl (r : ℕ) : Bool := decide (r = 60104 ∨ r = 60105 ∨ r = 60107)
variable {P : Polygon} {W : ℕ} {c : Config}
theorem flBody_exec (hw : WordsBounded W c) {FL v : ℕ}
    (hFL : c.nreg 130004 = FL) (hv : c.nreg 60103 = v) (h1 : c.nreg 120011 = 1)
    (hW : FL + v ≤ W) :
    ∃ c' k, Exec P W flBody c c' k ∧ k ≤ 8 ∧ FrameB BFl c c' ∧
      ztjve ∧
      ∀ x, flφ c.nmem FL v = some x → c'.nreg 60104 = 1 ∧ c'.nreg 60105 = x.1 ∧
        c'.nreg 60105 = x.2 := by
  have hwr : wr BFl flBody = true := by_decide
  suffices H : ∃ c' k, Exec P W flBody c c' k ∧ k ≤ 8 ∧
      ztjve ∧
      ∀ x, flφ c.nmem FL v = some x → c'.nreg 60104 = 1 ∧ c'.nreg 60105 = x.1 ∧
        c'.nreg 60105 = x.2 by
    zumr

  obtain ⟨c₁, k₁, e₁, hk₁, v7, R₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      ztjox c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 60107 = c.nmem ztcen ∧ (∀ r, r ≠ 60107 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    · omega
    simp_all
  have hW1 : ztbla := by have := hw.1 120011; omega
  zud
  zujxr
  have gv : c₁.nreg 60103 = v := by_simp_all
  unfold flφ
  by_cases hf : c.nmem ztcen = 1
  · simp only [hf, ite_true, reduceCtorEq, false_imp_iff, Option.some.injEq, true_and]
    obtain ⟨c₂, k₂, e₂, hk₂, a, b⟩ : ∃ c₂ k₂, Exec P W (block [.constN 60104 1, .copyN 60105 60103])
        c₁ c₂ k₂ ∧ k₂ = 2 ∧ c₂.nreg 60104 = 1 ∧ c₂.nreg 60105 = v := by
      exec_block
      · omega
      simp_all
    refine ⟨c₂, _, .seq e₁ (.ifLtN_false by_omega
      ztcry), by_omega, fun x hx => ?_⟩
    grind
  · simp only [hf, ite_false, forall_const, reduceCtorEq, false_imp_iff, and_true]
    rcases Nat.lt_or_gt_of_ne hf with h | h
    · zuept
      exact ⟨_, _, .seq e₁ ztbxn, by_omega,
        by config_simp⟩
    · zuept
      exact ⟨_, _, .seq e₁ (.ifLtN_false by_omega
        ztbxn), by_omega, by config_simp⟩

/-- **The list of `D*`.** -/
def dlS : Stmt :=
  .seq (block [.copyN 60100 9999, .addN 60101 60100 60034, .addN 9999 60101 60034,
      .constN 60102 0])
    (emitS 60103 60034 120011 60104 60105 60105 60100 60101 60102 60106 flBody)
theorem dlS_exec (hw : WordsBounded W c) {μ FL A₀ : ℕ}
    (hμ : c.nreg 60034 = μ) (hFL : c.nreg 130004 = FL) (h1 : c.nreg 120011 = 1)
    (hAl : c.nreg 9999 = A₀) (hFA : FL + μ ≤ A₀) (hW : A₀ + 2 * μ ≤ W) :
    ∃ c' k, Exec P W dlS c c' k ∧ k ≤ μ * 18 + 7 ∧
      (∀ r, (r < 60100 ∨ 60107 < r) → r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      (∀ r, BFl r = false → c'.rreg r = c.rreg r) ∧
      ztpt ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 9999 = A₀ + 2 * μ ∧ c'.nreg 60100 = A₀ ∧
      c'.nreg 60102 = (emitted ztjvf μ).length ∧
      PairsAt c'.nmem A₀ (A₀ + μ) (emitted ztjvf μ) := by
  obtain ⟨c₁, k₁, e₁, hk₁, a100, a101, a99, a102, K₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.copyN 60100 9999, .addN 60101 60100 60034, .addN 9999 60101 60034,
        .constN 60102 0]) c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 60100 = A₀ ∧ c₁.nreg 60101 = A₀ + μ ∧
      c₁.nreg 9999 = A₀ + 2 * μ ∧ c₁.nreg 60102 = 0 ∧
      (∀ r, r ≠ 60100 → r ≠ 60101 → r ≠ 9999 → r ≠ 60102 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · config_simp; omega
    · config_simp; omega
    · omega
    · refine ⟨rfl, by_simp_all, by_simp_all,
        by config_simp; omega, by config_simp, fun r a b d e => ?_, rfl, rfl, rfl, rfl⟩
      simp_all
  let J : Config → Prop := fun d => d.nreg 130004 = FL ∧ d.nreg 120011 = 1 ∧
    ∀ a, a < A₀ → d.nmem a = c.nmem a
  obtain ⟨c', k, ex, hk, r', rr', cnt, pairs, mem, rm, o, -⟩ := emitS_exec (P := P) (W := W)
    (ri := 60103) (rn := 60034) (r1 := 120011) (rf := 60104) (rv1 := 60105) (rv2 := 60105)
    (rR1 := 60100) (rR2 := 60101) (rc := 60102) (rt := 60106) (body := flBody) (B := BFl)
    by_decide by_decide by_decide by_decide by_decide by_decide by_decide
    (R1 := A₀) (R2 := A₀ + μ) (c₀ := 0) (n := μ) (κ := 8) J
    (fun d d' hJd hr hm => ⟨by zunwf; omega,
      by zunwf; omega,
      fun a ha => by_grind⟩)
    ztjvf
    (fun i d hi hJd hwd hri => by
      obtain ⟨d', k, ex, hk, F, a, b⟩ := flBody_exec (P := P) hwd hJd.1 hri hJd.2.1 by_omega
      have e : flφ d.nmem FL i = flφ c.nmem FL i := by
        unfold flφ; grind
      grind)
    e₁.wb_right ⟨by_simp_all,
      by simp_all, fun a _ => by zvmxn⟩
    by_simp_all
    by_simp_all a100 a101 a102
    by_omega by_omega
  simp only [Nat.add_zero, Nat.zero_add] at cnt pairs mem
  refine ⟨c', _, .seq e₁ ex, by_omega, fun r hr h9 => ?_, fun r hr => by_grind,
    fun a ha => by_grind, by_grind, by_grind, ?_, ?_, cnt, pairs⟩
  · rw [r' r (by unfold BFl; grind) by_omega by_omega
      by_omega, K₁ r by_omega by_omega h9 by_omega]
  · rw [r' _ by_decide by_decide by_decide by_decide, a99]
  · rw [r' _ by_decide by_decide by_decide by_decide, a100]

/-- **The facts of the list of `D*`.** -/
theorem dl_facts (m : ℕ → ℕ) (FL μ : ℕ) :
    (∀ i, i < (emitted ztfrf μ).length →
      ((emitted ztfrf μ).getD i ztdr).1 < μ ∧
        m (FL + ((emitted ztfrf μ).getD i ztdr).1) = 1) ∧
    (∀ v, v < μ → m ztcen = 1 → ∃ i, i < (emitted ztfrf μ).length ∧
      ((emitted ztfrf μ).getD i ztdr).1 = v) ∧
    (emitted ztfrf μ).length = ((Finset.range μ).filter fun v => m ztcen = 1).card := by
  set L := emitted _ μ with hL
  have hφ : ∀ j x, flφ m FL j = some x → x = (j, j) ∧ m (FL + j) = 1 := fun j x h => by
    unfold flφ at h; simp_all
  refine ⟨fun i hi => ?_, fun v hv hf => ?_, ?_⟩
  · obtain ⟨j, hj, e⟩ := mem_emitted.1 ztdoo
    grind
  · have : ztoji ∈ L := mem_emitted.2 ⟨v, hv, by unfold flφ; grind⟩
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem this
    exact ⟨i, hi, by_grind⟩
  · have hnd : L.Nodup := emitted_nodup (fun i x h => by_grind) μ
    zukzf
    rw [show L.toFinset = ((Finset.range μ).filter fun v => m ztcen = 1).image (fun v => ztoji)
      by
        zumx
        simp only [List.mem_toFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
        constructor
        · zuetb
          obtain ⟨j, hj, e⟩ := mem_emitted.1 hx
          grind
        · rintro ⟨j, ⟨hj, h'⟩, rfl⟩
          exact mem_emitted.2 ⟨j, hj, by unfold flφ; grind⟩]
    exact Finset.card_image_of_injective _ (fun a b h => by_grind)

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
  dl : ∀ i, i < nD → m ztnkm < μ ∧ m (FL + m ztnkm) = 1
  dl_all : ∀ v, v < μ → m ztcen = 1 → ∃ i, i < nD ∧ m ztnkm = v
  nD_eq : nD = ((Finset.range μ).filter fun v => m ztcen = 1).card
  ord_lt : ∀ i, i < μ → m ztdfw < μ
  ord_inj : ∀ i j, i < μ → j < μ → m ztdfw = m ztnno → i = j
  ord_rk : ∀ u, u < μ → m zttbs < μ ∧ m (ORD + m zttbs) = u
  ord_sorted : ∀ i j, i ≤ j → j < μ → m (LAB + m ztdfw) ≤ m (LAB + m ztnno)

/-- The facts survive memories agreeing below a bound above all the arrays. -/
theorem OrdFacts.mono {m m' : ℕ → ℕ} {μ FL LAB DL nD ORD RK X : ℕ}
    (h : OrdFacts m μ FL LAB DL nD ORD RK) (hX : ∀ a, a < X → m' a = m a)
    (hFL : FL + μ ≤ X) (hLAB : LAB + μ ≤ X) (hDL : DL + nD ≤ X) (hORD : ORD + μ ≤ X)
    (hRK : RK + μ ≤ X) : OrdFacts m' μ FL LAB DL nD ORD RK where
  dl i hi := by
    rw [hX _ by_omega]; obtain ⟨a, b⟩ := h.dl i hi; grind
  dl_all v hv hf := by
    rw [hX _ by_omega] at hf
    obtain ⟨i, hi, e⟩ := h.dl_all v hv hf
    grind
  nD_eq := by
    rw [h.nD_eq]; congr 1; grind
  ord_lt i hi := by rw [hX _ by_omega]; exact h.ord_lt i hi
  ord_inj i j hi hj e := by
    rw [hX _ by_omega, hX _ by_omega] at e; exact h.ord_inj i j hi hj e
  ord_rk u hu := by
    obtain ⟨a, b⟩ := h.ord_rk u hu
    grind
  ord_sorted i j hij hj := by
    have a := h.ord_lt i by_omega
    have b := h.ord_lt j hj
    rw [hX ztdfw by_omega, hX ztnno by_omega, hX _ by_omega, hX _ by_omega]
    exact h.ord_sorted i j hij hj
theorem rkBody_exec (hw : WordsBounded W c) {ORD RK i : ℕ}
    (h7 : c.nreg 60007 = ORD) (h10 : c.nreg 60110 = RK) (hi : c.nreg 60112 = i)
    (hb1 : ORD + i ≤ W) (hb2 : RK + c.nmem ztdfw ≤ W) :
    ∃ c' k, Exec P W rkBody c c' k ∧ k ≤ 4 ∧
      FrameB ztzfm c c' ∧
      c'.nreg 60113 = RK + c.nmem ztdfw ∧ c'.nreg 60114 = i := by
  have hwr : wr ztzfm rkBody = true := by_decide
  suffices H : ∃ c' k, Exec P W rkBody c c' k ∧ k ≤ 4 ∧
      c'.nreg 60113 = RK + c.nmem _ ∧ c'.nreg 60114 = i by
    zumr

  unfold rkBody
  exec_block
  · omega
  · simp_all
  simp_all
theorem rkS_exec (hw : WordsBounded W c) {μ ORD A : ℕ}
    (h7 : c.nreg 60007 = ORD) (hμ : c.nreg 60034 = μ) (h1 : c.nreg 120011 = 1)
    (hAl : c.nreg 9999 = A) (hOA : ORD + μ ≤ A) (hW : A + μ ≤ W)
    (hlt : ∀ t, t < μ → c.nmem zttbg < μ) :
    ∃ c' k, Exec P W rkS c c' k ∧ k ≤ μ * 8 + 5 ∧
      (∀ r, ztofv → r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      (∀ r, ztofv → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 60110 = A ∧ c'.nreg 9999 = A + μ ∧
      c'.nmem = scat c.nmem ztyqn ztfrq μ := by
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, rr₁, a10, a99⟩ := allocS_exec (P := P) hw (rb := 60110) (rn := 60034)
    (A := A) (n := μ) by_decide hAl hμ by_decide hW
  have hm₁ := F₁.2.2.1
  obtain ⟨c', k, ex, hk, r', rr', mm, rm, o, -, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 60112) (rn := 60034) (r1 := 120011) (ra := 60113) (rv := 60114) (body := rkBody)
    (B := fun r => decide ztevd) by_decide by_decide
    by_decide by_decide by_decide
    (fun d => d.nreg 60007 = ORD ∧ d.nreg 60110 = A ∧ ∀ a, a < A → d.nmem a = c.nmem a) A
    (fun d d' hJ hr hm => ⟨by_simp_all,
      by simp_all,
      fun a ha => by_simp_all⟩)
    (n := μ) (κ := 4) ztyqn ztfrq ztbeo
    (fun i d hi hJd hwd hri => by
      have e : d.nmem _ = c.nmem ztdfw := hJd.2.2 _ by_omega
      obtain ⟨d', k, ex, hk, F, v1, v2⟩ := rkBody_exec (P := P) hwd hJd.1 hJd.2.1 hri by_omega
        by_grind
      grind)
    e₁.wb_right ⟨by rw [F₁.1 _ by_decide, h7], a10, fun a _ => by rw [hm₁]⟩
    (by zunzr) (by zunzq) by_omega
  refine ⟨c', _, .seq e₁ ex, by_nlinarith, fun r hr h9 => ?_, ?_, by rw [rm, F₁.2.2.2.1],
    by rw [o, F₁.2.2.2.2], by_simp_all,
    by simp_all, by_simp_all⟩
  · rw [r' r by_grind by_omega,
      F₁.1 r by_grind]
  grind

/-- The band-`6` registers kept by `ordStage`. -/
def OKeep (r : ℕ) : Prop :=
  r < 60004 ∨ ztnhr ∨ (60021 ≤ r ∧ r ≤ 60099) ∨ 60115 ≤ r
set_option maxHeartbeats 4000000 in
theorem ordStage_exec (hw : WordsBounded W c)
    {μ FL LAB A₀ : ℕ} (hμ : c.nreg 60034 = μ) (hFL : c.nreg 130004 = FL)
    (hLAB : c.nreg 130005 = LAB) (h1 : c.nreg 120011 = 1) (hAl : c.nreg ALLOC = A₀)
    (hFA : FL + μ ≤ A₀) (hLA : LAB + μ ≤ A₀)
    (hroom : A₀ + 4 * μ + SortR.sortCost 20 μ ≤ W) :
    ∃ c' k, Exec P W ordStage c c' k ∧ k ≤ 40 * μ + SortR.sortCost 20 μ + 40 ∧
      FrameN dBands c c' ∧ A₀ ≤ c'.nreg ALLOC ∧
      c'.nreg ALLOC ≤ A₀ + 4 * μ + SortR.sortCost 20 μ ∧
      (∀ r, bandOf r = 6 → OKeep r → c'.nreg r = c.nreg r) ∧
      ztpt ∧
      c'.nreg 60100 + c'.nreg 60102 ≤ c'.nreg ALLOC ∧ c'.nreg 60007 + μ ≤ c'.nreg ALLOC ∧
      c'.nreg 60110 + μ ≤ c'.nreg ALLOC ∧
      OrdFacts c'.nmem μ FL LAB (c'.nreg 60100) (c'.nreg 60102) (c'.nreg 60007) (c'.nreg 60110) := by
  zuhp
  have hAl' := hAl
  -- 1. the list of `D*`
  obtain ⟨c₁, k₁, e₁, hk₁, r₁, rr₁, mem₁, rm₁, o₁, a99, a100, cnt, pairs⟩ :=
    dlS_exec (P := P) hw hμ hFL h1 hAl' hFA by_omega
  set L := emitted ztjvf μ with hL
  have hLlen : L.length ≤ μ := emitted_length_le _ _
  -- 2. the inputs of the sort
  have b130005 : c₁.nreg 130005 = LAB := by_simp_all
  have b60034 : c₁.nreg 60034 = μ := by_simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, w4, w5, w6⟩ : ∃ c₂ k₂, Exec P W ordPrep c₁ c₂ k₂ ∧ k₂ = 3 ∧
      FrameB ztzfk c₁ c₂ ∧ c₂.nreg 60004 = LAB ∧
      c₂.nreg 60005 = LAB ∧ c₂.nreg 60006 = μ := by
    have hwr : wr ztzfk ordPrep = true := by_decide
    suffices H : ∃ c₂ k₂, Exec P W ordPrep c₁ c₂ k₂ ∧ k₂ = 3 ∧ c₂.nreg 60004 = LAB ∧
        c₂.nreg 60005 = LAB ∧ c₂.nreg 60006 = μ by
      obtain ⟨c₂, k₂, ex, hk, a, b, d⟩ := H
      exact ⟨c₂, k₂, ex, hk, exec_frameB ex hwr, a, b, d⟩
    zud
    unfold ordPrep
    exec_block
    simp_all
  have hm₂ := F₂.2.2.1
  have c99 : c₂.nreg 9999 = A₀ + 2 * μ := by rw [F₂.1 _ by_decide, a99]
  have c1 : zthoq := by rw [F₂.1 _ by_decide, r₁ _ by_omega by_omega, h1]
  -- 3. the sort
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, al3a, al3b, R₃, sb₁, sb₂, hsort, hsurj, hlt⟩ :=
    sortCore_exec (P := P) e₂.wb_right (Z1 := LAB) (Z2 := LAB) (n := μ) (A₀ := A₀ + 2 * μ)
      w4 w5 w6 c1 c99 by_omega by_omega by_omega
  zvnek at al3a al3b
  set ORD := c₃.nreg 60007 with hORD
  set A₃ := c₃.nreg 9999 with hA₃
  have mem₃ : ∀ a, a < A₀ + 2 * μ → c₃.nmem a = c₁.nmem a := fun a ha => by
    rw [F₃.2.2.1 a by_grind, hm₂]
  -- 4. the ranks
  have d34 : c₃.nreg 60034 = μ := by
    rw [R₃ _ by_rfl by_decide by_decide by_decide by_decide,
      F₂.1 _ by_decide, b60034]
  have d1 : zthos := by
    rw [F₃.1 _ by_decide by_decide, c1]
  obtain ⟨c₄, k₄, e₄, hk₄, r₄, rr₄, rm₄, o₄, v110, v99, mm₄⟩ := rkS_exec (P := P) e₃.wb_right
    (ORD := ORD) (A := A₃) rfl d34 d1 rfl sb₂ by_omega hlt
  have below₄ : ∀ a, a < A₃ → c₄.nmem a = c₃.nmem a := fun a ha => by
    rw [mm₄, scat_below by_grind ha]
  have ex : Exec P W ordStage c c₄ _ := .seq e₁ ztcb
  have K6 : ∀ r, bandOf r = 6 → OKeep r → c₄.nreg r = c.nreg r := fun r hr hk => by
    unfold OKeep at hk; unfold bandOf at hr
    rw [r₄ r by_omega by_omega, R₃ r ztdmk by_omega by_omega by_omega
      by_omega, F₂.1 r by_grind,
      r₁ r by_omega by_omega]
  have g100 : c₄.nreg 60100 = A₀ := by
    rw [r₄ _ by_omega by_omega, R₃ _ by_rfl by_decide by_decide
      by_decide by_decide, F₂.1 _ by_decide, a100]
  have g102 : c₄.nreg 60102 = L.length := by
    rw [r₄ _ by_omega by_omega, R₃ _ by_rfl by_decide by_decide
      by_decide by_decide, F₂.1 _ by_decide, cnt]
  have g7 : c₄.nreg 60007 = ORD := by_grind
  have mem : ztced := fun a ha => by
    rw [below₄ a by_omega, mem₃ a by_omega, mem₁ a ha]
  have hDL : ∀ i, i < L.length → c₄.nmem (A₀ + i) = (L.getD i ztdr).1 := fun i hi => by
    rw [below₄ _ by_omega, mem₃ _ by_omega]; exact (pairs i hi).1
  have hORDm : ∀ t, t < μ → c₄.nmem _ = c₃.nmem zttbg := fun t ht =>
    below₄ _ by_omega
  obtain ⟨D1, D2, D3⟩ := dl_facts c.nmem FL μ
  refine ⟨c₄, _, ex, ?_, ?_, ?_, ?_, K6, mem, ?_, ?_, ?_, ?_⟩
  · omega
  · -- the frame
    have B6 : ∀ r, (decide ztlgf || decide ztyc) = true →
        bandOf r ∈ dBands ∨ r = ALLOC := fun r hr => by
      zufw
      zubuj
      · zugoq
      omega
    have FA : FrameN dBands c c₂ := PF.frameN
      ⟨fun r hr => by
        have := b6_ne hr
        rw [F₂.1 r by_grind, r₁ r by_omega this.1],
      fun r hr => by
        have := b6_ne hr
        rw [F₂.2.1 r by_grind,
          rr₁ r (by unfold BFl; zvnan; omega)],
      fun a ha => by_grind,
      fun a _ => by rw [F₂.2.2.2.1, rm₁], by rw [F₂.2.2.2.2, o₁]⟩ B6
      (by rw [hAL, F₂.2.1 _ by_decide, rr₁ _ by_decide])
    have FC : FrameN dBands c₃ c₄ := PF.frameN
      ⟨fun r hr => by
        have := b6_ne hr
        grind,
      fun r hr => by
        have := b6_ne hr
        grind,
      fun a ha => by_grind,
      by grind, by rw [o₄]⟩ B6 by_grind
    exact (FA.trans F₃ by_grind).trans FC
      by_grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · rw [g100, g102, g7, v110]
    have hFLm : ∀ v, v < μ → c₄.nmem _ = c.nmem ztcen := fun v hv => mem _ by_omega
    have hinj : ∀ t t', t < μ → t' < μ → c₃.nmem _ = c₃.nmem _ → t = t' :=
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
          zuiou

          · rintro ⟨hv, e⟩; exact ⟨hv, by rw [hFLm v hv]; exact e⟩
          · rintro ⟨hv, e⟩; exact ⟨hv, by rw [← hFLm v hv]; exact e⟩
        ord_lt := fun i hi => by rw [hORDm i hi]; grind
        ord_inj := fun i j hi hj e => by
          rw [hORDm i hi, hORDm j hj] at e; exact hinj i j hi hj e
        ord_rk := fun u hu => by
          obtain ⟨t, ht, e⟩ := hsurj u hu
          have : c₄.nmem (A₃ + u) = t := by
            rw [mm₄, ← e]
            exact scat_at ht
              fun j hj htj e' => by
                try simp only at e'
                have := hinj j t hj ht by_omega
                omega
          rw [this, hORDm t ht]; omega
        ord_sorted := fun i j hij hj => by
          have hs := hsort i j hij hj
          have ai := hlt i by_omega
          have aj := hlt j hj
          rw [hORDm i by_omega, hORDm j hj, below₄ _ by_omega,
            below₄ _ by_omega]
          simp only at hs
          rw [F₃.2.2.1 _ by_grind,
            F₃.2.2.1 (LAB + c₃.nmem _) by_grind]
          unfold PLe at hs; omega }
end
end OracleR
end Chazelle.Core
section
set_option hygiene false
local macro "zqbjv" : tactic => `(tactic| (have hq₁ := hq.frame F₁ by_grind
                                           obtain ⟨c₂, k₂, e₂, hk₂, F₂, x1, x2⟩ := xpS_exec (P := P) hW hv c₁ e₁.wb_right hq₁
                                           rw [a0] at x1 x2; rw [a1] at x2))
local macro "zqbjw" : tactic => `(tactic| (obtain ⟨c', k, ex, hk, a, b⟩ := H
                                           exact ztbjz))
local macro "zqbjx" : tactic => `(tactic| (obtain ⟨c₁, k₁, ex, hk, a, b⟩ := H
                                           exact ⟨c₁, k₁, ex, hk, exec_frameB ex hwr, a, b⟩))
local macro "zqbjy" : tactic => `(tactic| (obtain ⟨c', k, ex, hk, v⟩ := H
                                           exact ⟨c', k, ex, hk, exec_frameB ex hwr, v⟩))
local macro "zqbjz" : tactic => `(tactic| exact ⟨_, k', ex', by_omega, fun _ => by config_simp, by_grind⟩)
set_option hygiene true

/-!
# Lemma 3.6 (WP-H), preprocessing part 26: the comparator of the chord table

`chCmp` compares two chord records `a`, `b` (registers `30000`, `30001`) by `ChLe`: height
vertex, then the class of the left end, then (class `1`) the abscissa of the left end, by the sign
kernel.  Records `≥ K` come after, in their natural order (`chLeB`).  The chord area and `K` are in
`116000`, `116001`; the constants of the query (`120010 … 120049`) are those of a configuration
`c₀`, read through the values `qvOf c₀`.  Main result: `chCmp_ok` (the comparator contract).
-/
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
section Order
variable (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ)
theorem chLe_total (a b : ℕ) : ChLe P C V m a b ∨ ChLe P C V m b a := by
  unfold ChLe
  grind
theorem chLe_trans {a b d : ℕ} (h1 : ChLe P C V m a b) (h2 : ChLe P C V m b d) :
    ChLe P C V m a d := by
  unfold ChLe at *
  grind
open Classical in
/-- **The comparison of the sort**: records below `K` by `ChLe`, then the others. -/
noncomputable def chLeB (K a b : ℕ) : Bool :=
  if a < K then (if b < K then decide (ChLe P C V m a b) else true)
  else ztdva
theorem chLeB_total (K a b : ℕ) : (chLeB P C V m K a b || chLeB P C V m K b a) = true := by
  unfold chLeB
  have := chLe_total P C V m a b
  grind
theorem chLeB_trans (K a b d : ℕ) (h1 : chLeB P C V m K a b = true)
    (h2 : chLeB P C V m K b d = true) : chLeB P C V m K a d = true := by
  unfold chLeB at *
  split_ifs at h1 h2 ⊢ <;> zvmwo at h1 h2 ⊢ <;>
    first | omega | exact chLe_trans P C V m h1 h2
end Order

/-! ## The values read from the constant registers -/

/-- The values of the query read from the constant registers of `c`. -/
def qvOf (c : Config) : QV where
  D := c.nreg 120013
  NB := c.nreg 120014
  s := c.nreg 120015
  m := c.nreg 120016
  tIdx := c.nreg 120017
  β := c.nreg 120018
  sS := c.nreg 120021
  tv := c.nreg 120022
  hz := c.nreg 120023
  σb := c.nreg 120024
  zo := none
  A := c.nreg 120030
  POS := c.nreg 120031
  FL := c.nreg 120032
  LAB := c.nreg 120033
  DL := c.nreg 120034
  nD := c.nreg 120035
  ORD := c.nreg 120036
  RK := c.nreg 120037
  CH := c.nreg 120038
  K := c.nreg 120039
  MD := c.nreg 120040
  TB := c.nreg 120041
  L := c.nreg 120042
  CB := c.nreg 120043
  AB := c.nreg 120044
  RB := c.nreg 120045
  SB := c.nreg 120046
  LB := c.nreg 120047
  μ := c.nreg 120049

/-- The constant registers of `c` are those of the query for `qvOf c`, when they are consistent. -/
theorem qconst_qvOf {P : Polygon} {c : Config} (hn : c.nreg 120010 = P.n) (h1 : c.nreg 120011 = 1)
    (h0 : c.nreg 120012 = 0) (h2 : c.nreg 120048 = 2) (h6 : c.nreg 120028 = 6)
    (hm2 : c.nreg 120019 = 2 * c.nreg 120016) (hnW : c.nreg 120020 = 2 * c.nreg 120016 + 7)
    (hE : c.nreg 120029 = 2 * c.nreg 120016 + 6) (h25 : c.nreg 120025 = 2) :
    QConst P ztmne c :=
  ⟨hn, h1, h0, rfl, rfl, rfl, rfl, rfl, rfl, hm2, hnW, rfl, rfl, rfl, rfl,
    Or.inl ⟨h25, rfl⟩, h6, hE, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, h2, rfl⟩

/-- The record address `CB + 5 x` and the height of the record `x` (in `30000`). -/
def chRecA : Stmt :=
  block [.addN 116012 30000 30000, .addN 116012 116012 116012, .addN 116012 116012 30000, .addN 116012 116012 116000,
    .loadN 116010 116012]
theorem chRecA_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {CB x : ℕ}
    (h0 : c.nreg 116000 = CB) (hx : c.nreg 30000 = x) (hb : CB + 5 * x ≤ W) :
    ∃ c' k, Exec P W chRecA c c' k ∧ k = 5 ∧
      FrameB ztikc c c' ∧ c'.nreg 116012 = CB + 5 * x ∧
      c'.nreg 116010 = c.nmem ztpwq := by
  have hwr : wr ztikc chRecA = true := by_decide
  suffices H : ∃ c' k, Exec P W chRecA c c' k ∧ k = 5 ∧ c'.nreg 116012 = CB + 5 * x ∧
      c'.nreg 116010 = c.nmem _ by
    zqbjw
  unfold chRecA
  exec_block
  · omega
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · exact ⟨rfl, by config_simp; omega, by config_simp; grind⟩

/-- The record address `CB + 5 x` and the height of the record `x` (in `30001`). -/
def chRecB : Stmt :=
  block [.addN 116013 30001 30001, .addN 116013 116013 116013, .addN 116013 116013 30001, .addN 116013 116013 116000,
    .loadN 116011 116013]
theorem chRecB_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {CB x : ℕ}
    (h0 : c.nreg 116000 = CB) (hx : c.nreg 30001 = x) (hb : CB + 5 * x ≤ W) :
    ∃ c' k, Exec P W chRecB c c' k ∧ k = 5 ∧
      FrameB ztikd c c' ∧ c'.nreg 116013 = CB + 5 * x ∧
      c'.nreg 116011 = c.nmem ztpwq := by
  have hwr : wr ztikd chRecB = true := by_decide
  suffices H : ∃ c' k, Exec P W chRecB c c' k ∧ k = 5 ∧ c'.nreg 116013 = CB + 5 * x ∧
      c'.nreg 116011 = c.nmem _ by
    zqbjw
  unfold chRecB
  exec_block
  · omega
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · exact ⟨rfl, by config_simp; omega, by config_simp; grind⟩

/-- The walk edge of the left end of the record at `116012`. -/
def chWA : Stmt := block [.addN 116014 116012 120011, .loadN 116014 116014]
theorem chWA_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {a : ℕ}
    (ht : c.nreg 116012 = a) (h1 : c.nreg 120011 = 1) (hb : a + 1 ≤ W) :
    ∃ c' k, Exec P W chWA c c' k ∧ k = 2 ∧ FrameB ztlom c c' ∧
      c'.nreg 116014 = c.nmem ztdf := by
  have hwr : wr ztlom chWA = true := by_decide
  suffices H : ∃ c' k, Exec P W chWA c c' k ∧ k = 2 ∧ c'.nreg 116014 = c.nmem _ by
    zqbjy
  unfold chWA
  exec_block
  · omega
  simp_all

/-- The walk edge of the left end of the record at `116013`. -/
def chWB : Stmt := block [.addN 116015 116013 120011, .loadN 116015 116015]
theorem chWB_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {a : ℕ}
    (ht : c.nreg 116013 = a) (h1 : c.nreg 120011 = 1) (hb : a + 1 ≤ W) :
    ∃ c' k, Exec P W chWB c c' k ∧ k = 2 ∧ FrameB ztlon c c' ∧
      c'.nreg 116015 = c.nmem ztdf := by
  have hwr : wr ztlon chWB = true := by_decide
  suffices H : ∃ c' k, Exec P W chWB c c' k ∧ k = 2 ∧ c'.nreg 116015 = c.nmem _ by
    zqbjy
  unfold chWB
  exec_block
  · omega
  simp_all

/-- The class and the symbolic point of the left end of `a`, saved in `116016 … 116019`. -/
def xpA : Stmt :=
  .seq ztfbk
    (.seq xpS (block [.copyN 116016 120122, .copyN 116017 120123, .copyN 116018 120124,
      .copyN 116019 120125]))

/-- The class and the symbolic point of the left end of `b` (in `120122 …`). -/
def xpB : Stmt := .seq ztfbl xpS

/-- The registers written by the comparator (besides the kernel's and `30002`). -/
def BCh (r : ℕ) : Bool := decide (116010 ≤ r ∧ r ≤ 116019) || decide ztgxp
theorem xpA_exec {P : Polygon} {W : ℕ} (hW : 4 * P.n + 8 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) {c : Config} (hw : WordsBounded W c) (hq : QConst P V c) :
    ∃ c' k, Exec P W xpA c c' k ∧ k ≤ 46 ∧
      FrameB (fun r => decide ztgxl || decide ztgxp) c c' ∧
      c'.nreg 116016 = xpClass ztqhk ∧
      (xpClass ztqhk = 1 →
        SymPtIn c' 116017 (xpSym C V P.n ztqhk (c.nreg 116010))) := by
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, a0, a1⟩ : ∃ c₁ k₁, Exec P W
      ztfbk c c₁ k₁ ∧ k₁ = 2 ∧
      FrameB ztcia c c₁ ∧
      c₁.nreg 120120 = c.nreg 116014 ∧ c₁.nreg 120121 = c.nreg 116010 := by
    have hwr : wr ztcia
      ztfbk = true := by_decide
    suffices H : ∃ c₁ k₁, Exec P W _ c c₁ k₁ ∧
        k₁ = 2 ∧ c₁.nreg 120120 = c.nreg 116014 ∧ c₁.nreg 120121 = c.nreg 116010 by
      zqbjx
    exec_block
    simp
  zqbjv
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, y6, y7, y8, y9⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN 116016 120122, .copyN 116017 120123, .copyN 116018 120124,
        .copyN 116019 120125]) c₂ c₃ k₃ ∧ k₃ = 4 ∧
      FrameB ztzfn c₂ c₃ ∧
      c₃.nreg 116016 = c₂.nreg 120122 ∧ c₃.nreg 116017 = c₂.nreg 120123 ∧
      c₃.nreg 116018 = c₂.nreg 120124 ∧ c₃.nreg 116019 = c₂.nreg 120125 := by
    have hwr : wr ztzfn (block [.copyN 116016 120122,
      .copyN 116017 120123, .copyN 116018 120124, .copyN 116019 120125]) = true := by_decide
    suffices H : ∃ c₃ k₃, Exec P W _ c₂ c₃ k₃ ∧ k₃ = 4 ∧
        c₃.nreg 116016 = c₂.nreg 120122 ∧ c₃.nreg 116017 = c₂.nreg 120123 ∧
        c₃.nreg 116018 = c₂.nreg 120124 ∧ c₃.nreg 116019 = c₂.nreg 120125 by
      obtain ⟨c₃, k₃, ex, hk, a, b, d, e⟩ := H
      exact ⟨c₃, k₃, ex, hk, exec_frameB ex hwr, a, b, d, e⟩
    zue
    exec_block
    simp
  refine ⟨c₃, _, .seq e₁ ztcr, by_omega, ?_, by_omega, fun h => ?_⟩
  · refine ((FrameB.mono F₁ fun r hr => ?_).trans ztnla).trans
      (FrameB.mono F₃ fun r hr => ?_)
    · grind
    · simp only [BX, decide_eq_true_eq] at hr; grind
    simp_all
  · have hs := x2 h
    unfold xpSym at hs ⊢
    split_ifs at hs ⊢
    · exact ⟨by zuozt; exact hs.1, by zuozu; exact hs.2.1, by rw [y9]; exact hs.2.2⟩
    · exact ⟨by zuozt; exact hs.1, by zuozu; exact hs.2⟩
theorem xpB_exec {P : Polygon} {W : ℕ} (hW : 4 * P.n + 8 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) {c : Config} (hw : WordsBounded W c) (hq : QConst P V c) :
    ∃ c' k, Exec P W xpB c c' k ∧ k ≤ 42 ∧
      FrameB (fun r => decide ztgxp) c c' ∧
      c'.nreg 120122 = xpClass ztqhl ∧
      (xpClass ztqhl = 1 →
        SymPtIn c' 120123 (xpSym C V P.n ztqhl (c.nreg 116011))) := by
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, a0, a1⟩ : ∃ c₁ k₁, Exec P W
      ztfbl c c₁ k₁ ∧ k₁ = 2 ∧
      FrameB ztcia c c₁ ∧
      c₁.nreg 120120 = c.nreg 116015 ∧ c₁.nreg 120121 = c.nreg 116011 := by
    have hwr : wr ztcia
      ztfbl = true := by_decide
    suffices H : ∃ c₁ k₁, Exec P W _ c c₁ k₁ ∧
        k₁ = 2 ∧ c₁.nreg 120120 = c.nreg 116015 ∧ c₁.nreg 120121 = c.nreg 116011 by
      zqbjx
    exec_block
    simp
  zqbjv
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, ?_, x1, x2⟩
  refine (FrameB.mono F₁ fun r hr => ?_).trans ztnla
  · grind
  · simp only [BX, decide_eq_true_eq] at hr ⊢; omega

/-! ## The comparator -/

/-- The decision on equal heights: by the classes, then by the abscissas (sign kernel). -/
def chDec : Stmt :=
  .ifLtN 116016 120122 ztjo
    (.ifLtN 120122 116016 ztlr
      (.ifLtN 116016 120011 ztjo
        (.ifLtN 120011 116016 ztjo
          (.seq (sgnS 0 ztdyb ztmab ztmab)
            (.instr (.subN 30002 120011 10010))))))

/-- Equal heights. -/
def chTie : Stmt := .seq chWA (.seq chWB (.seq xpA (.seq xpB chDec)))

/-- Two records. -/
def chBoth : Stmt :=
  .seq chRecA (.seq chRecB (.ifLtN 116010 116011 ztjo
    (.ifLtN 116011 116010 ztlr chTie)))

/-- **The comparator of the chord table.** -/
def chCmp : Stmt :=
  .ifLtN 30000 116001 (.ifLtN 30001 116001 chBoth ztjo)
    (.ifLtN 30001 116001 ztlr
      ztxft)

/-- The registers written by the comparator. -/
def BCmp (r : ℕ) : Bool := decide ztkdj || BCh r || Bk r
theorem wr_chCmp : wr BCmp chCmp = true := by_decide
theorem wrR_chCmp : wrR Bk chCmp = true := by_decide

/-- The invariant of the comparator. -/
def ChCJ (c₀ : Config) (m₀ : ℕ → ℕ) (A₀ K : ℕ) (c : Config) : Prop :=
  c.nreg 116000 = (qvOf c₀).CB ∧ c.nreg 116001 = K ∧
    (∀ r, 120010 ≤ r → r ≤ 120049 → c.nreg r = c₀.nreg r) ∧ ∀ a, a < A₀ → c.nmem a = m₀ a
theorem chCJ_stable (c₀ : Config) (m₀ : ℕ → ℕ) (A₀ K : ℕ) :
    SortR.JStable ztpws A₀ := by
  intro c c' ⟨h0, h1, h2, h3⟩ hr _ hm _ _
  have hb : ∀ r, (116000 ≤ r ∧ r < 130000) → c'.nreg r = c.nreg r := fun r h =>
    hr r ztfgf ztu
  exact ⟨by_simp_all, by_simp_all,
    fun r a b => by_grind, by_simp_all⟩
set_option maxHeartbeats 8000000 in
theorem chBoth_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {c₀ : Config} {m₀ : ℕ → ℕ} {A₀ K : ℕ} (hv : QVOK P C ztglk)
    (hq : QConst P ztglk c₀) (hrec : ∀ i, i < K → (qvOf c₀).CB + 5 * i + 2 ≤ A₀)
    (hAW : A₀ ≤ W)
    (hh : ∀ i, i < K → m₀ ztlcy < P.n) (htv : (qvOf c₀).tv < P.n)
    (hn : 0 < P.n) {c : Config} (hw : WordsBounded W c) (hJ : ChCJ c₀ m₀ A₀ K c)
    (hA : c.nreg 30000 < K) (hB : c.nreg 30001 < K) :
    ∃ c' k, Exec P W chBoth c c' k ∧ k ≤ 480 ∧
      (ChLe P C ztglk m₀ ztjry ztjrz → c'.nreg 30002 = 1) ∧
      (¬ ChLe P C ztglk m₀ ztjry ztjrz → c'.nreg 30002 = 0) := by
  zufke
  have hra := hrec _ hA
  have hrb := hrec _ hB
  zufpc

  zudk
  have hW4 : 4 * P.n + 8 ≤ W := by_omega
  zuenb

  -- the heights
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, t12, h10⟩ := chRecA_exec (P := P) (CB := V.CB) (x := a) hw j0 rfl
    by_omega
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, t13, h11⟩ := chRecB_exec (P := P) (CB := V.CB) (x := b) e₁.wb_right
    (by rw [F₁.1 _ by_decide]; exact j0) ztnsw by_omega
  have hHa : c₂.nreg 116010 = chH m₀ V a := by
    rw [F₂.1 _ by_decide, h10, j3 _ by_omega]; rfl
  have hHb : c₂.nreg 116011 = chH m₀ V b := by
    rw [h11, F₁.2.2.1, j3 _ by_omega]; rfl
  have t12' : c₂.nreg 116012 = V.CB + 5 * a := by rw [F₂.1 _ by_decide, t12]
  have hq₂ := (hq'.frame F₁ by_grind).frame F₂ by_grind
  zulko
  zue
  rcases lt_trichotomy ztrng (chH m₀ V b) with hlt | heq | hgt
  · refine ⟨_, _, .seq e₁ (.seq e₂ (.ifLtN_true by_omega
      (Exec.constN w₂ 30002 1 hW1))), by_omega, by_simp_all, fun hc => ?_⟩
    exact absurd (Or.inl hlt) hc
  · -- equal heights
    have nlt : ¬ c₂.nreg 116010 < c₂.nreg 116011 := by_omega
    obtain ⟨c₃, k₃, e₃, hk₃, F₃, w14⟩ := chWA_exec w₂ t12' hq₂.one by_omega
    obtain ⟨c₄, k₄, e₄, hk₄, F₄, w15⟩ := chWB_exec e₃.wb_right
      (by rw [F₃.1 _ by_decide, t13])
      (by rw [F₃.1 _ by_decide]; exact hq₂.one) by_omega
    have hLa : c₄.nreg 116014 = chL m₀ V a := by
      rw [F₄.1 _ by_decide, w14, hm₂, j3 _ by_omega]; rfl
    have hLb : c₄.nreg 116015 = chL m₀ V b := by
      rw [w15, F₃.2.2.1, hm₂, show V.CB + 5 * b + 1 = V.CB + 5 * b + 1 from rfl,
        j3 _ by_omega]; rfl
    have hq₄ := (hq₂.frame F₃ by_grind).frame F₄ by_grind
    have hHa4 : c₄.nreg 116010 = chH m₀ V a := by
      rw [F₄.1 _ by_decide, F₃.1 _ by_decide, hHa]
    have hHb4 : c₄.nreg 116011 = chH m₀ V b := by
      rw [F₄.1 _ by_decide, F₃.1 _ by_decide, hHb]
    obtain ⟨c₅, k₅, e₅, hk₅, F₅, x16, sA⟩ := xpA_exec hW4 hv e₄.wb_right hq₄
    rw [hLa] at x16 sA; rw [hHa4] at sA
    have hq₅ := hq₄.frame F₅ fun r h1 h2 => by
      grind
    have hLb5 : c₅.nreg 116015 = chL m₀ V b := by
      rw [F₅.1 _ by_decide, hLb]
    have hHb5 : c₅.nreg 116011 = chH m₀ V b := by
      rw [F₅.1 _ by_decide, hHb4]
    obtain ⟨c₆, k₆, e₆, hk₆, F₆, x22, sB⟩ := xpB_exec hW4 hv e₅.wb_right hq₅
    rw [hLb5] at x22 sB; rw [hHb5] at sB
    have hq₆ := hq₅.frame F₆ by_grind
    have x16' : c₆.nreg 116016 = xpClass ztdmz := by rw [F₆.1 _ by_decide, x16]
    have sA' : xpClass _ = 1 →
        SymPtIn c₆ 116017 (xpSym C V P.n ztdmz ztrng) := fun h => by
      have := sA h
      have g7 := F₆.1 116017 by_decide
      have g8 := F₆.1 116018 by_decide
      have g9 := F₆.1 116019 by_decide
      unfold SymPtIn at this ⊢
      grind
    zujb
    have one₆ := hq₆.one
    have nlt2 : ¬ c₂.nreg 116011 < c₂.nreg 116010 := by_omega
    have hTie : ∀ c' k, Exec P W chDec c₆ c' k →
        ∃ k', Exec P W chBoth c c' k' ∧ k' = k₁ + k₂ + k₃ + k₄ + k₅ + k₆ + k + 4 := by
      intro c' k ex
      exact ⟨_, .seq e₁ (.seq e₂ (.ifLtN_false nlt (.ifLtN_false nlt2
        (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ ex))))))), by_omega⟩
    have hcl := xpClass_cases ztdmz
    have hclb := xpClass_cases ztrnh
    rcases lt_trichotomy (xpClass ztdmz) (xpClass ztrnh) with g | g | g
    · obtain ⟨k', ex', hk'⟩ := hTie _ _ (.ifLtN_true by_omega
        ztjil)
      exact ⟨_, k', ex', by_omega, fun _ => by config_simp,
        (absurd (Or.inr ⟨heq, Or.inl g⟩))⟩
    · by_cases g1 : xpClass ztdmz = 1
      · -- the abscissas
        have la := xpSym_lt (C := C) (w := chL m₀ V a) hn htv (hh a hA)
        have lb := xpSym_lt (C := C) (w := chL m₀ V b) hn htv (hh b hB)
        obtain ⟨c₇, k₇, e₇, hk₇, F₇, hbit, hiff⟩ := sgnS_exec hG by_omega 0 by_norm_num
          ztdyb ztmab ztmab c₆ w₆ by_decide by_decide by_decide
          (sB by_omega) ztwda ztwda lb la la
        have e₈ := Exec.subN (P := P) e₇.wb_right 30002 120011 10010
        have one₇ : c₇.nreg 120011 = 1 := by rw [F₇.1 _ by_decide, one₆]
        obtain ⟨k', ex', hk'⟩ := hTie _ _ (.ifLtN_false by_omega
          (.ifLtN_false by_omega (.ifLtN_false by_omega
            (.ifLtN_false by_omega ztjdu))))
        refine ⟨_, k', ex', by_omega, ?_, ?_⟩
        · zuchg
          config_simp
          rw [one₇]
          have : ¬ c₇.nreg 10010 = 1 := by
            zuozv; simp only [SignTest, not_lt]
            rcases hc with hc | ⟨-, hc | ⟨-, hc⟩⟩
            · omega
            · omega
            · exact hc g1
          omega
        · zuchg
          config_simp
          rw [one₇]
          have : c₇.nreg 10010 = 1 := by
            zuozv; zvnhd
            by_contra hx
            exact hc (Or.inr ⟨heq, Or.inr ⟨g, fun _ => not_lt.1 hx⟩⟩)
          omega
      · -- the classes `0` and `2`
        have hc1 : xpClass ztdmz < 1 ∨ 1 < xpClass ztdmz := by_omega
        have hok : ChLe P C V m₀ a b := Or.inr by_omega
        rcases hc1 with hc1 | hc1
        · obtain ⟨k', ex', hk'⟩ := hTie _ _ (.ifLtN_false by_omega
            (.ifLtN_false by_omega (.ifLtN_true by_omega
              ztjil)))
          zqbjz
        · obtain ⟨k', ex', hk'⟩ := hTie _ _ (.ifLtN_false by_omega
            (.ifLtN_false by_omega (.ifLtN_false by_omega
              (.ifLtN_true by_omega ztjil))))
          zqbjz
    · obtain ⟨k', ex', hk'⟩ := hTie _ _ (.ifLtN_false by_omega
        (.ifLtN_true by_omega (Exec.constN w₆ 30002 0 ztbg)))
      refine ⟨_, k', ex', by_omega, fun hc => ?_, fun _ => by config_simp⟩
      exfalso
      rcases hc with hc | ⟨-, hc | ⟨hc, -⟩⟩ <;> omega
  · refine ⟨_, _, .seq e₁ (.seq e₂ (.ifLtN_false by_omega
      (.ifLtN_true by_omega (Exec.constN w₂ 30002 0 ztbg)))),
      by omega, fun hc => ?_, by_simp_all⟩
    exfalso
    rcases hc with hc | ⟨hc, -⟩ <;> omega
set_option maxHeartbeats 4000000 in
theorem chCmp_ok {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {c₀ : Config} {m₀ : ℕ → ℕ} {A₀ K : ℕ} (hv : QVOK P C ztglk)
    (hq : QConst P ztglk c₀) (hrec : ∀ i, i < K → (qvOf c₀).CB + 5 * i + 2 ≤ A₀)
    (hAW : A₀ ≤ W)
    (hh : ∀ i, i < K → m₀ ztlcy < P.n) (htv : (qvOf c₀).tv < P.n)
    (hn : 0 < P.n) :
    SortR.CmpOK P W chCmp {bSign, bOPrep, bOQuery} ztpws
      (chLeB P C ztglk m₀ K) 500 := by
  zumgl
  zufke
  have hBc : ∀ r, (bandOf r = 1 ∨ bandOf r = 11 ∨ bandOf r = 12) →
      bandOf r ∈ ({bSign, bOPrep, bOQuery} : Finset ℕ) := by
    intro r h; simp only [Finset.mem_insert, Finset.mem_singleton, bSign, bOPrep, bOQuery]; omega
  zufpc

  suffices H : ∃ c' k, Exec P W chCmp c c' k ∧ k ≤ 500 ∧
      c'.nreg 30002 = (if chLeB P C V m₀ K _ _ then 1 else 0) by
    obtain ⟨c', k, ex, hk, hbit⟩ := H
    have f := exec_frameB ex wr_chCmp
    have fr := WalkKey.exec_rframe ex wrR_chCmp
    refine ⟨c', k, ex, hk, ⟨?_, ?_, fun r a b => ?_, fun a ha => by zunkg; simp_all⟩,
      hbit, fun r h0 h1 h2 hb => f.1 r ?_, fun r hb => fr r ?_, f.2.2.1, f.2.2.2.1, f.2.2.2.2⟩
    · zuome; exact j0
    · zudjx
    · rw [f.1 r (by simp only [BCmp, BCh, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)]
      simp_all
    · zukr
      simp only [Bool.not_eq_false, BCmp, BCh, Bk, Bool.or_eq_true, decide_eq_true_eq] at hc
      zucor
      · exact hb ztzvz
      · zugik
    · zukr
      simp only [Bool.not_eq_false, Bk, decide_eq_true_eq] at hc
      exact hb ztzvz
  zudk
  zuenb

  unfold chCmp chLeB
  by_cases hA : a < K
  · rw [ite_eq_left hA]
    zujsw
    · zulpv
      obtain ⟨c', k, ex, hk, v1, v0⟩ := chBoth_exec hG hW hv hq hrec hAW hh htv hn hw
        ⟨j0, j1, j2, j3⟩ hA hB
      refine ⟨c', _, .ifLtN_true by_omega ztcrz,
        by omega, ?_⟩
      grind
    · zulqc
      exact ⟨_, _, .ifLtN_true by_omega (.ifLtN_false by_omega
        ztpxu), by_omega, by_simp⟩
  · rw [ite_eq_right hA]
    zujsw
    · zulpv
      exact ⟨_, _, .ifLtN_false by_omega (.ifLtN_true by_omega
        ztzbr), by_omega, by_simp⟩
    · zulqc
      zujta
      · exact ⟨_, _, .ifLtN_false by_omega (.ifLtN_false by_omega
          (.ifLtN_true hba ztzbr)), by_omega,
          by simp_all⟩
      · exact ⟨_, _, .ifLtN_false by_omega (.ifLtN_false by_omega
          (.ifLtN_false hba ztpxu)), by_omega,
          by simp_all⟩
end
end OracleR
end Chazelle.Core
end
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
theorem chLe_refl (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (a : ℕ) : ChLe P C V m a a :=
  Or.inr by_simp_all
variable {P : Polygon}
theorem chLe_congr {C : Chain} {V : QV} {m m' : ℕ → ℕ} {i j : ℕ}
    (h : ∀ x, x = i ∨ x = j → m ztqdc = m' ztqdc ∧
      m ztnqa = m' ztnqa) :
    ChLe P C V m i j ↔ ChLe P C V m' i j := by
  unfold ChLe chH chL
  simp_all

/-- **The chord table.** -/
def chSortS : Stmt :=
  .seq ztdlq
    (.seq itemS (.seq (.instr (.copyN 30004 60006))
      (.seq (SortR.sortStmt chCmp) (.instr (.copyN 60120 30005)))))

/-- The bands of the chord table. -/
def chBands : Finset ℕ := {bSort, bSign, bDecomp, bOPrep, bOQuery}
set_option maxHeartbeats 4000000 in
theorem chSort_exec {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {c : Config} (hw : WordsBounded W c) {A₀ : ℕ} (hv : QVOK P C ztmne)
    (hq : QConst P ztmne c) (hAl : c.nreg 9999 = A₀)
    (hrec : ∀ i, i < (qvOf c).K → (qvOf c).CB + 5 * i + 2 ≤ A₀)
    (hh : ∀ i, i < (qvOf c).K → c.nmem ((qvOf c).CB + 5 * i) < P.n)
    (htv : (qvOf c).tv < P.n) (hn : 0 < P.n)
    (hroom : A₀ + (qvOf c).K + SortR.sortCost 500 (qvOf c).K ≤ W) :
    ∃ c' k, Exec P W chSortS c c' k ∧ k ≤ 7 * (qvOf c).K + SortR.sortCost 500 (qvOf c).K + 20 ∧
      FrameN chBands c c' ∧ A₀ + (qvOf c).K ≤ c'.nreg ALLOC ∧
      c'.nreg ALLOC ≤ A₀ + (qvOf c).K + SortR.sortCost 500 (qvOf c).K ∧
      (∀ r, bandOf r = 6 → r ≠ 60006 → r ≠ 60016 → r ≠ 60017 → r ≠ 60020 → r ≠ 60120 →
        c'.nreg r = c.nreg r) ∧
      ztdbb ∧
      A₀ + (qvOf c).K ≤ c'.nreg 60120 ∧ c'.nreg 60120 + (qvOf c).K ≤ c'.nreg ALLOC ∧
      (∀ q, q < (qvOf c).K → c'.nmem ztlkh < (qvOf c).K) ∧
      (∀ q q', q < (qvOf c).K → q' < (qvOf c).K →
        c'.nmem ztlkh = c'.nmem ztrlh → q = q') ∧
      (∀ q q', q ≤ q' → q' < (qvOf c).K →
        ChLe P C ztmne c.nmem (c'.nmem ztlkh) (c'.nmem ztrlh)) := by
  zuhp
  set V := qvOf c with hV
  set K := V.K with hKdef
  have hK : c.nreg 120039 = K := rfl
  have hCB : c.nreg 120043 = V.CB := rfl
  -- 1. the inputs
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, a6, a0, a1⟩ : ∃ c₁ k₁, Exec P W
      ztdlq c c₁ k₁ ∧ k₁ = 3 ∧
      FrameB ztgjm c c₁ ∧
      c₁.nreg 60006 = K ∧ c₁.nreg 116000 = V.CB ∧ c₁.nreg 116001 = K := by
    have hwr : wr ztgjm
      ztdlq = true := by_decide
    suffices H : ∃ c₁ k₁, Exec P W _ c c₁ k₁ ∧ k₁ = 3 ∧
        c₁.nreg 60006 = K ∧ c₁.nreg 116000 = V.CB ∧ c₁.nreg 116001 = K by
      obtain ⟨c₁, k₁, ex, hk, a, b, d⟩ := H
      exact ⟨c₁, k₁, ex, hk, exec_frameB ex hwr, a, b, d⟩
    exec_block
    simp_all
  have h1 := hq.one
  -- 2. the items
  obtain ⟨c₂, k₂, e₂, hk₂, n₂, m₂, rr₂, rm₂, o₂⟩ : ∃ c₂ k₂, Exec P W
      ztctx c₁ c₂ k₂ ∧ k₂ = 2 ∧
      c₂.nreg = upd ztrxt 9999 ztnjc ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    zud
    have a9 : ztlxy := by zunzp
    exec_block
    · config_simp; omega
    simp_all
  have b30 : ztpng := by_simp_all
  have b6 : c₂.nreg 60006 = K := by_simp_all
  have b11 : zthoq := by rw [n₂]; config_simp; zunzq
  obtain ⟨c₃, k₃, e₃, hk₃, r₃, rr₃, mm₃, rm₃, o₃, -, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 60020) (rn := 60006) (r1 := 120011) (ra := 60016) (rv := 60017)
    (body := block [.addN 60016 30003 60020, .copyN 60017 60020])
    (B := fun r => decide zthka) by_decide by_decide by_decide by_decide
    by_decide ztdky A₀
    (fun d d' hJ hr hm => JK.stable (rs := [60020]) (fun r hr' => by
      simp_all) hJ
      ztdod hm)
    (n := K) (κ := 2) ztijn ztfrq ztbeo
    (fun i d hi hJ hwd hri => by
      have g30 : ztpob := by rw [hJ.1 _ by_decide, b30]
      obtain ⟨d', k, e, hk, v1, v2⟩ : ∃ d' k, Exec P W (block [.addN 60016 30003 60020,
          .copyN 60017 60020]) d d' k ∧ k = 2 ∧ d'.nreg 60016 = A₀ + i ∧ d'.nreg 60017 = i := by
        exec_block
        · omega
        simp_all
      exact ztdjb)
    e₂.wb_right ztdkz b6 b11 by_omega
  zujwf
  -- 3. the count of the sort
  have e₄ := Exec.copyN (P := P) e₃.wb_right 30004 60006
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg 30004 _ } with hc₄
  have R₄ : ∀ r, r ≠ 30004 → c₄.nreg r = c₃.nreg r := fun r hr => by
    zunbf; config_simp; zunhy
  have hm₄ : ztmvj := rfl
  have g9 : c₄.nreg 9999 = A₀ + K := by
    zunaq; config_simp
  have g30 : ztpnr := by
    grind
  have g304 : c₄.nreg 30004 = K := by
    rw [hc₄]; config_simp; grind
  have hitems : SortL.seg c₄.nmem (c₄.nreg 30003) (List.range K).length = List.range K := by
    zugy

    zulzs
  have hmem₄ : ztced := fun a ha => by
    rw [hm₄, mm₃, scat_below by_grind ha, m₂, F₁.2.2.1]
  -- 4. the sort
  have hband : zthpg := fun r a b => by
    zuele
    rw [upd_other _ _ _ by_omega, upd_other _ _ _ by_omega,
      F₁.1 r by_grind]
  have hJ₄ : ChCJ c c₄.nmem ztnjc K c₄ :=
    ⟨by zunaq; config_simp; exact a0,
      by zunaq; config_simp; exact a1,
      hband, by_omega⟩
  have hW' : A₀ + K ≤ W := by_omega
  obtain ⟨c₅, k₅, e₅, hk₅, J₅, F₅, s₁, s₂, L', hseg, hperm, hpw⟩ := SortR.sortStmt_exec (P := P)
    (W := W) (chCmp_ok hG hW hv hq (m₀ := c₄.nmem) (A₀ := A₀ + K) (K := K)
      ztbmx hW'
      (fun i hi => by
        grind) htv hn) by_decide
    (fun a b d h h' => chLeB_trans _ _ _ _ _ _ _ _ h h') (chLeB_total _ _ _ _ _)
    e₄.wb_right hJ₄ (by rw [hAL, g9]; exact chCJ_stable _ _ _ _) ztpzt hitems
    by_grind by_grind
    by_grind
  rw [List.length_range] at hseg s₂ hk₅
  rw [hAL, g9] at s₁
  -- 5. the base of the table
  have e₆ := Exec.copyN (P := P) e₅.wb_right 60120 30005
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg 60120 _ } with hc₆
  have ex : Exec P W chSortS c c₆ _ := .seq e₁ ztbaqz
  have v120 : c₆.nreg 60120 = c₅.nreg 30005 := by_rfl
  have hm₆ : ztlar := rfl
  have hsd : ∀ t, t < K → c₆.nmem ztlms = L'.getD t 0 := fun t ht => by
    rw [hm₆, v120, ← hseg, SortL.seg_getD t ht]
  have hL'len : L'.length = K := by rw [← hseg, SortL.seg_length]
  have hmemL : ∀ t, t < K → L'.getD t 0 < K := fun t ht => by
    have : ztmtl := by rw [NFLoc.getD_of_lt 0 by_omega]; simp
    grind
  have hF5 : zteik := fun r hr =>
    F₅.1 r (by simp [hr, bSort, bSign, bOPrep, bOQuery])
      ztche
  have hsurj : ∀ i, i < K → ∃ t, t < K ∧ L'.getD t 0 = i := fun i hi => by
    zulgv
    zucoh
    exact ⟨t, by_omega, by rw [NFLoc.getD_of_lt 0 ht, e]⟩
  have hlt' : ∀ t, t < K → c₆.nmem ztlms < K := fun t ht => by
    grind
  have hsurj' : ∀ i, i < K → ∃ t, t < K ∧ c₆.nmem ztlms = i := fun i hi => by
    obtain ⟨t, ht, e⟩ := hsurj i hi; exact ⟨t, ht, by_grind⟩
  refine ⟨c₆, _, ex, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlt', fun q q' hq hq' e =>
    inj_of_surj hlt' hsurj' hq hq' e, ?_⟩
  · omega
  · have hAl' : ztpmf := hAl
    have F14 : FrameN chBands c c₄ := by
      refine PF.frameN (B := fun r => decide ztyc || decide ztgzi ||
        decide (116000 ≤ r ∧ r ≤ 116001) || decide ztgyw)
        ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_⟩ ztez ?_
      · zupg
        zuele
        zvmwf; split_ifs <;> first | omega | exact F₁.1 r (by
          zvnan; omega)
      · zupg
        show c₃.rreg r = c.rreg r
        rw [rr₃ r ztmz, rr₂,
          F₁.2.1 r ztmz]
      · grind
      · show c₃.rmem a = c.rmem a; rw [rm₃, rm₂, F₁.2.2.2.1]
      · show c₃.output = c.output; rw [o₃, o₂, F₁.2.2.2.2]
      · zufw
        zuws
        · omega
        · left; simp [chBands, bDecomp, bandOf]; omega
        · left; simp [chBands, bOPrep, bandOf]; omega
        · left; simp [chBands, bSort, bandOf]; omega
      · show c₃.rreg ALLOC = c.rreg ALLOC
        rw [rr₃ _ by_decide, rr₂, F₁.2.1 _ by_decide]
    have F56 : FrameN chBands c₅ c₆ :=
      Frame.toN (NFLoc.frame_of_frameB (exec_frameB e₆ (B := fun r => decide (r = 60120))
        by_decide) (fun r hr => by
          simp at hr; subst hr; decide) 1)
    have g9' : c₄.nreg ALLOC = A₀ + K := g9
    exact (F14.trans ztihd
      by_omega).trans F56
      by_grind
  · have := F₅.2.2.2.2.2.1; rw [hAL, g9] at this; zumys; exact this
  · have := F₅.2.2.2.2.2.2; rw [hAL, g9] at this; zumys; show c₅.nreg 9999 ≤ _; omega
  · intro r hr a b d e f
    rw [hc₆]; config_simp
    rw [upd_other _ _ _ f, hF5 r hr, R₄ r ztbej,
      R₃ r b d e, n₂]
    rw [upd_other _ _ _ ztbej,
      upd_other _ _ _ ztbej,
      F₁.1 r ztdua]
  · zumhh
    zumys; config_simp; zumya; exact J₅.2.2.1 r a b
  · omega
  · rw [v120, hc₆]; config_simp; exact s₂
  · zulni
    rw [hsd q by_omega, hsd q' hq']
    have hA := hmemL q by_omega
    have hB := hmemL q' hq'
    have hconv : ∀ i j, i < K → j < K →
        (ChLe P C V c₄.nmem i j ↔ ChLe P C V c.nmem i j) := fun i j hi hj =>
      chLe_congr fun x hx => by
        have : ztpql := by rcases hx with rfl | rfl <;> assumption
        grind
    rcases eq_or_lt_of_le hqq with h | h
    · subst h; exact chLe_refl _ _ _ _ _
    · have := List.pairwise_iff_getElem.1 hpw q q' by_omega by_omega h
      rw [← NFLoc.getD_of_lt 0 by_omega, ← NFLoc.getD_of_lt 0 by_omega] at this
      unfold chLeB at this
      grind
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
def wrRSOK (B : ℕ → Bool) : Instr → Bool
  | .storeN _ _ => true
  | i => wrROK B i

/-- Every instruction of the statement satisfies `wrRSOK B`. -/
def wrRS (B : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => wrRSOK B i
  | .seq s t => wrRS B s && wrRS B t
  | .ifLtN _ _ t e => wrRS B t && wrRS B e
  | .ifLtR _ _ t e => wrRS B t && wrRS B e
  | .whileLtN _ _ b => wrRS B b
  | .whileLtR _ _ b => wrRS B b
variable {P : Polygon} {W : ℕ} {C : Chain}
/-- **Real-register frame** with natural stores allowed. -/
theorem exec_rframeS {B : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : wrRS B s = true) : ∀ r, B r = false → c'.rreg r = c.rreg r := by
  induction h with
  | skip _ => exact by_simp_all
  | @instr ins c c' _ he _ _ =>
    simp only [wrRS] at hs
    cases ins <;> simp only [wrRSOK, wrROK, Bool.false_eq_true] at hs <;>
      zvncw at he <;>
      (try split at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;> subst he <;>
      intro j hj <;>
      first
      | rfl
      | (zvmwf; split_ifs with hh
         · simp_all
         · rfl)
  | seq _ _ ih₁ ih₂ =>
    simp only [wrRS, Bool.and_eq_true] at hs
    zufeo
  | ifLtN_true _ _ ih =>
    zufco
  | ifLtN_false _ _ ih =>
    zufcp
  | ifLtR_true _ _ ih =>
    zufco
  | ifLtR_false _ _ ih =>
    zufcp
  | whileLtN_false _ _ => exact by_simp_all
  | whileLtN_true _ _ _ ih₁ ih₂ =>
    zueov
  | whileLtR_false _ _ => exact by_simp_all
  | whileLtR_true _ _ _ ih₁ ih₂ =>
    zueov

/-- The registers of `PLoaded`. -/
def PLReg (r : ℕ) : Prop :=
  (120010 ≤ r ∧ r ≤ 120022) ∨ r = 120028 ∨ r = 120029 ∨ r = 120030 ∨ r = 120039 ∨
    (120043 ≤ r ∧ r ≤ 120048)
theorem PLoaded.congr {D NB s mm ti bb A K CB AB RB SB LB : ℕ} {c c' : Config}
    (h : PLoaded P D NB s mm ti bb A K CB AB RB SB LB c)
    (hr : ∀ r, PLReg r → c'.nreg r = c.nreg r) : PLoaded P D NB s mm ti bb A K CB AB RB SB LB c' := by
  have g : ∀ r, PLReg r → ∀ v, c.nreg r = v → c'.nreg r = v := by_simp_all
  exact ⟨g _ by_tauto _ h.n, g _ by_tauto _ h.one,
    g _ by_tauto _ h.zero, g _ ztqgd _ h.two,
    g _ by_tauto _ h.six, g _ by_tauto _ h.rD,
    g _ by_tauto _ h.rNB, g _ by_tauto _ h.rs,
    g _ by_tauto _ h.rm, g _ by_tauto _ h.rti,
    g _ by_tauto _ h.rbb, g _ by_tauto _ h.twoM,
    g _ by_tauto _ h.nW, g _ by_tauto _ h.tEnd,
    g _ by_tauto _ h.sS, g _ by_tauto _ h.tv,
    g _ by_tauto _ h.rA, g _ by_tauto _ h.rK,
    g _ ztqgd _ h.rCB, g _ by_tauto _ h.rAB,
    g _ by_tauto _ h.rRB, g _ by_tauto _ h.rSB,
    g _ by_tauto _ h.rLB⟩

/-- A neutral origin and direction, and the granularity saved in `120049`. -/
def setA : Stmt :=
  block [.constN 120025 2, .constN 120023 0, .constN 120024 0, .copyN 120049 110002,
    .copyN 120026 9999]

/-- The constant `3` of the zipper; the chord table into `120038`. -/
def setZ : Stmt := block [.constN 110205 3, .copyN 120038 60120]

/-- **Phase A.** -/
def phA : Stmt :=
  .seq pLoad (.seq setA (.seq chSortS (.seq setZ (.seq mdS (.seq tbS (.seq posTS posInit))))))

/-- The side of the top from the descriptor. -/
theorem sS_of_desc {m : ℕ → ℕ} {D : ℕ} {Q : Polygon} {H : Host} {C : Chain}
    (hD : ChainDescAt m D Q H C) :
    (if m ztcel = 1 then C.topIdx else 2 * C.m - C.topIdx) = C.sideS C.sideBeta := by
  obtain ⟨-, -, -, -, -, hd4⟩ := hD
  unfold Chain.sideS
  simp_all

/-- The chord order only reads the chord area, the chain and the top vertex of the values. -/
theorem chLe_V_congr {V V' : QV} {m : ℕ → ℕ} {i j : ℕ}
    (hCB : V.CB = V'.CB) (hm : V.m = V'.m) (hs : V.s = V'.s) (htv : V.tv = V'.tv) :
    ChLe P C V m i j ↔ ChLe P C V' m i j := by
  unfold ChLe xpX' xpSym chH chL
  simp_all
theorem arcs_pos {Q : Polygon} {N : NF} (hs : C.P.Simple)
    (hN : IsNF ztc Q N) : 0 < N.arcs.length := by
  obtain ⟨⟨U, hU, a, b, hab⟩, -⟩ := arcCover ztc Q ztwjh
    (Or.inl ⟨C, hs, rfl⟩) hN.1
  obtain ⟨j, hj, -⟩ := NFLoc.listed_of_isArc hN hU hab
  omega

/-- The bands of phase A. -/
def aBands : Finset ℕ := {bSort, bSign, bDecomp, bOPrep, bOQuery}
set_option maxHeartbeats 8000000 in
theorem phA_exec {c : Config} (hw : WordsBounded W c) (hG : GoodEnv P)
    (hW : 8 * P.n + 32 ≤ W) {H : Host} {C : Chain} {N : NF} {A₀ : ℕ}
    (hD : ChainDescAt c.nmem ztmfm zta H C) (hCQ : C.P = Qof P)
    (hsl : C.s < C.P.n) (hNFw : NFWithin c.nmem ztmfn A₀ N)
    (hN : IsNF ztc zta N) (hAl : c.nreg 9999 = A₀)
    (hDA : c.nreg 110000 + 5 ≤ A₀)
    (hroom : A₀ + 3 * (N.arcs.length + N.chords.length) +
      SortR.sortCost 500 N.chords.length + 20 ≤ W) :
    ∃ cA k, Exec P W phA c cA k ∧
      k ≤ 8 * Nat.clog 2 ztbbt + 8 * N.arcs.length +
        7 * N.chords.length + SortR.sortCost 500 N.chords.length + 230 ∧
      FrameN aBands c cA ∧
      A₀ + N.chords.length ≤ cA.nreg 120038 ∧ cA.nreg 120038 + N.chords.length ≤ cA.nreg 120040 ∧
      cA.nreg 120040 ≤ A₀ + N.chords.length + SortR.sortCost 500 N.chords.length ∧
      cA.nreg 9999 = cA.nreg 120040 + 6 + Nat.clog 2 ztbbt +
        N.arcs.length ∧
      PLoaded P ztmfm ztmfn C.s C.m C.topIdx ztnwl
        N.arcs.length N.chords.length ztnwm ztnwn
        (c.nmem (c.nreg 110001 + 5)) (c.nmem ztlkn) (c.nmem (c.nreg 110001 + 7)) cA ∧
      cA.nreg 120025 = 2 ∧ cA.nreg 120023 = 0 ∧ cA.nreg 120024 = 0 ∧
      cA.nreg 120049 = c.nreg 110002 ∧ cA.nreg 110205 = 3 ∧ cA.nreg 120026 = A₀ ∧
      cA.nmem (cA.nreg 120040) = 0 ∧
      (∀ i, i < 5 → cA.nmem (cA.nreg 120040 + 1 + i) = c.nmem (c.nreg 110000 + i)) ∧
      cA.nreg 120041 = cA.nreg 120040 + 6 ∧
      cA.nreg 120042 = Nat.clog 2 ztbbt ∧
      (∀ j, j < Nat.clog 2 ztbbt →
        cA.nmem (cA.nreg 120041 + j) = 2 ^ j) ∧
      N.arcs.length < 2 ^ Nat.clog 2 ztbbt ∧
      N.chords.length < 2 ^ Nat.clog 2 ztbbt ∧
      cA.nreg 120031 = cA.nreg 120041 + Nat.clog 2 ztbbt ∧
      (∀ j, j < N.arcs.length → cA.nmem ztrmu < N.arcs.length ∧
        N.seq.getD (cA.nmem ztrmu) 0 = j) ∧
      PosK P.n C.s C.m ztboi ztvcn cA ∧
      (∀ q, q < N.chords.length → cA.nmem ztllw < N.chords.length) ∧
      (∀ q q', q < N.chords.length → q' < N.chords.length →
        cA.nmem ztllw = cA.nmem (cA.nreg 120038 + q') → q = q') ∧
      (∀ q q', q ≤ q' → q' < N.chords.length →
        ChLe P C (qvOf cA) c.nmem (cA.nmem (cA.nreg 120038 + q)) (cA.nmem (cA.nreg 120038 + q'))) := by
  zuhp
  zuc
  zulm
  have hNF : ztpkv := hNFw.nfAt
  zuyo

  have hLle : Nat.clog 2 ztbbt ≤
      N.arcs.length + N.chords.length + 1 := by
    zuosp; exact (Nat.lt_two_pow_self).le
  zucme
  zubb
  have hsc := SortR.sortCost_ge 500 N.chords.length
  -- 1. the constants
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, PL₁⟩ := pLoad_exec (P := P) c hw hD hCQ hsl hNF by_omega
    by_omega hW
  -- 2. the neutral registers
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, s25, s23, s24, s49, s26⟩ : ∃ c₂ k₂, Exec P W setA c₁ c₂ k₂ ∧
      k₂ = 5 ∧ FrameB (fun r => decide (r = 120025 ∨ r = 120023 ∨ r = 120024 ∨ r = 120049 ∨
        r = 120026)) c₁ c₂ ∧
      c₂.nreg 120025 = 2 ∧ c₂.nreg 120023 = 0 ∧ c₂.nreg 120024 = 0 ∧
      c₂.nreg 120049 = c.nreg 110002 ∧ c₂.nreg 120026 = A₀ := by
    have hwr : wr (fun r => decide (r = 120025 ∨ r = 120023 ∨ r = 120024 ∨ r = 120049 ∨
      r = 120026)) setA = true := by_decide
    suffices H : ∃ c₂ k₂, Exec P W setA c₁ c₂ k₂ ∧ k₂ = 5 ∧
        c₂.nreg 120025 = 2 ∧ c₂.nreg 120023 = 0 ∧ c₂.nreg 120024 = 0 ∧
        c₂.nreg 120049 = c.nreg 110002 ∧ c₂.nreg 120026 = A₀ by
      obtain ⟨c₂, k₂, ex, hk, a, b, d, e, f⟩ := H
      exact ⟨c₂, k₂, ex, hk, exec_frameB ex hwr, a, b, d, e, f⟩
    zud
    zukaq
    unfold setA
    exec_block
    all_goals (try omega)
    exact ⟨rfl, by config_simp, by config_simp, by config_simp,
      by config_simp; exact F₁.1 _ by_decide,
      by config_simp; zunzp⟩
  have PL₂ := PL₁.congr fun r hr => F₂.1 r (by
    unfold PLReg at hr; grind)
  have a9₂ : zturo := by rw [F₂.1 _ by_decide, F₁.1 _ by_decide, hAl]
  zulko
  -- 3. the chord table
  have hq₂ : QConst P _ c₂ := qconst_qvOf PL₂.n PL₂.one PL₂.zero PL₂.two PL₂.six
    (by rw [PL₂.twoM, PL₂.rm]) (by rw [PL₂.nW, PL₂.rm]) (by rw [PL₂.tEnd, PL₂.rm]) s25
  have hv₂ : QVOK P C ztwcg :=
    ⟨hCQ, PL₂.rs, PL₂.rm, by show c₂.nreg 120021 = _; rw [PL₂.sS]; exact sS_of_desc hD,
      by show c₂.nreg 120023 < P.n; omega, by show c₂.nreg 120024 ≤ 1; omega,
      by show c₂.nreg 120015 < P.n; rw [PL₂.rs]; simp_all⟩
  have hK₂ : (qvOf c₂).K = N.chords.length := PL₂.rK
  have hCB₂ : (qvOf c₂).CB = c.nmem _ := PL₂.rCB
  have hrec : ∀ i, i < (qvOf c₂).K → (qvOf c₂).CB + 5 * i + 2 ≤ A₀ := fun i hi => by
    zuksv
    have h1 : Robust A₀ c.nmem fun m' => m' (m' _ + ztjfv) =
        (N.chord i).dn := fun m' hm' => by
      have := ((hNFw m' hm').2.2.2.2.2.1 i hi).2.2.2.2
      omega
    have := (NFLoc.robust_addr2 h1).2
    omega
  have hh : ∀ i, i < (qvOf c₂).K → c₂.nmem ((qvOf c₂).CB + 5 * i) < P.n := fun i hi => by
    zuksv
    rw [hm₂, hCB₂, (hNF.2.2.2.2.2.1 i hi).1]
    obtain ⟨-, -, -, -, -, -, -, -, -, hhh, -⟩ := hN
    have := hhh i hi; omega
  have htv : (qvOf c₂).tv < P.n := by
    show c₂.nreg 120022 < P.n; rw [PL₂.tv]; exact Nat.mod_lt _ by_omega
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, al3a, al3b, R6₃, R12₃, ch1, ch2, chlt, chinj, chsort⟩ :=
    chSort_exec (P := P) hG hW e₂.wb_right hv₂ hq₂ a9₂ hrec hh htv by_omega
      by_grind
  rw [hK₂] at hk₃ al3a al3b ch1 ch2 chlt chinj chsort
  zvnek at al3a al3b ch2
  set A₁ := c₃.nreg 9999 with hA₁
  have PL₃ := PL₂.congr fun r hr => R12₃ r zteql
    zteql
  -- 4. the zipper constant and the chord table
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, z205, z38⟩ : ∃ c₄ k₄, Exec P W setZ c₃ c₄ k₄ ∧ k₄ = 2 ∧
      FrameB ztikb c₃ c₄ ∧ c₄.nreg 110205 = 3 ∧
      c₄.nreg 120038 = c₃.nreg 60120 := by
    have hwr : wr ztikb setZ = true := by_decide
    suffices H : ∃ c₄ k₄, Exec P W setZ c₃ c₄ k₄ ∧ k₄ = 2 ∧ c₄.nreg 110205 = 3 ∧
        c₄.nreg 120038 = c₃.nreg 60120 by
      zudeg

    zubj
    unfold setZ
    exec_block
    · omega
    simp
  have PL₄ := PL₃.congr fun r hr => F₄.1 r (by
    unfold PLReg at hr; zvnan; omega)
  have a9₄ : c₄.nreg 9999 = A₁ := by zunpi
  -- 5. the model descriptor
  obtain ⟨c₅, k₅, e₅, hk₅, F₅, a9₅, md₅, m0₅, mi₅⟩ := mdS_exec (P := P) e₄.wb_right PL₄.rD
    PL₄.one a9₄ by_omega by_omega
  have PL₅ := PL₄.congr fun r hr => F₅.1 r (by
    unfold PLReg at hr; simp only [BMD, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  -- 6. the table of powers
  obtain ⟨c₆, k₆, e₆, hk₆, F₆, a9₆, tb₆, l₆, tab₆, Alt, Klt⟩ := tbS_exec (P := P) e₅.wb_right
    PL₅.rA PL₅.rK PL₅.one a9₅ by_omega
  have PL₆ := PL₅.congr fun r hr => F₆.1 r (by
    unfold PLReg at hr; simp only [BTB, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  -- 7. the inverse table
  have mem₆ : ztkoa := fun a ha => by
    rw [F₆.2.2.1 _ by_omega, F₅.2.2.1 _ by_omega, F₄.2.2.1,
      F₃.2.2.1 a by_grind, hm₂]
  have hseq : ∀ p, p < N.arcs.length →
      c₆.nmem (c.nmem ztlkn + p) = N.seq.getD p 0 := fun p hp => by
    rw [mem₆ _ by_omega]
    exact hNF.2.2.2.2.2.2.2.2.1 p ztlgr
  obtain ⟨c₇, k₇, e₇, hk₇, F₇, a9₇, pos₇, pf₇⟩ := posTS_exec (P := P) e₆.wb_right PL₆.rSB PL₆.rA
    PL₆.one a9₆ hseq by_omega by_omega (fun p hp => NFLoc.seq_lt hN hp)
    (fun p q hp hq e => by
      have hnd := OracleQ.seq_nodup hN
      zuhfd
      rw [NFLoc.getD_of_lt 0 by_omega, NFLoc.getD_of_lt 0 by_omega] at e
      exact (List.Nodup.getElem_inj_iff hnd).1 e)
    (fun j hj => NFLoc.seq_surj hN hj)
  have PL₇ := PL₆.congr fun r hr => F₇.1 r (by
    unfold PLReg at hr; simp only [BPT, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  -- 8. the position constants
  have hSs : c₇.nreg 120021 = C.sideS C.sideBeta := by rw [PL₇.sS]; exact sS_of_desc hD
  obtain ⟨c₈, k₈, e₈, hk₈, F₈, q0, q1, q2, q3, q4⟩ := posInit_exec (P := P) e₇.wb_right PL₇.rm
    PL₇.twoM hSs (C.sideS_lt _) hm1 by_omega
  have PL₈ := PL₇.congr fun r hr => F₈.1 r (by
    unfold PLReg at hr; simp only [BPI, decide_eq_false_iff_not]; omega)
  have ex : Exec P W phA c c₈ _ :=
    .seq e₁ ztey
  -- the later stages keep the registers outside their sets and the memory below `A₁`
  have K58 : ∀ r, BPI r = false → BPT r = false → BTB r = false → BMD r = false →
      c₈.nreg r = c₄.nreg r := fun r a b d e => by
    rw [F₈.1 r a, F₇.1 r b, F₆.1 r d, F₅.1 r e]
  have M48 : ∀ a, a < A₁ → c₈.nmem a = c₄.nmem a := fun a ha => by
    rw [F₈.2.2.1, F₇.2.2.1 a by_omega, F₆.2.2.1 a by_omega, F₅.2.2.1 a ha]
  have hMD : c₈.nreg 120040 = A₁ := by
    rw [F₈.1 _ by_decide, F₇.1 _ by_decide, F₆.1 _ by_decide, md₅]
  have hCH : c₈.nreg 120038 = c₃.nreg 60120 := by
    rw [K58 _ by_decide by_decide by_decide by_decide, z38]
  have hV : ∀ q q', ChLe P C ztwcg c₂.nmem q q' ↔ ChLe P C (qvOf c₈) c.nmem q q' := by
    intro q q'
    zundq
    exact chLe_V_congr (by show c₂.nreg 120043 = c₈.nreg 120043; rw [PL₂.rCB, PL₈.rCB])
      (by show c₂.nreg 120016 = c₈.nreg 120016; rw [PL₂.rm, PL₈.rm])
      (by show c₂.nreg 120015 = c₈.nreg 120015; rw [PL₂.rs, PL₈.rs])
      (by show c₂.nreg 120022 = c₈.nreg 120022; rw [PL₂.tv, PL₈.tv])
  refine ⟨c₈, _, ex, by_omega, ?_, by_omega, by_omega,
    by omega, ?_, PL₈, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Alt, Klt, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · -- the frame
    have hband : ∀ r, ztndx → bandOf r ∈ aBands := by
      intro r h; simp only [aBands, Finset.mem_insert, Finset.mem_singleton, bOPrep, bOQuery,
        bandOf]; omega
    have hrr₁ := fun r =>
      exec_rframeS ztyv (B := fun _ => false) by_decide r rfl
    have FA := PF.frameN (B := fun r => BPL r ||
        decide _)
      ⟨fun r hr => by
        simp only [Bool.or_eq_false_iff] at hr; zunte,
        fun r _ => hrr₁ r, by_grind, fun a _ => by zuomf,
        by zuomg⟩
      (fun r hr => by
        simp only [BPL, Bool.or_eq_true, decide_eq_true_eq] at hr
        left; exact hband r by_omega) (hrr₁ _)
    have FB : FrameN aBands c₂ c₃ := FrameN.mono F₃ by_decide
    have hrr₂ := fun r =>
      exec_rframeS (.seq e₄ zteka) (B := fun _ => false) by_decide r rfl
    have FC := PF.frameN (B := fun r => decide _ || BMD r ||
        BTB r || BPT r || BPI r)
      ⟨fun r hr => by
        zufar
        rw [K58 r hr.2 hr.1.2 hr.1.1.2 hr.1.1.1.2, F₄.1 r hr.1.1.1.1],
        fun r _ => hrr₂ r, fun a ha => by zvnek at ha; rw [M48 a ha, F₄.2.2.1],
        fun a ha => by
          zuksd
          rw [F₈.2.2.2.1, F₇.2.2.2.1 a by_omega, F₆.2.2.2.1 a by_omega, F₅.2.2.2.1 a ha,
            F₄.2.2.2.1],
        by rw [F₈.2.2.2.2, F₇.2.2.2.2, F₆.2.2.2.2, F₅.2.2.2.2, F₄.2.2.2.2]⟩
      (fun r hr => by
        simp only [BMD, BTB, BPT, BPI, Bool.or_eq_true, decide_eq_true_eq] at hr
        zujsv
        · omega
        · left; exact hband r by_omega) (hrr₂ _)
    have hA₂ : zteia := by_grind
    exact (FA.trans FB hA₂).trans FC by_grind
  · rw [F₈.1 _ by_decide, a9₇, hMD]
  · rw [K58 _ by_decide by_decide by_decide by_decide, F₄.1 _ by_decide,
      R12₃ _ by_omega by_omega, s25]
  · rw [K58 _ by_decide by_decide by_decide by_decide, F₄.1 _ by_decide,
      R12₃ _ by_omega by_omega, s23]
  · rw [K58 _ by_decide by_decide by_decide by_decide, F₄.1 _ by_decide,
      R12₃ _ by_omega by_omega, s24]
  · rw [K58 _ by_decide by_decide by_decide by_decide, F₄.1 _ by_decide,
      R12₃ _ by_omega by_omega, s49]
  · rw [K58 _ by_decide by_decide by_decide by_decide]; omega
  · rw [K58 _ by_decide by_decide by_decide by_decide, F₄.1 _ by_decide,
      R12₃ _ by_omega by_omega, s26]
  · rw [hMD, F₈.2.2.1, F₇.2.2.1 _ by_omega, F₆.2.2.1 _ by_omega, m0₅]
  · zug
    rw [hMD, F₈.2.2.1, F₇.2.2.1 _ by_omega, F₆.2.2.1 _ by_omega, mi₅ i hi, F₄.2.2.1,
      F₃.2.2.1 _ by_grind, hm₂]
  · rw [F₈.1 _ by_decide, F₇.1 _ by_decide, tb₆, hMD]
  · rw [F₈.1 _ by_decide, F₇.1 _ by_decide, l₆]
  · zun
    rw [F₈.1 _ by_decide, F₇.1 _ by_decide, tb₆, F₈.2.2.1, F₇.2.2.1 _ by_omega]
    exact tab₆ j hj
  · rw [F₈.1 _ by_decide, pos₇, F₈.1 _ by_decide, F₇.1 _ by_decide, tb₆]
  · zun
    rw [F₈.1 _ by_decide, pos₇, F₈.2.2.1]; exact pf₇ j hj
  · exact ⟨PL₈.n, PL₈.one, PL₈.zero, PL₈.rs, PL₈.rm, PL₈.twoM, by rw [F₈.1 _ by_decide, hSs],
      PL₈.six, PL₈.tEnd, q0, q1, q2, q3, q4⟩
  · zuco
    rw [hCH, M48 _ by_omega, F₄.2.2.1]; exact chlt q hq
  · zukjs
    rw [hCH, M48 _ by_omega, M48 _ by_omega, F₄.2.2.1] at e
    exact chinj q q' hq hq' e
  · zulni
    rw [hCH, M48 _ by_omega, M48 _ by_omega, F₄.2.2.1]
    exact (hV _ _).1 (chsort q q' hqq hq')
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
theorem RgMem.congr {m m' : ℕ → ℕ} {AB SB A : ℕ} {σ rg : ℕ → ℕ} (h : RgMem m AB SB A σ rg)
    {X : ℕ} (hX : ∀ a, a < X → m' a = m a) (hS : SB + A ≤ X) (hA : AB + 5 * A ≤ X) :
    RgMem m' AB SB A σ rg :=
  ⟨fun p hp => by rw [hX _ by_omega]; exact h.seq p hp, h.σ_lt,
    fun j hj => by rw [hX _ by_omega]; exact h.reg j hj⟩

/-! ## The star chords -/

/-- **The star chords.** -/
def starStage : Stmt := .seq frS iS
variable {P : Polygon} {W : ℕ} {c : Config} {S : Finset ℕ} {lo : ℕ}
theorem starStage_exec (hw : WordsBounded W c)
    {NB AB SB A R A₁ : ℕ} {σ rg : ℕ → ℕ} (hM : RgMem c.nmem AB SB A σ rg)
    (hNB : c.nreg 120014 = NB) (h2 : c.nreg 120048 = 2) (hR : c.nmem ztnng = R)
    (hAB : c.nreg 120044 = AB) (hSB : c.nreg 120046 = SB) (hA : c.nreg 120030 = A)
    (h1 : c.nreg 120011 = 1) (hAl : c.nreg 9999 = A₁) (hNBA : NB + 2 < A₁) (hSA : SB + A ≤ A₁)
    (hABA : AB + 5 * A ≤ A₁) (hρR : ∀ p, p < A → rg ztibw < R)
    (hW : A₁ + R + A + 2 * chCap A ≤ W) :
    ∃ c' k, Exec P W starStage c c' k ∧ k ≤ 46 * A + 23 ∧
      PF (fun r => BFR r || BIS r) A₁ c c' ∧ c'.nreg 9999 = A₁ + R + 2 * chCap A ∧
      c'.nreg 110072 = A₁ + R ∧ c'.nreg 110073 = A₁ + R + chCap A ∧
      c'.nreg 110074 = (starList ztcdf A).length ∧
      PairsAt c'.nmem (A₁ + R) (A₁ + R + chCap A) ztzxy := by
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, a9, a60, afr⟩ := frS_exec (P := P) hw hM hNB h2 hR hAB hSB hA h1 hAl
    hNBA hSA hABA hρR by_omega
  have hM₁ : RgMem c₁.nmem AB SB A σ rg := hM.congr (X := A₁) F₁.2.2.1 hSA hABA
  have K : ztjbg := F₁.1
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, b9, b72, b73, -, b74, pairs⟩ := iS_exec (P := P) e₁.wb_right hM₁
    (by rw [K _ by_decide, hAB]) (by rw [K _ by_decide, hSB]) (by rw [K _ by_decide, hA])
    (by rw [K _ by_decide, h1]) a60 a9 by_omega by_omega by_omega hρR afr by_omega
  refine ⟨c₂, _, .seq e₁ e₂, by_omega,
    (F₁.mono ztcvp le_rfl).trans
      (F₂.mono ztcvp by_omega), b9, b72, b73, b74, pairs⟩

/-! ## The raw zipper pairs -/

/-- **The raw zipper pairs.** -/
def zipStage : Stmt := .seq zS spS
theorem zipStage_exec {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {A₃ : ℕ} (hAl : c.nreg 9999 = A₃)
    (hlo : lo ≤ A₃) (hW : A₃ + 2 * zCap V.A + 10 ≤ W) :
    ∃ c' k, Exec P W zipStage c c' k ∧
      k ≤ 2 * V.A * ztzbg + 3 * ztxup + 220 ∧
      PF (fun r => BZS r || BSP r) A₃ c c' ∧ c'.nreg 9999 = A₃ + 2 * zCap V.A ∧
      c'.nreg 110293 = A₃ ∧ c'.nreg 110294 = A₃ + zCap V.A ∧
      c'.nreg 110295 = (OracleQ.zipRaw C zta N).length ∧
      PairsAt c'.nmem A₃ (A₃ + zCap V.A) (OracleQ.zipRaw C zta N) ∧ ZEnv P W lo C N V c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, a9, a93, a94, a97, a95, pairs₁, Z₁⟩ :=
    zS_exec (P := P) hw h hAl hlo by_omega
  have hA : ztscy := h.loc.holds.1.A
  have hlen : (emitted ztxna V.A ++ emitted ztxmz V.A).length ≤
      2 * V.A := by
    zujgr
    have := emitted_length_le ztxna V.A
    have := emitted_length_le ztxmz V.A
    omega
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, rm₂, o₂, cnt, ⟨pairs₂, mem₂⟩, Z₂⟩ := spS_exec (P := P)
    e₁.wb_right Z₁ a93 a94 a95 hlo (by have hz : ztied := rfl; omega)
    (by have hz : ztied := rfl; omega)
  have hz : ztied := rfl
  have hsplen : ztykt := by
    unfold OracleQ.zipSp OracleQ.zipSpO
    grind
  have hraw : OracleQ.zipRaw C zta N = (emitted ztxna V.A ++
      emitted ztxmz V.A) ++ OracleQ.zipSp C (Qof P) N := by
    zvmze; rfl
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, (F₁.mono ztcvp le_rfl).trans ?_, by rw [r₂ _ by_decide, a9],
    by rw [r₂ _ by_decide, a93], by rw [r₂ _ by_decide, a94], ?_, ?_, Z₂⟩
  · refine ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => mem₂ a ztec,
      fun a _ => by zuoez, by zuofa⟩
    · simp_all
    simp_all
  · grind
  · rw [hraw]
    refine PairsAt.append ztjwn pairs₂
    rw [mem₂ _ ztec, mem₂ _ ztbaly]
    zulzj

/-! ## The global frame -/

/-- **The frame of a phase** relative to a fixed bound `lo` (the allocator at the entry of the
preprocessing): registers outside the bands (and the allocator), real registers outside the
bands, memory below `lo`, output. -/
def GF (S : Finset ℕ) (lo : ℕ) (c c' : Config) : Prop :=
  ztgnh ∧
    ztimv ∧ zteda ∧
    ztiuo ∧ c'.output = c.output
theorem GF.trans {c₁ c₂ c₃ : Config} (h₁ : GF S lo c₁ c₂)
    (h₂ : GF S lo c₂ c₃) : GF S lo c₁ c₃ :=
  ⟨fun r a b => (h₂.1 r a b).trans (h₁.1 r a b), fun r a => (h₂.2.1 r a).trans (h₁.2.1 r a),
    fun a ha => (h₂.2.2.1 a ha).trans ztobj,
    fun a ha => (h₂.2.2.2.1 a ha).trans ztobk, h₂.2.2.2.2.trans h₁.2.2.2.2⟩
theorem FrameN.gf {c c' : Config} (h : FrameN S c c')
    (hlo : lo ≤ c.nreg ALLOC) : GF S lo c c' :=
  ⟨h.1, h.2.1, fun a ha => h.2.2.1 a by_omega, fun a ha => h.2.2.2.1 a by_omega, h.2.2.2.2⟩

/-- A stage frame with the written registers in the bands (or the allocator), whose real registers
are preserved. -/
theorem PF.gf {B : ℕ → Bool} {S : Finset ℕ} {lo lo' : ℕ} {c c' : Config} (h : PF B lo' c c')
    (hB : ∀ r, B r = true → bandOf r ∈ S ∨ r = ALLOC) (hrr : ∀ r, c'.rreg r = c.rreg r)
    (hlo : lo ≤ lo') : GF S lo c c' := by
  refine ⟨fun r hr hra => h.1 r ?_, fun r _ => hrr r, fun a ha => h.2.2.1 a by_omega,
    fun a ha => h.2.2.2.1 a by_omega, h.2.2.2.2⟩
  grind

/-! ## The deduplication -/

/-- **The sorted, deduplicated zipper pairs after the star chords.** -/
def dedupStage : Stmt := .seq dSort (.seq (.instr (.copyN 60008 60003)) dEmit)
set_option maxHeartbeats 2000000 in
theorem dedupStage_exec (hw : WordsBounded W c)
    {CH1 CH2 nI Z1 Z2 n A₄ : ℕ} (h72 : c.nreg 110072 = CH1) (h73 : c.nreg 110073 = CH2)
    (h74 : c.nreg 110074 = nI) (h93 : c.nreg 110293 = Z1) (h94 : c.nreg 110294 = Z2)
    (h95 : c.nreg 110295 = n) (h1 : c.nreg 120011 = 1) (h0 : c.nreg 120012 = 0)
    (hAl : c.nreg 9999 = A₄) (hZ1 : Z1 + n ≤ A₄) (hZ2 : Z2 + n ≤ A₄)
    (hC : CH1 + nI + n ≤ CH2) (hZ : CH2 + nI + n ≤ Z1) (hZ12 : Z1 ≤ Z2)
    (hroom : A₄ + n + SortR.sortCost 20 n ≤ W) :
    ∃ c' k, Exec P W dedupStage c c' k ∧ k ≤ 47 * n + SortR.sortCost 20 n + 25 ∧
      (∀ r, bandOf r ∉ dBands → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ dBands → c'.rreg r = c.rreg r) ∧
      (∀ a, (a < CH1 + nI ∨ (CH1 + nI + n ≤ a ∧ a < CH2 + nI) ∨ (CH2 + nI + n ≤ a ∧ a < A₄)) →
        c'.nmem a = c.nmem a) ∧
      (∀ a, a < A₄ → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      A₄ + n ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A₄ + n + SortR.sortCost 20 n ∧
      c'.nreg 60001 = CH1 ∧ c'.nreg 60002 = CH2 ∧ c'.nreg 60008 = nI ∧
      ∃ D : List ztw, c'.nreg 60003 = nI + D.length ∧ D.length ≤ n ∧
        PairsAt c'.nmem ztswe ztswf D ∧ D.Nodup ∧
        ∀ x, x ∈ D ↔ ∃ i, i < n ∧ ztchj = x := by
  zuhp
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, al1a, al1b, v1, v2, v3, v4, v5, v6, sb1, sb2, hsort, hsurj, hlt⟩ :=
    dSort_exec (P := P) hw h72 h73 h74 h93 h94 h95 h1 hAl hZ1 hZ2 hroom
  have hA₄ : c.nreg ALLOC = A₄ := hAl
  have e₂ := Exec.copyN (P := P) e₁.wb_right 60008 60003
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 60008 (c₁.nreg 60003) } with hc₂
  have R₂ : ∀ r, r ≠ 60008 → c₂.nreg r = c₁.nreg r := fun r hr => by
    simp_all
  have g11 : ztdxr := by
    rw [F₁.1 _ by_decide by_decide, h1]
  have g12 : ztpmr := by
    rw [F₁.1 _ by_decide by_decide, h0]
  have hW9 : c₁.nreg 9999 ≤ W := e₁.wb_right.1 9999
  have hDE : DEnv (c₁.nreg 60007) Z1 Z2 n ztkwf
      (fun i => c.nmem zthdf) (fun i => c.nmem zthdg) c₂ :=
    ⟨by_simp_all, by_simp_all, R₂ _ by_decide,
      by simp_all, by_simp_all,
      ⟨fun t _ => rfl, hlt, fun i hi => F₁.2.2.1 _ by_omega,
        fun i hi => F₁.2.2.1 _ by_omega⟩⟩
  obtain ⟨c₃, k₃, e₃, hk₃, r₃, rr₃, cnt₃, pairs₃, mem₃, rm₃, o₃⟩ := dEmit_exec (P := P) e₂.wb_right
    hDE by_simp_all by_simp_all
    by_simp_all by_simp_all hC hZ hZ12 by_omega
    by_omega
  set D := emitted (dedupF n ztyev
    ztkwf) n with hD
  have hDl : D.length ≤ n := emitted_length_le _ _
  have K3 : ∀ r, BDB r = false → r ≠ 60010 → r ≠ 60003 → r ≠ 60014 → r ≠ 60008 →
      c₃.nreg r = c₁.nreg r := fun r a b d e f => by_grind
  refine ⟨c₃, _, .seq e₁ ztcr, by_omega, fun r hr hra => ?_, fun r hr => ?_,
    fun a ha => ?_, fun a ha => by rw [rm₃, F₁.2.2.2.1 a by_omega],
    by rw [o₃, F₁.2.2.2.2], ?_, ?_, ?_, ?_, ?_, D, ?_, hDl, pairs₃, dedup_nodup hsort,
    fun x => mem_dedup hsurj hlt⟩
  · zuegm

    rw [K3 r ztkus by_omega by_omega
      by_omega by_omega, F₁.1 r hr hra]
  · zuegm

    rw [rr₃ r ztkus]
    exact F₁.2.1 r hr
  · rw [mem₃ a by_omega]
    exact F₁.2.2.1 a by_omega
  · zunmm; omega
  · zunmm; grind
  · rw [K3 _ by_decide by_decide by_decide by_decide by_decide, v1]
  · rw [K3 _ by_decide by_decide by_decide by_decide by_decide, v2]
  · rw [r₃ _ by_decide by_decide by_decide by_decide]; zumxp; config_simp; exact v3
  omega
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
theorem robust_addrF {E : ℕ} {m : ℕ → ℕ} {f : ztjx → ℕ} {v : ℕ}
    (hf : ∀ m', (∀ a, a < E → m' a = m a) → f m' = f m)
    (h : Robust E m fun m' => m' (f m') = v) : f m < E := by
  zucux
  have hm' : ∀ a, a < E → Function.update m ztvqf ztsp a = m a := fun a ha => by
    grind
  have := h _ hm'
  simp_all
variable {m m' : ℕ → ℕ} {P : Polygon}
/-- A host layout depends only on the memory below its end. -/
theorem hostAt_agree {B E : ℕ} {H : Host} (h : HostAt m B H)
    (hE : B + 3 * H.length + 4 ≤ E) (hm : ∀ a, a < E → m' a = m a) : HostAt m' B H := by
  zuko

/-- A chain descriptor depends only on the memory below its end. -/
theorem chainDescAt_agree {D X : ℕ} {Q : Polygon} {H : Host} {C : Chain}
    (h : ChainDescAt m D Q H C) (hD : D + 5 ≤ X) (hH : m D + 3 * H.length + 4 ≤ X)
    (hm : ∀ a, a < X → m' a = m a) : ChainDescAt m' D Q H C := by
  zubhb
  refine ⟨?_, h1, by_grind, by_grind,
    by grind, by_grind⟩
  zukuy
  exact hostAt_agree h0 hH hm

/-- A copy of a chain descriptor describes the same chain. -/
theorem chainDescAt_copy {m : ℕ → ℕ} {D D' : ℕ} {Q : Polygon} {H : Host} {C : Chain}
    (h : ChainDescAt m D Q H C) (hc : ∀ i, i < 5 → m (D' + i) = m ztbyg) :
    ChainDescAt m D' Q H C := by
  zubhb
  have e0 := hc 0 by_omega; have e1 := hc 1 by_omega; have e2 := hc 2 by_omega
  have e3 := hc 3 by_omega; have e4 := hc 4 by_omega
  zufba
  exact ⟨by_simp_all, h1, by_omega, by_omega, by_omega,
    by simp_all⟩

/-- A well-formed chain descriptor stays well formed under a change above the bound. -/
theorem chainWF_agree {m m' : ℕ → ℕ} {D X : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P X m D) (hD : ChainDescAt m D zta H C)
    (hm : ∀ a, a < X → m' a = m a) : ChainWF P X m' D := by
  obtain ⟨hDX, hall⟩ := hwf
  zueat
  refine ⟨hDX, fun H' C' hC' => ?_⟩
  have hD' := chainDescAt_agree hD hDX h3 hm
  zudnm

  grind

/-- **The model descriptor** made of `0` and a copy of a well-formed chain descriptor. -/
theorem modelDesc_of {m : ℕ → ℕ} {D MD X : ℕ} {H : Host} {C : Chain}
    (hD : ChainDescAt m D zta H C) (hwf : ChainWF P X m D) (h0 : m MD = 0)
    (hc : ∀ i, i < 5 → m ztged = m ztbyg) (hMX : MD + 6 ≤ X) :
    ModelDescAt m MD zta ztc ∧ ModelDescWF P X m MD := by
  have hD' : ChainDescAt m ztki zta H C := chainDescAt_copy hD hc
  refine ⟨Or.inl ⟨h0, H, C, hD', rfl⟩, hMX, fun _ => ztgoe⟩
  zudnm

  subst hH hC
  have e0 : m ztki = m D := by have := hc 0 by_omega; omega
  obtain ⟨h1, h2, h3, h4⟩ := hwf.2 H' C' hD
  simp_all

/-- The region table of the star chords from the normal form. -/
theorem rgMem_of {m : ℕ → ℕ} {B : ℕ} {M : Model} {Q : Polygon} {N : NF} (hNF : NFAt m B N)
    (hN : IsNF M Q N) :
    RgMem m ztbaie (m ztcsw) N.arcs.length ztijr
      ztgji :=
  ⟨fun p hp => hNF.2.2.2.2.2.2.2.2.1 p ztlgr,
    fun p hp => NFLoc.seq_lt hN hp, fun j hj => (hNF.2.2.2.2.2.2.1 j hj).1⟩

/-- **The locator facts of the zipper** from the descriptors and tables of phase A. -/
theorem zloc_of {W : ℕ} {m₀ m : ℕ → ℕ} {D NB MD TB L A₀ X : ℕ} {H : Host}
    {C : Chain} {N : NF} {V : QV} (hHW : hostWords P.n ≤ W) (hsimp : C.P.Simple)
    (hD : ChainDescAt m₀ D zta H C) (hwf : ChainWF P A₀ m₀ D)
    (hNFw : NFWithin m₀ NB A₀ N) (hN : IsNF ztc zta N)
    (hagree : ∀ a, a < A₀ → m a = m₀ a) (hmd0 : m MD = 0)
    (hmdc : ∀ i, i < 5 → m ztged = m₀ ztbyg) (hA₀MD : A₀ ≤ MD) (hMD6 : MD + 6 ≤ TB)
    (htab : ∀ j, j < L → m ztjnh = 2 ^ j) (hAlt : N.arcs.length < 2 ^ L)
    (hTBX : TB + L ≤ X) (hXW : X ≤ W)
    (hVMD : V.MD = MD) (hVNB : V.NB = NB) (hVTB : V.TB = TB) (hVL : V.L = L)
    (hVA : V.A = N.arcs.length) (hVAB : V.AB = m₀ ztcth) (hVSB : V.SB = m₀ ztcti)
    (hVμ : N.arcs.length ≤ V.μ) :
    Robust X m fun m' => LocMemOK P V m' W ztc N ∧ m' ztfos = V.AB ∧
      m' ztfot = V.SB := by
  zubxa
  zuc
  have agree0 : ∀ a, a < A₀ → m' a = m₀ a := fun a ha => by
    grind
  have hA0 := OracleR.arcs_pos hsimp hN
  obtain ⟨hNB7, hABb, hSBb⟩ := NFLoc.nfWithin_bounds hNFw hN hA0
  have hNF' : NFAt m' NB N := hNFw m' agree0
  zueav
  zueat
  have hD' : ChainDescAt m' D zta H C := chainDescAt_agree hD hDA h3 agree0
  have hwf' : ChainWF P X m' D :=
    ChainWF.mono (chainWF_agree ztont hD agree0) by_omega
  obtain ⟨hmd, hmdwf⟩ := modelDesc_of (m := m') (MD := MD) hD' hwf'
    by_grind
    ztbmx by_omega
  obtain ⟨hMDW, hlwf⟩ := NFLoc.locChainWF_of hmdwf hXW hHW
  have e4 : m' ztcth = m₀ ztcth := agree0 _ by_omega
  have e6 : m' ztcti = m₀ ztcti := agree0 _ by_omega
  refine ⟨⟨by_simp_all, Or.inl ⟨C, hsimp, rfl⟩, by_omega,
    by simp_all, by_simp_all, hN, hVA, fun j hj => ?_,
    fun j hj => by_grind,
    by simp_all, by_omega,
    by grind, by_grind,
    by omega, by_omega⟩, by_simp_all,
    by simp_all⟩
  zubtu
  simp_all
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
def stores : List ℕ → Stmt
  | [] => .skip
  | r :: L => .seq ztjpn ztwfe
variable {P : Polygon} {W : ℕ} {c : Config}
theorem stores_exec (L : List ℕ) {c : Config} (hw : WordsBounded W c)
    {p : ℕ} (hp : c.nreg 110005 = p) (h1 : c.nreg 120011 = 1) (hL : ∀ r ∈ L, r ≠ 110005)
    (hW : p + L.length ≤ W) :
    ∃ c' k, Exec P W ztwfe c c' k ∧ k = 2 * L.length ∧ c'.nreg 110005 = p + L.length ∧
      (∀ r, r ≠ 110005 → c'.nreg r = c.nreg r) ∧
      (∀ i, i < L.length → c'.nmem (p + i) = c.nreg ztszd) ∧
      (∀ a, (a < p ∨ p + L.length ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  induction L generalizing c p with
  | nil =>
    exact ⟨c, 0, .skip hw, rfl, by_omega, fun _ _ => rfl, fun i hi => by_simp_all,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | cons r L ih =>
    have hr : r ≠ 110005 := hL r by_simp
    obtain ⟨c₁, k₁, e₁, hk₁, v5, R₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
        ztjpn c c₁ k₁ ∧ k₁ = 2 ∧
        c₁.nreg 110005 = p + 1 ∧ (∀ r', r' ≠ 110005 → c₁.nreg r' = c.nreg r') ∧
        c₁.nmem = upd c.nmem p ztfgx ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧
        c₁.output = c.output := by
      exec_block
      · grind
      · refine ⟨rfl, by config_simp; omega, fun r' hr' => ?_, by_grind,
          rfl, rfl, rfl⟩
        config_simp; rw [upd_other _ _ _ hr']
    obtain ⟨c₂, k₂, e₂, hk₂, v5', R₂, m₂, m₂', rr₂, rm₂, o₂⟩ := ih e₁.wb_right v5
      by_grind (fun r' hr' => hL r' by_grind)
      by_grind
    refine ⟨c₂, _, .seq e₁ e₂, by_grind, by_grind,
      fun r' hr' => by_grind, fun i hi => ?_, fun a ha => ?_,
      by grind, by_grind, by_grind⟩
    · zukna
      · rw [Nat.add_zero, m₂' p ztec, m₁]; simp
      · zujnr
        have hj : ztsjn := by_omega
        have := m₂ j hj
        rw [show p + 1 + j = p + ztl by omega] at this
        rw [this, List.getD_cons_succ]
        have hmem : L.getD j 0 ∈ L := by
          zuofp; simp
        grind
    · simp at ha
      rw [m₂' a by_omega, m₁, upd_other _ _ _ by_omega]

/-- The registers of the header, in order. -/
def hdrRegs : List ℕ :=
  [120013, 120014, 120049, 9999, 120030, 120031, 130004, 130005, 60100, 60102, 60007, 60110,
    120038, 120039, 120040, 120041, 120042, 60034]

/-- **The header** at the allocator (address in `110003`). -/
def hdrS : Stmt :=
  .seq (block [.copyN 110003 9999, .constN 110004 18, .addN 9999 9999 110004, .copyN 110005 110003])
    (stores hdrRegs)
theorem hdrS_exec (hw : WordsBounded W c) {O : ℕ}
    (hAl : c.nreg 9999 = O) (h1 : c.nreg 120011 = 1) (hW : O + 18 ≤ W) :
    ∃ c' k, Exec P W hdrS c c' k ∧ k = 40 ∧ c'.nreg 110003 = O ∧ c'.nreg 9999 = O + 18 ∧
      (∀ r, r ≠ 110003 → r ≠ 110004 → r ≠ 110005 → r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      (∀ i, i < 18 → i ≠ 3 → c'.nmem ztnnn = c.nreg (hdrRegs.getD i 0)) ∧
      c'.nmem ztnnm = O + 18 ∧
      (∀ a, (a < O ∨ O + 18 ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a3, a9, a5, R₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.copyN 110003 9999, .constN 110004 18, .addN 9999 9999 110004,
        .copyN 110005 110003]) c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 110003 = O ∧ c₁.nreg 9999 = O + 18 ∧
      c₁.nreg 110005 = O ∧
      (∀ r, r ≠ 110003 → r ≠ 110004 → r ≠ 110005 → r ≠ 9999 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · omega
    · simp_all
    simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, v5, R₂, mm, mo, rr₂, rm₂, o₂⟩ := stores_exec (P := P) hdrRegs
    e₁.wb_right a5 by_simp_all
    by_decide by_tauto
  have hl : hdrRegs.length = 18 := rfl
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, by_simp_all,
    by simp_all, fun r a b d e => by_simp_all,
    fun i hi h3 => ?_, ?_, fun a ha => by_simp_all,
    by simp_all, by_simp_all, by_simp_all⟩
  · rw [mm i by_omega]
    have hne : hdrRegs.getD i 0 ≠ 110003 ∧ hdrRegs.getD i 0 ≠ 110004 ∧
        hdrRegs.getD i 0 ≠ 110005 ∧ hdrRegs.getD i 0 ≠ 9999 := by
      interval_cases i <;> simp_all [hdrRegs]
    grind
  · rw [mm 3 by_omega]
    tauto

/-! ## The payment of the allocator -/

/-- **The payment**: `ALLOC - A₀` rounds of a counting loop (`A₀` in `120026`). -/
def payS : Stmt := .seq (.instr (.subN 110008 9999 120026)) (forS 110009 110008 120011 .skip)
theorem payS_exec (hw : WordsBounded W c) {A₀ E : ℕ}
    (h26 : c.nreg 120026 = A₀) (hAl : c.nreg 9999 = E) (h1 : c.nreg 120011 = 1) :
    ∃ c' k, Exec P W payS c c' k ∧ k ≤ 3 * (E - A₀) + 4 ∧ E - A₀ ≤ k ∧
      (∀ r, r ≠ 110008 → r ≠ 110009 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have e₁ := Exec.subN (P := P) hw 110008 9999 120026
  set c₁ : Config := { c with nreg := upd c.nreg 110008 (c.nreg 9999 - c.nreg 120026) } with hc₁
  have v8 : c₁.nreg 110008 = E - A₀ := by_simp_all
  have R₁ : ∀ r, r ≠ 110008 → c₁.nreg r = c.nreg r := fun r hr => by
    simp_all
  let I : ℕ → Config → Prop := fun _ d => WordsBounded W d ∧ d.nreg 110008 = E - A₀ ∧
    d.nreg 120011 = 1 ∧ (∀ r, r ≠ 110009 → d.nreg r = c₁.nreg r) ∧ d.nmem = c₁.nmem ∧
    d.rreg = c₁.rreg ∧ d.rmem = c₁.rmem ∧ d.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, ⟨-, -, -, R₂, m₂, rr₂, rm₂, o₂⟩, -, hn⟩ := forS_exec (P := P) (W := W)
    (ri := 110009) (rn := 110008) (r1 := 120011) (body := .skip) by_decide by_decide
    (n := E - A₀) (κ := 0) I
    (fun i d h => ztcbv)
    (fun i d v h hw' => ⟨hw', by_tauto, by_tauto,
      fun r hr => by simp only; zunhy; grind,
      h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩)
    (fun i d _ h hri => ⟨d, 0, .skip h.1, le_rfl, hri, h⟩)
    e₁.wb_right (by rw [← v8]; exact e₁.wb_right.1 _)
    (fun d hwd h0 hr hm hrr hrm ho => ⟨hwd, by_simp_all,
      by simp_all, fun r hr' => hr r hr', hm, hrr, hrm, ho⟩)
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, by_omega, fun r a b => by_simp_all, m₂,
    rr₂, rm₂, o₂⟩
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
def setB : Stmt :=
  block [.addN 60034 120030 120048, .addN 60034 60034 120011, .addN 60037 60034 60003]

/-- **Phase B.** -/
def phB : Stmt := .seq starStage (.seq zipStage (.seq dedupStage setB))

/-- The bands of phase B. -/
def bBands : Finset ℕ := {bSign, bSort, bLocate, bDecomp, bOPrep, bOQuery}
variable {r : ℕ}
theorem BZS_const (h1 : 120010 ≤ r) (h2 : r ≤ 120049) : BZS r = false := by
  simp only [BZS, BZB, BPR, BLS, BL, NFLoc.Bdir, NFLoc.Bloc, Bcmp, Bk, Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  omega
theorem BSP_const (h1 : 120010 ≤ r) (h2 : r ≤ 120049) : BSP r = false := by
  simp only [BSP, BSA, BKI, BLZ, BTS, BL, NFLoc.Bdir, NFLoc.Bloc, Bcmp, Bk, BEm, BG, Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  omega
theorem sortCost_mono (κ : ℕ) {a b : ℕ} (h : a ≤ b) : SortR.sortCost κ a ≤ SortR.sortCost κ b := by
  unfold SortR.sortCost
  have := Nat.clog_mono_right 2 h
  gcongr
set_option maxHeartbeats 8000000 in
theorem phB_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) {H : Host} {C : Chain} {N : NF} {m₀ : ℕ → ℕ} {D NB A₀ : ℕ}
    (hCQ : C.P = Qof P) (hsl : C.s < C.P.n)
    (hD : ChainDescAt m₀ D zta H C) (hwf : ChainWF P A₀ m₀ D)
    (hNFw : NFWithin m₀ NB A₀ N) (hN : IsNF ztc zta N)
    (hagree : ∀ a, a < A₀ → c.nmem a = m₀ a)
    (PL : PLoaded P D NB C.s C.m C.topIdx (m₀ ztcel) N.arcs.length N.chords.length
      (m₀ ztclt) (m₀ ztcth) (m₀ ztceq) (m₀ ztcti) (m₀ ztctj) c)
    (h205 : c.nreg 110205 = 3) (hpk : PosK P.n C.s C.m ztboi ztvcn c)
    (hMD0 : c.nmem (c.nreg 120040) = 0)
    (hmdc : ∀ i, i < 5 → c.nmem (c.nreg 120040 + 1 + i) = m₀ ztbyg)
    (hA₀MD : A₀ ≤ c.nreg 120040) (hTB : c.nreg 120041 = c.nreg 120040 + 6)
    (htab : ∀ j, j < c.nreg 120042 → c.nmem (c.nreg 120041 + j) = 2 ^ j)
    (hAlt : N.arcs.length < 2 ^ c.nreg 120042) {A₁ : ℕ} (hAl : c.nreg 9999 = A₁)
    (hTBA : c.nreg 120041 + c.nreg 120042 ≤ A₁)
    (hroom : A₁ + N.regions.length + 20 * N.arcs.length + 60 +
      SortR.sortCost 20 ztgce ≤ W) :
    ∃ c' k, Exec P W phB c c' k ∧
      k ≤ 2 * N.arcs.length * (5500 * ztrlk + 410) +
        3 * (5500 * ztrlk + 262) + 150 * N.arcs.length + 600 +
        SortR.sortCost 20 ztgce ∧
      GF bBands A₁ c c' ∧ ztdbb ∧
      A₁ ≤ c'.nreg ALLOC ∧
      c'.nreg ALLOC ≤ A₁ + N.regions.length + 12 * N.arcs.length + 30 +
        SortR.sortCost 20 ztgce ∧
      ∃ CH1 CH2 : ℕ, ∃ Dl : List ztw,
        A₁ ≤ CH1 ∧ c'.nreg 60001 = CH1 ∧ c'.nreg 60002 = CH2 ∧
        c'.nreg 60008 = (starList ztffv N.arcs.length).length ∧
        c'.nreg 60034 = N.arcs.length + 3 ∧
        c'.nreg 60037 = N.arcs.length + 3 + (starList ztffv N.arcs.length ++ Dl).length ∧
        PairsAt c'.nmem CH1 CH2 (starList ztffv N.arcs.length ++ Dl) ∧
        CH1 + (starList ztffv N.arcs.length ++ Dl).length ≤ CH2 ∧
        CH2 + (starList ztffv N.arcs.length ++ Dl).length ≤ c'.nreg ALLOC ∧
        Dl.Nodup ∧ (∀ x, x ∈ Dl ↔ x ∈ OracleQ.zipRaw C zta N) ∧
        Dl.length ≤ 2 * N.arcs.length + 5 := by
  zuhp
  zuc
  zulm
  zuyo

  have hNFc : NFAt c.nmem NB N := hNFw c.nmem hagree
  zucme
  zubb
  have hW8 : ztiya := by unfold hostWords at hHW; omega
  set MD := c.nreg 120040 with hMDdef
  set L := c.nreg 120042 with hLdef
  -- 1. the star chords
  have e4 : c.nmem _ = m₀ ztcth := hagree _ by_omega
  have e6 : c.nmem _ = m₀ ztcti := hagree _ by_omega
  have hM := rgMem_of hNFc hN
  rw [e4, e6] at hM
  obtain ⟨-, -, -, hAo⟩ := NFLoc.isNF_arcs hN
  have hρR : ∀ p, p < N.arcs.length →
      ztgji (ztijr p) < N.regions.length := fun p hp => by
    zubxu
    exact (hA.1 _ ztctk).1
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, a9₁, b72, b73, b74, pairs₁⟩ := starStage_exec (P := P) hw hM PL.rNB
    PL.two hNFc.2.2.1 PL.rAB PL.rSB PL.rA PL.one hAl by_omega by_omega by_omega hρR
    ztqgi
  have hstar : starList (fun q => ztgji (ztijr q))
      N.arcs.length = starList ztffv N.arcs.length := rfl
  rw [hstar] at b74 pairs₁
  have K₁ : ∀ r, (BFR r || BIS r) = false → c₁.nreg r = c.nreg r := F₁.1
  have k12₁ : ∀ r, 120010 ≤ r → r ≤ 120049 → c₁.nreg r = c.nreg r := fun r a b => K₁ r (by
    zunpw; omega)
  have PL₁ := PL.congr fun r hr => k12₁ r zteql
    zteql
  -- 2. the zipper
  have mem₁ := F₁.2.2.1
  set V : QV := { qvOf c₁ with μ := N.arcs.length + 3 } with hV
  have hVMD : V.MD = MD := k12₁ _ by_norm_num by_norm_num
  have hVTB : V.TB = MD + 6 := by
    show c₁.nreg 120041 = _; grind
  have hVL : V.L = L := k12₁ _ by_norm_num by_norm_num
  have hVA : ztscy := PL₁.rA
  have hZ : ZEnv P W A₁ C N V c₁ :=
    { good := hG
      hW := hW8
      CQ := hCQ
      simple := hsimp
      s_lt := by_grind
      isNF := hN
      loc := zloc_of hHW hsimp hD hwf hNFw hN
        ztxl
        by_grind
        ztbmx hA₀MD le_rfl
        (fun j hj => by rw [mem₁ _ by_omega, ← hTB]; grind) hAlt
        by_omega by_omega hVMD PL₁.rNB hVTB hVL hVA PL₁.rAB PL₁.rSB by_grind
      pk := hpk.congr fun r hr => K₁ r (by
        zunpw; omega)
      rMD := rfl
      rNB := rfl
      rTB := rfl
      rL := rfl
      rA := rfl
      rAB := rfl
      rSB := rfl
      r3 := by rw [K₁ _ by_decide]; omega }
  set A₃ := A₁ + N.regions.length + 2 * chCap N.arcs.length with hA₃
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, a9₂, z93, z94, z95, pairsZ, -⟩ := zipStage_exec (P := P)
    e₁.wb_right hZ a9₁ by_omega (by rw [hVA]; unfold zCap chCap at *; omega)
  rw [hVA] at a9₂ z94 pairsZ hk₂
  rw [hVL] at hk₂
  have K₂ : ∀ r, (BZS r || BSP r) = false → c₂.nreg r = c₁.nreg r := F₂.1
  have k12₂ := fun r a b => K₂ r (by
    rw [BZS_const a b, BSP_const a b]; rfl)
  have hnraw : (OracleQ.zipRaw C zta N).length ≤ 2 * N.arcs.length + 5 := by
    unfold OracleQ.zipRaw
    have := emitted_length_le ztxna N.arcs.length
    have := emitted_length_le ztxmz N.arcs.length
    have : ztykt := by
      unfold OracleQ.zipSp OracleQ.zipSpO
      exact (List.length_filterMap_le _ _).trans by_simp
    zufaz
  have hnI : (starList ztffv N.arcs.length).length ≤ N.arcs.length := starList_length _ _
  -- 3. the deduplication
  set n := (OracleQ.zipRaw C zta N).length with hn
  set nI := (starList ztffv N.arcs.length).length with hnIdef
  set CH1 := A₁ + N.regions.length with hCH1
  set CH2 := A₁ + N.regions.length + chCap N.arcs.length with hCH2
  have hsc := sortCost_mono 20 hnraw
  have hchc : chCap N.arcs.length = 3 * N.arcs.length + 5 := rfl
  have hzc : zCap N.arcs.length = 2 * N.arcs.length + 5 := rfl
  obtain ⟨c₃, k₃, e₃, hk₃, r₃, rr₃, mem₃, rm₃, o₃, al3a, al3b, v1, v2, v8, Dl, cnt, hDl, pairsD,
      hnd, hmem⟩ := dedupStage_exec (P := P) e₂.wb_right (CH1 := CH1) (CH2 := CH2) (nI := nI)
    ztfph ztfph
    ztfph z93 z94 z95
    (by zuofr; exact PL₁.one)
    (by zuofr; exact PL₁.zero) a9₂
    by_omega by_omega by_omega
    by_omega by_omega
    by_omega
  have k12₃ : ∀ r, 120010 ≤ r → r ≤ 120049 → c₃.nreg r = c.nreg r := fun r a b => by
    rw [r₃ r ztdgx by_omega,
      k12₂ r a b, k12₁ r a b]
  -- 4. the numbers of the book
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, w34, w37⟩ : ∃ c₄ k₄, Exec P W setB c₃ c₄ k₄ ∧ k₄ = 3 ∧
      FrameB ztzfl c₃ c₄ ∧
      c₄.nreg 60034 = N.arcs.length + 3 ∧ c₄.nreg 60037 = N.arcs.length + 3 + ztttx := by
    have hwr : wr ztzfl setB = true := by_decide
    suffices H : ∃ c₄ k₄, Exec P W setB c₃ c₄ k₄ ∧ k₄ = 3 ∧ c₄.nreg 60034 = N.arcs.length + 3 ∧
        c₄.nreg 60037 = N.arcs.length + 3 + ztttx by
      zudeg

    zubj
    have g30 : c₃.nreg 120030 = N.arcs.length := by rw [k12₃ _ by_norm_num by_norm_num, PL.rA]
    have g48 : c₃.nreg 120048 = 2 := by rw [k12₃ _ by_norm_num by_norm_num, PL.two]
    have g11 : zthos := by rw [k12₃ _ by_norm_num by_norm_num, PL.one]
    unfold setB
    exec_block
    · grind
    · config_simp; grind
    · config_simp; grind
    · exact ⟨rfl, by config_simp; omega, by config_simp; omega⟩
  have ex : Exec P W phB c c₄ _ := .seq e₁ ztcb
  have hA₄ : A₃ + 2 * zCap N.arcs.length = A₃ + 4 * N.arcs.length + 10 := by_grind
  have k12₄ : zthpg := fun r a b => by
    have h4 : ztbahi = false := by
      zujoi
    rw [F₄.1 r h4, k12₃ r a b]
  refine ⟨c₄, _, ex, ?_, ?_, k12₄, ?_, ?_, CH1, CH2, Dl, by_omega, by rw [F₄.1 _ by_decide, v1],
    by rw [F₄.1 _ by_decide, v2], by rw [F₄.1 _ by_decide, v8], w34,
    by rw [w37, List.length_append], ?_, ?_, ?_, hnd, fun x => ?_, by_omega⟩
  · omega
  · -- the frame
    have hband : ∀ r, ztndx → bandOf r ∈ bBands := by
      intro r h; simp only [bBands, Finset.mem_insert, Finset.mem_singleton, bOPrep, bOQuery,
        bandOf]; omega
    have G₁ := PF.gf F₁ (fun r hr => by
        simp only [BFR, BIS, Bool.or_eq_true, decide_eq_true_eq] at hr
        zujsv
        · omega
        · left; exact hband r by_omega)
      (fun r => exec_rframeS e₁ (B := fun _ => false) by_decide r rfl) le_rfl
    have hrr₂ : ∀ r, Bk r = false → c₂.rreg r = c₁.rreg r := exec_rframeS e₂ by_decide
    have G₂ : GF bBands A₁ c₁ c₂ :=
      ⟨fun r hr hra => F₂.1 r (by
          by_contra h'; simp only [Bool.not_eq_false] at h'
          simp only [BZS, BZB, BPR, BLS, BL, NFLoc.Bdir, NFLoc.Bloc, Bcmp, Bk, BSP, BSA, BKI, BLZ, BTS, BEm, BG,
            Bool.or_eq_true, decide_eq_true_eq] at h'
          zuhbg
          simp only [bBands, Finset.mem_insert, Finset.mem_singleton, bSign, bLocate, bOPrep,
            bOQuery, bSort, bDecomp, bandOf]
          zugzy
          omega),
        fun r hr => hrr₂ r (by
          simp only [Bk, decide_eq_false_iff_not]; intro h
          exact hr (by simp only [bBands, Finset.mem_insert, Finset.mem_singleton, bSign, bandOf]
                       omega)),
        fun a ha => F₂.2.2.1 a by_omega, fun a ha => F₂.2.2.2.1 a by_omega, F₂.2.2.2.2⟩
    have G₃ : GF bBands A₁ c₂ c₃ :=
      ⟨fun r hr hra => r₃ r (fun h => hr (by
          zughn
          zunwg; tauto)) hra,
        fun r hr => rr₃ r (fun h => hr (by
          zughn
          zunwg; tauto)),
        fun a ha => mem₃ a ztec, fun a ha => rm₃ a by_omega, o₃⟩
    have hb6 : ∀ r, bandOf r ∉ bBands → ztbahi = false := by
      zuz
      have : bandOf r ≠ 6 := fun h => hr (by simp [bBands, bDecomp, h])
      unfold bandOf at this
      zujoi
    have G₄ : GF bBands A₁ c₃ c₄ :=
      ⟨fun r hr _ => F₄.1 r zttne, fun r hr => F₄.2.1 r zttne,
        fun a _ => by zuozz, fun a _ => by rw [F₄.2.2.2.1], F₄.2.2.2.2⟩
    exact G₁.trans (G₂.trans (G₃.trans G₄))
  · zvnek at al3a; zunzt; omega
  · zvnek at al3b; zunzt; omega
  · refine PairsAt.append ztjwn ?_
    · rw [F₄.2.2.1, mem₃ _ by_omega, mem₃ _ by_grind, F₂.2.2.1 _ by_omega, F₂.2.2.1 _ by_omega]
      zulzj
    · zuozz; omega
  · zukpn
  · zvnek at al3a; rw [List.length_append, hAL, F₄.1 _ by_decide]; omega
  · rw [hmem x]
    constructor
    · zuin
      zugql
      rw [z93, z94] at *
      zukyd
      zuhjy
      simp
    · zuetb
      obtain ⟨i, hi, e⟩ := List.getElem_of_mem hx
      zuifc
      zugql
      rw [p1, p2, NFLoc.getD_of_lt _ hi, e]
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleBook OracleBook.BookData
@[expose] public section
structure ClFacts (m : ℕ → ℕ) (B : BookData) (FL LAB k : ℕ) : Prop where
  k_pos : 1 ≤ k
  μ_le : B.N ≤ k ^ 3
  k_min : k = 1 ∨ ztie ^ 3 < B.N
  card : ((Finset.range B.N).filter fun v => m ztcen = 1).card ≤ 7 * k ^ 2
  hlab : ∀ u v (w : (OracleQ.bookGraph B).Walk u v), (∀ x ∈ w.support, m (FL + x) ≠ 1) →
    m (LAB + u) = m ztszg
  clus : ∀ l, ((Finset.range B.N).filter fun v => m ztcen ≠ 1 ∧ m ztszg = l).card ≤ k ^ 2
theorem ClFacts.mono {m m' : ℕ → ℕ} {B : BookData} {FL LAB k X : ℕ} (h : ClFacts m B FL LAB k)
    (hX : ∀ a, a < X → m' a = m a) (hFL : FL + B.N ≤ X) (hLAB : LAB + B.N ≤ X) :
    ClFacts m' B FL LAB k where
  k_pos := h.k_pos
  μ_le := h.μ_le
  k_min := h.k_min
  card := by
    refine le_trans ztkad h.card
    zulwq
  hlab u v w hw := by
    rw [hX _ by_omega, hX _ by_omega]
    exact h.hlab u v w fun x hx => by
      grind
  clus l := by
    refine le_trans ztkad ztvrs
    zulwq

/-- The trivial cluster facts: every node in `D*`, `k = 2` (at most `8` nodes, at least `2`). -/
theorem ClFacts.triv {m : ℕ → ℕ} {B : BookData} {FL LAB : ℕ} (h2 : 2 ≤ B.N) (h8 : B.N ≤ 8)
    (hfl : ∀ v, v < B.N → m ztcen = 1) : ClFacts m B FL LAB 2 where
  k_pos := by_norm_num
  μ_le := by_omega
  k_min := by_omega
  card := by
    grind
  hlab u v w hw := absurd by_simp_all (hw u w.start_mem_support)
  clus l := by
    rw [Finset.card_eq_zero.2]
    · omega
    simp_all

/-! ## The trivial decomposition -/

/-- The fill body: address `base + v`, value in `rv0`. -/
def fillBody (rb rv0 : ℕ) : Stmt := block [.addN 60094 rb 60093, .copyN 60095 rv0]

/-- **The trivial decomposition**: `FL[v] := 1`, `LAB[v] := 0`, `k := 2`. -/
def trivS : Stmt :=
  .seq (block [.copyN 130004 9999, .addN 9999 9999 60034, .copyN 130005 9999,
      .addN 9999 9999 60034, .constN 60090 2])
    (.seq (scatS 60093 60034 120011 60094 60095 (fillBody 130004 120011))
      (scatS 60093 60034 120011 60094 60095 (fillBody 130005 120012)))
variable {P : Polygon} {W : ℕ} {c : Config}
theorem fill_exec {rb rv0 : ℕ} (hrb : rb = 130004 ∨ rb = 130005)
    (hrv : rv0 = 120011 ∨ rv0 = 120012) {c : Config} (hw : WordsBounded W c) {μ b v0 : ℕ}
    (hμ : c.nreg 60034 = μ) (h1 : c.nreg 120011 = 1) (hb : c.nreg rb = b) (hv : c.nreg rv0 = v0)
    (hW : b + μ ≤ W) :
    ∃ c' k, Exec P W (scatS 60093 60034 120011 60094 60095 zttka) c c' k ∧
      k ≤ μ * 6 + 3 ∧ (∀ r, r ≠ 60093 → r ≠ 60094 → r ≠ 60095 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = scat c.nmem ztpbq ztrpv μ ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, ex, hk, r', rr', mm, rm, o, -, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 60093) (rn := 60034) (r1 := 120011) (ra := 60094) (rv := 60095) (body := fillBody rb rv0)
    (B := fun r => decide ztogn) by_decide by_decide by_decide by_decide
    by_decide (fun d => d.nreg rb = b ∧ d.nreg rv0 = v0) 0
    (fun d d' hJ hr _ => ⟨by rw [hr rb (by rcases hrb with rfl | rfl <;> decide)
        (by rcases hrb with rfl | rfl <;> decide)]; exact hJ.1,
      by rw [hr rv0 by_grind
        by_omega]; omega⟩)
    (n := μ) (κ := 2) ztpbq ztrpv (fun i _ => Nat.zero_le _)
    (fun i d hi hJ hwd hri => by
      obtain ⟨d', k, e, hk, v1, v2⟩ : ∃ d' k, Exec P W (fillBody rb rv0) d d' k ∧ k = 2 ∧
          d'.nreg 60094 = b + i ∧ d'.nreg 60095 = v0 := by
        unfold fillBody
        rcases hrb with rfl | rfl <;> rcases hrv with rfl | rfl <;>
        · exec_block
          · omega
          simp_all
      have hwr : wr (fun r => decide ztogn) zttka = true := by
        rfl
      exact ⟨d', k, e, by_omega, exec_frameB e hwr, v1, v2⟩)
    hw ⟨hb, hv⟩ hμ h1 by_omega
  refine ⟨c', k, ex, by_nlinarith, by_simp_all, ?_, mm, rm, o⟩
  exact funext fun r => exec_rframeS ex (B := fun _ => false)
    by_rfl r rfl
theorem trivS_exec (hw : WordsBounded W c) {μ A : ℕ}
    (hμ : c.nreg 60034 = μ) (h1 : c.nreg 120011 = 1) (h0 : c.nreg 120012 = 0)
    (hAl : c.nreg 9999 = A) (hW : A + 2 * μ ≤ W) (h2W : 2 ≤ W) :
    ∃ c' k, Exec P W trivS c c' k ∧ k ≤ 12 * μ + 12 ∧ c'.nreg 130004 = A ∧
      c'.nreg 130005 = A + μ ∧ c'.nreg 60090 = 2 ∧ c'.nreg 9999 = A + 2 * μ ∧
      (∀ v, v < μ → c'.nmem (A + v) = 1) ∧ zttp ∧
      (∀ r, r ≠ 130004 → r ≠ 130005 → r ≠ 9999 → r ≠ 60090 → r ≠ 60093 → r ≠ 60094 →
        r ≠ 60095 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a4, a5, a9, a90, R₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.copyN 130004 9999, .addN 9999 9999 60034, .copyN 130005 9999,
        .addN 9999 9999 60034, .constN 60090 2]) c c₁ k₁ ∧ k₁ = 5 ∧
      c₁.nreg 130004 = A ∧ c₁.nreg 130005 = A + μ ∧ c₁.nreg 9999 = A + 2 * μ ∧
      c₁.nreg 60090 = 2 ∧
      (∀ r, r ≠ 130004 → r ≠ 130005 → r ≠ 9999 → r ≠ 60090 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals first
      | (config_simp; rw [hAl, hμ]; omega)
      | (config_simp; omega)
      | omega
      | skip
    · refine ⟨rfl, by_simp_all, by_simp_all,
        by config_simp; omega, by config_simp, fun r a b d e => ?_, rfl, rfl, rfl, rfl⟩
      simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, R₂, rr₂, m₂, rm₂, o₂⟩ := fill_exec (P := P) (rb := 130004) (rv0 := 120011)
    ztp ztp e₁.wb_right (by rw [R₁ _ by_decide by_decide by_decide
      by_decide, hμ]) by_simp_all a4
    (by rw [R₁ _ by_decide by_decide by_decide by_decide, h1]) by_omega
  obtain ⟨c₃, k₃, e₃, hk₃, R₃, rr₃, m₃, rm₃, o₃⟩ := fill_exec (P := P) (rb := 130005) (rv0 := 120012)
    ztbt ztbt e₂.wb_right (by rw [R₂ _ by_decide by_decide by_decide,
      R₁ _ by_decide by_decide by_decide by_decide, hμ])
    (by rw [R₂ _ by_decide by_decide by_decide, R₁ _ by_decide by_decide by_decide
      by_decide, h1]) (by rw [R₂ _ by_decide by_decide by_decide, a5])
    (by rw [R₂ _ by_decide by_decide by_decide, R₁ _ by_decide by_decide by_decide
      by_decide, h0]) by_omega
  refine ⟨c₃, _, .seq e₁ ztcr, by_omega, ?_, ?_, ?_, ?_, fun v hv => ?_, fun a ha => ?_,
    fun r a b d e f g h => ?_, by_simp_all, by_simp_all, by_simp_all⟩
  · simp_all
  · rw [R₃ _ by_decide by_decide by_decide, R₂ _ by_decide by_decide by_decide, a5]
  · rw [R₃ _ by_decide by_decide by_decide, R₂ _ by_decide by_decide by_decide, a90]
  · rw [R₃ _ by_decide by_decide by_decide, R₂ _ by_decide by_decide by_decide, a9]
  · rw [m₃, scat_other by_grind, m₂]
    exact scat_at hv by_grind
  · rw [m₃, scat_below by_grind ha, m₂, scat_below by_grind ha, m₁]
  grind

/-! ## The clusters of the book -/

/-- **The clusters of the book**: the planar map and the cluster decomposition when there are
chords, the trivial decomposition otherwise. -/
def bookS : Stmt := .ifLtN 120012 120039 (.seq mapS clStage) trivS

/-- The bands of `bookS`. -/
def kBands : Finset ℕ := {bSort, bDecomp, bOPrep, bCluster}
set_option maxHeartbeats 8000000 in
theorem bookS_exec (hw : WordsBounded W c) (hG : GoodEnv P)
    {C : Chain} {N : NF} (hCQ : C.P = Qof P) {γ : ℕ}
    (hcan : IsCanonicalNF ztc zta N γ 4)
    {B : BookData} (hgok : OracleQ.GraphOK C zta N B) (hBN : B.N = N.arcs.length + 3)
    {CH1 CH2 A₅ : ℕ} (h1r : c.nreg 60001 = CH1) (h2r : c.nreg 60002 = CH2)
    (hI : c.nreg 60008 = B.I.length) (hμ : c.nreg 60034 = B.N) (hE : c.nreg 60037 = B.E)
    (hone : c.nreg 120011 = 1) (hzero : c.nreg 120012 = 0) (htwo : c.nreg 120048 = 2)
    (hK : c.nreg 120039 = N.chords.length) (hAl : c.nreg 9999 = A₅)
    (hP : PairsAt c.nmem CH1 CH2 ztclc) (hC1 : CH1 + (B.I ++ B.O).length ≤ A₅)
    (hC2 : CH2 + (B.I ++ B.O).length ≤ A₅)
    (hroom : A₅ + 10 * B.E + SortR.sortCost 20 ztbck + 3 * B.N + 3 + clCost B.N B.E ≤ W)
    (hPW : P.n + 3 ≤ W) (hNW : 8 * B.N + 8 ≤ W) :
    ∃ c' k, Exec P W bookS c c' k ∧
      k ≤ 400 * B.E + SortR.sortCost 20 ztbck + 30 * B.N + 150 + clCost B.N B.E ∧
      GF kBands A₅ c c' ∧ ztdbb ∧
      c'.nreg 60034 = B.N ∧ A₅ ≤ c'.nreg ALLOC ∧
      c'.nreg ALLOC ≤ A₅ + 10 * B.E + SortR.sortCost 20 ztbck + 3 * B.N + 3 + k ∧
      A₅ ≤ c'.nreg 130004 ∧ A₅ ≤ c'.nreg 130005 ∧ c'.nreg 130004 + B.N ≤ c'.nreg ALLOC ∧
      c'.nreg 130005 + B.N ≤ c'.nreg ALLOC ∧
      ClFacts c'.nmem B (c'.nreg 130004) (c'.nreg 130005) (c'.nreg 60090) := by
  zuhp
  zuiwp
  zulm
  have hBE : B.E = B.N + (B.I ++ B.O).length := by
    unfold BookData.E; grind
  by_cases hK0 : 0 < N.chords.length
  · -- the planar map and the clusters
    have hne : ztziv := by
      apply Set.nonempty_of_ncard_ne_zero
      rw [OracleR.chords_ncard hN]; omega
    have hV := OracleQ.valid_of_graphOK hsimp hN hne hgok
    obtain ⟨c₁, k₁, e₁, hk₁, F₁, al1a, al1b, h71, MP, hR⟩ := mapS_exec hw hV hμ hI h1r h2r
      hone htwo hE hAl hP hC1 hC2 by_omega
      by_omega
    have mp : ∀ r, (r = 60034 ∨ r = 60037 ∨ r = 120011) → MPres r := fun r hr => by
      zuiee
      · zuleg
      · zuleg
      · exact Or.inr by_decide
    obtain ⟨c₂, k₂, e₂, hk₂, F₂, al2a, al2b, K6₂, kpos, kcube, kmin, p4, p5, p4', p5', pcard, pwalk,
        pclus⟩ := clStage_exec e₁.wb_right rfl by_simp_all
      by_simp_all by_simp_all rfl hR hPW hNW
      by_omega
    refine ⟨c₂, _, .ifLtN_true by_omega ztyv, ?_, ?_, ?_, ?_, ?_, ?_,
      by omega, by_omega, p4', p5', ⟨kpos, kcube, kmin, pcard, pwalk, pclus⟩⟩
    · grind
    · refine (FrameN.gf (FrameN.mono F₁ by_decide) by_grind).trans
        (FrameN.gf (FrameN.mono F₂ by_decide) by_omega)
    · zumhh
      rw [F₂.1 r (by simp [bDecomp, bCluster, bandOf]; omega) by_omega,
        F₁.1 r ztdgx by_omega]
    · rw [K6₂ _ by_rfl by_omega, MP _ by_grind, hμ]
    · omega
    omega
  · -- the trivial decomposition
    have hK00 : N.chords.length = 0 := by_omega
    have hA5 : N.arcs.length ≤ 5 := by
      zujyh
      rw [regions_eq hsimp hN, hK00] at h1
      omega
    obtain ⟨c₁, k₁, e₁, hk₁, v4, v5, v90, v9, hfl, mem₁, R₁, rr₁, rm₁, o₁⟩ := trivS_exec hw
      hμ hone hzero hAl by_omega by_omega
    have hB8 : B.N ≤ 8 := by_omega
    refine ⟨c₁, _, .ifLtN_false by_omega e₁, by_omega, ?_, ?_, ?_, ?_, ?_,
      by rw [v4], by_omega, by_grind, by_grind, ?_⟩
    · refine ⟨fun r hr hra => R₁ r ?_ ?_ by_omega ?_ ?_ ?_ ?_,
        by grind, by_omega, by_grind, o₁⟩ <;>
      · zueta
    · grind
    · grind
    · grind
    · grind
    · rw [v4, v5, v90]
      exact ClFacts.triv by_omega hB8 by_omega
theorem clog_mul_le (a b : ℕ) : Nat.clog 2 zthdh ≤ Nat.clog 2 a + Nat.clog 2 b := by
  zujhc
  zulxf

/-- The unit of the costs. -/
def Fb (K : ℕ) : ℕ := ztbr * ztwoa
theorem nclog_le {n K : ℕ} (h : n ≤ 64 * ztbr) : n * ztcgv ≤ 64 * Fb K := by
  zumqu
  have := Nat.clog_mono_right 2 h
  calc n * ztcgv ≤ ztzsu * ztwoa :=
        Nat.mul_le_mul h by_omega
    _ = 64 * ztbarv := by_ring
theorem sortCost_le {κ n K : ℕ} (h : n ≤ 64 * ztbr) :
    SortR.sortCost κ n ≤ ztcxg * ztowj := by
  unfold SortR.sortCost
  have := nclog_le h
  simp_all
theorem clCost_le {μ E K : ℕ} (h : μ + E ≤ 64 * ztbr) :
    clCost μ E ≤ Cluster.clusterK * ztowj := by
  unfold clCost
  have := nclog_le h
  exact Nat.mul_le_mul_left _ by_omega
theorem clog_le_Fb {x K : ℕ} (h : x ≤ 64 * ztbr) : Nat.clog 2 x ≤ Fb K := by
  zumqu
  have := Nat.clog_mono_right 2 h
  grind
theorem mul_clog_le_Fb {a x K : ℕ} (ha : a ≤ 5 * ztbr) (h : x ≤ 64 * ztbr) :
    a * ztenn ≤ 5 * Fb K := by
  zumqu
  have := Nat.clog_mono_right 2 h
  calc a * ztenn ≤ (5 * ztbr) * ztwoa :=
        Nat.mul_le_mul ha by_omega
    _ = 5 * ztbarv := by_ring
variable (K : ℕ)
theorem one_le_Fb : 1 ≤ Fb K := by
  unfold Fb; grind
theorem K_le_Fb : K + 1 ≤ Fb K := by
  unfold Fb; simp

/-- **The unit against the budget of the specification.** -/
theorem Fb_le {K m : ℕ} (hm : 1 ≤ m) (hK : K ≤ 60 * ztfk) :
    Fb K ≤ 40 * ztjjd := by
  zumqu
  rcases Nat.eq_zero_or_pos K with rfl | hK0
  · have : Nat.clog 2 64 = 6 := by
      rfl
    simp_all
  · have h1 : 64 * ztbr ≤ 131072 * m := by_omega
    have h2 : Nat.clog 2 ztzsu ≤ 17 + Nat.clog 2 m := by
      have := Nat.clog_mono_right 2 h1
      have h3 := clog_mul_le 131072 m
      have h4 : Nat.clog 2 131072 = 17 := by
        rfl
      omega
    calc ztbr * ztwoa ≤ ztbds * (18 + Nat.clog 2 m) :=
          Nat.mul_le_mul by_omega by_omega
      _ ≤ 40 * ztjjd := by_nlinarith
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ OracleBook
@[expose] public section
def qvFin (P : Polygon) (m₀ : ℕ → ℕ) (D NB A K POS FL LAB DL nD ORD RK CH MD TB L : ℕ) : QV where
  D := D
  NB := NB
  s := m₀ ztef
  m := m₀ ztmo
  tIdx := m₀ ztclg
  β := m₀ ztcel
  sS := if m₀ ztcel = 1 then m₀ ztclg else 2 * m₀ ztmo - m₀ ztclg
  tv := ztzgn % P.n
  hz := 0
  σb := 0
  zo := none
  A := A
  POS := POS
  FL := FL
  LAB := LAB
  DL := DL
  nD := nD
  ORD := ORD
  RK := RK
  CH := CH
  K := K
  MD := MD
  TB := TB
  L := L
  CB := m₀ ztclt
  AB := m₀ ztcth
  RB := m₀ ztceq
  SB := m₀ ztcti
  LB := m₀ ztctj
  μ := A + 3

/-- The words of the header. -/
def hdrVals (D NB γ E A POS FL LAB DL nD ORD RK CH K MD TB L μ : ℕ) : List ℕ :=
  [D, NB, γ, E, A, POS, FL, LAB, DL, nD, ORD, RK, CH, K, MD, TB, L, μ]
set_option maxHeartbeats 16000000 in
/-- **The structure from the memory facts.** -/
theorem qat_of {P : Polygon} {m m₀ : ℕ → ℕ} {A₀ D NB γ O E : ℕ} {H : Host} {C : Chain}
    {N : NF} {B : BookData} {k POS FL LAB DL nD ORD RK CH MD TB L : ℕ} {Vc : QV}
    (hG : GoodEnv P) (hCQ : C.P = Qof P)
    (hD : ChainDescAt m₀ D zta H C) (hwf : ChainWF P A₀ m₀ D)
    (hNFw : NFWithin m₀ NB A₀ N) (hcan : IsCanonicalNF ztc zta N γ 4)
    (hagree : ∀ a, a < A₀ → m a = m₀ a)
    (hhdr : ∀ i, i < 18 → m ztnnn = (hdrVals D NB γ E N.arcs.length POS FL LAB DL nD ORD RK CH
      N.chords.length MD TB L ztenj).getD i 0)
    (hE : E = O + 18)
    (hCHA : A₀ ≤ CH) (hCHM : CH + N.chords.length ≤ MD) (hTB : TB = MD + 6)
    (hPOS : TB + L ≤ POS) (hPOSO : POS + N.arcs.length ≤ O)
    (hFL : FL + ztenj ≤ O) (hLAB : LAB + ztenj ≤ O)
    (hDL : DL + nD ≤ O) (hORD : ORD + ztenj ≤ O)
    (hRK : RK + ztenj ≤ O)
    (hmd0 : m MD = 0) (hmdc : ∀ i, i < 5 → m ztged = m₀ ztbyg)
    (htab : ∀ j, j < L → m ztjnh = 2 ^ j) (hAlt : N.arcs.length < 2 ^ L)
    (hKlt : N.chords.length < 2 ^ L) (hL : L = Nat.clog 2 ztbbt)
    (hpos : ∀ j, j < N.arcs.length → m ztjle < N.arcs.length ∧
      N.seq.getD (m ztjle) 0 = j)
    (hchlt : ∀ q, q < N.chords.length → m zthae < N.chords.length)
    (hchinj : ∀ q q', q < N.chords.length → q' < N.chords.length → m zthae = m ztnkd →
      q = q')
    (hVc : Vc.CB = m₀ ztclt ∧ Vc.m = m₀ ztmo ∧ Vc.s = m₀ ztef ∧
      Vc.tv = ztzgn % P.n)
    (hchsort : ∀ q q', q ≤ q' → q' < N.chords.length →
      ChLe P C Vc m₀ (m zthae) (m ztnkd))
    (hgok : GraphOK C zta N B) (hBN : B.N = N.arcs.length + 3)
    (hcl : ClFacts m B FL LAB k) (hord : OrdFacts m ztenj FL LAB DL nD ORD RK) :
    Robust E m fun m'' => ∃ V H C N B k, QAt P m'' O E V H C N B k := by
  intro m'' hm''
  zuc
  zuiwp
  have hsimp : C.P.Simple := by rw [hCQ]; exact (shearInvariance ztbhs P).1 hG.1
  zuyo

  have hNB11 : NB + 11 < A₀ := NFLoc.robust_addr (fun m' hm' => (hNFw m' hm').2.2.2.2.1)
  zueav
  obtain ⟨hHl, hHwf, hHb, hCs⟩ := hall H C hD
  have hOE : O + 18 ≤ E := by_omega
  have hA₀O : A₀ ≤ O := by_omega
  have ag0 : ∀ a, a < A₀ → m'' a = m₀ a := fun a ha => by rw [hm'' a by_omega, hagree a ha]
  have agE : ∀ a, a < O → m'' a = m a := fun a ha => hm'' a by_omega
  have hNF'' : NFAt m'' NB N := hNFw m'' ag0
  have hD'' : ChainDescAt m'' D zta H C := chainDescAt_agree hD hDA hHb ag0
  zukzh
  set K := N.chords.length with hKdef
  set V := qvFin P m₀ D NB A K POS FL LAB DL nD ORD RK CH MD TB L with hV
  have hVA : V.A = A := rfl
  have hVK : V.K = K := rfl
  have hVL : V.L = L := rfl
  have hVCH : V.CH = CH := rfl
  have hh : ∀ i, i < 18 → m'' ztnnn = (hdrVals D NB γ E A POS FL LAB DL nD ORD RK CH K MD TB L
      zttf).getD i 0 := fun i hi => by rw [hm'' _ by_omega]; exact hhdr i hi
  obtain ⟨-, -, hd1, hd2, hd3, hd4⟩ := hD
  have hcb : ∀ i, i < K → m₀ ztclt + 5 * i + 4 < A₀ := fun i hi => by
    have h1 : Robust A₀ m₀ fun m' => m' (m' ztclt + ztjfv) = (N.chord i).dn :=
      fun m' hm' => by
        have := ((hNFw m' hm').2.2.2.2.2.1 i hi).2.2.2.2
        omega
    have := (NFLoc.robust_addr2 h1).2; omega
  refine ⟨V, H, C, N, B, k, ?_⟩
  exact
    { lD := hh 0 by_norm_num
      lNB := hh 1 by_norm_num
      lE := hh 3 by_norm_num
      lA := hh 4 by_norm_num
      lPOS := hh 5 by_norm_num
      lFL := hh 6 by_norm_num
      lLAB := hh 7 by_norm_num
      lDL := hh 8 by_norm_num
      lnD := hh 9 by_norm_num
      lORD := hh 10 by_norm_num
      lRK := hh 11 by_norm_num
      lCH := hh 12 by_norm_num
      lK := hh 13 by_norm_num
      lMD := hh 14 by_norm_num
      lTB := hh 15 by_norm_num
      lL := hh 16 by_norm_num
      lμ := hh 17 by_norm_num
      O_le := hOE
      ds := by show m'' ztef = m₀ ztef; exact ag0 _ by_omega
      dm := by show m'' ztmo = m₀ ztmo; exact ag0 _ by_omega
      dt := by show m'' ztclg = m₀ ztclg; exact ag0 _ by_omega
      dβ := by show m'' ztcel = m₀ ztcel; exact ag0 _ by_omega
      sS := rfl
      tv := rfl
      desc := by_tauto
      CQ := hCQ
      simple := hsimp
      hostLen := hHl
      hostWF := hHwf
      D_le := by show D + 5 ≤ E; omega
      host_le := by show m'' D + 3 * H.length + 4 ≤ E; zuomn; omega
      s_lt := hCs
      nCB := by show m'' ztclt = m₀ ztclt; exact ag0 _ by_omega
      nAB := by show m'' ztcth = m₀ ztcth; exact ag0 _ by_omega
      nRB := by show m'' ztceq = m₀ ztceq; exact ag0 _ by_omega
      nSB := by show m'' ztcti = m₀ ztcti; exact ag0 _ by_omega
      nLB := by show m'' ztctj = m₀ ztctj; exact ag0 _ by_omega
      nf := by_tauto
      canon := by rw [hh 2 by_norm_num]; tauto
      hA := rfl
      hK := rfl
      regs := fun r hr => by
        have h1 : Robust A₀ m₀ fun m' => m' (m' ztceq + ztjfw) = (N.region r).wt :=
          fun m' hm' => by
            have := ((hNFw m' hm').2.2.2.2.2.2.2.1 r hr).2.2.1
            omega
        obtain ⟨h5, h54⟩ := NFLoc.robust_addr2 h1
        refine ⟨by show m₀ ztceq + 5 * r + 4 < E; omega, fun t ht => ?_⟩
        show m₀ ztctj + m'' ztyjs + t < E
        zuomn
        have := robust_addrF (E := A₀) (m := m₀)
          (f := fun m' => m' ztctj + m' ztyjq + t)
          (v := (N.region r).arcs.getD t 0)
          (fun m' hm' => by
            show m' ztctj + m' ztyjq + t =
              m₀ ztctj + m₀ ztyjs + t
            rw [hm' ztctj by_omega, hm' ztceq by_omega, hm' _ by_omega])
          (fun m' hm' => ((hNFw m' hm').2.2.2.2.2.2.2.1 r hr).2.2.2.1 t ht)
        grind
      pos := fun j hj => by
        rw [hVA] at hj
        show m'' ztjle < A ∧ N.seq.getD (m'' ztjle) 0 = j
        zungo; exact hpos j hj
      POS_le := by show POS + A ≤ E; omega
      gOK := hgok
      μ := hBN
      FL_le := by show FL + zttf ≤ E; omega
      LAB_le := by show LAB + zttf ≤ E; omega
      hlab := by
        have := (hcl.mono (m' := m'') (X := O) agE by_omega by_omega).hlab
        tauto
      dl := (hord.mono (m' := m'') (X := O) agE hFL hLAB hDL hORD hRK).dl
      dl_all := (hord.mono (m' := m'') (X := O) agE hFL hLAB hDL hORD hRK).dl_all
      DL_le := by show DL + nD ≤ E; omega
      nD_le := by
        show nD ≤ 7 * k ^ 2
        rw [hord.nD_eq]
        have := hcl.card; grind
      clus := fun l => by
        have := (hcl.mono (m' := m'') (X := O) agE by_omega
          by_omega).clus l
        rw [hBN] at this; tauto
      k_pos := hcl.k_pos
      μ_le := by have := hcl.μ_le; rw [hBN] at this; tauto
      μ_A := le_rfl
      k_min := by have := hcl.k_min; rw [hBN] at this; tauto
      ord_lt := (hord.mono (m' := m'') (X := O) agE hFL hLAB hDL hORD hRK).ord_lt
      ord_inj := (hord.mono (m' := m'') (X := O) agE hFL hLAB hDL hORD hRK).ord_inj
      ord_rk := (hord.mono (m' := m'') (X := O) agE hFL hLAB hDL hORD hRK).ord_rk
      ord_sorted := (hord.mono (m' := m'') (X := O) agE hFL hLAB hDL hORD hRK).ord_sorted
      ORD_le := by show ORD + zttf ≤ E; omega
      RK_le := by show RK + zttf ≤ E; omega
      ch_lt := fun q hq => by
        rw [hVK] at hq
        show m'' zthae < K; zungo; exact hchlt q hq
      ch_inj := fun q q' hq hq' e => by
        rw [hVK] at hq hq'
        rw [hVCH] at e
        rw [agE _ by_omega, agE _ by_omega] at e; exact hchinj q q' hq hq' e
      ch_sorted := fun q q' hqq hq' => by
        rw [hVK] at hq'
        show ChLe P C V m'' (m'' zthae) (m'' ztnkd)
        rw [agE _ by_omega, agE _ by_omega]
        have hs := hchsort q q' hqq hq'
        have a1 := hchlt q by_omega
        have a2 := hchlt q' hq'
        rw [chLe_V_congr (V' := V) hVc.1 hVc.2.1 hVc.2.2.1 hVc.2.2.2] at hs
        refine (chLe_congr fun x hx => ?_).1 hs
        zukgz
        have := hcb x hxK
        exact ⟨(ag0 _ (by show m₀ ztclt + 5 * x < A₀; omega)).symm,
          (ag0 _ (by show m₀ ztclt + 5 * x + 1 < A₀; omega)).symm⟩
      tab := fun j hj => by
        rw [hVL] at hj
        show m'' ztjnh = 2 ^ j; zungo; grind
      A_lt := hAlt
      K_lt := hKlt
      L_le := by
        show L ≤ Nat.clog 2 ztsus + 1
        zvnlm; exact clog_succ_le _
      TB_le := by show TB + L ≤ E; omega
      CH_le := by show CH + K ≤ TB; omega
      NB_TB := by show NB + 12 ≤ TB; omega
      AB_TB := by show m₀ ztcth + 5 * A ≤ TB; omega
      SB_TB := by show m₀ ztcti + A ≤ TB; omega
      CB_TB := fun i hi => by have := hcb i hi; show m₀ ztclt + 5 * i + 5 ≤ TB; omega
      md0 := by show m'' MD = 0; zungo; omega
      md := fun i hi => by
        show m'' ztged = m'' ztbyg
        rw [agE _ by_omega, hmdc i hi, ag0 _ by_omega]
      MD_le := by show MD + 6 ≤ E; omega }
