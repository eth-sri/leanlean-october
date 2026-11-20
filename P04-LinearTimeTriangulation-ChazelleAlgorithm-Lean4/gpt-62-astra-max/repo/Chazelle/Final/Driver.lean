module

public import Chazelle.Core.SpecAssembly
public import Chazelle.Final.RamDiag
public import Chazelle.Final.RamOrient
public import Chazelle.Final.RamOutput

/-!
# The final stage: from the visibility tables to the triangulation

`finalStmt` composes, on the configuration left by the visibility-map stage (`TablesReady Q`):

1. the layout of the scratch memory above the allocator `A = nreg 9999`
   (`M = |T| + |C|`, the diagonal band `DB = A`, heads `HB = A + 2M`, siblings `SB = HB + n`,
   the splitting work area `B = SB + M`, the marks `MB = B + 4 NN + n`, the piece work band
   `WB = MB + NN`, with `NN = n + 2 ND`);
2. `diagStmt`: the list `E` of the inserted diagonals, a permutation of `diagList Q T C`;
3. `orientStmt`: `σ = orient Q`;
4. `splitStmt`: the linked structure `runState P σ (initState n) E`, whose cycles are the pieces
   (`runState_spec` for `Q`, `runState_shear`);
5. `outStmt`: every piece triangulated once.

**Main result**: `finalStage : Chazelle.Core.FinalStageSpec`, with the constants `C = 10000`,
`K = 100`.
-/

namespace Chazelle.Final

open Machine Machine.Stmt Programs
open Chazelle.Split (EnumDiags)
open Chazelle.Mountain (orient)

@[expose] public section

/-- **The final-stage program.** -/
def finalStmt : Stmt :=
  .seq (block [.inputSize 252, .addN 253 9991 9993, .copyN 200 9999, .addN 201 200 253,
      .addN 201 201 253, .addN 202 201 252])
    (.seq diagStmt (.seq orientStmt
      (.seq (block [.addN 100 202 253, .copyN 101 200, .copyN 102 206])
        (.seq splitStmt
          (.seq (block [.copyN 240 115, .addN 241 109 252, .copyN 249 106, .copyN 250 105,
            .addN 251 241 240]) outStmt)))))

/-- Enumerations of the inserted diagonals are closed under permutation. -/
theorem EnumDiags.perm {Q : Polygon} {D D' : List (ℕ × ℕ)} (h : EnumDiags Q D)
    (hp : D.Perm D') : EnumDiags Q D' where
  sound d hd := h.sound d (hp.mem_iff.2 hd)
  complete d hd := by
    rcases h.complete d hd with h1 | h1
    · exact Or.inl (hp.mem_iff.1 h1)
    · exact Or.inr (hp.mem_iff.1 h1)
  distinct := hp.pairwise h.distinct fun {a b} hab =>
    ⟨fun e => hab.1 e.symm, fun e => hab.2 (by rw [e, Prod.swap_swap])⟩

/-- The final-stage input is no longer than the two tables together. -/
theorem diagList_length_le_tables (Q : Polygon) (T : TrapTable) (C : List ChordRec) :
    (diagList Q T C).length ≤ T.length + C.length := by
  unfold diagList
  have h1 := (List.dedup_sublist ((trapPairs Q T ++ chordPairs C).map sortPair)).length_le
  have h2 : (trapPairs Q T).length ≤ T.length := by
    unfold trapPairs; rw [List.length_map]; exact List.length_filter_le _ _
  have h3 : (chordPairs C).length = C.length := List.length_map _
  rw [List.length_map, List.length_append] at h1
  omega

set_option maxHeartbeats 4000000 in
/-- **The final stage** (`Chazelle.Core.FinalStageSpec`): from any configuration holding valid
tables of a simple polygon `Q` related to the input `P` by a shear, `finalStmt` emits a
triangulation of `Q` in at most `10000 (n + 1)` steps, using the memory `[A, A + 100 (n + 1))`
above the allocator `A`. -/
theorem finalStage : Core.FinalStageSpec := by
  classical
  refine ⟨finalStmt, 10000, 100, ?_⟩
  intro P Q hP hQ hPQ W c hc hready hroom
  obtain ⟨T, Cs, hT, hC, h9991, hTab, h9993, hCab, hTB, hCB, hout0⟩ := hready
  have hPQ' := hPQ
  obtain ⟨ε, -, hQe, hag⟩ := hPQ'
  have hQn : Q.n = P.n := hPQ.n_eq
  have hn3 : 3 ≤ P.n := hQn ▸ hQ.1
  have hTL : T.length ≤ 2 * P.n + 1 := hQn ▸ hT.length_le hQ
  have hCL : Cs.length ≤ 2 * P.n := hQn ▸ hC.length_le
  set A := c.nreg Core.ALLOC with hA
  set M := T.length + Cs.length with hM
  change c.nreg 9991 = T.length at h9991
  change c.nreg 9993 = Cs.length at h9993
  change Core.TrapTableAt c.nmem (c.nreg 9990) T at hTab
  change Core.ChordTableAt c.nmem (c.nreg 9992) Cs at hCab
  change c.nreg 9990 + 4 * T.length ≤ c.nreg 9999 at hTB
  change c.nreg 9992 + 3 * Cs.length ≤ c.nreg 9999 at hCB
  have hA' : c.nreg 9999 = A := rfl
  have hW : A + 100 * (P.n + 1) ≤ W := hroom
  have hML : M ≤ 4 * P.n + 1 := by omega
  -- 1. the layout
  unfold finalStmt
  refine spec_seq ?_
  exec_block
  · omega
  · config_simp; rw [h9991, h9993]; omega
  · config_simp; rw [hA', h9991, h9993]; omega
  · config_simp; rw [hA', h9991, h9993]; omega
  · config_simp; rw [hA', h9991, h9993]; omega
  refine spec_name fun c₁ hc₁ => ?_
  have hw₁ : WordsBounded W c₁ := by rw [hc₁]; assumption
  have r1 : ∀ r, r ≠ 200 → r ≠ 201 → r ≠ 202 → r ≠ 252 → r ≠ 253 → c₁.nreg r = c.nreg r := by
    intro r a b d e f; rw [hc₁]; config_simp
    simp only [Machine.upd_apply, a, b, d, e, f, ite_false]
  have c200 : c₁.nreg 200 = A := by rw [hc₁]; config_simp; exact hA'
  have c201 : c₁.nreg 201 = A + 2 * M := by
    rw [hc₁]; config_simp; rw [hA', h9991, h9993]; ring
  have c202 : c₁.nreg 202 = A + 2 * M + P.n := by
    rw [hc₁]; config_simp; rw [hA', h9991, h9993]; ring
  have c252 : c₁.nreg 252 = P.n := by rw [hc₁]; config_simp
  have c253 : c₁.nreg 253 = M := by rw [hc₁]; config_simp; rw [h9991, h9993]
  have m1 : c₁.nmem = c.nmem := by rw [hc₁]
  -- 2. the diagonal list
  refine spec_seq (spec_use (diagStmt_exec (P := P) (Q := Q) (W := W) hQ hQn hT hC
    (DB := A) (HB := A + 2 * M) (SB := A + 2 * M + P.n) (M := M) c₁ hw₁ c200 c201 c202
    (by rw [r1 9991 (by decide) (by decide) (by decide) (by decide) (by decide), h9991])
    (by rw [r1 9993 (by decide) (by decide) (by decide) (by decide) (by decide), h9993])
    (by rw [m1, r1 9990 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hTab)
    (by rw [m1, r1 9992 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hCab)
    (by rw [r1 9990 (by decide) (by decide) (by decide) (by decide) (by decide)]; omega)
    (by rw [r1 9992 (by decide) (by decide) (by decide) (by decide) (by decide)]; omega)
    le_rfl le_rfl (by omega) le_rfl (by omega)) ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨E, hE, h206, hband, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩
  have hED : EnumDiags Q E := EnumDiags.perm (enumDiags_diagList hQ hT hC) hE.symm
  have hElen : E.length ≤ M := hE.length_eq ▸ diagList_length_le_tables Q T Cs
  have hElen' : E.length ≤ 4 * P.n + 1 := hQn ▸ (hE.length_eq ▸ diagList_length_le hQ hT hC)
  have hElt : ∀ d ∈ E, d.1 < P.n ∧ d.2 < P.n ∧ d.1 ≠ d.2 := by
    intro d hd
    have := diagList_lt hQ hT hC (hE.mem_iff.1 hd)
    rw [hQn] at this
    exact ⟨by omega, this.2, by omega⟩
  set ND := E.length with hND
  set NN := P.n + 2 * ND with hNN
  set B := A + 2 * M + P.n + M with hB
  -- 3. the orientation
  refine spec_seq (spec_use (orientStmt_exec (P := P) (W := W) hPQ hQ c₂ hw₂ (by omega)) ?_)
  rintro c₃ k₃ hk₃ hw₃ ⟨hσ₃, hfn₃, hfr₃, hnm₃, hrm₃, hout₃⟩
  have R3 : ∀ r, (r < 203 ∨ 227 < r) → (r < 230 ∨ 236 < r) → c₃.nreg r = c₁.nreg r := by
    intro r h1 h2; rw [hfn₃ r h2, hfn₂ r h1]
  -- 4. the splitting registers
  refine spec_seq ?_
  exec_block
  · rw [R3 202 (by omega) (by omega), R3 253 (by omega) (by omega), c202, c253]; omega
  refine spec_name fun c₄ hc₄ => ?_
  have hw₄ : WordsBounded W c₄ := by rw [hc₄]; assumption
  have c4_100 : c₄.nreg 100 = B := by
    rw [hc₄]; config_simp; rw [R3 202 (by omega) (by omega), R3 253 (by omega) (by omega), c202,
      c253]
  have c4_101 : c₄.nreg 101 = A := by
    rw [hc₄]; config_simp; rw [R3 200 (by omega) (by omega), c200]
  have c4_102 : c₄.nreg 102 = ND := by
    rw [hc₄]; config_simp; rw [hfn₃ 206 (by omega), h206]
  have c4σ : c₄.rreg 100 = orient Q := by rw [hc₄]; config_simp; exact hσ₃
  have m4 : c₄.nmem = c₂.nmem := by rw [hc₄]; config_simp; exact hnm₃
  -- 5. the splitting
  have hband₄ : ∀ j < ND, c₄.nmem (A + 2 * j) = (E.getD j (0, 0)).1 ∧
      c₄.nmem (A + 2 * j + 1) = (E.getD j (0, 0)).2 := by
    intro j hj; rw [m4]; exact hband j hj
  refine spec_seq (spec_use (splitStmt_exec (P := P) (W := W) (B := B) (DB := A) (ND := ND)
    (NN := NN) (σ := orient Q) (D := E) c₄ hw₄ c4_100 c4_101 c4_102 c4σ rfl rfl hElt (by omega)
    hband₄ (Or.inl (by omega)) (by omega) (by omega)) ?_)
  rintro c₅ k₅ hk₅ hw₅ ⟨hS₅, h115, hfn₅, hfr₅, hnm₅, hrm₅, hout₅⟩
  -- 6. the output registers
  have e252 : c₅.nreg 252 = P.n := by
    rw [hfn₅ 252 (by omega), hc₄]; config_simp
    rw [R3 252 (by omega) (by omega), c252]
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hS₅.r109, e252]; omega
  · config_simp; rw [hS₅.r109, e252, h115]; omega
  refine spec_name fun c₆ hc₆ => ?_
  have hw₆ : WordsBounded W c₆ := by rw [hc₆]; assumption
  -- the structure and its cycles (for `Q`)
  set S := runState P (orient Q) (initState P.n) E with hSdef
  obtain ⟨cs, hR, hp⟩ := runState_spec hQ hED
  have hSQ : runState Q (orient Q) (initState Q.n) E = S := by
    rw [hSdef, hQn, hQe, runState_shear]
  rw [hSQ] at hR hp
  have hcnt : S.cnt = NN := by
    rw [hSdef, cnt_runState]; rfl
  have hX : OutCtx P Q W S cs NN (B + 4 * NN + P.n) (B + NN) B (B + 4 * NN + P.n + NN) :=
    { simple := hQ
      shear := ⟨ε, hQe, hag⟩
      enum := ⟨E, hED, hp⟩
      repr := hR
      cnt := hcnt
      lay1 := by omega
      lay2 := by omega
      lay3 := by omega
      lay4 := by omega }
  have m6 : c₆.nmem = c₅.nmem := by rw [hc₆]
  have hBands : Bands c₆.nmem S NN (B + NN) B := by
    intro y hy
    rw [m6]
    exact ⟨hS₅.mem.vtx y (by omega), hS₅.mem.nxt y (by omega)⟩
  refine spec_use (outStmt_exec (P := P) (W := W) hX c₆ hw₆ hBands
    (by rw [hc₆]; config_simp; exact h115)
    (by rw [hc₆]; config_simp; rw [hS₅.r109, e252])
    (by rw [hc₆]; config_simp; exact hS₅.r106)
    (by rw [hc₆]; config_simp; exact hS₅.r105)
    (by rw [hc₆]; config_simp; rw [hS₅.r109, e252, h115]) (by omega)) ?_
  rintro c₇ k₇ hk₇ hw₇ ⟨X, hX7, hout₇⟩
  refine ⟨?_, ?_⟩
  · -- the cost
    have hrc : runCost P (orient Q) (initState P.n) E ≤ 2 * 11 * E.length := by
      refine runCost_le E (initState P.n) (fun d hd => (hElt d hd).2.2) fun v => ?_
      have h1 := length_cop_init P.n v
      have h2 := countP_diagList_le hQ hT hC v
      rw [← hE.countP_eq] at h2
      omega
    have hk₂' : k₂ ≤ 202 * T.length + 174 * Cs.length + 5 * P.n + 20 := hk₂
    nlinarith
  · rw [hout₇, hc₆]
    config_simp
    rw [hout₅, hc₄]
    config_simp
    rw [hout₃, hout₂, hc₁]
    config_simp
    rw [hout0, List.nil_append]
    exact hX7

end

end Chazelle.Final
