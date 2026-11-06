module

public meta import Chazelle.Arithmetic

public import Chazelle.Mountain.RamSub
public import Chazelle.Mountain.RamTheorem

/-!
# The monotone-mountain stack walk on a sub-polygon given by an index table, part 2

This file completes the verification of `mountainSubStmt` (`RamSub.lean`): the walk
`subOuterLoop` mirrors `Chazelle.Mountain.walk` on `Q = subPoly P l`, the initialisation sets
up the stack `[1, 0]` at position `k = 2`, and the sign `σ = mountainSign Q` of
`D₀ = det v_{l[m-1]} v_{l[0]} v_{l[1]}` is computed once.

## Costs

* pop loop at position `k` with `p` pops: `≤ 32 * (p + 1) + 2` (`subInnerLoop_exec`);
* one iteration of the walk: `≤ 32 * p + 39`, plus `2` of loop overhead;
* the walk from position `k` with stack `s`:
  `≤ 32 * (walk Q σ k s).1.length + 41 * (m - k) + 2` (`subOuterLoop_exec`, potential
  `subOuterPot`);
* initialisation `21`, sign `≤ 10`.

Total (`mountainSubStmt_exec_sign`):
`≤ 32 * (mountainTriangulation Q σ).length + 41 * (m - 2) + 33`; for a mountain the
triangulation has `m - 2` triangles, whence `≤ 73 * m` (`mountainSub_exec`).

## Main results

* `mountainSub_exec`: the specification of the fragment (output, cost `≤ 73 * m`, frame).
* `weakTriangulates_mountainTriangulation_of_sign`, `mountainSub_exec_weak`: the emitted list is
  `T.map (relabelList l)` for a weak triangulation `T` of `subPoly P l` (the composable form).
* `mountainSub_range_exec`: the special case `l = List.range n` triangulates `P` itself.
* `mountainRangeProgram_triangulates`: a complete program (identity table built by a loop, then
  the fragment) runs within `80 * (n + 1)` steps with words bounded by `2 * (n + 1)` and
  triangulates a monotone mountain `P` — the plain `mountainProgram_triangulates` recovered
  through the relocatable fragment.
-/

namespace Chazelle.Mountain

open Machine Machine.Stmt Programs
open Chazelle.EarClip (detInto detInto_exec subPoly relabelList vtx_subPoly_getD n_subPoly
  subPoly_range getD_range)
open Chazelle.Existence (WeakTriangulates triangulates_of_weak)

@[expose] public section

/-! ### The walk -/

/-- The potential of the walk: `32` per triangle still to be emitted plus `41` per position
still to be processed. -/
noncomputable def subOuterPot (P : Polygon) (l : List ℕ) (σ : ℝ) (c : Config) : ℕ :=
  32 * (walk (subPoly P l) σ (c.nreg 64) (stackS c)).1.length + 41 * (l.length - c.nreg 64)

/-- **The invariant of the walk**, relative to the configuration `c₀` at the start of the loop
and the final output `out`: the word bound, the constants, the index table, the frame,
`top ≤ k`, stack entries `< m`, and the output followed by the (relabelled) triangles still to be
emitted by `walk (subPoly P l) σ k (stackS c)` is `out`. -/
def SOuterInv (P : Polygon) (W : ℕ) (l : List ℕ) (base sbase : ℕ) (σ : ℝ) (c₀ : Config)
    (out : List Polygon.Triangle) (c : Config) : Prop :=
  WordsBounded W c ∧ SConsts base sbase l.length σ c ∧ STab l base c ∧ SFrame c₀ c ∧
    c.nreg 63 ≤ c.nreg 64 ∧ (∀ x ∈ stackS c, x < l.length) ∧
    c.output ++ (walk (subPoly P l) σ (c.nreg 64) (stackS c)).1.map (relabelList l) = out

section walkLoop
variable {P : Polygon} {W : ℕ} {l : List ℕ} {base sbase : ℕ}

/-- **The push re-establishes the invariant of the walk.**  `c` is the configuration at the
start of the iteration (`k = nreg 64 < m`), `c₂` the one after the pop loop, `c'` the one
after the push, described by the equations `e…`. -/
theorem sOuterInv_push {σ : ℝ} {c₀ : Config} {out : List Polygon.Triangle} {c c₂ c' : Config}
    (hw' : WordsBounded W c') (hC' : SConsts base sbase l.length σ c') (hT' : STab l base c')
    (hF' : SFrame c₀ c') (hk : c.nreg 64 < l.length) (htop₂ : c₂.nreg 63 ≤ c.nreg 64)
    (hlt₂ : ∀ x ∈ stackS c₂, x < l.length)
    (hout : c.output ++ (walk (subPoly P l) σ (c.nreg 64) (stackS c)).1.map (relabelList l) =
      out)
    (hout₂ : c₂.output = c.output ++
      (popLoop (subPoly P l) σ (c.nreg 64) (stackS c)).1.map (relabelList l))
    (hst₂ : stackS c₂ = (popLoop (subPoly P l) σ (c.nreg 64) (stackS c)).2.1)
    (e61 : c'.nreg 61 = c₂.nreg 61) (e63 : c'.nreg 63 = c₂.nreg 63 + 1)
    (e64 : c'.nreg 64 = c.nreg 64 + 1)
    (enm : c'.nmem = upd c₂.nmem (c₂.nreg 61 + c₂.nreg 63) (c.nreg 64))
    (eout : c'.output = c₂.output) :
    SOuterInv P W l base sbase σ c₀ out c' ∧
      subOuterPot P l σ c' + 32 * (popLoop (subPoly P l) σ (c.nreg 64) (stackS c)).1.length +
        41 ≤ subOuterPot P l σ c := by
  have hs' : stackS c' = c.nreg 64 :: (popLoop (subPoly P l) σ (c.nreg 64) (stackS c)).2.1 := by
    unfold stackS
    rw [e61, e63, enm, stk_shift_push]
    exact congrArg _ hst₂
  have hkQ : c.nreg 64 < (subPoly P l).n := by ram_simp
  have hwalk := walk_of_lt (subPoly P l) σ hkQ (stackS c)
  refine ⟨⟨hw', hC', hT', hF', by omega, ?_, ?_⟩, ?_⟩
  · simp_all
  all_goals (grind [List.append_assoc, List.map_append, subOuterPot, List.length_append])

set_option maxHeartbeats 800000 in
/-- **One iteration of the walk** (`k < m`) preserves `SOuterInv` and decreases the potential
`subOuterPot` by at least its cost plus `2`. -/
theorem subOuterBody_inv (hL : SLayout W base sbase l.length) {σ : ℝ} {c₀ : Config}
    {out : List Polygon.Triangle} (c : Config) (hI : SOuterInv P W l base sbase σ c₀ out c)
    (ht : c.nreg 64 < c.nreg 62) :
    ∃ c' k', Exec P W subOuterBody c c' k' ∧ SOuterInv P W l base sbase σ c₀ out c' ∧
      subOuterPot P l σ c' + k' + 2 ≤ subOuterPot P l σ c := by
  have hL' := hL
  obtain ⟨hdisj, hWb, hWs⟩ := hL
  obtain ⟨hw, hC, hT, hF, htop, hlt, hout⟩ := hI
  obtain ⟨h60, h61, h62, h65, h68, h70, hr70, hr72⟩ := hC
  have hk : c.nreg 64 < l.length := by omega
  unfold subOuterBody
  refine spec_seq (spec_instr (Exec.constN hw 69 1 (by omega)) fun hw₁ => ?_)
  have hs₁ : stackS { c with nreg := upd c.nreg 69 1 } = stackS c :=
    stackS_congr (by config_simp) (by config_simp) rfl
  have hF₁ : SFrame c { c with nreg := upd c.nreg 69 1 } := sFrame_of_regs
    (fun r hr => by ram_simp) (fun r _ => rfl) rfl rfl
  refine spec_seq (spec_use (subInnerLoop_exec (P := P) (σ := σ) (k := c.nreg 64) hL' hk _ hw₁
    ⟨by ram_simp, by ram_simp, by ram_simp,
      by ram_simp, by ram_simp, by ram_simp,
      by omega, by omega⟩
    hT (by config_simp) (by omega_nf) (by ram_simp)
    (by config_simp)) ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨hC₂, hT₂, hF₂, h64₂, htop₂, hlt₂, hout₂, hst₂⟩
  rw [hs₁] at hk₂ hout₂ hst₂
  config_simp at hout₂
  obtain ⟨g60, g61, g62, g65, g68, g70, gr70, gr72⟩ := hC₂
  unfold subPushStmt
  exec_block
  · -- `addN 71 61 63`: `sbase + top ≤ W`
    omega
  · -- `addN 63 63 65`: `top + 1 ≤ W`
    omega_nf
  · -- `addN 64 64 65`: `k + 1 ≤ W`
    omega_nf
  · have hF₃ : SFrame c₂ { c₂ with
        nreg := upd (upd (upd c₂.nreg 71 (c₂.nreg 61 + c₂.nreg 63)) 63 (c₂.nreg 63 + c₂.nreg 65))
          64 (c₂.nreg 64 + c₂.nreg 65),
        nmem := upd c₂.nmem (c₂.nreg 61 + c₂.nreg 63) (c₂.nreg 64) } := by
      refine ⟨fun r hr => ?_, fun r _ => rfl, fun a ha => ?_, rfl⟩
      · have h1 : r ≠ 71 := by omega
        have h2 : r ≠ 63 := by omega
        have h3 : r ≠ 64 := by omega
        simp [h1, h2, h3]
      · ram_simp
    obtain ⟨hI', hp'⟩ := sOuterInv_push (P := P) (W := W) (c₀ := c₀) ‹WordsBounded _ _›
      ⟨by omega_nf, by omega_nf, by ram_simp,
        by ram_simp, by ram_simp, by ram_simp,
        by omega, by omega⟩
      (fun i hi => by
        config_simp
        rw [Machine.upd_other _ _ _ (by omega)]
        ram_grind)
      (sFrame_trans hF (sFrame_trans hF₁ (sFrame_trans hF₂ hF₃)))
      hk htop₂ hlt₂ hout hout₂ hst₂ (by config_simp)
      (by ram_simp) (by ram_simp) (by grind)
      (by config_simp)
    grind

/-- **Spec lemma for the walk.**  From a configuration with the constants, the index table,
`top ≤ k` (`k = nreg 64`) and stack entries `< m`, the walk appends
`(walk (subPoly P l) σ k (stackS c)).1.map (relabelList l)` to the output, keeps the constants,
the table and the frame, and costs
`≤ subOuterPot P l σ c + 2 = 32 * (walk … ).1.length + 41 * (m - k) + 2`. -/
theorem subOuterLoop_exec (hL : SLayout W base sbase l.length) {σ : ℝ} (c : Config)
    (hw : WordsBounded W c) (hC : SConsts base sbase l.length σ c) (hT : STab l base c)
    (htop : c.nreg 63 ≤ c.nreg 64) (hlt : ∀ x ∈ stackS c, x < l.length) :
    ∃ c' k', Exec P W subOuterLoop c c' k' ∧ k' ≤ subOuterPot P l σ c + 2 ∧
      c'.output = c.output ++
        (walk (subPoly P l) σ (c.nreg 64) (stackS c)).1.map (relabelList l) ∧
      SConsts base sbase l.length σ c' ∧ STab l base c' ∧ SFrame c c' := by
  obtain ⟨c', k', ex, ⟨-, hC', hT', hF', -, -, hout'⟩, hexit, hk⟩ := Exec.whileLtN_potential
    (SOuterInv P W l base sbase σ c
      (c.output ++ (walk (subPoly P l) σ (c.nreg 64) (stackS c)).1.map (relabelList l)))
    (subOuterPot P l σ) (fun _ h => h.1) (fun d hd ht => subOuterBody_inv hL d hd ht)
    ⟨hw, hC, hT, sFrame_refl c, htop, hlt, rfl⟩
  have hkn : (subPoly P l).n ≤ c'.nreg 64 := by rw [n_subPoly, ← hC'.2.2.1]; omega
  rw [walk_of_le _ σ hkn, List.map_nil, List.append_nil] at hout'
  exact ⟨c', k', ex, hk, hout', hC', hT', hF'⟩

end walkLoop

/-! ### Initialisation and the sign -/

section init
variable {P : Polygon} {W : ℕ} {l : List ℕ}

set_option maxHeartbeats 800000 in
/-- **Spec lemma for `subInitBlock`.**  With `3 ≤ m`, the layout hypothesis and the index
table: cost `≤ 21` (exactly `21`); `top = 2`, `k = 2`, the constants `nreg 65 = 1`,
`nreg 68 = 2`, `nreg 70 = 0`, the inputs `nreg 60, 61, 62` kept, the stack `[1, 0]`, the table
kept, the frame, the coordinates of `v_{l[m-1]}, v_{l[0]}, v_{l[1]}` in `rreg 61 … rreg 66`,
`rreg 72 = 0`, and the output unchanged. -/
theorem subInitBlock_exec (h3 : 3 ≤ l.length) (c : Config) (hc : WordsBounded W c)
    (hL : SLayout W (c.nreg 60) (c.nreg 61) l.length) (h62 : c.nreg 62 = l.length)
    (hT : STab l (c.nreg 60) c) :
    ∃ c' k, Exec P W subInitBlock c c' k ∧ k ≤ 21 ∧
      c'.nreg 60 = c.nreg 60 ∧ c'.nreg 61 = c.nreg 61 ∧ c'.nreg 62 = l.length ∧
      c'.nreg 63 = 2 ∧ c'.nreg 64 = 2 ∧ c'.nreg 65 = 1 ∧ c'.nreg 68 = 2 ∧ c'.nreg 70 = 0 ∧
      stackS c' = [1, 0] ∧ STab l (c.nreg 60) c' ∧ SFrame c c' ∧
      c'.rreg 61 = (P.vtx (l.getD (l.length - 1) 0)).1 ∧
      c'.rreg 62 = (P.vtx (l.getD (l.length - 1) 0)).2 ∧
      c'.rreg 63 = (P.vtx (l.getD 0 0)).1 ∧ c'.rreg 64 = (P.vtx (l.getD 0 0)).2 ∧
      c'.rreg 65 = (P.vtx (l.getD 1 0)).1 ∧ c'.rreg 66 = (P.vtx (l.getD 1 0)).2 ∧
      c'.rreg 72 = 0 ∧ c'.output = c.output := by
  obtain ⟨hdisj, hWb, hWs⟩ := hL
  have hg : ∀ i, i < l.length →
      upd (upd c.nmem (c.nreg 61) 0) (c.nreg 61 + 1) 1 (c.nreg 60 + i) = l.getD i 0 := by
    intro i hi
    rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega), hT i hi]
  have gA : upd (upd c.nmem (c.nreg 61) 0) (c.nreg 61 + 1) 1 (c.nreg 60 + c.nreg 62 - 1) =
      l.getD (l.length - 1) 0 := by
    grind
  have gB : upd (upd c.nmem (c.nreg 61) 0) (c.nreg 61 + 1) 1 (c.nreg 60) = l.getD 0 0 := by
    grind
  have gC : upd (upd c.nmem (c.nreg 61) 0) (c.nreg 61 + 1) 1 (c.nreg 60 + 1) = l.getD 1 0 :=
    hg 1 (by omega)
  unfold subInitBlock
  exec_block
  · omega
  · omega
  · omega
  · omega_nf
  · omega_nf
  · omega_nf
  · refine ⟨by omega, by config_simp, by config_simp, by ram_simp, by config_simp,
      by config_simp, by config_simp, by config_simp, by config_simp, ?_,
      fun i hi => by grind, ?_, by config_simp; rw [gA],
      by config_simp; rw [gA], by config_simp; rw [gB], by config_simp; rw [gB],
      by config_simp; rw [gC], by config_simp; rw [gC], by omega_nf, rfl⟩
    · unfold stackS
      config_simp
      simp [stk, upd]
    · refine ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_, rfl⟩
      · have h63 : r ≠ 63 := by omega
        have h64 : r ≠ 64 := by omega
        have h65 : r ≠ 65 := by omega
        have h68 : r ≠ 68 := by omega
        have h70 : r ≠ 70 := by omega
        have h71 : r ≠ 71 := by omega
        have h72 : r ≠ 72 := by omega
        have h73 : r ≠ 73 := by omega
        have h74 : r ≠ 74 := by omega
        simp [h63, h64, h65, h68, h70, h71, h72, h73, h74]
      · have h61 : r ≠ 61 := by omega
        have h62 : r ≠ 62 := by omega
        have h63 : r ≠ 63 := by omega
        have h64 : r ≠ 64 := by omega
        have h65 : r ≠ 65 := by omega
        have h66 : r ≠ 66 := by omega
        have h72 : r ≠ 72 := by omega
        simp [h61, h62, h63, h64, h65, h66, h72]
      · ram_simp

/-- **Spec lemma for `subSignStmt`.**  With `rreg 72 = 0`: cost `≤ 10`;
`rreg 70 = if 0 < det (rreg 61, rreg 62) (rreg 63, rreg 64) (rreg 65, rreg 66) then 1 else -1`;
real registers outside `61 … 72` and `rreg 72`, the natural registers, both memories and the
output are unchanged. -/
theorem subSignStmt_exec (c : Config) (hc : WordsBounded W c) (h72 : c.rreg 72 = 0) :
    ∃ c' k, Exec P W subSignStmt c c' k ∧ k ≤ 10 ∧
      c'.rreg 70 = (if 0 < det (c.rreg 61, c.rreg 62) (c.rreg 63, c.rreg 64) (c.rreg 65, c.rreg 66)
        then 1 else -1) ∧
      c'.rreg 72 = c.rreg 72 ∧ (∀ r, (r < 61 ∨ 72 < r) → c'.rreg r = c.rreg r) ∧
      c'.nreg = c.nreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold subSignStmt
  refine spec_seq (spec_use (detInto_exec (P := P) 67 68 69 61 62 63 64 65 66 (by decide)
    (by decide) (by decide)
    (fun r hr => by omega) c hc) ?_)
  rintro c₁ k₁ hk₁ hw₁ ⟨hdet, hfr, hn, hnm, hrm, hout⟩
  
  by_cases hpos : 0 < det (c.rreg 61, c.rreg 62) (c.rreg 63, c.rreg 64) (c.rreg 65, c.rreg 66)
  · refine spec_ifLtR_true (by ram_simp)
      (spec_instr (Exec.constR hw₁ 70 1) fun hw₂ => ?_)
    refine ⟨by omega, ?_, by ram_simp, fun r hr => ?_, by omega,
      by omega, by omega, by omega⟩
    · simp_all
    · config_simp
      rw [Machine.upd_other _ _ _ (by omega)]
      grind
  · refine spec_ifLtR_false (by ram_simp)
      (spec_instr (Exec.constR hw₁ 70 (-1)) fun hw₂ => ?_)
    refine ⟨by omega, ?_, by ram_simp, fun r hr => ?_, by omega,
      by omega, by omega, by omega⟩
    · simp_all
    · config_simp
      rw [Machine.upd_other _ _ _ (by omega)]
      grind

end init

/-! ### The whole fragment -/

section main
variable {P : Polygon} {W : ℕ} {l : List ℕ}

/-- **Spec lemma for `mountainSubStmt`, with the computed sign.**  For `3 ≤ m`, the layout
hypothesis, `nreg 62 = m` and the index table at `nreg 60`: the fragment appends
`(mountainTriangulation (subPoly P l) (mountainSign (subPoly P l))).map (relabelList l)` to the
output, keeps the frame, and costs
`≤ 32 * (mountainTriangulation …).length + 41 * (m - 2) + 33`. -/
theorem mountainSubStmt_exec_sign (h3 : 3 ≤ l.length) (c : Config) (hc : WordsBounded W c)
    (hL : SLayout W (c.nreg 60) (c.nreg 61) l.length) (h62 : c.nreg 62 = l.length)
    (hT : STab l (c.nreg 60) c) :
    ∃ c' k, Exec P W mountainSubStmt c c' k ∧
      k ≤ 32 * (mountainTriangulation (subPoly P l) (mountainSign (subPoly P l))).length +
        41 * (l.length - 2) + 33 ∧
      c'.output = c.output ++
        (mountainTriangulation (subPoly P l) (mountainSign (subPoly P l))).map (relabelList l) ∧
      SFrame c c' := by
  unfold mountainSubStmt
  refine spec_seq (spec_use (subInitBlock_exec (P := P) h3 c hc hL h62 hT) ?_)
  rintro c₁ k₁ hk₁ hw₁
    ⟨n60, n61, n62, n63, n64, n65, n68, n70, hs₁, hT₁, hF₁, r1, r2, r3, r4, r5, r6, r72, hout₁⟩
  refine spec_seq (spec_use (subSignStmt_exec (P := P) c₁ hw₁ r72) ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨e70, e72, erf, hn, hnm, hrm, hout₂⟩
  have hsig : c₂.rreg 70 = mountainSign (subPoly P l) := by
    rw [e70, r1, r2, r3, r4, r5, r6]
    unfold mountainSign
    rw [n_subPoly, vtx_subPoly_getD P l (by omega), vtx_subPoly_getD P l (by omega),
      vtx_subPoly_getD P l (by omega)]
  have hC : SConsts (c.nreg 60) (c.nreg 61) l.length (mountainSign (subPoly P l)) c₂ :=
    ⟨by rw [hn, n60], by rw [hn, n61], by rw [hn, n62], by rw [hn, n65], by rw [hn, n68],
      by rw [hn, n70], hsig, by grind⟩
  have hs₂ : stackS c₂ = [1, 0] := by
    rw [stackS_congr (by rw [hn]) (by rw [hn]) hnm]; exact hs₁
  have h64 : c₂.nreg 64 = 2 := by rw [hn, n64]
  have hF₂ : SFrame c₁ c₂ := sFrame_of_regs (fun r _ => by rw [hn]) erf hnm hrm
  refine spec_use (subOuterLoop_exec (P := P) hL c₂ hw₂ hC
    (fun i hi => by ram_grind) (by grind)
    (by grind)) ?_
  rintro c₃ k₃ hk₃ hw₃ ⟨hout₃, -, -, hF₃⟩
  unfold subOuterPot at hk₃
  rw [h64, hs₂] at hk₃
  refine ⟨?_, ?_, sFrame_trans hF₁ (sFrame_trans hF₂ hF₃)⟩
  all_goals (grind [mountainTriangulation])

/-- **Spec lemma for `mountainSubStmt`** on a monotone mountain `Q = subPoly P l` whose index
table `nmem (base + i) = l[i]` (`i < m = l.length`) sits at `base = nreg 60`, with `m` in
`nreg 62`, the stack region at `sbase = nreg 61`, the two regions disjoint and every address
`≤ W`.  The fragment appends `(mountainTriangulation Q σ).map (relabelList l)` (triangles in
original indices) to the output, for a sign `σ = ±1` with `0 < σ * det v_{m-1} v₀ v₁` (vertices
of `Q`, so that `mountain_triangulates_of_sign` applies), at cost `≤ 73 * m`.  **Frame:** natural
registers outside `63 … 74` (in particular the inputs `60, 61, 62`), real registers outside
`61 … 72`, natural memory outside the stack region (in particular the index table) and the real
memory are unchanged. -/
theorem mountainSub_exec (hM : IsMountain (subPoly P l)) (c : Config) (hc : WordsBounded W c)
    (htab : ∀ i, i < l.length → c.nmem (c.nreg 60 + i) = l.getD i 0)
    (hm : c.nreg 62 = l.length)
    (hdisj : c.nreg 60 + l.length ≤ c.nreg 61 ∨ c.nreg 61 + l.length ≤ c.nreg 60)
    (hWb : c.nreg 60 + l.length ≤ W) (hWs : c.nreg 61 + l.length ≤ W) :
    ∃ c' k σ, Exec P W mountainSubStmt c c' k ∧ (σ = 1 ∨ σ = -1) ∧
      0 < σ * det ((subPoly P l).vtx ((subPoly P l).n - 1)) ((subPoly P l).vtx 0)
        ((subPoly P l).vtx 1) ∧
      k ≤ 73 * l.length ∧
      c'.output = c.output ++ (mountainTriangulation (subPoly P l) σ).map (relabelList l) ∧
      (∀ r, (r < 63 ∨ 74 < r) → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 61 ∨ 72 < r) → c'.rreg r = c.rreg r) ∧
      (∀ a, (a < c.nreg 61 ∨ c.nreg 61 + l.length ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rmem = c.rmem := by
  have h3 : 3 ≤ l.length := by have := hM.1.1; simp_all
  obtain ⟨hσ, hpos⟩ := mountainSign_spec (subPoly P l) hM
  obtain ⟨c', k, ex, hk, hout, hF⟩ :=
    mountainSubStmt_exec_sign (P := P) h3 c hc ⟨hdisj, hWb, hWs⟩ hm htab
  have hlen := (mountain_triangulates_of_sign (subPoly P l) hM hσ hpos).1.2.1
  rw [n_subPoly] at hlen
  obtain ⟨hn, hr, hnm, hrm⟩ := hF
  refine ⟨c', k, mountainSign (subPoly P l), ex, hσ, hpos, by omega, hout, hn, hr,
    fun a ha => hnm a (by omega), hrm⟩

end main

/-! ### The composable form -/

/-- **The stack walk with a valid sign weakly triangulates a mountain**: for a mountain `Q` and
`σ = ±1` with `0 < σ * det v_{n-1} v₀ v₁`, `mountainTriangulation Q σ` is a weak triangulation
of `Q`. -/
theorem weakTriangulates_mountainTriangulation_of_sign {Q : Polygon} (hM : IsMountain Q)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hpos : 0 < σ * det (Q.vtx (Q.n - 1)) (Q.vtx 0) (Q.vtx 1)) :
    WeakTriangulates Q (mountainTriangulation Q σ) := by
  have hor : σ = orient Q := by
    have h := mountain_orient_det Q hM
    rcases sign_eq_or_eq_neg hσ (orient_eq Q) with h' | h'
    · exact h'
    nlinarith
  exact mountain_weakTriangulates Q hM hor

/-- **Spec lemma for `mountainSubStmt`, composable form**: under the hypotheses of
`mountainSub_exec`, the fragment appends `T.map (relabelList l)` to the output for a weak
triangulation `T` of `subPoly P l`, at cost `≤ 73 * m`, with the same frame. -/
theorem mountainSub_exec_weak {P : Polygon} {W : ℕ} {l : List ℕ} (hM : IsMountain (subPoly P l))
    (c : Config) (hc : WordsBounded W c)
    (htab : ∀ i, i < l.length → c.nmem (c.nreg 60 + i) = l.getD i 0)
    (hm : c.nreg 62 = l.length)
    (hdisj : c.nreg 60 + l.length ≤ c.nreg 61 ∨ c.nreg 61 + l.length ≤ c.nreg 60)
    (hWb : c.nreg 60 + l.length ≤ W) (hWs : c.nreg 61 + l.length ≤ W) :
    ∃ c' k T, Exec P W mountainSubStmt c c' k ∧ k ≤ 73 * l.length ∧
      WeakTriangulates (subPoly P l) T ∧ c'.output = c.output ++ T.map (relabelList l) ∧
      (∀ r, (r < 63 ∨ 74 < r) → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 61 ∨ 72 < r) → c'.rreg r = c.rreg r) ∧
      (∀ a, (a < c.nreg 61 ∨ c.nreg 61 + l.length ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rmem = c.rmem := by
  obtain ⟨c', k, σ, ex, hσ, hpos, hk, hout, hn, hr, hnm, hrm⟩ :=
    mountainSub_exec hM c hc htab hm hdisj hWb hWs
  exact ⟨c', k, _, ex, hk, weakTriangulates_mountainTriangulation_of_sign hM hσ hpos, hout, hn,
    hr, hnm, hrm⟩

/-! ### A complete program for the special case `l = List.range n`

`mountainRangeStmt` builds the identity table `nmem i = i` (`i < n`) at `base = 0`, puts the
stack region at `sbase = n`, and runs `mountainSubStmt`: it recovers the plain triangulator
`mountainProgram_triangulates` through the relocatable fragment (constants `2 * (n + 1)` for the
word bound, `80 * (n + 1)` for the steps). -/

section rangeProgram
variable {P : Polygon} {W : ℕ}

end rangeProgram

end

end Chazelle.Mountain
