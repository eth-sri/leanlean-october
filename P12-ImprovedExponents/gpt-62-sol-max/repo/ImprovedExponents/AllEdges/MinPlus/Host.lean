module

import ThreeSumApsp.Lang.Registers
import ThreeSumApsp.Lang.Symbolic

public import ImprovedExponents.AllEdges.MinPlus.Prefix
public import ThreeSumApsp.Programs.Sec3.Theorem21b.NegativeTriangle.Passes
public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Lang.PolyBounded

@[expose] public section

/-!
# A (min,+)-product host using all-edges Exact Triangle

The workspace contains eight matrices: the current minimum, the two prefixes, the two
remainders, the trial edge weights, and the two flag matrices. The input and output regions
are untouched until the final pass, which subtracts the shift from the product.
-/

namespace ImprovedExponents.AllEdges.MinPlus

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

namespace Host

registers [Size, Bound, A, B, Out, Base, Cells, Bound3, Power, Levels, Round, Res]

private def addr (i : ℕ) : Expr := v Base +' k i *' v Cells

private def setup : Stmt :=
  .set Cells (v Size *' v Size) ;; .set Bound3 (k 3 *' v Bound) ;;
  .set Power (k 1) ;; .set Levels (k 0)

private def powerLoop : Stmt :=
  .while (v Power ≤' v Bound3) (.set Power (k 2 *' v Power) ;; .set Levels (v Levels +' k 1))

private def start (pAff pTr pFill : ℕ) : Stmt :=
  .call pAff [v Cells, v A, k 1, v Bound, addr 3] Res ;;
  .call pTr [v Size, v B, v Bound, addr 4] Res ;;
  .call pFill [v Base, k 3 *' v Cells, k 0] Res

private def ask (pAE pAff e : ℕ) : Stmt :=
  .call pAff [v Cells, v Base, k 0 -' k 2, k 0 -' k e, addr 5] Res ;;
  .call pAE [v Size, k 9 *' v Bound, addr 5, addr 2, addr 1, addr (6 + e), addr 8] Res

namespace Update
registers [Len, Minima, Low, Mid, Idx]
end Update

open Update in
/-- Select the least attained candidate. -/
def updateBody : Stmt := pass Idx (v Len) (v Minima)
  (k 2 *' M (v Minima +' v Idx) +'
    (k 1 -' M (v Low +' v Idx)) *' (k 2 -' M (v Mid +' v Idx)))

private def round (pAE pAff pDown pUpdate : ℕ) : Stmt :=
  .call pDown [k 2 *' v Cells, addr 1, addr 3, v Power] Res ;;
  ask pAE pAff 0 ;; ask pAE pAff 1 ;;
  .call pUpdate [v Cells, v Base, addr 6, addr 7] Res

private def finish (pAff : ℕ) : Stmt :=
  .call pAff [v Cells, v Base, k 1, k 0 -' k 2 *' v Bound, v Out] Res

private def body (pAE pAff pTr pFill pDown pUpdate : ℕ) : Stmt :=
  setup ;; powerLoop ;; start pAff pTr pFill ;;
  .for Round (v Levels) (round pAE pAff pDown pUpdate) ;; finish pAff

def need (r : ℕ → ℕ → Need) (n U : ℕ) : Need :=
  ⟨(r n (9 * U)).word + 40 * U + 100, 8 * (n * n) + (r n (9 * U)).cells,
    (r n (9 * U)).depth + 1⟩

def askTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ := T n (9 * U) + 20 * (n * n) + 70
def roundTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  2 * askTime T n U + 126 * (n * n) + 70

/-- Two all-edges queries and linear passes over the matrices per bit. -/
def time (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  levels U * (roundTime T n U + 22) + 140 * (n * n) + 170

private abbrev atSlot (x : MatInst) (fr i : ℕ) : ℕ := fr + i * width x

private abbrev initial (x : MatInst) (fr : ℕ) : List ℤ := [x.n, x.U, x.a, x.b, x.c, fr]
private abbrev locs (x : MatInst) (fr : ℕ) (pow : ℤ) (lev j : ℕ) (res : ℤ) : List ℤ :=
  initial x fr ++ [(width x : ℤ), (3 * x.U : ℕ), pow, lev, j, res]
private abbrev atRound (x : MatInst) (fr j : ℕ) (res : ℤ) : List ℤ :=
  locs x fr (2 ^ levels x.U) (levels x.U) j res

local macro "layout_arith" : tactic => `(tactic|
  first | omega | (simp only [atSlot, width, best_length, List.length_map, length_affL,
    length_transposeL, length_aeFlags, Inside, Outside] at *; omega))

section verify

variable {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {P₀ R : Program}
  {pAE pAff pTr pFill pDown pUpdate : ℕ} {x : MatInst} {μ ν : ℕ → ℤ} {fr d : ℕ} {lim : Limits}

structure Ctx (P₀ R : Program) (pAE pAff pTr pFill pDown pUpdate : ℕ)
    (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) (lim : Limits) (d : ℕ) (x : MatInst) (μ : ℕ → ℤ)
    (fr : ℕ) : Prop where
  solver : Solves aeTask P₀ pAE T r
  aff : (P₀ ++ R)[pAff]? = some affineBody
  trans : (P₀ ++ R)[pTr]? = some transposeBody
  fill : (P₀ ++ R)[pFill]? = some fillBody
  down : (P₀ ++ R)[pDown]? = some prefDownBody
  update : (P₀ ++ R)[pUpdate]? = some updateBody
  pre : x.Pre μ fr
  ok : (need r x.n x.U).Ok lim fr d

variable (C : Ctx P₀ R pAE pAff pTr pFill pDown pUpdate T r lim d x μ fr)

include C

private theorem Ctx.fits : 40 * (x.U : ℤ) + 100 ≤ lim.word ∧
    fr + 8 * (x.n * x.n) ≤ lim.space ∧ d < lim.depth := by
  light_facts C.ok
  grind [need]

private theorem Ctx.solverOk : (r x.n (9 * x.U)).Ok lim (atSlot x fr 8) (d + 1) :=
  C.ok.mono (by constructor <;> grind) (by grind [need])
    (by grind [need])

omit C in
private theorem shifted_length (h : x.Pre μ fr) : (shifted x).length = 2 * width x := by
  simp [shifted, h.lenA, two_mul]

private theorem quo_range (ℓ : ℕ) : ∀ z ∈ (shifted x).map (prefQ ℓ),
    0 ≤ z ∧ z ≤ 2 * (x.U : ℤ) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  obtain ⟨h0, hu⟩ := shifted_range C.pre y hy
  exact ⟨prefQ_nonneg h0 ℓ, (prefQ_le h0 ℓ).trans hu⟩

private theorem power_spec :
    Ends lim (P₀ ++ R) d powerLoop ⟨frame (locs x fr 1 0 0 0), μ⟩ (14 * levels x.U + 6)
      (· = ⟨frame (atRound x fr 0 0), μ⟩) := by
  have hw := C.fits.1
  have hp : (2 : ℤ) ^ levels x.U ≤ 6 * x.U := by exact_mod_cast power_le C.pre.U_pos
  have hlt : (3 : ℤ) * x.U < 2 ^ levels x.U := by exact_mod_cast lt_power x.U
  refine Ends.whileBlock (fun j σ => σ = ⟨frame (locs x fr (2 ^ j) j 0 0), μ⟩)
    (levels x.U) rfl ?_ ?_ (by simp; omega)
  · rintro j _ hj rfl
    have hm : (2 : ℤ) ^ (j + 1) ≤ 2 ^ levels x.U := by
      exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2) hj)
    have hl : (j : ℤ) + 1 < 2 ^ (j + 1) := by exact_mod_cast (Nat.lt_two_pow_self (n := j+1))
    rw [pow_succ'] at hm hl
    generalize hpw : (2 : ℤ) ^ j = pw at hm hl ⊢
    exact ⟨by light_side, by simp; omega, by light_side,
      by simp [pow_succ', hpw, update_frame_setLocal, locs]⟩
  light_side

private structure Mem (x : MatInst) (fr ℓ level : ℕ) (μ ν : ℕ → ℤ) : Prop where
  min : Seg ν fr (best x level)
  quo : Seg ν (atSlot x fr 1) ((shifted x).map (prefQ ℓ))
  rem : Seg ν (atSlot x fr 3) ((shifted x).map (prefR (levels x.U) ℓ))
  kept : Kept μ ν fr

private abbrev query (x : MatInst) (fr ℓ e : ℕ) : AeInst :=
  ⟨⟨x.n, 9 * x.U, atSlot x fr 5, atSlot x fr 2, atSlot x fr 1, question x ℓ e,
    rightT x ℓ, left x ℓ⟩, atSlot x fr (6 + e)⟩

private theorem ask_spec {ℓ e j : ℕ} (he : e ≤ 1) (M : Mem x fr ℓ (ℓ + 1) μ ν) (res : ℤ) :
    Ends lim (P₀ ++ R) d (ask pAE pAff e) ⟨frame (atRound x fr j res), ν⟩ (askTime T x.n x.U)
      fun σ => ∃ res' ν', σ = ⟨frame (atRound x fr j res'), ν'⟩ ∧
        Mem x fr ℓ (ℓ + 1) μ ν' ∧ Seg ν' (atSlot x fr (6 + e)) (flags x ℓ e) ∧
        (e = 1 → SameOn (Inside (atSlot x fr 6) (width x)) ν ν' ) := by
  obtain ⟨hw, hsp, hd⟩ := C.fits
  have hs := C.ok.space
  have hm₀ : 6 * (x.n * x.n) ≤ (6 + e) * (x.n * x.n) := Nat.mul_le_mul_right _ (by omega)
  have hm₁ : (6 + e) * (x.n * x.n) ≤ 7 * (x.n * x.n) := Nat.mul_le_mul_right _ (by omega)
  have hm₁' : (6 + (e : ℤ)) * ((x.n : ℤ) * x.n) ≤ 7 * ((x.n : ℤ) * x.n) := by exact_mod_cast hm₁
  have hm₀' : 0 ≤ (6 + (e : ℤ)) * ((x.n : ℤ) * x.n) := by positivity
  have hU := C.pre.U_pos
  have hlen := best_length x (ℓ + 1)
  have hla : (left x ℓ).length = width x := by simp [C.pre.lenA]
  have hlb : (rightT x ℓ).length = width x := by simp
  have hl := shifted_length C.pre
  have hq : ∀ z ∈ best x (ℓ + 1), |-2 * z| ≤ lim.word ∧ |-2 * z + -(e : ℤ)| ≤ lim.word := by
    intro z hz
    have := best_bounds C.pre _ z hz
    simp only [abs_le]
    layout_arith
  unfold ask
  light_call (affine_meets (dst := atSlot x fr 5) C.aff M.min hs (by layout_arith) (by layout_arith) (Or.inl (by layout_arith)) hq)
    using addr, locs, hlen, askTime, width with _ ν₁ ⟨hAB, hk₁⟩
  have hqr := M.quo.of_sameOutside hk₁ (Or.inl (by simp only [List.length_map, hl]; layout_arith))
  simp only [shifted, List.map_append, seg_append, hla] at hqr
  have hqr' : Seg ν₁ (atSlot x fr 1) (left x ℓ) ∧ Seg ν₁ (atSlot x fr 2) (rightT x ℓ) := by
    simpa only [atSlot, one_mul, two_mul, Nat.add_assoc] using hqr
  have hsmall : AbsLe (left x ℓ) (9 * x.U : ℕ) ∧ AbsLe (rightT x ℓ) (9 * x.U : ℕ) := by
    have h : AbsLe ((shifted x).map (prefQ ℓ)) (9 * x.U : ℕ) := by
      intro z hz
      have := quo_range C ℓ z hz
      simp only [abs_le, Int.natCast_mul, Nat.cast_ofNat]
      omega
    simpa only [AbsLe, shifted, List.map_append, List.forall_mem_append] using h
  have hpre : (query x fr ℓ e).Pre ν₁ (atSlot x fr 8) := by
    refine ⟨⟨⟨⟨by simp, hAB, ?_, by layout_arith⟩,
        ⟨hlb, hqr'.2, hsmall.2, by layout_arith⟩, ⟨hla, hqr'.1, hsmall.1, by layout_arith⟩⟩, C.pre.n_pos, by layout_arith⟩,
      ?_, ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
      have := best_bounds C.pre _ y hy
      simp only [abs_le, Int.natCast_mul, Nat.cast_ofNat]
      layout_arith
    all_goals dsimp [query]; layout_arith
  light_call (C.solver.meets R (query x fr ℓ e) (atSlot x fr 8) hpre C.solverOk)
    using addr, locs, aeTask, query, askTime, hlen, atSlot, width with res' ν₂ ⟨hF, hk₂⟩
  change KeptBut ν₁ ν₂ (atSlot x fr 8) _ (width x) at hk₂
  have keep : Kept ν ν₂ (atSlot x fr 5) := by
    dsimp only [atSlot, width] at hk₁ hk₂ ⊢
    light_keep [hlen]
  have retain {b : ℕ} {L : List ℤ} (h : Seg ν b L) (hb : b + L.length ≤ atSlot x fr 5) :=
    h.of_sameOn keep fun i hi => by omega
  refine ⟨res', ν₂, rfl, ⟨retain M.min (by layout_arith),
    retain M.quo (by simp only [List.length_map, hl]; layout_arith),
    retain M.rem (by simp only [List.length_map, hl]; layout_arith),
    M.kept.trans (keep.mono fun b hb => by layout_arith)⟩, hF, ?_⟩
  rintro rfl
  exact hk₁.then hk₂ fun b (hb : Inside (atSlot x fr 6) (width x) b) =>
    ⟨Or.inr (by layout_arith), by layout_arith, Or.inl (by layout_arith)⟩

private theorem update_spec {ℓ : ℕ} (hℓ : ℓ + 1 ≤ levels x.U) (hD : Seg ν fr (best x (ℓ + 1)))
    (hF₀ : Seg ν (atSlot x fr 6) (flags x ℓ 0)) (hF₁ : Seg ν (atSlot x fr 7) (flags x ℓ 1)) :
    Meets lim (P₀ ++ R) pUpdate (d + 1) [width x, fr, atSlot x fr 6, atSlot x fr 7] ν
      (40 * width x + 6) fun _ ν' => Seg ν' fr (best x ℓ) ∧ SameOutside ν ν' fr (width x) := by
  obtain ⟨hw, hsp, _⟩ := C.fits
  have hs := C.ok.space
  refine .of_body C.update ?_
  unfold updateBody
  let vBest j := (best x ℓ).getD j 0
  refine Ends.pass vBest ?_ ⟨seg_wrote (best_length x ℓ) fun j hj => (List.getD_eq_getElem _ _ hj).symm,
    sameOutside_wrote le_rfl⟩ C.ok.space (by layout_arith) rfl rfl
  intro j hj
  have read {b : ℕ} {L : List ℤ} (hL : Seg ν b L) (hb : fr ≤ b) (hjL : j < L.length) :
      wrote ν fr vBest j (b + j) = L.getD j 0 :=
    (wrote_rest (Or.inr (by omega))).trans (hL.getD hjL 0)
  have h₀ := read hD le_rfl (by simpa using hj)
  have h₁ := read hF₀ (by layout_arith) (by simpa using hj)
  have h₂ := read hF₁ (by layout_arith) (by simpa using hj)
  have hflag (e : ℤ) : 0 ≤ (flags x ℓ e).getD j 0 ∧ (flags x ℓ e).getD j 0 < 2 := by
    rw [aeFlags_getD _ _ _ hj]
    exact flag_mem _
  have hbd (s : ℕ) : 0 ≤ (best x s).getD j 0 ∧ (best x s).getD j 0 ≤ 4 * (x.U : ℤ) :=
    List.getD_of_forall_mem (by layout_arith) (best_bounds C.pre s) j
  have hstep := refine_min C.pre hj hℓ
  have h₃ := hflag 0
  have h₄ := hflag 1
  have hd := hbd (ℓ + 1)
  have he := hbd ℓ
  change j < x.n * x.n at hj
  have haddr (c : ℕ) : ((fr : ℤ) + c * ((x.n : ℤ) * x.n) + j).toNat =
      fr + c * (x.n * x.n) + j := by
    simp only [← Int.natCast_mul, ← Int.natCast_add, Int.toNat_natCast]
  simp only [vBest, atSlot, width, List.getD_eq_getElem?_getD] at h₀ h₁ h₂ hstep h₃ h₄ hd he
  have h6 : ((fr : ℤ) + 6 * ((x.n : ℤ) * x.n) + j).toNat = fr + 6 * (x.n * x.n) + j := haddr 6
  have h7 : ((fr : ℤ) + 7 * ((x.n : ℤ) * x.n) + j).toNat = fr + 7 * (x.n * x.n) + j := haddr 7
  light_side [h6, h7, h₀, h₁, h₂, vBest, atSlot, width]

private theorem body_spec :
    Ends lim (P₀ ++ R) d (body pAE pAff pTr pFill pDown pUpdate) ⟨frame (initial x fr), μ⟩
      (time T x.n x.U) fun σ => Seg σ.mem x.c (minPlusList x.n x.A x.B) ∧
        KeptBut μ σ.mem fr x.c (width x) := by
  obtain ⟨hw, hsp, hd⟩ := C.fits
  have hs := C.ok.space
  have hc := C.pre.belowC
  have hlev : levels x.U ≤ 6 * x.U := Nat.lt_two_pow_self.le.trans (power_le C.pre.U_pos)
  have ht : time T x.n x.U = setup.blockCost + (14 * levels x.U + 6) + (120 * width x + 100) +
      (levels x.U * (roundTime T x.n x.U + 8) + 6) + (20 * width x + 46) := by
    unfold time
    simp [setup]
    ring
  rw [ht]
  unfold body
  refine Ends.pieceThen (T₁ := setup.blockCost) (R := (· = ⟨frame (locs x fr 1 0 0 0), μ⟩)) ?_ ?_
  · light_block using setup, initial, locs, width
    exact (frame_append_zeros _ 2).symm
  rintro _ rfl
  light_piece (power_spec C) with _ rfl
  have ha := C.pre.lenA
  have hb := C.pre.lenB
  have hba := C.pre.belowA
  have hbb := C.pre.belowB
  have hn : x.n ≤ x.n * x.n := by simpa using Nat.mul_le_mul_left x.n C.pre.n_pos
  have haf : ∀ z ∈ x.A, |1 * z| ≤ lim.word ∧ |1 * z + x.U| ≤ lim.word := fun z hz => by
    have := abs_le.1 (C.pre.leA z hz)
    simp [abs_le]; omega
  have hbf : ∀ z ∈ x.B, |z + x.U| ≤ lim.word := fun z hz => by
    have := abs_le.1 (C.pre.leB z hz)
    rw [abs_le]
    layout_arith
  unfold start
  light_call (affine_meets (dst := atSlot x fr 3) C.aff C.pre.segA hs (by layout_arith) (by layout_arith) (Or.inl (by layout_arith)) haf)
    using addr, locs, ha, width with _ ν₀ ⟨hA, hk₀⟩
  have hB := C.pre.segB.of_sameOutside hk₀ (Or.inl (by layout_arith))
  light_call (transpose_meets (dst := atSlot x fr 4) C.trans hB hb (Or.inl (by layout_arith)) ⟨hs, by layout_arith, by layout_arith⟩ hbf)
    using addr, locs, width, ha, hb with _ ν₁ ⟨hB, hk₁⟩
  light_call (fill_meets (dst := fr) (n := 3 * width x) (x := 0) C.fill hs (by layout_arith))
    using addr, locs, width, ha, hb with res ν₂ ⟨hz, hk₂⟩
  have hl := shifted_length C.pre
  have hlen : (affL 1 x.U x.A).length = width x := by simpa using ha
  have hlog : ∀ z ∈ shifted x, 0 ≤ z ∧ z < (2 : ℤ) ^ levels x.U := by
    have hh : (3 : ℤ) * x.U < 2 ^ levels x.U := by exact_mod_cast lt_power x.U
    intro z hz
    have := shifted_range C.pre z hz
    layout_arith
  have hzero : (shifted x).map (prefQ (levels x.U)) = List.replicate (2 * width x) 0 := by
    rw [map_prefQ_start hlog, affL]
    simp only [zero_mul, add_zero, List.map_const', hl]
  rw [show 3 * width x = width x + 2 * width x by layout_arith, List.replicate_add, seg_append] at hz
  have hkeep : Kept μ ν₂ fr :=
    (hk₀.then hk₁ fun b (hb : b < fr) => ⟨Or.inl (by layout_arith), Or.inl (by layout_arith)⟩).then
      hk₂ fun b hb => ⟨hb, Or.inl hb⟩
  have hM : Mem x fr (levels x.U) (levels x.U) μ ν₂ := by
    refine ⟨best_top C.pre ▸ hz.1, ?_, ?_, hkeep⟩
    · simpa only [hzero, List.length_replicate, atSlot, one_mul] using hz.2
    · rw [map_prefR_start hlog, shifted, seg_append, hlen,
        show atSlot x fr 3 + width x = atSlot x fr 4 by layout_arith]
      exact ⟨(hA.of_sameOutside hk₁ (Or.inl (by layout_arith))).of_sameOutside hk₂
        (Or.inr (by layout_arith)), hB.of_sameOutside hk₂ (Or.inr (by layout_arith))⟩
  refine Ends.next (levels x.U * (roundTime T x.n x.U + 8) + 6) (Ends.forShape (fun j res ν => ⟨frame (atRound x fr j res), ν⟩)
    (fun j _ ν => Mem x fr (levels x.U - j) (levels x.U - j) μ ν) (levels x.U)
    (roundTime T x.n x.U) res (by simpa using hM) ?_ ?_)
    (by simp [addr, width, ha]; omega)
  · intro j res' ν hj M
    let ℓ := levels x.U - (j + 1)
    have he : levels x.U - j = ℓ + 1 := by dsimp [ℓ]; omega
    have hℓ : ℓ + 1 ≤ levels x.U := by omega
    rw [he] at M
    have hp : (2 : ℤ) ^ levels x.U ≤ 6 * x.U := by exact_mod_cast power_le C.pre.U_pos
    have hlen : ((shifted x).map (prefQ (ℓ + 1))).length = 2 * width x := by simp only [List.length_map, hl]
    have H : PrefPre lim ν (atSlot x fr 1) (atSlot x fr 3) (2 ^ levels x.U)
        ((shifted x).map (prefQ (ℓ + 1))) ((shifted x).map (prefR (levels x.U) (ℓ + 1))) := by
      refine ⟨M.quo, M.rem, by simp, hs, by layout_arith, by layout_arith, Or.inl (by layout_arith), by layout_arith, ?_, ?_⟩
      · intro z hz
        have := quo_range C (ℓ + 1) z hz
        simp only [abs_le]
        omega
      · intro z hz
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
        have := prefR_nonneg (levels x.U) (ℓ + 1) y
        have := prefR_lt hℓ y
        simp only [abs_le]
        layout_arith
    unfold round
    light_call (prefDown_meets C.down H) using addr, locs, hlen, roundTime, width, C.pre.lenA
      with res₀ ξ₀ ⟨hQ, hR, k₀⟩
    rw [zipWith_shiftQ hℓ] at hQ
    rw [map_shiftR hℓ] at hR
    have keep₀ : Kept ν ξ₀ (fr + width x) := fun b hb =>
      k₀ b (Or.inl (by layout_arith)) (Or.inl (by layout_arith))
    have m₀ : Mem x fr ℓ (ℓ + 1) μ ξ₀ :=
      ⟨M.min.keep (by light_keep), hQ, hR, by light_keep [M.kept]⟩
    light_piece (ask_spec C (e := 0) (by decide) m₀ res₀) using roundTime, addr, hlen, width, C.pre.lenA
      with _ ⟨res₁, ξ₁, rfl, m₁, hF₀, -⟩
    light_piece (ask_spec C (e := 1) (by decide) m₁ res₁) using roundTime, addr, hlen, width, C.pre.lenA
      with _ ⟨res₂, ξ₂, rfl, m₂, hF₁, keepF⟩
    have keep := keepF rfl
    have hF := hF₀.keep (μ' := ξ₂) (by simpa using keep)
    light_call (update_spec C hℓ m₂.min hF hF₁)
      using addr, locs, roundTime, askTime, width, C.pre.lenA
      with res₃ ξ₃ ⟨hD, hk⟩
    exact ⟨res₃, ξ₃, rfl, hD, m₂.quo.keep (by light_keep [atSlot, hl]),
      m₂.rem.keep (by light_keep [atSlot, hl]), by light_keep [m₂.kept]⟩
  · intro res ν m
    have m : Mem x fr 0 0 μ ν := by simpa using m
    have hf : ∀ z ∈ best x 0, |1 * z| ≤ lim.word ∧ |1 * z - 2 * x.U| ≤ lim.word := by
      intro z hz
      have := best_bounds C.pre 0 z hz
      simp only [abs_le, one_mul]
      layout_arith
    have hl := best_length x 0
    unfold finish
    light_call (affine_meets (dst := x.c) (m := 1) (c := -(2 * (x.U : ℤ))) C.aff m.min hs (by layout_arith) (by layout_arith)
      (Or.inr (by layout_arith)) (by simpa only [sub_eq_add_neg] using hf)) using addr, locs, hl, width, ha, hb, pow_two
      with _ ν' ⟨hD, hk⟩
    exact ⟨best_zero C.pre ▸ hD, by light_keep [m.kept, hl]⟩

end verify

/-- The verified reduction appends the passes and the bit-by-bit host to an arbitrary
all-edges Exact Triangle solver. -/
theorem isHost : IsHost aeTask mpTask time need := by
  refine ⟨fun P p T r hsol => ?_, fun r h => ?_⟩
  · let hbody := body p P.length (P.length + 1) (P.length + 2) (P.length + 3) (P.length + 4)
    refine ⟨[affineBody, transposeBody, fillBody, prefDownBody, updateBody, hbody],
      P.length + 5, hbody, by simp, ?_⟩
    intro R lim d x μ fr hpre hok
    rw [List.append_assoc]
    exact body_spec ⟨hsol, by simp, by simp, by simp, by simp, by simp, hpre, hok⟩
  · unfold need
    poly_need [h.word, h.cells, h.depth]

end Host
end ImprovedExponents.AllEdges.MinPlus
