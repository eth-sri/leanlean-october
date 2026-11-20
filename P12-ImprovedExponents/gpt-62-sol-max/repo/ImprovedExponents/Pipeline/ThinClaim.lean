module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Program
public import ThreeSumApsp.Programs.Sec4.Corollary26.AllInstances
public import ThreeSumApsp.Sec4.Corollary31.RationalParameters
public import ThreeSumApsp.Sec4.ParameterSteps
public import ThreeSumApsp.Sec4.Table2.LogBounds
public import ThreeSumApsp.Util.Asymptotics.Dominated
public import ThreeSumApsp.Util.Log
public import ThreeSumApsp.Programs.LightModel
public import ImprovedExponents.Pipeline.OfflineWithin
public import ImprovedExponents.Pipeline.PolyBoundedList

@[expose] public section

/-!
# A thin-product solver at any parameters of the program

Upstream's solver for Corollary 26 is the procedure `allInstances26` of the program
`program31 ratParams26`: it tests whether `D^18 ≤ N`, calls the offline routine `offline32` if so
and the brute force if not (`Light.Sec4.allInstances26_solves`). The same three procedures are in
`program31 G` for every `G : RatParams`. This file redoes the upstream proof for an arbitrary `G`
(it follows `ThreeSumApsp/Programs/Sec4/Corollary26/AllInstances.lean` and `Claim.lean` line by
line; several lemmas there are private and are repeated here).

The solver `allBody` is generic in its two callees:

* the regime test (`RegimeTest`): a procedure that returns 1 on the instances `(N, D)` of a regime
  `Reg N D` and 0 on the others, with its time and the largest number it forms. Upstream's test
  `D^18 ≤ N` is the instance `regime18`; `ImprovedExponents.Pipeline.RegimeRS` adds the test
  `D^r ≤ N^s`;
* the offline routine (`OfflineRoutine`): a procedure that solves the thin product on the
  instances `Ok N D`, with its time and its need. Upstream's routine `offline32` at the parameters
  `G` is the instance `offline32Routine G`; `ImprovedExponents.PrunedProgram` adds the routine with
  the pruned encoder.

A solver has to be right on every instance, so the whole regime of the test must lie where the
routine is specified. For `offline32` this means that the hypotheses of Theorem 30 hold from the
threshold `m₀` on: this is `FitsR R G` (`Fits18 G` for the test of the program). It limits the
ratio `c = a/b` (the tile `√K N₀` must fit into `N`).

The result is `thinClaimR_of_offlineWithin`: if the offline routine stays within its two bounds on
the instances with `D ≤ N^ε` (`OfflineWithinT` of its time; `OfflineWithin` for `offline32`), and
these lie in the regime, then the thin product is solved, in the sense of the time model
`lightModel`, by one procedure whose time on these instances is at most a constant times
`w D^q (log D + 1) + N² (log D + 1)²/D^γ` (`ThinClaim`). `thinClaim_of_offlineWithin` is the case
of the program's test and routine, with `ε ≤ 1/18`.
-/

namespace ImprovedExponents

open ThreeSumApsp Light Light.Sec4

/-! ## The statement -/

/-- A time claim for the thin matrix product: one solver for all instances whose time on the
instances with `D ≤ N^ε` is at most a constant times `w D^q (log D + 1) + N² (log D + 1)²/D^γ`,
for `w` wanted positions. (Compare `Claim.Corollary_26_wanted`.) -/
def ThinClaim (M : DetTimeModel) (ε γ q : ℝ) : Prop :=
  ∃ (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ → ℝ), M.thinProduct T ∧
    ∀ (N D w : ℕ) (u : ℝ), 1 ≤ N → 1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ ε →
      T N D w u ≤ C * (preBound31 γ N D + (w : ℝ) * queryBound31 q D)

/-! ## The two callees -/

/-- A regime test: the procedure number `proc` with the body `body` returns 1 on the instances of
the regime `Reg N D` and 0 on the others, in `time` steps, forming no number above `word N D`, in
every program that holds it and the auxiliary procedures it calls (`aux`). -/
structure RegimeTest where
  /-- The regime: the instances on which the offline routine is called. -/
  Reg : ℕ → ℕ → Prop
  /-- The number of the test procedure. -/
  proc : ℕ
  /-- The body of the test procedure. -/
  body : Stmt
  /-- The auxiliary procedures the test calls are in the program. -/
  aux : Program → Prop
  /-- Appending procedures keeps the auxiliary procedures. -/
  aux_append : ∀ P R, aux P → aux (P ++ R)
  /-- The running time of the test. -/
  time : ℕ
  /-- The largest number the test forms on `N`, `D`. -/
  word : ℕ → ℕ → ℕ
  /-- That number is polynomial in `N` and `D`. -/
  word_poly : PolyBounded word
  /-- The specification of the test. -/
  meets : ∀ {lim : Limits} {P : Program} {d : ℕ}, aux P → P[proc]? = some body →
    d + 1 ≤ lim.depth → ∀ N D : ℕ, 1 ≤ N → 1 ≤ D → ((word N D : ℕ) : ℤ) ≤ lim.word →
    ∀ μ : ℕ → ℤ, Meets lim P proc d [N, D] μ time fun r μ' =>
      μ' = μ ∧ ((r = 1 ∧ Reg N D) ∨ (r = 0 ∧ ¬ Reg N D))

/-- An offline routine for the thin product: the procedure number `proc` with the body `body`
solves the task `thinTask` on the instances `(N, D)` with `Ok N D`, in `time N D w` steps, whenever
the limits allow for `need N D U`, in every program that holds it and the auxiliary procedures it
calls (`aux`). The routine is called at depth `d + 1`; the need is reckoned from the depth `d` of
the caller. -/
structure OfflineRoutine where
  /-- The instances on which the routine is specified. -/
  Ok : ℕ → ℕ → Prop
  /-- The number of the routine. -/
  proc : ℕ
  /-- The body of the routine. -/
  body : Stmt
  /-- The auxiliary procedures the routine calls are in the program. -/
  aux : Program → Prop
  /-- Appending procedures keeps the auxiliary procedures. -/
  aux_append : ∀ P Q, aux P → aux (P ++ Q)
  /-- The running time on `N`, `D` with `w` wanted positions. -/
  time : ℕ → ℕ → ℕ → ℕ
  /-- The time is monotone in the number of wanted positions. -/
  time_mono : ∀ N D w w' : ℕ, w ≤ w' → time N D w ≤ time N D w'
  /-- What the routine needs on `N`, `D` with entries bounded by `U`: the largest number it forms,
  the cells from the free pointer on, the levels of calls below the caller. -/
  need : ℕ → ℕ → ℕ → Need
  /-- The need is polynomial in `N`, `D`, `U`. -/
  need_poly : PolyNeedN fun ps => need (ps[0]?.getD 0) (ps[1]?.getD 0) (ps[3]?.getD 0)
  /-- The specification of the routine. -/
  meets : ∀ {lim : Limits} {P : Program} {d : ℕ} {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ},
    aux P → P[proc]? = some body → x.Pre μ fr → Ok x.N x.D → (need x.N x.D x.U).Ok lim fr d →
    Meets lim P proc (d + 1) [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
      (time x.N x.D x.w) fun r μ' => thinTask.Post x μ fr r μ'

/-- The solver with the regime test number `test` and the offline routine number `off`:
`allInstances26Body` with `test` in place of `regimeTest26` and `off` in place of `offline32`.
Locals 0 to 9 are the arguments, which are passed on as they are; local 10 is the result of the
test. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean
def allBody (test off : ℕ) : Stmt :=
  let args := [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9]
  .call test [v 0, v 1] 10 ;;
  .ite (k 0 <' v 10) (.call off args 0) (.call Sec2.pThinBrute args 0)

/-! ## Time and need -/

open Classical in
/-- The time of the solver with the test `R` and the routine `O`, for the parameters N, D, w, U. -/
noncomputable def allInstancesTimeR (R : RegimeTest) (O : OfflineRoutine) : List ℕ → ℕ
  | [N, D, w, _] => R.time + 64 + (if R.Reg N D then O.time N D w else 40 * ((w + 1) * (D + 1)))
  | _ => 0

/-- What the solver with the test `R` and the routine `O` needs, for the parameters N, D, w, U:
the largest number formed (by the test, the brute force and the routine), the cells from the free
pointer on (the brute force uses `N + 1`), the levels of calls (the test is called at depth `d + 1`
and needs one more; the routine's are reckoned from `d`). -/
def allInstancesNeedR (R : RegimeTest) (O : OfflineRoutine) (ps : List ℕ) : Need :=
  let N := ps[0]?.getD 0
  let D := ps[1]?.getD 0
  let U := ps[3]?.getD 0
  ⟨R.word N D + (100 + D * (U * U)) + (O.need N D U).word, N + 1 + (O.need N D U).cells,
    2 + (O.need N D U).depth⟩

/-- The need of the solver allows for the need of the routine. -/
theorem allInstancesNeedR_ok {lim : Limits} {R : RegimeTest} {O : OfflineRoutine}
    {N D w U fr d : ℕ} (ok : (allInstancesNeedR R O [N, D, w, U]).Ok lim fr d) :
    (O.need N D U).Ok lim fr d := by
  apply ok.mono <;>
    simp only [allInstancesNeedR, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some] <;> omega

/-- `L = ⌈(a/b) m⌉ ≤ a m`. -/
theorem ratParams_L_le_mul (G : RatParams) (m : ℕ) : G.L m ≤ G.a * m := by
  unfold RatParams.L
  have hb := G.hb
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  have h : G.a * m ≤ G.b * (G.a * m) := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-! ## The limits of offline32 -/

/-- What offline32 at the parameters `G` needs on `N`, `D` with entries bounded by `U`: the
numbers of `Lim31` and the numerals of `G` (with B = (N + 1)^5, which bounds 10^L in the regime,
the three numbers of `Lim30` are at most B³ U², 7 B U and 10 B); the cells of the block of
Theorem 30 behind the two padded matrices; the levels of the recursion. -/
def offline32Need (G : RatParams) (N D U : ℕ) : Need :=
  ⟨1000 + 100 * D + N * D + D * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U)
      + 7 * ((N + 1) ^ 5 * U) + 10 * (N + 1) ^ 5
      + (G.a * (4 * D) + G.p * (4 * D) + G.b + G.q + G.m₀),
    4 + N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4, G.a * (4 * D) + 12⟩

section need

variable {lim : Limits} {G : RatParams} {N D₀ U fr d : ℕ}

/-- The block of Theorem 30, behind the two padded matrices, ends within the cells of the need. -/
theorem top_le_of_need (hD : 1 ≤ D₀) (H : Hyp30 (parOf G N D₀) (switchOf31 G D₀))
    (ok : (offline32Need G N D₀ U).Ok lim fr d) :
    top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr) ≤ lim.space := by
  have hcells := ok.cells
  simp only [offline32Need] at hcells
  have hblock : top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr) - blockAt N D₀ fr
      ≤ 222 * ((N + 1) ^ 5) ^ 4 := top_sub_le_pow H (below H) _
  have hpad : N * D (logFour D₀) ≤ 4 * (N * D₀) :=
    (Nat.mul_le_mul_left N (Nat.pow_clog_le_mul (b := 4) (by norm_num) hD)).trans_eq (by ring)
  have hbase : blockAt N D₀ fr = fr + 3 + N * D (logFour D₀) + N * D (logFour D₀) := rfl
  omega

/-- If B bounds 10^L, 7^L and 10^m, the three numbers in the limits of Theorem 30 are at most B³ U²,
7 B U and 10 B. -/
theorem lim30_of_below {p : Sec2.Par} {t b0 B : ℕ} (hB : Below p t B) (std : Std lim)
    (hspace : top p t b0 ≤ lim.space)
    (fits : ∀ n : ℕ, n ≤ B ^ 3 * (U * U) + 7 * (B * U) + 10 * B → (n : ℤ) ≤ lim.word) :
    Lim30 lim p t b0 (U : ℤ) := by
  have hten := hB.T
  have hseven := hB.S7
  have htenm := hB.tenm
  have hvalue : 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) ≤ B ^ 3 * (U * U) :=
    calc 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) ≤ B * ((B * U) * (B * U)) := by gcongr
      _ = B ^ 3 * (U * U) := by ring
  have henc : 7 ^ (p.L + 1) * U ≤ 7 * (B * U) :=
    calc 7 ^ (p.L + 1) * U = 7 * (7 ^ p.L * U) := by ring
      _ ≤ 7 * (B * U) := by gcongr
  have hpow : 10 ^ (p.L + 1) ≤ 10 * B :=
    calc 10 ^ (p.L + 1) = 10 * 10 ^ p.L := by ring
      _ ≤ 10 * B := by gcongr
  exact {
    std := std
    space := hspace
    value := by grind
    enc := by grind
    pow := fits _ (hpow.trans (by omega)) }

/-- If the hypotheses of Theorem 30 hold from the threshold on, the need of offline32 covers what
it asks of the limits. -/
theorem lim31_of_need (hD : 1 ≤ D₀)
    (hfit : G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀))
    (ok : (offline32Need G N D₀ U).Ok lim fr d) : Lim31 lim G N D₀ fr (U : ℤ) := by
  have hcells := ok.cells
  simp only [offline32Need] at hcells
  have fits {n : ℕ} (h : n ≤ (offline32Need G N D₀ U).word := by simp only [offline32Need]; omega) :
      (n : ℤ) ≤ lim.word := (Int.ofNat_le.mpr h).trans ok.word
  have h4 : 4 ^ logFour D₀ ≤ 4 * D₀ := Nat.pow_clog_le_mul (b := 4) (by norm_num) hD
  have hm4 : logFour D₀ ≤ 4 * D₀ := logFour_le_four_mul hD
  have ha : G.a * logFour D₀ ≤ G.a * (4 * D₀) := Nat.mul_le_mul_left _ hm4
  have hp : G.p * logFour D₀ ≤ G.p * (4 * D₀) := Nat.mul_le_mul_left _ hm4
  have std : Std lim := ⟨ok.space, fits (n := 100)⟩
  have large (hm : G.m₀ ≤ logFour D₀) : Lim30 lim (parOf G N D₀) (switchOf31 G D₀)
      (blockAt N D₀ fr) (U : ℤ) :=
    have H := hfit hm
    lim30_of_below (B := (N + 1) ^ 5) (below H) std (top_le_of_need hD H ok)
      fun n hn => fits (hn.trans (by simp only [offline32Need]; omega))
  exact {
    std := std
    space := by
      unfold structEnd
      split_ifs with h
      · omega
      · exact (large (not_lt.mp h)).space
    pow := fits
    mword := fits
    m0word := fits
    ip := by exact_mod_cast fits (n := D₀ * (U * U))
    large := large }

end need

/-! ## Upstream's routine -/

open PolyBoundedList in
theorem offline32Need_poly (G : RatParams) :
    PolyNeedN fun ps => offline32Need G (ps[0]?.getD 0) (ps[1]?.getD 0) (ps[3]?.getD 0) := by
  apply polyNeed <;> dsimp only [offline32Need] <;> growth [param 0, param 1, param 3]

/-! ## The solver -/

/-! ## The need is polynomial in the parameters -/

open PolyBoundedList in
/-- The need is polynomial in the parameters. The bounds on the need of the routine and on the
number the test forms go into the constant and the degree. -/
theorem allInstancesNeedR_poly (R : RegimeTest) (O : OfflineRoutine) :
    PolyNeedN (allInstancesNeedR R O) := by
  obtain ⟨s, k, hO⟩ := O.need_poly
  have hw := of_polyBound fun ps => (hO ps).1
  have hc := of_polyBound fun ps => (hO ps).2.1
  have hd := of_polyBound fun ps => (hO ps).2.2
  have hR := comp₂ R.word_poly (param 0) (param 1)
  apply polyNeed <;> dsimp only [allInstancesNeedR] <;>
    growth [hw, hc, hd, hR, param 0, param 1, param 3]

/-! ## The claim -/

open Classical in
/-- **The thin-product claim from an offline routine `O`, for a regime test `R`.** If the regime
lies where the routine is specified, the instances with `D ≤ N^ε` lie in the regime, and the
routine stays within its bounds there, then the thin product is solved within these bounds by the
procedure `pAll` of a program that holds the solver `allBody` with the test `R` and the routine
`O`, the test, the routine, the brute force and the procedures the test and the routine call. -/
theorem thinClaimR_of_offlineWithin {P : Program} {R : RegimeTest} {O : OfflineRoutine}
    {pAll : ℕ} {ε γ q : ℝ} (hfit : ∀ N D : ℕ, R.Reg N D → O.Ok N D)
    (hall : P[pAll]? = some (allBody R.proc O.proc)) (htest : P[R.proc]? = some R.body)
    (haux : R.aux P) (hoff : P[O.proc]? = some O.body) (hauxO : O.aux P)
    (hbrute : P[Sec2.pThinBrute]? = some Sec2.thinBruteBody)
    (hreg : ∀ N D₀ : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε → R.Reg N D₀)
    (h : OfflineWithinT O.time ε γ q) : ThinClaim lightModel ε γ q := by
  obtain ⟨A, hA⟩ := h
  let C : ℝ := (R.time + 64 : ℕ)
  refine ⟨A * (1 + C / 400), fun N D₀ w _ => (allInstancesTimeR R O [N, D₀, w, 0] : ℝ),
    ⟨_, _, allInstancesTimeR R O, _, allInstancesNeedR_poly R O, ⟨_, hall, ?_⟩,
      fun N D₀ w w' U u _ _ _ hw _ => ?_⟩, fun N D₀ w u hN hD hDN => ?_⟩
  · intro Q lim d x μ fr hpre hok
    have ok : (allInstancesNeedR R O [x.N, x.D, x.w, x.U]).Ok lim fr d := hok
    have okO := allInstancesNeedR_ok ok
    have hword := ok.word
    have hcells := ok.cells
    have hdepth := ok.depth
    simp only [allInstancesNeedR, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some] at hword hcells hdepth
    have hfits : ∀ n : ℕ, n ≤ R.word x.N x.D + (100 + x.D * (x.U * x.U)) → (n : ℤ) ≤ lim.word :=
      fun n hn => le_trans (by exact_mod_cast (by omega)) hword
    have hroom : fr + x.N + 1 ≤ lim.space := by omega
    change Ends lim (P ++ Q) d (allBody R.proc O.proc)
      ⟨frame [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr], μ⟩
      (R.time + 64 + if R.Reg x.N x.D then O.time x.N x.D x.w
        else 40 * ((x.w + 1) * (x.D + 1))) _
    unfold allBody
    dsimp only
    refine Ends.callToThen (R.meets (R.aux_append P Q haux) (getElem?_append_of_eq_some htest Q)
      (by omega) x.N x.D hpre.N_pos hpre.D_pos (hfits _ (by omega)) μ) ?_ (hT := by simp; omega)
    rintro r μ ⟨rfl, hr⟩
    refine Ends.iteLast (fun hpos => ?_) (fun hneg => ?_)
    · have hreg : R.Reg x.N x.D := by
        aesop
      rw [ite_eq_left hreg]
      exact Ends.callTo (O.meets (O.aux_append P Q hauxO) (getElem?_append_of_eq_some hoff Q) hpre
        (hfit _ _ hreg) okO) fun _ _ h => h
    · have hreg : ¬ R.Reg x.N x.D := by
        rcases hr with ⟨rfl, -⟩ | ⟨-, h⟩
        · simp at hneg
        · exact h
      rw [ite_eq_right hreg]
      have hbrute : Meets lim (P ++ Q) Sec2.pThinBrute (d + 1)
          [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ (40 * ((x.w + 1) * (x.D + 1)))
          fun r μ' => thinTask.Post x μ fr r μ' :=
        .of_body (getElem?_append_of_eq_some hbrute Q) (Sec2.thinBrute_spec
          ⟨ok.space, by exact hfits 100 (by omega)⟩ x μ fr (x.U : ℤ) hpre hroom (hfits _ (by omega)))
      exact Ends.callTo hbrute fun _ _ h => h
  · change (allInstancesTimeR R O [N, D₀, w, U] : ℝ) ≤ (allInstancesTimeR R O [N, D₀, w', 0] : ℝ)
    exact_mod_cast (show allInstancesTimeR R O [N, D₀, w, U] ≤ allInstancesTimeR R O [N, D₀, w', 0] by
      simp only [allInstancesTimeR]
      split_ifs
      · exact Nat.add_le_add_left (O.time_mono N D₀ w w' hw) _
      · gcongr)
  · change (allInstancesTimeR R O [N, D₀, w, 0] : ℝ) ≤ _
    simp only [allInstancesTimeR, ite_eq_left (hreg N D₀ hN hD hDN)]
    rw [Nat.cast_add]
    change C + (O.time N D₀ w : ℝ) ≤ _
    have hbase := hA N D₀ w hN hD hDN
    have h400 : (400 : ℝ) ≤ A * (preBound31 γ N D₀ + w * queryBound31 q D₀) := by
      linarith
    nlinarith only [hbase, mul_le_mul_of_nonneg_left h400 (show 0 ≤ C / 400 by positivity)]

/-- `D ≤ N^ε` with `ε ≤ s/r` puts the instance in the regime `D^r ≤ N^s`, for `1 ≤ r`. -/
theorem pow_le_pow_of_le_rpow {N D₀ r s : ℕ} {ε : ℝ} (hr : 1 ≤ r) (hε : ε ≤ (s : ℝ) / r)
    (hN : 1 ≤ N) (hDN : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) : D₀ ^ r ≤ N ^ s := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h : ((D₀ : ℝ)) ^ r ≤ (N : ℝ) ^ s :=
    calc ((D₀ : ℝ)) ^ r ≤ ((N : ℝ) ^ ε) ^ r := pow_le_pow_left₀ (by positivity) hDN r
      _ = (N : ℝ) ^ (ε * r) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      _ ≤ (N : ℝ) ^ (s : ℝ) := Real.rpow_le_rpow_of_exponent_le hNR
          (by rwa [le_div_iff₀ hrR] at hε)
      _ = (N : ℝ) ^ s := Real.rpow_natCast _ _
  exact_mod_cast h

end ImprovedExponents
