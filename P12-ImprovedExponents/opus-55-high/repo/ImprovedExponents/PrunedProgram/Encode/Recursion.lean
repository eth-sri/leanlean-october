
import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Recursion
import ImprovedExponents.PrunedProgram.SegOn
import ImprovedExponents.PrunedProgram.Work
import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Recursion


/-!
# The pruned encoder: upstream's recursion with a budget of symbols `P₀`

Upstream's `encode` (`ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean`) encodes an array
of `7^L` numbers into all `10^L` leaves: at level `L + 1`, for each of the ten terms `λ` it forms
the slice `A_λ` and recurses into the part of the output below `λ`.  The consumers read the
encodings only at the leaves with at most `m` symbols `P₀`.  The pruned encoder

  encodeP(L, j, src, out, scr, tab, p7, p10)

is the same recursion with the budget `j` as its second argument: the first nine terms are treated
as upstream (the recursive call keeps the budget `j`), and the term `P₀` (digit 9, the last one) is
entered with the budget `j - 1` if `j ≥ 1`, and skipped if `j = 0`.  Called with the budget `j`, it
writes exactly the leaves with at most `j` digits `9` (`EncodePostP`, `encodeP_spec`); the other
cells of the output keep whatever the memory had.  Its time `tEncP L j` is at most
`cEncP * encWorkP L j` (`tEncP_le`), where `encWorkP L j = ∑_{k ≤ L} prefCount k j · 7^{L-k}` is
the number of entries of all the slices it forms.

The text differs from upstream's in two ways: the loop runs over the nine terms `λ < 9` only, and
the term `λ = 9` follows as an `.ite` on the budget (the loop rules of the language give every round
the same time, which would not let the budget `j - 1` of the last term show in the bound).  The
proofs follow upstream's: `EncodePre.toStep`/`toRec` give the hypotheses of the callees,
`TermsDoneP` is the invariant of the loop stated on leaves, and `encodeP_spec` is the induction.
The recursions `prefCount (k+1) j = 9 prefCount k j + prefCount k (j-1)` and
`encWorkP (n+1) j = 7^(n+1) + 9 encWorkP n j + encWorkP n (j-1)` are proved in the first section.

Adapted from upstream `ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean` (Apache-2.0).
-/

namespace Light.Sec2

open Finset ThreeSumApsp ThreeSumApsp.Spec ImprovedExponents

/-! ## The recursions of the counts -/

section Counts

variable (k : ℕ)

/-- The number of prefixes with no symbol `P₀`: `9^k`. -/
theorem prefCount_zero_right : prefCount k 0 = 9 ^ k := by
  simp [prefCount]

/-- `prefCount (k+1) 0 = 9 * prefCount k 0`. -/
theorem prefCount_succ_zero : prefCount (k + 1) 0 = 9 * prefCount k 0 := by
  grind [prefCount_zero_right, pow_succ, mul_comm]

/-- One term of Pascal's rule, with the factor `9` taken out. -/
theorem choose_succ_mul_pow (i : ℕ) :
    k.choose (i + 1) * 9 ^ (k - i) = 9 * (k.choose (i + 1) * 9 ^ (k - (i + 1))) := by
  rcases i.lt_or_ge k with h | h
  · have : k - i = k - (i + 1) + 1 := by omega
    grind
  grind

/-- Pascal's rule for the counts of prefixes: a prefix of length `k + 1` with at most `j + 1`
symbols `P₀` is one of length `k` with at most `j + 1` of them followed by one of the nine other
terms, or one with at most `j` of them followed by `P₀`. -/
theorem prefCount_succ_succ (j : ℕ) :
    prefCount (k + 1) (j + 1) = 9 * prefCount k (j + 1) + prefCount k j := by
  unfold prefCount
  rw [sum_range_succ',
    sum_range_succ' fun i => k.choose i * 9 ^ (k - i)]
  simp [Nat.choose_zero_right, Nat.choose_succ_succ, add_mul, Nat.succ_sub_succ_eq_sub, sum_add_distrib, mul_add, mul_sum]
  grind [choose_succ_mul_pow, sum_congr]

/-- `prefCount (k+1) j = 9 prefCount k j + prefCount k (j-1)` for `1 ≤ j`. -/
theorem prefCount_succ_left {j : ℕ} (hj : 1 ≤ j) :
    prefCount (k + 1) j = 9 * prefCount k j + prefCount k (j - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := by aesop
  rw [prefCount_succ_succ, Nat.add_sub_cancel]

/-- The number of prefixes of length `0`: the empty one. -/
theorem prefCount_zero_left (j : ℕ) : prefCount 0 j = 1 := by
  simp [prefCount, sum_range_succ']

/-- `encWorkP 0 j = 1`: the leaf alone. -/
theorem encWorkP_zero_left (j : ℕ) : encWorkP 0 j = 1 := by
  simp [encWorkP, prefCount_zero_left]

variable (n : ℕ)

/-- The work below a vertex at level `n + 1`: its slice of `7^(n+1)` entries, nine children with
the same budget and one with the budget reduced by one. -/
theorem encWorkP_succ_left {j : ℕ} (hj : 1 ≤ j) :
    encWorkP (n + 1) j = 7 ^ (n + 1) + 9 * encWorkP n j + encWorkP n (j - 1) := by
  unfold encWorkP
  rw [sum_range_succ', mul_sum, prefCount_zero_left,
    Nat.sub_zero]
  have h : ∀ k ∈ range (n + 1), prefCount (k + 1) j * 7 ^ (n + 1 - (k + 1))
      = 9 * prefCount k j * 7 ^ (n - k) + prefCount k (j - 1) * 7 ^ (n - k) := by grind [Nat.succ_sub_succ_eq_sub, prefCount_succ_left]
  rw [sum_congr rfl h, sum_add_distrib]
  ring

/-- The analogue with the budget `0`: the term `P₀` is not entered. -/
theorem encWorkP_succ_zero : encWorkP (n + 1) 0 = 7 ^ (n + 1) + 9 * encWorkP n 0 := by
  unfold encWorkP
  rw [sum_range_succ', mul_sum, prefCount_zero_left,
    Nat.sub_zero]
  grind [Nat.succ_sub_succ_eq_sub, prefCount_succ_zero, sum_congr]

end Counts

/-! ## The leaves -/

/-- The digit of a term is `9` exactly for `P₀`. -/
theorem termIdx_eq_nine_iff (lam : Term) : ((termIdx lam : Fin 10) : ℕ) = 9 ↔ lam = .P0 := by
  cases lam with
  | P i j => grind [termIdx]
  | P0 => decide

/-- The number of symbols `P₀` of a leaf, by its first symbol. -/
theorem card_P0Levels_cons {n : ℕ} (lam : Term) (τ' : Leaf n) :
    (P0Levels (Fin.cons lam τ' : Leaf (n + 1))).card
      = (if lam = .P0 then 1 else 0) + (P0Levels τ').card := by
  grind [P0Levels, card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-! ## The text -/

namespace EncodeP

/- The local variables of encodeP: the arguments L, j, src, out, scr, tab, p7, p10; the lengths
7^{L-1} and 10^{L-1}; the number of the term; the result of a call, which is not used. -/
slots Level Budget Src Out Scr Table Pow7 Pow10 Len7 Len10 TermNo Res

end EncodeP

open EncodeP

/-- The two calls for one term: step (2) into the scratch area, and step (3) from there into the
part of the output that belongs to the term, with the budget reduced by `dec` (`0` for the first
nine terms, `1` for `P₀`). -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encodeTerm)
def encodeTermP (pS pE dec : ℕ) : Stmt :=
  .call pS [v Src, v Scr, v Len7, v TermNo, v Table] Res ;;
  .call pE [v Level -' k 1, v Budget -' k dec, v Scr, v Out +' v TermNo *' v Len10,
    v Scr +' v Len7, v Table, v Pow7, v Pow10] Res

/-- encodeP(L, j, src, out, scr, tab, p7, p10): upstream's encode(L, src, out, scr, tab, p7, p10)
with the budget `j` of symbols `P₀` as its second argument.  The nine terms `λ < 9` are treated with
the budget `j`; the term `P₀` (`λ = 9`, the counter of the loop after it) is treated with the budget
`j - 1` if `j ≥ 1`, and skipped if `j = 0`.  pS and pE are the numbers that the procedures encStep
and encodeP have in the program. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encodeBody)
def encodePBody (pS pE : ℕ) : Stmt :=
  .ite (v Level =' k 0)
    (.store (v Out) (M (v Src)))
    (.set Len7 (M (v Pow7 +' v Level -' k 1)) ;;
     .set Len10 (M (v Pow10 +' v Level -' k 1)) ;;
     .for TermNo (k 9) (encodeTermP pS pE 0) ;;
     .ite (v Budget =' k 0) .skip (encodeTermP pS pE 1))

/-! ## How much time it needs -/

/-- The time of the two calls for one term with the budget `j` below. -/
def tTermP (L j : ℕ) (t : ℕ → ℕ → ℕ) : ℕ := 27 + tEncStep (7 ^ L) + t L j

/-- A bound on the number of steps of `encodeP`: at level `L + 1`, nine times the two calls for a
term with the budget `j`, the test on the budget, the two calls for `P₀` with the budget `j - 1` if
`j ≥ 1`, and 104 steps. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encTime)
def tEncP : ℕ → ℕ → ℕ
  | 0, _ => 8
  | L + 1, 0 => 104 + 9 * (27 + tEncStep (7 ^ L) + tEncP L 0) + 4
  | L + 1, j + 1 => 104 + 9 * (27 + tEncStep (7 ^ L) + tEncP L (j + 1))
      + (31 + tEncStep (7 ^ L) + tEncP L j)

/-- The constant of the running time of `encodeP`. -/
def cEncP : ℕ := 778

/-- The number of steps is `O(encWorkP L j)`.  The two further terms on the left make the induction
go through. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encTime_le)
theorem tEncP_le_aux (L : ℕ) : ∀ j, tEncP L j + 724 * 7 ^ L + 46 ≤ cEncP * encWorkP L j := by
  unfold cEncP
  induction L with
  | zero => simp [tEncP, encWorkP_zero_left]
  | succ L ih =>
    intro j
    cases j with
    | zero =>
      grind [tEncP, tEncStep, encWorkP_succ_zero]
    | succ j =>
      grind [encWorkP_succ_left, tEncP, tEncStep]

/-- The time of the pruned encoder is at most `cEncP` times its work. -/
theorem tEncP_le (L j : ℕ) : tEncP L j ≤ cEncP * encWorkP L j := by
  have := tEncP_le_aux L j
  omega

/-! ## What it guarantees -/

/-- What `encodeP` with the budget `j` guarantees: the leaves with at most `j` symbols `P₀` hold the
encoding, and only the `10^L` cells of `out` and the `scrSize L` cells of the scratch area have
changed. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (EncodePost)
def EncodePostP (μ : ℕ → ℤ) (out scr L : ℕ) (a c : ℕ → ℤ) (j : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ τ : Leaf L, (P0Levels τ).card ≤ j → μ' (out + codeT τ) = encIdx c L a (codeT τ)) ∧
    SameOutside2 μ μ' out (10 ^ L) scr (scrSize L)

variable {lim : Limits} {P : Program} {d : ℕ} {μ μ' μ₁ μ₂ : ℕ → ℤ}
  {src out scr tab p7 p10 L lam j : ℕ} {V : ℤ} {a c : ℕ → ℤ}


/-! ## One term -/

/-- The memory before the round of the term number `lam`: the leaves with at most `j` symbols `P₀`
below the earlier terms are filled, and only the output and the scratch area have changed. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (TermsDone)
def TermsDoneP (μ : ℕ → ℤ) (out scr L : ℕ) (a c : ℕ → ℤ) (j lam : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ τ : Leaf (L + 1), (P0Levels τ).card ≤ j → ((termIdx (τ 0) : Fin 10) : ℕ) < lam →
    μ' (out + codeT τ) = encIdx c (L + 1) a (codeT τ)) ∧
    SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))

/-- The two calls for the term number `lam`, with the budget `j'` below, fill the leaves below it
with at most `j` symbols `P₀`, if `j' ≥ j - [lam = 9]`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (TermsDone.step)
theorem TermsDoneP.step (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1)) (hlam : lam < 10)
    (h : TermsDoneP μ out scr L a c j lam μ') (same₁ : SameOutside μ' μ₁ scr (7 ^ L)) {j' : ℕ}
    (hj' : j ≤ j' + if lam = 9 then 1 else 0)
    (hpost : EncodePostP μ₁ (out + lam * 10 ^ L) (scr + 7 ^ L) L (encSlice c a L lam) c j' μ₂) :
    TermsDoneP μ out scr L a c j (lam + 1) μ₂ := by
  have hplaces := lay.places_succ
  have hpart : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  obtain ⟨hdone, same⟩ := h
  obtain ⟨hnew, same₂⟩ := hpost
  have hkept := sameOutside2_succ same
  refine ⟨fun τ hτ hlt => ?_, ?_⟩
  · have hcons := Fin.cons_self_tail τ
    have hcodeT : codeT τ = termIdx (τ 0) * 10 ^ L + codeT (Fin.tail τ) := by
      rfl
    have htail := codeT_lt (Fin.tail τ)
    by_cases hold : termIdx (τ 0) < lam
    · -- The leaves below the earlier terms are not touched.
      have hi : codeT τ < lam * 10 ^ L := by
        exact Nat.mul_add_lt_mul hold htail
      rw [same₂ _ (by omega), same₁ _ (by omega), hdone τ hτ hold]
    grind [card_P0Levels_cons, termIdx_eq_nine_iff, Nat.add_assoc, encIdx_succ]
  · simp [scrSize]
    light_keep

/-- With the budget `0`, the term `P₀` is skipped: no leaf with no symbol `P₀` lies below it. -/
theorem TermsDoneP.skip (h : TermsDoneP μ out scr L a c 0 9 μ') :
    TermsDoneP μ out scr L a c 0 10 μ' := by
  refine ⟨fun τ hτ hlt => h.1 τ hτ ?_, h.2⟩
  rcases Nat.lt_or_ge _ 9 with h9 | h9
  · assumption
  · have heq : ((termIdx (τ 0) : Fin 10) : ℕ) = 9 := by omega
    simp_all [P0Levels, mem_univ, termIdx_eq_nine_iff]

/-- After all ten terms, the output is as `encodeP` guarantees. -/
theorem TermsDoneP.done (h : TermsDoneP μ out scr L a c j 10 μ') :
    EncodePostP μ out scr (L + 1) a c j μ' :=
  ⟨fun τ hτ => h.1 τ hτ (termIdx _).isLt, h.2⟩

/-- The list of the local variables at level L + 1. -/
abbrev EncodeP.locals (L j src out scr tab p7 p10 lam : ℕ) (r : ℤ) : List ℤ :=
  [(L + 1 : ℕ), j, src, out, scr, tab, p7, p10, (7 ^ L : ℕ), (10 ^ L : ℕ), lam, r]

/-- The specification of encodeP at level L with every budget, for a caller at depth d. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (EncodeMeets)
def EncodeMeetsP (lim : Limits) (P : Program) (pE d tab p7 p10 L : ℕ) (c : ℕ → ℤ) : Prop :=
  ∀ (j : ℕ) (μ : ℕ → ℤ) (src out scr : ℕ) (V : ℤ) (a : ℕ → ℤ), (j : ℤ) ≤ lim.word →
    EncodePre lim μ src out scr tab p7 p10 V L a c →
    Meets lim P pE (d + 1) [L, j, src, out, scr, tab, p7, p10] μ (tEncP L j) fun _ μ' =>
      EncodePostP μ out scr L a c j μ'

variable {pS pE : ℕ}

/-- **One term**: step (2) and step (3) fill the leaves below the term number `lam` with at most `j`
symbols `P₀`, with the budget `j - dec` below, where `dec ≤ min j 1` and `dec = 0` if `lam ≠ 9`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encodeTerm_spec)
theorem encodeTermP_spec (hS : P[pS]? = some encStepBody)
    (hrec : EncodeMeetsP lim P pE d tab p7 p10 L c)
    (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c) (hd : d < lim.depth)
    (hj : (j : ℤ) ≤ lim.word) (hlam : lam < 10) {dec : ℕ} (hdec : dec ≤ j) (hdec1 : dec ≤ 1)
    (hdec' : lam ≠ 9 → dec = 0) (h : TermsDoneP μ out scr L a c j lam μ') (r : ℤ) :
    Ends lim P d (encodeTermP pS pE dec) ⟨frame (locals L j src out scr tab p7 p10 lam r), μ'⟩
      (tTermP L (j - dec) tEncP) fun σ' => ∃ (r' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame (locals L j src out scr tab p7 p10 lam r'), μ''⟩ ∧
          TermsDoneP μ out scr L a c j (lam + 1) μ'' := by
  have hplaces := pre.lay.places_succ
  -- The arguments of the two calls fit in a word, by the layout and the next facts.
  have hpart : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  have hprod : ((lam * 10 ^ L : ℕ) : ℤ) = lam * 10 ^ L := by rfl
  have hpow : ((7 ^ L : ℕ) : ℤ) = 7 ^ L := by rfl
  have hj' : j ≤ j - dec + if lam = 9 then 1 else 0 := by
    grind
  unfold encodeTermP tTermP
  -- Res := encStep(src, scr, 7^L, lam, tab)
  light_call (encStep_meets hS (EncodePre.toStep pre hlam h.2)) with r₁ μ₁ ⟨hstep, same₁⟩
  -- Res := encodeP(L, j - dec, scr, out + lam 10^L, scr + 7^L, tab, p7, p10)
  apply Ends.callTo (hrec (j - dec) _ _ _ _ _ _ (by omega)
    (EncodePre.toRec pre hlam h.2 hstep same₁))
  exact fun r₂ μ₂ hpost => ⟨r₂, μ₂, rfl, h.step pre.lay hlam same₁ hj' hpost⟩

/-! ## The recursion -/

/-- **A leaf**: the number is copied, whatever the budget. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encode_leaf)
theorem encodeP_leaf (pre : EncodePre lim μ src out scr tab p7 p10 V 0 a c) :
    Ends lim P d (encodePBody pS pE) ⟨frame [(0 : ℕ), j, src, out, scr, tab, p7, p10], μ⟩
      (tEncP 0 j) fun σ' => EncodePostP μ out scr 0 a c j σ'.mem := by
  light_facts pre.lay pre.lay.std
  have hread : μ src = a 0 := pre.srcV 0 (by norm_num)
  -- if Level = 0 then mem[Out] := mem[Src]
  refine Ends.iteLast (fun _ => ?_) (by simp) (hT := by tauto)
  refine Ends.storeTo out (a 0) ⟨fun τ _ => ?_, by light_keep⟩
    (by light_side [hread]) (by rfl)
  have h0 : codeT τ = 0 := by rfl
  aesop

/-- **An inner vertex**: the two lengths are read from the tables, the loop runs through the nine
terms `λ < 9`, and the term `P₀` is entered if the budget allows it. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encode_node)
theorem encodeP_node (hS : P[pS]? = some encStepBody)
    (hrec : EncodeMeetsP lim P pE d tab p7 p10 L c)
    (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c) (hd : d < lim.depth)
    (hj : (j : ℤ) ≤ lim.word) :
    Ends lim P d (encodePBody pS pE) ⟨frame [(L + 1 : ℕ), j, src, out, scr, tab, p7, p10], μ⟩
      (tEncP (L + 1) j) fun σ' => EncodePostP μ out scr (L + 1) a c j σ'.mem := by
  have hplaces := pre.lay.places_succ
  have haddr7 : (p7 + ((L : ℤ) + 1) - 1).toNat = p7 + L := by omega
  have haddr10 : (p10 + ((L : ℤ) + 1) - 1).toNat = p10 + L := by omega
  have htime : tEncP (L + 1) j = 104 + 9 * tTermP L j tEncP
      + 4 + if j = 0 then 0 else tTermP L (j - 1) tEncP := by
    cases j with
    | zero => rfl
    | succ j => grind [tEncP, tTermP]
  rw [htime]
  -- if Level = 0
  refine Ends.iteLast (fun h => absurd h (by simp; omega)) fun _ => ?_
  -- Len7 := mem[Pow7 + Level - 1]; Len10 := mem[Pow10 + Level - 1]
  light_set (7 ^ L) using haddr7, pre.p7V L (by omega)
  light_set (10 ^ L) using haddr10, pre.p10V L (by omega)
  -- for TermNo < 9: the leaves below the earlier terms are filled
  apply Ends.next (9 * (1 + tTermP L j tEncP + 7) + 1 + 5)
  refine Ends.forShape (fun lam r μ' => ⟨frame (locals L j src out scr tab p7 p10 lam r), μ'⟩)
    (TermsDoneP μ out scr L a c j) 9 _ 0
    ⟨by omega, .refl⟩
    fun lam r μ' hlam h => by
      simpa using encodeTermP_spec hS hrec pre hd hj (by omega) (Nat.zero_le j) (Nat.zero_le 1)
        (by omega) h r
    (fun r μ' h => ?_) (by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
  -- if Budget = 0 then skip else the two calls for P₀ with the budget j - 1
  refine Ends.iteLast (fun hc => ?_) fun hc => ?_
  · -- the budget is exhausted: nothing to do for P₀
    have hj : j = 0 := by simp_all
    subst hj
    exact Ends.skip h.skip.done
  · have hjne : j ≠ 0 := by simp_all
    apply (encodeTermP_spec hS hrec pre hd hj (by omega) (Nat.one_le_iff_ne_zero.2 hjne) le_rfl (by omega)
      h r).mono
      (by simp [hjne]; omega)
    rintro σ' ⟨r', μ'', rfl, h'⟩
    exact h'.done

/-- **encodeP** is correct and takes at most `tEncP L j` steps, in every program whose procedures
number pS and pE are encStep and encodeP.  It nests calls at most L deep. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encode_spec)
theorem encodeP_spec (hS : P[pS]? = some encStepBody) (hE : P[pE]? = some (encodePBody pS pE))
    (hd : d + L ≤ lim.depth) (hj : (j : ℤ) ≤ lim.word)
    (pre : EncodePre lim μ src out scr tab p7 p10 V L a c) :
    Ends lim P d (encodePBody pS pE) ⟨frame [L, j, src, out, scr, tab, p7, p10], μ⟩ (tEncP L j)
      fun σ' => EncodePostP μ out scr L a c j σ'.mem := by
  induction L generalizing d μ src out scr V a j with
  | zero => exact encodeP_leaf pre
  | succ L ih =>
    exact encodeP_node hS
      fun _ _ _ _ _ _ _ hj' pre' => by grind [Meets.of_body] pre (by omega) hj
