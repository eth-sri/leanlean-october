module

public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Lang.Frames
public import ThreeSumApsp.Spec.Sec3.Problems
public import ImprovedExponents.AllEdges.Task
public import ThreeSumApsp.Spec.Sec3.Theorem21b.NegativeTriangle
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.Tasks
public import ThreeSumApsp.Programs.Sec3.Theorem21b.NegativeTriangle.Passes
public import ThreeSumApsp.Lang.PolyBounded
public import ImprovedExponents.Pipeline.HostBound
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22

@[expose] public section

/-!
# Two loops over arrays for the reduction from all pairs to all-edges Exact Triangle

The host `pairsAE` (`ImprovedExponents.AllEdges.Pairs.Host`) asks a solver of all-edges Exact
Triangle `2b + 3` questions and takes, cell by cell, the disjunction of the answers; one of the
three matrices of a question is a transpose.  The two loops of this file do these two things.

* or(len, f, out) replaces out[i] by out[i] + f[i] − out[i] f[i] for i < len: the disjunction of
  two flags, in at most 31 len + 6 steps (`or_meets`; the pattern is upstream's `bump`).
* transpose(n, src, c, dst) writes src[i n + j] + c to dst[j n + i] for i, j < n, in at most
  30 n² + 20 n + 6 steps (`transpose_meets`): a loop over the columns j, whose body is a pass over
  the row j of the destination.
-/

namespace ImprovedExponents.AllEdges

open Light ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The disjunction of two arrays of flags -/

namespace OrPass

/-- The number of cells. -/
abbrev Len : ℕ := 0
/-- The address of the flags that are read. -/
abbrev Flags : ℕ := 1
/-- The address of the flags that are changed. -/
abbrev Dest : ℕ := 2
/-- The counter. -/
abbrev Index : ℕ := 3

end OrPass

open OrPass in
/-- or(len, f, out): for i < len, out[i] := out[i] + f[i] − out[i] · f[i]. -/
def orBody : Stmt :=
  pass Index (v Len) (v Dest)
    (M (v Dest +' v Index) +' M (v Flags +' v Index) -'
      M (v Dest +' v Index) *' M (v Flags +' v Index))

/-- The disjunction of two lists of flags, cell by cell. -/
def orL (L F : List ℤ) : List ℤ := List.zipWith (fun o f => o + f - o * f) L F

@[simp] theorem length_orL (L F : List ℤ) : (orL L F).length = min L.length F.length := by
  simp [orL]

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/Passes.lean (bump_meets)
/-- **or** replaces the flags at out by their disjunction with the flags at f, and changes nothing
else.  All flags are 0 or 1. -/
theorem or_meets {p : ℕ} (hp : P[p]? = some orBody) {μ : ℕ → ℤ} {fl out len : ℕ} {F L : List ℤ}
    (hF : Seg μ fl F) (hL : Seg μ out L) (hlen : F.length = len ∧ L.length = len)
    (hsep : Apart fl len out len)
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ fl + len ≤ lim.space ∧ out + len ≤ lim.space)
    (hflag : ∀ f ∈ F, f = 0 ∨ f = 1) (hL01 : ∀ o ∈ L, o = 0 ∨ o = 1) (hw : 1 ≤ lim.word) :
    Meets lim P p d [(len : ℤ), fl, out] μ (31 * len + 6) fun _ μ' =>
      Seg μ' out (orL L F) ∧ SameOutside μ μ' out len := by
  obtain ⟨lF, lL⟩ := hlen
  obtain ⟨hsp, hfl, hout⟩ := hlim
  set f : ℕ → ℤ := fun i => L.getD i 0 + F.getD i 0 - L.getD i 0 * F.getD i 0 with hf
  have hfi : ∀ i (hF : i < F.length) (hL : i < L.length), f i = L[i] + F[i] - L[i] * F[i] :=
    fun i hF hL => by
      rw [hf]
      simp only [List.getD_eq_getElem _ _ hF, List.getD_eq_getElem _ _ hL]
  refine .of_body hp (Ends.pass f (fun j hj => ?_) ?_ hsp hout rfl rfl)
  · -- round j reads f[j], which is never written, and out[j], which it then overwrites
    have hreadF : wrote μ out f j (fl + j) = F[j] :=
      (wrote_rest (by omega)).trans (hF j (by omega))
    have hreadL : wrote μ out f j (out + j) = L[j] :=
      (wrote_rest (by omega)).trans (hL j (by omega))
    rw [update_frame_setLocal]
    rcases hflag _ (List.getElem_mem (show j < F.length by omega)) with h | h <;>
    rcases hL01 _ (List.getElem_mem (show j < L.length by omega)) with h' | h'
    all_goals
      simp [Limits.Addr, abs_le, hreadF, hreadL, hfi j (by omega) (by omega), h, h']; omega
  · dsimp only
    refine ⟨seg_wrote (by simp [orL, lF, lL]) fun i hi => ?_, sameOutside_wrote le_rfl⟩
    simp only [orL, List.length_zipWith] at hi ⊢
    rw [List.getElem_zipWith]
    exact (hfi i (by omega) (by omega)).symm

/-! ## The transpose -/

namespace Transpose

/-- The side n of the matrix. -/
abbrev Side : ℕ := 0
/-- The address of the source. -/
abbrev Src : ℕ := 1
/-- The summand c. -/
abbrev Shift : ℕ := 2
/-- The address of the destination. -/
abbrev Dst : ℕ := 3
/-- The column j of the source. -/
abbrev Col : ℕ := 4
/-- The address of the row j of the destination. -/
abbrev Row : ℕ := 5
/-- The row i of the source. -/
abbrev Idx : ℕ := 6

end Transpose

open Transpose in
/-- The row j of the destination: for i < n, dst[j n + i] := src[i n + j] + c. -/
def transposeRow : Stmt :=
  .set Row (v Dst +' v Col *' v Side) ;;
  pass Idx (v Side) (v Row) (M (v Src +' v Idx *' v Side +' v Col) +' v Shift)

open Transpose in
/-- transpose(n, src, c, dst): for j < n, the row j of the destination. -/
def transposeBody : Stmt := .for Col (v Side) transposeRow

/-- The transpose of the `n × n` matrix `Y` (entry `(k, j)` at `k n + j`) with `c` added: cell
`q = j n + k` holds `Y[k n + j] + c`. -/
def transposeL (n : ℕ) (c : ℤ) (Y : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q => Y.getD (q % n * n + q / n) 0 + c

@[simp] theorem length_transposeL (n : ℕ) (c : ℤ) (Y : List ℤ) :
    (transposeL n c Y).length = n * n := by
  simp [transposeL]

/-- The entry `(j, k)` of the transpose. -/
theorem transposeL_getD {n : ℕ} (c : ℤ) (Y : List ℤ) {j k : ℕ} (hj : j < n) (hk : k < n) :
    (transposeL n c Y).getD (j * n + k) 0 = Y.getD (k * n + j) 0 + c := by
  have hq : j * n + k < n * n := by nlinarith
  have hdiv : (j * n + k) / n = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hk]
    simp
  have hmod : (j * n + k) % n = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  simp only [transposeL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq,
    Option.map_some, Option.getD_some, hdiv, hmod]

/-- The entries of the transpose of a matrix with entries in `[-U, U]`, with `c` added, lie in
`[c - U, c + U]`. -/
theorem mem_transposeL_bounds {n : ℕ} {Y : List ℤ} {U : ℤ} (hY : AbsLe Y U)
    (hlen : Y.length = n * n) (c : ℤ) : ∀ z ∈ transposeL n c Y, c - U ≤ z ∧ z ≤ c + U := by
  intro z hz
  simp only [transposeL, List.mem_map, List.mem_range] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  have hn : 0 < n := by rcases n with _ | n <;> simp_all
  have hidx : q % n * n + q / n < n * n := by
    have := Nat.mod_lt q hn
    have : q / n < n := by rwa [Nat.div_lt_iff_lt_mul hn]
    nlinarith
  have hmem : Y.getD (q % n * n + q / n) 0 ∈ Y := by
    rw [List.getD_eq_getElem _ _ (hlen ▸ hidx)]
    exact List.getElem_mem _
  have := abs_le.1 (hY _ hmem)
  constructor <;> omega

/-- The memory after the rows `0, …, j - 1` of the transpose have been written. -/
def tMem (μ : ℕ → ℤ) (dst n : ℕ) (c : ℤ) (Y : List ℤ) (j : ℕ) : ℕ → ℤ :=
  wrote μ dst (fun q => (transposeL n c Y).getD q 0) (j * n)

/-- The row `j` written on top of the rows below it. -/
theorem tMem_succ {μ : ℕ → ℤ} {dst n : ℕ} {c : ℤ} {Y : List ℤ} {j : ℕ} (hj : j < n) :
    wrote (tMem μ dst n c Y j) (dst + j * n) (fun i => Y.getD (i * n + j) 0 + c) n =
      tMem μ dst n c Y (j + 1) := by
  funext a
  simp only [tMem, wrote, Nat.succ_mul]
  by_cases h1 : dst + j * n ≤ a ∧ a < dst + j * n + n
  · rw [ite_eq_left h1, ite_eq_left (by omega)]
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < n ∧ a = dst + (j * n + i) :=
      ⟨a - dst - j * n, by omega, by omega⟩
    rw [show dst + (j * n + i) - (dst + j * n) = i by omega, Nat.add_sub_cancel_left,
      transposeL_getD c Y hj hi]
  · rw [ite_eq_right h1]
    by_cases h2 : dst ≤ a ∧ a < dst + j * n
    · rw [ite_eq_left h2, ite_eq_left (by omega)]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- **transpose** writes the transpose of the matrix at src, with c added to every entry, to the n²
cells from dst, and changes nothing else. -/
theorem transpose_meets {p : ℕ} (hp : P[p]? = some transposeBody) {μ : ℕ → ℤ} {src dst n : ℕ}
    {c : ℤ} {Y : List ℤ} (hY : Seg μ src Y) (hlen : Y.length = n * n)
    (hsep : Apart src (n * n) dst (n * n))
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ src + n * n ≤ lim.space ∧ dst + n * n ≤ lim.space)
    (hfits : ∀ y ∈ Y, |y + c| ≤ lim.word) :
    Meets lim P p d [(n : ℤ), src, c, dst] μ (30 * (n * n) + 20 * n + 6) fun _ μ' =>
      Seg μ' dst (transposeL n c Y) ∧ SameOutside μ μ' dst (n * n) := by
  obtain ⟨hsp, hsrc, hdst⟩ := hlim
  have : (n : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast (Nat.le_mul_self n).trans (by omega : n * n ≤ lim.space)) hsp
  refine .of_body hp ?_
  simp only [transposeBody]
  refine Ends.forShape (fun j (s : ℤ × ℤ) μ' => ⟨frame [n, src, c, dst, j, s.1, s.2], μ'⟩)
    (fun j μ' => μ' = tMem μ dst n c Y j) n (30 * n + 11) (0, 0) (by simp [tMem, wrote_zero])
    ?round ?done
    (first := by
      rw [update_frame_setLocal]
      exact congrArg (State.mk · μ) (frame_append_zeros _ 2).symm)
    (hT := by simp; nlinarith)
  case round =>
    rintro j s μ' hj rfl
    have hjn : j * n + n ≤ n * n := by nlinarith
    simp only [transposeRow]
    -- Row := Dst + Col * Side
    light_set (dst + j * n : ℕ)
    refine Ends.pass (fun i => Y.getD (i * n + j) 0 + c) (fun i hi => ?_) ?_ hsp (by omega) rfl rfl
      (hT := by simp; omega)
    · -- round i reads src[i n + j], which is never written
      have hin : i * n + j < n * n := by nlinarith
      have hread : wrote (tMem μ dst n c Y j) (dst + j * n) (fun i => Y.getD (i * n + j) 0 + c) i
          (src + (i * n + j)) = Y.getD (i * n + j) 0 := by
        rw [wrote_rest (by omega), tMem, wrote_rest (by omega), hY.getD (hlen ▸ hin)]
      have hmem : Y.getD (i * n + j) 0 ∈ Y := by
        rw [List.getD_eq_getElem _ _ (hlen ▸ hin)]
        exact List.getElem_mem _
      have hfit := abs_le.1 (hfits _ hmem)
      have htoNat : ((src : ℤ) + (i : ℤ) * n + j).toNat = src + (i * n + j) := by omega
      simp only [List.getD_eq_getElem?_getD] at hread hfit
      rw [update_frame_setLocal]
      have hjn' : ((i * n + j : ℕ) : ℤ) < ((n * n : ℕ) : ℤ) := by exact_mod_cast hin
      have hin' : ((j * n + n : ℕ) : ℤ) ≤ ((n * n : ℕ) : ℤ) := by exact_mod_cast hjn
      push_cast at hin' hjn'
      simp only [Expr.Safe, Op.eval, Expr.val, frame, setLocal, Nat.cast_add, Nat.cast_mul,
        List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
        Nat.lt_add_one, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
        Option.getD_some, Nat.ofNat_pos, true_and, Nat.one_lt_ofNat,
        List.getElem?_cons_succ, Nat.reduceLT, Limits.Addr, abs_le, htoNat, hread]
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> first | omega | trivial
    · refine ⟨((dst + j * n : ℕ), n), tMem μ dst n c Y (j + 1), ?_, rfl⟩
      rw [update_frame_setLocal, tMem_succ hj]
      rfl
  case done =>
    rintro s μ' rfl
    refine ⟨fun i hi => ?_, show SameOutside μ (tMem μ dst n c Y n) dst (n * n) from
      sameOutside_wrote le_rfl⟩
    simp only [length_transposeL] at hi
    change wrote μ dst (fun q => (transposeL n c Y).getD q 0) (n * n) (dst + i) = _
    rw [wrote_done hi, List.getD_eq_getElem _ _ (by simpa using hi)]






open Finset Light.Sec3 ThreeSumApsp.Spec

def shiftDiff (x y u ℓ : ℕ) : ℤ :=
  ((u / 2 ^ ℓ : ℕ) : ℤ) - ((x / 2 ^ ℓ : ℕ) : ℤ) - ((y / 2 ^ ℓ : ℕ) : ℤ)

theorem shiftDiff_zero (x y u : ℕ) : shiftDiff x y u 0 = (u : ℤ) - x - y := by
  simp [shiftDiff]

theorem shiftDiff_eq_zero {b x y u ℓ : ℕ} (hx : x < 2 ^ b) (hy : y < 2 ^ b) (hu : u < 2 ^ b)
    (hℓ : b ≤ ℓ) : shiftDiff x y u ℓ = 0 := by
  have hpow : 2 ^ b ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  simp [shiftDiff, Nat.div_eq_of_lt (hx.trans_le hpow), Nat.div_eq_of_lt (hy.trans_le hpow),
    Nat.div_eq_of_lt (hu.trans_le hpow)]

theorem shiftDiff_succ_bounds (x y u ℓ : ℕ) :
    2 * shiftDiff x y u (ℓ + 1) - 2 ≤ shiftDiff x y u ℓ
      ∧ shiftDiff x y u ℓ ≤ 2 * shiftDiff x y u (ℓ + 1) + 1 := by
  have h : ∀ n : ℕ, n / 2 ^ (ℓ + 1) = n / 2 ^ ℓ / 2 := fun n => by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  unfold shiftDiff
  rw [h x, h y, h u]
  generalize x / 2 ^ ℓ = X
  generalize y / 2 ^ ℓ = Y
  generalize u / 2 ^ ℓ = U
  omega

theorem two_le_shiftDiff_zero {x y u : ℕ} :
    ∀ ℓ, 2 ≤ shiftDiff x y u ℓ → 2 ≤ shiftDiff x y u 0
  | 0, h => h
  | ℓ + 1, h => two_le_shiftDiff_zero ℓ (by have := (shiftDiff_succ_bounds x y u ℓ).1; omega)

theorem exists_shiftDiff_eq {b x y u : ℕ} (hx : x < 2 ^ b) (hy : y < 2 ^ b) (hu : u < 2 ^ b) :
    ∀ d ℓ, ℓ + d = b → 2 ≤ shiftDiff x y u ℓ →
      ∃ ℓ' ≤ b, shiftDiff x y u ℓ' = 2 ∨ shiftDiff x y u ℓ' = 3 := by
  intro d
  induction d with
  | zero =>
    intro ℓ hℓ h2
    rw [shiftDiff_eq_zero hx hy hu (by omega)] at h2
    omega
  | succ d ih =>
    intro ℓ hℓ h2
    by_cases h : 2 ≤ shiftDiff x y u (ℓ + 1)
    · exact ih (ℓ + 1) (by omega) h
    · have := (shiftDiff_succ_bounds x y u ℓ).2
      exact ⟨ℓ, by omega, by omega⟩

theorem add_lt_iff_shiftDiff {b x y u : ℕ} (hx : x < 2 ^ b) (hy : y < 2 ^ b) (hu : u < 2 ^ b) :
    x + y < u ↔ shiftDiff x y u 0 = 1
      ∨ ∃ ℓ ≤ b, shiftDiff x y u ℓ = 2 ∨ shiftDiff x y u ℓ = 3 := by
  have := shiftDiff_zero x y u
  constructor
  · intro h
    by_cases h1 : shiftDiff x y u 0 = 1
    · exact Or.inl h1
    · exact Or.inr (exists_shiftDiff_eq hx hy hu b 0 (by omega) (by omega))
  · rintro (h1 | ⟨ℓ, -, h2⟩)
    · omega
    · have := two_le_shiftDiff_zero ℓ (by omega : 2 ≤ shiftDiff x y u ℓ)
      omega

def lemmaFInstances (b : ℕ) : Finset (ℕ × ℤ) := insert (0, 1) (range (b + 1) ×ˢ {2, 3})

theorem exists_mem_lemmaFInstances_iff (b : ℕ) (f : ℕ → ℤ) :
    (∃ c ∈ lemmaFInstances b, f c.1 = c.2) ↔ f 0 = 1 ∨ ∃ ℓ ≤ b, f ℓ = 2 ∨ f ℓ = 3 := by
  constructor
  · rintro ⟨⟨ℓ, r⟩, hc, hf⟩
    simp only [lemmaFInstances, mem_insert, Prod.mk.injEq, mem_product, mem_range,
      mem_singleton] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨hℓ, rfl | rfl⟩
    · exact Or.inl hf
    · exact Or.inr ⟨ℓ, by omega, Or.inl hf⟩
    · exact Or.inr ⟨ℓ, by omega, Or.inr hf⟩
  · rintro (h | ⟨ℓ, hℓ, h | h⟩)
    · exact ⟨(0, 1), mem_insert_self _ _, h⟩
    · exact ⟨(ℓ, 2), mem_insert_of_mem (mem_product.mpr ⟨mem_range.mpr (by omega), by simp⟩), h⟩
    · exact ⟨(ℓ, 3), mem_insert_of_mem (mem_product.mpr ⟨mem_range.mpr (by omega), by simp⟩), h⟩

theorem lt_iff_exists_instance {b W : ℕ} {p q t : ℤ} (hp : |p| ≤ W) (hq : |q| ≤ W)
    (hW : 2 * W < 2 ^ b) (ht : -(2 * W : ℤ) ≤ t) (ht' : t + 2 * W < 2 ^ b) :
    p + q < t ↔ ∃ c ∈ lemmaFInstances b,
      (p + W) / 2 ^ c.1 + (q + W) / 2 ^ c.1 + (c.2 - (t + 2 * W) / 2 ^ c.1) = 0 := by
  have := abs_le.mp hp
  have := abs_le.mp hq
  have : (2 * W : ℤ) < 2 ^ b := by exact_mod_cast hW
  obtain ⟨x, hx⟩ := Int.eq_ofNat_of_zero_le (by linarith : 0 ≤ p + W)
  obtain ⟨y, hy⟩ := Int.eq_ofNat_of_zero_le (by linarith : 0 ≤ q + W)
  obtain ⟨u, hu⟩ := Int.eq_ofNat_of_zero_le (by linarith : 0 ≤ t + 2 * W)
  have hxb : x < 2 ^ b := by exact_mod_cast (show (x : ℤ) < 2 ^ b by rw [← hx]; linarith)
  have hyb : y < 2 ^ b := by exact_mod_cast (show (y : ℤ) < 2 ^ b by rw [← hy]; linarith)
  have hub : u < 2 ^ b := by exact_mod_cast (show (u : ℤ) < 2 ^ b by rw [← hu]; exact ht')
  have hdiv : ∀ z ℓ : ℕ, (z : ℤ) / 2 ^ ℓ = ((z / 2 ^ ℓ : ℕ) : ℤ) := fun z ℓ => by norm_cast
  have hlt : p + q < t ↔ x + y < u := by omega
  rw [hlt, add_lt_iff_shiftDiff hxb hyb hub, ← exists_mem_lemmaFInstances_iff, hx, hy, hu]
  refine exists_congr fun c => and_congr_right fun _ => ?_
  rw [hdiv, hdiv, hdiv]
  unfold shiftDiff
  constructor <;> intro h <;> linarith

def aeLevels (U : ℕ) : ℕ := Nat.log 2 (3 * U) + 1

theorem lt_two_pow_aeLevels (U : ℕ) : 3 * U < 2 ^ aeLevels U :=
  Nat.lt_pow_succ_log_self (by norm_num) _

theorem two_pow_aeLevels_le {U : ℕ} (hU : 1 ≤ U) : 2 ^ aeLevels U ≤ 6 * U := by
  have := Nat.pow_log_le_self 2 (show 3 * U ≠ 0 by omega)
  rw [aeLevels, pow_succ]
  omega

def pStart (n U : ℕ) (X Y V : List ℤ) : List ℤ :=
  affL 1 U X ++ (transposeL n U Y ++ affL 1 (2 * U) V)

def instAC (U : ℕ) (X : List ℤ) (ℓ : ℕ) : List ℤ := (affL 1 U X).map (prefQ ℓ)

def instBC (n U : ℕ) (Y : List ℤ) (ℓ : ℕ) : List ℤ := (transposeL n U Y).map (prefQ ℓ)

def instAB (U : ℕ) (V : List ℤ) (ℓ : ℕ) (r : ℤ) : List ℤ :=
  affL (-1) r ((affL 1 (2 * U) V).map (prefQ ℓ))

section Lists

variable {n U : ℕ} {X Y V : List ℤ}

theorem length_pStart (hX : X.length = n * n) (hV : V.length = n * n) :
    (pStart n U X Y V).length = 3 * (n * n) := by
  simp only [pStart, List.length_append, length_affL, length_transposeL, hX, hV]
  omega

theorem pStart_range (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U) (hlenY : Y.length = n * n) :
    ∀ z ∈ pStart n U X Y V, 0 ≤ z ∧ z ≤ 3 * (U : ℤ) := by
  intro z hz
  simp only [pStart, List.mem_append] at hz
  rcases hz with hz | hz | hz
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    have := abs_le.1 (hX x hx)
    constructor <;> omega
  · have := mem_transposeL_bounds hY hlenY U z hz
    constructor <;> omega
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    have := abs_le.1 (hV x hx)
    constructor <;> omega

theorem getD_map_of_lt (f : ℤ → ℤ) {l : List ℤ} {idx : ℕ} (h : idx < l.length) :
    (l.map f).getD idx 0 = f (l.getD idx 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]

theorem absLe_map_prefQ {l : List ℤ} {B : ℤ} (h : ∀ z ∈ l, 0 ≤ z ∧ z ≤ B) (ℓ : ℕ) :
    ∀ z ∈ l.map (prefQ ℓ), 0 ≤ z ∧ z ≤ B := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  exact ⟨prefQ_nonneg (h y hy).1 ℓ, (prefQ_le (h y hy).1 ℓ).trans (h y hy).2⟩

theorem absLe_pStart_parts (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U)
    (hlenY : Y.length = n * n) (ℓ : ℕ) :
    (∀ z ∈ instAC U X ℓ, 0 ≤ z ∧ z ≤ 3 * (U : ℤ)) ∧
      (∀ z ∈ instBC n U Y ℓ, 0 ≤ z ∧ z ≤ 3 * (U : ℤ)) ∧
      ∀ z ∈ (affL 1 (2 * U) V).map (prefQ ℓ), 0 ≤ z ∧ z ≤ 3 * (U : ℤ) := by
  have h := absLe_map_prefQ (pStart_range hX hY hV hlenY) ℓ
  simp only [pStart, List.map_append, List.mem_append] at h
  exact ⟨fun z hz => h z (Or.inl hz), fun z hz => h z (Or.inr (Or.inl hz)),
    fun z hz => h z (Or.inr (Or.inr hz))⟩

theorem absLe_inst (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U) (hlenY : Y.length = n * n)
    (hU : 1 ≤ U) {ℓ : ℕ} {r : ℤ} (hr : 1 ≤ r ∧ r ≤ 3) :
    AbsLe (instAB U V ℓ r) ((9 * U : ℕ) : ℤ) ∧ AbsLe (instBC n U Y ℓ) ((9 * U : ℕ) : ℤ) ∧
      AbsLe (instAC U X ℓ) ((9 * U : ℕ) : ℤ) := by
  obtain ⟨h1, h2, h3⟩ := absLe_pStart_parts hX hY hV hlenY ℓ
  push_cast
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
    have := h3 y hy
    exact abs_le.2 ⟨by omega, by omega⟩
  · have := h2 z hz
    exact abs_le.2 ⟨by omega, by omega⟩
  · have := h1 z hz
    exact abs_le.2 ⟨by omega, by omega⟩

theorem pairFlags_iff (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U)
    (hlX : X.length = n * n) (hlY : Y.length = n * n) (hlV : V.length = n * n) {q : ℕ}
    (hq : q < n * n) :
    (pairFlags n X Y V).getD q 0 = 1 ↔ ∃ c ∈ lemmaFInstances (aeLevels U),
      (aeFlags n (instAB U V c.1 c.2) (instBC n U Y c.1) (instAC U X c.1)).getD q 0 = 1 := by
  have hn : 0 < n := by rcases n with _ | n <;> simp_all
  have hi : q / n < n := by rwa [Nat.div_lt_iff_lt_mul hn]
  have hj : q % n < n := Nat.mod_lt q hn
  have : q / n * n + q % n = q := Nat.div_add_mod' q n
  have hbN := lt_two_pow_aeLevels U
  have hb : (3 * U : ℤ) < 2 ^ aeLevels U := by exact_mod_cast hbN
  have hidx : ∀ {a b : ℕ}, a < n → b < n → a * n + b < n * n := fun ha hb => by nlinarith
  have hmem : ∀ (l : List ℤ), l.length = n * n → ∀ {idx : ℕ}, idx < n * n → l.getD idx 0 ∈ l :=
    fun l hl _ h => by rw [List.getD_eq_getElem _ _ (hl ▸ h)]; exact List.getElem_mem _
  have := abs_le.1 (hV _ (hmem V hlV hq))
  have hrange : ∀ f : ℕ → ℤ, ((List.range (n * n)).map f).getD q 0 = f q := fun f => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_range hq]
  have hmap : ∀ (l : List ℤ) (f : ℤ → ℤ) (idx : ℕ), idx < n * n → l.length = n * n →
      (l.map f).getD idx 0 = f (l.getD idx 0) := fun l f idx h hl => getD_map_of_lt f (hl ▸ h)
  simp only [pairFlags, aeFlags, hrange, flag_eq_one_iff]
  have hstep : ∀ k < n, (X.getD (q / n * n + k) 0 + Y.getD (k * n + q % n) 0 < V.getD q 0) ↔
      ∃ c ∈ lemmaFInstances (aeLevels U),
        (instAB U V c.1 c.2).getD q 0 +
          (instBC n U Y c.1).getD (q % n * n + k) 0 +
          (instAC U X c.1).getD (q / n * n + k) 0 = 0 := fun k hk => by
    rw [lt_iff_exists_instance (b := aeLevels U) (hX _ (hmem X hlX (hidx hi hk)))
      (hY _ (hmem Y hlY (hidx hk hj))) (by omega) (by omega) (by omega)]
    refine exists_congr fun c => and_congr_right fun _ => ?_
    simp only [instAB, instBC, instAC, affL]
    rw [hmap _ _ _ hq (by simp [hlV]), hmap _ _ _ hq (by simp [hlV]), hmap _ _ _ hq hlV,
      hmap _ _ _ (hidx hj hk) (by simp), transposeL_getD _ _ hj hk,
      hmap _ _ _ (hidx hi hk) (by simp [hlX]), hmap _ _ _ (hidx hi hk) hlX]
    simp only [prefQ, one_mul]
    constructor <;> intro h <;> linarith
  exact ⟨fun ⟨k, hk, h⟩ => let ⟨c, hc, h'⟩ := (hstep k hk).1 h; ⟨c, hc, k, hk, h'⟩,
    fun ⟨c, hc, k, hk, h'⟩ => ⟨k, hk, (hstep k hk).2 ⟨c, hc, h'⟩⟩⟩

end Lists

/-! ## The disjunction of the flags of the instances asked so far -/

/-- The flags of the pairs: cell `q` holds 1 if some instance `c` with `S c` has the flag 1 at
`q`, where `hit c q` says that it has. -/
noncomputable def orFlags (N : ℕ) (S : ℕ × ℤ → Prop) (hit : ℕ × ℤ → ℕ → Prop) : List ℤ :=
  (List.range N).map fun q => flag (∃ c, S c ∧ hit c q)

@[simp] theorem length_orFlags (N : ℕ) (S : ℕ × ℤ → Prop) (hit : ℕ × ℤ → ℕ → Prop) :
    (orFlags N S hit).length = N := by
  simp [orFlags]

theorem orFlags_mem (N : ℕ) (S : ℕ × ℤ → Prop) (hit : ℕ × ℤ → ℕ → Prop) :
    ∀ z ∈ orFlags N S hit, z = 0 ∨ z = 1 := by
  intro z hz
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hz
  unfold flag
  split_ifs <;> simp

/-- Before any question the flags are zero. -/
theorem orFlags_false (N : ℕ) (hit : ℕ × ℤ → ℕ → Prop) {l : List ℤ} (hl : l.length = N) :
    orFlags N (fun _ => False) hit = affL 0 0 l := by
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  simp [orFlags, affL, flag]

/-- The disjunction with the flags of one more instance. -/
theorem orL_orFlags {N : ℕ} {S : ℕ × ℤ → Prop} {hit : ℕ × ℤ → ℕ → Prop} {c : ℕ × ℤ} {F : List ℤ}
    (hF : F.length = N) (hhit : ∀ q < N, hit c q ↔ F.getD q 0 = 1)
    (h01 : ∀ f ∈ F, f = 0 ∨ f = 1) :
    orL (orFlags N S hit) F = orFlags N (fun c' => S c' ∨ c' = c) hit := by
  refine List.ext_getElem (by simp [hF]) fun i h1 h2 => ?_
  have hi : i < N := by simpa using h2
  have hFi : F.getD i 0 = F[i] := List.getD_eq_getElem _ _ (hF ▸ hi)
  have hc := hhit i hi
  rw [hFi] at hc
  simp only [orL, orFlags, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  rcases h01 _ (List.getElem_mem (hF ▸ hi)) with h | h
  · rw [h, flag_congr (show (∃ c', (S c' ∨ c' = c) ∧ hit c' i) ↔ ∃ c', S c' ∧ hit c' i from
      ⟨fun ⟨c', hc', hh⟩ => ⟨c', hc'.resolve_right fun he => by
        rw [he] at hh; exact absurd (hc.1 hh) (by rw [h]; decide), hh⟩,
        fun ⟨c', hc', hh⟩ => ⟨c', Or.inl hc', hh⟩⟩)]
    ring
  · rw [h, flag_of (p := ∃ c', (S c' ∨ c' = c) ∧ hit c' i) ⟨c, Or.inr rfl, hc.2 h⟩]
    unfold flag
    split_ifs <;> ring

/-- The instances at the levels above `ℓ` (and at most `b`) with `r ∈ {2, 3}`. -/
def Above (ℓ b : ℕ) (c : ℕ × ℤ) : Prop := ℓ < c.1 ∧ c.1 ≤ b ∧ (c.2 = 2 ∨ c.2 = 3)

/-- The two questions at the level `ℓ + 1` bring the asked set from above `ℓ + 1` to above `ℓ`. -/
theorem above_step {ℓ b : ℕ} (h : ℓ + 1 ≤ b) (c : ℕ × ℤ) :
    ((Above (ℓ + 1) b c ∨ c = (ℓ + 1, 2)) ∨ c = (ℓ + 1, 3)) ↔ Above ℓ b c := by
  obtain ⟨l, r⟩ := c
  simp only [Above, Prod.mk.injEq]
  constructor
  · rintro ((⟨h1, h2, h3⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) <;> omega
  · rintro ⟨h1, h2, h3⟩
    by_cases hl : l = ℓ + 1
    · subst hl
      rcases h3 with rfl | rfl <;> simp
    · exact Or.inl (Or.inl ⟨by omega, h2, h3⟩)

/-- Nothing has been asked at the top. -/
theorem above_self (b : ℕ) (c : ℕ × ℤ) : ¬ Above b b c := fun h => by
  have := h.1
  have := h.2.1
  omega

/-- After the questions at the level `0`, all instances of Lemma F have been asked. -/
theorem above_zero_iff (b : ℕ) (c : ℕ × ℤ) :
    (((Above 0 b c ∨ c = (0, 2)) ∨ c = (0, 3)) ∨ c = (0, 1)) ↔ c ∈ lemmaFInstances b := by
  obtain ⟨l, r⟩ := c
  simp only [Above, Prod.mk.injEq, lemmaFInstances, Finset.mem_insert, Finset.mem_product,
    Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (((⟨h1, h2, h3⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩)
    · exact Or.inr ⟨by omega, h3⟩
    · exact Or.inr ⟨by omega, Or.inl rfl⟩
    · exact Or.inr ⟨by omega, Or.inr rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨h1, h3⟩)
    · exact Or.inr ⟨rfl, rfl⟩
    · by_cases hl : l = 0
      · subst hl
        rcases h3 with rfl | rfl <;> simp
      · exact Or.inl (Or.inl (Or.inl ⟨by omega, by omega, h3⟩))

/-- **The flags of all pairs** are the disjunction of the flags of the instances of Lemma F. -/
theorem orFlags_eq_pairFlags {n U : ℕ} {X Y V : List ℤ} (hX : AbsLe X U) (hY : AbsLe Y U)
    (hV : AbsLe V U) (hlX : X.length = n * n) (hlY : Y.length = n * n) (hlV : V.length = n * n) :
    orFlags (n * n) (fun c => c ∈ lemmaFInstances (aeLevels U))
      (fun c q => (aeFlags n (instAB U V c.1 c.2) (instBC n U Y c.1) (instAC U X c.1)).getD q 0 = 1)
      = pairFlags n X Y V := by
  refine List.ext_getElem (by simp [pairFlags]) fun q h1 h2 => ?_
  have hq : q < n * n := by simpa using h1
  have h := pairFlags_iff hX hY hV hlX hlY hlV hq
  rw [List.getD_eq_getElem _ _ (by simp [pairFlags, hq])] at h
  simp only [orFlags, List.getElem_map, List.getElem_range]
  by_cases hp : (pairFlags n X Y V)[q] = 1
  · rw [hp, flag_of (h.1 hp)]
  · rw [flag_of_not fun hh => hp (h.2 hh)]
    have : (pairFlags n X Y V)[q] = 0 ∨ (pairFlags n X Y V)[q] = 1 := by
      simp only [pairFlags, List.getElem_map, List.getElem_range]
      unfold flag
      split_ifs <;> simp
    omega


/-!
# All pairs from all-edges Exact Triangle, as a host

Footnote 10 of the paper: the (min,+)-product reduces to all-edges Exact Triangle on the same `n`
vertices.  The threshold questions of upstream's `pairsTask` are answered, by Lemma F
(`ImprovedExponents.add_lt_iff_shiftDiff`), with `2b + 3` all-edges instances, `b = aeLevels U`.

pairsAE(n, U, x, y, v, out, fr) computes `b` and `2^b`, writes `X + U`, the transpose of `Y` plus
`U`, and `V + 2U` into an array r of `3n²` cells, zeros into an array q of `3n²` cells and into
out.  Then it makes `b` rounds: at the level `ℓ = b, …, 1` it asks, for `e = 2` and `e = 3`, the
all-edges instance with the third matrix `e − ⌊(V + 2U)/2^ℓ⌋` and takes the disjunction of the
answer into out (`or`), and then moves one more bit of every number from r to q (upstream's
`prefDown`).  At the level `0` it asks for `e = 2, 3, 1`.  The flags in out are then those of
`pairsTask` (`orFlags_eq_pairFlags`).

The text follows upstream's host from Negative Triangle to Exact Triangle
(`ThreeSumApsp/Programs/Sec3/Theorem21b/NegativeTriangle/Host.lean`); `isHost_pairsAE` is the
result.
-/



/-! ## The text -/

namespace PairsHost

/-- The number n of vertices. -/
abbrev Verts : ℕ := 0
/-- The bound U on the entries. -/
abbrev Bound : ℕ := 1
/-- The address of X. -/
abbrev MatX : ℕ := 2
/-- The address of Y. -/
abbrev MatY : ℕ := 3
/-- The address of V. -/
abbrev MatV : ℕ := 4
/-- The address of the flags. -/
abbrev Out : ℕ := 5
/-- The free pointer, where the array q begins: the prefixes of X + U. -/
abbrev PreX : ℕ := 6
/-- n². -/
abbrev Cells : ℕ := 7
/-- 2^b. -/
abbrev Power : ℕ := 8
/-- The number b of levels. -/
abbrev Levels : ℕ := 9
/-- The number of the round. -/
abbrev Round : ℕ := 10
/-- The result of a call. -/
abbrev Res : ℕ := 11
/-- 3U. -/
abbrev Bound3 : ℕ := 12
/-- The prefixes of the transpose of Y plus U. -/
abbrev PreY : ℕ := 13
/-- The prefixes of V + 2U. -/
abbrev PreV : ℕ := 14
/-- The first part of the array r. -/
abbrev RestX : ℕ := 15
/-- The second part of the array r. -/
abbrev RestY : ℕ := 16
/-- The third part of the array r. -/
abbrev RestV : ℕ := 17
/-- The array for the third matrix of a question. -/
abbrev Third : ℕ := 18
/-- The array for the answer of a question. -/
abbrev Flg : ℕ := 19
/-- The free pointer for the solver. -/
abbrev SolverFree : ℕ := 20
/-- 3n². -/
abbrev Cells3 : ℕ := 21
/-- 9U. -/
abbrev Bound9 : ℕ := 22

end PairsHost

open PairsHost

/-- The beginning of pairsAE: sizes and addresses. -/
def paInit : Stmt :=
  .set Cells (v Verts *' v Verts) ;;
  .set Bound3 (k 3 *' v Bound) ;;
  .set Bound9 (k 9 *' v Bound) ;;
  .set PreY (v PreX +' v Cells) ;;
  .set PreV (v PreY +' v Cells) ;;
  .set RestX (v PreV +' v Cells) ;;
  .set RestY (v RestX +' v Cells) ;;
  .set RestV (v RestY +' v Cells) ;;
  .set Third (v RestV +' v Cells) ;;
  .set Flg (v Third +' v Cells) ;;
  .set SolverFree (v Flg +' v Cells) ;;
  .set Cells3 (k 3 *' v Cells) ;;
  .set Power (k 1) ;;
  .set Levels (k 0)

/-- The number of levels b and the power 2^b, by doubling. -/
def paPow : Stmt :=
  .while (v Power ≤' v Bound3) (
    .set Power (k 2 *' v Power) ;;
    .set Levels (v Levels +' k 1))

/-- The arrays r and q at the top level, and zeros in out. -/
def paFill (pAff pTr : ℕ) : Stmt :=
  .call pAff [v Cells, v MatX, k 1, v Bound, v RestX] Res ;;
  .call pTr [v Verts, v MatY, v Bound, v RestY] Res ;;
  .call pAff [v Cells, v MatV, k 1, k 2 *' v Bound, v RestV] Res ;;
  .call pAff [v Cells3, v RestX, k 0, k 0, v PreX] Res ;;
  .call pAff [v Cells, v MatX, k 0, k 0, v Out] Res

/-- One question to the solver of all-edges Exact Triangle: the third matrix for the value e, the
call, and the disjunction of the answer into out. -/
def paProbe (pAE pAff pOr e : ℕ) : Stmt :=
  .call pAff [v Cells, v PreV, k 0 -' k 1, k e, v Third] Res ;;
  .call pAE [v Verts, v Bound9, v Third, v PreY, v PreX, v Flg, v SolverFree] Res ;;
  .call pOr [v Cells, v Flg, v Out] Res

/-- One round: the two questions at the level, then the next level. -/
def paRound (pAE pAff pOr pDown : ℕ) : Stmt :=
  paProbe pAE pAff pOr 2 ;; paProbe pAE pAff pOr 3 ;;
  .call pDown [v Cells3, v PreX, v RestX, v Power] Res

/-- pairsAE(n, U, x, y, v, out, fr). -/
def paBody (pAE pAff pTr pOr pDown : ℕ) : Stmt :=
  paInit ;; paPow ;; paFill pAff pTr ;; .for Round (v Levels) (paRound pAE pAff pOr pDown) ;;
  paProbe pAE pAff pOr 2 ;; paProbe pAE pAff pOr 3 ;; paProbe pAE pAff pOr 1 ;; .set 0 (k 0)

/-- The time of pairsAE, if the solver of all-edges Exact Triangle takes T n U steps: `2b + 3`
calls of the solver, each with O(n²) work around it, and O(n²) work at the start. -/
def pairsTimeAE (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  (2 * aeLevels U + 3) * (T n (9 * U) + 108 * (n * n) + 60) + 200 * (n * n) + 150

/-- The need of pairsAE, if the solver needs r n U. -/
def pairsNeedAE (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := 24 * U + 8 + (r n (9 * U)).word
  cells := 8 * (n * n) + (r n (9 * U)).cells
  depth := (r n (9 * U)).depth + 1

/-! ## The local variables and the hypotheses -/

namespace PairsHost

/-- The locals of pairsAE after its beginning; the last four are those that change later. -/
abbrev locals (x : PairsInst) (fr : ℕ) (pw lv rd res : ℤ) : List ℤ :=
  [x.n, x.U, x.x, x.y, x.v, x.out, fr, (x.n * x.n : ℕ), pw, lv, rd, res, (3 * x.U : ℕ),
    (fr + x.n * x.n : ℕ), (fr + 2 * (x.n * x.n) : ℕ), (fr + 3 * (x.n * x.n) : ℕ),
    (fr + 4 * (x.n * x.n) : ℕ), (fr + 5 * (x.n * x.n) : ℕ), (fr + 6 * (x.n * x.n) : ℕ),
    (fr + 7 * (x.n * x.n) : ℕ), (fr + 8 * (x.n * x.n) : ℕ), (3 * (x.n * x.n) : ℕ), (9 * x.U : ℕ)]

/-- The program has the solver and the four loops over arrays, the instance is as the task
prescribes, and the limits allow for the need of pairsAE. -/
structure Ctx (P₀ R' : Program) (p pAff pTr pOr pDown : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need)
    (lim : Limits) (d : ℕ) (x : PairsInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  solver : Solves aeTask P₀ p T r
  aff : (P₀ ++ R')[pAff]? = some affineBody
  tr : (P₀ ++ R')[pTr]? = some transposeBody
  orp : (P₀ ++ R')[pOr]? = some orBody
  down : (P₀ ++ R')[pDown]? = some prefDownBody
  pre : x.Pre μ fr
  ok : (pairsNeedAE r x.n x.U).Ok lim fr d

variable {P₀ R' : Program} {p pAff pTr pOr pDown : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
  {lim : Limits} {d : ℕ} {x : PairsInst} {μ : ℕ → ℤ} {fr : ℕ}

/-- The start list of the instance. -/
abbrev Z (x : PairsInst) : List ℤ := pStart x.n x.U x.X x.Y x.V

/-- The flag of the instance `c` at the cell `q`. -/
def hit (x : PairsInst) (c : ℕ × ℤ) (q : ℕ) : Prop :=
  (aeFlags x.n (instAB x.U x.V c.1 c.2) (instBC x.n x.U x.Y c.1) (instAC x.U x.X c.1)).getD q 0 = 1

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem21b/NegativeTriangle/Host.lean
/-- The arithmetic facts of the hypotheses as one conjunction. -/
theorem Ctx.places (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) :
    ((lim.space : ℤ) ≤ lim.word ∧ 24 * (x.U : ℤ) + 8 + (r x.n (9 * x.U)).word ≤ lim.word ∧
      fr + (8 * (x.n * x.n) + (r x.n (9 * x.U)).cells) ≤ lim.space ∧
      d + ((r x.n (9 * x.U)).depth + 1) ≤ lim.depth) ∧ 1 ≤ x.n * x.n ∧ 1 ≤ x.U ∧
      (x.X.length = x.n * x.n ∧ x.Y.length = x.n * x.n ∧ x.V.length = x.n * x.n) ∧
      x.x + x.n * x.n ≤ fr ∧ x.y + x.n * x.n ≤ fr ∧ x.v + x.n * x.n ≤ fr ∧
      x.out + x.n * x.n ≤ fr ∧ (Z x).length = 3 * (x.n * x.n) ∧
      3 * x.U < 2 ^ aeLevels x.U ∧ 2 ^ aeLevels x.U ≤ 6 * x.U :=
  ⟨⟨C.ok.space, by exact_mod_cast C.ok.word, C.ok.cells, C.ok.depth⟩,
    Nat.mul_pos C.pre.n_pos C.pre.n_pos, C.pre.U_pos, ⟨C.pre.lenX, C.pre.lenY, C.pre.lenV⟩,
    C.pre.belowX, C.pre.belowY, C.pre.belowV, C.pre.belowOut,
    length_pStart C.pre.lenX C.pre.lenV, lt_two_pow_aeLevels _,
    two_pow_aeLevels_le C.pre.U_pos⟩

/-- **affine** as a procedure, for a source and a destination that lie apart, below the free pointer
of the solver. -/
theorem Ctx.affine_meets (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {μ' : ℕ → ℤ}
    {l : List ℤ} {src dst : ℕ} {m c : ℤ} (hl : Seg μ' src l)
    (hplace : src + l.length ≤ fr + 8 * (x.n * x.n) ∧ dst + l.length ≤ fr + 8 * (x.n * x.n) ∧
      (src + l.length ≤ dst ∨ dst + l.length ≤ src))
    (hfits : ∀ w ∈ l, |m * w| ≤ lim.word ∧ |m * w + c| ≤ lim.word) :
    Meets lim (P₀ ++ R') pAff (d + 1) [l.length, src, m, c, dst] μ' (20 * l.length + 6)
      fun _ μ'' => Seg μ'' dst (affL m c l) ∧ SameOutside μ' μ'' dst l.length := by
  have := C.places
  exact Sec3.affine_meets C.aff hl C.ok.space (by omega) (by omega) hplace.2.2 hfits

/-! ## The beginning -/

/-- **The beginning** sets the sizes and the addresses. -/
theorem init_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) :
    Ends lim (P₀ ++ R') d paInit ⟨frame [x.n, x.U, x.x, x.y, x.v, x.out, fr], μ⟩ paInit.blockCost
      fun σ' => σ' = ⟨frame (locals x fr 1 0 0 0), μ⟩ := by
  have := C.places
  have : (0 : ℤ) ≤ (x.n : ℤ) * x.n := by positivity
  unfold paInit
  light_set (x.n * x.n : ℕ)
  light_set (3 * x.U : ℕ)
  light_set (9 * x.U : ℕ)
  light_set (fr + x.n * x.n : ℕ)
  light_set (fr + 2 * (x.n * x.n) : ℕ)
  light_set (fr + 3 * (x.n * x.n) : ℕ)
  light_set (fr + 4 * (x.n * x.n) : ℕ)
  light_set (fr + 5 * (x.n * x.n) : ℕ)
  light_set (fr + 6 * (x.n * x.n) : ℕ)
  light_set (fr + 7 * (x.n * x.n) : ℕ)
  light_set (fr + 8 * (x.n * x.n) : ℕ)
  light_set (3 * (x.n * x.n) : ℕ)
  light_set 1
  light_set 0
  rfl

/-- The state of the loop that doubles after i rounds. -/
def PowInv (x : PairsInst) (μ : ℕ → ℤ) (fr i : ℕ) (σ : State) : Prop :=
  σ = ⟨frame (locals x fr (2 ^ i : ℕ) i 0 0), μ⟩

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem21b/NegativeTriangle/Host.lean
/-- **The loop that doubles** computes the number b of levels and 2^b. -/
theorem pow_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) :
    Ends lim (P₀ ++ R') d paPow ⟨frame (locals x fr 1 0 0 0), μ⟩ (14 * aeLevels x.U + 6)
      fun σ' => σ' = ⟨frame (locals x fr (2 ^ aeLevels x.U : ℕ) (aeLevels x.U) 0 0), μ⟩ := by
  have hplaces := C.places
  refine Ends.whileBlock (PowInv x μ fr) (aeLevels x.U) (by simp [PowInv]) ?round ?done
    (by simp; omega)
  case round =>
    rintro i _ hi rfl
    have hpow : 2 ^ (i + 1) ≤ 2 ^ aeLevels x.U := Nat.pow_le_pow_right (by norm_num) hi
    have hlt : i + 1 < 2 ^ (i + 1) := Nat.lt_two_pow_self
    rw [pow_succ'] at hpow hlt
    generalize hpw : 2 ^ i = pw at hpow hlt ⊢
    exact ⟨by light_side, by simp; omega, by light_side,
      by simp [PowInv, pow_succ', hpw, update_frame_setLocal, locals]⟩
  case done =>
    rintro _ rfl
    generalize 2 ^ aeLevels x.U = pw at hplaces ⊢
    exact ⟨by light_side, by simp; omega, rfl⟩

/-! ## The memory -/

/-- The memory at the level ℓ with the asked set S: q holds the prefixes, r the rests, out the
disjunction of the flags of the instances in S, and nothing else below the free pointer changed. -/
def PMem (x : PairsInst) (μ : ℕ → ℤ) (fr ℓ : ℕ) (S : ℕ × ℤ → Prop) (μ' : ℕ → ℤ) : Prop :=
  Seg μ' fr ((Z x).map (prefQ ℓ)) ∧
    Seg μ' (fr + 3 * (x.n * x.n)) ((Z x).map (prefR (aeLevels x.U) ℓ)) ∧
    Seg μ' x.out (orFlags (x.n * x.n) S (hit x)) ∧ KeptBut μ μ' fr x.out (x.n * x.n)

/-- The numbers in the array r at the top level lie in `[0, 3U]`, below `2^b`. -/
theorem Z_range (hpre : x.Pre μ fr) :
    ∀ z ∈ Z x, 0 ≤ z ∧ z ≤ 3 * (x.U : ℤ) ∧ z < 2 ^ aeLevels x.U := by
  intro z hz
  obtain ⟨h0, h1⟩ := pStart_range hpre.leX hpre.leY hpre.leV hpre.lenY z hz
  have h2 : ((3 * x.U : ℕ) : ℤ) < ((2 ^ aeLevels x.U : ℕ) : ℤ) := by
    exact_mod_cast lt_two_pow_aeLevels x.U
  push_cast at h2
  exact ⟨h0, h1, by omega⟩

/-- The three parts of the array q. -/
theorem seg_parts (hpre : x.Pre μ fr) {μ' : ℕ → ℤ} {ℓ : ℕ}
    (hq : Seg μ' fr ((Z x).map (prefQ ℓ))) :
    Seg μ' fr (instAC x.U x.X ℓ) ∧ Seg μ' (fr + x.n * x.n) (instBC x.n x.U x.Y ℓ) ∧
      Seg μ' (fr + 2 * (x.n * x.n)) ((affL 1 (2 * x.U) x.V).map (prefQ ℓ)) := by
  simp only [Z, pStart, List.map_append] at hq
  rw [seg_append, seg_append] at hq
  simp only [List.length_map, length_affL, length_transposeL, hpre.lenX] at hq
  rwa [show fr + x.n * x.n + x.n * x.n = fr + 2 * (x.n * x.n) by omega] at hq

/-- **The five calls** fill the arrays r and q for the top level and zero out. -/
theorem fill_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) (pw lv rd res : ℤ) :
    Ends lim (P₀ ++ R') d (paFill pAff pTr) ⟨frame (locals x fr pw lv rd res), μ⟩
      (170 * (x.n * x.n) + 70) fun σ' => ∃ res' μ',
        σ' = ⟨frame (locals x fr pw lv rd res'), μ'⟩ ∧
          PMem x μ fr (aeLevels x.U) (fun _ => False) μ' := by
  have hpre := C.pre
  have hplaces := C.places
  have hZ := Z_range hpre
  have hn : x.n ≤ x.n * x.n := Nat.le_mul_self x.n
  have hapX := hpre.apartX
  have hW : 24 * (x.U : ℤ) + 8 ≤ lim.word := by omega
  have hfit1 : ∀ c : ℤ, c = x.U ∨ c = 2 * x.U → ∀ w ∈ x.V ++ x.X, |1 * w| ≤ lim.word ∧
      |1 * w + c| ≤ lim.word := fun c hc w hw => by
    have := abs_le.1 ((List.mem_append.1 hw).elim (hpre.leV w) (hpre.leX w))
    simp only [one_mul, abs_le]
    rcases hc with rfl | rfl <;> omega
  unfold paFill
  -- Res := pAff(Cells, MatX, 1, Bound, RestX)
  refine Ends.callToThen (C.affine_meets (m := 1) (c := x.U) (dst := fr + 3 * (x.n * x.n))
    hpre.segX (by omega) fun w hw => hfit1 _ (Or.inl rfl) w (by simp [hw])) ?_
    (ha := by light_side [hpre.lenX]) (hT := by simp [hpre.lenX]; omega)
  rintro r₁ μ₁ ⟨s₁, o₁⟩
  -- Res := pTr(Verts, MatY, Bound, RestY)
  refine Ends.callToThen (transpose_meets C.tr (dst := fr + 4 * (x.n * x.n)) (c := x.U)
    hpre.segY.keep hpre.lenY (by omega) ⟨C.ok.space, by omega, by omega⟩ fun w hw => by
      have := abs_le.1 (hpre.leY w hw); rw [abs_le]; omega) ?_
    (ha := by light_side) (hT := by simp [hpre.lenX]; omega)
  rintro r₂ μ₂ ⟨s₂, o₂⟩
  -- Res := pAff(Cells, MatV, 1, 2 * Bound, RestV)
  refine Ends.callToThen (C.affine_meets (m := 1) (c := 2 * x.U) (dst := fr + 5 * (x.n * x.n))
    hpre.segV.keep (by omega) fun w hw => hfit1 _ (Or.inr rfl) w (by simp [hw])) ?_
    (ha := by light_side [hpre.lenV]) (hT := by simp [hpre.lenX, hpre.lenV]; omega)
  rintro r₃ μ₃ ⟨s₃, o₃⟩
  have sZ : Seg μ₃ (fr + 3 * (x.n * x.n)) (Z x) := by
    rw [Z, pStart, seg_append, seg_append]
    simp only [length_affL, length_transposeL, hpre.lenX]
    rw [show fr + 3 * (x.n * x.n) + x.n * x.n = fr + 4 * (x.n * x.n) by omega,
      show fr + 4 * (x.n * x.n) + x.n * x.n = fr + 5 * (x.n * x.n) by omega]
    exact ⟨s₁.keep, s₂.keep, s₃⟩
  -- Res := pAff(Cells3, RestX, 0, 0, PreX)
  refine Ends.callToThen (C.affine_meets (m := 0) (c := 0) (dst := fr) sZ (by omega)
    fun w _ => by simp; omega) ?_ (ha := by light_side) (hT := by simp; omega)
  rintro r₄ μ₄ ⟨s₄, o₄⟩
  -- Res := pAff(Cells, MatX, 0, 0, Out)
  refine Ends.callTo (C.affine_meets (m := 0) (c := 0) (dst := x.out) hpre.segX.keep (by omega)
    fun w _ => by simp; omega) ?_ (ha := by light_side [hpre.lenX])
    (hT := by simp [hpre.lenX]; omega)
  rintro r₅ μ₅ ⟨s₅, o₅⟩
  refine ⟨r₅, μ₅, rfl, ?_, ?_, ?_, fun c hc => ?_⟩
  · rw [map_prefQ_start fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.2⟩]
    exact s₄.keep
  · rw [map_prefR_start fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.2⟩]
    exact sZ.keep
  · rw [orFlags_false _ _ hpre.lenX]
    exact s₅
  · light_keep

/-! ## One question -/

/-- The instance of all-edges Exact Triangle for the level ℓ and the value e, as it lies in the
arrays. -/
def question (x : PairsInst) (fr ℓ : ℕ) (e : ℤ) : AeInst :=
  ⟨x.n, 9 * x.U, fr + 6 * (x.n * x.n), fr + x.n * x.n, fr, fr + 7 * (x.n * x.n),
    instAB x.U x.V ℓ e, instBC x.n x.U x.Y ℓ, instAC x.U x.X ℓ⟩

/-- The question is an instance as the task prescribes. -/
theorem question_pre (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {μ' : ℕ → ℤ}
    {ℓ : ℕ} {e : ℤ} (he : 1 ≤ e ∧ e ≤ 3) (hq : Seg μ' fr ((Z x).map (prefQ ℓ)))
    (hthird : Seg μ' (fr + 6 * (x.n * x.n)) (instAB x.U x.V ℓ e)) :
    (question x fr ℓ e).Pre μ' (fr + 8 * (x.n * x.n)) := by
  have hpre := C.pre
  have := C.places
  obtain ⟨hqX, hqY, -⟩ := seg_parts hpre hq
  obtain ⟨b1, b2, b3⟩ := absLe_inst hpre.leX hpre.leY hpre.leV hpre.lenY hpre.U_pos (ℓ := ℓ) he
  exact {
    n_pos := hpre.n_pos
    U_pos := by simp only [question]; omega
    lenAB := by simp [question, instAB, hpre.lenV]
    lenBC := by simp [question, instBC]
    lenAC := by simp [question, instAC, hpre.lenX]
    segAB := hthird
    segBC := hqY
    segAC := hqX
    leAB := b1
    leBC := b2
    leAC := b3
    belowAB := by simp only [question]; omega
    belowBC := by simp only [question]; omega
    belowAC := by simp only [question]; omega
    belowOut := by simp only [question]; omega }

/-- The state between two steps: the locals, with some result of the last call, and the memory at
the level ℓ with the asked set S. -/
def St (x : PairsInst) (μ : ℕ → ℤ) (fr : ℕ) (rd : ℤ) (ℓ : ℕ) (S : ℕ × ℤ → Prop) (σ : State) :
    Prop :=
  ∃ (res : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (locals x fr (2 ^ aeLevels x.U : ℕ) (aeLevels x.U) rd res), μ'⟩ ∧
      PMem x μ fr ℓ S μ'

/-- The time of one question. -/
abbrev probeTime (T : ℕ → ℕ → ℕ) (x : PairsInst) : ℕ := 51 * (x.n * x.n) + 35 + T x.n (9 * x.U)

/-- The flags of the solver are 0 or 1. -/
theorem aeFlags_01 (n : ℕ) (AB BC AC : List ℤ) :
    ∀ f ∈ aeFlags n AB BC AC, f = 0 ∨ f = 1 := by
  intro f hf
  simp only [aeFlags, List.mem_map] at hf
  obtain ⟨q, -, rfl⟩ := hf
  unfold flag
  split_ifs <;> simp

/-- The flag of the instance `(ℓ, e)`, spelled out. -/
theorem hit_iff (x : PairsInst) (ℓ : ℕ) (e : ℤ) (q : ℕ) :
    hit x (ℓ, e) q ↔
      (aeFlags x.n (instAB x.U x.V ℓ e) (instBC x.n x.U x.Y ℓ) (instAC x.U x.X ℓ)).getD q 0 = 1 :=
  Iff.rfl

/-- **One question** leaves the arrays as they are and adds the instance `(ℓ, e)` to the asked set.
-/
theorem probe_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {ℓ e : ℕ}
    (he : 1 ≤ e ∧ e ≤ 3) {rd : ℤ} {S : ℕ × ℤ → Prop} {σ : State} (hσ : St x μ fr rd ℓ S σ) :
    Ends lim (P₀ ++ R') d (paProbe p pAff pOr e) σ (probeTime T x)
      (St x μ fr rd ℓ (fun c => S c ∨ c = (ℓ, (e : ℤ)))) := by
  obtain ⟨res, μ₀, rfl, hq, hr, hout, hk⟩ := hσ
  have hpre := C.pre
  have := C.places
  have he' : 1 ≤ (e : ℤ) ∧ (e : ℤ) ≤ 3 := by omega
  have hlenV : ((affL 1 (2 * x.U) x.V).map (prefQ ℓ)).length = x.n * x.n := by simp [hpre.lenV]
  have hV3 := (absLe_pStart_parts hpre.leX hpre.leY hpre.leV hpre.lenY ℓ).2.2
  have h01 := aeFlags_01 x.n (instAB x.U x.V ℓ e) (instBC x.n x.U x.Y ℓ) (instAC x.U x.X ℓ)
  unfold paProbe
  -- Res := pAff(Cells, PreV, 0 - 1, e, Third)
  refine Ends.callToThen (C.affine_meets (m := -1) (c := e) (dst := fr + 6 * (x.n * x.n))
    (seg_parts hpre hq).2.2 (by omega) fun w hw => ?_) ?_
    (ha := by light_side [hlenV]) (hT := by simp [hlenV, probeTime]; omega)
  · have := hV3 w hw
    simp only [abs_le]
    omega
  rintro r₁ μ₁ ⟨hthird, h₁⟩
  rw [hlenV] at h₁
  have hq₁ : Seg μ₁ fr ((Z x).map (prefQ ℓ)) := hq.keep (by light_keep)
  -- Res := pAE(Verts, Bound9, Third, PreY, PreX, Flg, SolverFree)
  refine Ends.callToThen (C.solver.meets R' (question x fr ℓ e) (fr + 8 * (x.n * x.n))
    (question_pre C he' hq₁ hthird)
    { word := by simp only [aeTask, question]; omega
      cells := by simp only [aeTask, question]; omega
      space := C.ok.space
      depth := by simp only [aeTask, question]; omega }) ?_ (by simp [aeTask, question])
    (hT := by simp [aeTask, question, probeTime]; omega)
  rintro r₂ μ₂ ⟨hflg, h₂⟩
  simp only [question] at hflg h₂
  have hout₂ : Seg μ₂ x.out (orFlags (x.n * x.n) S (hit x)) :=
    hout.keep (by light_keep)
  -- Res := pOr(Cells, Flg, Out)
  refine Ends.callTo (or_meets C.orp (len := x.n * x.n) hflg hout₂ (by simp) (by omega)
    ⟨C.ok.space, by omega, by omega⟩ h01 (orFlags_mem _ _ _) (by omega)) ?_
    (ha := by light_side) (hT := by simp [aeTask, question, probeTime]; omega)
  rintro r₃ μ₃ ⟨hout₃, h₃⟩
  have hor := orL_orFlags (S := S) (c := (ℓ, (e : ℤ))) (length_aeFlags x.n _ _ _)
    (fun q _ => hit_iff x ℓ e q) h01
  rw [hor] at hout₃
  exact ⟨r₃, μ₃, rfl, hq₁.keep (by light_keep), hr.keep (by light_keep), hout₃,
    fun c hc => by light_keep⟩

/-! ## The rounds -/

/-- What prefDown needs holds at every level above 0. -/
theorem down_pre (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {μ' : ℕ → ℤ} {ℓ : ℕ}
    (hℓ : ℓ + 1 ≤ aeLevels x.U) (hq : Seg μ' fr ((Z x).map (prefQ (ℓ + 1))))
    (hr : Seg μ' (fr + 3 * (x.n * x.n)) ((Z x).map (prefR (aeLevels x.U) (ℓ + 1)))) :
    PrefPre lim μ' fr (fr + 3 * (x.n * x.n)) (2 ^ aeLevels x.U)
      ((Z x).map (prefQ (ℓ + 1))) ((Z x).map (prefR (aeLevels x.U) (ℓ + 1))) := by
  have := C.places
  have hZ := Z_range C.pre
  have hL : ((2 ^ aeLevels x.U : ℕ) : ℤ) ≤ ((6 * x.U : ℕ) : ℤ) := by
    exact_mod_cast two_pow_aeLevels_le C.pre.U_pos
  push_cast at hL
  refine ⟨hq, hr, by simp, C.ok.space, by simp; omega, by simp; omega, by simp; omega, by omega,
    fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have := prefQ_nonneg (hZ z hz).1 (ℓ + 1)
    have := (prefQ_le (hZ z hz).1 (ℓ + 1)).trans (hZ z hz).2.1
    simp only [abs_le]
    omega
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have := prefR_nonneg (aeLevels x.U) (ℓ + 1) z
    have := prefR_lt hℓ z
    simp only [abs_le]
    omega

/-- The time of one round. -/
abbrev roundTime (T : ℕ → ℕ → ℕ) (x : PairsInst) : ℕ := 2 * probeTime T x + 114 * (x.n * x.n) + 12

/-- **One round** at the level ℓ + 1: the two questions, then the level ℓ. -/
theorem round_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {ℓ : ℕ}
    (hℓ : ℓ + 1 ≤ aeLevels x.U) {rd : ℤ} {σ : State}
    (hσ : St x μ fr rd (ℓ + 1) (Above (ℓ + 1) (aeLevels x.U)) σ) :
    Ends lim (P₀ ++ R') d (paRound p pAff pOr pDown) σ (roundTime T x)
      (St x μ fr rd ℓ (Above ℓ (aeLevels x.U))) := by
  have hplaces := C.places
  have hZl : (Z x).length = 3 * (x.n * x.n) := length_pStart C.pre.lenX C.pre.lenV
  unfold paRound
  refine Ends.next _ ((probe_spec C (by norm_num) hσ).mono le_rfl fun σ₂ hσ₂ => ?_)
    (by simp only [roundTime, probeTime]; omega)
  refine Ends.next _ ((probe_spec C (by norm_num) hσ₂).mono le_rfl fun σ₃ hσ₃ => ?_)
    (by simp only [roundTime, probeTime]; omega)
  obtain ⟨res, μ₀, rfl, hq, hr, hout, hk⟩ := hσ₃
  -- Res := pDown(Cells3, PreX, RestX, Power)
  refine Ends.callTo (prefDown_meets C.down (down_pre C hℓ hq hr)) ?_ (by simp [hZl])
    (hT := by simp [roundTime, probeTime]; omega)
  rintro r₁ μ₁ ⟨hq', hr', hrest⟩
  rw [zipWith_shiftQ hℓ] at hq'
  rw [map_shiftR hℓ] at hr'
  simp only [List.length_map] at hrest
  refine ⟨r₁, μ₁, rfl, hq', hr', ?_, fun c hc => ?_⟩
  · have : orFlags (x.n * x.n) (fun c => (Above (ℓ + 1) (aeLevels x.U) c ∨ c = (ℓ + 1, 2)) ∨
        c = (ℓ + 1, 3)) (hit x) = orFlags (x.n * x.n) (Above ℓ (aeLevels x.U)) (hit x) := by
      simp only [orFlags]
      exact List.map_congr_left fun q _ => flag_congr (exists_congr fun c =>
        and_congr_left fun _ => above_step hℓ c)
    rw [← this]
    refine hout.keep fun a ha => ?_
    rw [length_orFlags] at ha
    exact hrest a (Or.inl (by omega)) (Or.inl (by omega))
  · exact (hrest c (Or.inl (by omega)) (Or.inl (by omega))).trans (hk c hc)

/-- **The b rounds**: from the level b to the level 0. -/
theorem rounds_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {res : ℤ}
    {μ' : ℕ → ℤ} (hm : PMem x μ fr (aeLevels x.U) (fun _ => False) μ') :
    Ends lim (P₀ ++ R') d (.for Round (v Levels) (paRound p pAff pOr pDown))
      ⟨frame (locals x fr (2 ^ aeLevels x.U : ℕ) (aeLevels x.U) 0 res), μ'⟩
      (aeLevels x.U * (roundTime T x + 8) + 6)
      (St x μ fr (aeLevels x.U) 0 (Above 0 (aeLevels x.U))) := by
  have hplaces := C.places
  have hL : aeLevels x.U ≤ 6 * x.U :=
    (Nat.lt_two_pow_self (n := aeLevels x.U)).le.trans (two_pow_aeLevels_le C.pre.U_pos)
  refine Ends.for (fun t σ => St x μ fr t (aeLevels x.U - t) (Above (aeLevels x.U - t)
    (aeLevels x.U)) σ) (aeLevels x.U) (roundTime T x) ?start ?round ?done ?bound (by omega)
    (by simp; ring_nf; omega)
  case start =>
    refine ⟨res, μ', ?_, ?_⟩
    · rw [update_frame_setLocal]
      rfl
    · simp only [Nat.sub_zero]
      have : orFlags (x.n * x.n) (Above (aeLevels x.U) (aeLevels x.U)) (hit x) =
          orFlags (x.n * x.n) (fun _ => False) (hit x) := by
        simp only [orFlags]
        exact List.map_congr_left fun q _ => flag_congr (exists_congr fun c =>
          and_congr_left fun _ => iff_of_false (above_self _ c) id)
      obtain ⟨h1, h2, h3, h4⟩ := hm
      exact ⟨h1, h2, this ▸ h3, h4⟩
  case round =>
    intro t σ ht _ hσ
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, aeLevels x.U - t = ℓ + 1 := ⟨aeLevels x.U - t - 1, by omega⟩
    rw [show aeLevels x.U - (t + 1) = ℓ by omega]
    rw [hℓ] at hσ
    refine (round_spec C (by omega) hσ).mono le_rfl fun σ' hσ' => ?_
    obtain ⟨res', μ'', rfl, hm'⟩ := hσ'
    exact ⟨rfl, res', μ'', by rw [update_frame_setLocal]; rfl, hm'⟩
  case done =>
    intro σ _ hσ
    simpa using hσ
  case bound =>
    rintro t _ - - ⟨res', μ'', rfl, -⟩
    exact ⟨trivial, rfl⟩

/-! ## The procedure -/

/-- **pairsAE is correct**, in every program that begins with the solver's program and has the four
loops over arrays. -/
theorem pairsAE_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) :
    Ends lim (P₀ ++ R') d (paBody p pAff pTr pOr pDown)
      ⟨frame [x.n, x.U, x.x, x.y, x.v, x.out, fr], μ⟩ (pairsTimeAE T x.n x.U) fun σ' =>
        Seg σ'.mem x.out (pairFlags x.n x.X x.Y x.V) ∧ KeptBut μ σ'.mem fr x.out (x.n * x.n) := by
  have hpre := C.pre
  have hplaces := C.places
  have htime : pairsTimeAE T x.n x.U = aeLevels x.U * (roundTime T x + 8) + 6 +
      (3 * probeTime T x + 30 * aeLevels x.U + 371 * (x.n * x.n) + 219) := by
    simp only [pairsTimeAE, roundTime, probeTime]
    ring
  rw [htime]
  unfold paBody
  -- paInit
  refine Ends.next _ ((init_spec C).mono le_rfl ?_) (by simp [paInit]; omega)
  rintro _ rfl
  -- paPow
  refine Ends.next _ ((pow_spec C).mono le_rfl ?_) (by simp [paInit]; omega)
  rintro _ rfl
  -- paFill
  refine Ends.next _ ((fill_spec C _ _ _ _).mono le_rfl ?_) (by simp [paInit]; omega)
  rintro _ ⟨res, μ₁, rfl, hm⟩
  -- the rounds
  refine Ends.next _ ((rounds_spec C hm).mono le_rfl ?_) (by simp [paInit]; omega)
  intro σ₂ hσ₂
  -- the three questions at the level 0
  refine Ends.next _ ((probe_spec C (by norm_num) hσ₂).mono le_rfl fun σ₃ hσ₃ => ?_)
    (by simp [paInit]; omega)
  refine Ends.next _ ((probe_spec C (by norm_num) hσ₃).mono le_rfl fun σ₄ hσ₄ => ?_)
    (by simp [paInit]; omega)
  refine Ends.next _ ((probe_spec C (by norm_num) hσ₄).mono le_rfl fun σ₅ hσ₅ => ?_)
    (by simp [paInit]; omega)
  obtain ⟨res', μ₅, rfl, -, -, hout, hk⟩ := hσ₅
  refine Ends.setTo 0 ⟨?_, hk⟩ (hT := by simp [paInit]; omega)
  rw [← orFlags_eq_pairFlags hpre.leX hpre.leY hpre.leV hpre.lenX hpre.lenY hpre.lenV]
  have : orFlags (x.n * x.n) (fun c => ((Above 0 (aeLevels x.U) c ∨ c = (0, ((2 : ℕ) : ℤ))) ∨
      c = (0, ((3 : ℕ) : ℤ))) ∨ c = (0, ((1 : ℕ) : ℤ))) (hit x) =
      orFlags (x.n * x.n) (fun c => c ∈ lemmaFInstances (aeLevels x.U)) (hit x) := by
    simp only [orFlags]
    exact List.map_congr_left fun q _ => flag_congr (exists_congr fun c =>
      and_congr_left fun _ => by push_cast; exact above_zero_iff _ c)
  exact this ▸ hout

end PairsHost

/-- The need of pairsAE is polynomially bounded if the need of the solver is. -/
theorem polyNeed_pairsNeedAE {r : ℕ → ℕ → Need} (h : PolyNeed r) : PolyNeed (pairsNeedAE r) := by
  unfold pairsNeedAE
  poly_need [h.word, h.cells, h.depth]

/-- **All pairs from all-edges Exact Triangle**: from every solver of all-edges Exact Triangle, the
five procedures affine, transpose, or, prefDown, pairsAE make a solver of all pairs. -/
theorem isHost_pairsAE : IsHost aeTask pairsTask pairsTimeAE pairsNeedAE := by
  refine ⟨fun P p T r hsol => ⟨[affineBody, transposeBody, orBody, prefDownBody,
    paBody p P.length (P.length + 1) (P.length + 2) (P.length + 3)], P.length + 4,
    paBody p P.length (P.length + 1) (P.length + 2) (P.length + 3), by simp,
    fun R lim d x μ fr hpre hok => ?_⟩, fun r => polyNeed_pairsNeedAE⟩
  rw [List.append_assoc]
  exact PairsHost.pairsAE_spec ⟨hsol, by simp, by simp, by simp, by simp, hpre, hok⟩



open ThreeSumApsp.WordRam Filter

theorem aeLevels_le {U : ℕ} (hU : 1 ≤ U) {u : ℝ} (hu : (U : ℝ) ≤ u) :
    (aeLevels U : ℝ) ≤ 3 * (1 + logU u) := by
  have : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hhalf := Real.one_half_lt_log_two
  have := log_two_le_logU u
  have hpow : 2 ^ Nat.log 2 (3 * U) ≤ 3 * U := Nat.pow_log_le_self 2 (by omega)
  have hlog : (Nat.log 2 (3 * U) : ℝ) * Real.log 2 ≤ Real.log (3 * U) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  rw [Real.log_mul (by norm_num) (by positivity)] at hlog
  have : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_four]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have : Real.log U ≤ logU u := (Real.log_le_log (by positivity) hu).trans
    (log_le_logU (by linarith))
  simp only [aeLevels]
  push_cast
  rcases le_or_gt (Nat.log 2 (3 * U)) 1 with hL | hL
  · have : (Nat.log 2 (3 * U) : ℝ) ≤ 1 := by exact_mod_cast hL
    linarith
  · have hL2 : (0 : ℝ) ≤ (Nat.log 2 (3 * U) : ℝ) - 2 := by
      have : (2 : ℝ) ≤ Nat.log 2 (3 * U) := by exact_mod_cast hL
      linarith
    have := mul_le_mul_of_nonneg_left hhalf.le hL2
    linarith

theorem pairsTimeAE_le {Tn : ℕ → ℕ → ℕ} {T : ℕ → ℝ → ℝ}
    (hT : ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤ T n u)
    {n U : ℕ} {u : ℝ} (hn : 1 ≤ n) (hU : 1 ≤ U) (hu : (U : ℝ) ≤ u) :
    (pairsTimeAE Tn n U : ℝ) ≤ 2000 * ((1 + logU u) * (T n (9 * u) + (n : ℝ) ^ 2)) := by
  have := aeLevels_le hU hu
  have hL0 : (0 : ℝ) ≤ logU u := (logU_pos u).le
  have hTn := hT n (9 * U) (9 * u) hn (by omega) (by push_cast; linarith)
  have hT0 : (0 : ℝ) ≤ T n (9 * u) := (Nat.cast_nonneg _).trans hTn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hn)
  have hcalls : (2 * (aeLevels U : ℝ) + 3) ≤ 9 * (1 + logU u) := by linarith
  have hcall : (Tn n (9 * U) : ℝ) + 108 * (n : ℝ) ^ 2 + 60 ≤
      168 * (T n (9 * u) + (n : ℝ) ^ 2) := by linarith
  have hprod := mul_le_mul hcalls hcall (by positivity) (by positivity)
  have hstart : 350 * (T n (9 * u) + (n : ℝ) ^ 2) ≤
      350 * ((1 + logU u) * (T n (9 * u) + (n : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) (by linarith)) (by norm_num)
  have hsq : ((n : ℝ) * n) = (n : ℝ) ^ 2 := (sq (n : ℝ)).symm
  simp only [pairsTimeAE]
  push_cast
  rw [hsq]
  nlinarith [hprod, hstart, hL0, hT0, hn1]

theorem mpTime_le {Tn : ℕ → ℕ → ℕ} {Tp : ℕ → ℝ → ℝ}
    (hTn : ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤ Tp n u)
    {n U : ℕ} {u : ℝ} (hn : 1 ≤ n) (hU : 1 ≤ U) (hu : (U : ℝ) ≤ u) :
    (mpTime Tn n U : ℝ) ≤ 1100 * (logU u * (Tp n (6 * u) + (n : ℝ) ^ 2)) := by
  have hR := MinPlusFromNeg.mpRounds_le hU hu
  have : 1 / 2 < logU u := Real.one_half_lt_log_two.trans_le (log_two_le_logU u)
  have hT := hTn n (6 * U) (6 * u) hn (by omega) (by push_cast; linarith)
  have hT0 : (0 : ℝ) ≤ Tp n (6 * u) := (Nat.cast_nonneg _).trans hT
  have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hn)
  have : (0 : ℝ) ≤ mpRounds U := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ logU u := by linarith
  have hstep : (mpRounds U : ℝ) * ((Tn n (6 * U) : ℝ) + 49 * (n : ℝ) ^ 2 + 70)
      ≤ 8 * logU u * (Tp n (6 * u) + 49 * (n : ℝ) ^ 2 + 70) :=
    mul_le_mul hR (by linarith) (by positivity) (by positivity)
  have ha : 0 ≤ logU u * ((n : ℝ) ^ 2 - 1) := mul_nonneg hL0 (by linarith)
  have hb : (n : ℝ) ^ 2 ≤ 2 * logU u * (n : ℝ) ^ 2 :=
    le_mul_of_one_le_left (by positivity) (by linarith)
  have hc : 0 ≤ logU u * Tp n (6 * u) := mul_nonneg hL0 hT0
  have hsq : ((n : ℝ) * n) = (n : ℝ) ^ 2 := (sq (n : ℝ)).symm
  simp only [mpTime]
  push_cast
  rw [hsq]
  nlinarith [hstep, ha, hb, hc]

theorem solvedIn_mp_of_allEdges {T : ℕ → ℝ → ℝ} (h : SolvedIn aeTask T) :
    SolvedIn mpTask fun n u => 1100 * (logU u *
      (2000 * ((1 + logU (6 * u)) * (T n (9 * (6 * u)) + (n : ℝ) ^ 2)) + (n : ℝ) ^ 2)) :=
  isHost_mp.solvedIn
    (isHost_pairsAE.solvedIn h fun _ hTn _ _ _ hn hU hu => pairsTimeAE_le hTn hn hU hu)
    fun _ hTn _ _ _ hn hU hu => mpTime_le hTn hn hU hu

theorem _root_.Light.SolvedIn.nonneg {task : Task} {T : ℕ → ℝ → ℝ} (h : SolvedIn task T) {n : ℕ}
    {u : ℝ} (hn : 1 ≤ n) (hu : 1 ≤ u) : 0 ≤ T n u := by
  obtain ⟨_, _, Tn, _, -, -, hT⟩ := h
  exact (Nat.cast_nonneg (Tn n 1)).trans (hT n 1 u hn le_rfl (by exact_mod_cast hu))

theorem eventually_le_of_explicit {n₀ : ℕ} {K δ : ℝ} {e : ℕ} {T : ℕ → ℝ → ℝ}
    (hb : ∀ (n : ℕ) (κ u : ℝ), n₀ ≤ n → 1 ≤ κ → u ≤ (n : ℝ) ^ κ →
      T n u ≤ K * (κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)))
    {c κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ᶠ n : ℕ in atTop,
      T n (c * (n : ℝ) ^ κ) ≤ K * ((κ + 1) * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)) := by
  filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop ⌈c⌉₊, eventually_ge_atTop 1] with n
    hn₀ hnc hn1
  refine hb n (κ + 1) _ hn₀ (by linarith) ?_
  have hcn : c ≤ (n : ℝ) := (Nat.le_ceil c).trans (by exact_mod_cast hnc)
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [Real.rpow_add_one hn0, mul_comm]
  exact mul_le_mul_of_nonneg_left hcn (Real.rpow_nonneg (Nat.cast_nonneg n) κ)

theorem clog_add_one_le (n : ℕ) (hn : 2 ≤ n) : (Nat.clog 2 n : ℝ) + 1 ≤ 6 * Real.log n := by
  have : (Nat.clog 2 n : ℝ) < Real.log n / Real.log 2 + 1 := by
    simpa [Real.logb] using Real.natCast_clog_lt_logb_add_one 2 n
  have := Real.one_half_lt_log_two
  have : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have : Real.log n / Real.log 2 ≤ 2 * Real.log n := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

theorem minPlusInPolylog_of_explicitFrom {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1)
    (h : ExplicitFrom lightModelAE δ e) :
    Claim.MinPlusInPolylog lightModelAE (3 - δ) := by
  obtain ⟨n₀, K, T, hT, hb⟩ := h
  intro κ hκ
  refine ⟨_, solvedIn_mp_of_allEdges hT, ?_⟩
  have hev := eventually_le_of_explicit hb (c := 54) (κ := κ) hκ
  have h1 : IsPowPolylog (fun n : ℕ => logU ((n : ℝ) ^ κ)) 0 :=
    isPowPolylog_logU_of_le (c := 1) fun n hn =>
      ⟨Real.one_le_rpow (Nat.one_le_cast.2 hn) hκ, (one_mul _).ge⟩
  have h2 : IsPowPolylog (fun n : ℕ => 1 + logU (6 * (n : ℝ) ^ κ)) 0 :=
    (isPowPolylog_const 1).add (isPowPolylog_logU_mul_rpow (by norm_num) hκ)
  have h3 : IsPowPolylog
      (fun n : ℕ => K * ((κ + 1) * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e))) (3 - δ) :=
    ((isPowPolylog_rpow_mul_log_pow (3 - δ) e).const_mul (κ + 1)).const_mul K
  have h4 : IsPowPolylog (fun n : ℕ => (n : ℝ) ^ 2) (3 - δ) :=
    (isBigOPow_natCast_pow 2).isPowPolylog.mono (by push_cast; linarith)
  have hg : IsPowPolylog (fun n : ℕ => 1100 * (logU ((n : ℝ) ^ κ) *
      ((2000 : ℝ) * ((1 + logU (6 * (n : ℝ) ^ κ)) *
        (K * ((κ + 1) * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)) + (n : ℝ) ^ 2)) + (n : ℝ) ^ 2)))
      (3 - δ) :=
    ((h1.mul ((((h2.mul (h3.add h4)).mono (by simp)).const_mul 2000).add h4)).mono
      (by simp)).const_mul 1100
  refine hg.upperPowPolylog.mono_left ?_
  filter_upwards [hev] with n hn
  have h54 : (9 : ℝ) * (6 * (n : ℝ) ^ κ) = 54 * (n : ℝ) ^ κ := by ring
  have := logU_pos ((n : ℝ) ^ κ)
  have := logU_pos (6 * (n : ℝ) ^ κ)
  simp only [h54]
  gcongr

theorem apspInPolylog_of_explicitFrom {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1)
    (h : ExplicitFrom lightModelAE δ e) :
    Claim.ApspInPolylog lightModelAE (3 - δ) := by
  obtain ⟨n₀, K, T, hT, hb⟩ := h
  obtain ⟨c, C₀, hc, hsq⟩ := claim_apspFromMinPlus
  intro κ hκ
  refine ⟨_, hsq _ (solvedIn_mp_of_allEdges hT), ?_⟩
  have : (0 : ℝ) ≤ c := zero_le_one.trans hc
  have hev := eventually_le_of_explicit hb (c := 54 * c) (κ := κ + 1) (by linarith)
  have hmag : ∀ n : ℕ, 1 ≤ n → 1 ≤ c * ((n : ℝ) * (n : ℝ) ^ κ) ∧
      c * ((n : ℝ) * (n : ℝ) ^ κ) ≤ c * (n : ℝ) ^ (κ + 1) := fun n hn => by
    have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
    have hpow : (1 : ℝ) ≤ (n : ℝ) ^ κ := Real.one_le_rpow hn1 hκ
    refine ⟨one_le_mul_of_one_le_of_one_le hc (one_le_mul_of_one_le_of_one_le hn1 hpow), ?_⟩
    rw [Real.rpow_add_one (by positivity), mul_comm (n : ℝ)]
  have h0 : IsPowPolylog (fun n : ℕ => 6 * Real.log n) 0 := isPowPolylog_log.const_mul 6
  have h1 : IsPowPolylog (fun n : ℕ => logU (c * ((n : ℝ) * (n : ℝ) ^ κ))) 0 :=
    isPowPolylog_logU_of_le hmag
  have h2 : IsPowPolylog (fun n : ℕ => 1 + logU (6 * (c * ((n : ℝ) * (n : ℝ) ^ κ)))) 0 :=
    (isPowPolylog_const 1).add (isPowPolylog_logU_of_le (c := 6 * c) (κ := κ + 1) fun n hn =>
      ⟨one_le_mul_of_one_le_of_one_le (by norm_num) (hmag n hn).1,
        by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hmag n hn).2 (by norm_num)⟩)
  have h3 : IsPowPolylog
      (fun n : ℕ => K * ((κ + 1 + 1) * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e))) (3 - δ) :=
    ((isPowPolylog_rpow_mul_log_pow (3 - δ) e).const_mul (κ + 1 + 1)).const_mul K
  have h4 : IsPowPolylog (fun n : ℕ => (n : ℝ) ^ 2) (3 - δ) :=
    (isBigOPow_natCast_pow 2).isPowPolylog.mono (by push_cast; linarith)
  have h5 : IsPowPolylog
      (fun n : ℕ => C₀ * ((n : ℝ) ^ 2 * (1 + logU (c * ((n : ℝ) * (n : ℝ) ^ κ))))) (3 - δ) :=
    ((h4.mul ((isPowPolylog_const 1).add h1)).mono (by simp)).const_mul C₀
  have hg : IsPowPolylog (fun n : ℕ => 6 * Real.log n *
      (1100 * (logU (c * ((n : ℝ) * (n : ℝ) ^ κ)) *
        ((2000 : ℝ) * ((1 + logU (6 * (c * ((n : ℝ) * (n : ℝ) ^ κ)))) *
          (K * ((κ + 1 + 1) * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)) + (n : ℝ) ^ 2)) +
            (n : ℝ) ^ 2)) +
        C₀ * ((n : ℝ) ^ 2 * (1 + logU (c * ((n : ℝ) * (n : ℝ) ^ κ)))))) (3 - δ) :=
    (h0.mul ((((h1.mul ((((h2.mul (h3.add h4)).mono (by simp)).const_mul 2000).add h4)).mono
      (by simp)).const_mul 1100).add h5)).mono (by simp)
  refine hg.upperPowPolylog.mono_left ?_
  filter_upwards [hev, eventually_ge_atTop 2] with n hn hn2
  have hn1 : 1 ≤ n := by omega
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hmul : (9 : ℝ) * (6 * (c * ((n : ℝ) * (n : ℝ) ^ κ))) = 54 * c * (n : ℝ) ^ (κ + 1) := by
    rw [Real.rpow_add_one hn0]
    ring
  rw [← hmul] at hn
  have hclog := clog_add_one_le n hn2
  have := logU_pos (c * ((n : ℝ) * (n : ℝ) ^ κ))
  have := logU_pos (6 * (c * ((n : ℝ) * (n : ℝ) ^ κ)))
  have hX0 := (hsq _ (solvedIn_mp_of_allEdges hT)).nonneg hn1
    (Real.one_le_rpow (Nat.one_le_cast.2 hn1) hκ)
  exact mul_le_mul hclog (by gcongr) (nonneg_of_mul_nonneg_right hX0 (by positivity))
    (by positivity)

end ImprovedExponents.AllEdges
