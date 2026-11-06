module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.NodeMemory
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Sizes
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Contracts

@[expose] public section

section
open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Pure facts -/

/-- Convolution-3SUM holds of the list of the first `N` cells of an array if and only if `ConvOne N`
holds of the array. -/
theorem conv_range_iff (N : ℕ) (y : ℕ → ℤ) :
    Convolution3SUM (vecOf N ((List.range N).map y)) ↔ ConvOne N y := by
  have : vecOf N ((List.range N).map y) = fun i : Fin N => y i := by
    funext i
    unfold vecOf
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  rw [this]
  exact convolution3SUM_iff_convOne N y

/-- One of four answers is yes if and only if their sum is positive. -/
theorem flag_sum_pos (a b c e : Prop) : 0 < flag a + flag b + flag c + flag e ↔ a ∨ b ∨ c ∨ e := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases he : e <;>
    simp [flag_of, flag_of_not, ha, hb, hc, he]

/-- The number of binary digits of the labels is at most V + 2. -/
theorem lam_le (V : ℕ) : Lam V ≤ V + 2 := by
  unfold Lam
  rcases Nat.eq_zero_or_pos V with rfl | h
  · simp
  · have : Nat.log 2 (2 * V) = Nat.log 2 V + 1 := by
      rw [Nat.mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
    have : Nat.log 2 V < V := Nat.log_lt_self 2 (by omega)
    omega

/-! ## The procedure -/

namespace NodesLocals

/-- The local variables of nodes: the arguments f, s₁, l₁, s₂, l₂, s₃, l₃, cx, fr; the parameters V,
m, Λ, np, pr, cnt, read from the block at cx; the modulus M; the length 8m² of the array; the free
pointer behind the array; the result of nodeArray, which is not used; the answer of the solver; and
for each of the three children the number of heavy elements and the answer.  At the end local 0
receives the result, as in every procedure. -/
abbrev LEVELS : ℕ := 0
@[inherit_doc LEVELS] abbrev SET1 : ℕ := 1
@[inherit_doc LEVELS] abbrev LEN1 : ℕ := 2
@[inherit_doc LEVELS] abbrev SET2 : ℕ := 3
@[inherit_doc LEVELS] abbrev LEN2 : ℕ := 4
@[inherit_doc LEVELS] abbrev SET3 : ℕ := 5
@[inherit_doc LEVELS] abbrev LEN3 : ℕ := 6
@[inherit_doc LEVELS] abbrev CTX : ℕ := 7
@[inherit_doc LEVELS] abbrev FREE : ℕ := 8
@[inherit_doc LEVELS] abbrev VMAX : ℕ := 9
@[inherit_doc LEVELS] abbrev MMAX : ℕ := 10
@[inherit_doc LEVELS] abbrev LAM : ℕ := 11
@[inherit_doc LEVELS] abbrev NPRIMES : ℕ := 12
@[inherit_doc LEVELS] abbrev PRIMES : ℕ := 13
@[inherit_doc LEVELS] abbrev CNT : ℕ := 14
@[inherit_doc LEVELS] abbrev MOD : ℕ := 15
@[inherit_doc LEVELS] abbrev LEN : ℕ := 16
@[inherit_doc LEVELS] abbrev FR2 : ℕ := 17
@[inherit_doc LEVELS] abbrev RES : ℕ := 18
@[inherit_doc LEVELS] abbrev ANS0 : ℕ := 19
@[inherit_doc LEVELS] abbrev HEAVY1 : ℕ := 20
@[inherit_doc LEVELS] abbrev ANS1 : ℕ := 21
@[inherit_doc LEVELS] abbrev HEAVY2 : ℕ := 22
@[inherit_doc LEVELS] abbrev ANS2 : ℕ := 23
@[inherit_doc LEVELS] abbrev HEAVY3 : ℕ := 24
@[inherit_doc LEVELS] abbrev ANS3 : ℕ := 25

end NodesLocals

open NodesLocals in
/-- The parameters are read from the block at cx. -/
def nodesParams : Stmt :=
  .set VMAX (M (v CTX)) ;;
  .set MMAX (M (v CTX +' k 1)) ;;
  .set LAM (M (v CTX +' k 2)) ;;
  .set NPRIMES (M (v CTX +' k 3)) ;;
  .set PRIMES (M (v CTX +' k 4)) ;;
  .set CNT (M (v CTX +' k 5))

open NodesLocals in
/-- The node itself: its modulus, its array at the free pointer, and the answer of the solver. -/
def nodesOwn (pMod pArr pC3 : ℕ) : Stmt :=
  .call pMod
      [v SET1, v LEN1, v SET2, v LEN2, v SET3, v LEN3, v LAM, v NPRIMES, v PRIMES, v CNT, v FREE]
      MOD ;;
  .set LEN (k 8 *' (v MMAX *' v MMAX)) ;;
  .set FR2 (v FREE +' v LEN) ;;
  .call pArr
      [v MOD, v SET1, v LEN1, v SET2, v LEN2, v SET3, v LEN3, v VMAX, v MMAX, v FREE, v CNT, v FR2]
      RES ;;
  .call pC3 [v LEN, k 60 *' v VMAX +' k 40, v FREE, v FR2] ANS0

open NodesLocals in
/-- The first child: the heavy elements of the first set are written at the free pointer, and the
procedure calls itself with them in place of the first set. -/
def nodesChild₁ (pSelf pHeavy : ℕ) : Stmt :=
  .call pHeavy [v LEN1, v SET1, v MOD, v FREE, v CNT, v FREE +' v LEN1] HEAVY1 ;;
  .call pSelf
      [v LEVELS -' k 1, v FREE, v HEAVY1, v SET2, v LEN2, v SET3, v LEN3, v CTX, v FREE +' v LEN1]
      ANS1

open NodesLocals in
/-- The second child. -/
def nodesChild₂ (pSelf pHeavy : ℕ) : Stmt :=
  .call pHeavy [v LEN2, v SET2, v MOD, v FREE, v CNT, v FREE +' v LEN2] HEAVY2 ;;
  .call pSelf
      [v LEVELS -' k 1, v SET1, v LEN1, v FREE, v HEAVY2, v SET3, v LEN3, v CTX, v FREE +' v LEN2]
      ANS2

open NodesLocals in
/-- The third child. -/
def nodesChild₃ (pSelf pHeavy : ℕ) : Stmt :=
  .call pHeavy [v LEN3, v SET3, v MOD, v FREE, v CNT, v FREE +' v LEN3] HEAVY3 ;;
  .call pSelf
      [v LEVELS -' k 1, v SET1, v LEN1, v SET2, v LEN2, v FREE, v HEAVY3, v CTX, v FREE +' v LEN3]
      ANS3

open NodesLocals in
/-- The answer is yes if one of the four answers is. -/
def nodesAnswer : Stmt :=
  .ite (k 0 <' v ANS0 +' v ANS1 +' v ANS2 +' v ANS3) (.set 0 (k 1)) (.set 0 (k 0))

/-- A triple of nonempty sets with at least one level to go. -/
def nodesMain (pSelf pMod pArr pC3 pHeavy : ℕ) : Stmt :=
  nodesParams ;; nodesOwn pMod pArr pC3 ;; nodesChild₁ pSelf pHeavy ;; nodesChild₂ pSelf pHeavy ;;
  nodesChild₃ pSelf pHeavy ;; nodesAnswer

open NodesLocals in
/-- nodes(f, s₁, l₁, s₂, l₂, s₃, l₃, cx, fr), over the procedures pSelf (itself), pMod (modulus),
pArr (nodeArray), pC3 (a solver of Convolution-3SUM), pHeavy (heavy): the answer is 0 if no level is
left or one of the sets is empty. -/
def nodesBody (pSelf pMod pArr pC3 pHeavy : ℕ) : Stmt :=
  .ite (v LEVELS =' k 0) (.set 0 (k 0)) (
  .ite (v LEN1 =' k 0) (.set 0 (k 0)) (
  .ite (v LEN2 =' k 0) (.set 0 (k 0)) (
  .ite (v LEN3 =' k 0) (.set 0 (k 0)) (nodesMain pSelf pMod pArr pC3 pHeavy))))

/-- What the procedure assumes about the program: it begins with the program of a solver of
Convolution-3SUM, holds the procedure itself, and meets the specifications of the three routines
that the procedure calls. -/
structure NodesCtx (lim : Limits) (P₀ R : Program) (p pMod pArr pC3 pHeavy : ℕ) (T : ℕ → ℕ → ℕ)
    (r : ℕ → ℕ → Need) : Prop where
  solver : Solves c3Task P₀ pC3 T r
  self : (P₀ ++ R)[p]? = some (nodesBody p pMod pArr pC3 pHeavy)
  modulus : ModulusSpec lim (P₀ ++ R) pMod
  array : NodeArraySpec lim (P₀ ++ R) pArr
  heavy : HeavySpec lim (P₀ ++ R) pHeavy

/-- The number of calls of the procedure is at most three times the number of nodes, plus one. -/
theorem treeCalls_le (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    treeCalls Q Λ f S₁ S₂ S₃ ≤ 3 * (nodes Q Λ f S₁ S₂ S₃).length + 1 := by
  induction f generalizing S₁ S₂ S₃ with
  | zero => simp [treeCalls]
  | succ f ih =>
    unfold treeCalls nodes
    split_ifs with h
    · simp
    · simp only [List.length_cons, List.length_append]
      have := ih (ChanHe.heavy S₁ (ChanHe.modulus Q Λ S₁ S₂ S₃)) S₂ S₃
      have := ih S₁ (ChanHe.heavy S₂ (ChanHe.modulus Q Λ S₁ S₂ S₃)) S₃
      have := ih S₁ S₂ (ChanHe.heavy S₃ (ChanHe.modulus Q Λ S₁ S₂ S₃))
      omega

/-- The procedure is called at least once. -/
theorem one_le_treeCalls (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    1 ≤ treeCalls Q Λ f S₁ S₂ S₃ := by
  cases f with
  | zero => simp [treeCalls]
  | succ f =>
    unfold treeCalls
    split_ifs <;> omega

/-! ## Needs and times -/

section needs

variable {r : ℕ → ℕ → Need} {fr n V m f l M : ℕ}

/-- What is allowed at a node covers what modulus needs. -/
theorem modulusNeed_ok (h : (nodesNeed r n V m (f + 1)).Ok lim fr d) :
    (modulusNeed n V m).Ok lim fr (d + 1) := by
  refine h.mono ?_ ?_ ?_ <;> simp only [nodesNeed] <;> omega

/-- What is allowed at a node covers what nodeArray needs behind the array. -/
theorem nodeArrayNeed_ok (h : (nodesNeed r n V m (f + 1)).Ok lim fr d) :
    (nodeArrayNeed n V m).Ok lim (fr + 8 * m ^ 2) (d + 1) := by
  refine h.mono ?_ ?_ ?_ <;> simp only [nodesNeed, nodeArrayNeed, modulusNeed] <;> omega

/-- What is allowed at a node covers what the solver needs behind the array. -/
theorem solverNeed_ok (h : (nodesNeed r n V m (f + 1)).Ok lim fr d) :
    (r (8 * m ^ 2) (60 * V + 40)).Ok lim (fr + 8 * m ^ 2) (d + 1) := by
  refine h.mono ?_ ?_ ?_ <;> simp only [nodesNeed] <;> omega

/-- What is allowed at a node covers what heavy needs behind its output. -/
theorem collNeed_ok (h : (nodesNeed r n V m (f + 1)).Ok lim fr d) (hl : l ≤ n) (hM : M ≤ m * m) :
    (collNeed l V M).Ok lim (fr + l) (d + 1) := by
  have : (f + 1) * n = f * n + n := by ring
  have := wordNeed_mono (V := V) hl hM
  refine h.mono ?_ ?_ ?_ <;> simp only [nodesNeed, collNeed, modulusNeed] <;> omega

/-- What is allowed at a node covers what a child needs behind its set of heavy elements. -/
theorem childNeed_ok (h : (nodesNeed r n V m (f + 1)).Ok lim fr d) (hl : l ≤ n) :
    (nodesNeed r n V m f).Ok lim (fr + l) (d + 1) := by
  have : (f + 1) * n = f * n + n := by ring
  refine h.mono ?_ ?_ ?_ <;> simp only [nodesNeed] <;> omega

/-- The time of resid grows with the lengths of the sets. -/
theorem tResid_mono {l n : ℕ} (h : l ≤ n) (V : ℕ) : tResid l V ≤ tResid n V := by
  unfold tResid
  gcongr

/-- The time of tally grows with the lengths of the sets. -/
theorem tTally_mono {l n : ℕ} (h : l ≤ n) : tTally l ≤ tTally n := by
  unfold tTally
  omega

/-- The time of coll grows with the lengths of the sets. -/
theorem tColl_mono {l n : ℕ} (h : l ≤ n) (V : ℕ) : tColl l V ≤ tColl n V := by
  have := tResid_mono h V
  have := tTally_mono h
  unfold tColl
  omega

/-- The time of heavy grows with the lengths of the sets. -/
theorem tHeavy_mono {l n : ℕ} (h : l ≤ n) (V : ℕ) : tHeavy l V ≤ tHeavy n V := by
  have := tResid_mono h V
  have := tTally_mono h
  unfold tHeavy
  omega

/-- The time of modulus grows with the lengths of the sets. -/
theorem tModulus_mono {l₁ l₂ l₃ n : ℕ} (h₁ : l₁ ≤ n) (h₂ : l₂ ≤ n) (h₃ : l₃ ≤ n) (np V : ℕ) :
    tModulus np l₁ l₂ l₃ V ≤ tModulus np n n n V := by
  have := tColl_mono h₁ V
  have := tColl_mono h₂ V
  have := tColl_mono h₃ V
  have : tSearch np l₁ l₂ l₃ V ≤ tSearch np n n n V :=
    Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
  unfold tModulus
  omega

/-- The time of nodeArray grows with the lengths of the sets. -/
theorem tNodeArray_mono {l₁ l₂ l₃ n : ℕ} (h₁ : l₁ ≤ n) (h₂ : l₂ ≤ n) (h₃ : l₃ ≤ n) (m V : ℕ) :
    tNodeArray m l₁ l₂ l₃ V ≤ tNodeArray m n n n V := by
  have := tResid_mono h₁ V
  have := tResid_mono h₂ V
  have := tResid_mono h₃ V
  have := tTally_mono h₁
  have := tTally_mono h₂
  have := tTally_mono h₃
  unfold tNodeArray
  omega

end needs

/-! ## The parts of the procedure -/

section parts

variable {P₀ R : Program} {p pMod pArr pC3 pHeavy : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
  {a : NodeArgs} {Λ cx f Mo : ℕ} {μ μ₀ μ' : ℕ → ℤ}

/-- What the limits allow at a node: an address fits in a word; behind the free pointer there is
room for a set and the array; the number of levels is at most the number of cells, so that it fits
in a word; the numbers up to 64 (V + 1) and 64 (m² + 1) fit in a word; and one more level of calls
is allowed. -/
structure NodesFits (lim : Limits) (d fr n V m f : ℕ) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  room : fr + n + 8 * (m * m) ≤ lim.space
  levels : f ≤ lim.space
  wordV : 64 * ((V : ℤ) + 1) ≤ lim.word
  wordM : 64 * ((m : ℤ) * m + 1) ≤ lim.word
  depth : d < lim.depth

/-- What the procedure assumes provides what the limits have to allow at a node. -/
theorem NodesPre.fits (H : NodesPre lim r μ a Λ cx (f + 1) d) (hn : 1 ≤ a.n) :
    NodesFits lim d a.fr a.n a.V a.m f := by
  have hcells := H.ok.cells
  have hdepth := H.ok.depth
  have hword : ((wordNeed a.n a.V (a.m * a.m) : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast le_max_left _ _) H.ok.word
  simp only [nodesNeed] at hcells hdepth
  have : f ≤ f * a.n := Nat.le_mul_of_pos_right f hn
  have : (f + 1) * a.n = f * a.n + a.n := by ring
  have : a.m ^ 2 = a.m * a.m := pow_two a.m
  have hone : 1 ≤ (a.n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  refine ⟨H.ok.space, by omega, by omega, ?_, ?_, by omega⟩
  · simpa using mul_le_word (x := 1) (y := 1) (z := 64 * (a.V + 1)) hword hone (by omega) le_rfl
  · have h := mul_le_word (x := 1) (y := a.m * a.m + 1) (z := 64) hword hone le_rfl (by omega)
    push_cast at h
    linarith

/-- The first child of a node meets what the procedure assumes, with one level less.  μ₀, μ and μ'
are the memories when the procedure is called, before heavy, and after heavy. -/
theorem NodesPre.child₁ (H : NodesPre lim r μ₀ a Λ cx (f + 1) d) (kept : Kept μ₀ μ a.fr)
    (hk : KeptBut μ μ' (a.fr + a.X₁.len) a.fr a.X₁.len)
    (hs : SetAt μ' a.fr #(ChanHe.heavy a.X₁.set Mo) (ChanHe.heavy a.X₁.set Mo)) :
    NodesPre lim r μ' (a.child₁ Mo) Λ cx f (d + 1) :=
  { H with
    mem := (H.mem.kept kept).child₁ hk hs
    ctx := H.ctx.kept H.belowCtx (kept.then hk fun b hb => by omega)
    belowCtx := H.belowCtx.trans (Nat.le_add_right _ _)
    ok := childNeed_ok H.ok H.mem.set₁.le }

/-- The second child of a node meets what the procedure assumes, with one level less. -/
theorem NodesPre.child₂ (H : NodesPre lim r μ₀ a Λ cx (f + 1) d) (kept : Kept μ₀ μ a.fr)
    (hk : KeptBut μ μ' (a.fr + a.X₂.len) a.fr a.X₂.len)
    (hs : SetAt μ' a.fr #(ChanHe.heavy a.X₂.set Mo) (ChanHe.heavy a.X₂.set Mo)) :
    NodesPre lim r μ' (a.child₂ Mo) Λ cx f (d + 1) :=
  { H with
    mem := (H.mem.kept kept).child₂ hk hs
    ctx := H.ctx.kept H.belowCtx (kept.then hk fun b hb => by omega)
    belowCtx := H.belowCtx.trans (Nat.le_add_right _ _)
    ok := childNeed_ok H.ok H.mem.set₂.le }

/-- The third child of a node meets what the procedure assumes, with one level less. -/
theorem NodesPre.child₃ (H : NodesPre lim r μ₀ a Λ cx (f + 1) d) (kept : Kept μ₀ μ a.fr)
    (hk : KeptBut μ μ' (a.fr + a.X₃.len) a.fr a.X₃.len)
    (hs : SetAt μ' a.fr #(ChanHe.heavy a.X₃.set Mo) (ChanHe.heavy a.X₃.set Mo)) :
    NodesPre lim r μ' (a.child₃ Mo) Λ cx f (d + 1) :=
  { H with
    mem := (H.mem.kept kept).child₃ hk hs
    ctx := H.ctx.kept H.belowCtx (kept.then hk fun b hb => by omega)
    belowCtx := H.belowCtx.trans (Nat.le_add_right _ _)
    ok := childNeed_ok H.ok H.mem.set₃.le }

/-- The node with the modulus `Mo`. -/
abbrev NodeArgs.node (a : NodeArgs) (Mo : ℕ) : Node := ⟨a.X₁.set, a.X₂.set, a.X₃.set, Mo⟩

/-- The list of the local variables of nodes: the arguments, with x for the number of levels; the
parameters that are read from the block at cx; and the list t of what has been computed since. -/
@[simp] abbrev nodesLocals (x : ℤ) (a : NodeArgs) (Λ cx : ℕ) (t : List ℤ) : List ℤ :=
  x :: a.sets ++ [(cx : ℤ), a.fr, a.V, a.m, Λ, a.np, a.pr, a.cnt] ++ t

/-- **The parameters** are read from the block at cx. -/
theorem nodesParams_ends (hctx : CtxAt μ cx a.V a.m Λ a.np a.pr a.cnt) (hcx : cx + 6 ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) {x : ℤ} :
    Ends lim P d nodesParams ⟨frame (x :: a.sets ++ [(cx : ℤ), a.fr]), μ⟩ 28 fun σ' =>
      σ' = ⟨frame (nodesLocals x a Λ cx []), μ⟩ := by
  have hV : μ cx = a.V := by simpa using hctx 0 (by simp)
  have hm : μ (cx + 1) = a.m := by simpa using hctx 1 (by simp)
  have hΛ : μ (cx + 2) = Λ := by simpa using hctx 2 (by simp)
  have hnp : μ (cx + 3) = a.np := by simpa using hctx 3 (by simp)
  have hpr : μ (cx + 4) = a.pr := by simpa using hctx 4 (by simp)
  have hcnt : μ (cx + 5) = a.cnt := by simpa using hctx 5 (by simp)
  -- the address cx + j as a natural number
  have haddr : ∀ j : ℤ, 0 ≤ j → ((cx : ℤ) + j).toNat = cx + j.toNat := fun j hj => by omega
  -- V := mem[cx]; m := mem[cx + 1]; Λ := mem[cx + 2]
  light_set a.V using hV
  light_set a.m using hm
  light_set Λ using haddr, hΛ
  -- np := mem[cx + 3]; pr := mem[cx + 4]; cnt := mem[cx + 5]
  light_set a.np using haddr, hnp
  light_set a.pr using haddr, hpr
  light_set a.cnt using haddr, hcnt
  rfl

/-- The solver of Convolution-3SUM, called for the array of a node at the free pointer. -/
theorem c3_meets (hsol : Solves c3Task P₀ pC3 T r) (hV : 1 ≤ a.V) (hm : 1 ≤ a.m)
    (hN : NodeMem μ₀ a) (harr : ∀ u < 8 * a.m ^ 2, μ (a.fr + u) = (a.node Mo).oneArray a.V u)
    (hok : (r (8 * a.m ^ 2) (60 * a.V + 40)).Ok lim (a.fr + 8 * a.m ^ 2) d) :
    Meets lim (P₀ ++ R) pC3 d
      [(8 * a.m ^ 2 : ℕ), (60 * a.V + 40 : ℕ), a.fr, (a.fr + 8 * a.m ^ 2 : ℕ)] μ
      (T (8 * a.m ^ 2) (60 * a.V + 40)) fun res μ' =>
        res = flag (ConvOne (8 * a.m ^ 2) ((a.node Mo).oneArray a.V)) ∧
          Kept μ μ' (a.fr + 8 * a.m ^ 2) := by
  have hpos : 1 ≤ a.m ^ 2 := Nat.one_le_pow _ _ hm
  refine (hsol.meets R (⟨8 * a.m ^ 2, 60 * a.V + 40, a.fr,
    (List.range (8 * a.m ^ 2)).map fun u => (a.node Mo).oneArray a.V u⟩ : VecInst)
    (a.fr + 8 * a.m ^ 2) ⟨?_, ?_, by simp, ?_, ?_, le_rfl⟩ hok).mono le_rfl ?_
  · -- the length is positive
    change 1 ≤ 8 * a.m ^ 2
    omega
  · -- the bound is positive
    change 1 ≤ 60 * a.V + 40
    omega
  · -- the list stands at fr
    intro u hu
    simp [harr u (by simpa using hu)]
  · -- its entries are bounded
    intro e he
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 he
    have := Node.abs_oneArray_le (ν := a.node Mo) hN.set₁.bdd hN.set₂.bdd hN.set₃.bdd u
    push_cast
    exact this
  · rintro _ μ' ⟨rfl, kept⟩
    exact ⟨flag_congr (conv_range_iff _ _), kept⟩

/-- **The node itself**: the modulus is computed, the array is written at the free pointer, and the
solver answers for it. -/
theorem nodesOwn_ends (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r)
    (H : NodesPre lim r μ a Λ cx (f + 1) d) (hn : 1 ≤ a.n)
    (hMo : Mo = ChanHe.modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set) (hM1 : 1 ≤ Mo)
    (hM : Mo ≤ a.m * a.m) {x : ℤ} :
    Ends lim (P₀ ++ R) d (nodesOwn pMod pArr pC3) ⟨frame (nodesLocals x a Λ cx []), μ⟩
      (47 + tModulus a.np a.X₁.len a.X₂.len a.X₃.len a.V +
        tNodeArray a.m a.X₁.len a.X₂.len a.X₃.len a.V + T (8 * a.m ^ 2) (60 * a.V + 40))
      fun σ' => ∃ (y : ℤ) (μ' : ℕ → ℤ), Kept μ μ' a.fr ∧
        σ' = ⟨frame (nodesLocals x a Λ cx [Mo, (8 * a.m ^ 2 : ℕ), (a.fr + 8 * a.m ^ 2 : ℕ), y,
          flag (ConvOne (8 * a.m ^ 2) ((a.node Mo).oneArray a.V))]), μ'⟩ := by
  have hfits := H.fits hn
  have := hfits.room
  light_facts hfits
  have hsq : a.m ^ 2 = a.m * a.m := pow_two a.m
  have : (0 : ℤ) ≤ (a.m : ℤ) * a.m := by positivity
  -- M := modulus(s₁, l₁, s₂, l₂, s₃, l₃, Λ, np, pr, cnt, fr)
  light_call (C.modulus a Λ μ H.mem (H.lam ▸ lam_le a.V) (d + 1) (modulusNeed_ok H.ok))
    with _ μ₁ ⟨rfl, kept₁⟩
  rw [← hMo]
  -- len := 8 * (m * m); fr' := fr + len
  light_set (8 * a.m ^ 2 : ℕ) using hsq
  light_set (a.fr + 8 * a.m ^ 2 : ℕ) using hsq
  -- nodeArray(M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, fr, cnt, fr')
  light_call (C.array (a.push (8 * a.m ^ 2)) Mo a.fr μ₁ ((H.mem.kept kept₁).push .refl) hM1 hM
    ⟨le_rfl, Or.inr H.mem.set₁.below, Or.inr H.mem.set₂.below, Or.inr H.mem.set₃.below,
      Or.inr H.mem.envOk.belowCnt⟩ (d + 1) (nodeArrayNeed_ok H.ok))
    with y μ₂ ⟨harr, (kept₂ : KeptBut μ₁ μ₂ (a.fr + 8 * a.m ^ 2) a.fr (8 * a.m ^ 2))⟩
  -- a₀ := c3(len, 60 V + 40, fr, fr')
  light_call (c3_meets C.solver H.V_pos H.m_pos H.mem harr (solverNeed_ok H.ok))
    with _ μ₃ ⟨rfl, kept₃⟩
  exact ⟨y, μ₃, (kept₁.then kept₂ fun b hb => by omega).then kept₃ fun b hb => by omega, rfl⟩

/-- **The first child.**  Started in a memory μ that agrees below fr with the memory μ₀ in which the
procedure was called, the part leaves the number of heavy elements of the first set and the answer
for the child in HEAVY1 and ANS1, and changes no cell below fr.  x, y, z are the values of LEN, FR2,
RES, which are no longer used. -/
theorem nodesChild₁_ends (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r)
    (ih : NodesSpecAt lim (P₀ ++ R) p T r f) (H : NodesPre lim r μ₀ a Λ cx (f + 1) d)
    (hn : 1 ≤ a.n) (kept : Kept μ₀ μ a.fr) (hM1 : 1 ≤ Mo) (hM : Mo ≤ a.m * a.m)
    {x y z a₀ : ℤ} :
    Ends lim (P₀ ++ R) d (nodesChild₁ p pHeavy)
      ⟨frame (nodesLocals (f + 1 : ℕ) a Λ cx [Mo, x, y, z, a₀]), μ⟩
      (25 + tHeavy a.X₁.len a.V + tNodes T a.n a.V a.m a.np ((a.child₁ Mo).calls Λ f))
      fun σ' => ∃ μ' : ℕ → ℤ, Kept μ₀ μ' a.fr ∧
        σ' = ⟨frame (nodesLocals (f + 1 : ℕ) a Λ cx [Mo, x, y, z, a₀,
          #(ChanHe.heavy a.X₁.set Mo), flag ((a.child₁ Mo).Yes Λ f)]), μ'⟩ := by
  have hfits := H.fits hn
  have := hfits.room
  have hX := (H.mem.kept kept).set₁
  have hle := hX.le
  light_facts hfits
  -- h₁ := heavy(l₁, s₁, M, fr, cnt, fr + l₁)
  light_call (C.heavy (d + 1) (a.fr + a.X₁.len) _ _ _ _ a.fr _ _ _ μ
    ((hX.push .refl).bucket ((H.mem.kept kept).envOk.push .refl) hM1 hM)
    ⟨le_rfl, Or.inl hX.below, Or.inr H.mem.envOk.belowCnt⟩ (collNeed_ok H.ok hle hM))
    with _ μ₁ ⟨rfl, hset, kept₁⟩
  -- a₁ := nodes(F - 1, fr, h₁, s₂, l₂, s₃, l₃, cx, fr + l₁), where the local LEVELS holds f + 1
  light_call (ih (a.child₁ Mo) Λ cx μ₁ (d + 1) (H.child₁ kept kept₁ hset))
    with _ μ₂ ⟨rfl, (kept₂ : Kept μ₁ μ₂ (a.fr + a.X₁.len))⟩
  exact ⟨μ₂, (kept.then kept₁ fun b hb => by omega).then kept₂ fun b hb => by omega, rfl⟩

/-- **The second child**: as for the first, with HEAVY2 and ANS2. -/
theorem nodesChild₂_ends (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r)
    (ih : NodesSpecAt lim (P₀ ++ R) p T r f) (H : NodesPre lim r μ₀ a Λ cx (f + 1) d)
    (hn : 1 ≤ a.n) (kept : Kept μ₀ μ a.fr) (hM1 : 1 ≤ Mo) (hM : Mo ≤ a.m * a.m)
    {x y z a₀ h₁ a₁ : ℤ} :
    Ends lim (P₀ ++ R) d (nodesChild₂ p pHeavy)
      ⟨frame (nodesLocals (f + 1 : ℕ) a Λ cx [Mo, x, y, z, a₀, h₁, a₁]), μ⟩
      (25 + tHeavy a.X₂.len a.V + tNodes T a.n a.V a.m a.np ((a.child₂ Mo).calls Λ f))
      fun σ' => ∃ μ' : ℕ → ℤ, Kept μ₀ μ' a.fr ∧
        σ' = ⟨frame (nodesLocals (f + 1 : ℕ) a Λ cx [Mo, x, y, z, a₀, h₁, a₁,
          #(ChanHe.heavy a.X₂.set Mo), flag ((a.child₂ Mo).Yes Λ f)]), μ'⟩ := by
  have hfits := H.fits hn
  have := hfits.room
  have hX := (H.mem.kept kept).set₂
  have hle := hX.le
  light_facts hfits
  -- h₂ := heavy(l₂, s₂, M, fr, cnt, fr + l₂)
  light_call (C.heavy (d + 1) (a.fr + a.X₂.len) _ _ _ _ a.fr _ _ _ μ
    ((hX.push .refl).bucket ((H.mem.kept kept).envOk.push .refl) hM1 hM)
    ⟨le_rfl, Or.inl hX.below, Or.inr H.mem.envOk.belowCnt⟩ (collNeed_ok H.ok hle hM))
    with _ μ₁ ⟨rfl, hset, kept₁⟩
  -- a₂ := nodes(F - 1, s₁, l₁, fr, h₂, s₃, l₃, cx, fr + l₂), where the local LEVELS holds f + 1
  light_call (ih (a.child₂ Mo) Λ cx μ₁ (d + 1) (H.child₂ kept kept₁ hset))
    with _ μ₂ ⟨rfl, (kept₂ : Kept μ₁ μ₂ (a.fr + a.X₂.len))⟩
  exact ⟨μ₂, (kept.then kept₁ fun b hb => by omega).then kept₂ fun b hb => by omega, rfl⟩

/-- **The third child**: as for the first, with HEAVY3 and ANS3. -/
theorem nodesChild₃_ends (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r)
    (ih : NodesSpecAt lim (P₀ ++ R) p T r f) (H : NodesPre lim r μ₀ a Λ cx (f + 1) d)
    (hn : 1 ≤ a.n) (kept : Kept μ₀ μ a.fr) (hM1 : 1 ≤ Mo) (hM : Mo ≤ a.m * a.m)
    {x y z a₀ h₁ a₁ h₂ a₂ : ℤ} :
    Ends lim (P₀ ++ R) d (nodesChild₃ p pHeavy)
      ⟨frame (nodesLocals (f + 1 : ℕ) a Λ cx [Mo, x, y, z, a₀, h₁, a₁, h₂, a₂]), μ⟩
      (25 + tHeavy a.X₃.len a.V + tNodes T a.n a.V a.m a.np ((a.child₃ Mo).calls Λ f))
      fun σ' => ∃ μ' : ℕ → ℤ, Kept μ₀ μ' a.fr ∧
        σ' = ⟨frame (nodesLocals (f + 1 : ℕ) a Λ cx [Mo, x, y, z, a₀, h₁, a₁, h₂, a₂,
          #(ChanHe.heavy a.X₃.set Mo), flag ((a.child₃ Mo).Yes Λ f)]), μ'⟩ := by
  have hfits := H.fits hn
  have := hfits.room
  have hX := (H.mem.kept kept).set₃
  have hle := hX.le
  light_facts hfits
  -- h₃ := heavy(l₃, s₃, M, fr, cnt, fr + l₃)
  light_call (C.heavy (d + 1) (a.fr + a.X₃.len) _ _ _ _ a.fr _ _ _ μ
    ((hX.push .refl).bucket ((H.mem.kept kept).envOk.push .refl) hM1 hM)
    ⟨le_rfl, Or.inl hX.below, Or.inr H.mem.envOk.belowCnt⟩ (collNeed_ok H.ok hle hM))
    with _ μ₁ ⟨rfl, hset, kept₁⟩
  -- a₃ := nodes(F - 1, s₁, l₁, s₂, l₂, fr, h₃, cx, fr + l₃), where the local LEVELS holds f + 1
  light_call (ih (a.child₃ Mo) Λ cx μ₁ (d + 1) (H.child₃ kept kept₁ hset))
    with _ μ₂ ⟨rfl, (kept₂ : Kept μ₁ μ₂ (a.fr + a.X₃.len))⟩
  exact ⟨μ₂, (kept.then kept₁ fun b hb => by omega).then kept₂ fun b hb => by omega, rfl⟩

/-- **The answer** is yes if one of the four answers is.  The lemma is stated for arbitrary locals,
so that the 26 values need not be listed; for a state that is written as a list, hloc holds by
definition and determines the four statements. -/
theorem nodesAnswer_ends {loc : ℕ → ℤ} {R₀ R₁ R₂ R₃ : Prop} (hword : (4 : ℤ) ≤ lim.word)
    (hloc : loc NodesLocals.ANS0 = flag R₀ ∧ loc NodesLocals.ANS1 = flag R₁ ∧
      loc NodesLocals.ANS2 = flag R₂ ∧ loc NodesLocals.ANS3 = flag R₃ := by
      exact ⟨rfl, rfl, rfl, rfl⟩) :
    Ends lim P d nodesAnswer ⟨loc, μ⟩ 12 fun σ' =>
      σ'.loc 0 = flag (R₀ ∨ R₁ ∨ R₂ ∨ R₃) ∧ σ'.mem = μ := by
  obtain ⟨e₀, e₁, e₂, e₃⟩ := hloc
  have := flag_mem R₀
  have := flag_mem R₁
  have := flag_mem R₂
  have := flag_mem R₃
  unfold nodesAnswer
  -- if 0 < a₀ + a₁ + a₂ + a₃ then return 1 else return 0
  refine Ends.iteLast (fun hyes => ?_) (fun hno => ?_) (by light_side [e₀, e₁, e₂, e₃])
  · have hpos : 0 < flag R₀ + flag R₁ + flag R₂ + flag R₃ := by simpa [e₀, e₁, e₂, e₃] using hyes
    exact Ends.setLast ⟨by simp [flag_of ((flag_sum_pos _ _ _ _).1 hpos)], rfl⟩ (by simp; omega)
  · have hzero : ¬ 0 < flag R₀ + flag R₁ + flag R₂ + flag R₃ := by
      simpa [e₀, e₁, e₂, e₃] using hno
    exact Ends.setLast ⟨by simp [flag_of_not fun h => hzero ((flag_sum_pos _ _ _ _).2 h)], rfl⟩
      (by simp; omega)

/-- The time of a node: its own work and the three subtrees.  The 178 steps are
28 + 47 + 3 · 25 + 12 for the parts of nodesMain and 16 for the four tests of nodesBody. -/
theorem tNodes_succ_le (hN : NodeMem μ a) (hS : ¬ (a.X₁.set = ∅ ∨ a.X₂.set = ∅ ∨ a.X₃.set = ∅))
    (hMo : Mo = ChanHe.modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set) :
    178 + tModulus a.np a.X₁.len a.X₂.len a.X₃.len a.V +
      tNodeArray a.m a.X₁.len a.X₂.len a.X₃.len a.V + T (8 * a.m ^ 2) (60 * a.V + 40) +
      tHeavy a.X₁.len a.V + tHeavy a.X₂.len a.V + tHeavy a.X₃.len a.V +
      tNodes T a.n a.V a.m a.np ((a.child₁ Mo).calls Λ f) +
      tNodes T a.n a.V a.m a.np ((a.child₂ Mo).calls Λ f) +
      tNodes T a.n a.V a.m a.np ((a.child₃ Mo).calls Λ f)
    ≤ tNodes T a.n a.V a.m a.np (a.calls Λ (f + 1)) := by
  have hmod := tModulus_mono hN.set₁.le hN.set₂.le hN.set₃.le a.np a.V
  have harr := tNodeArray_mono hN.set₁.le hN.set₂.le hN.set₃.le a.m a.V
  have hheavy₁ := tHeavy_mono hN.set₁.le a.V
  have hheavy₂ := tHeavy_mono hN.set₂.le a.V
  have hheavy₃ := tHeavy_mono hN.set₃.le a.V
  have hcalls : a.calls Λ (f + 1) =
      1 + ((a.child₁ Mo).calls Λ f + (a.child₂ Mo).calls Λ f + (a.child₃ Mo).calls Λ f) := by
    simp [NodeArgs.calls, treeCalls, if_neg hS, ← hMo]
  rw [hcalls]
  generalize (a.child₁ Mo).calls Λ f = c₁
  generalize (a.child₂ Mo).calls Λ f = c₂
  generalize (a.child₃ Mo).calls Λ f = c₃
  simp only [tNodes]
  have hnode : tNode T a.n a.V a.m a.np = tModulus a.np a.n a.n a.n a.V +
      tNodeArray a.m a.n a.n a.n a.V + T (8 * a.m ^ 2) (60 * a.V + 40) + 3 * tHeavy a.n a.V +
      300 := rfl
  rw [show (1 + (c₁ + c₂ + c₃)) * (tNode T a.n a.V a.m a.np + 60) =
    (tNode T a.n a.V a.m a.np + 60) + c₁ * (tNode T a.n a.V a.m a.np + 60) +
    c₂ * (tNode T a.n a.V a.m a.np + 60) + c₃ * (tNode T a.n a.V a.m a.np + 60) by ring]
  omega

/-- The nodes of a tree with a nonempty root: the root and the nodes of the three subtrees. -/
theorem NodeArgs.yes_succ (hS : ¬ (a.X₁.set = ∅ ∨ a.X₂.set = ∅ ∨ a.X₃.set = ∅))
    (hMo : Mo = ChanHe.modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set) :
    a.Yes Λ (f + 1) ↔ ConvOne (8 * a.m ^ 2) ((a.node Mo).oneArray a.V) ∨
      (a.child₁ Mo).Yes Λ f ∨ (a.child₂ Mo).Yes Λ f ∨ (a.child₃ Mo).Yes Λ f := by
  simp only [NodeArgs.Yes, TreeYes, NodeArgs.child₁, NodeArgs.child₂, NodeArgs.child₃, Slot.heavy,
    Env.push, nodes, if_neg hS, ← hMo, List.mem_cons, List.mem_append, or_and_right, exists_or,
    exists_eq_left, or_assoc]

/-- **A triple of nonempty sets with at least one level to go**: the parts, one after the other.
The four tests of nodesBody have taken 16 steps. -/
theorem nodesMain_ends (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r)
    (ih : NodesSpecAt lim (P₀ ++ R) p T r f) (H : NodesPre lim r μ a Λ cx (f + 1) d)
    (hS : ¬ (a.X₁.set = ∅ ∨ a.X₂.set = ∅ ∨ a.X₃.set = ∅)) (hn : 1 ≤ a.n) :
    Ends lim (P₀ ++ R) d (nodesMain p pMod pArr pC3 pHeavy)
      ⟨frame (((f + 1 : ℕ) : ℤ) :: a.sets ++ [(cx : ℤ), a.fr]), μ⟩
      (tNodes T a.n a.V a.m a.np (a.calls Λ (f + 1)) - 16) fun σ' =>
      σ'.loc 0 = flag (a.Yes Λ (f + 1)) ∧ Kept μ σ'.mem a.fr := by
  obtain ⟨Mo, hMo⟩ :
      ∃ Mo, Mo = ChanHe.modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set := ⟨_, rfl⟩
  obtain ⟨hM1, hM⟩ : 1 ≤ Mo ∧ Mo ≤ a.m * a.m := by
    have := modulus_bounds H.primes (fun q hq => Nat.prime_of_mem_primesLE hq)
      (fun q hq => Nat.le_of_mem_primesLE hq) H.mem.set₁.bdd H.mem.set₂.bdd H.mem.set₃.bdd
    rwa [← H.lam, ← hMo, pow_two] at this
  have := tNodes_succ_le (T := T) (f := f) H.mem hS hMo
  have hfits := H.fits hn
  have := hfits.room
  light_facts H hfits
  rw [flag_congr (NodeArgs.yes_succ hS hMo)]
  -- the parameters
  light_piece (nodesParams_ends H.ctx (by omega) hfits.space_le) with _ rfl
  -- the node itself
  light_piece (nodesOwn_ends C H hn hMo hM1 hM) with _ ⟨x, μ₁, kept₁, rfl⟩
  -- the three children
  light_piece (nodesChild₁_ends C ih H hn kept₁ hM1 hM) with _ ⟨μ₂, kept₂, rfl⟩
  light_piece (nodesChild₂_ends C ih H hn kept₂ hM1 hM) with _ ⟨μ₃, kept₃, rfl⟩
  light_piece (nodesChild₃_ends C ih H hn kept₃ hM1 hM) with _ ⟨μ₄, kept₄, rfl⟩
  -- the answer
  light_piece (nodesAnswer_ends (by omega)) with _ ⟨hres, hmem⟩
  exact ⟨hres, hmem ▸ kept₄⟩

end parts

/-- **The recursion tree**: the procedure meets its specification. -/
theorem nodes_spec {P₀ R : Program} {p pMod pArr pC3 pHeavy : ℕ} {T : ℕ → ℕ → ℕ}
    {r : ℕ → ℕ → Need} (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r) :
    NodesSpec lim (P₀ ++ R) p T r := by
  intro f
  induction f with
  | zero =>
    intro a Λ cx μ d H
    have : (0 : ℤ) ≤ lim.word := le_trans (by positivity) H.ok.space
    -- if f = 0 then return 0
    refine .of_body C.self (Ends.iteLast (fun _ => ?_) (fun h => absurd h (by simp))
      (hT := by simp [tNodes, treeCalls]))
    exact Ends.setTo 0 ⟨by simp [flag_of_not, TreeYes, nodes], .refl⟩
      (hT := by simp [tNodes, treeCalls])
  | succ f ih =>
    intro a Λ cx μ d H
    have : (0 : ℤ) ≤ lim.word := le_trans (by positivity) H.ok.space
    have : 60 ≤ tNodes T a.n a.V a.m a.np (a.calls Λ (f + 1)) :=
      le_trans (by omega) (Nat.le_mul_of_pos_left _ (one_le_treeCalls _ _ _ _ _ _))
    -- A triple with an empty set has no node.
    have hempty : (a.X₁.set = ∅ ∨ a.X₂.set = ∅ ∨ a.X₃.set = ∅) → ∀ T', 2 ≤ T' →
        Ends lim (P₀ ++ R) d (.set 0 (k 0))
          ⟨frame (((f + 1 : ℕ) : ℤ) :: a.sets ++ [(cx : ℤ), a.fr]), μ⟩ T' fun σ' =>
          σ'.loc 0 = flag (a.Yes Λ (f + 1)) ∧ Kept μ σ'.mem a.fr := fun h T' hT' =>
      Ends.setTo 0 ⟨by simp [flag_of_not, TreeYes, nodes, h], .refl⟩
    -- if f = 0, l₁ = 0, l₂ = 0 or l₃ = 0 then return 0
    refine .of_body C.self (Ends.iteLast (fun h => absurd h (by simp; omega)) fun _ => ?_)
    refine Ends.iteLast (fun h => ?_) fun h₁ => ?_
    · exact hempty (Or.inl (H.mem.set₁.set.eq_empty (by simpa using h))) _ (by light_time)
    refine Ends.iteLast (fun h => ?_) fun h₂ => ?_
    · exact hempty (Or.inr (Or.inl (H.mem.set₂.set.eq_empty (by simpa using h)))) _
        (by light_time)
    refine Ends.iteLast (fun h => ?_) fun h₃ => ?_
    · exact hempty (Or.inr (Or.inr (H.mem.set₃.set.eq_empty (by simpa using h)))) _
        (by light_time)
    have hl₁ : a.X₁.len ≠ 0 := by simpa using h₁
    have hS : ¬ (a.X₁.set = ∅ ∨ a.X₂.set = ∅ ∨ a.X₃.set = ∅) := by
      rintro (h | h | h)
      · exact hl₁ (by rw [← H.mem.set₁.set.card, h, Finset.card_empty])
      · exact h₂ (by simp [← H.mem.set₂.set.card, h])
      · exact h₃ (by simp [← H.mem.set₃.set.card, h])
    light_piece (nodesMain_ends C ih H hS (by have := H.mem.set₁.le; omega))

end Light.Sec3.ChanHe
end

section
namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

variable {lim : Limits} {P : Program} {d : ℕ}

namespace RoundLocals

/-- The local variables of round: the arguments β, β', b, nd, val, bt, Λ, A, n, f, cx, fr; then
1 - b, A + n, A + 2n, and the sizes of the three sets. -/
abbrev BETA : ℕ := 0
@[inherit_doc BETA] abbrev BETA' : ℕ := 1
@[inherit_doc BETA] abbrev BIT : ℕ := 2
@[inherit_doc BETA] abbrev NVALUES : ℕ := 3
@[inherit_doc BETA] abbrev VAL : ℕ := 4
@[inherit_doc BETA] abbrev BITS : ℕ := 5
@[inherit_doc BETA] abbrev LAM : ℕ := 6
@[inherit_doc BETA] abbrev OUT0 : ℕ := 7
@[inherit_doc BETA] abbrev NMAX : ℕ := 8
@[inherit_doc BETA] abbrev LEVELS : ℕ := 9
@[inherit_doc BETA] abbrev CTX : ℕ := 10
@[inherit_doc BETA] abbrev FREE : ℕ := 11
@[inherit_doc BETA] abbrev NBIT : ℕ := 12
@[inherit_doc BETA] abbrev OUT1 : ℕ := 13
@[inherit_doc BETA] abbrev OUT2 : ℕ := 14
@[inherit_doc BETA] abbrev SIZE0 : ℕ := 15
@[inherit_doc BETA] abbrev SIZE1 : ℕ := 16
@[inherit_doc BETA] abbrev SIZE2 : ℕ := 17

end RoundLocals

open RoundLocals in
/-- The three sets of the splitting are written to A, A + n and A + 2n. -/
def roundSets (pPick : ℕ) : Stmt :=
  .set NBIT (k 1 -' v BIT) ;;
  .set OUT1 (v OUT0 +' v NMAX) ;;
  .set OUT2 (v OUT1 +' v NMAX) ;;
  .call pPick [v NVALUES, v VAL, v BITS, v LAM, v BETA, v BIT, v BETA', k 0, k 0, v OUT0] SIZE0 ;;
  .call pPick [v NVALUES, v VAL, v BITS, v LAM, v BETA, v NBIT, v BETA', k 0, k 1, v OUT1] SIZE1 ;;
  .call pPick [v NVALUES, v VAL, v BITS, v LAM, v BETA, v NBIT, v BETA', k 1, k 1, v OUT2] SIZE2

open RoundLocals in
/-- round(β, β', b, nd, val, bt, Λ, A, n, f, cx, fr), over the procedures number pPick and pNodes:
the three sets are written, and the recursive procedure is called on them. -/
def roundBody (pPick pNodes : ℕ) : Stmt :=
  roundSets pPick ;;
  .call pNodes [v LEVELS, v OUT0, v SIZE0, v OUT1, v SIZE1, v OUT2, v SIZE2, v CTX, v FREE] 0

/-- The recursive procedure makes at most `2 · 3^f` calls. -/
theorem ChRound.treeCalls_le_pow (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    treeCalls Q Λ f S₁ S₂ S₃ ≤ 2 * 3 ^ f := by
  have := treeCalls_le Q Λ f S₁ S₂ S₃
  have := length_nodes_le Q Λ f S₁ S₂ S₃
  omega

section front

variable {μ μ' : ℕ → ℤ} {a : FrontArgs}

/-- What the memory holds while the splittings are run through is kept if, below the free pointer,
only the 3n cells from A change. -/
theorem FrontMem.keptBut (h : FrontMem μ a)
    (hk : KeptBut μ μ' a.fr a.A (3 * a.n)) : FrontMem μ' a := by
  have keep : ∀ s len : ℕ, s + len ≤ a.fr → Apart a.A (3 * a.n) s len →
      ∀ i < len, μ' (s + i) = μ (s + i) := fun s len hb hap i hi =>
    hk _ ⟨by omega, by omega⟩
  exact { h with
    segVal := h.segVal.congr fun i hi => keep a.val a.nd h.belowVal h.apartVal i (h.lenD ▸ hi)
    segBt := h.segBt.congr fun i hi => keep a.bt (a.nd * a.Λ) h.belowBt h.apartBt i
      (by rw [← h.lenD, ← length_bitTable a.V]; exact hi)
    ctx := Seg.congr h.ctx fun i hi => keep a.cx 6 h.belowCx h.apartCx i (by simpa using hi)
    primes := ⟨h.primes.1, h.primes.2.congr fun i hi =>
      keep a.pr a.np h.belowPr h.apartPr i (by rw [h.primes.1]; simpa using hi)⟩
    zero := fun i hi => (keep a.cnt (a.m * a.m) h.belowCnt h.apartCnt i hi).trans (h.zero i hi) }

/-- The same if only the 3n cells from A change at all. -/
theorem FrontMem.of_sameOutside (h : FrontMem μ a)
    (hs : SameOutside μ μ' a.A (3 * a.n)) : FrontMem μ' a :=
  h.keptBut (SameOn.mono hs fun _ hb => hb.2)

/-- pick, called for the distinct values, with the output in one of the three parts of the 3n
cells from A. -/
theorem FrontMem.pick_meets (h : FrontMem μ a) {pPick : ℕ}
    (hPick : PickSpec lim P pPick) {β β' o : ℕ} (hβ : β < a.Λ) (hβ' : β' < a.Λ) (x x' two : ℤ)
    (ho : o + a.n ≤ 3 * a.n) (hfr : a.fr ≤ lim.space) (hw : (lim.space : ℤ) ≤ lim.word)
    (hword : (8 : ℤ) ≤ lim.word) :
    Meets lim P pPick d [a.nd, a.val, a.bt, a.Λ, β, x, β', x', two, (a.A + o : ℕ)] μ (tPick a.nd)
      fun r μ' =>
      r = ((pickList a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)).length : ℤ) ∧
        Seg μ' (a.A + o) (pickList a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)) ∧
        SameOutside μ μ' (a.A + o) a.nd := by
  light_facts h
  have : a.D.length * a.Λ = a.nd * a.Λ := by rw [h.lenD]
  rw [← h.lenD]
  exact hPick d a.val a.bt (a.A + o) a.Λ β β' x x' two a.D _ μ {
    lenTable := length_bitTable a.V a.Λ a.D
    posA := hβ
    posB := hβ'
    segSrc := h.segVal
    segTable := h.segBt
    apartSrc := by omega
    apartTable := by omega
    spaceSrc := by omega
    spaceTable := by omega
    spaceOut := by omega
    space_le := hw
    word := hword }

/-- Three subsets of the distinct values in the three parts of the 3n cells from A, with the rest of
the memory, are the memory of a node. -/
theorem FrontMem.nodeMem (h : FrontMem μ a)
    {k₁ k₂ k₃ : ℕ} {S₁ S₂ S₃ : Finset ℤ} (h₁ : SetAt μ a.A k₁ S₁) (h₂ : SetAt μ (a.A + a.n) k₂ S₂)
    (h₃ : SetAt μ (a.A + a.n + a.n) k₃ S₃) (hk₁ : k₁ ≤ a.n) (hk₂ : k₂ ≤ a.n) (hk₃ : k₃ ≤ a.n)
    (hS₁ : S₁ ⊆ a.D.toFinset) (hS₂ : S₂ ⊆ a.D.toFinset) (hS₃ : S₃ ⊆ a.D.toFinset) :
    NodeMem μ ⟨a.toEnv, ⟨a.A, k₁, S₁⟩, ⟨a.A + a.n, k₂, S₂⟩, ⟨a.A + a.n + a.n, k₃, S₃⟩⟩ := by
  light_facts h
  exact
    { envOk := ⟨h.primes, h.zero, h.belowPr, h.belowCnt, h.cntPr⟩
      set₁ := ⟨h₁, hk₁, h.bdd.mono hS₁, by dsimp only; omega, by dsimp only; omega⟩
      set₂ := ⟨h₂, hk₂, h.bdd.mono hS₂, by dsimp only; omega, by dsimp only; omega⟩
      set₃ := ⟨h₃, hk₃, h.bdd.mono hS₃, by dsimp only; omega, by dsimp only; omega⟩ }

/-- **The three sets of the splitting** are written, and with the rest of the memory they are the
memory of a node. -/
theorem roundSets_ends (hF : FrontMem μ a) {pPick : ℕ}
    (hPick : PickSpec lim P pPick) {β β' f : ℕ} (hβ : β < a.Λ) (hβ' : β' < a.Λ) (v : Bool)
    (hfr : a.fr ≤ lim.space) (hw : (lim.space : ℤ) ≤ lim.word) (hword : (8 : ℤ) ≤ lim.word)
    (hd : d < lim.depth) :
    Ends lim P d (roundSets pPick)
      ⟨frame [β, β', if v then 1 else 0, a.nd, a.val, a.bt, a.Λ, a.A, a.n, f, a.cx, a.fr], μ⟩
        (48 + 3 * tPick a.nd)
      fun σ' => ∃ (k₁ k₂ k₃ : ℕ) (μ' : ℕ → ℤ), SameOutside μ μ' a.A (3 * a.n) ∧
        NodeMem μ' ⟨a.toEnv, ⟨a.A, k₁, splitA a.V β v a.D.toFinset⟩,
          ⟨a.A + a.n, k₂, splitB a.V β β' v false a.D.toFinset⟩,
          ⟨a.A + a.n + a.n, k₃, splitB a.V β β' v true a.D.toFinset⟩⟩ ∧
        σ' = ⟨frame [β, β', if v then 1 else 0, a.nd, a.val, a.bt, a.Λ, a.A, a.n, f, a.cx, a.fr,
          if !v then 1 else 0, (a.A + a.n : ℕ), (a.A + a.n + a.n : ℕ), k₁, k₂, k₃], μ'⟩ := by
  have := hF.belowA
  have hndn := hF.nd_le
  have hlen : ∀ x x' two, (pickList a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)).length ≤ a.n :=
    fun x x' two => (length_pickList_le a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)).trans
      (hF.lenD ▸ hndn)
  -- b' := 1 - b; A₁ := A + n; A₂ := A₁ + n
  refine Ends.setToThen (if !v then 1 else 0) ?_ (by cases v <;> simp <;> omega)
  light_set (a.A + a.n : ℕ)
  light_set (a.A + a.n + a.n : ℕ)
  -- n₀ := pick(nd, val, bt, Λ, β, b, β', 0, 0, A)
  light_call (hF.pick_meets (o := 0) hPick hβ hβ' (if v then 1 else 0) 0 0
    (by omega) hfr hw hword) with _ μ₁ ⟨rfl, seg₁, same₁⟩
  have out₁ : SameOutside μ μ₁ a.A (3 * a.n) := same₁.mono (by omega) (by omega)
  have hF₁ := hF.of_sameOutside out₁
  -- n₁ := pick(nd, val, bt, Λ, β, b', β', 0, 1, A₁)
  light_call (hF₁.pick_meets (o := a.n) hPick hβ hβ' (if !v then 1 else 0) 0 1
    (by omega) hfr hw hword) with _ μ₂ ⟨rfl, seg₂, same₂⟩
  have out₂ : SameOutside μ₁ μ₂ a.A (3 * a.n) := same₂.mono (by omega) (by omega)
  have hF₂ := hF₁.of_sameOutside out₂
  -- n₂ := pick(nd, val, bt, Λ, β, b', β', 1, 1, A₂)
  light_call (hF₂.pick_meets (o := a.n + a.n) hPick hβ hβ' (if !v then 1 else 0) 1 1
    (by omega) hfr hw hword) with _ μ₃ ⟨rfl, seg₃, same₃⟩
  have out₃ : SameOutside μ₂ μ₃ a.A (3 * a.n) := same₃.mono (by omega) (by omega)
  -- The three lists are the three sets of the splitting.  (For the first set pick looks at one
  -- digit only, and the 0 stands for the value of the other digit, which it ignores.)
  obtain ⟨nodup₁, set₁⟩ := pick_splitA a.V a.Λ hβ hβ' v 0 hF.nodup
  obtain ⟨nodup₂, set₂⟩ := pick_splitB a.V a.Λ hβ hβ' v false hF.nodup
  obtain ⟨nodup₃, set₃⟩ := pick_splitB a.V a.Λ hβ hβ' v true hF.nodup
  have hlen₁ := hlen (if v then 1 else 0) 0 0
  have hlen₂ := hlen (if !v then 1 else 0) 0 1
  exact ⟨_, _, _, μ₃, out₁.trans (out₂.trans out₃),
    (hF₂.of_sameOutside out₃).nodeMem
      ⟨_, rfl, (seg₁.of_sameOutside same₂ (by omega)).of_sameOutside same₃ (by omega), nodup₁, set₁⟩
      ⟨_, rfl, seg₂.of_sameOutside same₃ (by omega), nodup₂, set₂⟩
      ⟨_, rfl, Nat.add_assoc a.A a.n a.n ▸ seg₃, nodup₃, set₃⟩ hlen₁ hlen₂ (hlen _ _ _)
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) (Finset.filter_subset _ _), rfl⟩

end front

/-- The time of round covers three calls of pick and the recursion tree: 48 steps and the three
calls for roundSets, 11 steps and the tree for the last call. -/
theorem le_tRound (T : ℕ → ℕ → ℕ) {n nd : ℕ} (hnd : nd ≤ n) (V m np Λ f : ℕ)
    (S₁ S₂ S₃ : Finset ℤ) :
    59 + 3 * tPick nd + tNodes T n V m np (treeCalls (Nat.primesLE m) Λ f S₁ S₂ S₃)
      ≤ tRound T n V m np f := by
  have : tPick nd ≤ tPick n := by simp only [tPick]; omega
  have htree := Nat.mul_le_mul_right (tNode T n V m np + 60)
    (ChRound.treeCalls_le_pow (Nat.primesLE m) Λ f S₁ S₂ S₃)
  simp only [tRound, tTree, tNodes] at htree ⊢
  omega

/-- **round meets its specification**, in every program that holds its body and meets the
specifications of the two routines that it calls. -/
theorem round_spec {p pPick pNodes : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (hP : P[p]? = some (roundBody pPick pNodes)) (hPick : PickSpec lim P pPick)
    (hN : NodesSpec lim P pNodes T r) : RoundSpec lim P p T r := by
  intro a f β β' v μ hF hβ hβ' d H
  refine .of_body hP ?_
  have hw := H.ok.space
  have hcells := H.ok.cells
  have hword := H.ok.word
  have hdepth := H.ok.depth
  simp only [gridNeed] at hcells hword hdepth
  push_cast at hword
  have := le_tRound T hF.nd_le a.V a.m a.np a.Λ f (splitA a.V β v a.D.toFinset)
    (splitB a.V β β' v false a.D.toFinset) (splitB a.V β β' v true a.D.toFinset)
  -- the three sets
  light_piece (roundSets_ends hF hPick hβ hβ' v (by omega) hw (by omega)
    (by omega)) with _ ⟨k₁, k₂, k₃, μ₁, out, hmem, rfl⟩
  -- return nodes(f, A, n₀, A₁, n₁, A₂, n₂, cx, fr)
  light_call (hN f _ a.Λ a.cx μ₁ (d + 1)
    { mem := hmem
      ctx := (hF.of_sameOutside out).ctx
      belowCtx := hF.belowCx
      apartCtx := hF.cntCx
      V_pos := H.V_pos
      m_pos := H.m_pos
      lam := H.lam
      primes := H.primes
      ok := { word := by dsimp only; omega, cells := hcells, space := hw,
              depth := by dsimp only; omega } })
    using NodeArgs.calls with _ μ₂ ⟨rfl, kept⟩
  exact ⟨by simp [SplitYes, TreeYes], out.then kept fun b hb => ⟨hb.2, hb.1⟩⟩

end Light.Sec3.ChanHe
end

section
open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

/-! ## The three answers, and the time -/

/-- 3SUM, through the three kinds of three-set inputs. -/
theorem threeSum_iff_trees {n U : ℕ} (hn : 1 ≤ n) (x : Fin n → ℤ) (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    ThreeSum x ↔
      (∃ β < Lam (2 * U), ∃ β' < Lam (2 * U), ∃ v,
        SplitYes (mPar n (2 * U)) (Lam (2 * U)) (fuel n) (2 * U) (univ.image x) β β' v) ∨
      TreeYes (mPar n (2 * U)) (Lam (2 * U)) (fuel n) (2 * U) (twiceSet x) {0} (univ.image x) ∨
      TreeYes (mPar n (2 * U)) (Lam (2 * U)) (fuel n) (2 * U) (zeroSet x) {0} {0} := by
  rw [instances_correct n U hn x hx]
  unfold instances allNodes SplitYes TreeYes reduction
  simp only [List.mem_map, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨y, ⟨ν, (⟨β, hβ, β', hβ', v, -, hν⟩ | hν | hν), rfl⟩, hc⟩
    · exact Or.inl ⟨β, hβ, β', hβ', v, ν, hν, hc⟩
    · exact Or.inr (Or.inl ⟨ν, hν, hc⟩)
    · exact Or.inr (Or.inr ⟨ν, hν, hc⟩)
  · rintro (⟨β, hβ, β', hβ', v, ν, hν, hc⟩ | ⟨ν, hν, hc⟩ | ⟨ν, hν, hc⟩)
    · exact ⟨_, ⟨ν, Or.inl ⟨β, hβ, β', hβ', v, by cases v <;> simp, hν⟩, rfl⟩, hc⟩
    · exact ⟨_, ⟨ν, Or.inr (Or.inl hν), rfl⟩, hc⟩
    · exact ⟨_, ⟨ν, Or.inr (Or.inr hν), rfl⟩, hc⟩

/-- A sum of three answers is positive if and only if one of them is yes. -/
theorem ChCore.flag_sum_pos (a b c : Prop) : 0 < flag a + flag b + flag c ↔ a ∨ b ∨ c := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;>
    simp [flag_of, flag_of_not, ha, hb, hc]

/-- The steps of the routine are within the time of the host. -/
theorem ChCore.time_le (T : ℕ → ℕ → ℕ) (n V : ℕ) :
    tParams n V + tPrep n (Lam V) (mPar n V)
        + tGrid T n V (mPar n V) #(Nat.primesLE (mPar n V)) (fuel n) (Lam V) + tTwice n
        + tTree T n V (mPar n V) #(Nat.primesLE (mPar n V)) (fuel n) + tZeroThree n
        + tTree T n V (mPar n V) #(Nat.primesLE (mPar n V)) (fuel n) + 126 ≤ coreTime T n V := by
  set m := mPar n V
  set np := #(Nat.primesLE m)
  set Λ := Lam V
  set tt := tTree T n V m np (fuel n) with htt
  have htree : tt = callsB n * nodeOwn n V m np + callsB n * T (8 * m ^ 2) (60 * V + 40) := by
    rw [htt, tTree, tNodes_eq, callsB]
    ring
  have hgrid : tGrid T n V m np (fuel n) Λ
      = Λ ^ 2 * (6 * tPick n + 2 * tt + 320) + 80 * Λ + 40 := by
    simp only [tGrid, tRow, tRound, ← htt]
    ring
  have hcore : coreTime T n V = tParams n V + tPrep n Λ m
      + (Λ ^ 2 * (6 * tPick n + 2 * tt + 320) + 280 * Λ ^ 2 + 2 * tt + 6 * tPick n + 600)
      + tTwice n + tZeroThree n + 400 := by
    simp only [coreTime, coreOwn, coreCalls, inputsB, tSetup]
    rw [htree]
    ring
  have : Λ ≤ Λ ^ 2 := Nat.le_self_pow two_ne_zero Λ
  rw [hgrid, hcore]
  omega

/-! ## The program -/

namespace Core

/-- The locals of core; each is assigned once.  The arguments: n, V, x and the free pointer b.  Then
a local for a result that is not read; the parameters Λ, m and f, which params has written to the
three cells from b; the base b + 3 of the arrays; the number of distinct values; the addresses of
the sorted copy, the values, their multiplicities, the table of digits, the three sets, the doubles
and the cell that holds 0, and the free pointer behind the arrays.  Then the answer for the
splittings, the number of doubles and the answer for them, and the length of the set for a triple
zero and the answer for it. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Bound : ℕ := 1
@[inherit_doc Len] abbrev Src : ℕ := 2
@[inherit_doc Len] abbrev Free : ℕ := 3
@[inherit_doc Len] abbrev Unread : ℕ := 4
@[inherit_doc Len] abbrev Digits : ℕ := 5
@[inherit_doc Len] abbrev PrimeBound : ℕ := 6
@[inherit_doc Len] abbrev Levels : ℕ := 7
@[inherit_doc Len] abbrev Base : ℕ := 8
@[inherit_doc Len] abbrev NumValues : ℕ := 9
@[inherit_doc Len] abbrev Sorted : ℕ := 10
@[inherit_doc Len] abbrev Val : ℕ := 11
@[inherit_doc Len] abbrev Mul : ℕ := 12
@[inherit_doc Len] abbrev Table : ℕ := 13
@[inherit_doc Len] abbrev Sets : ℕ := 14
@[inherit_doc Len] abbrev Doubles : ℕ := 15
@[inherit_doc Len] abbrev Zero : ℕ := 16
@[inherit_doc Len] abbrev Top : ℕ := 17
@[inherit_doc Len] abbrev AnsSplit : ℕ := 18
@[inherit_doc Len] abbrev NumDoubles : ℕ := 19
@[inherit_doc Len] abbrev AnsDoubles : ℕ := 20
@[inherit_doc Len] abbrev NumZero : ℕ := 21
@[inherit_doc Len] abbrev AnsZero : ℕ := 22

end Core

open Core in
/-- The parameters, and the arrays. -/
def coreSetup (pParams pPrep : ℕ) : Stmt :=
  .call pParams [v Len, v Bound, v Free] Unread ;;
  .set Digits (M (v Free)) ;;
  .set PrimeBound (M (v Free +' k 1)) ;;
  .set Levels (M (v Free +' k 2)) ;;
  .set Base (v Free +' k 3) ;;
  .call pPrep [v Len, v Bound, v Digits, v PrimeBound, v Src, v Base] NumValues

open Core in
/-- The addresses of the arrays from the sorted copy on. -/
def coreAddr : Stmt :=
  .set Sorted (v Base +' k 6 +' v PrimeBound +' v PrimeBound *' v PrimeBound) ;;
  .set Val (v Sorted +' v Len) ;;
  .set Mul (v Val +' v Len) ;;
  .set Table (v Mul +' v Len) ;;
  .set Sets (v Table +' v Len *' v Digits) ;;
  .set Doubles (v Sets +' k 3 *' v Len) ;;
  .set Zero (v Doubles +' v Len) ;;
  .set Top (v Zero +' k 1)

open Core in
/-- The loop over the splittings. -/
def coreSplit (pGrid : ℕ) : Stmt :=
  .call pGrid [v NumValues, v Val, v Table, v Digits, v Sets, v Len, v Levels, v Base, v Top]
    AnsSplit

open Core in
/-- The three-set input for the solutions a + a + c = 0 with a ≠ 0: the doubles of the repeated
values, {0}, and the values. -/
def coreDoubles (pTwice pNodes : ℕ) : Stmt :=
  .call pTwice [v NumValues, v Val, v Mul, v Doubles] NumDoubles ;;
  .call pNodes [v Levels, v Doubles, v NumDoubles, v Zero, k 1, v Val, v NumValues, v Base, v Top]
    AnsDoubles

open Core in
/-- The three-set input for the solution 0 + 0 + 0 = 0: {0} if 0 occurs three times and the empty
set if not, {0}, and {0}. -/
def coreZero (pZero pNodes : ℕ) : Stmt :=
  .call pZero [v NumValues, v Val, v Mul] NumZero ;;
  .call pNodes [v Levels, v Zero, v NumZero, v Zero, k 1, v Zero, k 1, v Base, v Top] AnsZero

open Core in
/-- The answer: 1 if one of the three answers is 1. -/
def coreAnswer : Stmt :=
  .ite (k 0 <' v AnsSplit +' v AnsDoubles +' v AnsZero) (.set Len (k 1)) (.set Len (k 0))

/-- core(n, V, x, b), over the procedures pParams, pPrep, pGrid, pTwice, pZero, pNodes. -/
def coreBody (pParams pPrep pGrid pTwice pZero pNodes : ℕ) : Stmt :=
  coreSetup pParams pPrep ;;
  coreAddr ;;
  coreSplit pGrid ;;
  coreDoubles pTwice pNodes ;;
  coreZero pZero pNodes ;;
  coreAnswer

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Core

/-- The locals after coreSetup: a is the memory map, f the number of levels, nd the number of
distinct values. -/
abbrev setupFrame (a : Map) (V f nd : ℕ) (x b unread : ℤ) : List ℤ :=
  [a.n, V, x, b, unread, a.Λ, a.m, f, a.b, nd]

/-- The locals after coreAddr. -/
abbrev addrFrame (a : Map) (V f nd : ℕ) (x b unread : ℤ) : List ℤ :=
  setupFrame a V f nd x b unread ++ [(a.srt : ℤ), a.val, a.mul, a.bt, a.A, a.tw, a.one, a.top]

end Core

open Core

/-! ## The addresses -/

/-- `coreAddr` takes 42 steps. -/
theorem coreAddr_cost : coreAddr.blockCost = 42 := rfl

/-- coreAddr computes the addresses. -/
theorem coreAddr_runs (a : Map) (V f nd : ℕ) (x b unread : ℤ) (μ : ℕ → ℤ)
    (htop : (a.top : ℤ) ≤ lim.word) (hword : (6 : ℤ) ≤ lim.word) :
    coreAddr.Runs lim ⟨frame (setupFrame a V f nd x b unread), μ⟩
      (· = ⟨frame (addrFrame a V f nd x b unread), μ⟩) := by
  have := a.layout
  have : (0 : ℤ) ≤ (a.m : ℤ) * a.m := by positivity
  have : (0 : ℤ) ≤ (a.n : ℤ) * a.Λ := by positivity
  exact ⟨by light_side [coreAddr],
    by simp [coreAddr, update_frame_setLocal, Map.top, Map.one, Map.tw, Map.A, Map.bt, Map.mul,
      Map.val, Map.srt, Map.cnt, Map.pr, add_assoc]⟩

/-! ## The arrays, and a three-set input in the memory -/

namespace Core

/-- The parameters are those of the reduction. -/
structure Par (a : Map) (V f : ℕ) : Prop where
  len_pos : 1 ≤ a.n
  bound_pos : 1 ≤ V
  primeBound : a.m = mPar a.n V
  digits : a.Λ = Lam V
  levels : f = fuel a.n

/-- There is a prime up to m. -/
theorem Par.primes_nonempty {a : Map} {V f : ℕ} (h : Par a V f) : (Nat.primesLE a.m).Nonempty := by
  have hcard := wPar_le_card_primesLE a.n V
  rw [← h.primeBound] at hcard
  have : 1 ≤ wPar a.n V :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.succ_pos _)) (Nat.succ_pos _)
  exact Finset.card_pos.1 (by omega)

/-- The bound on the primes is positive. -/
theorem Par.primeBound_pos {a : Map} {V f : ℕ} (h : Par a V f) : 1 ≤ a.m :=
  (Finset.card_pos.2 h.primes_nonempty).trans_le (Nat.card_primesLE_le a.m)

/-- The cells that no routine called after coreAddr writes: those below the three sets of a
splitting, and the cell that holds 0. -/
abbrev Fixed (a : Map) (q : ℕ) : Prop := q < a.A ∨ q = a.one

/-- The arrays that the parts after coreAddr read: the distinct values D, how often they occur, the
block of parameters, the primes, the zeros of the count table, and the cell that holds 0. -/
structure Arrays (a : Map) (V : ℕ) (D C : List ℤ) (ν : ℕ → ℤ) : Prop where
  val : Seg ν a.val D
  mul : Seg ν a.mul C
  ctx : CtxAt ν a.cx V a.m a.Λ #(Nat.primesLE a.m) a.pr a.cnt
  primes : PrimesAt ν a.pr #(Nat.primesLE a.m) a.m
  zero : ZeroAt ν a.cnt (a.m * a.m)
  one : ν a.one = 0
  val_le : D.length ≤ a.n
  mul_le : C.length ≤ a.n

section

variable {a : Map} {V : ℕ} {D C : List ℤ} {μ ν : ℕ → ℤ}

/-- The arrays are still there if the fixed cells have not changed. -/
theorem Arrays.of_sameOn (h : Arrays a V D C μ) (hs : SameOn (Fixed a) μ ν) :
    Arrays a V D C ν := by
  have := a.layout
  have hval := h.val_le
  have hmul := h.mul_le
  have := Nat.card_primesLE_le a.m
  exact
    { val := h.val.of_sameOn hs fun i hi => Or.inl (by omega)
      mul := h.mul.of_sameOn hs fun i hi => Or.inl (by omega)
      ctx := Seg.of_sameOn h.ctx hs fun i hi => Or.inl (by simp at hi; omega)
      primes := ⟨rfl, h.primes.2.of_sameOn hs fun i hi => Or.inl (by
        rw [List.length_map, Finset.length_sort] at hi
        omega)⟩
      zero := fun q hq => (hs _ (Or.inl (by omega))).trans (h.zero q hq)
      one := (hs _ (Or.inr rfl)).trans h.one
      val_le := hval, mul_le := hmul }

/-- A set of at most n numbers of absolute value at most V, in the l cells from s, which lie among
the arrays from the values on. -/
structure Placed (a : Map) (V : ℕ) (ν : ℕ → ℤ) (s l : ℕ) (S : Finset ℤ) : Prop where
  set : SetAt ν s l S
  le : l ≤ a.n
  bdd : Bdd V S
  from_val : a.val ≤ s
  below : s + l ≤ a.top

/-- The set of the distinct values. -/
theorem Arrays.placed_val (h : Arrays a V D C ν) (hD : D.Nodup) (hb : Bdd V D.toFinset) :
    Placed a V ν a.val D.length D.toFinset := by
  have := a.layout
  have hval := h.val_le
  exact ⟨⟨D, rfl, h.val, hD, rfl⟩, hval, hb, le_rfl, by omega⟩

/-- The set {0}. -/
theorem Arrays.placed_zero (h : Arrays a V D C ν) (hn : 1 ≤ a.n) : Placed a V ν a.one 1 {0} := by
  have := a.layout
  exact ⟨⟨[0], rfl, by simpa [seg_cons] using h.one, by simp, by simp⟩, hn, bdd_zero V, by omega,
    by omega⟩

/-- Three sets among the arrays are a three-set input as the recursive procedure wants it. -/
theorem Arrays.nodesPre {r : ℕ → ℕ → Need} {f s₁ l₁ s₂ l₂ s₃ l₃ : ℕ} {S₁ S₂ S₃ : Finset ℤ}
    (h : Arrays a V D C ν) (hpar : Par a V f) (p₁ : Placed a V ν s₁ l₁ S₁)
    (p₂ : Placed a V ν s₂ l₂ S₂) (p₃ : Placed a V ν s₃ l₃ S₃)
    (hok : (nodesNeed r a.n V a.m f).Ok lim a.top d) :
    NodesPre lim r ν ⟨⟨a.top, a.n, V, a.m, #(Nat.primesLE a.m), a.pr, a.cnt⟩, ⟨s₁, l₁, S₁⟩,
      ⟨s₂, l₂, S₂⟩, ⟨s₃, l₃, S₃⟩⟩ a.Λ a.cx f d := by
  have := a.layout
  have := Nat.card_primesLE_le a.m
  light_facts p₁ p₂ p₃
  exact
    { mem :=
        { envOk := ⟨h.primes, h.zero, by dsimp only; omega, by dsimp only; omega,
            by dsimp only; omega⟩
          set₁ := ⟨p₁.set, p₁.le, p₁.bdd, p₁.below, by dsimp only; omega⟩
          set₂ := ⟨p₂.set, p₂.le, p₂.bdd, p₂.below, by dsimp only; omega⟩
          set₃ := ⟨p₃.set, p₃.le, p₃.bdd, p₃.below, by dsimp only; omega⟩ }
      ctx := h.ctx, belowCtx := by dsimp only; omega, apartCtx := by dsimp only; omega
      V_pos := hpar.bound_pos, m_pos := hpar.primeBound_pos, lam := hpar.digits
      primes := hpar.primes_nonempty, ok := hok }

/-- The recursive procedure, called for three sets among the arrays. -/
theorem Arrays.nodes_meets {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {pNodes f s₁ l₁ s₂ l₂ s₃ l₃ : ℕ}
    {S₁ S₂ S₃ : Finset ℤ} (hNodes : NodesSpec lim P pNodes T r) (h : Arrays a V D C ν)
    (hpar : Par a V f) (p₁ : Placed a V ν s₁ l₁ S₁) (p₂ : Placed a V ν s₂ l₂ S₂)
    (p₃ : Placed a V ν s₃ l₃ S₃) (hok : (nodesNeed r a.n V a.m f).Ok lim a.top d) :
    Meets lim P pNodes d [(f : ℤ), s₁, l₁, s₂, l₂, s₃, l₃, a.cx, a.top] ν
      (tNodes T a.n V a.m #(Nat.primesLE a.m) (treeCalls (Nat.primesLE a.m) a.Λ f S₁ S₂ S₃))
      fun res μ' => res = flag (TreeYes a.m a.Λ f V S₁ S₂ S₃) ∧ Kept ν μ' a.top :=
  hNodes f _ a.Λ a.cx ν d (h.nodesPre hpar p₁ p₂ p₃ hok)

end


/-! ## The three answers -/


/-- What the parts after coreAddr assume: the parameters, the values of the input X, the arrays in
the memory μ, and what the limits must allow. -/
structure Ctx (lim : Limits) (r : ℕ → ℕ → Need) (d : ℕ) (a : Map) (V f : ℕ) (X D C : List ℤ)
    (μ : ℕ → ℤ) : Prop where
  par : Par a V f
  values : Values a.n X D C
  arrays : Arrays a V D C μ
  bddVal : Bdd V D.toFinset
  bddDoubles : Bdd V (twiceSet (vecOf a.n X))
  space : (lim.space : ℤ) ≤ lim.word
  cells : a.top + (nodesNeed r a.n V a.m f).cells ≤ lim.space
  word : ((nodesNeed r a.n V a.m f).word : ℤ) + 8 * V + 4 * a.n + 64 ≤ lim.word
  depth : d + (nodesNeed r a.n V a.m f).depth + 4 ≤ lim.depth

section

variable {r : ℕ → ℕ → Need} {a : Map} {V f : ℕ} {X D C : List ℤ} {μ ν : ℕ → ℤ}

/-- The limits allow for a call of nodes. -/
theorem Ctx.okNodes (K : Ctx lim r d a V f X D C μ) :
    (nodesNeed r a.n V a.m f).Ok lim a.top (d + 1) :=
  ⟨by have := K.word; omega, K.cells, K.space, by have := K.depth; omega⟩

/-- The limits allow for a call of grid. -/
theorem Ctx.okGrid (K : Ctx lim r d a V f X D C μ) :
    (gridNeed r a.n V a.m f 2).Ok lim a.top (d + 1) :=
  ⟨by have := K.word; simp only [gridNeed]; push_cast; omega, K.cells, K.space,
    by have := K.depth; simp only [gridNeed]; omega⟩

/-- The recursive procedure stays within the time for a tree with f levels. -/
theorem tNodes_le_tTree (T : ℕ → ℕ → ℕ) (n V m np Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    tNodes T n V m np (treeCalls (Nat.primesLE m) Λ f S₁ S₂ S₃) ≤ tTree T n V m np f :=
  Nat.mul_le_mul_right _ (ChRound.treeCalls_le_pow _ _ _ _ _ _)

/-- The set for a triple zero lies in the cell that holds 0; its length is the answer of
zeroThree. -/
theorem Ctx.placed_zeroSet (K : Ctx lim r d a V f X D C μ) (h : Arrays a V D C ν) :
    ∃ l : ℕ, flag (∃ q ∈ D.zip C, q.1 = 0 ∧ 3 ≤ q.2) = (l : ℤ) ∧
      Placed a V ν a.one l (zeroSet (vecOf a.n X)) := by
  have := a.layout
  have := h.placed_zero K.par.len_pos
  by_cases h3 : 3 ≤ #{i | vecOf a.n X i = 0}
  · refine ⟨1, by rw [flag_of (K.values.zeroThree.2 h3)]; rfl, ?_⟩
    rwa [zeroSet, if_pos h3]
  · refine ⟨0, by rw [flag_of_not (mt K.values.zeroThree.1 h3)]; rfl, ?_⟩
    rw [zeroSet, if_neg h3]
    exact ⟨⟨[], rfl, Seg.nil, by simp, by simp⟩, Nat.zero_le _, fun _ hx => absurd hx (by simp),
      by omega, by omega⟩

end

end Core

section parts

variable {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {a : Map} {V f : ℕ} {X D C : List ℤ} {μ ν : ℕ → ℤ}
  {x b unread : ℤ}

/-- grid, called for the arrays of a map. -/
theorem grid_meets_of_map {pGrid : ℕ} (hGrid : GridSpec lim P pGrid T r)
    (hF : FrontMem μ (a.front V D)) (H : GridPre lim r (a.front V D) f 2 d) :
    Meets lim P pGrid d [(D.length : ℤ), a.val, a.bt, a.Λ, a.A, a.n, f, a.cx, a.top] μ
      (tGrid T a.n V a.m #(Nat.primesLE a.m) f a.Λ) fun res μ' =>
      res = flag (∃ β < a.Λ, ∃ β' < a.Λ, ∃ v, SplitYes a.m a.Λ f V D.toFinset β β' v) ∧
        KeptBut μ μ' a.top a.A (3 * a.n) :=
  hGrid (a.front V D) f μ hF d H

/-- coreSplit decides whether some splitting gives a yes-instance. -/
theorem coreSplit_ends {pGrid : ℕ} (hGrid : GridSpec lim P pGrid T r)
    (K : Ctx lim r d a V f X D C μ)
    (hF : FrontMem μ (a.front V D)) :
    Ends lim P d (coreSplit pGrid) ⟨frame (addrFrame a V f D.length x b unread), μ⟩
      (tGrid T a.n V a.m #(Nat.primesLE a.m) f a.Λ + 11) fun σ' => ∃ μ' : ℕ → ℤ,
        σ' = ⟨frame (addrFrame a V f D.length x b unread ++
          [flag (∃ β < a.Λ, ∃ β' < a.Λ, ∃ v, SplitYes a.m a.Λ f V D.toFinset β β' v)]), μ'⟩ ∧
          SameOn (Fixed a) μ μ' := by
  have := a.layout
  have := K.depth
  -- ansSplit := grid(numValues, val, table, digits, sets, len, levels, base, top)
  light_call (grid_meets_of_map hGrid hF ⟨K.par.bound_pos, K.par.primeBound_pos, K.par.digits,
    K.par.primes_nonempty, K.okGrid⟩) with _ μ' ⟨rfl, hkept⟩
  exact ⟨μ', rfl, hkept.mono fun q hq => by omega⟩

/-- coreDoubles decides the three-set input for the solutions that use a value other than 0
twice. -/
theorem coreDoubles_ends {pTwice pNodes : ℕ} (hTwice : TwiceSpec lim P pTwice)
    (hNodes : NodesSpec lim P pNodes T r) (K : Ctx lim r d a V f X D C μ)
    (hν : SameOn (Fixed a) μ ν) (ans : ℤ) :
    Ends lim P d (coreDoubles pTwice pNodes)
      ⟨frame (addrFrame a V f D.length x b unread ++ [ans]), ν⟩
      (tTwice a.n + tTree T a.n V a.m #(Nat.primesLE a.m) f + 17) fun σ' =>
        ∃ (len : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (addrFrame a V f D.length x b unread ++ [ans, len,
          flag (TreeYes a.m a.Λ f V (twiceSet (vecOf a.n X)) {0} D.toFinset)]), μ'⟩ ∧
          SameOn (Fixed a) μ μ' := by
  have := a.layout
  have hspace := K.space
  have := K.cells
  have hval := K.arrays.val_le
  light_facts K
  have hlenC : C.length = D.length := by rw [K.values.counts, List.length_map]
  have harr := K.arrays.of_sameOn hν
  have : tTwice D.length ≤ tTwice a.n := by simp only [tTwice]; omega
  have := tNodes_le_tTree T a.n V a.m #(Nat.primesLE a.m) a.Λ f
    (twiceSet (vecOf a.n X)) {0} D.toFinset
  -- numDoubles := twice(numValues, val, mul, doubles)
  light_call (hTwice (d + 1) a.val a.mul a.tw V D C ν
    { len := hlenC, bounded := fun y hy => K.bddVal y (List.mem_toFinset.2 hy)
      segVal := harr.val, segMul := harr.mul, apartVal := by omega, apartMul := by omega
      spaceVal := by omega, spaceMul := by omega, spaceOut := by omega, space_le := hspace
      word := by omega }) with _ ν₁ ⟨rfl, hdoubles, hsame⟩
  have hν₁ : SameOn (Fixed a) μ ν₁ := hν.trans (SameOn.mono hsame fun q hq => by omega)
  have harr₁ := K.arrays.of_sameOn hν₁
  have hplaced : Placed a V ν₁ a.tw (twiceList D C).length (twiceSet (vecOf a.n X)) :=
    ⟨⟨_, rfl, hdoubles, K.values.twice.1, K.values.twice.2⟩,
      (length_twiceList_le D C).trans hval, K.bddDoubles, by omega,
      by have := length_twiceList_le D C; omega⟩
  -- ansDoubles := nodes(levels, doubles, numDoubles, zero, 1, val, numValues, base, top)
  light_call (harr₁.nodes_meets hNodes K.par hplaced (harr₁.placed_zero K.par.len_pos)
    (harr₁.placed_val K.values.nodup K.bddVal) K.okNodes) with _ μ' ⟨rfl, hkept⟩
  exact ⟨_, μ', rfl, hν₁.trans (hkept.mono fun q hq => by omega)⟩

/-- coreZero decides the three-set input for the solution that uses 0 three times. -/
theorem coreZero_ends {pZero pNodes : ℕ} (hZero : ZeroThreeSpec lim P pZero)
    (hNodes : NodesSpec lim P pNodes T r) (K : Ctx lim r d a V f X D C μ)
    (hν : SameOn (Fixed a) μ ν) (ans₁ len ans₂ : ℤ) :
    Ends lim P d (coreZero pZero pNodes)
      ⟨frame (addrFrame a V f D.length x b unread ++ [ans₁, len, ans₂]), ν⟩
      (tZeroThree a.n + tTree T a.n V a.m #(Nat.primesLE a.m) f + 16) fun σ' =>
        ∃ (len' : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (addrFrame a V f D.length x b unread ++ [ans₁, len,
          ans₂, len', flag (TreeYes a.m a.Λ f V (zeroSet (vecOf a.n X)) {0} {0})]), μ'⟩ ∧
          SameOn (Fixed a) μ μ' := by
  have := a.layout
  have hspace := K.space
  have := K.cells
  light_facts K K.arrays
  have hlenC : C.length = D.length := by rw [K.values.counts, List.length_map]
  have harr := K.arrays.of_sameOn hν
  have : tZeroThree D.length ≤ tZeroThree a.n := by simp only [tZeroThree]; omega
  have := tNodes_le_tTree T a.n V a.m #(Nat.primesLE a.m) a.Λ f
    (zeroSet (vecOf a.n X)) {0} {0}
  obtain ⟨l, hflag, hplaced⟩ := K.placed_zeroSet harr
  have hzero := harr.placed_zero (V := V) K.par.len_pos
  -- numZero := zeroThree(numValues, val, mul)
  light_call (hZero (d + 1) a.val a.mul D C ν hlenC harr.val harr.mul (by omega)
    (by omega) hspace (by omega)) with _ ν₁ ⟨rfl, hν₁⟩
  rw [hν₁, hflag]
  -- ansZero := nodes(levels, zero, numZero, zero, 1, zero, 1, base, top)
  light_call (harr.nodes_meets hNodes K.par hplaced hzero hzero K.okNodes)
    with _ μ' ⟨rfl, hkept⟩
  exact ⟨_, μ', rfl, hν.trans (hkept.mono fun q hq => by omega)⟩

/-- `coreAnswer` takes 10 steps. -/
theorem coreAnswer_cost : coreAnswer.blockCost = 10 := rfl

/-- coreAnswer returns 1 if one of the three answers is yes, and 0 if not. -/
theorem coreAnswer_runs (G₁ G₂ G₃ : Prop) (nd : ℕ) (len₂ len₃ : ℤ) (hword : (6 : ℤ) ≤ lim.word) :
    coreAnswer.Runs lim
      ⟨frame (addrFrame a V f nd x b unread ++ [flag G₁, len₂, flag G₂, len₃, flag G₃]), μ⟩
      fun σ' => σ'.loc 0 = flag (G₁ ∨ G₂ ∨ G₃) ∧ σ'.mem = μ := by
  have := flag_mem G₁
  have := flag_mem G₂
  have := flag_mem G₃
  have hpos := ChCore.flag_sum_pos G₁ G₂ G₃
  by_cases h : G₁ ∨ G₂ ∨ G₃
  · have hsum := hpos.2 h
    exact ⟨by light_side [coreAnswer], by simp [coreAnswer, hsum, flag_of h]⟩
  · have hsum := mt hpos.1 h
    exact ⟨by light_side [coreAnswer], by simp [coreAnswer, hsum, flag_of_not h]⟩

end parts

/-! ## The parameters and the arrays -/

namespace Core

/-- What coreSetup leaves in the memory μ': the arrays for the values D of the input X, with how
often they occur; nothing below the free pointer b has changed. -/
structure Setup (a : Map) (V b : ℕ) (X D C : List ℤ) (μ μ' : ℕ → ℤ) : Prop where
  values : Values a.n X D C
  mul : Seg μ' a.mul C
  one : μ' a.one = 0
  front : FrontMem μ' (a.front V D)
  kept : Kept μ μ' b

end Core

/-- coreSetup computes the parameters and fills the arrays. -/
theorem coreSetup_ends {pParams pPrep : ℕ} (hParams : ParamsSpec lim P pParams)
    (hPrep : PrepSpec lim P pPrep) {r : ℕ → ℕ → Need} {a : Map} {V f x b : ℕ} {X : List ℤ}
    {μ : ℕ → ℤ} (hpar : Par a V f) (hb : a.b = b + 3) (hlen : X.length = a.n) (hX : AbsLe X V)
    (hseg : Seg μ x X) (hxb : x + a.n ≤ b) (hok : (coreNeed r a.n V).Ok lim b d) :
    Ends lim P d (coreSetup pParams pPrep) ⟨frame [a.n, V, x, b], μ⟩
      (tParams a.n V + tPrep a.n a.Λ a.m + 30) fun σ' =>
        ∃ (unread : ℤ) (D C : List ℤ) (μ' : ℕ → ℤ),
          σ' = ⟨frame (setupFrame a V f D.length x b unread), μ'⟩ ∧ Setup a V b X D C μ μ' := by
  have := a.layout
  have hspace := hok.space
  have hcells := hok.cells
  have hword := hok.word
  have hdepth := hok.depth
  simp only [coreNeed, coreCells, ← hpar.primeBound, ← hpar.digits, ← hpar.levels]
    at hcells hword hdepth
  push_cast at hword
  have : (0 : ℤ) ≤ 8 * ((a.m : ℤ) + 1) ^ 2 := by positivity
  -- unread := params(len, bound, free)
  light_call (hParams (d + 1) a.n V b μ (by omega) hspace
    (by rw [← hpar.primeBound]; push_cast; omega) (by omega)) with unread μ₁ ⟨hcellsP, hsame₁⟩
  rw [← hpar.primeBound, ← hpar.digits, ← hpar.levels] at hcellsP
  have hdigits : μ₁ b = a.Λ := by simpa using hcellsP 0 (by simp)
  have hprime : μ₁ (b + 1) = a.m := by simpa using hcellsP 1 (by simp)
  have hlevels : μ₁ (b + 2) = f := by simpa using hcellsP 2 (by simp)
  have haddr₁ : ((b : ℤ) + 1).toNat = b + 1 := by omega
  have haddr₂ : ((b : ℤ) + 2).toNat = b + 2 := by omega
  -- digits := mem[free]; primeBound := mem[free + 1]; levels := mem[free + 2]; base := free + 3
  light_set a.Λ using hdigits
  light_set a.m using haddr₁, hprime
  light_set f using haddr₂, hlevels
  light_set a.b using hb
  -- numValues := prep(len, bound, digits, primeBound, src, base)
  light_call (hPrep (d + 1) a V x X μ₁
    { len := hlen, bounded := hX, below := by omega, bound_pos := hpar.bound_pos
      digits := hpar.digits
      ok := ⟨by simp only [prepNeed]; push_cast; omega, by simp only [prepNeed]; omega, hspace,
        by simp only [prepNeed]; omega⟩ } (hseg.of_sameOutside hsame₁ (by omega)))
    with _ μ₂ ⟨⟨D, C, rfl, hvalues, hmul, hone, hfront⟩, hkept₂⟩
  exact ⟨unread, D, C, μ₂, rfl, hvalues, hmul, hone, hfront,
    fun q hq => (hkept₂ q (by omega)).trans (hsame₁ q (Or.inl hq))⟩

/-- After coreSetup the other parts find what they assume. -/
theorem Core.Setup.ctx {r : ℕ → ℕ → Need} {a : Map} {U b : ℕ} {X D C : List ℤ} {μ μ' : ℕ → ℤ}
    (S : Setup a (2 * U) b X D C μ μ') (hpar : Par a (2 * U) (fuel a.n)) (hb : a.b = b + 3)
    (hx : ∀ i, |vecOf a.n X i| ≤ (U : ℤ)) (hok : (coreNeed r a.n (2 * U)).Ok lim b d) :
    Ctx lim r d a (2 * U) (fuel a.n) X D C μ' := by
  have := a.layout
  have hcells := hok.cells
  have hword := hok.word
  have hdepth := hok.depth
  simp only [coreNeed, coreCells, ← hpar.primeBound, ← hpar.digits] at hcells hword hdepth
  push_cast at hword
  have : (0 : ℤ) ≤ 8 * ((a.m : ℤ) + 1) ^ 2 := by positivity
  exact
    { par := hpar, values := S.values
      arrays :=
        { val := S.front.segVal, mul := S.mul, ctx := S.front.ctx, primes := S.front.primes
          zero := S.front.zero, one := S.one, val_le := S.values.length_le
          mul_le := by rw [S.values.counts, List.length_map]; exact S.values.length_le }
      bddVal := S.front.bdd, bddDoubles := bdd_twiceSet hx, space := hok.space
      cells := by omega, word := by push_cast; omega, depth := by omega }

/-! ## The routine -/

/-- The six parts one after the other, for the memory map a with the base b + 3. -/
theorem coreBody_ends {pParams pPrep pGrid pTwice pZero pNodes : ℕ} {T : ℕ → ℕ → ℕ}
    {r : ℕ → ℕ → Need} (hParams : ParamsSpec lim P pParams) (hPrep : PrepSpec lim P pPrep)
    (hGrid : GridSpec lim P pGrid T r) (hTwice : TwiceSpec lim P pTwice)
    (hZero : ZeroThreeSpec lim P pZero) (hNodes : NodesSpec lim P pNodes T r) {a : Map}
    {U x b : ℕ} {X : List ℤ} {μ : ℕ → ℤ} (hpar : Par a (2 * U) (fuel a.n)) (hb : a.b = b + 3)
    (hlen : X.length = a.n) (hx : ∀ i, |vecOf a.n X i| ≤ (U : ℤ)) (hX : AbsLe X (2 * U : ℕ))
    (hseg : Seg μ x X) (hxb : x + a.n ≤ b) (hok : (coreNeed r a.n (2 * U)).Ok lim b d) :
    Ends lim P d (coreBody pParams pPrep pGrid pTwice pZero pNodes)
      ⟨frame [a.n, ((2 * U : ℕ) : ℤ), x, b], μ⟩ (coreTime T a.n (2 * U)) fun σ' =>
        σ'.loc 0 = flag (ThreeSum (vecOf a.n X)) ∧ Kept μ σ'.mem b := by
  have := a.layout
  have hfinal := threeSum_iff_trees hpar.len_pos (vecOf a.n X) hx
  have htime := ChCore.time_le T a.n (2 * U)
  rw [← hpar.primeBound, ← hpar.digits] at hfinal htime
  have := coreAddr_cost
  have := coreAnswer_cost
  refine Ends.mono ?_ htime fun _ h => h
  -- coreSetup
  light_piece (coreSetup_ends hParams hPrep hpar hb hlen hX hseg hxb hok)
    with _ ⟨unread, D, C, μ₁, rfl, S⟩
  rw [← S.values.values] at hfinal
  have K := S.ctx hpar hb hx hok
  have := K.cells
  light_facts K
  -- coreAddr
  refine Ends.next _ (Ends.block ((coreAddr_runs a (2 * U) (fuel a.n) D.length x b unread μ₁
    (by omega) (by omega)).mono ?_) le_rfl)
  rintro _ rfl
  -- coreSplit
  light_piece (coreSplit_ends hGrid K S.front) with _ ⟨μ₂, rfl, hμ₂⟩
  -- coreDoubles
  light_piece (coreDoubles_ends hTwice hNodes K hμ₂ _) with _ ⟨len₂, μ₃, rfl, hμ₃⟩
  -- coreZero
  light_piece (coreZero_ends hZero hNodes K hμ₃ _ _ _) with _ ⟨len₃, μ₄, rfl, hμ₄⟩
  -- coreAnswer
  refine Ends.block ((coreAnswer_runs _ _ _ _ _ _ (by omega)).mono ?_)
  rintro σ' ⟨hres, hmem⟩
  exact ⟨by rw [hres, propext hfinal], fun q hq => by
    rw [hmem, hμ₄ q (Or.inl (by omega)), S.kept q hq]⟩

/-- **core meets its specification**, in every program that holds its body and meets the
specifications of the routines that it calls. -/
theorem core_spec {p pParams pPrep pGrid pTwice pZero pNodes : ℕ} {T : ℕ → ℕ → ℕ}
    {r : ℕ → ℕ → Need} (hP : P[p]? = some (coreBody pParams pPrep pGrid pTwice pZero pNodes))
    (hParams : ParamsSpec lim P pParams) (hPrep : PrepSpec lim P pPrep)
    (hGrid : GridSpec lim P pGrid T r) (hTwice : TwiceSpec lim P pTwice)
    (hZero : ZeroThreeSpec lim P pZero) (hNodes : NodesSpec lim P pNodes T r) :
    CoreSpec lim P p T r := by
  intro d n U x b X μ hlen hXU hseg hxb hn hU hok
  have hx : ∀ i, |vecOf n X i| ≤ (U : ℤ) := fun i => by
    have hi : i.val < X.length := by rw [hlen]; exact i.isLt
    simp only [vecOf, List.getD_eq_getElem _ _ hi]
    exact hXU.getElem hi
  exact ⟨_, hP, coreBody_ends hParams hPrep hGrid hTwice hZero hNodes
    (a := ⟨b + 3, n, Lam (2 * U), mPar n (2 * U)⟩) ⟨hn, by omega, rfl, rfl, rfl⟩ rfl hlen hx
    (fun y hy => (hXU y hy).trans (by push_cast; omega)) hseg hxb hok⟩

end Light.Sec3.ChanHe
end
