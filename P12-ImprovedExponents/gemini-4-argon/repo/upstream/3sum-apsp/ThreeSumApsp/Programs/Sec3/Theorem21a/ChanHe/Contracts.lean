module

public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.FromNumbers
public import ThreeSumApsp.Spec.Sec3.Problems
public import ThreeSumApsp.Lang.Tasks
public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Definitions
public import ThreeSumApsp.Util.Flag

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset


/-- The `len` cells from `a` hold the elements of the set `S`, each once, in some order. -/
def SetAt (μ : ℕ → ℤ) (a len : ℕ) (S : Finset ℤ) : Prop :=
  ∃ L : List ℤ, L.length = len ∧ Seg μ a L ∧ L.Nodup ∧ L.toFinset = S

/-- The `cap` cells from `cnt` hold zeros. -/
def ZeroAt (μ : ℕ → ℤ) (cnt cap : ℕ) : Prop := ∀ r < cap, μ (cnt + r) = 0

/-! ## Time functions and needs -/

/-- The time of a remainder of a number of absolute value at most `V`. -/
def tEmod (V : ℕ) : ℕ := 60 * (Nat.log 2 (V + 1) + 1) + 40
/-- What a remainder needs: words for doubled multiples of the modulus, and a cell for each of
them. -/
def emodNeed (V M : ℕ) : Need := ⟨4 * V + 4 * M + 16, Nat.log 2 (V + 1) + 2, 0⟩

/-- The remainders of `len` numbers. -/
def tResid (len V : ℕ) : ℕ := len * (tEmod V + 30) + 20
/-- One pass over `len` remainders that changes their counts. -/
def tTally (len : ℕ) : ℕ := 30 * len + 20
/-- The colliding pairs of a set of `len` numbers: remainders, counting, a pass that adds up, and
removing the counts. -/
def tColl (len V : ℕ) : ℕ := tResid len V + 2 * tTally len + 30 * len + 60
/-- The heavy elements of a set of `len` numbers: remainders, counting, a pass that copies, and
removing the counts. -/
def tHeavy (len V : ℕ) : ℕ := tResid len V + 2 * tTally len + 40 * len + 60
/-- One search: every candidate prime costs three collision counts. -/
def tSearch (np l₁ l₂ l₃ V : ℕ) : ℕ := np * (tColl l₁ V + tColl l₂ V + tColl l₃ V + 120) + 40
/-- The modulus of a node: two searches, and the collision counts modulo the first prime. -/
def tModulus (np l₁ l₂ l₃ V : ℕ) : ℕ := 2 * tSearch np l₁ l₂ l₃ V + tColl l₁ V + tColl l₂ V +
  tColl l₃ V + 160
/-- The array of a node: the padding pattern, and for each of the three sets remainders, counting, a
pass that writes, and removing the counts. -/
def tNodeArray (m l₁ l₂ l₃ V : ℕ) : ℕ :=
  80 * (2 * m ^ 2) + (tResid l₁ V + tResid l₂ V + tResid l₃ V) +
    2 * (tTally l₁ + tTally l₂ + tTally l₃) + 60 * (l₁ + l₂ + l₃) + 200

/-- The words that the routines below the tree need, for sets of at most `n` numbers of absolute
value at most `V` and moduli up to `M`: products of a collision count and a number of primes,
thresholds of the searches, entries and indices of the arrays. -/
def wordNeed (n V M : ℕ) : ℕ := 64 * (n + 1) ^ 2 * (M + 1) * (V + 1)

/-- The needs.  A caller's need covers its callees': the remainders of a set take `len` cells, a
long division `log₂ (V + 1) + 2`; the depth is the number of levels of calls below the routine. -/
def residNeed (len V M : ℕ) : Need := ⟨wordNeed len V M, Nat.log 2 (V + 1) + 2, 1⟩
/-- The need of coll and of heavy. -/
def collNeed (len V M : ℕ) : Need := ⟨wordNeed len V M, len + Nat.log 2 (V + 1) + 2, 2⟩
/-- The need of modulus; the moduli are at most `m²`. -/
def modulusNeed (n V m : ℕ) : Need := ⟨wordNeed n V (m * m), n + Nat.log 2 (V + 1) + 2, 4⟩
/-- The need of nodeArray. -/
def nodeArrayNeed (n V m : ℕ) : Need := ⟨wordNeed n V (m * m), n + Nat.log 2 (V + 1) + 2, 2⟩

/-! ## The generic library

The logarithms, the remainder, the sieve and sorting of the general library meet these
specifications (`EmodSpec` is below). -/

/-- The time of log2. -/
def tLog2 (x : ℕ) : ℕ := 30 * (Nat.log 2 x + 1) + 20

/-- log2(x) returns `⌊log₂ x⌋` (0 for `x = 0`); it touches no cell. -/
def Log2Spec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d x : ℕ) (μ : ℕ → ℤ), (4 * x + 4 : ℤ) ≤ lim.word →
    Meets lim P p d [x] μ (tLog2 x) fun r μ' => r = (Nat.log 2 x : ℤ) ∧ μ' = μ

/-- clog2(x) returns `⌈log₂ x⌉` (0 for `x ≤ 1`); it touches no cell. -/
def Clog2Spec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d x : ℕ) (μ : ℕ → ℤ), (4 * x + 4 : ℤ) ≤ lim.word →
    Meets lim P p d [x] μ (tLog2 x + 30) fun r μ' => r = (Nat.clog 2 x : ℤ) ∧ μ' = μ

/-- The time of the sieve. -/
def tPrimes (m : ℕ) : ℕ := 60 * m * (Nat.log 2 m + 2) + 60
/-- The need of the sieve: a table of `m + 1` cells. -/
def primesNeed (m : ℕ) : Need := ⟨4 * m + 16, m + 1, 0⟩

/-- primes(m, out, fr) writes the primes up to `m` in ascending order to `out` (room for `m` cells)
and returns their number. -/
def PrimesSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr m out : ℕ) (μ : ℕ → ℤ), out + m ≤ fr → (primesNeed m).Ok lim fr d →
    Meets lim P p d [m, out, fr] μ (tPrimes m) fun r μ' =>
      r = (#(Nat.primesLE m) : ℤ) ∧
        Seg μ' out (((Nat.primesLE m).sort (· ≤ ·)).map fun q : ℕ => (q : ℤ)) ∧
        KeptBut μ μ' fr out m

/-- The time of sorting. -/
def tSort (n : ℕ) : ℕ := 80 * n * (Nat.log 2 n + 2) + 60
/-- The need of sorting: `n` cells, and a level of calls for each halving. -/
def sortNeed (n V : ℕ) : Need := ⟨2 * V + 4 * n + 16, n, Nat.log 2 n + 2⟩

/-- sort(n, a, fr) sorts the `n` cells from `a` in place, in ascending order. -/
def SortSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr a V : ℕ) (L : List ℤ) (μ : ℕ → ℤ), Seg μ a L → AbsLe L V → a + L.length ≤ fr →
    (sortNeed L.length V).Ok lim fr d →
    Meets lim P p d [L.length, a, fr] μ (tSort L.length) fun _ μ' =>
      (∃ L' : List ℤ, Seg μ' a L' ∧ L'.Perm L ∧ L'.Pairwise (· ≤ ·)) ∧ KeptBut μ μ' fr a L.length

/-! ## Remainders, counts, collisions, heavy elements -/

/-- emod(x, M, fr) returns `x % M`, for `M ≥ 1`. -/
def EmodSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr V M : ℕ) (x : ℤ) (μ : ℕ → ℤ), 1 ≤ M → |x| ≤ (V : ℤ) → (emodNeed V M).Ok lim fr d →
    Meets lim P p d [x, M, fr] μ (tEmod V) fun r μ' => r = x % (M : ℤ) ∧ Kept μ μ' fr

/-- resid(len, s, sg, M, key, fr) writes the remainders of `sg · x` modulo `M`, for the `len`
numbers `x` from `s`, to `key`.  `sg` is 1 or -1. -/
def ResidSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr V M s key : ℕ) (sg : ℤ) (L : List ℤ) (μ : ℕ → ℤ), 1 ≤ M → (sg = 1 ∨ sg = -1) → AbsLe L V →
    Seg μ s L →
    s + L.length ≤ fr → key + L.length ≤ fr → Apart s L.length key L.length →
    (residNeed L.length V M).Ok lim fr d →
    Meets lim P p d [L.length, s, sg, M, key, fr] μ (tResid L.length V) fun _ μ' =>
      Seg μ' key (L.map fun x => (sg * x) % (M : ℤ)) ∧ KeptBut μ μ' fr key L.length

/-- tally(len, key, cnt, δ) adds `δ` to the cell `cnt + k` for each of the `len` numbers `k` from
`key`. -/
def TallySpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d key cnt cap : ℕ) (δ : ℤ) (K : List ℕ) (μ : ℕ → ℤ), (∀ k ∈ K, k < cap) → (δ = 1 ∨ δ = -1) →
    Seg μ key (K.map fun k : ℕ => (k : ℤ)) → Apart key K.length cnt cap →
    (∀ r < cap, |μ (cnt + r)| ≤ (K.length : ℤ)) →
    key + K.length ≤ lim.space → cnt + cap ≤ lim.space → (lim.space : ℤ) ≤ lim.word →
    (2 * K.length + 2 : ℤ) ≤ lim.word →
    Meets lim P p d [K.length, key, cnt, δ] μ (tTally K.length) fun _ μ' =>
      (∀ r < cap, μ' (cnt + r) = μ (cnt + r) + δ * (K.count r : ℤ)) ∧ SameOutside μ μ' cnt cap

/-- A set of `len` numbers of absolute value at most `V` at `s`, and a table of zeros at `cnt` with
a cell for each remainder modulo `M`; both below the free pointer, and apart. -/
structure BucketMem (μ : ℕ → ℤ) (fr V M s len cnt cap : ℕ) (S : Finset ℤ) : Prop where
  modulus_pos : 1 ≤ M
  modulus_le : M ≤ cap
  bdd : Bdd V S
  set : SetAt μ s len S
  zero : ZeroAt μ cnt cap
  belowSet : s + len ≤ fr
  belowTable : cnt + cap ≤ fr
  apart : Apart s len cnt cap

/-- coll(len, s, M, cnt, fr) returns the number of colliding ordered pairs of the set at `s` modulo
`M`. -/
def CollSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr V M s len cnt cap : ℕ) (S : Finset ℤ) (μ : ℕ → ℤ), BucketMem μ fr V M s len cnt cap S →
    (collNeed len V M).Ok lim fr d →
    Meets lim P p d [len, s, M, cnt, fr] μ (tColl len V) fun r μ' =>
      r = (coll S M : ℤ) ∧ Kept μ μ' fr

/-- Where the output of heavy stands: below the free pointer, apart from the set and the table. -/
structure HeavyOut (fr s cnt cap out len : ℕ) : Prop where
  below : out + len ≤ fr
  apartSet : Apart s len out len
  apartTable : Apart out len cnt cap

/-- heavy(len, s, M, out, cnt, fr) writes the heavy elements of the set at `s` modulo `M` to `out`
(room for `len` cells) and returns their number. -/
def HeavySpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr V M s len out cnt cap : ℕ) (S : Finset ℤ) (μ : ℕ → ℤ),
    BucketMem μ fr V M s len cnt cap S → HeavyOut fr s cnt cap out len →
    (collNeed len V M).Ok lim fr d →
    Meets lim P p d [len, s, M, out, cnt, fr] μ (tHeavy len V) fun r μ' =>
      r = (#(heavy S M) : ℤ) ∧ SetAt μ' out #(heavy S M) (heavy S M) ∧ KeptBut μ μ' fr out len

/-! ## The modulus of a node -/

/-- The primes up to `m`, in ascending order, lie in the `np` cells from `pr`. -/
def PrimesAt (μ : ℕ → ℤ) (pr np m : ℕ) : Prop :=
  np = #(Nat.primesLE m) ∧ Seg μ pr (((Nat.primesLE m).sort (· ≤ ·)).map fun q : ℕ => (q : ℤ))

/-- A set in the memory: the address and the length of its list, and the set. -/
structure Slot : Type where
  (addr len : ℕ)
  set : Finset ℤ

/-- What the routines below the recursion tree share: the free pointer `fr`; the bounds `n` on the
sizes of the sets and `V` on their elements; the bound `m` on the primes, their number `np` and the
address `pr` of their list; the address `cnt` of the count table of `m²` cells. -/
structure Env : Type where
  (fr n V m np pr cnt : ℕ)

/-- The primes up to `m` and the count table are in the memory, below the free pointer and apart. -/
structure Env.Ok (μ : ℕ → ℤ) (e : Env) : Prop where
  primes : PrimesAt μ e.pr e.np e.m
  zero : ZeroAt μ e.cnt (e.m * e.m)
  belowPr : e.pr + e.np ≤ e.fr
  belowCnt : e.cnt + e.m * e.m ≤ e.fr
  apartPr : Apart e.pr e.np e.cnt (e.m * e.m)

/-- A set of at most `n` numbers of absolute value at most `V` is in the memory, below the free
pointer and apart from the count table. -/
structure Slot.Ok (μ : ℕ → ℤ) (e : Env) (X : Slot) : Prop where
  set : SetAt μ X.addr X.len X.set
  le : X.len ≤ e.n
  bdd : Bdd e.V X.set
  below : X.addr + X.len ≤ e.fr
  apart : Apart X.addr X.len e.cnt (e.m * e.m)

/-- A node of the recursion tree in the memory: its three sets, and what the routines share. -/
structure NodeArgs : Type extends Env where
  (X₁ X₂ X₃ : Slot)

/-- The addresses and lengths of the three sets, as the routines are given them. -/
@[simp] abbrev NodeArgs.sets (a : NodeArgs) : List ℤ :=
  [a.X₁.addr, a.X₁.len, a.X₂.addr, a.X₂.len, a.X₃.addr, a.X₃.len]

/-- The three sets of a node, the primes and the count table are in the memory. -/
structure NodeMem (μ : ℕ → ℤ) (a : NodeArgs) : Prop where
  envOk : a.toEnv.Ok μ
  set₁ : a.X₁.Ok μ a.toEnv
  set₂ : a.X₂.Ok μ a.toEnv
  set₃ : a.X₃.Ok μ a.toEnv

/-- The arguments of search: a node, the factor `mult` of the moduli, and a bound for each set. -/
structure SearchArgs : Type extends NodeArgs where
  (mult b₁ b₂ b₃ : ℕ)

/-- The values of the arguments of search. -/
@[simp] abbrev SearchArgs.vals (x : SearchArgs) : List ℤ :=
  (x.mult : ℤ) :: x.sets ++ [(x.b₁ : ℤ), x.b₂, x.b₃, x.np, x.pr, x.cnt, x.fr]

/-- A candidate `q` is good: each of the three sets has at most `bᵢ / np` colliding pairs modulo
`mult · q`. -/
def SearchArgs.Good (x : SearchArgs) (q : ℕ) : Prop :=
  coll x.X₁.set (x.mult * q) * x.np ≤ x.b₁ ∧ coll x.X₂.set (x.mult * q) * x.np ≤ x.b₂ ∧
    coll x.X₃.set (x.mult * q) * x.np ≤ x.b₃

instance (x : SearchArgs) : DecidablePred x.Good := fun q => by
  unfold SearchArgs.Good
  infer_instance

/-- The need of search. -/
def searchNeed (n V m : ℕ) : Need := ⟨wordNeed n V (m * m), n + Nat.log 2 (V + 1) + 2, 3⟩

/-- search(mult, s₁, l₁, s₂, l₂, s₃, l₃, b₁, b₂, b₃, np, pr, cnt, fr) returns the least good prime
up to `m`, and 1 if there is none. -/
def SearchSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (x : SearchArgs) (μ : ℕ → ℤ), NodeMem μ x.toNodeArgs → 1 ≤ x.mult → x.mult ≤ x.m →
    ∀ d, (searchNeed x.n x.V x.m).Ok lim x.fr d →
    Meets lim P p d x.vals μ (tSearch x.np x.X₁.len x.X₂.len x.X₃.len x.V) fun r μ' =>
      r = (pick {q ∈ Nat.primesLE x.m | x.Good q} : ℤ) ∧ Kept μ μ' x.fr

/-- The values of the arguments of modulus. -/
@[simp] abbrev NodeArgs.modulusVals (a : NodeArgs) (Λ : ℕ) : List ℤ :=
  a.sets ++ [(Λ : ℤ), a.np, a.pr, a.cnt, a.fr]

/-- modulus(s₁, l₁, s₂, l₂, s₃, l₃, Λ, np, pr, cnt, fr) returns the modulus of the node. -/
def ModulusSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (a : NodeArgs) (Λ : ℕ) (μ : ℕ → ℤ), NodeMem μ a → Λ ≤ a.V + 2 →
    ∀ d, (modulusNeed a.n a.V a.m).Ok lim a.fr d →
    Meets lim P p d (a.modulusVals Λ) μ
      (tModulus a.np a.X₁.len a.X₂.len a.X₃.len a.V) fun r μ' =>
      r = (modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set : ℤ) ∧ Kept μ μ' a.fr

/-! ## The array of a node -/

/-- Where the array of a node is written: `8 m²` cells from `y`, below the free pointer and apart
from the three sets and the count table. -/
structure NodeArrayOut (a : NodeArgs) (y : ℕ) : Prop where
  below : y + 8 * a.m ^ 2 ≤ a.fr
  apart₁ : Apart y (8 * a.m ^ 2) a.X₁.addr a.X₁.len
  apart₂ : Apart y (8 * a.m ^ 2) a.X₂.addr a.X₂.len
  apart₃ : Apart y (8 * a.m ^ 2) a.X₃.addr a.X₃.len
  apartCnt : Apart y (8 * a.m ^ 2) a.cnt (a.m * a.m)

/-- nodeArray(M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, y, cnt, fr) writes the first `8 m²` cells of the
one-array instance of the node to `y`. -/
def NodeArraySpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (a : NodeArgs) (M y : ℕ) (μ : ℕ → ℤ), NodeMem μ a → 1 ≤ M → M ≤ a.m * a.m →
    NodeArrayOut a y →
    ∀ d, (nodeArrayNeed a.n a.V a.m).Ok lim a.fr d →
    Meets lim P p d ((M : ℤ) :: a.sets ++ [(a.V : ℤ), a.m, y, a.cnt, a.fr]) μ
      (tNodeArray a.m a.X₁.len a.X₂.len a.X₃.len a.V) fun _ μ' =>
      (∀ u < 8 * a.m ^ 2,
        μ' (y + u) = Node.oneArray ⟨a.X₁.set, a.X₂.set, a.X₃.set, M⟩ a.V u) ∧
        KeptBut μ μ' a.fr y (8 * a.m ^ 2)

/-! ## The recursion tree -/

/-- The number of calls of the recursive procedure: one for the triple, and those of the three
children if the triple is a node. -/
def treeCalls (Q : Finset ℕ) (Λ : ℕ) : ℕ → Finset ℤ → Finset ℤ → Finset ℤ → ℕ
  | 0, _, _, _ => 1
  | f + 1, S₁, S₂, S₃ =>
    if S₁ = ∅ ∨ S₂ = ∅ ∨ S₃ = ∅ then 1 else
      1 + (treeCalls Q Λ f (heavy S₁ (modulus Q Λ S₁ S₂ S₃)) S₂ S₃ +
        treeCalls Q Λ f S₁ (heavy S₂ (modulus Q Λ S₁ S₂ S₃)) S₃ +
        treeCalls Q Λ f S₁ S₂ (heavy S₃ (modulus Q Λ S₁ S₂ S₃)))

/-- The cost of one node, when a Convolution-3SUM solver takes `T N B` steps: the modulus, the
array, the call, and the three sets of heavy elements. -/
def tNode (T : ℕ → ℕ → ℕ) (n V m np : ℕ) : ℕ :=
  tModulus np n n n V + tNodeArray m n n n V + T (8 * m ^ 2) (60 * V + 40) + 3 * tHeavy n V + 300

/-- The time of the recursive procedure. -/
def tNodes (T : ℕ → ℕ → ℕ) (n V m np calls : ℕ) : ℕ := calls * (tNode T n V m np + 60)

/-- What the recursive procedure needs with `f` levels to go: a set of heavy elements for each
level, one array, and what the solver needs. -/
def nodesNeed (r : ℕ → ℕ → Need) (n V m f : ℕ) : Need :=
  ⟨max (modulusNeed n V m).word (r (8 * m ^ 2) (60 * V + 40)).word,
    f * n + 8 * m ^ 2 + max (modulusNeed n V m).cells (r (8 * m ^ 2) (60 * V + 40)).cells,
    f + 1 + max (modulusNeed n V m).depth (r (8 * m ^ 2) (60 * V + 40)).depth⟩

/-- The block of parameters that the recursive procedure gets by its address `cx`: `V`, `m`, `Λ`,
`np`, `pr`, `cnt`. -/
def CtxAt (μ : ℕ → ℤ) (cx V m Λ np pr cnt : ℕ) : Prop := Seg μ cx [(V : ℤ), m, Λ, np, pr, cnt]

/-- What the recursive procedure assumes with `f` levels to go: the memory of a node, the block of
parameters at `cx`, below the free pointer and apart from the count table, and the limits. -/
structure NodesPre (lim : Limits) (r : ℕ → ℕ → Need) (μ : ℕ → ℤ) (a : NodeArgs) (Λ cx f d : ℕ) :
    Prop where
  mem : NodeMem μ a
  ctx : CtxAt μ cx a.V a.m Λ a.np a.pr a.cnt
  belowCtx : cx + 6 ≤ a.fr
  apartCtx : Apart cx 6 a.cnt (a.m * a.m)
  V_pos : 1 ≤ a.V
  m_pos : 1 ≤ a.m
  lam : Λ = Lam a.V
  primes : (Nat.primesLE a.m).Nonempty
  ok : (nodesNeed r a.n a.V a.m f).Ok lim a.fr d

/-- The number of calls of the procedure for the tree with `f` levels below a node. -/
abbrev NodeArgs.calls (a : NodeArgs) (Λ f : ℕ) : ℕ :=
  treeCalls (Nat.primesLE a.m) Λ f a.X₁.set a.X₂.set a.X₃.set

/-- Some node of the tree of a three-set input gives a yes-instance. -/
def TreeYes (m Λ f V : ℕ) (S₁ S₂ S₃ : Finset ℤ) : Prop :=
  ∃ ν ∈ nodes (Nat.primesLE m) Λ f S₁ S₂ S₃, ConvOne (8 * m ^ 2) (ν.oneArray V)

/-- The one-array instance of some node of the tree with `f` levels below a node in the memory is a
yes-instance. -/
abbrev NodeArgs.Yes (a : NodeArgs) (Λ f : ℕ) : Prop :=
  TreeYes a.m Λ f a.V a.X₁.set a.X₂.set a.X₃.set

/-- The specification of nodes for trees with `f` levels: see `NodesSpec`. -/
def NodesSpecAt (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) (f : ℕ) :
    Prop :=
  ∀ (a : NodeArgs) (Λ cx : ℕ) (μ : ℕ → ℤ) (d : ℕ), NodesPre lim r μ a Λ cx f d →
    Meets lim P p d ((f : ℤ) :: a.sets ++ [(cx : ℤ), a.fr]) μ
      (tNodes T a.n a.V a.m a.np (a.calls Λ f)) fun res μ' =>
        res = ThreeSumApsp.flag (a.Yes Λ f) ∧ Kept μ μ' a.fr

/-- nodes(f, s₁, l₁, s₂, l₂, s₃, l₃, cx, fr) returns 1 if the one-array instance of some node of the
tree with `f` levels is a yes-instance at length `8 m²`, and 0 if not.  `T` and `r` are the time and
the need of the Convolution-3SUM solver that it calls. -/
def NodesSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ f, NodesSpecAt lim P p T r f

/-! ## The front: distinct values, multiplicities, binary digits, the splittings -/

/-- The time of distinct. -/
def tDistinct (n : ℕ) : ℕ := 60 * n + 40
/-- The time of twice. -/
def tTwice (n : ℕ) : ℕ := 60 * n + 40
/-- The time of zeroThree. -/
def tZeroThree (n : ℕ) : ℕ := 40 * n + 40
/-- The time of bits. -/
def tBits (len Λ : ℕ) : ℕ := len * (60 * Λ + 40) + 40 * Λ + 60
/-- The time of pick. -/
def tPick (len : ℕ) : ℕ := 90 * len + 40

/-- What distinct assumes: the sorted list stands at `a`; the three regions lie in the memory and do
not meet; addresses and counts fit in a word. -/
structure Distinct.Ctx (lim : Limits) (μ : ℕ → ℤ) (a val mul : ℕ) (L : List ℤ) : Prop where
  sorted : L.Pairwise (· ≤ ·)
  seg : Seg μ a L
  apartVal : Apart a L.length val L.length
  apartMul : Apart a L.length mul L.length
  apart : Apart val L.length mul L.length
  spaceSrc : a + L.length ≤ lim.space
  spaceVal : val + L.length ≤ lim.space
  spaceMul : mul + L.length ≤ lim.space
  space_le : (lim.space : ℤ) ≤ lim.word
  word : (2 * L.length + 8 : ℤ) ≤ lim.word

/-- distinct(n, a, val, mul): the `n` cells from `a` hold a sorted list.  Writes its distinct values
to `val` and how often each occurs to `mul` (room for `n` cells each), and returns the number of
distinct values. -/
def DistinctSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d a val mul : ℕ) (L : List ℤ) (μ : ℕ → ℤ), Distinct.Ctx lim μ a val mul L →
    Meets lim P p d [L.length, a, val, mul] μ (tDistinct L.length) fun r μ' =>
      (∃ D : List ℤ, r = (D.length : ℤ) ∧ D.Nodup ∧ D.toFinset = L.toFinset ∧ Seg μ' val D ∧
        Seg μ' mul (D.map fun x => (L.count x : ℤ))) ∧
      SameOutside2 μ μ' val L.length mul L.length

/-- The doubles of the values that are not 0 and occur at least twice. -/
def twiceList (D C : List ℤ) : List ℤ :=
  ((D.zip C).filter fun q => decide (q.1 ≠ 0 ∧ 2 ≤ q.2)).map fun q => 2 * q.1

/-- What twice assumes: the values, of absolute value at most `V`, stand at `val` and as many
multiplicities at `mul`; the three regions lie in the memory, and the output meets neither of the
others; addresses and doubled values fit in a word. -/
structure Twice.Ctx (lim : Limits) (μ : ℕ → ℤ) (val mul out V : ℕ) (D C : List ℤ) : Prop where
  len : C.length = D.length
  bounded : AbsLe D V
  segVal : Seg μ val D
  segMul : Seg μ mul C
  apartVal : Apart val D.length out D.length
  apartMul : Apart mul D.length out D.length
  spaceVal : val + D.length ≤ lim.space
  spaceMul : mul + D.length ≤ lim.space
  spaceOut : out + D.length ≤ lim.space
  space_le : (lim.space : ℤ) ≤ lim.word
  word : (2 * V + 2 * D.length + 8 : ℤ) ≤ lim.word

/-- twice(nd, val, mul, out) writes the doubles of the values that are not 0 and occur at least
twice to `out` (room for `nd` cells), and returns their number. -/
def TwiceSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d val mul out V : ℕ) (D C : List ℤ) (μ : ℕ → ℤ), Twice.Ctx lim μ val mul out V D C →
    Meets lim P p d [D.length, val, mul, out] μ (tTwice D.length) fun r μ' =>
      r = ((twiceList D C).length : ℤ) ∧ Seg μ' out (twiceList D C) ∧ SameOutside μ μ' out D.length

/-- zeroThree(nd, val, mul) returns 1 if the value 0 occurs at least three times, and 0 if not; it
writes no cell. -/
def ZeroThreeSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d val mul : ℕ) (D C : List ℤ) (μ : ℕ → ℤ), C.length = D.length → Seg μ val D → Seg μ mul C →
    val + D.length ≤ lim.space → mul + D.length ≤ lim.space → (lim.space : ℤ) ≤ lim.word →
    (2 * D.length + 8 : ℤ) ≤ lim.word →
    Meets lim P p d [D.length, val, mul] μ (tZeroThree D.length) fun r μ' =>
      r = ThreeSumApsp.flag (∃ q ∈ D.zip C, q.1 = 0 ∧ 3 ≤ q.2) ∧ μ' = μ

/-- The table of the binary digits of the labels: digit `β` of the label of the `i`-th element in
cell `i Λ + β`. -/
def bitTable (V Λ : ℕ) (L : List ℤ) : List ℤ :=
  L.flatMap fun x => (List.range Λ).map fun β => if (lab V x).testBit β then 1 else 0

/-- What bits assumes: the list of numbers of absolute value at most `V` stands at `s`; the labels
have `Λ` binary digits, and `2^Λ` is not much larger than they are; the list and the table lie in
the memory and do not meet; addresses and doubled labels fit in a word. -/
structure Bits.Ctx (lim : Limits) (μ : ℕ → ℤ) (s V Λ bt : ℕ) (L : List ℤ) : Prop where
  bounded : AbsLe L V
  lt_pow : 2 * V < 2 ^ Λ
  pow_le : 2 ^ Λ ≤ 4 * V + 4
  seg : Seg μ s L
  apart : Apart s L.length bt (L.length * Λ)
  spaceSrc : s + L.length ≤ lim.space
  spaceTable : bt + L.length * Λ ≤ lim.space
  space_le : (lim.space : ℤ) ≤ lim.word
  word : (8 * V + 16 : ℤ) ≤ lim.word

/-- bits(len, s, V, Λ, bt, fr) writes the table of the binary digits of the labels `x + V` of the
`len` numbers from `s` to `bt` (`len Λ` cells).  It does not use the free pointer. -/
def BitsSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr s bt V Λ : ℕ) (L : List ℤ) (μ : ℕ → ℤ), Bits.Ctx lim μ s V Λ bt L →
    Meets lim P p d [L.length, s, V, Λ, bt, fr] μ (tBits L.length Λ) fun _ μ' =>
      Seg μ' bt (bitTable V Λ L) ∧ SameOutside μ μ' bt (L.length * Λ)

/-- The elements whose digit `β` is `x` and, unless `two = 0`, whose digit `β'` is `x'`. -/
def pickList (Λ β β' : ℕ) (x x' two : ℤ) (L BT : List ℤ) : List ℤ :=
  ((List.range L.length).filter fun i =>
    decide (BT.getD (i * Λ + β) 0 = x ∧ (two = 0 ∨ BT.getD (i * Λ + β') 0 = x'))).map
    fun i => L.getD i 0

/-- What pick assumes: the list stands at `s` and the table of its digits at `bt`, `Λ` cells for
each element; the two positions are below `Λ`; the three regions lie in the memory, and the output
meets neither of the others; addresses fit in a word. -/
structure Pick.Ctx (lim : Limits) (μ : ℕ → ℤ) (s bt out Λ β β' : ℕ) (L BT : List ℤ) : Prop where
  lenTable : BT.length = L.length * Λ
  posA : β < Λ
  posB : β' < Λ
  segSrc : Seg μ s L
  segTable : Seg μ bt BT
  apartSrc : Apart s L.length out L.length
  apartTable : Apart bt (L.length * Λ) out L.length
  spaceSrc : s + L.length ≤ lim.space
  spaceTable : bt + L.length * Λ ≤ lim.space
  spaceOut : out + L.length ≤ lim.space
  space_le : (lim.space : ℤ) ≤ lim.word
  word : (8 : ℤ) ≤ lim.word

/-- pick(len, s, bt, Λ, β, x, β', x', two, out) writes the elements selected by one binary digit
(`two = 0`) or by two to `out` (room for `len` cells) and returns their number. -/
def PickSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d s bt out Λ β β' : ℕ) (x x' two : ℤ) (L BT : List ℤ) (μ : ℕ → ℤ),
    Pick.Ctx lim μ s bt out Λ β β' L BT →
    Meets lim P p d [L.length, s, bt, Λ, β, x, β', x', two, out] μ (tPick L.length) fun r μ' =>
      r = ((pickList Λ β β' x x' two L BT).length : ℤ) ∧
        Seg μ' out (pickList Λ β β' x x' two L BT) ∧ SameOutside μ μ' out L.length



/-! ## The table of binary digits -/

/-- A binary digit of the label of a number, as an integer. -/
def bitOf (V β : ℕ) (x : ℤ) : ℤ := if (lab V x).testBit β then 1 else 0

/-- The `Λ` lowest binary digits of `z`. -/
def bitRow (Λ z : ℕ) : List ℤ := (List.range Λ).map fun β => if z.testBit β then 1 else 0

@[simp] theorem length_bitRow (Λ z : ℕ) : (bitRow Λ z).length = Λ := by simp [bitRow]

/-- The table begins with the digits of the first label. -/
theorem bitTable_cons (V Λ : ℕ) (x : ℤ) (L : List ℤ) :
    bitTable V Λ (x :: L) = bitRow Λ (lab V x) ++ bitTable V Λ L := by
  simp [bitTable, bitRow]

/-- The table ends with the digits of the last label. -/
theorem bitTable_append (V Λ : ℕ) (L : List ℤ) (x : ℤ) :
    bitTable V Λ (L ++ [x]) = bitTable V Λ L ++ bitRow Λ (lab V x) := by
  simp [bitTable, bitRow, List.flatMap_append]

/-- The table has `Λ` cells for each number. -/
theorem length_bitTable (V Λ : ℕ) (L : List ℤ) : (bitTable V Λ L).length = L.length * Λ := by
  induction L with
  | nil => simp [bitTable]
  | cons x L ih =>
    rw [bitTable_cons, List.length_append, ih, length_bitRow, List.length_cons, Nat.succ_mul,
      Nat.add_comm]

/-- Cell `i Λ + β` of the table holds digit `β` of the label of the `i`-th number. -/
theorem getD_bitTable (V Λ : ℕ) (L : List ℤ) {i β : ℕ} (hi : i < L.length) (hβ : β < Λ) :
    (bitTable V Λ L).getD (i * Λ + β) 0 = bitOf V β (L.getD i 0) := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x L ih =>
    rw [bitTable_cons]
    cases i with
    | zero =>
      rw [List.getD_append _ _ _ _ (by simpa using hβ)]
      simp [bitRow, List.getD_eq_getElem?_getD, hβ, bitOf]
    | succ i =>
      rw [List.getD_append_right _ _ _ _ (by rw [length_bitRow, Nat.succ_mul]; omega),
        length_bitRow, show (i + 1) * Λ + β - Λ = i * Λ + β by rw [Nat.succ_mul]; omega,
        ih (by simpa using hi), List.getD_cons_succ]

/-! ## Selecting by binary digits -/

/-- A filter written with positions. -/
theorem filter_by_position (L : List ℤ) (q : ℤ → Bool) :
    ((List.range L.length).filter fun i => q (L.getD i 0)).map (fun i => L.getD i 0) =
      L.filter q := by
  have hL : L = (List.range L.length).map fun i => L.getD i 0 := by
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  conv_rhs => rw [hL, List.filter_map]
  rfl

/-- The selection by cells of the table of digits is a filter of the list. -/
theorem pickList_eq (V Λ : ℕ) {β β' : ℕ} (hβ : β < Λ) (hβ' : β' < Λ) (b b' two : ℤ) (L : List ℤ) :
    pickList Λ β β' b b' two L (bitTable V Λ L) =
      L.filter fun x => decide (bitOf V β x = b ∧ (two = 0 ∨ bitOf V β' x = b')) := by
  rw [← filter_by_position L]
  unfold pickList
  congr 1
  refine List.filter_congr fun i hi => ?_
  have : i < L.length := List.mem_range.1 hi
  rw [getD_bitTable V Λ L this hβ, getD_bitTable V Λ L this hβ']

/-- The digit as an integer, against the digit as a Boolean. -/
theorem bitOf_eq_iff (V β : ℕ) (x : ℤ) (v : Bool) :
    bitOf V β x = (if v then 1 else 0) ↔ (lab V x).testBit β = v := by
  unfold bitOf
  cases v <;> cases (lab V x).testBit β <;> simp

/-- The selection by one digit gives the set `splitA`. -/
theorem pick_splitA (V Λ : ℕ) {β β' : ℕ} (hβ : β < Λ) (hβ' : β' < Λ) (v : Bool) (b' : ℤ)
    {L : List ℤ} (hL : L.Nodup) :
    (pickList Λ β β' (if v then 1 else 0) b' 0 L (bitTable V Λ L)).Nodup ∧
      (pickList Λ β β' (if v then 1 else 0) b' 0 L (bitTable V Λ L)).toFinset =
        splitA V β v L.toFinset := by
  rw [pickList_eq V Λ hβ hβ']
  refine ⟨hL.filter _, ?_⟩
  ext x
  simp [splitA, bitOf_eq_iff]

/-- The selection by two digits gives the set `splitB`. -/
theorem pick_splitB (V Λ : ℕ) {β β' : ℕ} (hβ : β < Λ) (hβ' : β' < Λ) (v w : Bool) {L : List ℤ}
    (hL : L.Nodup) :
    (pickList Λ β β' (if !v then 1 else 0) (if w then 1 else 0) 1 L (bitTable V Λ L)).Nodup ∧
      (pickList Λ β β' (if !v then 1 else 0) (if w then 1 else 0) 1 L (bitTable V Λ L)).toFinset =
        splitB V β β' v w L.toFinset := by
  rw [pickList_eq V Λ hβ hβ']
  refine ⟨hL.filter _, ?_⟩
  ext x
  simp only [List.toFinset_filter, Finset.mem_filter, List.mem_toFinset, decide_eq_true_eq,
    bitOf_eq_iff, splitB]
  simp

/-- A selection is not longer than the list. -/
theorem length_pickList_le (Λ β β' : ℕ) (b b' two : ℤ) (L BT : List ℤ) :
    (pickList Λ β β' b b' two L BT).length ≤ L.length := by
  unfold pickList
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

/-! ## The values of the input and how often they occur -/

/-- A list of `n` numbers is the list of the values of its vector. -/
theorem eq_ofFn_vecOf {n : ℕ} {X : List ℤ} (hX : X.length = n) : X = List.ofFn (vecOf n X) := by
  refine List.ext_getElem (by simp [hX]) fun i h1 h2 => ?_
  simp [vecOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-- The set of the members of a list of `n` numbers is the image of its vector. -/
theorem toFinset_eq_image {n : ℕ} {X : List ℤ} (hX : X.length = n) :
    X.toFinset = univ.image (vecOf n X) := by
  conv_lhs => rw [eq_ofFn_vecOf hX]
  ext a
  simp [List.mem_ofFn]

/-- How often a value occurs in a list of `n` numbers, in terms of its vector. -/
theorem count_eq_card {n : ℕ} {X : List ℤ} (hX : X.length = n) (a : ℤ) :
    X.count a = #{i : Fin n | vecOf n X i = a} := by
  conv_lhs => rw [eq_ofFn_vecOf hX]
  exact List.count_ofFn _ a

/-- `D` lists the distinct values of the input `X`, and `C` how often each occurs. -/
structure Values (n : ℕ) (X D C : List ℤ) : Prop where
  /-- No value stands twice. -/
  nodup : D.Nodup
  /-- The members of `D` are the values of the input. -/
  values : D.toFinset = univ.image (vecOf n X)
  /-- `C` says at how many positions each value stands. -/
  counts : C = D.map fun a => ((#{i : Fin n | vecOf n X i = a} : ℕ) : ℤ)

/-- The distinct values of a rearrangement of the input, with how often each occurs there. -/
theorem Values.of_perm {n : ℕ} {X Ls D : List ℤ} (hX : X.length = n) (hp : Ls.Perm X)
    (hD : D.Nodup) (hv : D.toFinset = Ls.toFinset) :
    Values n X D (D.map fun a => (Ls.count a : ℤ)) :=
  ⟨hD, by rw [hv, List.toFinset_eq_of_perm _ _ hp, toFinset_eq_image hX],
    List.map_congr_left fun a _ => by rw [hp.count_eq, count_eq_card hX]⟩

/-- There are at most `n` distinct values. -/
theorem Values.length_le {n : ℕ} {X D C : List ℤ} (h : Values n X D C) : D.length ≤ n := by
  rw [← List.toFinset_card_of_nodup h.nodup, h.values]
  exact card_image_univ_le _

/-- The pairs of a value and the number of its occurrences. -/
theorem Values.zip {n : ℕ} {X D C : List ℤ} (h : Values n X D C) :
    D.zip C = D.map fun a => (a, ((#{i : Fin n | vecOf n X i = a} : ℕ) : ℤ)) := by
  rw [h.counts]
  exact List.map_prod_left_eq_zip.symm

/-- The doubles of the repeated values. -/
theorem Values.twice {n : ℕ} {X D C : List ℤ} (h : Values n X D C) :
    (twiceList D C).Nodup ∧ (twiceList D C).toFinset = twiceSet (vecOf n X) := by
  have hfilter : twiceList D C =
      (D.filter fun a => decide (a ≠ 0 ∧ 2 ≤ #{i : Fin n | vecOf n X i = a})).map
        fun a => 2 * a := by
    unfold twiceList
    rw [h.zip, List.filter_map, List.map_map]
    congr 1
    refine List.filter_congr fun a _ => ?_
    simp only [Function.comp, decide_eq_decide]
    exact and_congr_right fun _ => by norm_cast
  rw [hfilter]
  refine ⟨(h.nodup.filter _).map fun a b hab => by simpa using hab, ?_⟩
  have hmem : ∀ a : ℤ, a ∈ D ↔ a ∈ univ.image (vecOf n X) := fun a => by
    rw [← h.values, List.mem_toFinset]
  ext y
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq, twiceSet,
    Finset.mem_image, Finset.mem_filter, hmem]

/-- There are at most as many doubles as values. -/
theorem length_twiceList_le (D C : List ℤ) : (twiceList D C).length ≤ D.length := by
  unfold twiceList
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp [List.length_zip])

/-- Whether 0 occurs at least three times. -/
theorem Values.zeroThree {n : ℕ} {X D C : List ℤ} (h : Values n X D C) :
    (∃ q ∈ D.zip C, q.1 = 0 ∧ 3 ≤ q.2) ↔ 3 ≤ #{i : Fin n | vecOf n X i = 0} := by
  rw [h.zip]
  constructor
  · rintro ⟨q, hq, h0, h3⟩
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hq
    simp only at h0 h3
    subst h0
    exact_mod_cast h3
  · intro h3
    have hne : (#{i : Fin n | vecOf n X i = 0}) ≠ 0 := by omega
    obtain ⟨i, hi⟩ := Finset.card_ne_zero.1 hne
    have : vecOf n X i = 0 := (Finset.mem_filter.1 hi).2
    have h0 : (0 : ℤ) ∈ D := by
      rw [← List.mem_toFinset, h.values]
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, this⟩
    exact ⟨_, List.mem_map.2 ⟨0, h0, rfl⟩, rfl, Int.ofNat_le.2 h3⟩


/-- What the routines that run through the splittings are given, besides what the routines below
the recursion tree share: the number `Λ` of binary digits, the number `nd` of the distinct values
`D`, their address `val`, the addresses `bt` of the table of digits, `A` of the cells for the three
sets and `cx` of the block of parameters. -/
structure FrontArgs : Type extends Env where
  (Λ nd val bt A cx : ℕ)
  D : List ℤ

/-- The values of the arguments of grid; row and round get them after their own. -/
@[simp] abbrev FrontArgs.vals (a : FrontArgs) (f : ℕ) : List ℤ :=
  [a.nd, a.val, a.bt, a.Λ, a.A, a.n, f, a.cx, a.fr]

/-- What the memory holds while the splittings are run through: the `nd` distinct values `D` at
`val`, the table of their binary digits at `bt`, the block of parameters at `cx`, the primes, the
count table, and `3n` cells from `A` for the three sets of a splitting.  Everything lies below the
free pointer, and the cells from `A` and the count table meet nothing else. -/
structure FrontMem (μ : ℕ → ℤ) (a : FrontArgs) : Prop where
  lenD : a.D.length = a.nd
  nd_le : a.nd ≤ a.n
  nodup : a.D.Nodup
  bdd : Bdd a.V a.D.toFinset
  segVal : Seg μ a.val a.D
  segBt : Seg μ a.bt (bitTable a.V a.Λ a.D)
  ctx : CtxAt μ a.cx a.V a.m a.Λ a.np a.pr a.cnt
  primes : PrimesAt μ a.pr a.np a.m
  zero : ZeroAt μ a.cnt (a.m * a.m)
  belowVal : a.val + a.nd ≤ a.fr
  belowBt : a.bt + a.nd * a.Λ ≤ a.fr
  belowCx : a.cx + 6 ≤ a.fr
  belowPr : a.pr + a.np ≤ a.fr
  belowCnt : a.cnt + a.m * a.m ≤ a.fr
  belowA : a.A + 3 * a.n ≤ a.fr
  apartVal : Apart a.A (3 * a.n) a.val a.nd
  apartBt : Apart a.A (3 * a.n) a.bt (a.nd * a.Λ)
  apartCx : Apart a.A (3 * a.n) a.cx 6
  apartPr : Apart a.A (3 * a.n) a.pr a.np
  apartCnt : Apart a.A (3 * a.n) a.cnt (a.m * a.m)
  cntVal : Apart a.val a.nd a.cnt (a.m * a.m)
  cntCx : Apart a.cx 6 a.cnt (a.m * a.m)
  cntPr : Apart a.pr a.np a.cnt (a.m * a.m)

/-- Some node of the tree of the splitting `(β, β', v)` of the set `S` gives a yes-instance. -/
def SplitYes (m Λ f V : ℕ) (S : Finset ℤ) (β β' : ℕ) (v : Bool) : Prop :=
  TreeYes m Λ f V (splitA V β v S) (splitB V β β' v false S) (splitB V β β' v true S)

/-- Some node of the tree of the splitting `(β, β', v)` of the distinct values gives a
yes-instance. -/
abbrev FrontArgs.Yes (a : FrontArgs) (f β β' : ℕ) (v : Bool) : Prop :=
  SplitYes a.m a.Λ f a.V a.D.toFinset β β' v

/-- The time of the recursive procedure for one three-set input, with `f` levels. -/
def tTree (T : ℕ → ℕ → ℕ) (n V m np f : ℕ) : ℕ := tNodes T n V m np (2 * 3 ^ f)

/-- The time of round. -/
def tRound (T : ℕ → ℕ → ℕ) (n V m np f : ℕ) : ℕ := 3 * tPick n + tTree T n V m np f + 120
/-- The time of row. -/
def tRow (T : ℕ → ℕ → ℕ) (n V m np f Λ : ℕ) : ℕ := Λ * (2 * tRound T n V m np f + 80) + 40
/-- The time of grid. -/
def tGrid (T : ℕ → ℕ → ℕ) (n V m np f Λ : ℕ) : ℕ := Λ * (tRow T n V m np f Λ + 40) + 40

/-- The need of round, row (`extra = 1`) and grid (`extra = 2`): that of the recursive procedure,
and the levels of calls above it. -/
def gridNeed (r : ℕ → ℕ → Need) (n V m f extra : ℕ) : Need :=
  ⟨(nodesNeed r n V m f).word + 4 * V + 16, (nodesNeed r n V m f).cells,
    (nodesNeed r n V m f).depth + 1 + extra⟩

/-- What round (`extra = 0`), row (`extra = 1`) and grid (`extra = 2`) assume besides the memory. -/
structure GridPre (lim : Limits) (r : ℕ → ℕ → Need) (a : FrontArgs) (f extra d : ℕ) : Prop where
  V_pos : 1 ≤ a.V
  m_pos : 1 ≤ a.m
  lam : a.Λ = Lam a.V
  primes : (Nat.primesLE a.m).Nonempty
  ok : (gridNeed r a.n a.V a.m f extra).Ok lim a.fr d

/-- round(β, β', b, nd, val, bt, Λ, A, n, f, cx, fr), with `b` = 1 for `v = true` and 0 for
`v = false`, returns 1 if the splitting gives a yes-instance, and 0 if not.  The three sets are
written to `A`, `A + n`, `A + 2n`. -/
def RoundSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ (a : FrontArgs) (f β β' : ℕ) (v : Bool) (μ : ℕ → ℤ), FrontMem μ a → β < a.Λ → β' < a.Λ →
    ∀ d, GridPre lim r a f 0 d →
    Meets lim P p d ((β : ℤ) :: β' :: (if v then 1 else 0) :: a.vals f) μ
      (tRound T a.n a.V a.m a.np f) fun res μ' =>
      res = flag (a.Yes f β β' v) ∧ KeptBut μ μ' a.fr a.A (3 * a.n)

/-- row(β, nd, val, bt, Λ, A, n, f, cx, fr) returns a number between 0 and `2Λ` that is positive
exactly if some splitting `(β, β', v)` gives a yes-instance. -/
def RowSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ (a : FrontArgs) (f β : ℕ) (μ : ℕ → ℤ), FrontMem μ a → β < a.Λ →
    ∀ d, GridPre lim r a f 1 d →
    Meets lim P p d ((β : ℤ) :: a.vals f) μ (tRow T a.n a.V a.m a.np f a.Λ) fun res μ' =>
      0 ≤ res ∧ res ≤ 2 * (a.Λ : ℤ) ∧ (0 < res ↔ ∃ β' < a.Λ, ∃ v, a.Yes f β β' v) ∧
        KeptBut μ μ' a.fr a.A (3 * a.n)

/-- grid(nd, val, bt, Λ, A, n, f, cx, fr) returns 1 if some splitting gives a yes-instance, and 0 if
not. -/
def GridSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ (a : FrontArgs) (f : ℕ) (μ : ℕ → ℤ), FrontMem μ a → ∀ d, GridPre lim r a f 2 d →
    Meets lim P p d (a.vals f) μ (tGrid T a.n a.V a.m a.np f a.Λ) fun res μ' =>
      res = flag (∃ β < a.Λ, ∃ β' < a.Λ, ∃ v, a.Yes f β β' v) ∧
        KeptBut μ μ' a.fr a.A (3 * a.n)



/-- An upper bound on the number of calls of the recursive procedure for one three-set input. -/
def callsB (n : ℕ) : ℕ := 2 * 3 ^ fuel n

/-- The cost of one call of the recursive procedure without the call of the solver. -/
def nodeOwn (n V m np : ℕ) : ℕ := tModulus np n n n V + tNodeArray m n n n V + 3 * tHeavy n V + 360

/-- The time of the recursive procedure, split into its own work and the calls of the solver. -/
theorem tNodes_eq (T : ℕ → ℕ → ℕ) (n V m np calls : ℕ) :
    tNodes T n V m np calls = calls * (nodeOwn n V m np + T (8 * m ^ 2) (60 * V + 40)) := by
  unfold tNodes tNode nodeOwn
  ring

/-- The time of params: four logarithms and a square root. -/
def tParams (n V : ℕ) : ℕ :=
  tLog2 (2 * V) + (18 * Nat.sqrt n + 12) + tLog2 (wPar n V + 1) + tLog2 n +
    (tLog2 (Nat.log 2 n + 2) + 30) + 160

/-- The time of prep: primes, count table, a copy, sorting, distinct values, binary digits. -/
def tPrep (n Λ m : ℕ) : ℕ :=
  tPrimes m + (13 * (m * m) + 6) + (16 * n + 6) + tSort n + tDistinct n + tBits n Λ + 240

/-- The time of params and prep. -/
def tSetup (n V : ℕ) : ℕ := tParams n V + tPrep n (Lam V) (mPar n V)

/-- The number of three-set inputs. -/
def inputsB (V : ℕ) : ℕ := 2 * Lam V ^ 2 + 2

/-- The number of calls of the solver, for the bound `V = 2U`. -/
def coreCalls (n V : ℕ) : ℕ := inputsB V * callsB n

/-- The host's own work, for the bound `V = 2U`. -/
def coreOwn (n V : ℕ) : ℕ :=
  tSetup n V + inputsB V * (callsB n * nodeOwn n V (mPar n V) #(Nat.primesLE (mPar n V)) + 3 *
    tPick n + 300) + tTwice n + tZeroThree n + 400

/-- The time of the host after the bound has been fixed. -/
def coreTime (T : ℕ → ℕ → ℕ) (n V : ℕ) : ℕ :=
  coreOwn n V + coreCalls n V * T (8 * mPar n V ^ 2) (60 * V + 40)

/-- **The time of the host.** -/
def chTime (κ : ℕ) (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ := 20 * κ + 40 + coreTime T n (2 * max U (n ^ κ))

/-- The cells of the host's own arrays: the block of parameters, the primes, the count table, the
sorted copy, values and multiplicities, the binary digits, three sets for a splitting, the doubles,
and one cell for the set {0}. -/
def coreCells (n V : ℕ) : ℕ := 6 + mPar n V + mPar n V * mPar n V + 7 * n + n * Lam V + 1

/-- The need of the host after the bound has been fixed. -/
def coreNeed (r : ℕ → ℕ → Need) (n V : ℕ) : Need :=
  ⟨(nodesNeed r n V (mPar n V) (fuel n)).word + 8 * (mPar n V + 1) ^ 2 + 8 * V + 4 * n + 64,
    coreCells n V + (nodesNeed r n V (mPar n V) (fuel n)).cells + mPar n V + n + Lam V + 8,
    (nodesNeed r n V (mPar n V) (fuel n)).depth + Nat.log 2 n + 6⟩

/-- **The need of the host.** -/
def chNeed (κ : ℕ) (r : ℕ → ℕ → Need) (n U : ℕ) : Need :=
  ⟨(coreNeed r n (2 * max U (n ^ κ))).word + 2 * n ^ κ + 2 * U,
    (coreNeed r n (2 * max U (n ^ κ))).cells,
    (coreNeed r n (2 * max U (n ^ κ))).depth + 1⟩




/-! ## The memory map -/

/-- The addresses of the arrays of core, for the base address `b`, `n` numbers, `Λ` binary digits
and primes up to `m`. -/
structure Map : Type where
  /-- The base address. -/
  b : ℕ
  /-- The number of integers of the input. -/
  n : ℕ
  /-- The number of binary digits of a label. -/
  Λ : ℕ
  /-- The bound on the primes. -/
  m : ℕ

namespace Map
variable (a : Map)
/-- The block of parameters of the recursive procedure, 6 cells. -/
def cx : ℕ := a.b
/-- The primes, `m` cells. -/
def pr : ℕ := a.b + 6
/-- The count table, `m²` cells. -/
def cnt : ℕ := a.pr + a.m
/-- The sorted copy of the input, `n` cells. -/
def srt : ℕ := a.cnt + a.m * a.m
/-- The distinct values, `n` cells. -/
def val : ℕ := a.srt + a.n
/-- How often they occur, `n` cells. -/
def mul : ℕ := a.val + a.n
/-- The binary digits of the labels, `n Λ` cells. -/
def bt : ℕ := a.mul + a.n
/-- The three sets of a splitting, `3n` cells. -/
def A : ℕ := a.bt + a.n * a.Λ
/-- The doubles of the repeated values, `n` cells. -/
def tw : ℕ := a.A + 3 * a.n
/-- One cell that holds 0: the set {0}. -/
def one : ℕ := a.tw + a.n
/-- The free pointer behind the arrays. -/
def top : ℕ := a.one + 1

/-- The arrays stand one after the other: each address is the one before plus the length of the
array that stands there.  A proof begins with `have hmap := a.layout`, which states the whole
map. -/
theorem layout : a.cx = a.b ∧ a.pr = a.cx + 6 ∧ a.cnt = a.pr + a.m ∧ a.srt = a.cnt + a.m * a.m ∧
    a.val = a.srt + a.n ∧ a.mul = a.val + a.n ∧ a.bt = a.mul + a.n ∧ a.A = a.bt + a.n * a.Λ ∧
    a.tw = a.A + 3 * a.n ∧ a.one = a.tw + a.n ∧ a.top = a.one + 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Map

/-! ## params -/

/-- params(n, V, out) writes `Lam V`, `mPar n V` and `fuel n` to the three cells from `out`. -/
def ParamsSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d n V out : ℕ) (μ : ℕ → ℤ), out + 3 ≤ lim.space → (lim.space : ℤ) ≤ lim.word →
    ((8 * (mPar n V + 1) ^ 2 + 8 * V + 4 * n + 64 : ℕ) : ℤ) ≤ lim.word → d + 1 ≤ lim.depth →
    Meets lim P p d [n, V, out] μ (tParams n V) fun _ μ' =>
      Seg μ' out [(Lam V : ℤ), mPar n V, fuel n] ∧ SameOutside μ μ' out 3

/-! ## prep -/

/-- What prep needs: the size of a word, the number of cells behind the arrays (the sieve's table
and the scratch space of sorting stand there), and the depth of calls. -/
def prepNeed (n V Λ m : ℕ) : Need :=
  ⟨8 * (m + 1) ^ 2 + 8 * V + 4 * n + 64, m + n + Λ + 4, Nat.log 2 n + 3⟩

/-- What prep assumes about its arguments: the input `X` has `n` numbers of absolute value at most
`V` and stands below the base; `Λ` is the number of binary digits for `V`; and the limits allow for
what prep needs behind the arrays. -/
structure Prep.Ctx (lim : Limits) (d : ℕ) (a : Map) (V x : ℕ) (X : List ℤ) : Prop where
  /-- The input has `n` numbers. -/
  len : X.length = a.n
  /-- They have absolute value at most `V`. -/
  bounded : AbsLe X V
  /-- The input stands below the base. -/
  below : x + a.n ≤ a.b
  /-- `V` is not 0. -/
  bound_pos : 1 ≤ V
  /-- `Λ` is the number of binary digits for `V`. -/
  digits : a.Λ = Lam V
  /-- The limits allow for what prep needs. -/
  ok : (prepNeed a.n V a.Λ a.m).Ok lim a.top d

/-- What the routines that run through the splittings are given, for the arrays of a map and the
distinct values `D`. -/
@[simp] def Map.front (a : Map) (V : ℕ) (D : List ℤ) : FrontArgs where
  fr := a.top
  n := a.n
  V := V
  m := a.m
  np := #(Nat.primesLE a.m)
  pr := a.pr
  cnt := a.cnt
  Λ := a.Λ
  nd := D.length
  val := a.val
  bt := a.bt
  A := a.A
  cx := a.cx
  D := D

/-- prep(n, V, Λ, m, x, b): the input `X` stands at `x`.  Fills the arrays of the map `a` with base
`b`: the primes, zeros in the count table, the distinct values `D` and how often they occur, the
binary digits of their labels, the block of parameters, and 0 in the cell `one`.  Returns the number
of distinct values. -/
def PrepSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d : ℕ) (a : Map) (V x : ℕ) (X : List ℤ) (μ : ℕ → ℤ), Prep.Ctx lim d a V x X → Seg μ x X →
    Meets lim P p d [a.n, V, a.Λ, a.m, x, a.b] μ (tPrep a.n a.Λ a.m) fun res μ' =>
      (∃ D C : List ℤ, res = (D.length : ℤ) ∧ Values a.n X D C ∧ Seg μ' a.mul C ∧ μ' a.one = 0 ∧
        FrontMem μ' (a.front V D)) ∧
      Kept μ μ' a.b

/-! ## core -/

/-- core(n, V, x, b), with `V = 2U`: the input `X`, `n` numbers of absolute value at most `U`,
stands at `x`, below the free pointer `b`.  Returns 1 if three of the numbers, at different
positions, sum to 0, and 0 if not.  `T` and `r` are the time and the need of the Convolution-3SUM
solver. -/
def CoreSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ (d n U x b : ℕ) (X : List ℤ) (μ : ℕ → ℤ), X.length = n → AbsLe X U → Seg μ x X → x + n ≤ b →
    1 ≤ n → 1 ≤ U → (coreNeed r n (2 * U)).Ok lim b d →
    Meets lim P p d [n, ((2 * U : ℕ) : ℤ), x, b] μ (coreTime T n (2 * U)) fun res μ' =>
      res = flag (ThreeSum (vecOf n X)) ∧ Kept μ μ' b



end Light.Sec3.ChanHe
