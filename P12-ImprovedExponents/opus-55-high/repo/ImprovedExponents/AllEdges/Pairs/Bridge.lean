
import ImprovedExponents.AllEdges.Task
import ImprovedExponents.AllEdges.Pairs.Passes
import ImprovedExponents.MinPlus.ExactTriangle
import ThreeSumApsp.Spec.Sec3.Theorem21b.NegativeTriangle
import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.Tasks


/-!
# The questions of the reduction from all pairs to all-edges Exact Triangle

Footnote 10 of the paper: the (min,+)-product reduces to the all-edges version of Exact Triangle
on the same `n` vertices.  The step from the threshold questions of upstream's `pairsTask`
("is there a `k` with `X[i,k] + Y[k,j] < V[i,j]`?") to zero triangles is Lemma F of the paper
(`ImprovedExponents.add_lt_iff_shiftDiff`, in the form `exists_lt_iff_exists_exactTriangle`): with
`b = aeLevels U` levels, `3U < 2^b ≤ 6U`, the threshold holds for some `k` if and only if one of
the `2b + 3` instances `(ℓ, r) ∈ lemmaFInstances b` has a zero triangle through `(i, j)`.

The instance `(ℓ, r)` has, in the convention of `aeTask` (`AB` at `a n + b`, `BC` at `b n + c`,
`AC` at `a n + c`, with `a = i`, `b = j`, `c = k`), the matrices `r − ⌊(V + 2U)/2^ℓ⌋` (`instAB`),
the transpose of `⌊(Y + U)/2^ℓ⌋` (`instBC`) and `⌊(X + U)/2^ℓ⌋` (`instAC`).  `pairFlags_iff`
is the bridge, `absLe_inst*` bound the weights by `9U`, and `orFlags` with `orL_orFlags` describes
the disjunction of the flags of the instances asked so far.
-/

namespace ImprovedExponents.AllEdges

open Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- The number of levels: for `U ≥ 1`, the least `b` with `2^b > 3U`. -/
def aeLevels (U : ℕ) : ℕ := Nat.log 2 (3 * U) + 1

theorem lt_two_pow_aeLevels (U : ℕ) : 3 * U < 2 ^ aeLevels U :=
  Nat.lt_pow_succ_log_self (by norm_num) _

theorem two_pow_aeLevels_le {U : ℕ} (hU : 1 ≤ U) : 2 ^ aeLevels U ≤ 6 * U := by
  grind [Nat.pow_log_le_self, aeLevels]

/-! ## The lists of the instances -/

/-- The shifted numbers at the start: `X + U`, the transpose of `Y` plus `U`, and `V + 2U`, one
list after the other (the array on which the prefixes are computed). -/
def pStart (n U : ℕ) (X Y V : List ℤ) : List ℤ :=
  affL 1 U X ++ (transposeL n U Y ++ affL 1 (2 * U) V)

/-- The matrix `AC` of the instance of the level `ℓ`: `⌊(X + U)/2^ℓ⌋`. -/
def instAC (U : ℕ) (X : List ℤ) (ℓ : ℕ) : List ℤ := (affL 1 U X).map (prefQ ℓ)

/-- The matrix `BC` of the instance of the level `ℓ`: the transpose of `⌊(Y + U)/2^ℓ⌋`. -/
def instBC (n U : ℕ) (Y : List ℤ) (ℓ : ℕ) : List ℤ := (transposeL n U Y).map (prefQ ℓ)

/-- The matrix `AB` of the instance `(ℓ, r)`: `r − ⌊(V + 2U)/2^ℓ⌋`. -/
def instAB (U : ℕ) (V : List ℤ) (ℓ : ℕ) (r : ℤ) : List ℤ :=
  affL (-1) r ((affL 1 (2 * U) V).map (prefQ ℓ))

section Lists

variable {n U : ℕ} {X Y V : List ℤ}

theorem length_pStart (hX : X.length = n * n) (hV : V.length = n * n) :
    (pStart n U X Y V).length = 3 * (n * n) := by
  grind [pStart, List.length_append, length_affL, length_transposeL]

/-- The numbers at the start are between `0` and `3U`. -/
theorem pStart_range (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U) (hlenY : Y.length = n * n) :
    ∀ z ∈ pStart n U X Y V, 0 ≤ z ∧ z ≤ 3 * (U : ℤ) := by
  intro z hz
  simp [pStart, List.mem_append] at hz
  rcases hz with hz | hz | hz
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    have := abs_le.1 (by aesop)
    omega
  · have := mem_transposeL_bounds hY hlenY U z hz
    omega
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    have := abs_le.1 (by aesop)
    omega

variable {l : List ℤ}


/-- The entries of the prefixes of a list of numbers in `[0, B]` lie in `[0, B]`. -/
theorem absLe_map_prefQ {B : ℤ} (h : ∀ z ∈ l, 0 ≤ z ∧ z ≤ B) (ℓ : ℕ) :
    ∀ z ∈ l.map (prefQ ℓ), 0 ≤ z ∧ z ≤ B := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  exact ⟨by simp_all [prefQ_nonneg], (prefQ_le (h y hy).1 ℓ).trans (h y hy).2⟩

/-- The parts of the prefixes of the start list. -/
theorem absLe_pStart_parts (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U)
    (hlenY : Y.length = n * n) (ℓ : ℕ) :
    (∀ z ∈ instAC U X ℓ, 0 ≤ z ∧ z ≤ 3 * (U : ℤ)) ∧
      (∀ z ∈ instBC n U Y ℓ, 0 ≤ z ∧ z ≤ 3 * (U : ℤ)) ∧
      ∀ z ∈ (affL 1 (2 * U) V).map (prefQ ℓ), 0 ≤ z ∧ z ≤ 3 * (U : ℤ) := by
  have h := absLe_map_prefQ (pStart_range hX hY hV hlenY) ℓ
  simp only [pStart, List.map_append, List.mem_append] at h
  exact ⟨fun z hz => h z (Or.inl hz), fun z hz => h z (by tauto),
    by simp_all⟩

/-- The weights of the three matrices of an instance are bounded by `9U`. -/
theorem absLe_inst (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U) (hlenY : Y.length = n * n)
    (hU : 1 ≤ U) {ℓ : ℕ} {r : ℤ} (hr : 1 ≤ r ∧ r ≤ 3) :
    AbsLe (instAB U V ℓ r) ((9 * U : ℕ) : ℤ) ∧ AbsLe (instBC n U Y ℓ) ((9 * U : ℕ) : ℤ) ∧
      AbsLe (instAC U X ℓ) ((9 * U : ℕ) : ℤ) := by
  obtain ⟨h1, h2, h3⟩ := absLe_pStart_parts hX hY hV hlenY ℓ
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
    grind
  · grind
  grind

/-! ## The bridge -/

/-- **The bridge**: the flag of the pair `q` of `pairsTask` is 1 if and only if one of the
instances `(ℓ, r) ∈ lemmaFInstances (aeLevels U)` has the flag 1 at `q`. -/
theorem pairFlags_iff (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U)
    (hlX : X.length = n * n) (hlY : Y.length = n * n) (hlV : V.length = n * n) {q : ℕ}
    (hq : q < n * n) :
    (pairFlags n X Y V).getD q 0 = 1 ↔ ∃ c ∈ lemmaFInstances (aeLevels U),
      (aeFlags n (instAB U V c.1 c.2) (instBC n U Y c.1) (instAC U X c.1)).getD q 0 = 1 := by
  have hn : 0 < n := by grind
  have hi : q / n < n := by simp_all [Nat.div_lt_iff_lt_mul]
  have hj := q.mod_lt hn
  have hqe := Nat.div_add_mod' q n
  have hbN := lt_two_pow_aeLevels U
  have hb : (3 * U : ℤ) < 2 ^ aeLevels U := by linarith
  -- the matrices as functions on `Fin n`
  set A : Fin n → Fin n → ℤ := fun i k => X.getD (i * n + k) 0 with hA
  set B : Fin n → Fin n → ℤ := fun k j => Y.getD (k * n + j) 0 with hB
  set t : Fin n → Fin n → ℤ := fun i j => V.getD (i * n + j) 0 with ht
  have hidx : ∀ a b : Fin n, a * n + b < n * n := fun a b => by nlinarith [a.2, b.2]
  have hmem : ∀ (l : List ℤ), l.length = n * n → ∀ a b : Fin n, l.getD (a * n + b) 0 ∈ l :=
    by simp_all
  have key := exists_lt_iff_exists_exactTriangle A B t (b := aeLevels U)
    (by aesop) (by aesop) (by omega)
    fun i j => by
      have := abs_le.1 (hV _ (hmem V hlV i j))
      grind ⟨q / n, hi⟩ ⟨q % n, hj⟩
  simp only [hA, hB, ht, hqe] at key
  have hrange : ∀ f : ℕ → ℤ, ((List.range (n * n)).map f).getD q 0 = f q := by simp_all
  simp only [pairFlags, aeFlags, hrange, flag_eq_one_iff]
  rw [show (∃ k < n, X.getD _ 0 + Y.getD _ 0 < V.getD q 0) ↔
      ∃ k : Fin n, X.getD (q / n * n + k) 0 + Y.getD (k * n + q % n) 0 < V.getD q 0 from
    ⟨by tauto, by grind⟩, key]
  refine exists_congr fun c => and_congr_right fun hc => ?_
  have hmap : ∀ (l : List ℤ) (f : ℤ → ℤ) (idx : ℕ), idx < n * n → l.length = n * n →
      (l.map f).getD idx 0 = f (l.getD idx 0) := by simp_all
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, k.2, ?_⟩
    simp only [instAB, instBC, instAC, affL, etIK, etKJ, etJI] at hk ⊢
    rw [hmap _ _ _ hq (by simp_all), hmap _ _ _ hq (by simp_all), hmap _ _ _ hq hlV,
      hmap _ _ _ (hidx ⟨q % n, hj⟩ k) (by simp), transposeL_getD _ _ hj k.2,
      hmap _ _ _ (by grind) (by simp_all), hmap _ _ _ (by grind) hlX]
    grind [prefQ]
  · rintro ⟨k, hk, h⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    simp only [instAB, instBC, instAC, affL, etIK, etKJ, etJI] at h ⊢
    rw [hmap _ _ _ hq (by simp_all), hmap _ _ _ hq (by simp_all), hmap _ _ _ hq hlV,
      hmap _ _ _ (hidx ⟨q % n, hj⟩ ⟨k, hk⟩) (by simp), transposeL_getD _ _ hj hk,
      hmap _ _ _ (hidx ⟨q / n, hi⟩ ⟨k, hk⟩) (by simp_all),
      hmap _ _ _ (by tauto) hlX] at h
    grind [prefQ]

end Lists

/-! ## The disjunction of the flags of the instances asked so far -/

/-- The flags of the pairs: cell `q` holds 1 if some instance `c` with `S c` has the flag 1 at
`q`, where `hit c q` says that it has. -/
noncomputable def orFlags (N : ℕ) (S : ℕ × ℤ → Prop) (hit : ℕ × ℤ → ℕ → Prop) : List ℤ :=
  (List.range N).map fun q => flag (∃ c, S c ∧ hit c q)

variable (N : ℕ) (S : ℕ × ℤ → Prop) (hit : ℕ × ℤ → ℕ → Prop)

@[simp] theorem length_orFlags :
    (orFlags N S hit).length = N := by
  simp [orFlags]

theorem orFlags_mem :
    ∀ z ∈ orFlags N S hit, z = 0 ∨ z = 1 := by
  intro z hz
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hz
  unfold flag
  omega

/-- Before any question the flags are zero. -/
theorem orFlags_false {l : List ℤ} (hl : l.length = N) :
    orFlags N (fun _ => False) hit = affL 0 0 l := by
  simp_all [orFlags, affL, flag]

/-- The disjunction with the flags of one more instance. -/
theorem orL_orFlags {N : ℕ} {S : ℕ × ℤ → Prop} {hit : ℕ × ℤ → ℕ → Prop} {c : ℕ × ℤ} {F : List ℤ}
    (hF : F.length = N) (hhit : ∀ q < N, hit c q ↔ F.getD q 0 = 1)
    (h01 : ∀ f ∈ F, f = 0 ∨ f = 1) :
    orL (orFlags N S hit) F = orFlags N (fun c' => S c' ∨ c' = c) hit := by
  refine List.ext_getElem (by simp_all) fun i h1 h2 => ?_
  have hi : i < N := by simp_all
  have hFi : F.getD i 0 = F[i] := by simp_all
  have hc := hhit i hi
  rw [hFi] at hc
  simp only [orL, orFlags, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  rcases h01 _ (List.getElem_mem (hF ▸ hi)) with h | h
  · simp_all
  · rw [h, flag_of (p := ∃ c', (S c' ∨ c' = c) ∧ hit c' i) ⟨c, Or.inr rfl, hc.2 h⟩]
    omega

/-- The instances at the levels above `ℓ` (and at most `b`) with `r ∈ {2, 3}`. -/
def Above (ℓ b : ℕ) (c : ℕ × ℤ) : Prop := ℓ < c.1 ∧ c.1 ≤ b ∧ (c.2 = 2 ∨ c.2 = 3)

/-- The two questions at the level `ℓ + 1` bring the asked set from above `ℓ + 1` to above `ℓ`. -/
theorem above_step {ℓ b : ℕ} (h : ℓ + 1 ≤ b) (c : ℕ × ℤ) :
    ((Above (ℓ + 1) b c ∨ c = (ℓ + 1, 2)) ∨ c = (ℓ + 1, 3)) ↔ Above ℓ b c := by
  grind [Above]

variable (b : ℕ)

/-- Nothing has been asked at the top. -/
theorem above_self (c : ℕ × ℤ) : ¬ Above b b c := fun h => by
  have := h.1
  have := h.2.1
  omega

/-- After the questions at the level `0`, all instances of Lemma F have been asked. -/
theorem above_zero_iff (c : ℕ × ℤ) :
    (((Above 0 b c ∨ c = (0, 2)) ∨ c = (0, 3)) ∨ c = (0, 1)) ↔ c ∈ lemmaFInstances b := by
  grind [Above, lemmaFInstances]

/-- **The flags of all pairs** are the disjunction of the flags of the instances of Lemma F. -/
theorem orFlags_eq_pairFlags {n U : ℕ} {X Y V : List ℤ} (hX : AbsLe X U) (hY : AbsLe Y U)
    (hV : AbsLe V U) (hlX : X.length = n * n) (hlY : Y.length = n * n) (hlV : V.length = n * n) :
    orFlags (n * n) (fun c => c ∈ lemmaFInstances (aeLevels U))
      (fun c q => (aeFlags n (instAB U V c.1 c.2) (instBC n U Y c.1) (instAC U X c.1)).getD q 0 = 1)
      = pairFlags n X Y V := by
  refine List.ext_getElem (by simp [pairFlags]) fun q h1 h2 => ?_
  have hq : q < n * n := by simp_all
  have h := pairFlags_iff hX hY hV hlX hlY hlV hq
  grind [List.getD_eq_getElem, orFlags, pairFlags, flag_of, flag_of_not, flag]
