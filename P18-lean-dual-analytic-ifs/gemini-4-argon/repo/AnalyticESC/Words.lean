module

public import AnalyticESC.Defs

@[expose] public section

/-!
# Words

Finite and infinite words: prefixes, prepending, the longest common prefix `|i ∧ j|`,
convergence of words by prefixes and the compactness of `Σ_* ∪ Σ`, and the decomposition of two
distinct words of equal length at their last difference.
-/

namespace AnalyticESC

open Set Filter Topology

namespace Word

variable {N : ℕ}

@[simp] theorem length_fin (w : List (Fin N)) : (fin w).length = w.length := rfl

@[simp] theorem length_inf (w : ℕ → Fin N) : (inf w).length = ⊤ := rfl

@[simp] theorem get?_fin (w : List (Fin N)) (n : ℕ) : (fin w).get? n = w[n]? := rfl

@[simp] theorem get?_inf (w : ℕ → Fin N) (n : ℕ) : (inf w).get? n = some (w n) := rfl

@[simp] theorem take_fin (w : List (Fin N)) (n : ℕ) : (fin w).take n = w.take n := rfl

@[simp] theorem take_inf (w : ℕ → Fin N) (n : ℕ) :
    (inf w).take n = List.ofFn fun k : Fin n => w k := rfl

theorem isSome_get?_iff (w : Word N) (n : ℕ) : (w.get? n).isSome ↔ (n : ℕ∞) < w.length := by
  cases w with
  | fin w => simp [Option.isSome_iff_ne_none]
  | inf w => simp

/-- The letters of a prefix. -/
private theorem getElem?_take_word (w : Word N) (n k : ℕ) :
    (w.take n)[k]? = if k < n then w.get? k else none := by
  cases w with
  | fin w => simp [List.getElem?_take]
  | inf w =>
    simp only [take_inf, List.getElem?_ofFn, get?_inf]
    split_ifs <;> rfl

/-- A word is determined by its letters. -/
theorem ext_get? {v w : Word N} (h : ∀ n, v.get? n = w.get? n) : v = w := by
  cases v with
  | fin v => cases w with
    | fin w => exact congrArg fin (List.ext_getElem? h)
    | inf w => exact absurd (h v.length) (by simp)
  | inf v => cases w with
    | fin w => exact absurd (h w.length) (by simp)
    | inf w => exact congrArg inf (funext fun n => Option.some_injective _ (h n))

theorem get?_prepend (a : List (Fin N)) (w : Word N) (n : ℕ) :
    (w.prepend a).get? n = if n < a.length then a[n]? else w.get? (n - a.length) := by
  cases w with
  | fin w => simp [prepend, List.getElem?_append]
  | inf w =>
    simp only [prepend, get?_inf]
    split_ifs with hn <;> simp [hn]

theorem length_take_of_le {w : Word N} {n : ℕ} (h : (n : ℕ∞) ≤ w.length) :
    (w.take n).length = n := by
  cases w with
  | fin w => simpa [List.length_take] using h
  | inf w => simp

theorem take_prepend_of_le (a : List (Fin N)) (w : Word N) {n : ℕ} (hn : n ≤ a.length) :
    (w.prepend a).take n = a.take n := by
  refine List.ext_getElem? fun k => ?_
  rw [getElem?_take_word, get?_prepend, List.getElem?_take]
  split_ifs <;> first | rfl | omega

theorem take_prepend_add (a : List (Fin N)) (w : Word N) (n : ℕ) :
    (w.prepend a).take (a.length + n) = a ++ w.take n := by
  refine List.ext_getElem? fun k => ?_
  rw [getElem?_take_word, get?_prepend, List.getElem?_append, getElem?_take_word]
  split_ifs <;> first | rfl | omega

theorem le_commonPrefixLength_iff {i j : Word N} {n : ℕ} :
    (n : ℕ∞) ≤ i.commonPrefixLength j ↔ ∀ k < n, (i.get? k).isSome ∧ i.get? k = j.get? k := by
  refine ⟨fun h k hk => ?_, fun h =>
    le_iSup₂ (f := fun (n : ℕ) (_ : ∀ k < n, (i.get? k).isSome ∧ i.get? k = j.get? k) =>
      (n : ℕ∞)) n h⟩
  by_contra hk'
  have hle : i.commonPrefixLength j ≤ k := iSup₂_le fun m hm => by
    by_contra hmk; exact hk' (hm k (by exact_mod_cast not_le.1 hmk))
  have := h.trans hle
  norm_cast at this; omega

private theorem le_length_of_forall_isSome {w : Word N} {n : ℕ}
    (h : ∀ k < n, (w.get? k).isSome) : (n : ℕ∞) ≤ w.length := by
  cases n with
  | zero => simp
  | succ m =>
    exact_mod_cast Order.add_one_le_of_lt ((isSome_get?_iff w m).1 (h m (Nat.lt_succ_self m)))

theorem inf_eq_prepend (u : ℕ → Fin N) (n : ℕ) :
    inf u = (inf fun m => u (n + m)).prepend (List.ofFn fun m : Fin n => u m) :=
  ext_get? fun m => by simp [get?_prepend, List.getElem?_ofFn]; split_ifs <;> [rfl; (congr 2; omega)]

private theorem eq_prepend_take {w : Word N} {n : ℕ} (h : (n : ℕ∞) ≤ w.length) :
    ∃ w' : Word N, w = w'.prepend (w.take n) ∧ (w.take n).length = n := by
  cases w with
  | fin v =>
    exact ⟨fin (v.drop n), congrArg fin (List.take_append_drop n v).symm,
      by simpa [List.length_take] using h⟩
  | inf v => exact ⟨inf fun k => v (n + k), inf_eq_prepend v n, by simp⟩

/-- Two words sharing a prefix of length `n` are obtained from one finite word of length `n`. -/
theorem exists_eq_prepend {i j : Word N} {n : ℕ} (h : (n : ℕ∞) ≤ i.commonPrefixLength j) :
    ∃ (a : List (Fin N)) (i' j' : Word N), a.length = n ∧ i = i'.prepend a ∧ j = j'.prepend a := by
  have hP := le_commonPrefixLength_iff.1 h
  obtain ⟨i', hi', hilen⟩ := eq_prepend_take (le_length_of_forall_isSome fun k hk => (hP k hk).1)
  obtain ⟨j', hj', -⟩ := eq_prepend_take
    (le_length_of_forall_isSome fun k hk => (hP k hk).2 ▸ (hP k hk).1)
  have htake : i.take n = j.take n := List.ext_getElem? fun k => by
    rw [getElem?_take_word, getElem?_take_word]; split_ifs with hk; exacts [(hP k hk).2, rfl]
  exact ⟨i.take n, i', j', hilen, hi', htake ▸ hj'⟩

/-! ## Convergence of words -/

/-- `w k → w₀` letter by letter: every letter of `w₀` is eventually the letter of `w k`. -/
def TendstoPrefix (w : ℕ → Word N) (w₀ : Word N) : Prop :=
  ∀ n, ∀ᶠ k in atTop, (w k).get? n = w₀.get? n

/-- Any sequence of finite words of lengths tending to `∞` has a subsequence converging letter by
letter to an infinite word. -/
theorem exists_subseq_tendstoPrefix (hN : 0 < N) {l : ℕ → List (Fin N)}
    (hlen : Tendsto (fun k => (l k).length) atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ i : ℕ → Fin N,
      TendstoPrefix (fun k => fin (l (φ k))) (inf i) := by
  let _ : TopologicalSpace (Fin N) := ⊥
  have : DiscreteTopology (Fin N) := ⟨rfl⟩
  obtain ⟨i, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq fun k (n : ℕ) => (l k)[n]?.getD ⟨0, hN⟩
  refine ⟨φ, hφ, i, fun n => ?_⟩
  have hcoord : ∀ᶠ k in atTop, (l (φ k))[n]?.getD ⟨0, hN⟩ = i n := by
    simpa [nhds_discrete] using tendsto_pi_nhds.1 hlim n
  filter_upwards [(hlen.comp hφ.tendsto_atTop).eventually_gt_atTop n, hcoord] with k hk1 hk2
  simp [List.getElem?_eq_getElem hk1, ← hk2]

theorem TendstoPrefix.comp {w : ℕ → Word N} {w₀ : Word N} (h : TendstoPrefix w w₀)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : TendstoPrefix (w ∘ φ) w₀ :=
  fun n => hφ.tendsto_atTop.eventually (h n)

theorem TendstoPrefix.eventually_le_commonPrefixLength {w : ℕ → Word N} {i : ℕ → Fin N}
    (h : TendstoPrefix w (inf i)) (n : ℕ) :
    ∀ᶠ k in atTop, (n : ℕ∞) ≤ (w k).commonPrefixLength (inf i) := by
  filter_upwards [eventually_all.2 fun m : Fin n => h m] with k hk
  exact le_commonPrefixLength_iff.2 fun m hm => ⟨by simp [hk ⟨m, hm⟩], hk ⟨m, hm⟩⟩

end Word

/-- Two distinct words of equal length split at their last difference: `i = a u`, `j = b u` with
`|a| = |b| ≥ 1` and different last letters of `a` and `b`. -/
theorem List.exists_decomp_of_ne {N : ℕ} {i j : List (Fin N)} (hlen : i.length = j.length)
    (hne : i ≠ j) :
    ∃ a b u : List (Fin N), i = a ++ u ∧ j = b ++ u ∧ a.length = b.length ∧ 0 < a.length ∧
      a.getLast? ≠ b.getLast? := by
  induction i using _root_.List.reverseRecOn generalizing j with
  | nil => exact absurd (_root_.List.eq_nil_of_length_eq_zero hlen.symm).symm hne
  | append_singleton i x ih =>
    have hj : j ≠ [] := fun h => by simp [h] at hlen
    obtain ⟨j', y, rfl⟩ : ∃ j' y, j = j' ++ [y] :=
      ⟨j.dropLast, j.getLast hj, (_root_.List.dropLast_append_getLast hj).symm⟩
    simp only [_root_.List.length_append, _root_.List.length_singleton,
      Nat.add_right_cancel_iff] at hlen
    by_cases hxy : x = y
    · subst hxy
      obtain ⟨a, b, u, rfl, rfl, hab, ha, hlast⟩ := ih hlen fun h => hne (h ▸ rfl)
      exact ⟨a, b, u ++ [x], by simp, by simp, hab, ha, hlast⟩
    · exact ⟨i ++ [x], j' ++ [y], [], by simp, by simp, by simp [hlen], by simp, by simp [hxy]⟩

end AnalyticESC
