module

public import AnalyticESC.Defs
set_option hygiene false
local notation "𝖞" => Fin N
local notation "𝖝" => w.take n
local notation "𝔟" => n + 1


@[expose] public section

/-!
# Words

Finite and infinite words: prefixes, prepending, the longest common prefix `|i ∧ j|`,
convergence of words by prefixes and the compactness of `Σ_* ∪ Σ`, and the decomposition of two
distinct words of equal length at their last difference.
-/

namespace AnalyticESC

variable {n : ℕ} {v w i j : Word N}

open Filter Topology

namespace Word


@[simp] theorem length_fin (w : 𝔚 N) : (fin w).length = w.length := rfl

@[simp] theorem length_inf (w : 𝔖 N) : (inf w).length = ⊤ := rfl

@[simp] theorem get?_fin (w : 𝔚 N) n : (fin w).get? n = w[n]? := rfl

@[simp] theorem get?_inf (w : 𝔖 N) n : (inf w).get? n = some (w n) := rfl

@[simp] theorem take_fin (w : 𝔚 N) n : (fin w).take n = w.take n := rfl

@[simp] theorem take_inf (w : 𝔖 N) n :
    (inf w).take n = List.ofFn fun k : Fin n => w k := rfl

theorem length_take (w : Word N) n : ((w.take n).length : ℕ∞) = min (n : ℕ∞) w.length := by
  cases w with
  | fin w => simpa using Nat.mono_cast.map_min
  | inf w => simp

theorem isSome_get?_iff (w : Word N) n : (w.get? n).isSome ↔ (n : ℕ∞) < w.length := by
  cases w with
  | fin w => simp
  | inf w => simp

/-- The letters of a prefix. -/
theorem getElem?_take_word :
    𝖝[k]? = if k < n then w.get? k else none := by
  cases w with
  | fin w => simp [List.getElem?_take]
  | inf w =>
    simp only [take_inf, List.getElem?_ofFn]
    split_ifs <;> rfl

/-- Two prefixes of length `n` agree if and only if the first `n` letters agree. -/
theorem take_eq_take_iff :
    v.take n = w.take n ↔ ∀ k < n, v.get? k = w.get? k := by
  constructor
  · intro h k hk
    have := congrArg (fun l : 𝔚 N => l[k]?) h
    simpa [getElem?_take_word, hk] using this
  · intro h
    refine List.ext_getElem? fun k => ?_
    rw [getElem?_take_word, getElem?_take_word]
    grind

/-- A word is determined by its letters. -/
theorem ext_get? (h : ∀ n, v.get? n = w.get? n) : v = w := by
  cases v with
  | fin v =>
    cases w with
    | fin w => exact congrArg fin (List.ext_getElem? h)
    | inf w => have := h v.length; simp at this
  | inf v =>
    cases w with
    | fin w => have := h w.length; simp at this
    | inf w => exact congrArg inf (funext fun n => Option.some_injective _ (h n))

theorem get?_succ_eq_none (h : w.get? n = none) :
    w.get? 𝔟 = none := by
  cases w with
  | fin w =>
    simp at h ⊢
    omega
  | inf w => simp at h

theorem get?_prepend :
    (w.prepend a).get? n = if n < a.length then a[n]? else w.get? (n - a.length) := by
  cases w with
  | fin w => simp [prepend, List.getElem?_append]
  | inf w =>
    simp [prepend]
    split_ifs with hn <;> simp

theorem length_take_of_le (h : (n : ℕ∞) ≤ w.length) :
    (w.take n).length = n := by
  have := length_take w n
  simp_all

theorem take_of_length_le (h : w.length ≤ n) : w = fin 𝖝 := by
  cases w with
  | fin w =>
    simp at h
    simp [List.take_of_length_le h]
  | inf w => simp at h

theorem length_prepend :
    (w.prepend a).length = a.length + w.length := by
  cases w with
  | fin w => simp [prepend]
  | inf w => simp [prepend]

theorem get?_prepend_of_lt a (w : Word N) (hn : n < a.length) :
    (w.prepend a).get? n = a[n]? := by
  simp [get?_prepend, hn]

theorem get?_prepend_add a (w : Word N) n :
    (w.prepend a).get? (a.length + n) = w.get? n := by
  simp [get?_prepend]

theorem take_prepend_of_le a (w : Word N) (hn : n ≤ a.length) :
    (w.prepend a).take n = a.take n := by
  refine List.ext_getElem? fun k => ?_
  rw [getElem?_take_word, get?_prepend, List.getElem?_take]
  grind

theorem take_prepend_add a (w : Word N) n :
    (w.prepend a).take (a.length + n) = a ++ w.take n := by
  refine List.ext_getElem? fun k => ?_
  rw [getElem?_take_word, get?_prepend, List.getElem?_append, getElem?_take_word]
  grind

theorem commonPrefixLength_comm (i j : Word N) :
    i.commonPrefixLength j = j.commonPrefixLength i := by
  have key : ∀ i j : Word N, i.commonPrefixLength j ≤ j.commonPrefixLength i := by
    intro i j
    refine iSup₂_le fun n hn => ?_
    refine le_iSup₂ (f := fun n (_ : ∀ k < n, (j.get? k).isSome ∧ j.get? k = i.get? k) =>
      (n : ℕ∞)) n fun k hk => ?_
    grind
  grind

theorem le_commonPrefixLength_iff :
    (n : ℕ∞) ≤ i.commonPrefixLength j ↔ ∀ k < n, (i.get? k).isSome ∧ i.get? k = j.get? k := by
  constructor
  · intro h
    by_contra hn
    simp only [not_forall] at hn
    obtain ⟨k, hk, hk'⟩ := hn
    have hle : i.commonPrefixLength j ≤ k := by
      refine iSup₂_le fun m hm => ?_
      by_contra hmk
      exact hk' (hm k (by simp_all))
    have := h.trans hle
    norm_cast at this
    omega
  · intro h
    exact le_iSup₂ (f := fun n (_ : ∀ k < n, (i.get? k).isSome ∧ i.get? k = j.get? k) =>
      (n : ℕ∞)) n h

theorem commonPrefixLength_le_length (i j : Word N) :
    i.commonPrefixLength j ≤ min i.length j.length := by
  have key : ∀ i j : Word N, i.commonPrefixLength j ≤ i.length := by
    intro i j
    refine iSup₂_le fun m hm => ?_
    cases m with
    | zero => simp
    | succ m =>
      have := (isSome_get?_iff i m).1 (hm m (Nat.lt_succ_self m)).1
      exact_mod_cast Order.add_one_le_of_lt this
  exact le_min (key i j) (commonPrefixLength_comm i j ▸ key j i)

theorem commonPrefixLength_lt_top (h : i ≠ j) : i.commonPrefixLength j < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  refine h (ext_get? fun k => ?_)
  have : ((k + 1 : ℕ) : ℕ∞) ≤ i.commonPrefixLength j := by simp_all
  exact (le_commonPrefixLength_iff.1 this k (Nat.lt_succ_self k)).2

theorem eq_prepend_take (h : (n : ℕ∞) ≤ w.length) :
    ∃ w' : Word N, w = w'.prepend 𝖝 ∧ (w.take n).length = n := by
  let w' : Word N := match w with
    | fin v => fin (v.drop n)
    | inf v => inf fun k => v (n + k)
  have hw' : ∀ k, w'.get? k = w.get? (n + k) := by aesop
  refine ⟨w', ext_get? fun k => ?_, length_take_of_le h⟩
  rw [get?_prepend, length_take_of_le h, getElem?_take_word, hw']
  grind

/-- Two words sharing a prefix of length `n` are obtained from one finite word of length `n`. -/
theorem exists_eq_prepend (h : (n : ℕ∞) ≤ i.commonPrefixLength j) :
    ∃ (a : 𝔚 N) (i' j' : Word N), a.length = n ∧ i = i'.prepend a ∧ j = j'.prepend a := by
  obtain ⟨i', hi', hilen⟩ := eq_prepend_take (h.trans ((commonPrefixLength_le_length i j).trans (min_le_left _ _)))
  obtain ⟨j', hj', -⟩ := eq_prepend_take (h.trans ((commonPrefixLength_le_length i j).trans (min_le_right _ _)))
  have htake := take_eq_take_iff.2 fun k hk => ((le_commonPrefixLength_iff.1 h) k hk).2
  grind

/-! ## Convergence of words -/

/-- `w k → w₀` letter by letter: every prefix of `w₀` is eventually the prefix of `w k`. -/
def TendstoPrefix (w : ℕ → Word N) (w₀ : Word N) : Prop :=
  ∀ n, ∀ᶠ k in atTop, (w k).take n = w₀.take n

/-- A sequence of letters which stays `none` once `none` is the sequence of letters of a word. -/
theorem exists_get?_eq (a : ℕ → Option 𝖞) (ha : ∀ n, a n = none → a 𝔟 = none) :
    ∃ w : Word N, ∀ n, w.get? n = a n := by
  classical
  by_cases hex : ∃ n, a n = none
  · have hnone : ∀ n, Nat.find hex ≤ n → a n = none := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => exact Nat.find_spec hex
      | succ n _ ih => exact ha n ih
    refine ⟨fin (List.ofFn fun k : Fin (Nat.find hex) => (a k).get ((fun n hn => Option.isSome_iff_ne_none.2 (Nat.find_min hex hn)) k k.2)), fun n => ?_⟩
    simp only [get?_fin, List.getElem?_ofFn]
    split_ifs with hn
    · simp
    · grind
  · have hex' := fun n hn => hex ⟨n, hn⟩
    exact ⟨inf fun n => (a n).get (Option.isSome_iff_ne_none.2 (hex' n)), fun n => by simp⟩

/-- `Σ_* ∪ Σ` is sequentially compact. -/
theorem exists_subseq_tendstoPrefix (w : ℕ → Word N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w₀ : Word N, TendstoPrefix (w ∘ φ) w₀ := by
  let _ : TopologicalSpace (Option 𝖞) := ⊥
  have : DiscreteTopology (Option 𝖞) := by tauto
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq fun k n => (w k).get? n
  have hcoord : ∀ n, ∀ᶠ k in atTop, (w (φ k)).get? n = a n := by
    intro n
    have := tendsto_pi_nhds.1 hlim n
    rwa [nhds_discrete, tendsto_pure] at this
  obtain ⟨w₀, hw₀⟩ := exists_get?_eq a (by intro n hn; obtain ⟨k, hk1, hk2⟩ := ((hcoord n).and (hcoord 𝔟)).exists; rw [← hk2]; exact get?_succ_eq_none (hk1.trans hn))
  refine ⟨φ, hφ, w₀, fun n => ?_⟩
  have hall : ∀ᶠ k in atTop, ∀ m : Fin n, (w (φ k)).get? m = a m :=
    eventually_all.2 fun m => hcoord m
  filter_upwards [hall] with k hk
  exact take_eq_take_iff.2 fun m hm => (hk ⟨m, hm⟩).trans (hw₀ m).symm

section
variable {w : ℕ → Word N} {w₀ : Word N} (h : TendstoPrefix w w₀)
include h

theorem TendstoPrefix.comp (hφ : StrictMono φ) : TendstoPrefix (w ∘ φ) w₀ :=
  fun n => hφ.tendsto_atTop.eventually (h n)

theorem TendstoPrefix.eventually_get?_eq n : ∀ᶠ k in atTop, (w k).get? n = w₀.get? n :=
  (h 𝔟).mono fun _ hk => take_eq_take_iff.1 hk n (Nat.lt_succ_self n)

theorem TendstoPrefix.eventually_eq (h₀ : w₀.length ≠ ⊤) : ∀ᶠ k in atTop, w k = w₀ := by
  obtain ⟨l, rfl⟩ : ∃ l, w₀ = fin l := by
    cases w₀ with
    | fin l => exact ⟨l, rfl⟩
    | inf _ => simp at h₀
  filter_upwards [h (l.length + 1)] with k hk
  have hlen := length_take (w k) (l.length + 1)
  rw [hk, take_fin, List.take_of_length_le (by omega)] at hlen
  have hle : (w k).length ≤ ((l.length + 1 : ℕ) : ℕ∞) := by
    by_contra hc
    rw [min_eq_left (not_le.1 hc).le] at hlen
    norm_cast at hlen
    omega
  rw [take_of_length_le hle, hk, take_fin, List.take_of_length_le (by omega)]

/-- A limit of words which eventually have length `L` has length `L`. -/
theorem TendstoPrefix.length_eq_of_eventually {L : ℕ} (hL : ∀ᶠ k in atTop, (w k).length = L) : w₀.length = L := by
  obtain ⟨k, hk1, hk2⟩ := ((h (L + 1)).and hL).exists
  have h1 : min ((L + 1 : ℕ) : ℕ∞) w₀.length = L := by
    rw [← length_take, ← hk1, length_take, hk2]
    simp_all
  rcases le_or_gt w₀.length ((L + 1 : ℕ) : ℕ∞) with hc | hc
  · grind
  · rw [min_eq_left hc.le] at h1
    simp_all

theorem TendstoPrefix.eventually_le_commonPrefixLength (h₀ : w₀.length = ⊤) (n : ℕ) :
    ∀ᶠ k in atTop, (n : ℕ∞) ≤ (w k).commonPrefixLength w₀ := by
  filter_upwards [h n] with k hk
  rw [le_commonPrefixLength_iff]
  intro m hm
  refine ⟨?_, take_eq_take_iff.1 hk m hm⟩
  rw [take_eq_take_iff.1 hk m hm, isSome_get?_iff, h₀]
  simp_all

theorem TendstoPrefix.tendsto_length (hlen : Tendsto (fun k => (w k).length) atTop (𝓝 ⊤)) : w₀.length = ⊤ := by
  by_contra h₀
  obtain ⟨L, hL⟩ := ENat.ne_top_iff_exists.1 h₀
  obtain ⟨k, hk1, hk2⟩ :=
    ((h.eventually_eq h₀).and (hlen.eventually_const_lt (ENat.natCast_lt_top L))).exists
  grind

end

theorem TendstoPrefix.length_eq {i j : ℕ → Word N} {i₀ j₀ : Word N} (hi : TendstoPrefix i i₀)
    (hj : TendstoPrefix j j₀) (hlen : ∀ k, (i k).length = (j k).length) :
    i₀.length = j₀.length := by
  have key : ∀ {i j : ℕ → Word N} {i₀ j₀ : Word N}, TendstoPrefix i i₀ → TendstoPrefix j j₀ →
      (∀ k, (i k).length = (j k).length) → i₀.length ≠ ⊤ → j₀.length = i₀.length := by
    intro i j i₀ j₀ hi hj hlen h₀
    obtain ⟨L, hL⟩ := ENat.ne_top_iff_exists.1 h₀
    rw [← hL]
    refine hj.length_eq_of_eventually ?_
    filter_upwards [hi.eventually_eq h₀] with k hk
    rw [← hlen, hk, hL]
  by_cases hi₀ : i₀.length = ⊤
  · grind
  · grind

theorem eq_inf_of_length_eq_top (h : w.length = ⊤) : ∃ v : 𝔖 N, w = inf v := by
  cases w with
  | fin w => simp at h
  | inf v => exact ⟨v, rfl⟩

end Word

/-- Two distinct words of equal length split at their last difference: `i = a u`, `j = b u` with
`|a| = |b| ≥ 1` and different last letters of `a` and `b`. -/
theorem List.exists_decomp_of_ne {i j : 𝔚 N} (hlen : i.length = j.length)
    (hne : i ≠ j) :
    ∃ a b u : 𝔚 N, i = a ++ u ∧ j = b ++ u ∧ a.length = b.length ∧ 0 < a.length ∧
      a.getLast? ≠ b.getLast? := by
  induction i using _root_.List.reverseRecOn generalizing j with
  | nil =>
    have : j = [] := _root_.List.eq_nil_of_length_eq_zero hlen.symm
    exact absurd this.symm hne
  | append_singleton i x ih =>
    obtain ⟨j', y, rfl⟩ : ∃ j' y, j = j' ++ [y] :=
      ⟨j.dropLast, j.getLast (by grind), (_root_.List.dropLast_append_getLast (by grind)).symm⟩
    simp at hlen
    by_cases hxy : x = y
    · subst hxy
      have hne' : i ≠ j' := fun h => hne (h ▸ rfl)
      grind
    · exact ⟨i ++ [x], j' ++ [y], [], by simp, by simp, by simp_all, by simp, by simp_all⟩

end AnalyticESC
