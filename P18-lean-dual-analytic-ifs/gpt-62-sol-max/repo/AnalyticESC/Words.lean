module

public import AnalyticESC.Defs

@[expose] public section

/-! Prefix calculations and compactness for infinite words. -/

namespace AnalyticESC

open Set Filter Topology

namespace Word

theorem pref_add {α : Type*} (w : ℕ → α) (k n : ℕ) :
    pref w (n + k) = pref w k ++ pref (shift w k) n :=
  List.ext_getElem (by grind) fun l h₁ h₂ => by grind

theorem pref_succ {α : Type*} (w : ℕ → α) (n : ℕ) :
    pref w (n + 1) = w 0 :: pref (shift w 1) n := List.ofFn_succ

variable {N : ℕ}

@[simp] theorem get?_fin (w : List (Fin N)) (n : ℕ) : (fin w).get? n = w[n]? := rfl

@[simp] theorem get?_inf (w : ℕ → Fin N) (n : ℕ) : (inf w).get? n = some (w n) := rfl

@[simp] theorem take_fin (w : List (Fin N)) (n : ℕ) : (fin w).take n = w.take n := rfl

@[simp] theorem take_inf (w : ℕ → Fin N) (n : ℕ) :
    (inf w).take n = List.ofFn fun k : Fin n => w k := rfl

theorem sameLength_fin {u v : List (Fin N)} (h : u.length = v.length) :
    (fin u).SameLength (fin v) := by
  intro n
  apply Bool.eq_iff_iff.2
  simp_all

/-- The letters of a prefix. -/
theorem getElem?_take_word (w : Word N) (n k : ℕ) :
    (w.take n)[k]? = if k < n then w.get? k else none := by
  cases w with
  | fin w => aesop
  | inf w =>
    simp

theorem take_eq_of_get?_eq {v w : Word N} {n : ℕ}
    (h : ∀ k < n, v.get? k = w.get? k) : v.take n = w.take n :=
  List.ext_getElem? fun k => by simp only [getElem?_take_word]; simp_all

/-- A word is determined by its letters. -/
private theorem ext_get? {v w : Word N} (h : ∀ n, v.get? n = w.get? n) : v = w := by
  cases v with
  | fin v =>
    cases w with
    | fin w => aesop
    | inf w => have := h v.length; simpa
  | inf v =>
    cases w with
    | fin w => have := h w.length; simpa
    | inf w => aesop

/-- The suffix after deleting the first `n` letters. -/
def drop : Word N → ℕ → Word N
  | fin w, n => fin (w.drop n)
  | inf w, n => inf (shift w n)

theorem take_add_drop (w : Word N) (m n : ℕ) : w.take (m + n) = w.take m ++ (w.drop m).take n := by
  cases w with
  | fin w => simp [drop, List.take_add]
  | inf w => simpa only [take_inf, drop, Nat.add_comm m n] using pref_add w m n

@[simp] theorem get?_drop (w : Word N) (n k : ℕ) : (w.drop n).get? k = w.get? (k + n) := by
  cases w <;> simp [drop, shift, List.getElem?_drop, Nat.add_comm]

theorem length_take_of_get?_eq_some {w : Word N} {n : ℕ} {a : Fin N}
    (h : w.get? n = some a) : (w.take n).length = n := by
  cases w with
  | fin w =>
    have := (List.getElem?_eq_some_iff.1 h).1
    simp_all; nlinarith
  | inf _ => simp

/-- Distinct words of equal length have a common finite prefix followed by different letters. -/
theorem exists_prefix_first_ne {v w : Word N} (hne : v ≠ w) (hlen : v.SameLength w) :
    ∃ n c d, v.take n = w.take n ∧ v.get? n = some c ∧ w.get? n = some d ∧ c ≠ d := by
  classical
  have H : ∃ n, v.get? n ≠ w.get? n := by
    by_contra! h
    exact hne (ext_get? h)
  let n := Nat.find H
  have hn := Nat.find_spec H
  have he : v.take n = w.take n := take_eq_of_get?_eq fun k hk => by
    aesop
  have hh := hlen n
  refine ⟨n, ?_⟩
  change v.get? n ≠ w.get? n at hn
  cases hc : v.get? n <;> cases hd : w.get? n <;> simp_all

/-! ## Convergence of words -/

theorem eventually_eq_letter {α : Type*} {l : Filter α} {a : α → ℕ → Fin N} {w : ℕ → Fin N}
    (h : Tendsto a l (𝓝 w)) (n : ℕ) : ∀ᶠ k in l, a k n = w n := by
  simp_all [tendsto_pi_nhds]

end Word

end AnalyticESC
