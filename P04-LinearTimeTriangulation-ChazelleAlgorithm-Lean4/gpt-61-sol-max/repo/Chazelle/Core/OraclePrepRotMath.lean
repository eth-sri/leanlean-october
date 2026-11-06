module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.OraclePrepGraph

/-!
# Lemma 3.6 (WP-H), preprocessing part 18: the rotation from the sorted darts

Darts `d < M` with vertex `G d` and key `K d`, listed by a sequence `s` (a bijection of
`[0, M)`) in strictly increasing lexicographic order of `(G, K)`.  `rotN`: the next dart of the
sequence if it has the same vertex, else the first dart of the vertex (`fpN`).  `rotN_spec`: it is
the next dart around the vertex in key order, cyclically (the characterisation of
`OracleBook.csucc`).
-/

namespace Chazelle.Core

namespace OracleR

@[expose] public section

/-- Strict lexicographic order of pairs. -/
def PLt (x y : ℕ × ℕ) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

variable (M : ℕ) (G K s : ℕ → ℕ)

/-- The sequence is a sorted enumeration of the darts. -/
structure SortedDarts : Prop where
  lt : ∀ t, t < M → s t < M
  surj : ∀ d, d < M → ∃ t, t < M ∧ s t = d
  sorted : ∀ t t', t < t' → t' < M → PLt (G (s t), K (s t)) (G (s t'), K (s t'))

open Classical in
/-- The first position of vertex `v` in the sequence. -/
noncomputable def fpN (v : ℕ) : ℕ :=
  if h : ∃ t, t < M ∧ G (s t) = v then Nat.find h else 0

open Classical in
/-- **The rotation at position `t`.** -/
noncomputable def rotN (t : ℕ) : ℕ :=
  if t + 1 < M ∧ G (s (t + 1)) = G (s t) then s (t + 1) else s (fpN M G s (G (s t)))

variable {M G K s}

theorem fpN_spec (_h : SortedDarts M G K s) {t : ℕ} (ht : t < M) :
    fpN M G s (G (s t)) < M ∧ G (s (fpN M G s (G (s t)))) = G (s t) ∧
      ∀ t', t' < M → G (s t') = G (s t) → fpN M G s (G (s t)) ≤ t' := by
  classical
  have hex : ∃ t', t' < M ∧ G (s t') = G (s t) := ⟨t, ht, rfl⟩
  unfold fpN
  rw [dite_eq_left hex]
  obtain ⟨a, b⟩ := Nat.find_spec hex
  exact ⟨a, b, fun t' ht' e => Nat.find_min' hex ⟨ht', e⟩⟩

section
variable (h : SortedDarts M G K s)
include h
/-- Positions are ordered like the pairs. -/
theorem pos_lt_of {t t' : ℕ} (ht : t < M) (_ht' : t' < M)
    (hp : PLt (G (s t), K (s t)) (G (s t'), K (s t'))) : t < t' := by
  by_contra hc
  rcases eq_or_lt_of_le (not_lt.1 hc) with e | e
  · simp_all [PLt] <;> omega_nf
  · have := h.sorted t' t e ht
    simp_all [PLt] <;> omega_nf

/-- **The rotation is the cyclic successor in key order.** -/
theorem rotN_spec {t : ℕ} (ht : t < M) :
    rotN M G s t < M ∧ G (rotN M G s t) = G (s t) ∧
      ((K (s t) < K (rotN M G s t) ∧ ∀ f, f < M → G f = G (s t) → K (s t) < K f →
          K (rotN M G s t) ≤ K f) ∨
        ((∀ f, f < M → G f = G (s t) → K f ≤ K (s t)) ∧
          ∀ f, f < M → G f = G (s t) → K (rotN M G s t) ≤ K f)) := by
  unfold rotN
  split_ifs with hn
  · obtain ⟨h1, h2⟩ := hn
    refine ⟨h.lt _ h1, h2, Or.inl ⟨?_, fun f hf hg hk => ?_⟩⟩
    · have := h.sorted t (t + 1) (by omega) h1
      simp_all [PLt] <;> omega_nf
    · obtain ⟨t', ht', rfl⟩ := h.surj f hf
      have hlt : t < t' := pos_lt_of h ht ht' (Or.inr ⟨hg.symm, hk⟩)
      rcases eq_or_lt_of_le (show t + 1 ≤ t' by omega) with e | e
      · simp_all
      · have := h.sorted (t + 1) t' e ht'
        simp_all [PLt] <;> omega_nf
  · obtain ⟨f1, f2, f3⟩ := fpN_spec h ht
    refine ⟨h.lt _ f1, f2, Or.inr ⟨fun f hf hg => ?_, fun f hf hg => ?_⟩⟩
    · obtain ⟨t', ht', rfl⟩ := h.surj f hf
      by_contra hc
      have hlt : t < t' := pos_lt_of h ht ht' (Or.inr ⟨hg.symm, by omega⟩)
      apply hn
      refine ⟨by omega, ?_⟩
      have a := h.sorted t (t + 1) (by omega) (by omega)
      rcases eq_or_lt_of_le (show t + 1 ≤ t' by omega) with e | e
      · simp_all
      · have b := h.sorted (t + 1) t' e ht'
        simp_all [PLt] <;> omega_nf
    · obtain ⟨t', ht', rfl⟩ := h.surj f hf
      have hle := f3 t' ht' hg
      rcases eq_or_lt_of_le hle with e | e
      · rw [e]
      · have := h.sorted _ t' e ht'
        simp_all [PLt] <;> omega_nf


end

end

end OracleR

end Chazelle.Core
