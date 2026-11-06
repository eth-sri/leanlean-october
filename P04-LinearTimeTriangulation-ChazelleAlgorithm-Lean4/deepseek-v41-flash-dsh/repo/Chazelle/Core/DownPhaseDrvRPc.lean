module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseMathJunc

/-!
# Down-phase driver (RAM side): the leaves of a region chain

The canonical map of a region chain `C_R = ⟨H.poly Q, 0, #points - 1⟩` is built by merging
*leaves* (portions of the runs of `Q` vertices of the host `H`, computed by Lemma 4.1 or brute
force) and *connectors* (the host pieces between leaves, empty maps).  A leaf of a run item
`.run a ℓ` at host offset `p` avoids the first and the last point of the run (so every junction
of a merge is a run-interior vertex, the padding rule M2 of `DownMath.sharedGeneric_run`), does
not contain the wrap-around edge `v_{n-1} v_0`, and has at most `C` edges.

* `chunks C s a L`: the segment of `L` edges from host point `s` (`Q` vertex `a`) in pieces of at
  most `C` edges;
* `runLeaves n C p a ℓ`: the leaves of a run item at host offset `p`;
* `hostLeaves n C p H`: all leaves of a host whose first point has offset `p`.

Leaves are triples `(s, len, a)`: host start, number of edges, `Q` start.
-/

namespace Chazelle.Core

namespace DrvR

@[expose] public section

/-- The segment of `L` edges from host point `s` (`Q` vertex `a`) in pieces of at most `C`
edges. -/
def chunks (C : ℕ) (s a L : ℕ) : List (ℕ × ℕ × ℕ) :=
  if L = 0 then [] else if L ≤ C ∨ C = 0 then [(s, L, a)]
  else (s, C, a) :: chunks C (s + C) (a + C) (L - C)
termination_by L
decreasing_by omega

/-- The leaves of a run item `.run a ℓ` at host offset `p`: the interior points `1 … ℓ - 1`,
split at the wrap-around of the `Q` indices. -/
def runLeaves (n C p a ℓ : ℕ) : List (ℕ × ℕ × ℕ) :=
  if ℓ < 3 then [] else
    if (a + 1) % n + (ℓ - 2) ≤ n - 1 then chunks C (p + 1) ((a + 1) % n) (ℓ - 2)
    else chunks C (p + 1) ((a + 1) % n) (n - 1 - (a + 1) % n) ++
      chunks C (p + 1 + (n - (a + 1) % n)) 0 (ℓ - 2 - (n - (a + 1) % n))

/-- The leaves of a host whose first point has offset `p`. -/
def hostLeaves (n C : ℕ) : ℕ → Host → List (ℕ × ℕ × ℕ)
  | _, [] => []
  | p, .run a ℓ :: H => runLeaves n C p a ℓ ++ hostLeaves n C (p + ℓ + 1) H
  | p, .pt _ :: H => hostLeaves n C (p + 1) H

/-! ## Chunks -/

theorem chunks_zero (C s a : ℕ) : chunks C s a 0 = [] := by
  rw [chunks]; simp

theorem chunks_le {C s a L : ℕ} (h0 : L ≠ 0) (h : L ≤ C ∨ C = 0) :
    chunks C s a L = [(s, L, a)] := by
  Ξ chunks, ite_eq_right h0, ite_eq_left h

theorem chunks_gt {C s a L : ℕ} (h0 : L ≠ 0) (h : C < L) (hC : C ≠ 0) :
    chunks C s a L = (s, C, a) :: chunks C (s + C) (a + C) (L - C) := by
  rw [chunks, ite_eq_right h0, ite_eq_right (⋄)]

/-- The pieces of a segment: inside it, nonempty, at most `C` edges, `Q` start shifted like the
host start. -/
theorem mem_chunks {C : ℕ} (hC : 1 ≤ C) : ∀ (L s a : ℕ) (x : ℕ × ℕ × ℕ), x ∈ chunks C s a L →
    s ≤ x.1 ∧ x.1 + x.2.1 ≤ s + L ∧ 1 ≤ x.2.1 ∧ x.2.1 ≤ C ∧ x.2.2 + s = a + x.1 := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro s a x hx
    by_cases h0 : L = 0
    · rw [h0, chunks_zero] at hx; simp at hx
    by_cases hle : L ≤ C
    · rw [chunks_le h0 (Or.inl hle)] at hx
      simp only [List.mem_singleton] at hx
      subst hx; dsimp only; omega
    · rw [chunks_gt h0 (⋄) (by omega)] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · dsimp only; omega
      · have := ih (L - C) (⋄) (s + C) (a + C) x hx
        omega

/-- The number of pieces of a segment. -/
theorem chunks_length {C : ℕ} (hC : 1 ≤ C) : ∀ (L s a : ℕ), (chunks C s a L).length * C ≤ L + C - 1 := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro s a
    by_cases h0 : L = 0
    · rw [h0, chunks_zero]; simp
    by_cases hle : L ≤ C
    · rw [chunks_le h0 (Or.inl hle)]; simp; omega
    · rw [chunks_gt h0 (⋄) (by omega)]
      have := ih (L - C) (⋄) (s + C) (a + C)
      ϴ List.length_cons, Nat.succ_mul
      omega

/-! ## Leaves of a run -/

/-- **A leaf of the run item `.run a ℓ` at host offset `q`**: strictly inside the run, nonempty,
at most `C` edges, no wrap-around, and its `Q` start is the run vertex at its host start. -/
def LeafIn (n C q a ℓ : ℕ) (x : ℕ × ℕ × ℕ) : Prop :=
  q + 1 ≤ x.1 ∧ x.1 + x.2.1 + 1 ≤ q + ℓ ∧ 1 ≤ x.2.1 ∧ x.2.1 ≤ C ∧ x.2.2 + x.2.1 + 1 ≤ n ∧
    x.2.2 = (a + (x.1 - q)) % n

/-- A piece of a segment of the run interior is a leaf. -/
theorem leafIn_of_seg {n C p a ℓ s0 u L : ℕ} (hC : 1 ≤ C) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ chunks C s0 u L) (hs0 : p + 1 ≤ s0) (hend : s0 + L + 1 ≤ p + ℓ)
    (hnu : u + L + 1 ≤ n) (hmod : u = (a + (s0 - p)) % n) : LeafIn n C p a ℓ x := by
  obtain ⟨h1, h2, h4, h5, h6⟩ := mem_chunks hC _ _ _ x hx
  refine ⟨by omega, by omega, h4, h5, by omega, ?_⟩
  have e : x.2.2 = u + (x.1 - s0) := by omega
  rw [e, show a + (x.1 - p) = a + (s0 - p) + (x.1 - s0) by omega, ← Nat.mod_add_mod, ← hmod,
    Nat.mod_eq_of_lt (by omega)]

theorem mem_runLeaves {n C p a ℓ : ℕ} (hC : 1 ≤ C) (hn : 1 ≤ n) (hℓ : ℓ < n) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ runLeaves n C p a ℓ) : LeafIn n C p a ℓ x := by
  have hu : (a + 1) % n < n := Nat.mod_lt _ (by omega)
  have hq := Nat.mod_add_div (a + 1) n
  unfold runLeaves at hx
  split_ifs at hx with h3 hw
  · simp at hx
  · exact leafIn_of_seg hC hx (le_refl _) (by omega) (by omega)
      (by rw [show a + (p + 1 - p) = a + 1 by omega])
  · rcases List.mem_append.1 hx with hx | hx
    · exact leafIn_of_seg hC hx (le_refl _) (by omega) (by omega)
        (by rw [show a + (p + 1 - p) = a + 1 by omega])
    · refine leafIn_of_seg hC hx (by omega) (by omega) (by omega) ?_
      rw [show a + (p + 1 + (n - (a + 1) % n) - p) = 0 + n * ((a + 1) / n + 1) by
        rw [Nat.mul_add, Nat.mul_one]; omega, Nat.add_mul_mod_self_left, Nat.zero_mod]

/-! ## Leaves of a host -/

theorem mem_hostLeaves {n C : ℕ} (hC : 1 ≤ C) (hn : 1 ≤ n) : ∀ (H : Host) (p : ℕ),
    HostWF n H → ∀ x ∈ hostLeaves n C p H, ∃ H₁ a ℓ H₂, H = H₁ ++ HostItem.run a ℓ :: H₂ ∧
      LeafIn n C (p + (H₁.pts n).length) a ℓ x
  | [], p, _, x, hx => by simp [hostLeaves] at hx
  | .run a ℓ :: H, p, hwf, x, hx => by
    rw [hostLeaves, List.mem_append] at hx
    have hit := hwf (.run a ℓ) (List.mem_cons_self ..)
    simp only at hit
    have hwf' : HostWF n H := fun it h => hwf it (List.mem_cons_of_mem _ h)
    rcases hx with hx | hx
    · exact ⟨[], a, ℓ, H, rfl, by simpa [Host.pts] using mem_runLeaves hC hn hit.2 hx⟩
    · obtain ⟨H₁, a', ℓ', H₂, e, hL⟩ := mem_hostLeaves hC hn H (p + ℓ + 1) hwf' x hx
      refine ⟨HostItem.run a ℓ :: H₁, a', ℓ', H₂, by rw [e]; rfl, ?_⟩
      rw [DownMath.pts_cons, List.length_append, DownMath.run_pts_length]
      rwa [show p + (ℓ + 1 + (H₁.pts n).length) = p + ℓ + 1 + (H₁.pts n).length by omega]
  | .pt y :: H, p, hwf, x, hx => by
    rw [hostLeaves] at hx
    have hwf' : HostWF n H := fun it h => hwf it (List.mem_cons_of_mem _ h)
    obtain ⟨H₁, a', ℓ', H₂, e, hL⟩ := mem_hostLeaves hC hn H (p + 1) hwf' x hx
    refine ⟨HostItem.pt y :: H₁, a', ℓ', H₂, by rw [e]; rfl, ?_⟩
    rw [DownMath.pts_cons, List.length_append]
    rwa [show ((HostItem.pt y).pts n).length = 1 from rfl,
      show p + (1 + (H₁.pts n).length) = p + 1 + (H₁.pts n).length by omega]

end

end DrvR

end Chazelle.Core
