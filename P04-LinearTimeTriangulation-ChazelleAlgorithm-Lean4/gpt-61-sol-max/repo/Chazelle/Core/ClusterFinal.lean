module

public import Chazelle.Core.ClusterFlagH

/-!
# WP-I, part 64: the final state — clusters and the size of `D*`

* `reach_items`: at the end of the driver (empty stack), a reachability through unflagged
  vertices stays in one finished segment; `class_card`: a class of an exact labelling of the
  reachability has at most `s` vertices;
* `H_card`: the light levels of the least frequent residue hold at most `μ / k'` vertices;
* `dstar_bound`: `|D| + |H| ≤ 7 k²`.
-/

namespace Chazelle.Core.Cluster

open Machine Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

section reach

variable {μ k s : ℕ} {H : Finset ℕ} {slab : ℕ → ℕ} {Adj : ℕ → ℕ → Prop} {act : ℕ → ℕ}
  {fin : Finset (ℕ × ℕ)} {D : Finset ℕ} {nsp : ℕ}

section
variable {G : Env} (hI : SInv μ k s H slab Adj act [] fin D nsp) (hstep : ∀ u w, G.Step u w → Adj u w ∧ u ∉ H ∧ u ∉ D ∧ w ∉ H ∧ w ∉ D)
include hI hstep
/-- **Reachability stays in a finished segment.** -/
theorem reach_items
    {p : ℕ × ℕ} (hp : p ∈ fin) {x y : ℕ} (hx : x ∈ items act p) (hr : G.Reach x y) :
    y ∈ items act p := by
  induction hr with
  | refl => exact hx
  | tail _ hst ih =>
    rename_i b c'
    obtain ⟨hadj, h1, h2, h3, h4⟩ := hstep _ _ hst
    obtain ⟨q, hq, hbq, hcq⟩ := hI.edge _ _ hadj h1 h2 h3 h4
    by_cases hqp : q = p
    · simp_all
    · exact absurd (Finset.disjoint_left.mp (hI.disj q p hq (Or.inr hp) hqp) hbq) (not_not.mpr ih)

/-- **A label class has at most `s` vertices.** -/
theorem class_card
    {lab : ℕ → ℕ} {X : Finset ℕ} (hX : ∀ v ∈ X, v < μ ∧ v ∉ H ∧ v ∉ D)
    (hlab : ∀ x ∈ X, ∀ y ∈ X, lab x = lab y → G.Reach x y) (l : ℕ) :
    (X.filter (fun v => lab v = l)).card ≤ s := by
  by_cases hne : (X.filter (fun v => lab v = l)).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    simp only [Finset.mem_filter] at hx0
    obtain ⟨hμ0, hH0, hD0⟩ := hX x0 hx0.1
    obtain ⟨p, hp, hxp⟩ := hI.cover x0 hμ0 hH0 hD0
    have hpf : p ∈ fin := hp.resolve_left (by simp)
    have hsub : X.filter (fun v => lab v = l) ⊆ items act p := fun v hv => by
      simp only [Finset.mem_filter] at hv
      exact reach_items hI hstep hpf hxp (hlab x0 hx0.1 v hv.1 (hx0.2.trans hv.2.symm))
    calc _ ≤ (items act p).card := Finset.card_le_card hsub
      _ = len p := items_card (hI.inj p hp)
      _ ≤ s := hI.small p hpf
  simp_all


end

end reach

/-- The light residue. -/
theorem mod_light {l k ρ : ℕ} (hk : 0 < k) (hρ : ρ < k) :
    (l + (k - 1 - ρ)) % k = k - 1 ↔ l % k = ρ := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show k - 1 - ρ < k by omega)]
  have h := Nat.mod_lt l hk
  generalize l % k = r at h ⊢
  by_cases hr : r + (k - 1 - ρ) < k
  · rw [Nat.mod_eq_of_lt hr]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- **The least frequent residue class is small.** -/
theorem minres_card {μ k ρ : ℕ} {f : ℕ → ℕ} (_hk : 0 < k) (hf : ∀ v, v < μ → f v < k)
    (hmin : ∀ r, r < k → cntBelow f μ ρ ≤ cntBelow f μ r) : k * cntBelow f μ ρ ≤ μ := by
  have hsum : ∑ r ∈ Finset.range k, cntBelow f μ r = μ := by
    rw [sum_cntBelow]; unfold cntLt
    rw [Finset.filter_true_of_mem (fun v hv => hf v (Finset.mem_range.mp hv))]; simp
  calc k * cntBelow f μ ρ = ∑ _r ∈ Finset.range k, cntBelow f μ ρ := by simp
    _ ≤ ∑ r ∈ Finset.range k, cntBelow f μ r :=
        Finset.sum_le_sum (fun r hr => hmin r (Finset.mem_range.mp hr))
    _ = μ := hsum

/-- **The size of `D*`.** -/
theorem dstar_bound {μ k k' s D H : ℕ} (hk : 1 ≤ k) (hμ : 0 < μ) (hμk : μ ≤ k ^ 3)
    (hk' : k' = min k μ) (hs : s = min (k' * k') μ) (hD : s * D ≤ 6 * k' * μ)
    (hH : k' * H ≤ μ) : D + H ≤ 7 * k ^ 2 := by
  rcases Nat.le_total k μ with hkμ | hkμ
  · have e : k' = k := by omega
    subst e
    have hH' : H ≤ k' ^ 2 := by
      have : k' * H ≤ k' * k' ^ 2 := by
        ring_nf <;> omega
      exact Nat.le_of_mul_le_mul_left this (by omega)
    have hD' : D ≤ 6 * k' ^ 2 := by
      rcases Nat.le_total (k' * k') μ with h | h
      · rw [hs, min_eq_left h] at hD
        have : k' * k' * D ≤ k' * k' * (6 * k' ^ 2) := by
          calc k' * k' * D ≤ 6 * k' * μ := hD
            _ ≤ 6 * k' * k' ^ 3 := Nat.mul_le_mul_left _ hμk
            _ = k' * k' * (6 * k' ^ 2) := by ring
        exact Nat.le_of_mul_le_mul_left this (Nat.mul_pos (by omega) (by omega))
      · rw [hs, min_eq_right h] at hD
        have : μ * D ≤ μ * (6 * k') := by
          grind
        have := Nat.le_of_mul_le_mul_left this hμ
        have : k' ≤ k' ^ 2 := by nlinarith
        omega
    omega
  · have e : k' = μ := by omega
    subst e
    have hs' : s = k' := by rw [hs]; exact min_eq_right (Nat.le_mul_of_pos_left _ hμ)
    rw [hs'] at hD
    have hD' : D ≤ 6 * k' := by
      have : k' * D ≤ k' * (6 * k') := by
        grind
      exact Nat.le_of_mul_le_mul_left this hμ
    have hH' : H ≤ 1 := by
      have : k' * H ≤ k' * 1 := by omega
      exact Nat.le_of_mul_le_mul_left this hμ
    have : k ≤ k ^ 2 := by nlinarith
    omega

/-- The cluster size is at most `k²`. -/
theorem s_le_sq {μ k k' s : ℕ} (hk' : k' = min k μ) (hs : s = min (k' * k') μ) : s ≤ k ^ 2 := by
  have h1 : k' ≤ k := by omega
  have h2 : s ≤ k' * k' := by omega
  have : k' * k' ≤ k * k := Nat.mul_le_mul h1 h1
  grind [sq]

end

end Chazelle.Core.Cluster
