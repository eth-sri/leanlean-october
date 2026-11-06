module

public import Chazelle.Core.Lemma41Ram12

/-!
# WP-J, part 21: the cost of the merge tree, combinatorially

With `F, G, H` monotone and every merge at granularity `≤ Gλ`, one merge of nodes `x, y` costs at
most `(kb x + kb y + 1) · φ` (`pairCost_le`), where `φ = κ(4) F(Gλ) G(Gλ) (H(Gλ) + ⌈log₂(L+1)⌉ + 1)`.
The chord bounds `kb` of a level split into the leaves (granularity `≤ G₀`; these form a sublist
of the leaves of the first level, `leaves_pairUp_sublist`) and the merged nodes (granularity
`> G₀`, so `kb ≤ 60 (2m + 7) / (G₀ + 1)`).  Hence every level costs at most `lb` and the tree at
most `⌈log₂ j⌉ (lb + 2)` (`totCost_le`).
-/

namespace Chazelle.Core.L41

open Finset

@[expose] public section

/-- A leaf of the merge tree: granularity at most `G₀`. -/
def leafP (G0 : ℕ) (x : Shp) : Bool := decide (x.2.2 ≤ G0)

/-- The cost factor of one merge. -/
def phiL (κ F G H : ℕ → ℕ) (Gl L : ℕ) : ℕ :=
  κ 4 * F Gl * G Gl * (H Gl + Nat.clog 2 (L + 1) + 1)

/-- The cost bound of one level. -/
def lvBound (κ F G H : ℕ → ℕ) (Gl G0 J L LS0 : ℕ) : ℕ :=
  phiL κ F G H Gl L * (LS0 + (120 * L + 420 * J) / (G0 + 1) + J) + 344 * J + 40

theorem sum_range_nd (f : Shp → ℕ) : ∀ ns : List Shp,
    ∑ k ∈ range ns.length, f (nd ns k) = (ns.map f).sum
  | [] => by simp
  | a :: l => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [nd_cons_succ, nd_cons_zero]
    rw [sum_range_nd f l]; ring

theorem sum_pairs (g : ℕ → ℕ) : ∀ p : ℕ,
    ∑ q ∈ range p, (g (2 * q) + g (2 * q + 1)) = ∑ k ∈ range (2 * p), g k
  | 0 => by simp
  | p + 1 => by
    rw [Finset.sum_range_succ, sum_pairs g p, show 2 * (p + 1) = 2 * p + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ]; ring

theorem sublist_sum_le {l₁ l₂ : List ℕ} (h : l₁.Sublist l₂) : l₁.sum ≤ l₂.sum := by
  induction h with
  | slnil => simp
  | cons a _ ih => simp only [List.sum_cons]; omega
  | cons_cons a _ ih => simp only [List.sum_cons]; omega

/-- Two entries weigh at most the total. -/
theorem pair_le_sum (ns : List Shp) {q : ℕ} (hq : q < ns.length / 2) :
    (nd ns (2 * q)).2.1 + (nd ns (2 * q + 1)).2.1 ≤ (ns.map fun x => x.2.1).sum := by
  rw [← sum_range_nd]
  have hsub : ({2 * q, 2 * q + 1} : Finset ℕ) ⊆ range ns.length := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_range]; omega
  have := Finset.sum_le_sum_of_subset (f := fun k => (nd ns k).2.1) hsub
  rw [Finset.sum_pair (by omega)] at this
  exact this

/-- **One merge.** -/
theorem pairCost_le (κ F G H : ℕ → ℕ) (hF : Monotone F) (hG : Monotone G) (hH : Monotone H)
    (ns : List Shp) {γ₀ Gl q : ℕ} (hq : q < ns.length / 2) (hγ : γ₀ + fuseLoss ≤ Gl) :
    pairCost κ F G H ns γ₀ q ≤ (kb (nd ns (2 * q)) + kb (nd ns (2 * q + 1)) + 1) *
      phiL κ F G H Gl (ns.map fun x => x.2.1).sum := by
  unfold pairCost mergeCostV phiL
  have h1 := hF hγ; have h2 := hG hγ; have h3 := hH hγ
  have h4 := Nat.clog_mono_right 2 (Nat.add_le_add_right (pair_le_sum ns hq) 1)
  calc κ 4 * (kb (nd ns (2 * q)) + kb (nd ns (2 * q + 1)) + 1) * F (γ₀ + fuseLoss) *
        G (γ₀ + fuseLoss) * (H (γ₀ + fuseLoss) +
          Nat.clog 2 ((nd ns (2 * q)).2.1 + (nd ns (2 * q + 1)).2.1 + 1) + 1)
      ≤ κ 4 * (kb (nd ns (2 * q)) + kb (nd ns (2 * q + 1)) + 1) * F Gl * G Gl *
        (H Gl + Nat.clog 2 ((ns.map fun x => x.2.1).sum + 1) + 1) := by gcongr
    _ = _ := by ring

/-- **One level.** -/
theorem lvCost_le (κ F G H : ℕ → ℕ) (hF : Monotone F) (hG : Monotone G) (hH : Monotone H)
    (ns : List Shp) {γ₀ Gl : ℕ} (hγ : γ₀ + fuseLoss ≤ Gl) :
    lvCost κ F G H ns γ₀ ≤ phiL κ F G H Gl (ns.map fun x => x.2.1).sum *
      ((ns.map kb).sum + ns.length) + 344 * ns.length + 40 := by
  set Φ := phiL κ F G H Gl (ns.map fun x => x.2.1).sum with hΦ
  set p := ns.length / 2 with hp
  have h1 : ∑ q ∈ range p, (pairCost κ F G H ns γ₀ q + 331) ≤
      ∑ q ∈ range p, ((kb (nd ns (2 * q)) + kb (nd ns (2 * q + 1))) * Φ + (Φ + 331)) :=
    Finset.sum_le_sum fun q hq => by
      have := pairCost_le κ F G H hF hG hH ns (Finset.mem_range.mp hq) hγ
      rw [← hΦ] at this
      nlinarith
  have h2 : ∑ q ∈ range p, ((kb (nd ns (2 * q)) + kb (nd ns (2 * q + 1))) * Φ + (Φ + 331)) =
      (∑ k ∈ range (2 * p), kb (nd ns k)) * Φ + p * (Φ + 331) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_pairs (fun k => kb (nd ns k)),
      Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h3 : ∑ k ∈ range (2 * p), kb (nd ns k) ≤ (ns.map kb).sum := by
    rw [← sum_range_nd]
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
  have h4 : (∑ k ∈ range (2 * p), kb (nd ns k)) * Φ ≤ (ns.map kb).sum * Φ :=
    Nat.mul_le_mul_right _ h3
  have h5 : p * (Φ + 331) ≤ ns.length * Φ + 331 * ns.length := by
    have : p ≤ ns.length := by omega
    nlinarith
  unfold lvCost
  rw [← hp]
  have h6 : 13 * ((ns.length + 1) / 2) ≤ 13 * ns.length := by omega
  have h7 : Φ * ((ns.map kb).sum + ns.length) = (ns.map kb).sum * Φ + ns.length * Φ := by ring
  omega

theorem kb_split (G0 : ℕ) : ∀ ns : List Shp, (ns.map kb).sum =
    ((ns.filter (leafP G0)).map kb).sum + ((ns.filter fun x => !leafP G0 x).map kb).sum
  | [] => by simp
  | a :: l => by
    rw [List.filter_cons, List.filter_cons, List.map_cons, List.sum_cons, kb_split G0 l]
    cases leafP G0 a <;> simp <;> ring

theorem sum_lin : ∀ ns : List Shp, (ns.map fun x => 60 * (2 * x.2.1 + 7)).sum =
    120 * (ns.map fun x => x.2.1).sum + 420 * ns.length
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, sum_lin l]; ring

/-- The merged nodes. -/
theorem nonleaf_le (G0 : ℕ) : ∀ ns : List Shp, (∀ x ∈ ns, leafP G0 x = false → G0 + 1 ≤ x.2.2) →
    ((ns.filter fun x => !leafP G0 x).map kb).sum ≤
      (ns.map fun x => 60 * (2 * x.2.1 + 7)).sum / (G0 + 1)
  | [], _ => by simp
  | a :: l, h => by
    have ih := nonleaf_le G0 l fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    have hsplit : 60 * (2 * a.2.1 + 7) / (G0 + 1) + (l.map fun x => 60 * (2 * x.2.1 + 7)).sum / (G0 + 1)
        ≤ (60 * (2 * a.2.1 + 7) + (l.map fun x => 60 * (2 * x.2.1 + 7)).sum) / (G0 + 1) :=
      Nat.div_add_div_le_add_div
    cases hl : leafP G0 a
    · simp only [Bool.not_false, ite_true, List.map_cons, List.sum_cons]
      have ha := h a List.mem_cons_self hl
      have hk : kb a ≤ 60 * (2 * a.2.1 + 7) / (G0 + 1) := Nat.div_le_div_left ha (by omega)
      omega
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      have : (l.map fun x => 60 * (2 * x.2.1 + 7)).sum / (G0 + 1) ≤
          (60 * (2 * a.2.1 + 7) + (l.map fun x => 60 * (2 * x.2.1 + 7)).sum) / (G0 + 1) :=
        Nat.div_le_div_right (by omega)
      omega

/-- The leaves of the next level are leaves of this one. -/
theorem leaves_pairUp_sublist {G0 t : ℕ} (ht : G0 < t) : ∀ ns : List Shp,
    ((pairUp ns t).filter (leafP G0)).Sublist (ns.filter (leafP G0))
  | [] => by simp [pairUp]
  | [a] => by simp [pairUp]
  | a :: b :: rest => by
    have ih := leaves_pairUp_sublist ht rest
    have hm : leafP G0 (a.1, a.2.1 + b.2.1, t) = false := by
      unfold leafP; simp only [decide_eq_false_iff_not]; omega
    simp only [pairUp, List.filter_cons, hm, Bool.false_eq_true, ite_false]
    refine ih.trans ?_
    have h1 : rest.Sublist (a :: b :: rest) :=
      (List.sublist_cons_self b rest).trans (List.sublist_cons_self a _)
    have := h1.filter (leafP G0)
    simpa [List.filter_cons] using this

theorem mem_pairUp {t : ℕ} : ∀ {ns : List Shp} {x : Shp}, x ∈ pairUp ns t → x ∈ ns ∨ x.2.2 = t
  | [], _, h => by simp [pairUp] at h
  | [_], _, h => by simp [pairUp] at h; simp [h]
  | a :: b :: rest, x, h => by
    simp only [pairUp, List.mem_cons] at h
    rcases h with h | h
    · right; rw [h]
    · rcases mem_pairUp h with h' | h'
      · left; simp [h']
      · right; exact h'

/-- The invariant of the cost analysis along the levels. -/
def PInv (G0 Gl J L LS0 : ℕ) (ns : List Shp) (γ₀ : ℕ) : Prop :=
  1 ≤ ns.length ∧ ns.length ≤ J ∧ (ns.map fun x => x.2.1).sum = L ∧
    γ₀ + Nat.clog 2 ns.length ≤ Gl ∧ G0 ≤ γ₀ ∧ ((ns.filter (leafP G0)).map kb).sum ≤ LS0 ∧
    ∀ x ∈ ns, leafP G0 x = false → G0 + 1 ≤ x.2.2

/-- **The cost of the merge tree.** -/
theorem totCost_le (κ F G H : ℕ → ℕ) (hF : Monotone F) (hG : Monotone G) (hH : Monotone H)
    {G0 Gl J L LS0 : ℕ} : ∀ (f : ℕ) (ns : List Shp) (γ₀ : ℕ), ns.length ≤ f →
    PInv G0 Gl J L LS0 ns γ₀ →
    totCost κ F G H Gl f ns γ₀ ≤ Nat.clog 2 ns.length * (lvBound κ F G H Gl G0 J L LS0 + 2) := by
  intro f
  induction f with
  | zero => intro ns γ₀ hf h; have := h.1; omega
  | succ f ih =>
    intro ns γ₀ hf h
    obtain ⟨h1, hJ, hL, hcl, hG0, hLS, hnl⟩ := h
    by_cases hlen : ns.length ≤ 1
    · rw [totCost, ite_eq_left hlen]; exact Nat.zero_le _
    · have hj2 : 2 ≤ ns.length := by omega
      set t := lvTgt Gl ns.length γ₀ with ht
      have hcl2 := clog_half hj2
      have hfl : fuseLoss = 1 := rfl
      have htγ : γ₀ + 1 ≤ t := by rw [ht]; unfold lvTgt; split_ifs <;> omega
      rw [totCost, ite_eq_right hlen]
      rw [← ht]
      -- this level
      have hlv := lvCost_le κ F G H hF hG hH ns (γ₀ := γ₀) (Gl := Gl) (by omega)
      rw [hL] at hlv
      have hkb : (ns.map kb).sum ≤ LS0 + (120 * L + 420 * J) / (G0 + 1) := by
        rw [kb_split G0 ns]
        have := nonleaf_le G0 ns hnl
        rw [sum_lin, hL] at this
        have : (120 * L + 420 * ns.length) / (G0 + 1) ≤ (120 * L + 420 * J) / (G0 + 1) :=
          Nat.div_le_div_right (by omega)
        omega
      have hlvb : lvCost κ F G H ns γ₀ ≤ lvBound κ F G H Gl G0 J L LS0 := by
        unfold lvBound
        have : phiL κ F G H Gl L * ((ns.map kb).sum + ns.length) ≤
            phiL κ F G H Gl L * (LS0 + (120 * L + 420 * J) / (G0 + 1) + J) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      -- the next level
      have hlen' : (pairUp ns t).length = (ns.length + 1) / 2 := pairUp_length ns t
      have hinv : PInv G0 Gl J L LS0 (pairUp ns t) t := by
        refine ⟨by omega, by omega, by rw [pairUp_sum]; exact hL, ?_, by omega,
          le_trans (sublist_sum_le ((leaves_pairUp_sublist (by omega) ns).map kb)) hLS,
          fun x hx hxl => ?_⟩
        · rw [hlen', ht]; unfold lvTgt; split_ifs with h3
          · rw [show (ns.length + 1) / 2 = 1 by omega, Nat.clog_one_right]; omega
          · omega
        · rcases mem_pairUp hx with h' | h'
          · exact hnl x h' hxl
          · omega
      have := ih (pairUp ns t) t (by omega) hinv
      rw [hlen'] at this
      rw [hcl2]
      nlinarith

end

end Chazelle.Core.L41
