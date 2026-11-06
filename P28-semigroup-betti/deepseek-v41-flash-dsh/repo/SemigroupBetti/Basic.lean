/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

public import Mathlib

/-!
# Linear upper bounds for the first Betti number of four-generated numerical semigroups
-/

@[expose] public section

namespace SemigroupBetti

open Finset MvPolynomial

/-! ## Defs -/
/-- A subset of `Fin 4`. -/
abbrev F4 := Finset (Fin 4)

/-- An exponent vector. -/
abbrev Vec := Fin 4 → ℕ

abbrev K01 : F4 := {0, 1}
abbrev K02 : F4 := {0, 2}
abbrev K03 : F4 := {0, 3}
abbrev K12 : F4 := {1, 2}
abbrev K13 : F4 := {1, 3}
abbrev K23 : F4 := {2, 3}

/-- Generator data with the standing hypotheses `(H)`. -/
class GenData where
  (m a b w : ℕ)
  m_pos : 0 < m
  a_pos : 0 < a
  a_lt_b : a < b
  b_lt_w : b < w
  gcd_eq_one : Nat.gcd m (Nat.gcd a (Nat.gcd b w)) = 1

/-- Support `{i : zᵢ > 0}`. -/
def supp (z : Vec) : F4 := univ.filter (fun i => 0 < z i)

/-- Two vectors share a variable. -/
def SharesVar (z z' : Vec) : Prop := ∃ i, 0 < z i ∧ 0 < z' i

instance : DecidableRel SharesVar := fun z z' =>
  inferInstanceAs (Decidable (∃ i, 0 < z i ∧ 0 < z' i))

@[simp] lemma mem_supp {z : Vec} {i : Fin 4} : i ∈ supp z ↔ 0 < z i := by
  simp [supp]

lemma SharesVar.symm {z z' : Vec} (h : SharesVar z z') : SharesVar z' z := by
  obtain ⟨i, h1, h2⟩ := h; exact ⟨i, h2, h1⟩

variable [G : GenData] {d : ℕ}

abbrev m : ℕ := G.m
abbrev a : ℕ := G.a
abbrev b : ℕ := G.b
abbrev w : ℕ := G.w
lemma m_pos : 0 < m := G.m_pos
lemma a_pos : 0 < a := G.a_pos
lemma a_lt_b : a < b := G.a_lt_b
lemma b_lt_w : b < w := G.b_lt_w
lemma gcd_eq_one : Nat.gcd m (Nat.gcd a (Nat.gcd b w)) = 1 := G.gcd_eq_one

/-- The generator vector `n = (m, m+a, m+b, m+w)`. -/
def n : Vec := ![m, m + a, m + b, m + w]

/-- `g = gcd(a, gcd(b, w))`. -/
def g : ℕ := Nat.gcd a (Nat.gcd b w)

/-- `A = a / g`. -/
def A : ℕ := a / g
/-- `B = b / g`. -/
def B : ℕ := b / g
/-- `W = w / g` (normalized width). -/
def W : ℕ := w / g

/-- Degree `ν(z) = ∑ zᵢ nᵢ`. -/
def nu (z : Vec) : ℕ := ∑ i, z i * n i

@[simp] lemma n_zero : n 0 = m := rfl
@[simp] lemma n_one : n 1 = m + a := rfl
@[simp] lemma n_two : n 2 = m + b := rfl
@[simp] lemma n_three : n 3 = m + w := rfl

lemma nu_eq_sum (z : Vec) : nu z = z 0 * m + z 1 * (m + a) +
    z 2 * (m + b) + z 3 * (m + w) := by
  simp [nu, Fin.sum_univ_four]

lemma m_le_n (i : Fin 4) : m ≤ n i := by
  fin_cases i <;> simp [n]

lemma n_pos (i : Fin 4) : 0 < n i := m_pos.trans_le (m_le_n i)

lemma n_le_n_three (i : Fin 4) : n i ≤ n 3 := by
  have := a_pos; have := a_lt_b; have := b_lt_w
  fin_cases i <;> simp [n] <;> omega

/-! ### Additivity of `ν` -/

@[simp] lemma nu_zero : nu 0 = 0 := by simp [nu]

lemma nu_add (x y : Vec) : nu (x + y) = nu x + nu y := by
  simp [nu, add_mul, Finset.sum_add_distrib]

lemma nu_single (i : Fin 4) (k : ℕ) : nu (Pi.single i k) = k * n i := by
  simp only [nu, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ h; simp [h]
  · simp

/-- If `x ≤ y` coordinatewise then `ν(y) = ν(x) + ν(y - x)`. -/
lemma nu_sub {x y : Vec} (h : x ≤ y) : nu y = nu x + nu (y - x) := by
  simp only [nu, Pi.sub_apply, ← Finset.sum_add_distrib, ← add_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_sub_cancel' (h i)]

lemma single_le_nu (z : Vec) (i : Fin 4) : z i * n i ≤ nu z :=
  Finset.single_le_sum (f := fun j => z j * n j) (fun _ _ => Nat.zero_le _) (mem_univ i)

lemma nu_pos_of_pos {z : Vec} {i : Fin 4} (h : 0 < z i) : 0 < nu z :=
  (Nat.mul_pos h (n_pos i)).trans_le (single_le_nu z i)

/-! ### Lemma 1: normalized arithmetic -/

lemma g_dvd_a : g ∣ a := Nat.gcd_dvd_left _ _
lemma g_dvd_b : g ∣ b := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
lemma g_dvd_w : g ∣ w := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)

lemma g_pos : 0 < g := Nat.gcd_pos_of_pos_left _ a_pos

lemma a_eq : a = g * A := (Nat.mul_div_cancel' g_dvd_a).symm
lemma b_eq : b = g * B := (Nat.mul_div_cancel' g_dvd_b).symm
lemma w_eq : w = g * W := (Nat.mul_div_cancel' g_dvd_w).symm

lemma A_pos : 0 < A := by
  have h := a_pos; rw [a_eq] at h; exact Nat.pos_of_mul_pos_left h

lemma A_lt_B : A < B := by
  have h := a_lt_b; rw [a_eq, b_eq] at h; exact Nat.lt_of_mul_lt_mul_left h

lemma B_lt_W : B < W := by
  have h := b_lt_w; rw [b_eq, w_eq] at h; exact Nat.lt_of_mul_lt_mul_left h

lemma two_le_B : 2 ≤ B := by have := A_pos; have := A_lt_B; omega
lemma three_le_W : 3 ≤ W := by have := two_le_B; have := B_lt_W; omega
lemma two_le_W_sub_A : 2 ≤ W - A := by
  have := A_lt_B; have := B_lt_W; omega

lemma gcd_m_g : Nat.gcd g m = 1 := by rw [Nat.gcd_comm]; exact gcd_eq_one

lemma W_le_w : W ≤ w := by
  rw [w_eq]; exact Nat.le_mul_of_pos_left _ g_pos

/-! ## Fiber -/

/-! ### Definition 3: fibers -/

/-- The fiber `F_d = {z ∈ ℕ⁴ : ν(z) = d}`, enumerated inside the box `{0,…,d/m}⁴`. -/
def fiber (d : ℕ) : Finset (Vec) :=
  (Fintype.piFinset fun _ => range (d / m + 1)).filter (fun z => nu z = d)

lemma le_div_m_of_nu_eq {z : Vec} (h : nu z = d) (i : Fin 4) :
    z i ≤ d / m := by
  rw [Nat.le_div_iff_mul_le m_pos, mul_comm, ← h, mul_comm]
  exact (Nat.mul_le_mul_left _ (m_le_n i)).trans (single_le_nu z i)

@[simp] lemma mem_fiber {z : Vec} : z ∈ fiber d ↔ nu z = d := by
  simp only [fiber, mem_filter, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  intro h i; exact Nat.lt_succ_of_le (le_div_m_of_nu_eq h i)

lemma fiber_zero : fiber 0 = {0} := by
  ext z
  rw [mem_fiber, mem_singleton]
  exact ⟨fun h => by
    ext i
    have := single_le_nu z i
    rw [h] at this
    exact (Nat.mul_eq_zero.1 (Nat.le_zero.1 this)).resolve_right (n_pos i).ne',
    by rintro rfl; simp⟩

/-! ### Definition 3: the graph `∇_d` -/

/-- The factorization graph `∇_d` on the fiber: distinct factorizations sharing a variable. -/
def nabla (d : ℕ) : SimpleGraph (fiber d) where
  Adj z z' := z ≠ z' ∧ SharesVar z.1 z'.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (d : ℕ) : DecidableRel (nabla d).Adj := fun z z' =>
  inferInstanceAs (Decidable (z ≠ z' ∧ SharesVar z.1 z'.1))

/-- The type of connected components of `∇_d`. -/
abbrev Comp (d : ℕ) := (nabla d).ConnectedComponent

/-- The component of a vertex. -/
abbrev cmk (z : fiber d) : Comp d := (nabla d).connectedComponentMk z

/-- `c_d`: the number of connected components of `∇_d` (`0` when the fiber is empty). -/
def ncomp (d : ℕ) : ℕ := Fintype.card (Comp d)

/-- A degree contributes when `∇_d` has at least two components. -/
def contributes (d : ℕ) : Prop := 2 ≤ ncomp d

instance (d : ℕ) : Decidable (contributes d) := inferInstanceAs (Decidable (2 ≤ _))

/-- The explicit cutoff `H = n₃ (n₀+n₁+n₂+n₃)`. -/
def H : ℕ := n 3 * ∑ i, n i

/-- **Definition 3 (bounded form).** The combinatorial first Betti number
`β₁ = ∑_{d ≤ H} (c_d - 1)`. -/
def beta1 : ℕ := ∑ d ∈ range (H + 1), (ncomp d - 1)

/-- The support of a component: the union of the supports of its vertices. -/
noncomputable def compSupp (C : Comp d) : F4 := by
  classical
  exact univ.filter (fun i => ∃ z : fiber d, cmk z = C ∧ 0 < z.1 i)

lemma mem_compSupp {C : Comp d} {i : Fin 4} :
    i ∈ compSupp C ↔ ∃ z : fiber d, cmk z = C ∧ 0 < z.1 i := by
  classical
  unfold compSupp; simp

lemma supp_subset_compSupp (z : fiber d) :
    supp z.1 ⊆ compSupp (cmk z) := fun i hi =>
  mem_compSupp.2 ⟨z, rfl, mem_supp.1 hi⟩

/-! ### Basic graph facts -/

lemma reachable_of_sharesVar {z y : fiber d} (h : SharesVar z.1 y.1) :
    (nabla d).Reachable z y := by
  by_cases hzy : z = y
  · subst hzy; rfl
  · exact SimpleGraph.Adj.reachable ⟨hzy, h⟩

lemma ncomp_le_one_of_reachable (h : ∀ z y : fiber d, (nabla d).Reachable z y) :
    ncomp d ≤ 1 := by
  unfold ncomp
  rw [Fintype.card_le_one_iff_subsingleton]
  exact ⟨SimpleGraph.ConnectedComponent.ind₂ fun v w =>
    SimpleGraph.ConnectedComponent.sound (h v w)⟩

lemma exists_not_reachable (h : 2 ≤ ncomp d) :
    ∃ z y : fiber d, ¬ (nabla d).Reachable z y := by
  by_contra hne
  push Not at hne
  have := ncomp_le_one_of_reachable hne
  omega

lemma pos_of_two_le_ncomp (h : 2 ≤ ncomp d) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h1 : ncomp 0 ≤ 1 := by
      apply ncomp_le_one_of_reachable
      intro z y
      have hzy : z = y := Subtype.ext (by
        have hz : z.1 = 0 := by simpa [fiber_zero] using z.2
        have hy : y.1 = 0 := by simpa [fiber_zero] using y.2
        rw [hz, hy])
      rw [hzy]
    omega
  · exact hd

/-! ### Lemma 2: component supports and replacement bridges -/

/-- **Lemma 2.1.** Distinct components of `∇_d` have disjoint supports. -/
lemma compSupp_disjoint {C C' : Comp d} (h : C ≠ C') :
    Disjoint (compSupp C) (compSupp C') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  obtain ⟨z, rfl, hz⟩ := mem_compSupp.1 hi
  obtain ⟨z', rfl, hz'⟩ := mem_compSupp.1 hi'
  exact h (SimpleGraph.ConnectedComponent.sound (reachable_of_sharesVar ⟨i, hz, hz'⟩))

/-- **Lemma 2.2.** At positive degree every component has nonempty support. -/
lemma compSupp_nonempty (hd : 0 < d) (C : Comp d) :
    (compSupp C).Nonempty := by
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h z =>
    have hnu : 0 < nu z := by rw [mem_fiber.1 z.2]; exact hd
    have hz : z.1 ≠ 0 := by rintro h0; rw [h0, nu_zero] at hnu; omega
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
    exact ⟨i, mem_compSupp.2 ⟨z, rfl, Nat.pos_of_ne_zero hi⟩⟩

/-- **Lemma 2.3.** If `u ≤ x` and `ν(u) = ν(v)` then `b = x - u + v` has `ν(b) = ν(x)`. -/
lemma nu_replace {u v x : Vec} (hux : u ≤ x) (huv : nu u = nu v) :
    nu (x - u + v) = nu x := by
  rw [nu_add, nu_sub hux, huv, add_comm]

/-- **Lemma 2.4.** A factorization `b` of `d` sharing a variable with `z` and with `y` puts
`z` and `y` in the same component. -/
lemma reachable_of_bridge {z y : fiber d} (b : Vec) (hb : nu b = d)
    (hz : SharesVar b z.1) (hy : SharesVar b y.1) : (nabla d).Reachable z y :=
  (reachable_of_sharesVar (z := (⟨b, mem_fiber.2 hb⟩ : fiber d)) hz).symm.trans
    (reachable_of_sharesVar hy)

/-! ### Lemma 0, part A: the finite cutoff -/

/-- Core of Lemma 0A: a factorization with a coordinate exceeding `N = n₃` is connected to
every other factorization of the same degree. -/
lemma reachable_of_coord_gt (z y : fiber d) {i : Fin 4} (hzi : n 3 < z.1 i) :
    (nabla d).Reachable z y := by
  have hz := mem_fiber.1 z.2
  have hy := mem_fiber.1 y.2
  obtain ⟨j, hj⟩ : ∃ j, 0 < y.1 j := by
    by_contra hc; push Not at hc
    have : y.1 = 0 := funext fun k => Nat.le_zero.1 (hc k)
    rw [this, nu_zero] at hy
    have := nu_pos_of_pos (z := z.1) (i := i) (by omega)
    omega
  by_cases hzj : 0 < z.1 j
  · exact reachable_of_sharesVar ⟨j, hzj, hj⟩
  have hij : i ≠ j := by rintro rfl; omega
  have hnj := n_le_n_three j
  -- the bridge `b = z - nⱼ eᵢ + nᵢ eⱼ`
  have hle : Pi.single i (n j) ≤ z.1 := by
    intro k
    by_cases hk : k = i
    · subst hk; simp; omega
    · simp [hk]
  have heq : nu (Pi.single i (n j)) = nu (Pi.single j (n i)) := by
    rw [nu_single, nu_single, mul_comm]
  refine reachable_of_bridge (z.1 - Pi.single i (n j) + Pi.single j (n i))
    ((nu_replace hle heq).trans hz) ⟨i, ?_, by omega⟩ ⟨j, ?_, hj⟩
  · simp [hij]; omega
  · simp [hij.symm, n_pos i]

/-- **Lemma 0A.** At a contributing degree every coordinate of every factorization is at most
`N = n₃`, and hence every contributing degree satisfies `d ≤ H`. -/
lemma le_H_of_contributes (h : contributes d) : d ≤ H := by
  obtain ⟨z, -, -⟩ := exists_not_reachable h
  have hcoord : ∀ i, z.1 i ≤ n 3 := by
    intro i
    by_contra hc
    push Not at hc
    obtain ⟨y, y', hyy'⟩ := exists_not_reachable h
    exact hyy' (((reachable_of_coord_gt z y hc).symm).trans (reachable_of_coord_gt z y' hc))
  rw [← mem_fiber.1 z.2, nu, H, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (hcoord i)

/-! ## Critical -/

/-! ### Definition 5 -/

/-- Membership in `Tᵢ`: `k ≥ 1` and `k nᵢ` has a factorization other than `k eᵢ`. -/
def IsCritCand (i : Fin 4) (k : ℕ) : Prop :=
  1 ≤ k ∧ ∃ y ∈ fiber (k * n i), y ≠ Pi.single i k

instance (i : Fin 4) : DecidablePred (IsCritCand i) := fun k =>
  inferInstanceAs (Decidable (1 ≤ k ∧ ∃ y ∈ fiber (k * n i), y ≠ Pi.single i k))

lemma isCritCand_iff {i : Fin 4} {k : ℕ} :
    IsCritCand i k ↔ 1 ≤ k ∧ ∃ y : Vec, nu y = k * n i ∧ y ≠ Pi.single i k := by
  simp [IsCritCand]

/-- `nⱼ ∈ Tᵢ` for `j ≠ i`, witnessed by `nᵢ eⱼ ≠ nⱼ eᵢ`. -/
lemma isCritCand_n {i j : Fin 4} (hji : j ≠ i) : IsCritCand i (n j) := by
  rw [isCritCand_iff]
  refine ⟨n_pos j, Pi.single j (n i), by rw [nu_single, mul_comm], ?_⟩
  intro h
  have := congrFun h j
  simp [hji, (n_pos i).ne'] at this

lemma succ_ne (i : Fin 4) : i + 1 ≠ i := by fin_cases i <;> decide

lemma crit_exists (i : Fin 4) : ∃ k, IsCritCand i k := ⟨_, isCritCand_n (succ_ne i)⟩

/-- **Definition 5.** The critical exponent `cᵢ = min Tᵢ`. -/
def crit (i : Fin 4) : ℕ := Nat.find (crit_exists i)

lemma crit_spec (i : Fin 4) : IsCritCand i (crit i) := Nat.find_spec (crit_exists i)

/-! ### Lemma 3 -/

/-- **Lemma 3.1.** `1 ≤ cᵢ`. -/
lemma one_le_crit (i : Fin 4) : 1 ≤ crit i := (crit_spec i).1

lemma exists_alt (i : Fin 4) :
    ∃ y : Vec, nu y = crit i * n i ∧ y ≠ Pi.single i (crit i) :=
  (isCritCand_iff.1 (crit_spec i)).2

/-- **Lemma 3.2.** Every alternative factorization at the critical degree avoids `i`. -/
lemma alt_coord_eq_zero {i : Fin 4} {y : Vec} (hy : nu y = crit i * n i)
    (hne : y ≠ Pi.single i (crit i)) : y i = 0 := by
  by_contra hyi
  have hyi : 0 < y i := Nat.pos_of_ne_zero hyi
  have hle : y i ≤ crit i := by
    have := single_le_nu y i
    rw [hy] at this
    exact Nat.le_of_mul_le_mul_right this (n_pos i)
  rcases hle.lt_or_eq with hlt | heq
  · -- `v = y - yᵢ eᵢ` is an alternative for `r = cᵢ - yᵢ < cᵢ`
    have hsub : Pi.single i (y i) ≤ y := fun k => by by_cases hk : k = i <;> simp [hk]
    have hnu := nu_sub hsub
    rw [nu_single, hy] at hnu
    have hcand : IsCritCand i (crit i - y i) := by
      rw [isCritCand_iff]
      refine ⟨by omega, y - Pi.single i (y i), ?_, ?_⟩
      · rw [Nat.sub_mul]; omega
      · intro h
        have := congrFun h i
        simp at this; omega
    exact Nat.find_min (crit_exists i) (show crit i - y i < crit i by omega) hcand
  · -- `yᵢ = cᵢ` forces `y = cᵢ eᵢ`
    apply hne
    funext k
    by_cases hk : k = i
    · subst hk; simp [heq]
    · have h2 : y k * n k + y i * n i ≤ nu y :=
        Finset.add_le_sum (f := fun j => y j * n j) (fun _ _ => Nat.zero_le _)
          (mem_univ k) (mem_univ i) hk
      rw [hy, heq] at h2
      have : y k * n k = 0 := by omega
      simp [hk, (n_pos k).ne'] at this ⊢; exact this

/-- The vertex `cᵢ eᵢ` of `∇_{cᵢ nᵢ}`. -/
def critVertex (i : Fin 4) : fiber (crit i * n i) :=
  ⟨Pi.single i (crit i), mem_fiber.2 (nu_single i _)⟩

/-- **Lemma 3.3.** `cᵢ eᵢ` is isolated in `∇_{cᵢ nᵢ}`. -/
lemma critVertex_not_adj (i : Fin 4) (z : fiber (crit i * n i)) :
    ¬ (nabla _).Adj (critVertex i) z := by
  rintro ⟨hne, k, hk, hzk⟩
  have hki : k = i := by
    by_contra h; simp [critVertex, h] at hk
  subst hki
  have hz : z.1 ≠ Pi.single k (crit k) := fun h => hne (Subtype.ext h.symm)
  have := alt_coord_eq_zero (mem_fiber.1 z.2) hz
  omega

/-- **Lemma 3.3.** The component of `cᵢ eᵢ` is `{cᵢ eᵢ}`. -/
lemma eq_critVertex_of_reachable (i : Fin 4) {z : fiber (crit i * n i)}
    (h : (nabla _).Reachable (critVertex i) z) : z = critVertex i := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (critVertex_not_adj i _)

/-- **Lemma 3.3.** The component `{cᵢ eᵢ}` has support `{i}`. -/
lemma compSupp_critVertex (i : Fin 4) :
    compSupp (cmk (critVertex i)) = {i} := by
  ext k
  rw [mem_compSupp, mem_singleton]
  constructor
  · rintro ⟨z, hz, hzk⟩
    have := eq_critVertex_of_reachable i (SimpleGraph.ConnectedComponent.exact hz).symm
    subst this
    by_contra h; simp [critVertex, h] at hzk
  · intro h
    rw [h]
    exact ⟨critVertex i, rfl, by simpa [critVertex] using Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_crit i)⟩

/-- **Lemma 3.4.** At a contributing degree, a component with support `{i}` lives in degree
`cᵢ nᵢ`. -/
lemma degree_eq_of_singleton_comp (hd : contributes d) {i : Fin 4}
    {C : Comp d} (hC : compSupp C = {i}) : d = crit i * n i := by
  have hdpos := pos_of_two_le_ncomp hd
  obtain ⟨k0, hk0⟩ := compSupp_nonempty hdpos C
  obtain ⟨z, hz, -⟩ := mem_compSupp.1 hk0
  have hzd := mem_fiber.1 z.2
  -- `z = k eᵢ` with `k = zᵢ`
  have hzform : z.1 = Pi.single i (z.1 i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · have h0 : z.1 j = 0 := by
        by_contra hzj
        have hmem : j ∈ compSupp C := mem_compSupp.2 ⟨z, hz, Nat.pos_of_ne_zero hzj⟩
        rw [hC, mem_singleton] at hmem; exact hj hmem
      simp [hj, h0]
  set k := z.1 i with hk
  have hdk : d = k * n i := by rw [← hzd, hzform, nu_single]
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, zero_mul] at hdk; omega
    · exact h
  rcases lt_trichotomy k (crit i) with hlt | heq | hgt
  · -- no alternative: the fiber is a single vertex
    exfalso
    have hall : ∀ y : fiber d, y = z := by
      intro y
      by_contra hyz
      have hy : y.1 ≠ Pi.single i k := by
        intro h; exact hyz (Subtype.ext (h.trans hzform.symm))
      exact Nat.find_min (crit_exists i) hlt
        (isCritCand_iff.2 ⟨hkpos, y.1, (mem_fiber.1 y.2).trans hdk, hy⟩)
    have := ncomp_le_one_of_reachable (d := d) (fun y y' => by rw [hall y, hall y'])
    unfold contributes at hd; omega
  · rw [hdk, heq]
  · -- the bridge `b = (k - cᵢ) eᵢ + y` enlarges the support
    exfalso
    obtain ⟨y, hy, hyne⟩ := exists_alt i
    have hyi := alt_coord_eq_zero hy hyne
    obtain ⟨j, hj⟩ : ∃ j, 0 < y j := by
      by_contra hc; push Not at hc
      have hy0 : y = 0 := funext fun l => Nat.le_zero.1 (hc l)
      rw [hy0, nu_zero] at hy
      have := Nat.mul_pos (one_le_crit i) (n_pos i); omega
    have hji : j ≠ i := by rintro rfl; omega
    let b := Pi.single i (k - crit i) + y
    have hb : nu b = d := by
      simp only [b]; rw [nu_add, nu_single, hy, hdk, ← Nat.add_mul, Nat.sub_add_cancel hgt.le]
    have hbz : cmk (⟨b, mem_fiber.2 hb⟩ : fiber d) = C := by
      rw [← hz]
      apply SimpleGraph.ConnectedComponent.sound
      apply reachable_of_sharesVar
      exact ⟨i, by simp only [b, Pi.add_apply, Pi.single_eq_same, hyi, add_zero]; omega,
        by rw [← hk]; exact hkpos⟩
    have : j ∈ compSupp C :=
      mem_compSupp.2 ⟨⟨b, mem_fiber.2 hb⟩, hbz, by simp [b, hji.symm, hj]⟩
    rw [hC, mem_singleton] at this
    exact hji this

/-! ### Definition 6 and Lemma 4 -/

/-- Some component of `∇_d` has support of cardinality one. -/
def HasSingletonComp (d : ℕ) : Prop :=
  ∃ C : Comp d, (compSupp C).card = 1

/-- **Definition 6.** `𝓢`: contributing degrees having a singleton-support component. -/
noncomputable def singletonDegrees : Finset ℕ := by
  classical
  exact (range (H + 1)).filter (fun d => contributes d ∧ HasSingletonComp d)

lemma mem_singletonDegrees :
    d ∈ singletonDegrees ↔ d ≤ H ∧ contributes d ∧ HasSingletonComp d := by
  classical
  unfold singletonDegrees; simp only [mem_filter, mem_range, Nat.lt_succ_iff]

/-- **Definition 6.** `σ = ∑_{d ∈ 𝓢} (c_d - 1)`. -/
noncomputable def sigma : ℕ := ∑ d ∈ singletonDegrees, (ncomp d - 1)

/-- The indices whose critical degree is `d`. -/
def critIndices (d : ℕ) : F4 := univ.filter (fun i => crit i * n i = d)

/-- **Lemma 4, per-degree step.** For `d ∈ 𝓢`: `c_d - 1 ≤ r_d ≤ #{i : cᵢ nᵢ = d}`. -/
lemma ncomp_sub_one_le (hd : contributes d) (hS : HasSingletonComp d) :
    ncomp d - 1 ≤ (critIndices d).card := by
  classical
  have hdpos := pos_of_two_le_ncomp hd
  set K1 := (univ : Finset (Comp d)).filter
    (fun C => (compSupp C).card = 1) with hK1
  set K2 := (univ : Finset (Comp d)).filter
    (fun C => ¬ (compSupp C).card = 1) with hK2
  have hsplit : K1.card + K2.card = ncomp d := by
    rw [hK1, hK2, card_filter_add_card_filter_not]; rfl
  -- `r_d = #K1 ≤ #{i : cᵢ nᵢ = d}`: the singleton supports are disjoint and indexed by
  -- critical indices (Lemmas 2.1 and 3.4)
  have hK1le : K1.card ≤ (critIndices d).card := by
    have hdisj : (K1 : Set (Comp d)).PairwiseDisjoint compSupp :=
      fun C _ C' _ h => compSupp_disjoint h
    have hcard : (K1.biUnion compSupp).card = K1.card := by
      rw [card_biUnion hdisj]
      rw [Finset.sum_congr rfl (fun C hC => (mem_filter.1 hC).2)]
      simp [hK1]
    rw [← hcard]
    apply card_le_card
    intro i hi
    obtain ⟨C, hC, hiC⟩ := mem_biUnion.1 hi
    obtain ⟨i', hi'⟩ := card_eq_one.1 (mem_filter.1 hC).2
    rw [hi', mem_singleton] at hiC
    subst hiC
    simp only [critIndices, mem_filter, mem_univ, true_and]
    exact (degree_eq_of_singleton_comp hd hi').symm
  -- at most one component with support of size `≥ 2`
  have hK2le : K2.card ≤ 1 := by
    obtain ⟨C0, hC0⟩ := hS
    rw [card_le_one]
    intro C hC C' hC'
    by_contra hne
    have h2 : ∀ D ∈ K2, 2 ≤ (compSupp D).card := by
      intro D hD
      have h1 := (mem_filter.1 hD).2
      have h0 := (compSupp_nonempty hdpos D).card_pos
      omega
    have hC2 := h2 C hC
    have hC'2 := h2 C' hC'
    have hCC0 : C ≠ C0 := fun h => (mem_filter.1 hC).2 (h ▸ hC0)
    have hC'C0 : C' ≠ C0 := fun h => (mem_filter.1 hC').2 (h ▸ hC0)
    have hu := card_le_univ (compSupp C ∪ compSupp C' ∪ compSupp C0)
    rw [card_union_of_disjoint, card_union_of_disjoint (compSupp_disjoint hne)] at hu
    · simp only [Fintype.card_fin] at hu; omega
    · exact disjoint_union_left.2 ⟨compSupp_disjoint hCC0, compSupp_disjoint hC'C0⟩
  omega

/-- **Lemma 4.** Singleton-support degrees contribute at most four: `σ ≤ 4`. -/
theorem sigma_le_four : sigma ≤ 4 := by
  classical
  let f : Vec := fun i => crit i * n i
  let s := univ.filter (fun i => f i ∈ singletonDegrees)
  have hmaps : (s : Set (Fin 4)).MapsTo f singletonDegrees := fun i hi => (mem_filter.1 hi).2
  calc sigma = ∑ d ∈ singletonDegrees, (ncomp d - 1) := rfl
    _ ≤ ∑ d ∈ singletonDegrees, (critIndices d).card := by
      apply sum_le_sum
      intro d hd
      obtain ⟨-, hc, hS⟩ := mem_singletonDegrees.1 hd
      exact ncomp_sub_one_le hc hS
    _ = ∑ d ∈ singletonDegrees, (s.filter (fun i => f i = d)).card := by
      apply sum_congr rfl
      intro d hd
      congr 1
      ext i
      simp only [critIndices, s, f, mem_filter, mem_univ, true_and]
      constructor
      · intro h; exact ⟨h ▸ hd, h⟩
      · exact fun h => h.2
    _ = s.card := (card_eq_sum_card_fiberwise hmaps).symm
    _ ≤ 4 := by simpa using card_le_univ s

/-! ## Partition -/

section PairSide

variable {K : F4}

/-- Propagating a property along a reachability path. -/
lemma reachable_induction {V : Type*} {Γ : SimpleGraph V} (P : V → Prop)
    (hstep : ∀ x y, P x → Γ.Adj x y → P y) {x y : V} (h : Γ.Reachable x y) (hx : P x) : P y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hx
  | cons ha _ ih => exact ih (hstep _ _ hx ha)

/-! ### Splitting along a pair -/

/-- `∇_d` has two distinct components with supports `K` and `Kᶜ`. -/
def IsSplit (d : ℕ) (K : F4) : Prop :=
  ∃ C C' : Comp d, C ≠ C' ∧ compSupp C = K ∧ compSupp C' = Kᶜ

lemma IsSplit.compl (h : IsSplit d K) : IsSplit d Kᶜ := by
  obtain ⟨C, C', hne, hC, hC'⟩ := h
  exact ⟨C', C, hne.symm, hC', by rw [compl_compl, hC]⟩

/-- A component containing a factorization positive at some index of `compSupp C` is `C`. -/
lemma comp_eq_of_mem {C : Comp d} (z : fiber d) {i : Fin 4}
    (hi : i ∈ compSupp C) (hzi : 0 < z.1 i) : cmk z = C := by
  by_contra hne
  exact Finset.disjoint_left.1 (compSupp_disjoint hne) (supp_subset_compSupp z (mem_supp.2 hzi)) hi

/-- **No bridge across a split.** If `d` splits along `K`, `z` is positive somewhere in `K`, `y`
somewhere in `Kᶜ`, then no factorization of `d` shares a variable with both. -/
lemma no_bridge (hS : IsSplit d K) {z y b : Vec}
    (hz : nu z = d) (hy : nu y = d) (hb : nu b = d) {i j : Fin 4} (hi : i ∈ K)
    (hzi : 0 < z i) (hj : j ∉ K) (hyj : 0 < y j) (hbz : SharesVar b z) (hby : SharesVar b y) :
    False := by
  obtain ⟨C, C', hne, hC, hC'⟩ := hS
  have h1 : cmk (⟨z, mem_fiber.2 hz⟩ : fiber d) = C :=
    comp_eq_of_mem _ (hC ▸ hi) hzi
  have h2 : cmk (⟨y, mem_fiber.2 hy⟩ : fiber d) = C' :=
    comp_eq_of_mem _ (hC' ▸ mem_compl.2 hj) hyj
  refine hne ?_
  rw [← h1, ← h2]
  exact SimpleGraph.ConnectedComponent.sound (reachable_of_bridge b hb hbz hby)

/-! ### Lemma 5 -/

/-- **Lemma 5 (full support).** A component with support `{i, j}` contains a factorization
positive at both `i` and `j`. -/
lemma exists_full_vertex {C : Comp d} {i j : Fin 4}
    (hij : i ≠ j) (hC : compSupp C = {i, j}) :
    ∃ z : fiber d, cmk z = C ∧ 0 < z.1 i ∧ 0 < z.1 j := by
  by_contra H
  push Not at H
  obtain ⟨z0, hz0, hz0i⟩ := mem_compSupp.1 (show i ∈ compSupp C by rw [hC]; simp)
  obtain ⟨z1, hz1, hz1j⟩ := mem_compSupp.1 (show j ∈ compSupp C by rw [hC]; simp)
  have hreach : (nabla d).Reachable z0 z1 := SimpleGraph.ConnectedComponent.exact (hz0.trans hz1.symm)
  have key := reachable_induction
    (fun x : fiber d => cmk x = C ∧ 0 < x.1 i)
    (by
      rintro x y ⟨hxC, hxi⟩ hadj
      have hyC : cmk y = C :=
        (SimpleGraph.ConnectedComponent.sound hadj.reachable).symm.trans hxC
      obtain ⟨-, k, hxk, hyk⟩ := hadj
      have hk : k ∈ compSupp C := hxC ▸ supp_subset_compSupp x (mem_supp.2 hxk)
      rw [hC, mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact ⟨hyC, hyk⟩
      · have := H x hxC hxi; omega)
    hreach ⟨hz0, hz0i⟩
  have := H z1 hz1 key.2
  omega

/-- **Lemma 5.** At a contributing degree without singleton-support components, `∇_d` has exactly
two components, and their supports form one of the partitions `01|23`, `02|13`, `03|12`. -/
theorem lemma5 (hd : contributes d) (hS : ¬ HasSingletonComp d) :
    ncomp d = 2 ∧ (IsSplit d K01 ∨ IsSplit d K02 ∨ IsSplit d K03) := by
  classical
  have hdpos := pos_of_two_le_ncomp hd
  have hcard2 : ∀ C : Comp d, 2 ≤ (compSupp C).card := by
    intro C
    have h0 := (compSupp_nonempty hdpos C).card_pos
    have h1 : (compSupp C).card ≠ 1 := fun h => hS ⟨C, h⟩
    omega
  have hnt : Nontrivial (Comp d) := by
    rw [← Fintype.one_lt_card_iff_nontrivial]; exact hd
  obtain ⟨C1, C2, h12⟩ := exists_pair_ne (Comp d)
  have hdisj := compSupp_disjoint h12
  have hc1 := hcard2 C1
  have hc2 := hcard2 C2
  have hsum : (compSupp C1).card + (compSupp C2).card = 4 := by
    have hle := card_le_univ (compSupp C1 ∪ compSupp C2)
    rw [card_union_of_disjoint hdisj, Fintype.card_fin] at hle
    omega
  have huniv : compSupp C1 ∪ compSupp C2 = univ := by
    apply eq_univ_of_card
    rw [card_union_of_disjoint hdisj, Fintype.card_fin]; omega
  have hcompl : compSupp C2 = (compSupp C1)ᶜ := by
    rw [eq_compl_iff_isCompl]
    refine ⟨hdisj.symm, ?_⟩
    rw [codisjoint_iff]
    show compSupp C2 ∪ compSupp C1 = univ
    rw [union_comm]; exact huniv
  have hall : ∀ C, C = C1 ∨ C = C2 := by
    intro C
    by_contra hC
    push Not at hC
    obtain ⟨k, hk⟩ := compSupp_nonempty hdpos C
    have : k ∈ compSupp C1 ∪ compSupp C2 := huniv ▸ mem_univ k
    rcases mem_union.1 this with h | h
    · exact Finset.disjoint_left.1 (compSupp_disjoint hC.1) hk h
    · exact Finset.disjoint_left.1 (compSupp_disjoint hC.2) hk h
  refine ⟨?_, ?_⟩
  · unfold ncomp
    rw [← card_univ, show (univ : Finset (Comp d)) = {C1, C2} by
      ext C; simp only [mem_univ, mem_insert, mem_singleton, true_iff]; exact hall C]
    exact card_pair h12
  · have hsplit1 : IsSplit d (compSupp C1) := ⟨C1, C2, h12, rfl, hcompl⟩
    have hsplit2 : IsSplit d (compSupp C2) := by rw [hcompl]; exact hsplit1.compl
    have hc1' : (compSupp C1).card = 2 := by omega
    have hc2' : (compSupp C2).card = 2 := by omega

    have key : ∀ K : F4, K.card = 2 → 0 ∈ K → K = K01 ∨ K = K02 ∨ K = K03 := by
      decide
    have h0 : (0 : Fin 4) ∈ compSupp C1 ∪ compSupp C2 := huniv ▸ mem_univ 0
    rcases mem_union.1 h0 with h | h
    · rcases key _ hc1' h with e | e | e <;> rw [e] at hsplit1 <;> simp [hsplit1]
    · rcases key _ hc2' h with e | e | e <;> rw [e] at hsplit2 <;> simp [hsplit2]

/-! ### Definition 7 -/

/-- The pair family for the partition `K | Kᶜ`: contributing degrees `≤ H` without
singleton-support components which split along `K`. -/
noncomputable def fam (K : F4) : Finset ℕ := by
  classical
  exact (range (H + 1)).filter (fun d => contributes d ∧ ¬ HasSingletonComp d ∧ IsSplit d K)

lemma mem_fam :
    d ∈ fam K ↔ d ≤ H ∧ contributes d ∧ ¬ HasSingletonComp d ∧ IsSplit d K := by
  classical
  unfold fam; simp only [mem_filter, mem_range, Nat.lt_succ_iff]

/-- `𝓟` (partition `01|23`), `𝓠` (`02|13`), `ℰ` (`03|12`). -/
noncomputable def famP : Finset ℕ := fam K01
noncomputable def famQ : Finset ℕ := fam K02
noncomputable def famE : Finset ℕ := fam K03

/-- `P = |𝓟|`, `Q = |𝓠|`, `E = |ℰ|`. -/
noncomputable def P : ℕ := famP.card
noncomputable def Q : ℕ := famQ.card
noncomputable def E : ℕ := famE.card

/-- The selected factorization of `d` with support exactly `K` (a fixed choice; `0` if none). -/
noncomputable def sel (d : ℕ) (K : F4) : Vec := by
  classical
  exact if h : ∃ z : Vec, nu z = d ∧ supp z = K then h.choose else 0

/-- The selected vectors at a split degree: `ν = d` and support `K`. -/
lemma sel_of_split (hS : IsSplit d K) (hK : K.card = 2) :
    nu (sel d K) = d ∧ supp (sel d K) = K := by
  classical
  obtain ⟨C, -, -, hC, -⟩ := hS
  have hex : ∃ z : Vec, nu z = d ∧ supp z = K := by
    obtain ⟨i, j, hij, rfl⟩ := card_eq_two.1 hK
    obtain ⟨z, hz, hzi, hzj⟩ := exists_full_vertex hij hC
    refine ⟨z.1, mem_fiber.1 z.2, Subset.antisymm (hC ▸ hz ▸ supp_subset_compSupp z) ?_⟩
    intro k hk
    rw [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl <;> simpa
  unfold sel
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact hex.choose_spec

lemma card_compl_of_card_two (hK : K.card = 2) : Kᶜ.card = 2 := by
  rw [card_compl, Fintype.card_fin, hK]

lemma sel_pos (hS : IsSplit d K) (hK : K.card = 2) {i : Fin 4}
    (hi : i ∈ K) : 0 < sel d K i := by
  rw [← mem_supp, (sel_of_split hS hK).2]; exact hi

lemma sel_eq_zero (hS : IsSplit d K) (hK : K.card = 2) {i : Fin 4}
    (hi : i ∉ K) : sel d K i = 0 := by
  by_contra h
  exact hi ((sel_of_split hS hK).2 ▸ mem_supp.2 (Nat.pos_of_ne_zero h))

/-- **Selected-vector replacement principle**: at a degree splitting along a pair `K`, no
replacement `z - U + V` of the selected `K`-vector `z` keeps a coordinate of `z` and gains a
coordinate outside `K`. -/
lemma no_replace (hS : IsSplit d K) (hK : K.card = 2)
    {U V : Vec} (hUz : U ≤ sel d K) (hUV : nu U = nu V) {k j : Fin 4}
    (hk : U k < sel d K k) (hj : j ∉ K) (hVj : 0 < V j) : False := by
  have hz := sel_of_split hS hK
  have hy := sel_of_split hS.compl (card_compl_of_card_two hK)
  have hkK : k ∈ K := hz.2 ▸ mem_supp.2 (by omega)
  have hyj : 0 < sel d Kᶜ j := by rw [← mem_supp, hy.2]; exact mem_compl.2 hj
  refine no_bridge hS hz.1 hy.1 ((nu_replace hUz hUV).trans hz.1) hkK (by omega) hj hyj
    ⟨k, ?_, by omega⟩ ⟨j, ?_, hyj⟩
  · simp only [Pi.add_apply, Pi.sub_apply]; omega
  · simp only [Pi.add_apply, Pi.sub_apply]; omega

/-! ### Lemma 6 -/

lemma isSplit_exclusive {K L : F4} (hK : IsSplit d K) (hL : IsSplit d L)
    {i : Fin 4} (hiK : i ∈ K) (hiL : i ∈ L) : K = L := by
  obtain ⟨C, -, -, hC, -⟩ := hK
  obtain ⟨C', -, -, hC', -⟩ := hL
  by_contra hne
  have : C ≠ C' := by rintro rfl; exact hne (hC.symm.trans hC')
  exact Finset.disjoint_left.1 (compSupp_disjoint this) (hC ▸ hiK) (hC' ▸ hiL)

/-- **Lemma 6.** `β₁ = σ + P + Q + E`, and `c_d = 2` on the three pair families. -/
theorem beta1_eq : beta1 = sigma + P + Q + E := by
  classical
  have hpt : ∀ d ∈ range (H + 1), ncomp d - 1 =
      (if d ∈ singletonDegrees then ncomp d - 1 else 0) + (if d ∈ famP then 1 else 0) +
      (if d ∈ famQ then 1 else 0) + (if d ∈ famE then 1 else 0) := by
    intro d hd
    have hdH : d ≤ H := Nat.lt_succ_iff.1 (mem_range.1 hd)
    simp only [famP, famQ, famE, mem_fam, mem_singletonDegrees]
    by_cases hc : contributes d
    · by_cases hS : HasSingletonComp d
      · simp [hc, hS, hdH]
      · obtain ⟨h2, hsp⟩ := lemma5 hc hS
        rcases hsp with h | h | h
        · have e2 : ¬ IsSplit d K02 := fun h' =>
            absurd (isSplit_exclusive h h' (i := 0) (by simp) (by simp)) (by decide)
          have e3 : ¬ IsSplit d K03 := fun h' =>
            absurd (isSplit_exclusive h h' (i := 0) (by simp) (by simp)) (by decide)
          simp [h, h2, e2, e3, hc, hS, hdH]
        · have e1 : ¬ IsSplit d K01 := fun h' =>
            absurd (isSplit_exclusive h' h (i := 0) (by simp) (by simp)) (by decide)
          have e3 : ¬ IsSplit d K03 := fun h' =>
            absurd (isSplit_exclusive h h' (i := 0) (by simp) (by simp)) (by decide)
          simp [h, h2, e1, e3, hc, hS, hdH]
        · have e1 : ¬ IsSplit d K01 := fun h' =>
            absurd (isSplit_exclusive h' h (i := 0) (by simp) (by simp)) (by decide)
          have e2 : ¬ IsSplit d K02 := fun h' =>
            absurd (isSplit_exclusive h' h (i := 0) (by simp) (by simp)) (by decide)
          simp [h, h2, e1, e2, hc, hS, hdH]
    · have : ncomp d ≤ 1 := by unfold contributes at hc; omega
      simp [hc, hdH]; omega
  have hsub : ∀ s : Finset ℕ, s ⊆ range (H + 1) →
      s.card = ∑ d ∈ range (H + 1), (if d ∈ s then 1 else 0) := by
    intro s hs
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hs]; simp
  have hfam : ∀ K, fam K ⊆ range (H + 1) := by
    intro K d hd; exact mem_range.2 (Nat.lt_succ_of_le (mem_fam.1 hd).1)
  have hsig : sigma = ∑ d ∈ range (H + 1),
      (if d ∈ singletonDegrees then ncomp d - 1 else 0) := by
    have hsd : singletonDegrees ⊆ range (H + 1) := by
      intro d hd; exact mem_range.2 (Nat.lt_succ_of_le (mem_singletonDegrees.1 hd).1)
    rw [sigma, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsd]
  rw [beta1, Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hsig, P, Q, E, hsub famP (hfam _), hsub famQ (hfam _),
    hsub famE (hfam _)]

/-! ### Lemma 7 -/

/-- **Lemma 7.** For a fixed side `K` (a pair), the selected `K`-vectors at distinct split degrees
are not comparable: `¬ (z_d ≤ z_{d'})`. -/
theorem sel_antichain (hK : K.card = 2) {d d' : ℕ} (hS : IsSplit d K)
    (hS' : IsSplit d' K) (hne : d ≠ d') : ¬ sel d K ≤ sel d' K := by
  intro hle
  have hz := sel_of_split hS hK
  have hz' := sel_of_split hS' hK
  have hKc := card_compl_of_card_two hK
  have hy := sel_of_split hS.compl hKc
  have hy' := sel_of_split hS'.compl hKc
  have hex : ∃ i, sel d K i < sel d' K i := by
    by_contra h
    push Not at h
    exact hne (by rw [← hz.1, ← hz'.1]; congr 1; funext i; exact le_antisymm (hle i) (h i))
  obtain ⟨i, hi⟩ := hex
  have hiK : i ∈ K := hz'.2 ▸ mem_supp.2 (Nat.lt_of_le_of_lt (Nat.zero_le _) hi)
  obtain ⟨j, hj⟩ : Kᶜ.Nonempty := card_pos.1 (by rw [card_compl_of_card_two hK]; omega)
  have hyj : 0 < sel d Kᶜ j := by rw [← mem_supp, hy.2]; exact hj
  have hy'j : 0 < sel d' Kᶜ j := by rw [← mem_supp, hy'.2]; exact hj
  have hb : nu (sel d' K - sel d K + sel d Kᶜ) = d' := by
    rw [nu_replace hle (hz.1.trans hy.1.symm), hz'.1]
  exact no_bridge hS' hz'.1 hy'.1 hb hiK (Nat.lt_of_le_of_lt (Nat.zero_le _) hi)
    (mem_compl.1 hj) hy'j
    ⟨i, by simp only [Pi.add_apply, Pi.sub_apply]; omega⟩
    ⟨j, by simp only [Pi.add_apply, Pi.sub_apply]; omega⟩

/-! ## Identities -/

/-! ### Definition 8 -/

/-- `s = A`. -/
def s : ℕ := A
/-- `t = W - B`. -/
def t : ℕ := W - B
/-- `d = gcd(s, t)` (named `dg`). -/
def dg : ℕ := Nat.gcd s t
/-- `p = t / d`. -/
def p : ℕ := t / dg
/-- `q = s / d`. -/
def q : ℕ := s / dg
/-- `R = min(B, W - A)`. -/
def R : ℕ := min B (W - A)

lemma s_pos : 1 ≤ s := A_pos
lemma t_pos : 1 ≤ t := by have := B_lt_W; unfold t; omega
lemma dg_pos : 1 ≤ dg := Nat.gcd_pos_of_pos_left _ s_pos
lemma dg_mul_p : dg * p = t := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
lemma dg_mul_q : dg * q = s := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
lemma p_pos : 1 ≤ p := Nat.pos_of_mul_pos_left (dg_mul_p ▸ t_pos)
lemma q_pos : 1 ≤ q := Nat.pos_of_mul_pos_left (dg_mul_q ▸ s_pos)
lemma dg_mul_p_add_q : dg * (p + q) = s + t := by
  rw [mul_add, dg_mul_p, dg_mul_q, add_comm]
lemma p_add_q_eq : p + q = (s + t) / dg := by
  rw [← dg_mul_p_add_q, Nat.mul_div_cancel_left _ dg_pos]
lemma p_add_q_le : p + q ≤ s + t := by
  rw [← dg_mul_p_add_q]; exact Nat.le_mul_of_pos_left _ dg_pos
lemma W_eq_B_add_t : W = B + t := by have := B_lt_W; unfold t; omega
lemma R_eq : R = W - max s t := by
  have := A_lt_B; have := B_lt_W; unfold R s t; omega
lemma two_le_R : 2 ≤ R := by
  have := two_le_B; have := two_le_W_sub_A; unfold R; omega
/-- `p A = q t`. -/
lemma p_mul_A : p * A = q * t := by
  have h : dg * (p * A) = dg * (q * t) := by
    rw [← mul_assoc, ← mul_assoc, dg_mul_p, dg_mul_q, mul_comm]
    rfl
  exact Nat.eq_of_mul_eq_mul_left dg_pos h

/-! ### Lemma 8 -/

/-- `U₁ = (0,B,0,0)`, `V₁ = (B-A,0,A,0)`. -/
def U1 : Vec := ![0, B, 0, 0]
def V1 : Vec := ![B - A, 0, A, 0]
/-- `U₂ = (0,0,W-A,0)`, `V₂ = (0,W-B,0,B-A)`. -/
def U2 : Vec := ![0, 0, W - A, 0]
def V2 : Vec := ![0, W - B, 0, B - A]
/-- `U₃ = (0,p,q,0)`, `V₃ = (p,0,0,q)`. -/
def U3 : Vec := ![0, p, q, 0]
def V3 : Vec := ![p, 0, 0, q]

lemma nu_vec (x0 x1 x2 x3 : ℕ) :
    nu ![x0, x1, x2, x3] = x0 * m + x1 * (m + a) + x2 * (m + b) + x3 * (m + w) := by
  simp [nu, Fin.sum_univ_four]

/-- **Lemma 8, first identity.** -/
theorem identity1 : nu U1 = nu V1 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le A_lt_B.le
  have e1 : B - A = k := by omega
  simp only [U1, V1, nu_vec, e1]
  rw [a_eq, b_eq, hk]; ring

/-- **Lemma 8, second identity.** -/
theorem identity2 : nu U2 = nu V2 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le A_lt_B.le
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le B_lt_W.le
  have e1 : B - A = k := by omega
  have e2 : W - B = l := by omega
  have e3 : W - A = k + l := by omega
  simp only [U2, V2, nu_vec, e1, e2, e3]
  rw [a_eq, b_eq, w_eq, hl, hk]; ring

/-- **Lemma 8, third identity.** -/
theorem identity3 : nu U3 = nu V3 := by
  simp only [U3, V3, nu_vec]
  rw [a_eq, b_eq, w_eq, W_eq_B_add_t]
  linear_combination g * p_mul_A

/-! ### Lemma 9 -/

/-- **Lemma 9 (coordinate 1).** At a degree splitting along a pair `K ∋ 1`, the selected
`K`-vector has `1 ≤ u ≤ B - 1` at coordinate `1`. -/
theorem sel_one_bounds (hS : IsSplit d K) (hK : K.card = 2)
    (h1 : 1 ∈ K) : 1 ≤ sel d K 1 ∧ sel d K 1 ≤ B - 1 := by
  refine ⟨sel_pos hS hK h1, ?_⟩
  by_contra hc
  have hB := two_le_B
  have hge : B ≤ sel d K 1 := by omega
  have key : ∀ K : F4, K.card = 2 → 1 ∈ K →
      (∃ k ∈ K, k ≠ 1) ∧ ((0 : Fin 4) ∉ K ∨ (2 : Fin 4) ∉ K) := by decide
  obtain ⟨⟨k, hkK, hk1⟩, h02⟩ := key K hK h1
  have hU : U1 ≤ sel d K := by intro i; fin_cases i <;> simp [U1, hge]
  have hUk : U1 k < sel d K k := by
    have := sel_pos hS hK hkK; fin_cases k <;> simp_all [U1]
  have hAB := A_lt_B
  have hA := A_pos
  rcases h02 with h0 | h2
  · exact no_replace hS hK hU identity1 hUk h0 (by simp [V1]; omega)
  · exact no_replace hS hK hU identity1 hUk h2 (by simp [V1]; omega)

/-- **Lemma 9 (coordinate 2).** At a degree splitting along a pair `K ∋ 2`, the selected
`K`-vector has `1 ≤ v ≤ W - A - 1` at coordinate `2`. -/
theorem sel_two_bounds (hS : IsSplit d K) (hK : K.card = 2)
    (h2 : 2 ∈ K) : 1 ≤ sel d K 2 ∧ sel d K 2 ≤ W - A - 1 := by
  refine ⟨sel_pos hS hK h2, ?_⟩
  by_contra hc
  have hWA := two_le_W_sub_A
  have hge : W - A ≤ sel d K 2 := by omega
  have key : ∀ K : F4, K.card = 2 → 2 ∈ K →
      (∃ k ∈ K, k ≠ 2) ∧ ((1 : Fin 4) ∉ K ∨ (3 : Fin 4) ∉ K) := by decide
  obtain ⟨⟨k, hkK, hk2⟩, h13⟩ := key K hK h2
  have hU : U2 ≤ sel d K := by intro i; fin_cases i <;> simp [U2, hge]
  have hUk : U2 k < sel d K k := by
    have := sel_pos hS hK hkK; fin_cases k <;> simp_all [U2]
  have hAB := A_lt_B
  have hBW := B_lt_W
  rcases h13 with h1 | h3
  · exact no_replace hS hK hU identity2 hUk h1 (by simp [V2]; omega)
  · exact no_replace hS hK hU identity2 hUk h3 (by simp [V2]; omega)

/-! ## Antichain -/

section AntichainVars

variable {F : Finset ℕ} {i k : Fin 4}

/-- Distinct members of `T` are coordinatewise incomparable. -/
def IsPairAntichain (T : Finset (ℕ × ℕ)) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x.1 ≤ y.1 → x.2 ≤ y.2 → x = y

variable {T : Finset (ℕ × ℕ)}

lemma IsPairAntichain.fst_inj (hT : IsPairAntichain T) {x y : ℕ × ℕ}
    (hx : x ∈ T) (hy : y ∈ T) (h : x.1 = y.1) : x = y := by
  rcases le_total x.2 y.2 with h2 | h2
  · exact hT x hx y hy h.le h2
  · exact (hT y hy x hx h.ge h2).symm

lemma IsPairAntichain.snd_inj (hT : IsPairAntichain T) {x y : ℕ × ℕ}
    (hx : x ∈ T) (hy : y ∈ T) (h : x.2 = y.2) : x = y := by
  rcases le_total x.1 y.1 with h1 | h1
  · exact hT x hx y hy h1 h.le
  · exact (hT y hy x hx h1 h.ge).symm

/-- **Lemma 11 (backward bound).** The number of members whose first coordinate is at least
`x.1` is at most `x.2`. -/
lemma IsPairAntichain.corank_le (hT : IsPairAntichain T)
    (hpos : ∀ x ∈ T, 1 ≤ x.1 ∧ 1 ≤ x.2) {x : ℕ × ℕ} (hx : x ∈ T) :
    (T.filter (fun y => x.1 ≤ y.1)).card ≤ x.2 := by
  have hle : ∀ y ∈ T, x.1 ≤ y.1 → y.2 ≤ x.2 := by
    intro y hy h1
    by_contra h2
    have := hT x hx y hy h1 (by omega)
    subst this; omega
  have := card_le_card_of_injOn (fun y : ℕ × ℕ => y.2)
    (s := T.filter (fun y => x.1 ≤ y.1)) (t := Icc 1 x.2)
    (fun y hy => mem_coe.2 (mem_Icc.2 ⟨(hpos y (mem_filter.1 (mem_coe.1 hy)).1).2,
      hle y (mem_filter.1 (mem_coe.1 hy)).1 (mem_filter.1 (mem_coe.1 hy)).2⟩))
    (fun y hy y' hy' h => hT.snd_inj (mem_filter.1 (mem_coe.1 hy)).1
      (mem_filter.1 (mem_coe.1 hy')).1 h)
  simpa using this

/-- If `x` has minimal first coordinate in `T`, then `T.card ≤ x.2`. -/
lemma IsPairAntichain.card_le_snd {T : Finset (ℕ × ℕ)} (hT : IsPairAntichain T)
    (hpos : ∀ x ∈ T, 1 ≤ x.1 ∧ 1 ≤ x.2) {x : ℕ × ℕ} (hx : x ∈ T)
    (hmin : ∀ y ∈ T, x.1 ≤ y.1) : T.card ≤ x.2 := by
  have := hT.corank_le hpos hx
  rwa [filter_true_of_mem hmin] at this


lemma isSplit_of_mem_fam (h : d ∈ fam K) : IsSplit d K :=
  (mem_fam.1 h).2.2.2

/-- Two selected `K`-vectors (`K = {i,k}`) are comparable iff their `i`- and `k`-coordinates are. -/
lemma sel_le_of_coords (hKe : K = {i, k}) (hK : K.card = 2)
    {d d' : ℕ} (hS : IsSplit d K) (hS' : IsSplit d' K)
    (hi : sel d K i ≤ sel d' K i) (hk : sel d K k ≤ sel d' K k) : sel d K ≤ sel d' K := by
  intro j
  by_cases hj : j ∈ K
  · rw [hKe, mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact hi
    · exact hk
  · rw [sel_eq_zero hS hK hj, sel_eq_zero hS' hK hj]

/-- The selected `(i, k)`-coordinate pairs of a family on side `K = {i,k}`. -/
noncomputable def pairsOf (F : Finset ℕ) (K : F4) (i k : Fin 4) : Finset (ℕ × ℕ) :=
  F.image (fun d => (sel d K i, sel d K k))

lemma pairsOf_injOn (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, IsSplit d K) :
    Set.InjOn (fun d => (sel d K i, sel d K k)) F := by
  have hK : K.card = 2 := by rw [hKe]; exact card_pair hik
  intro d hd d' hd' h
  simp only [Prod.mk.injEq] at h
  have hle := sel_le_of_coords hKe hK (hF d hd) (hF d' hd') h.1.le h.2.le
  have hge := sel_le_of_coords hKe hK (hF d' hd') (hF d hd) h.1.ge h.2.ge
  rw [← (sel_of_split (hF d hd) hK).1, ← (sel_of_split (hF d' hd') hK).1, le_antisymm hle hge]

lemma card_pairsOf (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, IsSplit d K) : (pairsOf F K i k).card = F.card :=
  card_image_of_injOn (pairsOf_injOn hik hKe hF)

lemma pairsOf_antichain (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, IsSplit d K) : IsPairAntichain (pairsOf F K i k) := by
  have hK : K.card = 2 := by rw [hKe]; exact card_pair hik
  intro x hx y hy h1 h2
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  obtain ⟨d', hd', rfl⟩ := mem_image.1 hy
  by_cases hne : d = d'
  · rw [hne]
  · exact absurd (sel_le_of_coords hKe hK (hF d hd) (hF d' hd') h1 h2)
      (sel_antichain hK (hF d hd) (hF d' hd') hne)

lemma pairsOf_pos (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, IsSplit d K) :
    ∀ x ∈ pairsOf F K i k, 1 ≤ x.1 ∧ 1 ≤ x.2 := by
  have hK : K.card = 2 := by rw [hKe]; exact card_pair hik
  intro x hx
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  exact ⟨sel_pos (hF d hd) hK (by rw [hKe]; simp),
    sel_pos (hF d hd) hK (by rw [hKe]; simp)⟩

/-- **Lemma 10 (injectivity).** Two selected `K`-vectors on a side with equal `k`-coordinates come
from the same degree. -/
lemma sel_coord_injOn (hik : i ≠ k) (hKe : K = {i, k})
    (F : Finset ℕ) (hF : ∀ d ∈ F, IsSplit d K) :
    Set.InjOn (fun d => sel d K k) F := by
  have hK : K.card = 2 := by rw [hKe]; exact card_pair hik
  intro d hd d' hd' h
  by_contra hne
  rcases le_total (sel d K i) (sel d' K i) with hi | hi
  · exact sel_antichain hK (hF d hd) (hF d' hd') hne
      (sel_le_of_coords hKe hK (hF d hd) (hF d' hd') hi h.le)
  · exact sel_antichain hK (hF d' hd') (hF d hd) (Ne.symm hne)
      (sel_le_of_coords hKe hK (hF d' hd') (hF d hd) hi h.ge)

/-- A family whose selected `k`-coordinates are injective with values in `[1, c]` has at most
`c` members. -/
lemma card_le_of_coord (hik : i ≠ k) (hKe : K = {i, k})
    (hF : ∀ d ∈ F, IsSplit d K) {c : ℕ}
    (hc : ∀ d ∈ F, 1 ≤ sel d K k ∧ sel d K k ≤ c) : F.card ≤ c := by
  have := card_le_card_of_injOn (fun d => sel d K k) (t := Icc 1 c)
    (fun d hd => mem_coe.2 (mem_Icc.2 (hc d (mem_coe.1 hd)))) (sel_coord_injOn hik hKe F hF)
  simpa using this

/-- **Saturation.** If the selected `k`-coordinates of a family of size `c` take values in
`[1, c]`, every value in `[1, c]` is attained. -/
lemma exists_coord_eq (hik : i ≠ k) (hKe : K = {i, k})
    (hF : ∀ d ∈ F, IsSplit d K) {c : ℕ}
    (hc : ∀ d ∈ F, 1 ≤ sel d K k ∧ sel d K k ≤ c) (hcard : F.card = c) {v : ℕ}
    (hv1 : 1 ≤ v) (hvc : v ≤ c) : ∃ d ∈ F, sel d K k = v := by
  have himage : F.image (fun d => sel d K k) = Icc 1 c := by
    apply eq_of_subset_of_card_le
    · intro x hx; obtain ⟨d, hd, rfl⟩ := mem_image.1 hx; exact mem_Icc.2 (hc d hd)
    · rw [card_image_of_injOn (sel_coord_injOn hik hKe F hF), hcard]; simp
  obtain ⟨d, hd, h⟩ := mem_image.1 (himage ▸ mem_Icc.2 ⟨hv1, hvc⟩)
  exact ⟨d, hd, h⟩

/-! ### Lemma 10 -/

/-- **Lemma 10.** `P ≤ R - 1`. -/
theorem P_le : P ≤ R - 1 := by
  have h1 : P ≤ B - 1 := card_le_of_coord (F := famP) (i := 0) (k := 1) (by decide) rfl
    (fun d hd => isSplit_of_mem_fam hd)
    (fun d hd => sel_one_bounds (isSplit_of_mem_fam hd) (by decide) (by decide))
  have h2 : P ≤ W - A - 1 := card_le_of_coord (F := famP) (K := K01ᶜ) (i := 3) (k := 2) (by decide) (by decide) (fun d hd => (isSplit_of_mem_fam hd).compl)
    (fun d hd => sel_two_bounds ((isSplit_of_mem_fam hd).compl) (by decide) (by decide))
  unfold R; omega

/-- **Lemma 10.** `Q ≤ R - 1`. -/
theorem Q_le : Q ≤ R - 1 := by
  have h1 : Q ≤ W - A - 1 := card_le_of_coord (F := famQ) (i := 0) (k := 2) (by decide) rfl
    (fun d hd => isSplit_of_mem_fam hd)
    (fun d hd => sel_two_bounds (isSplit_of_mem_fam hd) (by decide) (by decide))
  have h2 : Q ≤ B - 1 := card_le_of_coord (F := famQ) (K := K02ᶜ) (i := 3) (k := 1) (by decide) (by decide) (fun d hd => (isSplit_of_mem_fam hd).compl)
    (fun d hd => sel_one_bounds ((isSplit_of_mem_fam hd).compl) (by decide) (by decide))
  unfold R; omega

/-! ### Lemma 12 -/

lemma isSplit12_of_mem_famE (h : d ∈ famE) : IsSplit d K12 := by
  have hc : K03ᶜ = K12 := by decide
  exact hc ▸ (isSplit_of_mem_fam h).compl

/-- **Lemma 12, exclusion step.** At a degree of `ℰ`, the selected interior vector `(0,u,v,0)`
does not satisfy `u ≥ p`, `v ≥ q`, `(u,v) ≠ (p,q)`. -/
theorem not_dominates_pq (hd : d ∈ famE) (hu : p ≤ sel d K12 1)
    (hv : q ≤ sel d K12 2) (hne : (sel d K12 1, sel d K12 2) ≠ (p, q)) : False := by
  have hS := isSplit12_of_mem_famE hd
  have hK : K12.card = 2 := by decide
  have hU : U3 ≤ sel d K12 := by
    intro i; fin_cases i <;> simp [U3, hu, hv]
  have hp := p_pos
  by_cases h1 : p < sel d K12 1
  · exact no_replace hS hK hU identity3 (k := 1) (by simpa [U3] using h1)
      (j := 0) (by decide) (by simp [V3]; omega)
  · have h2 : q < sel d K12 2 := by
      by_contra h2
      exact hne (Prod.ext (by simp only; omega) (by simp only; omega))
    exact no_replace hS hK hU identity3 (k := 2) (by simpa [U3] using h2)
      (j := 0) (by decide) (by simp [V3]; omega)

/-- The selected interior pairs `(u, v)` over `ℰ`. -/
noncomputable def pairsE : Finset (ℕ × ℕ) := pairsOf famE K12 1 2

lemma pairsE_antichain : IsPairAntichain pairsE :=
  pairsOf_antichain (by decide) (by decide) (fun d hd => isSplit12_of_mem_famE hd)

lemma pairsE_pos : ∀ x ∈ pairsE, 1 ≤ x.1 ∧ 1 ≤ x.2 :=
  pairsOf_pos (by decide) (by decide) (fun d hd => isSplit12_of_mem_famE hd)

/-- **Lemma 12.** `E ≤ p + q - 1`. -/
theorem E_le : E ≤ p + q - 1 := by
  by_contra hc
  have hp := p_pos
  have hq := q_pos
  have hcard : p + q ≤ pairsE.card := by
    have h : pairsE.card = E := by
      rw [pairsE, card_pairsOf (i := 1) (k := 2) (by decide) (by decide)
        (fun d hd => isSplit12_of_mem_famE hd)]
      rfl
    omega
  have hT := pairsE_antichain
  have hpos := pairsE_pos
  set A := pairsE.filter (fun x => x.1 ≤ p - 1) with hA
  set Bl := pairsE.filter (fun x => x.2 ≤ q - 1) with hB
  have hAle : A.card ≤ p - 1 := by
    have := card_le_card_of_injOn (fun x : ℕ × ℕ => x.1) (s := A) (t := Icc 1 (p - 1))
      (fun x hx => mem_coe.2 (mem_Icc.2 ⟨(hpos x (mem_filter.1 (mem_coe.1 hx)).1).1,
        (mem_filter.1 (mem_coe.1 hx)).2⟩))
      (fun x hx y hy h => hT.fst_inj (mem_filter.1 (mem_coe.1 hx)).1
        (mem_filter.1 (mem_coe.1 hy)).1 h)
    simpa using this
  have hBle : Bl.card ≤ q - 1 := by
    have := card_le_card_of_injOn (fun x : ℕ × ℕ => x.2) (s := Bl) (t := Icc 1 (q - 1))
      (fun x hx => mem_coe.2 (mem_Icc.2 ⟨(hpos x (mem_filter.1 (mem_coe.1 hx)).1).2,
        (mem_filter.1 (mem_coe.1 hx)).2⟩))
      (fun x hx y hy h => hT.snd_inj (mem_filter.1 (mem_coe.1 hx)).1
        (mem_filter.1 (mem_coe.1 hy)).1 h)
    simpa using this
  have hsub : pairsE ⊆ A ∪ Bl ∪ {(p, q)} := by
    intro x hx
    by_cases h1 : x.1 ≤ p - 1
    · simp [hA, hx, h1]
    · by_cases h2 : x.2 ≤ q - 1
      · simp [hB, hx, h2]
      · push Not at h1 h2
        have hxq : x = (p, q) := by
          by_contra hne
          obtain ⟨d, hd, rfl⟩ := mem_image.1
            (show x ∈ famE.image (fun d => (sel d K12 1, sel d K12 2)) from hx)
          exact not_dominates_pq hd (by omega) (by omega) hne
        simp [hxq]
  have h3 : (A ∪ Bl ∪ {(p, q)}).card ≤ A.card + Bl.card + 1 := by
    refine (card_union_le _ _).trans ?_
    have := card_union_le A Bl
    simp only [card_singleton]
    omega
  have := card_le_card hsub
  omega

/-! ## Exceptional -/

/-! ### Facts in the exceptional case -/

section Exceptional

variable (hA : A = 1) (hB : B = W - 1)
include hA hB
set_option linter.unusedSectionVars false

lemma exc_R : R = W - 1 := by
  have := three_le_W; unfold R; omega

lemma exc_p : p = 1 := by
  have := three_le_W
  have ht : t = 1 := by unfold t; omega
  have hs : s = 1 := hA
  unfold p dg; rw [ht, hs]; rfl

lemma exc_q : q = 1 := by
  have := three_le_W
  have ht : t = 1 := by unfold t; omega
  have hs : s = 1 := hA
  unfold q dg; rw [ht, hs]; rfl

lemma exc_U2 : U2 = Pi.single 2 (W - 1) := by
  funext j; fin_cases j <;> simp [U2, hA]

lemma exc_V2 : V2 = ![0, 1, 0, W - 2] := by
  have := three_le_W
  have h1 : W - B = 1 := by omega
  have h2 : B - A = W - 2 := by omega
  simp only [V2, h1, h2]

/-- `ν(0,0,W-1,0) = ν(0,1,0,W-2)`, both equal to `(W-1) n₂`. -/
lemma exc_nu_V2 : nu ![0, 1, 0, W - 2] = (W - 1) * n 2 := by
  rw [← exc_V2 hA hB, ← identity2, exc_U2 hA hB, nu_single]

/-- `gcd(n₂, n₃) = 1` in the exceptional family. -/
lemma exc_coprime : Nat.Coprime (n 3) (n 2) := by
  have hn2 : n 2 = m + g * (W - 1) := by rw [n_two, b_eq, hB]
  have hn3 : n 3 = n 2 + g := by
    rw [hn2, n_three, w_eq]
    have hW := three_le_W
    have : W = (W - 1) + 1 := by omega
    conv_lhs => rw [this]
    ring
  rw [Nat.coprime_iff_gcd_eq_one, hn3, Nat.gcd_comm, show n 2 + g = g + n 2 by ring,
    Nat.gcd_add_self_right, Nat.gcd_comm, hn2,
    show m + g * (W - 1) = m + (W - 1) * g by ring, Nat.gcd_comm, Nat.gcd_add_mul_right_left,
    Nat.gcd_comm, gcd_m_g]

end Exceptional

/-! ### Lemma 14 -/

lemma sideP_split (hd : d ∈ famP) : IsSplit d K23 := by
  have hc : K01ᶜ = K23 := by decide
  exact hc ▸ (isSplit_of_mem_fam hd).compl

lemma sideQ_split (hd : d ∈ famQ) : IsSplit d K13 := by
  have hc : K02ᶜ = K13 := by decide
  exact hc ▸ (isSplit_of_mem_fam hd).compl

/-- **Lemma 14.** If `A = 1`, `B = W - 1` and `P = W - 2`, then `c₂ = W - 1`. -/
theorem lemma14 (hA : A = 1) (hB : B = W - 1) (hP : P = W - 2) :
    crit 2 = W - 1 := by
  have hW := three_le_W
  have hle : crit 2 ≤ W - 1 := by
    apply Nat.find_min'
    rw [isCritCand_iff]
    exact ⟨by omega, ![0, 1, 0, W - 2], exc_nu_V2 hA hB,
      fun h => by have := congrFun h 1; simp at this⟩
  by_contra hne
  have hc : crit 2 ≤ W - 2 := by omega
  have hc1 := one_le_crit 2
  have hK : K23.card = 2 := by decide
  -- saturation: some `𝓟` degree has selected `23`-vector `(0,0,W-2,y)`
  obtain ⟨D, hD, hzD⟩ := exists_coord_eq (F := famP) (K := K23) (i := 3) (k := 2) (by decide) (by decide)
    (fun d hd => sideP_split hd)
    (fun d hd => by
      have := sel_two_bounds (sideP_split hd) hK (by decide); rw [hA] at this; exact this)
    hP (v := W - 2) (by omega) le_rfl
  have hS23 := sideP_split hD
  have hS01 := isSplit_of_mem_fam hD
  set z := sel D K23 with hz
  have hz0 : z 0 = 0 := sel_eq_zero hS23 hK (by decide)
  have hz1 : z 1 = 0 := sel_eq_zero hS23 hK (by decide)
  have hz3 : 0 < z 3 := sel_pos hS23 hK (by decide)
  have hnuz : nu z = D := (sel_of_split hS23 hK).1
  -- the alternative `r` at the critical degree avoids `2`, and the bridge uses a coordinate
  -- `j ∉ {2,3}` where `r` and the `01`-selected vector are both positive
  obtain ⟨r, hr, hrne⟩ := exists_alt 2
  have hr2 := alt_coord_eq_zero hr hrne
  have hK01 : K01.card = 2 := by decide
  obtain ⟨j, hjr, hjK, hj3⟩ : ∃ j : Fin 4, 0 < r j ∧ j ∉ K23 ∧ 0 < sel D K01 j := by
    by_cases h0 : 0 < r 0
    · exact ⟨0, h0, by decide, sel_pos hS01 hK01 (by decide)⟩
    · have h1 : 0 < r 1 := by
        by_contra h1
        have hr0 : r 0 = 0 := by omega
        have hr1 : r 1 = 0 := by omega
        have hreq : r = Pi.single 3 (r 3) := by
          funext k; fin_cases k <;> simp [hr0, hr1, hr2]
        rw [hreq, nu_single] at hr
        have hdvd : n 3 ∣ crit 2 * n 2 := ⟨r 3, by rw [← hr, mul_comm]⟩
        have := Nat.le_of_dvd (by omega) ((exc_coprime hA hB).dvd_of_dvd_mul_right hdvd)
        have := W_le_w
        have hn3 : n 3 = m + w := rfl
        omega
      exact ⟨1, h1, by decide, sel_pos hS01 hK01 (by decide)⟩
  let b := r + Pi.single 2 (W - 2 - crit 2) + Pi.single 3 (z 3)
  have hb : nu b = D := by
    simp only [b]
    rw [nu_add, nu_add, nu_single, nu_single, hr, ← hnuz, nu_eq_sum z, hz0, hz1, hzD,
      ← Nat.add_mul, Nat.add_sub_cancel' hc, n_two, n_three]
    ring
  refine no_bridge hS23 hnuz (sel_of_split hS01 hK01).1 hb (i := 3) (by decide) hz3 hjK hj3
    ⟨3, ?_, hz3⟩ ⟨j, ?_, hj3⟩
  · simp [b]; omega
  · simp [b]; omega

/-- **Lemma 15.** If `A = 1`, `B = W - 1` and `Q = W - 2`, then some `𝓠` degree has selected
`13`-vector with `u = 1`, and every such vector is exactly `(0,1,0,W-2)`. -/
theorem lemma15 (hA : A = 1) (hB : B = W - 1) (hQ : Q = W - 2) :
    (∃ D ∈ famQ, sel D K13 1 = 1) ∧
      ∀ D ∈ famQ, sel D K13 1 = 1 → sel D K13 = ![0, 1, 0, W - 2] := by
  have hW := three_le_W
  have hK : K13.card = 2 := by decide
  have hF : ∀ d ∈ famQ, IsSplit d K13 := fun d hd => sideQ_split hd
  refine ⟨?_, ?_⟩
  · exact exists_coord_eq (F := famQ) (K := K13) (i := 3) (k := 1) (by decide) (by decide) hF
      (fun d hd => by
        have := sel_one_bounds (hF d hd) hK (by decide); rw [hB] at this; exact this)
      (by have : Q = famQ.card := rfl; omega) (v := 1) le_rfl (by omega)
  · intro D hD hu
    have hS := hF D hD
    have hz0 : sel D K13 0 = 0 := sel_eq_zero hS hK (by decide)
    have hz2 : sel D K13 2 = 0 := sel_eq_zero hS hK (by decide)
    -- lower bound `v ≥ W - 2` from Lemma 11
    have hT := pairsOf_antichain (F := famQ) (i := 1) (k := 3) (by decide) (by decide) hF
    have hpos := pairsOf_pos (F := famQ) (i := 1) (k := 3) (by decide) (by decide) hF
    have hmem : (sel D K13 1, sel D K13 3) ∈ pairsOf famQ K13 1 3 :=
      mem_image.2 ⟨D, hD, rfl⟩
    have hco := hT.card_le_snd hpos hmem (fun y hy => by rw [hu]; exact (hpos y hy).1)
    rw [card_pairsOf (by decide) (by decide) hF, show famQ.card = W - 2 from hQ] at hco
    -- upper bound `v ≤ W - 2` by the exceptional replacement
    have hv : sel D K13 3 ≤ W - 2 := by
      by_contra hv
      have hU : V2 ≤ sel D K13 := by
        rw [exc_V2 hA hB]; intro j; fin_cases j <;> simp [hz0, hz2, hu]; omega
      exact no_replace hS hK hU identity2.symm (k := 3)
        (by rw [exc_V2 hA hB]; simp; omega) (j := 2) (by decide)
        (by rw [exc_U2 hA hB]; simp; omega)
    funext j; fin_cases j <;> simp [hz0, hz2, hu]; omega

/-! ### Lemma 16 -/

/-- **Lemma 16.** If `(A, B) = (1, W - 1)` then `P + Q ≤ 2W - 5`. -/
theorem lemma16_PQ (hA : A = 1) (hB : B = W - 1) : P + Q ≤ 2 * W - 5 := by
  have hW := three_le_W
  have hP := P_le
  have hQ := Q_le
  rw [exc_R hA hB] at hP hQ
  by_contra hc
  have hP' : P = W - 2 := by omega
  have hQ' : Q = W - 2 := by omega
  have hc2 := lemma14 hA hB hP'
  obtain ⟨⟨D, hD, hu⟩, hall⟩ := lemma15 hA hB hQ'
  have hsel := hall D hD hu
  have hK : K13.card = 2 := by decide
  have hDeq : D = crit 2 * n 2 := by
    rw [← (sel_of_split (sideQ_split hD) hK).1, hsel, exc_nu_V2 hA hB, hc2]
  obtain ⟨-, hcon, hS, -⟩ := mem_fam.1 hD
  subst hDeq
  exact hS ⟨_, by rw [compSupp_critVertex 2]; rfl⟩

/-- **Lemma 16.** If `(A, B) = (1, W - 1)` then `β₁ ≤ 2W`. -/
theorem beta1_le_two_W_exceptional (hA : A = 1) (hB : B = W - 1) :
    beta1 ≤ 2 * W := by
  have hW := three_le_W
  have hPQ := lemma16_PQ hA hB
  have hE := E_le
  rw [exc_p hA hB, exc_q hA hB] at hE
  have hσ := sigma_le_four
  rw [beta1_eq]
  omega

/-! ## Arith -/

/-- **Lemma 13 (general bound).** `β₁ ≤ 4 + 2(R - 1) + (p + q - 1)`. -/
theorem beta1_le_general : beta1 ≤ 4 + 2 * (R - 1) + (p + q - 1) := by
  rw [beta1_eq]
  have := sigma_le_four
  have := P_le
  have := Q_le
  have := E_le
  omega

/-- **Lemma 13 (closed form).** `4 + 2(R-1) + (p+q-1) = 2W - 2 max(s,t) + (s+t)/d + 1`. -/
theorem general_bound_eq :
    4 + 2 * (R - 1) + (p + q - 1) = 2 * W - 2 * max s t + (s + t) / dg + 1 := by
  rw [← p_add_q_eq, R_eq]
  have := two_le_R; rw [R_eq] at this
  have := p_pos
  omega

lemma dg_eq_s_of_s_eq_t (h : s = t) : dg = s := by unfold dg; rw [← h, Nat.gcd_self]

/-- The exceptional case `(s,t) = (1,1)` is exactly `(A, B) = (1, W - 1)`. -/
lemma st_eq_one_one_iff : (s, t) = (1, 1) ↔ A = 1 ∧ B = W - 1 := by
  have := B_lt_W
  simp only [Prod.mk.injEq, s, t]
  omega

/-- **Lemma 13.** If `(s,t) ≠ (1,1)` then `β₁ ≤ 2W`. -/
theorem beta1_le_two_W_of_ne (h : (s, t) ≠ (1, 1)) : beta1 ≤ 2 * W := by
  have hb := beta1_le_general
  rw [general_bound_eq] at hb
  have hs := s_pos
  have ht := t_pos
  have hR := two_le_R
  rw [R_eq] at hR
  rw [← p_add_q_eq] at hb
  have hpq := p_add_q_le
  rcases lt_trichotomy s t with hlt | heq | hgt
  · -- Case 1: `s < t`
    omega
  · -- Cases 3–4: `s = t`, so `d = s` and `p = q = 1`
    have hdg : dg = s := dg_eq_s_of_s_eq_t heq
    have hp : p = 1 := by
      have := dg_mul_p; rw [hdg, ← heq] at this
      exact (Nat.mul_eq_left (by omega)).1 this
    have hq : q = 1 := by
      have := dg_mul_q; rw [hdg] at this
      exact (Nat.mul_eq_left (by omega)).1 this
    have hs2 : 2 ≤ s := by
      by_contra hc
      exact h (Prod.ext (by simp only; omega) (by simp only; omega))
    omega
  · -- Case 2: `s > t`
    omega

end AntichainVars

end PairSide

/-! ## Bridge -/
section Mono

variable (K : Type*) [Field K]

/-- The monomial `X^z` for `z : Vec`. -/
noncomputable def mono (z : Vec) : MvPolynomial (Fin 4) K :=
  monomial (Finsupp.equivFunOnFinite.symm z) 1

/-- The toric map `K[X₀,…,X₃] → K[t]`, `Xᵢ ↦ t^{nᵢ}`. -/
noncomputable def toricMap (n : Vec) : MvPolynomial (Fin 4) K →ₐ[K] Polynomial K :=
  aeval (fun i => (Polynomial.X : Polynomial K) ^ n i)

variable {K}

lemma mono_coe (s : Fin 4 →₀ ℕ) : mono K ⇑s = monomial s 1 := by
  simp [mono]

lemma toricMap_monomial (n : Vec) (s : Fin 4 →₀ ℕ) (c : K) :
    toricMap K n (monomial s c) = Polynomial.C c * Polynomial.X ^ (∑ i, s i * n i) := by
  rw [toricMap, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum, Polynomial.algebraMap_eq]
  congr 2
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma X_mul_mono (i : Fin 4) (u : Vec) :
    (X i : MvPolynomial (Fin 4) K) * mono K u = mono K (u + Pi.single i 1) := by
  rw [mono, mono, X, monomial_mul_monomial, one_mul]
  have : Finsupp.single i 1 + Finsupp.equivFunOnFinite.symm u =
      Finsupp.equivFunOnFinite.symm (u + Pi.single i 1) := by
    refine Finsupp.ext fun j => ?_
    by_cases h : j = i
    · subst h; simp [add_comm]
    · simp [h]
  rw [this]

end Mono

variable {d : ℕ} (K : Type*) [Field K]

lemma toricMap_mono (z : Vec) : toricMap K n (mono K z) = Polynomial.X ^ nu z := by
  rw [mono, toricMap_monomial]; simp [nu]

/-- The toric ideal, written exactly as in `Challenge.lean` (`SemigroupBetti.toricIdeal K n`
unfolds to this). -/
noncomputable abbrev toricKer : Ideal (MvPolynomial (Fin 4) K) :=
  RingHom.ker (MvPolynomial.aeval (fun i => (Polynomial.X : Polynomial K) ^ n i)).toRingHom

lemma mem_toricKer {f : MvPolynomial (Fin 4) K} : f ∈ toricKer K ↔ toricMap K n f = 0 :=
  RingHom.mem_ker

/-! ### Representatives, base components, and the generating binomials -/

/-- A chosen representative factorization of a component of `∇_d`. -/
noncomputable def rep (C : Comp d) : Vec :=
  (Quot.out C : fiber d).1

lemma nu_rep (C : Comp d) : nu (rep C) = d :=
  mem_fiber.1 (Quot.out C).2

lemma rep_mk (C : Comp d) :
    cmk (⟨rep C, (Quot.out C).2⟩ : fiber d) = C :=
  Quot.out_eq C

open Classical in
/-- The chosen binomials of degree `d`: `X^{rep C} - X^{rep C₀}` for `C ≠ C₀`, where `C₀` is
a fixed base component (none if the fiber is empty). -/
noncomputable def genSet (d : ℕ) : Finset (MvPolynomial (Fin 4) K) :=
  if h : Nonempty (Comp d) then
    (univ.erase (Classical.choice h)).image
      (fun C => mono K (rep C) - mono K (rep (Classical.choice h)))
  else ∅

open Classical in
/-- All chosen binomials, over the degrees `d ≤ H`. -/
noncomputable def binomGens : Finset (MvPolynomial (Fin 4) K) :=
  (range (H + 1)).biUnion (genSet K)

lemma card_binomGens_le : #(binomGens K) ≤ beta1 := by
  classical
  refine (card_biUnion_le).trans (sum_le_sum fun d _ => ?_)
  unfold genSet
  split_ifs with h
  · refine (card_image_le).trans ?_
    rw [card_erase_of_mem (mem_univ _), card_univ, ncomp]
  · simp

lemma binomGens_subset_toricKer : (binomGens K : Set (MvPolynomial (Fin 4) K)) ⊆ toricKer K := by
  classical
  intro p hp
  simp only [binomGens, coe_biUnion, coe_range, Set.mem_iUnion, mem_coe] at hp
  obtain ⟨d, -, hp⟩ := hp
  unfold genSet at hp
  split_ifs at hp with h
  · obtain ⟨C, -, rfl⟩ := mem_image.1 hp
    change mono K (rep C) - mono K (rep (Classical.choice h)) ∈ toricKer K
    rw [mem_toricKer, map_sub, toricMap_mono, toricMap_mono, nu_rep, nu_rep, sub_self]
  · simp at hp

/-! ### Every equal-degree binomial lies in the span -/

/-- Edge step (write-up Lemma 0C): if `z, z'` of degree `d` share a variable `i`, then
`X^z - X^{z'} = Xᵢ (X^{z-eᵢ} - X^{z'-eᵢ})`, and the inner binomial has degree `d - nᵢ < d`. -/
lemma sub_mem_of_sharesVar {J : Ideal (MvPolynomial (Fin 4) K)} 
    (IH : ∀ e < d, ∀ z z' : Vec, nu z = e → nu z' = e → mono K z - mono K z' ∈ J)
    {z z' : Vec} (hz : nu z = d) (hz' : nu z' = d) (h : SharesVar z z') :
    mono K z - mono K z' ∈ J := by
  obtain ⟨i, hi, hi'⟩ := h
  have key : ∀ y : Vec, 0 < y i → y = (y - Pi.single i 1) + Pi.single i 1 := by
    intro y hy; ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [hj]
  have hdeg : ∀ y : Vec, 0 < y i → nu y = nu (y - Pi.single i 1) + n i := by
    intro y hy
    conv_lhs => rw [key y hy]
    rw [nu_add, nu_single, one_mul]
  rw [key z hi, key z' hi', ← X_mul_mono, ← X_mul_mono, ← mul_sub]
  refine J.mul_mem_left _ (IH (nu (z - Pi.single i 1)) ?_ _ _ rfl ?_)
  · have := hdeg z hi; have := n_pos i; omega
  · have := hdeg z hi; have := hdeg z' hi'; omega

/-- Path step (write-up Lemma 0D). -/
lemma sub_mem_of_reachable {J : Ideal (MvPolynomial (Fin 4) K)} 
    (IH : ∀ e < d, ∀ z z' : Vec, nu z = e → nu z' = e → mono K z - mono K z' ∈ J)
    {x y : fiber d} (h : (nabla d).Reachable x y) : mono K x.1 - mono K y.1 ∈ J := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons u v w hadj _ ih =>
    rw [← sub_add_sub_cancel _ (mono K v.1) _]
    exact add_mem (sub_mem_of_sharesVar K IH (mem_fiber.1 u.2) (mem_fiber.1 v.2) hadj.2) ih

/-- Base-component step (write-up Lemma 0D/0F): the chosen binomials link any two
representatives at a degree `d ≤ H`. -/
lemma rep_sub_rep_mem (hd : d ≤ H) (C C' : Comp d) :
    mono K (rep C) - mono K (rep C') ∈ Ideal.span (binomGens K : Set _) := by
  classical
  have h : Nonempty (Comp d) := ⟨C⟩
  have base : ∀ D : Comp d, mono K (rep D) - mono K (rep (Classical.choice h)) ∈
      Ideal.span (binomGens K : Set _) := by
    intro D
    by_cases hD : D = Classical.choice h
    · rw [hD, sub_self]; exact zero_mem _
    · apply Ideal.subset_span
      simp only [binomGens, coe_biUnion, coe_range, Set.mem_iUnion, mem_coe, Set.mem_Iio]
      refine ⟨d, by omega, ?_⟩
      unfold genSet
      simp only [h, ↓reduceDIte]
      exact mem_image.2 ⟨D, mem_erase.2 ⟨hD, mem_univ _⟩, rfl⟩
  rw [← sub_sub_sub_cancel_right _ _ (mono K (rep (Classical.choice h)))]
  exact sub_mem (base C) (base C')

/-- **Lemma 0 (B–F), binomial form.** Every binomial `X^z - X^{z'}` with `ν z = ν z'` lies in
the ideal spanned by the chosen binomials. -/
lemma mono_sub_mem_span (d : ℕ) : ∀ z z' : Vec, nu z = d → nu z' = d →
    mono K z - mono K z' ∈ Ideal.span (binomGens K : Set _) := by
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro z z' hz hz'
  obtain ⟨x, hx⟩ : ∃ x : fiber d, x.1 = z := ⟨⟨z, mem_fiber.2 hz⟩, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : fiber d, y.1 = z' := ⟨⟨z', mem_fiber.2 hz'⟩, rfl⟩
  subst hx hy
  by_cases hr : (nabla d).Reachable x y
  · exact sub_mem_of_reachable K IH hr
  · set Cx := cmk x
    set Cy := cmk y
    have hne : Cx ≠ Cy := fun h => hr (SimpleGraph.ConnectedComponent.exact h)
    have hd : d ≤ H := le_H_of_contributes (by
      unfold contributes ncomp
      exact Fintype.one_lt_card_iff.2 ⟨Cx, Cy, hne⟩)
    have h1 : mono K x.1 - mono K (rep Cx) ∈ Ideal.span (binomGens K : Set _) :=
      sub_mem_of_reachable K IH (x := x) (y := ⟨rep Cx, (Quot.out Cx).2⟩)
        (SimpleGraph.ConnectedComponent.exact (rep_mk Cx).symm)
    have h2 : mono K (rep Cy) - mono K y.1 ∈ Ideal.span (binomGens K : Set _) :=
      sub_mem_of_reachable K IH (x := ⟨rep Cy, (Quot.out Cy).2⟩) (y := y)
        (SimpleGraph.ConnectedComponent.exact (rep_mk Cy))
    have h3 := rep_sub_rep_mem K hd Cx Cy
    have : mono K x.1 - mono K y.1 = (mono K x.1 - mono K (rep Cx)) +
        (mono K (rep Cx) - mono K (rep Cy)) + (mono K (rep Cy) - mono K y.1) := by ring
    rw [this]
    exact add_mem (add_mem h1 h3) h2

/-! ### The kernel is spanned by equal-degree binomials -/

open Classical in
/-- A chosen factorization of `d` (junk `0` when the fiber is empty). -/
noncomputable def root (d : ℕ) : Vec :=
  if h : (fiber d).Nonempty then h.choose else 0

/-- **Lemma 0B.** An element of the kernel has zero coefficient sum on every fiber. -/
lemma coeff_sum_eq_zero {f : MvPolynomial (Fin 4) K} (hf : f ∈ toricKer K) (d : ℕ) :
    ∑ s ∈ f.support.filter (fun s : Fin 4 →₀ ℕ => nu ⇑s = d), f.coeff s = 0 := by
  have hφ := (mem_toricKer K).1 hf
  rw [f.as_sum, map_sum] at hφ
  have := congrArg (fun p : Polynomial K => p.coeff d) hφ
  simp only [toricMap_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at this
  rw [Finset.sum_filter]
  simpa [nu, eq_comm] using this

lemma toricKer_le_span : toricKer K ≤ Ideal.span (binomGens K : Set _) := by
  intro f hf
  set J := Ideal.span (binomGens K : Set (MvPolynomial (Fin 4) K))
  have hsplit : f = ∑ s ∈ f.support, C (f.coeff s) * (mono K s - mono K (root (nu s))) +
      ∑ s ∈ f.support, C (f.coeff s) * mono K (root (nu s)) := by
    rw [← sum_add_distrib]
    simp_rw [← mul_add, sub_add_cancel, mono_coe, C_mul_monomial, mul_one]
    exact f.as_sum
  have hzero : ∑ s ∈ f.support, C (f.coeff s) * mono K (root (nu s)) = 0 := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun s : Fin 4 →₀ ℕ => nu s)
      (t := f.support.image (fun s : Fin 4 →₀ ℕ => nu s)) (fun s hs => mem_image_of_mem _ hs)]
    refine Finset.sum_eq_zero fun d _ => ?_
    have : ∀ s ∈ f.support.filter (fun s : Fin 4 →₀ ℕ => nu ⇑s = d),
        C (f.coeff s) * mono K (root (nu s)) = C (f.coeff s) * mono K (root d) := by
      intro s hs; rw [(mem_filter.1 hs).2]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← map_sum, coeff_sum_eq_zero K hf d,
      map_zero, zero_mul]
  rw [hsplit, hzero, add_zero]
  exact J.sum_mem fun s _ => J.mul_mem_left _
    (mono_sub_mem_span K (nu s) s _ rfl (by
      have h : (fiber (nu s)).Nonempty := ⟨s, mem_fiber.2 rfl⟩
      rw [root]; simp only [h, ↓reduceDIte]
      exact mem_fiber.1 h.choose_spec))

/-! ### Main theorems -/

/-- **Lemma 0F.** The toric ideal is generated by the chosen binomials. -/
theorem toricKer_eq_span : toricKer K = Ideal.span (binomGens K : Set _) :=
  le_antisymm (toricKer_le_span K) (Ideal.span_le.2 (binomGens_subset_toricKer K))

/-- **Bridge (inequality half of Lemma 0).** `μ(I) ≤ β₁`, with `μ` = `Submodule.spanRank`. -/
theorem spanRank_toricKer_le_beta1 :
    (RingHom.ker (MvPolynomial.aeval (R := K)
      (fun i => (Polynomial.X : Polynomial K) ^ n i)).toRingHom).spanRank ≤
      (beta1 : Cardinal) := by
  change (toricKer K).spanRank ≤ _
  rw [toricKer_eq_span K]
  calc (Ideal.span (binomGens K : Set (MvPolynomial (Fin 4) K))).spanRank
      ≤ Cardinal.mk (binomGens K : Set (MvPolynomial (Fin 4) K)) :=
        Submodule.spanRank_span_le_card _
    _ = (#(binomGens K) : Cardinal) := Cardinal.mk_coe_finset
    _ ≤ (beta1 : Cardinal) := Nat.cast_le.2 (card_binomGens_le K)

/-! ### From the hypotheses of `Challenge.lean` to `GenData` -/

/-- Build the generator data from the hypotheses of `Challenge.lean`:
`0 < n 0`, `StrictMono n` and `Finset.univ.gcd n = 1`. -/
def ofChallenge (v : Vec) (hpos : 0 < v 0) (hmono : StrictMono v)
    (hgcd : Finset.univ.gcd v = 1) : GenData where
  m := v 0
  a := v 1 - v 0
  b := v 2 - v 0
  w := v 3 - v 0
  m_pos := hpos
  a_pos := by have h := hmono (by decide : (0 : Fin 4) < 1); omega
  a_lt_b := by
    have h1 := hmono (by decide : (0 : Fin 4) < 1)
    have h2 := hmono (by decide : (1 : Fin 4) < 2); omega
  b_lt_w := by
    have h1 := hmono (by decide : (0 : Fin 4) < 2)
    have h2 := hmono (by decide : (2 : Fin 4) < 3); omega
  gcd_eq_one := by
    let D := Nat.gcd (v 0) (Nat.gcd (v 1 - v 0) (Nat.gcd (v 2 - v 0) (v 3 - v 0)))
    have hall : D ∣ Finset.univ.gcd v := by
      refine Finset.dvd_gcd fun i _ => ?_
      have h0 : D ∣ v 0 := Nat.gcd_dvd_left _ _
      have hi : D ∣ v i - v 0 := by
        fin_cases i
        · simp
        · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
        · exact (Nat.gcd_dvd_right _ _).trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))
        · exact (Nat.gcd_dvd_right _ _).trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
      rw [← Nat.add_sub_cancel' (hmono.monotone (Fin.zero_le i))]
      exact Nat.dvd_add h0 hi
    change D = 1
    rw [hgcd] at hall
    exact Nat.dvd_one.1 hall

lemma ofChallenge_n (v : Vec) (hpos : 0 < v 0) (hmono : StrictMono v)
    (hgcd : Finset.univ.gcd v = 1) :
    n (G := ofChallenge v hpos hmono hgcd) = v := by
  have h1 := hmono (by decide : (0 : Fin 4) < 1)
  have h2 := hmono (by decide : (0 : Fin 4) < 2)
  have h3 := hmono (by decide : (0 : Fin 4) < 3)
  funext i
  fin_cases i
  · rfl
  · change v 0 + (v 1 - v 0) = v 1; omega
  · change v 0 + (v 2 - v 0) = v 2; omega
  · change v 0 + (v 3 - v 0) = v 3; omega

/-! ## Main -/

/-- **Main combinatorial theorem.** `β₁ ≤ 2W`. -/
theorem beta1_le_two_W : beta1 ≤ 2 * W := by
  by_cases h : (s, t) = (1, 1)
  · obtain ⟨hA, hB⟩ := st_eq_one_one_iff.1 h
    exact beta1_le_two_W_exceptional hA hB
  · exact beta1_le_two_W_of_ne h

/-- `β₁ ≤ 2w`. -/
theorem beta1_le_two_w : beta1 ≤ 2 * G.w :=
  beta1_le_two_W.trans (Nat.mul_le_mul_left 2 W_le_w)

end SemigroupBetti
