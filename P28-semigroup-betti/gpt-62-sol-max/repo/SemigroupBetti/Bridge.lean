/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

public import SemigroupBetti.Counting

/-! Critical pure powers and closed two-pair splits generate the toric ideal.
In the quotient by these binomials, induction on degree first handles shared
variables, and then reduces each factorization to a common representative. -/

@[expose] public section

namespace SemigroupBetti

open Finset Finsupp MvPolynomial
attribute [local simp] weight_single
noncomputable section

variable (K : Type*) [Field K]

local notation "M" => MvPolynomial (Fin 4) K

/-- The kernel of evaluation at the powers of `X` with exponents `n`. -/
def toricIdeal (n : Fin 4 → ℕ) : Ideal M :=
  RingHom.ker (MvPolynomial.aeval (fun i => (Polynomial.X : Polynomial K) ^ n i)).toRingHom

namespace GenData

variable (G : GenData)

local notation "φ" => aeval (fun i => (Polynomial.X : Polynomial K) ^ G.n i)

local notation "mon " z:arg => monomial z (1 : K)

@[simp] private lemma eval_mono (z : Vec) :
    φ (mon z) = Polynomial.basisMonomials K (G.nu z) := by
  simp [aeval_monomial, Finsupp.prod, ← pow_mul, prod_pow_eq_pow_sum, weight_apply,
    Finsupp.sum, mul_comm, ← Polynomial.X_pow_eq_monomial]

private abbrev Mixed (x : Vec) := 1 < x.support.card

private def Preferred (d : ℕ) (x : Vec) : Prop :=
  G.nu x = d ∧ ((∃ y : G.Fiber d, Mixed y.1) → Mixed x)

/-- A degree representative, chosen to be mixed if possible. -/
private def best (d : ℕ) : Vec := Classical.epsilon (G.Preferred d)

private lemma best_spec {d : ℕ} (x : G.Fiber d) : G.Preferred d (G.best d) := by
  apply Classical.epsilon_spec
  rcases em (∃ y : G.Fiber d, Mixed y.1) with ⟨y, hy⟩ | h
  · exact ⟨y.1, y.2, fun _ => hy⟩
  · exact ⟨x.1, x.2, by tauto⟩

private def Alt (i : Fin 4) : Set ℕ :=
  {c | ∃ z : G.Fiber (c * G.n i), z.1.support.Nonempty ∧ i ∉ z.1.support}

/-- The least positive exponent with a factorization avoiding `i`. -/
private abbrev crit (i : Fin 4) : ℕ := sInf (G.Alt i)

private def gens : Set M :=
  Set.range (fun i : Fin 4 =>
    let z := single i (G.crit i)
    mon z - mon (G.best (G.nu z))) ∪
  ⋃ k : Fin 3, Set.range (fun d : G.Fam k => mon (pick d false) - mon (pick d true))

local notation "J" => Ideal.span (gens K G)
local notation "π" => Ideal.Quotient.mkₐ K J
local notation "qmon " z:arg => π (mon z)

private lemma quot_eq {x y : Vec} (h : mon x - mon y ∈ gens K G) :
    qmon x = qmon y := Ideal.Quotient.eq.2 (Ideal.subset_span h)

private lemma mixed_eq {d : ℕ}
    (apart : ∀ {z w : G.Fiber d}, qmon z.1 ≠ qmon w.1 →
      Disjoint z.1.support w.1.support)
    (z w : G.Fiber d) (hz : Mixed z.1) (hw : Mixed w.1) :
    qmon z.1 = qmon w.1 := by
  by_contra h
  obtain ⟨k, b, hz', hw'⟩ := pair_sides _ _ hz hw (apart h)
  -- If the quotient monomials differ, every support lies on one of their sides.
  let D : G.Fam k := ⟨d, ?_, fun u => ?_⟩
  · have link (u : G.Fiber d) (c : Bool) (hs : u.1.support = face k c) :
        qmon u.1 = qmon (pick D c) := by
      by_contra he
      simpa [hs, pick_spec, (face_nonempty k c).ne_empty] using
        apart (w := ⟨pick D c, (pick_spec D c).1⟩) he
    have e : qmon (pick D false) = qmon (pick D true) :=
      quot_eq K G (Or.inr (Set.mem_iUnion.2 ⟨k, D, rfl⟩))
    have := link z b hz'
    have := link w (!b) hw'
    cases b <;> grind
  · intro c
    cases b <;> cases c <;> solve_by_elim [Exists.intro]
  · by_cases e : qmon u.1 = qmon z.1
    · refine ⟨b, ?_⟩
      simpa [hw', ← face_compl, ← subset_compl_iff_disjoint_right] using apart (e.trans_ne h)
    · refine ⟨!b, ?_⟩
      simpa [hz', ← subset_compl_iff_disjoint_right, face_compl] using apart e

private lemma quot_best {d : ℕ} (x : G.Fiber d) :
    qmon x.1 = qmon (G.best d) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    obtain rfl | hd := Nat.eq_zero_or_pos d
    · rw [(G.nu_eq_zero _).1 x.2, (G.nu_eq_zero _).1 (G.best_spec x).1]
    -- Cancel the common monomial to compare factorizations at a smaller degree.
    have apart {z w : G.Fiber d} (e : qmon z.1 ≠ qmon w.1) :
        Disjoint z.1.support w.1.support := by
      by_contra h
      let u := z.1 ⊓ w.1
      have hu : 0 < G.nu u := by simpa [nu_pos, u] using not_disjoint_iff_nonempty_inter.1 h
      have factor (v : G.Fiber d) (hle : u ≤ v.1) :
          qmon v.1 = qmon (G.best (d - G.nu u)) * qmon u := by
        rw [← ih _ (Nat.sub_lt hd hu) ⟨v.1 - u, by rw [← map_tsub_of_le G.nu _ _ hle, v.2]⟩,
          ← map_mul, monomial_mul_monomial, one_mul, tsub_add_cancel_of_le hle]
      exact e ((factor z inf_le_left).trans (factor w inf_le_right).symm)
    let v : G.Fiber d := ⟨G.best d, (G.best_spec x).1⟩
    change qmon x.1 = qmon v.1
    have mix (z : G.Fiber d) (hz : Mixed z.1) : qmon z.1 = qmon v.1 :=
      mixed_eq K G (@apart) z v hz ((G.best_spec z).2 ⟨z, hz⟩)
    by_contra h
    obtain ⟨i, c, xe⟩ := card_support_le_one'.1 (Nat.le_of_not_gt fun hm => h (mix x hm))
    obtain rfl : d = c * G.n i := by simpa [xe] using x.2.symm
    have hc := Nat.pos_of_mul_pos_right hd
    have hs : i ∈ x.1.support := by simp [xe, hc.ne']
    have ak : c ∈ G.Alt i := ⟨v, (G.nu_pos _).1 (v.2.symm ▸ hd), disjoint_left.1 (apart h) hs⟩
    have hc' := Nat.sInf_le ak
    obtain E | E := eq_or_lt_of_le hc'
    · exact h (by simpa [xe, v, E] using quot_eq K G (Or.inl ⟨i, rfl⟩))
    -- Above the critical exponent, the first replacement leaves a mixed factorization.
    obtain ⟨a, hna, ha⟩ : G.crit i ∈ G.Alt i := Nat.sInf_mem ⟨_, ak⟩
    let w : G.Fiber (c * G.n i) := ⟨single i (c - G.crit i) + a.1, by
      rw [map_add, weight_single, smul_eq_mul, a.2, ← add_mul, Nat.sub_add_cancel hc']⟩
    have H : Mixed w.1 ∧ i ∈ w.1.support := by
      simp [w, support_add_eq_union, -single_tsub, (Nat.sub_pos_of_lt E).ne',
        card_insert_of_notMem ha, hna]
    exact disjoint_left.1 (apart (fun e => h (e.trans (mix w H.1)))) hs H.2

private lemma ker_eq_span : toricIdeal K G.n = J := by
  -- The quotient map factors linearly through toric evaluation.
  let L := (Polynomial.basisMonomials K).constr K fun d => qmon (G.best d)
  have factor : L ∘ₗ (φ).toLinearMap = (π).toLinearMap := by
    refine (MvPolynomial.basisMonomials (Fin 4) K).ext fun s => ?_
    simpa [L, -Polynomial.coe_basisMonomials] using (quot_best K G ⟨s, rfl⟩).symm
  apply le_antisymm
  · intro f hf
    apply Ideal.Quotient.eq_zero_iff_mem.1
    simpa [show φ f = 0 from hf] using (LinearMap.congr_fun factor f).symm
  · have deg (z : Vec) := (G.best_spec ⟨z, rfl⟩).1
    simp [Ideal.span_le, gens, Set.iUnion_subset_iff, Set.range_subset_iff,
      toricIdeal, RingHom.mem_ker, -weight_single, deg]

lemma spanRank_le_two :
    (toricIdeal K G.n).spanRank ≤ (2 * G.W : ℕ) := by
  rw [← Cardinal.toENat_le_natCast, ker_eq_span K G]
  refine (Cardinal.toENat.monotone' (Submodule.spanRank_span_le_card _)).trans ?_
  change (gens K G).encard ≤ _
  simp_rw [gens, ← Set.image_univ]
  grw [Set.encard_union_le, Set.encard_iUnion_le_of_fintype,
    Set.encard_image_le, Set.encard_image_le]
  simpa using G.sum_bound

end GenData
end
end SemigroupBetti
