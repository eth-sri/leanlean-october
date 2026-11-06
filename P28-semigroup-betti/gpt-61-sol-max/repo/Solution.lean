/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Sub.Unbundled.Hom
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Module.SpanRank
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Pairwise
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.WLOG
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Zify
import Mathlib.Data.Finsupp.Weight

/-!
# Linear bounds for the first Betti number of four-generated numerical semigroups

The combinatorial argument bounds the sum of component contributions over **any finite
set of degrees**. Component supports are disjoint; singleton components contribute at
most four times, and the three pair splits are bounded by antichain and replacement
arguments. Finally, Noetherian compactness selects finitely many degrees whose chosen
binomials generate the toric ideal. Thus no explicit degree cutoff is needed.
-/

noncomputable section
namespace SemigroupBetti
open Finset

/-! ## The toric ideal and normalized width -/

variable (K : Type*) [Field K] (n : Fin 4 → ℕ)

def toricIdeal :
    Ideal (MvPolynomial (Fin 4) K) :=
  RingHom.ker (MvPolynomial.aeval (fun i => (Polynomial.X : Polynomial K) ^ n i)).toRingHom

def MinimallyGenerates : Prop :=
  ∀ i : Fin 4, n i ∉ AddSubmonoid.closure (n '' {j | j ≠ i})

def normalizedWidth : ℕ :=
  (n 3 - n 0) / Nat.gcd (n 1 - n 0) (Nat.gcd (n 2 - n 0) (n 3 - n 0))

abbrev Vec := Fin 4 →₀ ℕ
abbrev Support := Finset (Fin 4)

/-! ## Counting disjoint support families -/
set_option maxRecDepth 200000 in
lemma support_family_count : ∀ F : Finset Support,
    ∅ ∉ F → @Set.Pairwise Support F Disjoint →
    F.card - 1 ≤ (∑ i : Fin 4, if {i} ∈ F then 1 else 0) +
      ∑ i ∈ {0, 3, 2}, if {1, i} ∈ F ∧ {1, i}ᶜ ∈ F then 1 else 0 := by
  decide +kernel

open Classical MvPolynomial

local grind_pattern Finsupp.mem_support_iff => f a
attribute [local grind ←=] Quot.sound


/-! ## Normalized generator data

`degrees` is an arbitrary finite set used only for the counting argument.
-/
structure GenData where
  n : Fin 4 → ℕ
  pos : ∀ i, n i ≠ 0
  inc : StrictMono n
  degrees : Finset ℕ

namespace GenData
variable (G : GenData) {S : Support} ⦃d d' : ℕ⦄ {k : Fin 4}

def g := Nat.gcd (G.n 1 - G.n 0) (Nat.gcd (G.n 2 - G.n 0) (G.n 3 - G.n 0))
def A := (G.n 1 - G.n 0) / G.g
def B := (G.n 2 - G.n 0) / G.g
abbrev W := normalizedWidth G.n

abbrev nu : Vec →+ ℕ := Finsupp.weight G.n

lemma n_values : G.n 1 = G.n 0 + G.g * G.A ∧
    G.n 2 = G.n 0 + G.g * G.B ∧ G.n 3 = G.n 0 + G.g * G.W := by
  unfold A B W normalizedWidth g
  grind [! (G.inc (a := 0)),
    Nat.gcd_dvd_left, Nat.gcd_dvd_right,
    Nat.mul_div_cancel', Nat.dvd_trans]

attribute [local simp] Fin.exists_fin_succ n_values MvPolynomial.single_eq_monomial
  Finsupp.weight_single aeval_monomial Finsupp.prod_fintype Finset.prod_pow_eq_pow_sum

lemma bounds : 0 < G.A ∧ G.A < G.B ∧ G.B < G.W := by
  have := G.inc
  simp_all [StrictMono, Fin.forall_fin_succ]
  constructor <;> nlinarith

/-! ## Fibers and their factorization graphs -/

abbrev fiber d := {z : Vec // G.nu z = d}

instance : Finite (G.fiber d) :=
  Finsupp.finite_of_nat_weight_eq G.n G.pos d

abbrev Comp d := Quot (fun z z' : G.fiber d => ∃ i, 0 < z.1 i ∧ 0 < z'.1 i)
abbrev cc : G.fiber d → G.Comp d := Quot.mk _
attribute [local instance 100] Fintype.ofFinite

abbrev ncomp d := Fintype.card (G.Comp d)

def compSupp C := univ.filter (∃ z : G.fiber d, G.cc z = C ∧ 0 < z.1 ·)

lemma supp_subset_compSupp (z : G.fiber d) :
    z.1.support ⊆ G.compSupp (G.cc z) := by
  grind [compSupp]

local grind_pattern supp_subset_compSupp => z.1

lemma compSupp_disjoint {C C' : G.Comp d} :
    C ≠ C' → Disjoint (G.compSupp C) (G.compSupp C') := by
  grind [compSupp, disjoint_left]

lemma supp_closed {C : G.Comp d} {b} (hb : G.nu b = d) {i} :
    i ∈ G.compSupp C → 0 < b i → b.support ⊆ G.compSupp C := by
  grind [compSupp, G.supp_subset_compSupp ⟨b, hb⟩]

attribute [local grind →] supp_closed

lemma compSupp_nonempty (h : 2 ≤ G.ncomp d) (C : G.Comp d) :
    (G.compSupp C).Nonempty := by
  let := Finsupp.nonTorsionWeight_of ℕ G.n G.pos
  obtain ⟨D, hD⟩ := Fintype.exists_ne_of_one_lt_card h C
  grind [Finsupp.weight_eq_zero_iff_eq_zero,
    C.out_eq, D.out_eq]

lemma nu_replace {u v x} : u ≤ x → G.nu u = G.nu v →
    G.nu (x - u + v) = G.nu x := by
  intro hux
  grind [tsub_add_cancel_of_le hux]

/-! ## Singleton component contributions -/

abbrev compFamily d := univ.image (@G.compSupp d)

def IsSplit d S :=
  S.card = 2 ∧ S ∈ G.compFamily d ∧ Sᶜ ∈ G.compFamily d
attribute [local grind =] Finsupp.add_apply Finsupp.tsub_apply Finsupp.le_def
  IsSplit Set.InjOn Set.MapsTo Set.Pairwise

def sigma := ∑ d ∈ G.degrees,
  (univ.filter (fun i => 2 ≤ G.ncomp d ∧ {i} ∈ G.compFamily d)).card
lemma sigma_le_four : G.sigma ≤ 4 := by
  rw [sigma, ← card_biUnion]
  · exact card_le_univ _
  rintro d - e - hde
  simp [disjoint_left]
  intro i hd C hC he D hD
  contrapose hde
  induction C, D using Quot.induction_on₂ with | h u v =>
  wlog hle : u.1 ≤ v.1 generalizing d e
  · exact (this he hd v u hD hC <| by grind).symm
  suffices u.1 = v.1 by grind
  obtain ⟨C', hC'⟩ := Fintype.exists_ne_of_one_lt_card hd (G.cc u)
  obtain ⟨w, hw, hwj⟩ := (mem_filter.1 (G.compSupp_nonempty hd C').choose_spec).2
  grind [G.compSupp_disjoint hC',
    G.nu_replace hle (u.2.trans w.2.symm), hle i, disjoint_left]

/-! ## Pair splits and selected factorizations -/

abbrev V2 : Vec := Finsupp.single 1 (G.W - G.B) + Finsupp.single 3 (G.B - G.A)

lemma identities :
    G.nu (Finsupp.single 1 G.B) =
      G.nu (Finsupp.single 0 (G.B - G.A) + Finsupp.single 2 G.A) ∧
    G.nu (Finsupp.single 2 (G.W - G.A)) = G.nu G.V2 := by
  have := G.bounds
  simp [-Finsupp.single_tsub]
  zify at *
  grind

lemma IsSplit.compl : G.IsSplit d S → G.IsSplit d Sᶜ := by
  simp_all [IsSplit, card_compl]
abbrev fam S :=
  G.degrees.filter (G.IsSplit · S)
lemma fam_split : d ∈ G.fam S → G.IsSplit d S := And.right ∘ mem_filter.mp

abbrev famP := G.fam {1, 0}
abbrev famQ := G.fam {1, 3}
abbrev famE := G.fam {1, 2}

abbrev Selected d S z := G.nu z = d ∧ z.support = S
def sel d := Classical.epsilon ∘ G.Selected d

namespace IsSplit
variable {G} (hS : G.IsSplit d S)

/-- The selected factorization supplied by a split. -/
abbrev sel (_hS : G.IsSplit d S) := G.sel d S

@[grind →] lemma spec : G.Selected d S hS.sel := by
  apply Classical.epsilon_spec
  obtain ⟨C, -, hC⟩ := mem_image.1 hS.2.1
  obtain ⟨i, j, hij, rfl⟩ := card_eq_two.1 hS.1
  have := hC.symm ▸ mem_insert_self i {j}
  by_contra!
  have hv z := @congrArg _ _ (G.cc z) C <|
    Quot.lift (fun z => i ∈ z.1.support) <| by
      clear z
      grind
  grind (gen := 16) [compSupp]

lemma minimal {U V} : U ≤ hS.sel → G.nu U = G.nu V →
    (∃ j ∉ S, 0 < V j) → U = hS.sel := by
  grind [ → nu_replace]

@[grind! .] theorem eq_of_le (hS' : G.IsSplit d' S) :
    hS.sel ≤ hS'.sel → d = d' := by
  grind [hS.compl, → minimal, mem_compl, card_pos, Fin.exists_fin_succ]

lemma lt_single {c} {V} : G.nu (Finsupp.single k c) = G.nu V →
    (∃ j ∉ S, 0 < V j) → hS.sel k < c := by
  grind [=_ Finsupp.single_le_iff, → minimal, Finsupp.card_support_le_one']

end IsSplit

/-! ## Antichain counting -/

section
variable (F : Finset ℕ) (hF : ∀ d ∈ F, G.IsSplit d S)
include hF

lemma card_le_of_coord (hk : k ∈ S) {c}
    (hc : ∀ d ∈ F, G.sel d S k < c) : F.card ≤ c - 1 := by
  simpa using card_le_card_of_injOn (G.sel · S k) (s := F) (t := Ico 1 c)
    (by grind) <| by grind [card_eq_two]
lemma pair_family_le : 1 ∈ S → 2 ∉ S → F.card ≤ min G.B (G.W - G.A) - 1 := by
  intro h1 h2
  have := G.card_le_of_coord F hF h1 fun d hd =>
    (hF d hd).lt_single G.identities.1 <| by simp [h2, G.bounds.1]
  have := G.card_le_of_coord F (fun d hd => (hF d hd).compl) (mem_compl.2 h2) fun d hd =>
    (hF d hd).compl.lt_single G.identities.2 <| by simp [h1, G.bounds.2.2]
  omega

end

attribute [local grind =] Fin.exists_fin_succ

theorem E_le p q : 0 < p → p * G.A + q * G.B = q * G.W → G.famE.card ≤ p + q - 1 := by
  intros
  let u d := G.sel d {1, 2}
  let f d := if u d 1 < p then u d 1 else p - 1 + u d 2
  simpa using card_le_card_of_injOn f (s := G.famE) (t := Ico 1 (p + q))
    (by
      intro d hd
      have := (G.fam_split hd).minimal (U := Finsupp.single 1 p + Finsupp.single 2 q)
        (V := Finsupp.single 0 p + Finsupp.single 3 q)
      grind [Finsupp.weight_single, n_values])
    <| by grind

/-! ## The exceptional normalized parameters -/

theorem P_le_of_Q_eq : G.A = 1 → G.B = G.W - 1 →
    G.famQ.card = G.W - 2 → G.famP.card ≤ G.W - 2 - 1 := by
  intro hA hB hQeq
  have := G.bounds.2.1
  obtain ⟨D, hD, hu⟩ := surjOn_of_injOn_of_card_le (s := G.famQ) (t := Ico 1 G.B)
    (G.sel · {1, 3} 1)
    (by
      intro d hd
      grind [(G.fam_split hd).lt_single G.identities.1])
    (by grind)
    (by simp; omega) (mem_Ico.2 ⟨le_rfl, by omega⟩)
  have hS := G.fam_split hD
  have hle : hS.sel ≤ G.V2 := by
    have := (hS.minimal · G.identities.2.symm)
    grind

  let b : G.fiber _ :=
    ⟨_, G.nu_replace hle (hS.spec.1.trans hS.compl.spec.1.symm)⟩
  have hrel := map_tsub_of_le G.nu b.1 (Finsupp.single 2 (b.1 2))
    (Finsupp.single_le_iff.2 le_rfl)
  simp [-n_values, -Finsupp.single_tsub, b.2, ← G.identities.2, hA, ← Nat.sub_mul] at hrel
  rw [← smul_eq_mul, ← Finsupp.weight_single] at hrel

  exact G.card_le_of_coord (k := 2) G.famP (fun d hd => (G.fam_split hd).compl)
    (by decide) fun d hd => by
    have := (G.fam_split hd).compl.lt_single hrel
    grind [hS.compl, mem_compl]

/-! ## Generators of the toric ideal -/

abbrev genSet d :=
  if h : Nonempty (G.Comp d) then
    (univ.erase h.some).image
      (monomial ·.out.1 (1 : K) - monomial h.some.out.1 1)
  else ∅

abbrev binomGens :=
  G.degrees.biUnion (G.genSet K)

abbrev relationIdeal := ⨆ d, Ideal.span (SetLike.coe (G.genSet K d))

theorem card_binomGens_le_two_W : #(G.binomGens K) ≤ 2 * G.W := by
  trans G.sigma + G.famP.card + G.famQ.card + G.famE.card
  · apply card_biUnion_le.trans
    unfold sigma
    conv_rhs => simp only [card_eq_sum_ones, sum_filter, ← sum_add_distrib]
    gcongr with d
    by_cases hc : 2 ≤ G.ncomp d
    case' pos =>
      have hn := G.compSupp_nonempty hc
      have := by
        apply support_family_count (G.compFamily d) <;>
          grind [compSupp_disjoint]
      simp_all [-sum_boole, IsSplit,
        card_image_of_injective univ
          <| Function.injective_iff_pairwise_ne.2 fun _ _ h =>
            (G.compSupp_disjoint h).ne (hn _).ne_empty, sum_insert, add_assoc]
    all_goals grind [card_image_le]
  have := G.pair_family_le G.famP G.fam_split
  have := G.pair_family_le G.famQ G.fam_split
  have := G.E_le (G.W - G.B) G.A
  grind [G.sigma_le_four, G.bounds,
    Nat.sub_add_cancel G.bounds.2.2.le, → G.E_le 1 1, → G.P_le_of_Q_eq]

abbrev monomialQ s := Ideal.Quotient.mk (G.relationIdeal K) (monomial s 1)
lemma mono_eq_quot : ∀ z z' : G.fiber d,
    G.monomialQ K z.1 = G.monomialQ K z'.1 := by
  refine Nat.strong_induction_on d ?_
  intro d IH x y
  have h := Nonempty.intro (G.cc x)
  have (v : G.fiber d) : G.monomialQ K v.1 = G.monomialQ K h.some.out.1 := by
    apply (congrArg
      (Quot.lift (G.monomialQ K ·.1) <| by
        intro u v ⟨i, hi, hi'⟩
        rw [← Finsupp.sub_add_single_one_cancel hi.ne',
          ← Finsupp.sub_add_single_one_cancel hi'.ne']
        simp_rw [monomialQ, monomial_add_single, map_mul]
        congr 1
        refine IH _ ?_ ⟨_, rfl⟩ ⟨_, ?_⟩
        all_goals grind [! Finsupp.weight_sub_single_add, G.pos i]
      )
      (G.cc v).out_eq.symm).trans
    apply Ideal.Quotient.eq.2
    by_cases hC : G.cc v = h.some
    · simp [hC]
    apply Submodule.mem_iSup_of_mem d
    apply Ideal.subset_span
    grind
  grind

theorem toricKer_eq_span : toricIdeal K G.n = G.relationIdeal K := by
  apply le_antisymm
  · have hq : (Ideal.Quotient.mkₐ K (G.relationIdeal K)).toLinearMap =
      (Polynomial.lsum fun d =>
        LinearMap.toSpanSingleton K _ (G.monomialQ K (Function.invFun G.nu d))).comp
          (aeval (Polynomial.X ^ G.n ·)).toLinearMap := by
      ext s
      simp [← pow_mul']
      simpa [Finsupp.weight_eq_sum, Polynomial.X_pow_eq_monomial] using
        G.mono_eq_quot K ⟨s, rfl⟩ ⟨_, Function.apply_invFun_apply⟩
    intro f hf
    simp [toricIdeal] at hf
    simpa [hf, Ideal.Quotient.eq_zero_iff_mem] using LinearMap.congr_fun hq f
  · refine iSup_le fun d => Ideal.span_le.2 ?_
    unfold genSet
    split_ifs <;> simp [Set.subset_def, toricIdeal, ← pow_mul']
    grind [Finsupp.weight_eq_sum]

end GenData

/-! ## Main results -/

variable (hpos : 0 < n 0) (hmono : StrictMono n) (hgcd : Finset.univ.gcd n = 1)
    (hmin : MinimallyGenerates n)
include hpos hmono hgcd hmin

theorem beta1_le_two_mul_normalizedWidth :
    (toricIdeal K n).spanRank ≤ (2 * normalizedWidth n : ℕ) := by
  let G := GenData.mk n (by grind [! (hmono (a := 0))]) hmono ∅
  obtain ⟨D, hD⟩ := (IsCompactElement.of_wellFoundedGT _).exists_finset_of_le_iSup
    (Ideal.span ∘ SetLike.coe ∘ G.genSet K) le_rfl
  let G' := GenData.mk G.n G.pos G.inc D
  have hspan : G.relationIdeal K = Ideal.span (G'.binomGens K) := by
    simp [Ideal.span_iUnion]
    exact hD.antisymm <| iSup₂_le_iSup _ _
  grw [G.toricKer_eq_span K, hspan, Submodule.spanRank_span_le_card, coe_sort_coe,
    Cardinal.mk_coe_finset,
    G'.card_binomGens_le_two_W K]

theorem beta1_le_two_mul_width :
    (toricIdeal K n).spanRank ≤ (2 * (n 3 - n 0) : ℕ) := by
  grw [beta1_le_two_mul_normalizedWidth, normalizedWidth, Nat.div_le_self] <;> assumption

end SemigroupBetti
end
