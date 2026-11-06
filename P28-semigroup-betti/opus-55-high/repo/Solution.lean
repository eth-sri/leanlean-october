module

public import Mathlib

@[expose] public section


open Finset Classical SimpleGraph MvPolynomial
noncomputable section
namespace SemigroupBetti

variable (K : Type*) [Field K] (n : Fin 4 → ℕ)

def toricIdeal :=
  RingHom.ker (aeval (R := K) fun i => (Polynomial.X : Polynomial K) ^ n i).toRingHom

def MinimallyGenerates :=
  ∀ i, n i ∉ AddSubmonoid.closure (n '' {j | j ≠ i})

def normalizedWidth :=
  (n 3 - n 0) / Nat.gcd (n 1 - n 0) (Nat.gcd (n 2 - n 0) (n 3 - n 0))

structure GD where
  (m g A s t : ℕ)
  h : 0 < m ∧ 0 < A ∧ 0 < s ∧ 0 < t

namespace GD
variable (G : GD) {d}

def N i := G.m + G.g * ![0, G.A, G.A + G.s, G.A + G.s + G.t] i

abbrev ν z := z ⬝ᵥ G.N

lemma n_pos i : 0 < G.N i := Nat.add_pos_left G.h.1 _

lemma ν_sub {z U} (h : U ≤ z) : G.ν (z - U) + G.ν U = G.ν z := by
  rw [← add_dotProduct, tsub_add_cancel_of_le h]

def V d := {z // G.ν z = d}

instance : Fintype (G.V d) :=
  ((Set.finite_Iic fun _ => d).subset fun z (h : _ = d) i => h ▸ (Nat.le_mul_of_pos_right _ (G.n_pos i)).trans
    (single_le_sum_of_canonicallyOrdered (f := z * G.N) (mem_univ i))).fintype

abbrev Γ d := SimpleGraph.fromRel fun x y : G.V d => ∃ i, 0 < x.1 i ∧ 0 < y.1 i

abbrev CC d := (G.Γ d).ConnectedComponent

abbrev cc := (G.Γ d).connectedComponentMk

abbrev ncomp d := Fintype.card (G.CC d)

def cs (C : G.CC d) : Finset (Fin 4) := {i | ∃ x, G.cc x = C ∧ 0 < x.1 i}

lemma memc (v : G.V d) {l} (hl : 0 < v.1 l) : l ∈ G.cs (G.cc v) := by grind [cs]

lemma eqC {C C' : G.CC d} {i} (h : i ∈ G.cs C) (h' : i ∈ G.cs C') : C = C' := by
  grind [cs, ConnectedComponent.sound, Adj.reachable, fromRel_adj]

lemma nzC {C C' : G.CC d} (h : C ≠ C') : (G.cs C').Nonempty := by
  induction C, C' using ConnectedComponent.ind₂
  rename_i x y
  by_cases ∃ i, 0 < y.1 i
  · grind [→ G.memc]
  refine absurd (congrArg _ (Subtype.ext (funext fun i => ?_))) h
  have := x.2.trans y.2.symm
  simp_all [dotProduct, (G.n_pos _).ne']

abbrev SP d (K : Finset _) z := G.ν z = d ∧ ∀ i, 0 < z i ↔ i ∈ K

def sel d K := Classical.epsilon (G.SP d K)

abbrev Side d K :=
  G.SP d K (G.sel d K) ∧ (∀ b : G.V d, ∀ i ∈ K, 0 < b.1 i → ∀ j, 0 < b.1 j → j ∈ K) ∧
    ∃ y : G.V d, ∃ j ∉ K, 0 < y.1 j

lemma eqU {K U V} (H : G.Side d K) (hU : U ≤ G.sel d K) (hUV : G.ν U = G.ν V) j
    (hV : 0 < V j) (hj : j ∉ K := by decide) : U = G.sel d K := by
  by_contra hne
  obtain ⟨-, k, hk⟩ := Pi.lt_def.1 (hU.lt_of_ne hne)
  grind [H.2.1 ⟨G.sel d K - U + V, by grind [add_dotProduct, G.ν_sub hU]⟩, Pi.add_apply, Pi.sub_apply]

lemma anti2 {d' K i} (h : G.Side d K) (h' : G.Side d' K)
    (e : ∀ j ∈ K, j ≠ i → G.sel d K j = G.sel d' K j) : d = d' := by
  wlog hi : G.sel d K i ≤ G.sel d' K i
  · grind
  have := h.2.2.choose_spec.choose_spec
  rw [← h.1.1, ← h'.1.1, G.eqU h' (fun l => by
    grind) (h.1.1.trans h.2.2.choose.2.symm) _ this.2 this.1]

lemma sle {k c} {z : Fin 4 → ℕ} (h : c ≤ z k) : Pi.single k c ≤ z := fun l => by grind

lemma card_le {K k c F} (hc : ∀ d ∈ F, G.sel d K k < c) (hF : ∀ d ∈ F, G.Side d K)
    (h : k ∈ K ∧ ∃ i, ∀ j ∈ K, j ≠ i → j = k := by decide) : #F ≤ c - 1 := by
  simpa using card_le_card_of_injOn (t := Ioo 0 c) (G.sel · K k) (by grind [Set.MapsTo]) fun d hd d' hd' e =>
    G.anti2 (hF d hd) (hF d' hd') (h.2.choose_spec · · · ▸ e)

lemma cb {K k c V F} i j (hF : ∀ d ∈ F, G.Side d K) (hV : G.ν (Pi.single k c) = G.ν V)
    (hVj : 0 < V j := by simp [G.h])
    (h : i ∈ K ∧ j ∉ K ∧ i ≠ k ∧ k ∈ K ∧ ∃ i, ∀ l ∈ K, l ≠ i → l = k := by decide) : #F ≤ c - 1 :=
  G.card_le (fun d hd => by
    by_contra! hc
    grind [congrFun (G.eqU (hF d hd) (sle hc) hV j hVj h.2.1) i]) hF h.2.2.2

lemma sideC {C C' : G.CC d} (h : C ≠ C') (hc : #(G.cs C) ≤ 2) :
    G.Side d (G.cs C) := by
  obtain ⟨i, j, hij⟩ : ∃ i j, G.cs C = {i, j} := by
    have := G.nzC h.symm; generalize G.cs C = s at *; revert s; decide
  refine ⟨?_, by grind [G.eqC, → G.memc], ?_⟩
  · have e := Finset.ext_iff.1 hij
    simp [cs] at e
    obtain ⟨x, hx⟩ := (e i).2 (.inl rfl)
    obtain ⟨y, hy⟩ := (e j).2 (.inr rfl)
    obtain ⟨z, hz⟩ : ∃ z, G.cc z = C ∧ 0 < z.1 i ∧ 0 < z.1 j := by
      by_contra! H
      obtain ⟨⟨⟨a, b⟩, hab⟩, -, ha, hb⟩ := (ConnectedComponent.exact (hx.1.trans hy.1.symm)).some.exists_boundary_dart
        {v | G.cc v = C ∧ 0 < v.1 i} hx (by grind)
      rcases hab.2 with ⟨l, h1, h2⟩ | ⟨l, h2, h1⟩ <;> grind [G.memc b h2, ConnectedComponent.sound, Adj.reachable]
    exact Classical.epsilon_spec ⟨z.1, z.2, by grind [G.memc]⟩
  · grind [cs, G.eqC, G.nzC h]

def pr (j : Fin 3) : Finset (Fin 4) := {0, j.succ}

abbrev S d j := G.Side d (pr j) ∧ G.Side d (pr j)ᶜ

abbrev Pf (D : Finset ℕ) j := {d ∈ D | G.S d j}

lemma P1 D j d : d ∈ G.Pf D j → G.Side d (pr j) := by grind

lemma P2 D j d : d ∈ G.Pf D j → G.Side d (pr j)ᶜ := by grind

lemma perdeg d : G.ncomp d - 1 ≤ #{i | G.Side d {i}} + #{j | G.S d j} := by
  by_cases hA : ∃ C1 C2 : G.CC d, C1 ≠ C2 ∧ 1 < #(G.cs C1) ∧ 1 < #(G.cs C2)
  · obtain ⟨C1, C2, hne, h1, h2⟩ := hA
    have := disjoint_left.2 fun i h h' => hne (G.eqC h h')
    obtain ⟨hL, h4, h5, j, hj⟩ : G.cs C2 = (G.cs C1)ᶜ ∧ #(G.cs C1) ≤ 2 ∧ #(G.cs C2) ≤ 2 ∧
        ∃ j, pr j = G.cs C1 ∨ pr j = (G.cs C1)ᶜ := by
      generalize G.cs C1 = K, G.cs C2 = L at *; revert K L; decide
    refine (Nat.sub_le_of_le_add ((card_le_card (t := {C1, C2}) fun C _ => by
      rcases eq_or_ne C C1 with rfl | h
      · simp
      obtain ⟨w, hw⟩ := G.nzC h.symm
      by_cases w ∈ G.cs C2 <;> grind [G.eqC, mem_compl]).trans card_le_two)).trans ?_
    exact le_add_left (card_pos.2 ⟨j, by
      grind [G.sideC hne h4, hL ▸ G.sideC hne.symm h5, compl_compl]⟩)
  by_cases h : G.ncomp d ≤ 1
  · omega
  have : #{C | ¬ #(G.cs C) ≤ 1} ≤ 1 := card_le_one.2 fun a ha b hb =>
    by_contra (hA ⟨a, b, ·, by simp_all⟩)
  have : #{C | #(G.cs C) ≤ 1} ≤ #{i | G.Side d {i}} :=
    card_le_card_of_forall_subsingleton (Membership.mem ∘ G.cs) (fun C hC => by
      have hC' := (Fintype.exists_ne_of_one_lt_card (not_le.1 h) C).choose_spec
      obtain ⟨i, hi⟩ := card_eq_one.1 (le_antisymm (by simp_all) (card_pos.2 (G.nzC hC')))
      exact ⟨i, by grind [G.sideC hC'.symm (hi ▸ by simp)], by simp_all⟩)
      fun i _ C hC C' hC' => G.eqC hC.2 hC'.2
  grind [card_filter_add_card_filter_not]

macro "nu" : tactic => `(tactic| (simp [ν, dotProduct, Fin.sum_univ_four, N, *]; ring))

lemma Ebound {p q} D (hp : 0 < p) (hν : G.ν ![0, p, q, 0] = G.ν ![p, 0, 0, q] := by nu) :
    #(G.Pf D 2) ≤ p + (q - 1) := by
  rw [← card_filter_add_card_filter_not (G.sel · (pr 2)ᶜ 1 < p + 1)]
  refine add_le_add (G.card_le (fun _ => And.right ∘ mem_filter.1) ?_)
    (G.card_le (fun d hd => by
      have := mem_filter.1 hd
      by_contra! h
      have := congrFun (G.eqU (G.P2 D 2 d this.1) (fun i => by fin_cases i <;> simp <;> omega) hν 0
        hp) 1
      simp_all) ?_) <;> grind

lemma exc D : G.A ≠ 1 ∨ G.t ≠ 1 ∨ #(G.Pf D 0) < G.s ∨ #(G.Pf D 1) < G.s := by
  by_contra!
  have := G.h
  obtain ⟨⟨E, hE, hE3⟩, F, hF, hF2⟩ :
      (∃ E ∈ G.Pf D 1, G.s ≤ G.sel E (pr 1)ᶜ 3) ∧ ∃ F ∈ G.Pf D 0, G.s ≤ G.sel F (pr 0)ᶜ 2 := by
    constructor <;> by_contra! H' <;> grind [G.card_le H' (G.P2 _ _)]
  obtain ⟨-, h02, h31⟩ := mem_filter.1 hE
  have h32 := G.P2 D 0 F hF
  have := (h31.1.2 1).2 (by decide)
  have := G.eqU h31 (U := ![0, 1, 0, G.s]) (by simp [Pi.le_def, Fin.forall_fin_succ]; omega)
    (V := Pi.single 2 (G.s + 1)) (by nu) 2 (by simp) ▸ h31.1.1
  have := G.ν_sub (sle ((h02.1.2 2).2 (by decide)))
  have := h02.1.1
  refine ((h32.1.2 3).2 (by decide)).ne' ?_
  rw [← G.eqU h32 (sle hF2) (V := G.sel E (pr 1) - Pi.single 2 1) ?_ 0
    (by grind [Pi.sub_apply, pr])]
  · simp
  have : G.N 1 + G.s * G.N 3 = G.s * G.N 2 + G.N 2 := by nu
  simp [ν, dotProduct, Fin.sum_univ_four] at *
  omega

lemma main D : ∑ d ∈ D, (G.ncomp d - 1) ≤ 2 * (G.A + G.s + G.t) := by
  have : ∑ i, #{d ∈ D | G.Side d {i}} ≤ 4 := sum_le_card_nsmul univ _ 1 fun i _ => card_le_one.2 fun d hd d' hd' =>
    G.anti2 (i := i) (mem_filter.1 hd).2 (mem_filter.1 hd').2 (by simp)
  have e1 : G.ν (Pi.single 1 (G.A + G.s)) = G.ν ![G.s, 0, G.A, 0] := by nu
  have e2 : G.ν (Pi.single 2 (G.s + G.t)) = G.ν ![0, G.t, 0, G.s] := by nu
  have := sum_le_sum (s := D) fun d _ => G.perdeg d
  simp only [card_filter, sum_add_distrib, sum_comm (s := D)] at this
  simp [Fin.sum_univ_three] at this
  have := fun h : G.A = G.t => G.Ebound D one_pos (q := 1)
  grind [G.h, G.exc D, G.Ebound D G.h.2.2.2 (q := G.A), G.cb 0 2 (G.P1 D 0) e1, G.cb 3 1 (G.P2 D 0) e2, G.cb 0 1 (G.P1 D 1) e2, G.cb 3 2 (G.P2 D 1) e1]

lemma D0fin : {d | 1 < G.ncomp d}.Finite := by
  by_contra h
  obtain ⟨D, hD, hc⟩ := Set.Infinite.exists_subset_card_eq h (2 * (G.A + G.s + G.t) + 1)
  have := G.main D
  have := card_nsmul_le_sum D (G.ncomp · - 1) 1 fun d hd => Nat.le_sub_of_add_le (hD hd)
  grind

abbrev φ := aeval (R := K) (Polynomial.X (R := K) ^ G.N ·)

def mono (z : Fin 4 → ℕ) := monomial (Finsupp.equivFunOnFinite.symm z) (1 : K)

def root d := Classical.epsilon (G.ν · = d)

def gens d :=
  if h : G.ν (G.root d) = d then ((univ.erase (G.cc ⟨_, h⟩)).image
    fun C => mono K (Quot.out C).1 - mono K (G.root d)) else ∅

def J := Ideal.span {g | g ∈ G.D0fin.toFinset.biUnion (G.gens K)}

def q := Ideal.Quotient.mk (G.J K)

lemma φ_mono s c : G.φ K (monomial s c) = Polynomial.monomial (G.ν s) c := by
  simp [aeval_monomial, Finsupp.prod_fintype, ← pow_mul, prod_pow_eq_pow_sum, dotProduct, mul_comm,
    Polynomial.C_mul_X_pow_eq_monomial]

lemma key x : G.q K (mono K x) = G.q K (mono K (G.root (G.ν x))) := by
  induction hx : G.ν x using Nat.strong_induction_on generalizing x
  rename_i d ih
  have hr := Classical.epsilon_spec (p := (G.ν · = d)) ⟨x, hx⟩
  have edge (w : G.V d) i (hw : 0 < w.1 i) :
      G.q K (mono K w.1) = G.q K (X i * mono K (G.root (d - G.N i))) := by
    have := G.ν_sub (sle (c := 1) hw)
    have : G.ν (Pi.single i 1) = _ := single_one_dotProduct ..
    have := G.n_pos i
    have := w.2
    rw [map_mul, ← ih _ (by omega) (w.1 - Pi.single i 1) (by omega), ← map_mul]
    simp_all [mono, X]
    congr
    ext
    simp
    grind
  have hreach u v (p : (G.Γ d).Walk u v) : G.q K (mono K u.1) = G.q K (mono K v.1) := by
    induction p <;> grind [fromRel_adj]
  by_cases hc : G.cc ⟨x, hx⟩ = G.cc ⟨_, hr⟩
  · exact hreach ⟨x, hx⟩ ⟨_, hr⟩ (ConnectedComponent.exact hc).some
  refine (hreach ⟨x, hx⟩ _ (ConnectedComponent.exact (Quot.out_eq _).symm).some).trans
    (Ideal.Quotient.eq.2 (Ideal.subset_span (mem_biUnion.2 ⟨d,
      by simpa using Fintype.one_lt_card_iff.2 ⟨_, _, hc⟩, by grind [gens, root]⟩)))

theorem bridge : (toricIdeal K G.N).spanRank ≤ (2 * (G.A + G.s + G.t) : ℕ) := by
  have : toricIdeal K G.N = G.J K := by
    refine le_antisymm (fun f hf => ?_) (Ideal.span_le.2 fun g hg => ?_)
    · simpa [show G.φ K f = 0 from hf] using f.induction_on' (P := fun f => f - Polynomial.lsum (LinearMap.toSpanSingleton K _ <| mono K <| G.root ·)
          (G.φ K f) ∈ G.J K) (fun s a => by
          simpa [φ_mono, mono, smul_sub, smul_monomial] using Submodule.smul_of_tower_mem _ a (Ideal.Quotient.eq.1 (G.key K s)))
        fun p q hp hq => by simpa [map_add, add_sub_add_comm] using add_mem hp hq
    · simp [gens, mem_dite] at hg
      obtain ⟨d, -, H, h⟩ := hg
      obtain ⟨C, -, rfl⟩ := H h
      simp [toricIdeal, mono, φ_mono, (Quot.out C).2, h]
  refine this ▸ (Submodule.spanRank_span_le_card _).trans (Cardinal.mk_coe_finset.trans_le (Nat.cast_le.2
    (card_biUnion_le.trans ((sum_le_sum fun d _ => ?_).trans (G.main _)))))
  unfold gens
  split_ifs <;> simp [card_image_le.trans]

end GD

variable (hpos : 0 < n 0) (hmono : StrictMono n)
  (hgcd : Finset.univ.gcd n = 1) (hmin : MinimallyGenerates n)
include hpos hmono hgcd hmin

theorem beta1_le_two_mul_normalizedWidth :
    (toricIdeal K n).spanRank ≤ (2 * normalizedWidth n : ℕ) := by
  unfold normalizedWidth
  set g := Nat.gcd (n 1 - n 0) (Nat.gcd (n 2 - n 0) (n 3 - n 0))
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩, W, hW⟩ := (Nat.dvd_gcd_iff.1 (dvd_refl g)).imp_right Nat.dvd_gcd_iff.1
  simp [Fin.strictMono_iff_lt_succ, Fin.forall_fin_succ] at hmono
  have h0 : 0 < g * A := by omega
  have hAB := Nat.lt_of_mul_lt_mul_left (by omega : g * A < g * B)
  have hBW := Nat.lt_of_mul_lt_mul_left (by omega : g * B < g * W)
  convert (GD.mk (n 0) g A (B - A) (W - B) ⟨hpos, Nat.pos_of_mul_pos_left h0, by omega, by omega⟩).bridge K using 3 <;> (try funext i; fin_cases i) <;> simp [GD.N, hW, Nat.pos_of_mul_pos_right h0] <;> grind

theorem beta1_le_two_mul_width : (toricIdeal K n).spanRank ≤ (2 * (n 3 - n 0) : ℕ) :=
  (beta1_le_two_mul_normalizedWidth K n hpos hmono hgcd hmin).trans
    (by gcongr; apply Nat.div_le_self)

end SemigroupBetti
