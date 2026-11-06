import RequestProject.OrderNerveRealizationMapCoordinates
import RequestProject.Tac


/-! Exact barycentric-coordinate reconstruction for a finite poset. This is
used to split an actual cone point into its radial coordinate and base point. -/

noncomputable section
bwd

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical

theorem orderNerveRealizationCoordinates_simplex {P} [PartialOrder P]
    {n} s
    (z : SimplexCategory.toTop.obj n) p :
    orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) p =
      orderNerveAffineSimplex (if · = p then 1 else 0) s z :=
  congrArg (· z)
    (orderNerveAffineRealization_simplex _ s)

theorem orderNerveRealizationCoordinates_nonneg {P} [PartialOrder P]
    x p :
    0 ≤ orderNerveRealizationCoordinates P x p := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  rw [orderNerveRealizationCoordinates_simplex]
  change 0 ≤ ∑ i, z.down.weights i * (if s.obj i = p then 1 else 0)
  apply Finset.sum_nonneg
  aesop

theorem orderNerveRealizationCoordinates_sum {P} [PartialOrder P] [Fintype P]
    x : ∑ p, orderNerveRealizationCoordinates P x p = 1 := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  simp only [orderNerveRealizationCoordinates_simplex, orderNerveAffineSimplex,
    ContinuousMap.coe_mk]
  rw [Finset.sum_comm]
  simp

theorem orderNerveRealizationCoordinates_support_chain {P} [PartialOrder P]
    (x : orderNerveRealization P) :
    IsChain (· ≤ ·) {p | 0 < orderNerveRealizationCoordinates P x p} := by
  obtain ⟨n, s, z, hz, rfl⟩ := orderNerveRealization_interior_cover P x
  intro p hp q hq _
  rw [Set.mem_setOf_eq, orderNerveRealizationCoordinates_simplex] at hp hq
  obtain ⟨i, rfl⟩ := (orderNerveAffineSimplex_indicator_pos_iff s.val z hz p).mp hp
  obtain ⟨j, rfl⟩ := (orderNerveAffineSimplex_indicator_pos_iff s.val z hz q).mp hq
  rcases le_total i j with hij | hij
  · exact Or.inl (leOfHom (s.val.map (homOfLE hij)))
  · exact Or.inr (leOfHom (s.val.map (homOfLE hij)))

/-- Every probability vector whose positive support is a chain represents
an actual point of the geometric realization, with precisely those coordinates. -/
theorem orderNerveRealizationCoordinates_exists {P} [PartialOrder P] [Fintype P]
    (c : P → ℝ) (hc : ∀ p, 0 ≤ c p) (hsum : ∑ p, c p = 1)
    (hchain : IsChain (· ≤ ·) {p | 0 < c p}) :
    ∃ x, ∀ p, orderNerveRealizationCoordinates P x p = c p := by
  let A := {p : P // 0 < c p}
  have hzero : ∀ p, ¬ 0 < c p → c p = 0 :=
    by grind
  have hA : ∑ p : A, c p.val = 1 := by
    have h := Fintype.sum_subtype_add_sum_subtype (0 < c ·) c
    have hz : (∑ p : {p : P // ¬ 0 < c p}, c p.val) = 0 :=
      Finset.sum_eq_zero (by simp_all)
    grind
  have hne : Nonempty A := by
    by_contra hn
    simp_all
  letI : LinearOrder A :=
    { Subtype.partialOrder _ with
      le_total := fun x y => hchain.total x.property y.property
      toDecidableLE := Subtype.decidableLE
      toDecidableLT := Subtype.decidableLT
      toDecidableEq := Subtype.instDecidableEq }
  cases' Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := A))) with n hn
  let e := (Fintype.orderIsoFinOfCardEq A hn).symm
  let s :=
    (show Monotone (fun i => (e.symm i).val) from
      fun _ _ hij => e.symm.monotone hij).functor
  have hs := Subtype.val_injective.comp e.symm.injective
  let zold : stdSimplex ℝ (Fin (n + 1)) := ⟨fun i => c (s.obj i),
    ⟨by simp_all, (e.symm.toEquiv.sum_comp (c ·.val)).trans hA⟩⟩
  let z :=
    ULift.up ((TopologicalSingular.simplexCoordinates n).symm zold)
  refine ⟨orderNerveRealizationSimplex P s z, ?_⟩
  intro p
  by_cases hp : 0 < c p
  · let i := e ⟨p, hp⟩
    have hi : s.obj i = p := by aesop
    calc
      orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) p =
          orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) (s.obj i) :=
        by simp_all
      _ = z.down.weights i := (orderNerveRealizationCoordinates_simplex s z _).trans
        (orderNerveAffineSimplex_indicator s hs i z)
      _ = c p := by
        aesop
  · have hn : ∀ i, s.obj i ≠ p := by
      intro i hi
      exact hp (hi ▸ (e.symm i).property)
    rw [orderNerveRealizationCoordinates_simplex]
    simp [orderNerveAffineSimplex, ContinuousMap.coe_mk, hn, ite_false, mul_zero,
      Finset.sum_const_zero, hzero p hp]
