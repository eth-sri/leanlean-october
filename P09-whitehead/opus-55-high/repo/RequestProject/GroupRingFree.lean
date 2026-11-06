import Mathlib
noncomputable section


/-!
# `k[Q]` is a free `k[H]`-module on coset representatives

Lemma 2.1 of the paper is reduced, in its "outline of a direct proof", to a
statement about free modules over the commutative domain `k[H]` by means of the
remark that

> the free modules remain free, since `k[Q]` is free over `k[H]` on coset
> representatives.

This file proves exactly that remark, with no hypotheses on `k`, `Q` or `H`
beyond `k` a commutative ring, `Q` a group and `H ≤ Q` a subgroup: the group
algebra `k[Q]`, viewed as a left module over `k[H]` through the inclusion
`k[H] → k[Q]`, is free with basis the right cosets `H \ Q`, a basis element
being the chosen representative of the coset.

The commutative-algebra core of Lemma 2.1 itself is in
`RequestProject/QuotientInjectivity.lean`.
-/

namespace FiniteChains

open MonoidAlgebra

variable (k : Type*) [CommRing k] {Q : Type*} [Group Q] (H : Subgroup Q)

/-- The right cosets `H \ Q`; left multiplication by `H` preserves a class. -/
abbrev RightCosets := Quotient (QuotientGroup.rightRel H)

/-- The inclusion of group algebras `k[H] → k[Q]`. -/
def groupRingIncl : MonoidAlgebra k H →+* MonoidAlgebra k Q :=
  MonoidAlgebra.mapDomainRingHom k H.subtype

/-- `k[Q]` as a left module over `k[H]`. -/
instance moduleGroupRing :
    Module (MonoidAlgebra k H) (MonoidAlgebra k Q) := (groupRingIncl k H).toModule

variable {k H}

theorem groupRingIncl_apply_mem x q hq :
    (groupRingIncl k H x).coeff q = x.coeff ⟨q, hq⟩ :=
  Finsupp.mapDomain_apply_of_injective Subtype.val_injective x.coeff ⟨q, hq⟩

theorem groupRingIncl_apply_notMem x q (hq : q ∉ H) :
    (groupRingIncl k H x).coeff q = 0 := by
  refine Finsupp.mapDomain_notin_range x.coeff q ?_
  simp_all

theorem smul_def' x y :
    x • y = groupRingIncl k H x * y := rfl

theorem groupRingIncl_single h a :
    groupRingIncl k H (single h a) = single (h : Q) a :=
  MonoidAlgebra.mapDomain_single

variable (k H)

/-- The chosen representative of a right coset. -/
def cosetRep (c : RightCosets H) := c.out

variable {k H}

theorem mul_cosetRep_inv_mem q :
    q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹ ∈ H := by
  have h : (Quotient.mk _ q) =
      Quotient.mk _
        (cosetRep H (Quotient.mk _ q)) :=
    (Quotient.out_eq _).symm
  have := Quotient.exact h.symm
  exact QuotientGroup.rightRel_apply.mp this

theorem mk_eq_iff :
    Quotient.mk (QuotientGroup.rightRel H) q = Quotient.mk (QuotientGroup.rightRel H) r ↔
      r * q⁻¹ ∈ H := by
  rw [Quotient.eq]
  exact QuotientGroup.rightRel_apply

/-- The `k[H]`-linear map `(H \ Q →₀ k[H]) → k[Q]` sending the `c`-th basis vector to the
chosen representative of the coset `c`. -/
def cosetCombination :
    (RightCosets H →₀ MonoidAlgebra k H) →ₗ[MonoidAlgebra k H] MonoidAlgebra k Q :=
  Finsupp.linearCombination (MonoidAlgebra k H) fun c => single (cosetRep H c) (1 : k)

/-- The coefficients of `cosetCombination`: the `q`-th coefficient only sees the coset of
`q`, at the position `q · (rep of its coset)⁻¹` of `H`. -/
theorem cosetCombination_apply (F : RightCosets H →₀ MonoidAlgebra k H) q :
    (cosetCombination F).coeff q =
      (F (Quotient.mk (QuotientGroup.rightRel H) q)).coeff
        ⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹,
          mul_cosetRep_inv_mem q⟩ := by
  classical
  rw [cosetCombination, Finsupp.linearCombination_apply, Finsupp.sum]
  have hterm : ∀ c ∈ F.support,
      (F c • single (cosetRep H c) (1)).coeff q =
        if Quotient.mk _ q = c then
          (F (Quotient.mk _ q)).coeff
            ⟨q * (cosetRep H (Quotient.mk _ q))⁻¹,
              mul_cosetRep_inv_mem q⟩
        else 0 := by
    intro c _
    rw [smul_def', MonoidAlgebra.coeff_mul_single_apply, mul_one]
    by_cases hc : Quotient.mk _ q = c
    · subst hc
      rw [if_pos rfl]
      exact groupRingIncl_apply_mem _ _ _
    · rw [if_neg hc]
      refine groupRingIncl_apply_notMem _ _ ?_
      intro hmem
      apply hc
      have : Quotient.mk _ q =
          Quotient.mk (QuotientGroup.rightRel H) (cosetRep H c) := by
        grind [mk_eq_iff]
      rw [this]
      exact c.out_eq
  have hsum : (∑ c ∈ F.support, F c • single (cosetRep H c) (1 : k)).coeff q
      = ∑ c ∈ F.support, (F c • single (cosetRep H c) (1)).coeff q := by
    simp
  rw [hsum, Finset.sum_congr rfl hterm]
  simp_all

/-- The inverse bijection `Q ≃ (H \ Q) × H`. -/
def cosetEquiv : Q ≃ (RightCosets H × H) where
  toFun q := (Quotient.mk (QuotientGroup.rightRel H) q,
    ⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹, mul_cosetRep_inv_mem q⟩)
  invFun p := (p.2 : Q) * cosetRep H p.1
  left_inv q := by simp
  right_inv p := by
    obtain ⟨c, h, hh⟩ := p
    have hmk : Quotient.mk (QuotientGroup.rightRel H) ((h : Q) * cosetRep H c) = c := by
      have : Quotient.mk (QuotientGroup.rightRel H) ((h : Q) * cosetRep H c) =
          Quotient.mk _ (cosetRep H c) := by
        rw [mk_eq_iff]
        simp_all
      rw [this]; exact c.out_eq
    simp_all

/-- `cosetCombination` is bijective: `k[Q]` is free over `k[H]` on coset representatives. -/
theorem cosetCombination_bijective :
    Function.Bijective (cosetCombination (k := k) (H := H)) := by
  classical
  constructor
  · intro F G hFG
    ext c h
    have h1 := congrArg (·.coeff (h * cosetRep H c)) hFG
    simp [cosetCombination_apply] at h1
    have hmk : Quotient.mk _ (h * cosetRep H c) = c :=
      congrArg Prod.fst ((cosetEquiv (H := H)).right_inv (c, h))
    simp_all
  · intro f
    refine MonoidAlgebra.induction f ⟨0, map_zero _⟩ ?_
    rintro q a g - - ⟨G, hG⟩
    refine ⟨Finsupp.single (Quotient.mk _ q)
      (single ⟨q * (cosetRep H (Quotient.mk _ q))⁻¹,
        mul_cosetRep_inv_mem q⟩ a) + G, ?_⟩
    rw [map_add, hG, cosetCombination, Finsupp.linearCombination_single, smul_def',
      groupRingIncl_single, MonoidAlgebra.single_mul_single]
    simp

/-- The basis of `k[Q]` over `k[H]` given by coset representatives. -/
def cosetBasis :
    Module.Basis (RightCosets H) (MonoidAlgebra k H) (MonoidAlgebra k Q) :=
  Module.Basis.ofRepr
    (LinearEquiv.ofBijective _
      cosetCombination_bijective).symm
