module

public import RequestProject.InitialComplex
public import RequestProject.CoreSignedCollapseFinsupp

@[expose] public section

/-! The actual initial presentation `relY` is Cockcroft for an arbitrary
acyclic core. All cycle computations use finite-support chains. The
pointwise Fox and first-order augmentation calculations are those of the
original construction; no finite presentation is substituted for the core. -/

noncomputable section
open scoped Classical

namespace FiniteChains
open BlockFamily

variable {I J : Type} [LinearOrder I] [DecidableEq I] (r : J → FreeGroup I)

omit [LinearOrder I] in
theorem expSurjective_of_expMatrix_surjective
    (h : Function.Surjective (expMatrix r)) : ExpSurjective r := by
  assumption

/-- A supported cycle can be read through any additive coefficient
functional which detects one cell. -/
theorem fs_boundary_extract {A L : Type} [DecidableEq A]
    (ρ : L → FreeGroup A) (ψ : MonoidAlgebra ℤ (PresGroup ρ) →+ ℤ)
    (a : A) (k : L) (s : ℤ)
    (hterm : ∀ (j : L) (z : MonoidAlgebra ℤ (PresGroup ρ)),
      ψ (z * foxMatrixPres ρ a j) = if j = k then s * augPres ρ z else 0)
    (v : L →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    ψ (coverSecondBoundary (relSub ρ) ρ v a) = s * augPres ρ (v k) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, Finsupp.add_apply, hv, hw, mul_add]
  | single j z =>
      rw [fsCoverSecondBoundary_apply, Finsupp.sum_single_index (zero_mul _), hterm]
      by_cases hj : j = k
      · simp_all
      · simp [hj]

section

variable (hM : ExpSurjective r)
include hM

variable (i : I)

theorem psiY_mid_cross_zero
    (c : CrossY I) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r (i, true)
      (z * foxMatrixPres (relY r) (Sum.inr (i, false)) (Sum.inr (Sum.inr c))) = 0 := by
  obtain ⟨⟨⟨p, q⟩, hpq⟩, u, w⟩ := c
  rw [psiY_cross_term hM] <;> grind

theorem psiY_mid_cell
    (c : CellY I J) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r (i, true) (z * foxMatrixPres (relY r) (Sum.inr (i, false)) c) =
      if c = Sum.inr (Sum.inl i) then augPres (relY r) z else 0 := by
  cases c with
  | inl j => simp_all [foxMatrix_inr_inl]
  | inr c =>
    cases c with
    | inl k =>
      by_cases hk : k = i
      · subst k
        rw [foxMatrix_inr_mid hM, if_pos rfl]
        simpa using psiY_mul_sub_one r (i, true) (i, true) z
      · simp_all [foxMatrix_inr_mid, hk]
    | inr c =>
      simp_all [psiY_mid_cross_zero]

theorem fs_aug_cycle_mid
    {v : CellY I J →₀ MonoidAlgebra ℤ (GroupY r)}
    (hv : FSIsFoxCycle (relY r) v) (i : I) :
    augPres (relY r) (v (Sum.inr (Sum.inl i))) = 0 := by
  have h := fs_boundary_extract (relY r) (psiY r (i, true)).toAddMonoidHom
    (Sum.inr (i, false)) (Sum.inr (Sum.inl i)) 1
    (by simp_all [psiY_mid_cell]) v
  rw [hv, Finsupp.zero_apply, map_zero, one_mul] at h; exact h.symm

theorem psiY_cross_mid_zero {p q : I} (hpq : p < q)
    (u w : Bool) (k : I) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r (q, w)
      (z * foxMatrixPres (relY r) (Sum.inr (p, u)) (Sum.inr (Sum.inl k))) = 0 := by
  rw [foxMatrix_inr_mid hM]
  by_cases hk : k = p
  · subst k
    have hne (b : Bool) : ((p, b) : I × Bool) ≠ (q, w) :=
      fun h => (ne_of_lt hpq) (congrArg Prod.fst h)
    rw [if_pos rfl]
    cases u
    · change psiY r (q, w) (z * (yRing p true - 1)) = 0
      rw [psiY_mul_sub_one r (q, w) (p, true), if_neg (hne true), mul_zero]
    · change psiY r (q, w) (z * -(yRing p false - 1)) = 0
      rw [mul_neg, map_neg, psiY_mul_sub_one r (q, w) (p, false),
        if_neg (hne false), mul_zero, neg_zero]
  · simp_all

theorem psiY_cross_cross_extract
    (c₀ c : CrossY I) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r (c₀.1.1.2, c₀.2.2)
      (z * foxMatrixPres (relY r) (Sum.inr (c₀.1.1.1, c₀.2.1))
        (Sum.inr (Sum.inr c))) =
      if c = c₀ then -augPres (relY r) z else 0 := by
  obtain ⟨⟨⟨p, q⟩, hpq⟩, u, w⟩ := c₀
  by_cases hc : c = (⟨(p, q), hpq⟩, u, w)
  · subst c
    have hne : ((p, u) : I × Bool) ≠ (q, w) :=
      fun h => (ne_of_lt hpq) (congrArg Prod.fst h)
    simp_all [psiY_cross_term, hne]
  · obtain ⟨⟨⟨p', q'⟩, hpq'⟩, u', w'⟩ := c
    rw [psiY_cross_term hM, if_neg hc] <;> grind

theorem psiY_cross_cell (c₀ : CrossY I)
    (c : CellY I J) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r (c₀.1.1.2, c₀.2.2)
      (z * foxMatrixPres (relY r) (Sum.inr (c₀.1.1.1, c₀.2.1)) c) =
      if c = Sum.inr (Sum.inr c₀) then -augPres (relY r) z else 0 := by
  cases c with
  | inl j => simp_all [foxMatrix_inr_inl]
  | inr c =>
    cases c with
    | inl k =>
      rw [psiY_cross_mid_zero r hM c₀.1.property]
      simp
    | inr c => simpa using psiY_cross_cross_extract r hM c₀ c z

theorem fs_aug_cycle_cross
    {v : CellY I J →₀ MonoidAlgebra ℤ (GroupY r)}
    (hv : FSIsFoxCycle (relY r) v) (c₀ : CrossY I) :
    augPres (relY r) (v (Sum.inr (Sum.inr c₀))) = 0 := by
  have h := fs_boundary_extract (relY r)
    (psiY r (c₀.1.1.2, c₀.2.2)).toAddMonoidHom
    (Sum.inr (c₀.1.1.1, c₀.2.1)) (Sum.inr (Sum.inr c₀)) (-1)
    (by simp_all [psiY_cross_cell]) v
  rw [hv, Finsupp.zero_apply, map_zero, neg_one_mul] at h; exact neg_eq_zero.mp h.symm

end

/-- The same concrete initial presentation as in Lemma 3.1, now for any
sets of core generators and core relators. -/
theorem fsIsCockcroft_relY (hMs : ExpSurjective r)
    (hMi : Function.Injective (expMatrix r)) : FSIsCockcroft (relY r) := by
  let extra := fun c => relY r (Sum.inr c)
  have he : corePres r extra = relY r := by
    funext c
    cases c <;> rfl
  have href := corePres_fsAugmentation_reflect r extra hMi
  rw [he] at href
  intro v hv
  apply href v hv
  grind [fs_aug_cycle_mid, fs_aug_cycle_cross]

theorem fsIsCockcroft_relY_of_expMatrix_bijective
    (hM : Function.Bijective (expMatrix r)) : FSIsCockcroft (relY r) :=
  fsIsCockcroft_relY r (expSurjective_of_expMatrix_surjective r hM.2) hM.1

end FiniteChains
