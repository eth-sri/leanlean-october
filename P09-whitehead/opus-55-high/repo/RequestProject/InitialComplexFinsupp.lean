import RequestProject.InitialComplex
import RequestProject.CoreSignedCollapseFinsupp
import RequestProject.Tac


/-! The actual initial presentation `relY` is Cockcroft for an arbitrary
acyclic core. All cycle computations use finite-support chains. The
pointwise Fox and first-order augmentation calculations are those of the
original construction; no finite presentation is substituted for the core. -/

noncomputable section
open scoped Classical

bwd

namespace FiniteChains
open BlockFamily

variable {I J : Type} [LinearOrder I] [DecidableEq I] (r : J → FreeGroup I)

omit [LinearOrder I] in
theorem expSurjective_of_expMatrix_surjective
    (h : Function.Surjective (expMatrix r)) : ExpSurjective r := by
  tauto

/-- A supported cycle can be read through any additive coefficient
functional which detects one cell. -/
theorem fs_boundary_extract {A L : Type} [DecidableEq A]
    ρ (ψ : MonoidAlgebra ℤ (PresGroup ρ) →+ ℤ)
    (a : A) k s
    (hterm : ∀ j z,
      ψ (z * foxMatrixPres ρ a j) = if j = k then s * augPres ρ z else 0)
    (v : L →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    ψ (coverSecondBoundary (relSub ρ) ρ v a) = s * augPres ρ (v k) := by
  lin_ind v with v w hv hw => simp [map_add, Finsupp.add_apply, hv, hw, mul_add]
  | j z =>
      rw [fsCoverSecondBoundary_apply, Finsupp.sum_single_index (zero_mul _), hterm]
      grind

theorem psiY_mid_cross_zero (hM : ExpSurjective r) i
    c z :
    psiY r (i, true)
      (z * foxMatrixPres (relY r) (Sum.inr (i, false)) (Sum.inr (Sum.inr c))) = 0 := by
  rw [psiY_cross_term hM]
  grind

theorem psiY_mid_cell (hM : ExpSurjective r) i
    c z :
    psiY r (i, true) (z * foxMatrixPres (relY r) (Sum.inr (i, false)) c) =
      if c = Sum.inr (Sum.inl i) then augPres (relY r) z else 0 := by
  cases c with
  | inl j => simp [foxMatrix_inr_inl, mul_zero, map_zero, Sum.inl_ne_inr, if_false]
  | inr c =>
    cases c with
    | inl k =>
      by_cases hk : k = i
      · subst k
        rw [foxMatrix_inr_mid hM]
        simpa using psiY_mul_sub_one r (i, true) (i, true) z
      · simp [foxMatrix_inr_mid hM, hk]
    | inr c =>
      rw [psiY_mid_cross_zero r hM]
      simp

theorem fs_aug_cycle_mid (hM : ExpSurjective r)
    {v : CellY I J →₀ MonoidAlgebra ℤ (GroupY r)}
    (hv : FSIsFoxCycle (relY r) v) i :
    augPres (relY r) (v (Sum.inr (Sum.inl i))) = 0 := by
  have h := fs_boundary_extract _ (psiY r (i, true)).toAddMonoidHom
    _ _ 1
    (by intro c z; simpa [one_mul, LinearMap.toAddMonoidHom_coe] using psiY_mid_cell r hM i c z) v
  change coverSecondBoundary _ _ v = 0 at hv
  simp_all

theorem psiY_cross_mid_zero (hM : ExpSurjective r) {p q} (hpq : p < q)
    u w k z :
    psiY r (q, w)
      (z * foxMatrixPres (relY r) (Sum.inr (p, u)) (Sum.inr (Sum.inl k))) = 0 := by
  rw [foxMatrix_inr_mid hM]
  by_cases hk : k = p
  · subst k
    have hne (b : Bool) : ((p, b)) ≠ (q, w) :=
      by grind
    rw [if_pos rfl]
    cases u
    · simp_all [psiY_mul_sub_one r _ (p, true), mul_zero]
    · change psiY r (q, w) (z * -(yRing p false - 1)) = 0
      rw [mul_neg, map_neg, psiY_mul_sub_one r _ (p, false),
        if_neg (hne false), mul_zero, neg_zero]
  simp_all

theorem psiY_cross_cross_extract (hM : ExpSurjective r)
    c₀ c z :
    psiY r (c₀.1.1.2, c₀.2.2)
      (z * foxMatrixPres (relY r) (Sum.inr (c₀.1.1.1, c₀.2.1))
        (Sum.inr (Sum.inr c))) =
      if c = c₀ then -augPres (relY r) z else 0 := by
  obtain ⟨⟨⟨p, q⟩, hpq⟩, u, w⟩ := c₀
  by_cases hc : c = (⟨(p, q), hpq⟩, u, w)
  · grind [psiY_cross_term hM]
  · rw [psiY_cross_term hM]
    grind

theorem psiY_cross_cell (hM : ExpSurjective r) c₀
    c z :
    psiY r (c₀.1.1.2, c₀.2.2)
      (z * foxMatrixPres (relY r) (Sum.inr (c₀.1.1.1, c₀.2.1)) c) =
      if c = Sum.inr (Sum.inr c₀) then -augPres (relY r) z else 0 := by
  cases c with
  | inl j => simp [foxMatrix_inr_inl, mul_zero, map_zero, Sum.inl_ne_inr, if_false]
  | inr c =>
    cases c with
    | inl k =>
      rw [psiY_cross_mid_zero r hM c₀.1.property]
      simp
    | inr c => simpa using psiY_cross_cross_extract r hM c₀ c z

theorem fs_aug_cycle_cross (hM : ExpSurjective r)
    {v : CellY I J →₀ MonoidAlgebra ℤ (GroupY r)}
    (hv : FSIsFoxCycle (relY r) v) c₀ :
    augPres (relY r) (v (Sum.inr (Sum.inr c₀))) = 0 := by
  have h := fs_boundary_extract _
    (psiY r (c₀.1.1.2, c₀.2.2)).toAddMonoidHom
    _ _ (-1)
    (by intro c z; simpa [neg_one_mul, LinearMap.toAddMonoidHom_coe] using psiY_cross_cell r hM c₀ c z) v
  change coverSecondBoundary _ _ v = 0 at hv
  simp_all

/-- The same concrete initial presentation as in Lemma 3.1, now for any
sets of core generators and core relators. -/
theorem fsIsCockcroft_relY (hMs : ExpSurjective r)
    (hMi : Function.Injective (expMatrix r)) : FSIsCockcroft (relY r) := by
  let extra := fun c => relY r (Sum.inr c)
  have he : corePres r extra = relY r := by
    aesop
  have href := corePres_fsAugmentation_reflect r extra hMi
  rw [he] at href
  intro v hv
  apply href v hv
  intro c
  cases c with
  | inl i => exact fs_aug_cycle_mid r hMs hv i
  | inr c => exact fs_aug_cycle_cross r hMs hv c

theorem fsIsCockcroft_relY_of_expMatrix_bijective
    (hM : Function.Bijective (expMatrix r)) : FSIsCockcroft (relY r) :=
  fsIsCockcroft_relY r (expSurjective_of_expMatrix_surjective r hM.2) hM.1
