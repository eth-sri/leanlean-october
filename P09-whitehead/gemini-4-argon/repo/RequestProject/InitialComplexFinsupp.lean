module

public import RequestProject.InitialComplex
public import RequestProject.CoreSignedCollapseFinsupp

@[expose] public section

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains
open BlockFamily

variable {I J : Type} [LinearOrder I] [DecidableEq I] (r : J → FreeGroup I)

omit [LinearOrder I] in
theorem expSurjective_of_expMatrix_surjective
    (h : Function.Surjective (expMatrix r)) : ExpSurjective r := by
  rw [ExpSurjective, funext (expCol_eq_expVec r)]; exact h

theorem fs_boundary_extract {A L : Type} [DecidableEq A]
    (ρ : L → FreeGroup A) (ψ : MonoidAlgebra ℤ (PresGroup ρ) →+ ℤ) (a : A) (k : L) (s : ℤ)
    (hterm : ∀ (j : L) (z : MonoidAlgebra ℤ (PresGroup ρ)),
      ψ (z * foxMatrixPres ρ a j) = if j = k then s * augPres ρ z else 0)
    (v : L →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    ψ (coverSecondBoundary (relSub ρ) ρ v a) = s * augPres ρ (v k) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, Finsupp.add_apply, hv, hw, mul_add]
  | single j z =>
      rw [fsCoverSecondBoundary_apply, Finsupp.sum_single_index (zero_mul _), hterm]
      by_cases hj : j = k <;> simp [hj]

theorem psiY_mid_cell (hM : ExpSurjective r) (i : I)
    (c : CellY I J) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r (i, true) (z * foxMatrixPres (relY r) (Sum.inr (i, false)) c) =
      if c = Sum.inr (Sum.inl i) then augPres (relY r) z else 0 := by
  rcases c with j | k | ⟨⟨⟨p, q⟩, hpq⟩, u, w⟩
  · simp [foxMatrix_inr_inl]
  · by_cases hk : k = i
    · subst k; rw [foxMatrix_inr_mid hM, if_pos rfl]
      simpa using psiY_mul_sub_one r (i, true) (i, true) z
    · simp [foxMatrix_inr_mid hM, hk]
  · rw [psiY_cross_term hM]
    have : p ≠ q := ne_of_lt hpq
    split_ifs <;> simp_all

theorem psiY_cross_cell (hM : ExpSurjective r) (c₀ : CrossY I)
    (c : CellY I J) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r (c₀.1.1.2, c₀.2.2)
      (z * foxMatrixPres (relY r) (Sum.inr (c₀.1.1.1, c₀.2.1)) c) =
      if c = Sum.inr (Sum.inr c₀) then -augPres (relY r) z else 0 := by
  obtain ⟨⟨⟨p, q⟩, hpq⟩, u, w⟩ := c₀
  rcases c with j | k | c
  · simp [foxMatrix_inr_inl]
  · rw [foxMatrix_inr_mid hM]; simp only [Sum.inr.injEq, reduceCtorEq, ite_false]
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
    · rw [if_neg hk, mul_zero, map_zero]
  · simp only [Sum.inr.injEq]
    by_cases hc : c = (⟨(p, q), hpq⟩, u, w)
    · subst c
      have hne : ((p, u) : I × Bool) ≠ (q, w) := fun h => (ne_of_lt hpq) (congrArg Prod.fst h)
      rw [psiY_cross_term hM]; simp [hne]
    · obtain ⟨⟨⟨p', q'⟩, hpq'⟩, u', w'⟩ := c
      rw [psiY_cross_term hM, if_neg hc]
      have hfirst : ((p, u) : I × Bool) = (p', u') → (q', w') ≠ (q, w) := by
        rintro ⟨⟩ ⟨⟩; exact hc rfl
      have hsecond : ((p, u) : I × Bool) = (q', w') → (p', u') ≠ (q, w) := by
        intro h₁ h₂
        have := congrArg Prod.fst h₁; have := congrArg Prod.fst h₂
        subst_vars; exact lt_asymm hpq hpq'
      split_ifs <;> simp_all

theorem fsIsCockcroft_relY (hMs : ExpSurjective r)
    (hMi : Function.Injective (expMatrix r)) : FSIsCockcroft (relY r) := by
  let extra : I ⊕ CrossY I → FreeGroup (GenY I) := fun c => relY r (Sum.inr c)
  have he : corePres r extra = relY r := by funext c; cases c <;> rfl
  have href := corePres_fsAugmentation_reflect r extra hMi
  rw [he] at href
  intro v hv
  apply href v hv
  rintro (i | c₀)
  · have h := fs_boundary_extract (relY r) (psiY r (i, true)).toAddMonoidHom
      (Sum.inr (i, false)) (Sum.inr (Sum.inl i)) 1
      (fun c z => by simpa only [one_mul, LinearMap.toAddMonoidHom_coe] using psiY_mid_cell r hMs i c z) v
    change coverSecondBoundary _ _ v = 0 at hv
    rw [hv, Finsupp.zero_apply, map_zero, one_mul] at h; exact h.symm
  · have h := fs_boundary_extract (relY r) (psiY r (c₀.1.1.2, c₀.2.2)).toAddMonoidHom
      (Sum.inr (c₀.1.1.1, c₀.2.1)) (Sum.inr (Sum.inr c₀)) (-1)
      (fun c z => by simpa only [neg_one_mul, LinearMap.toAddMonoidHom_coe] using psiY_cross_cell r hMs c₀ c z) v
    change coverSecondBoundary _ _ v = 0 at hv
    rw [hv, Finsupp.zero_apply, map_zero, neg_one_mul] at h; exact neg_eq_zero.mp h.symm

theorem fsIsCockcroft_relY_of_expMatrix_bijective
    (hM : Function.Bijective (expMatrix r)) : FSIsCockcroft (relY r) :=
  fsIsCockcroft_relY r (expSurjective_of_expMatrix_surjective r hM.2) hM.1
