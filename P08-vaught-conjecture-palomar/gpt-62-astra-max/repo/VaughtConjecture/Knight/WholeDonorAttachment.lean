/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorBoundary
public import VaughtConjecture.Knight.RequestAttachment

/-! # Literal attachment of a whole donor to a private context

The plan is attached along the literal common root; occurrences and rows use
the ordered union in `WholeDonorBoundary`, not `requestInventory`. No labels,
catalogue, model, or receiving predicate are needed for this input adapter.
-/

@[expose] public section

namespace VaughtConjecture.Knight.WholeDonorAttachment
open AmalgamationPlan Transform Value ExtOrd
noncomputable section
variable {n N : ℕ} (e : Fin n ↪ Fin N)

abbrev privateScope : Finset (Fin (N + 1)) := Finset.univ.image Fin.castSuccEmb
abbrev donorScope : Finset (Fin (N + 1)) := Finset.univ.image (onePointProj e)
abbrev rootScope : Finset (Fin (N + 1)) := Finset.univ.image (e.trans Fin.castSuccEmb)

theorem donor_card : (donorScope e).card = n + 1 := by
  rw [Finset.card_image_of_injective _ (onePointProj e).injective]
  simp

theorem fresh_private : Fin.last N ∉ privateScope := by
  simp

theorem root_private : rootScope e ⊆ privateScope := by
  intro x hx
  aesop

theorem root_left_image : (Finset.univ.image e).image Fin.castSuccEmb = rootScope e := by
  aesop

theorem root_right_image :
    (Finset.univ.image Fin.castSuccEmb).image (onePointProj e) =
      rootScope e := by
  rw [Finset.image_image]
  aesop

theorem commute : e.trans Fin.castSuccEmb = Fin.castSuccEmb.trans (onePointProj e) := by
  aesop

theorem intersection : privateScope ∩ donorScope e = rootScope e := by
  rw [donorScope, univ_image_onePointProj]
  ext x
  aesop

theorem union : Finset.univ = privateScope ∪ donorScope e := by
  rw [donorScope, univ_image_onePointProj, ← Finset.union_assoc,
    Finset.union_eq_left.mpr (root_private e)]
  exact image_castSuccEmb_union_last.symm

theorem private_proper : privateScope (N := N) ≠ Finset.univ := by
  intro he
  exact fresh_private (he.symm ▸ Finset.mem_univ (Fin.last N))

theorem donor_proper (h : n + 1 < N) : donorScope e ≠ Finset.univ := by
  intro he
  have hc := donor_card e
  simp_all

section Plans
variable {a b c : ℕ} (D : SemScheme b) (Q : SemScheme a)
variable (f : Fin a ↪ Fin b) (g : Fin b ↪ Fin c)
variable (hf : Finset.univ.image f ∈ D.scheme.plan) (he : D.restrictFace f hf = Q)

include he in
/-- Plan equality is derived from literal semantic restriction. -/
theorem pushed_root_plan :
    Plan.restrictPlan (D.scheme.plan.image (Finset.image g)) (Finset.univ.image (f.trans g)) =
      Q.scheme.plan.image (Finset.image (f.trans g)) := by
  have hc : (Finset.univ.image f).image g = Finset.univ.image (f.trans g) := by
    rw [Finset.image_image]; rfl
  rw [← hc, restrictPlan_image, ← image_restrictFace_plan D.scheme f hf]
  have hp := congrArg (fun S => S.scheme.plan) he
  change ((D.restrictFace f hf).scheme.plan.image (Finset.image f)).image (Finset.image g) = _
  rw [Finset.image_image]
  congr 1
  aesop
end Plans

variable (P : SemScheme N) (D : SemScheme (n + 1)) (Q : SemScheme n)
variable (hp : Finset.univ.image e ∈ P.scheme.plan)
variable (hd : Finset.univ.image Fin.castSuccEmb ∈ D.scheme.plan)
variable (hpr : P.restrictFace e hp = Q) (hdr : D.restrictFace Fin.castSuccEmb hd = Q)

include hpr hdr in
theorem exists_plan : ∃ R,
    Plan.IsPlan Finset.univ R ∧ privateScope ∈ R ∧
    Plan.restrictPlan R privateScope = P.scheme.plan.image (Finset.image Fin.castSuccEmb) ∧
    donorScope e ∈ R ∧
    Plan.restrictPlan R (donorScope e) = D.scheme.plan.image (Finset.image (onePointProj e)) := by
  have hP := Plan.isPlan_image Fin.castSuccEmb P.scheme.isPlan
  have hroot :=
    Finset.mem_image.mpr ⟨_, hp, root_left_image e⟩
  have hD : Plan.IsPlan (rootScope e ∪ {Fin.last N})
      (D.scheme.plan.image (Finset.image (onePointProj e))) := by
    rw [← univ_image_onePointProj]
    exact Plan.isPlan_image _ D.scheme.isPlan
  have hrootD :=
    Finset.mem_image.mpr ⟨_, hd, root_right_image e⟩
  have heq : Plan.restrictPlan (D.scheme.plan.image (Finset.image (onePointProj e)))
      (rootScope e) =
      Plan.restrictPlan (P.scheme.plan.image (Finset.image Fin.castSuccEmb)) (rootScope e) := by
    rw [pushed_root_plan P Q e Fin.castSuccEmb hp hpr]
    simpa only [← commute e] using
      pushed_root_plan D Q Fin.castSuccEmb (onePointProj e) hd hdr
  obtain ⟨R, hr, hleft, hl, hright, hr'⟩ :=
    hP.attach_one_over_face hroot fresh_private hD hrootD heq
  rw [image_castSuccEmb_union_last] at hr
  rw [← univ_image_onePointProj] at hright hr'
  grind

def plan : Finset (Finset (Fin (N + 1))) := Classical.choose (exists_plan e P D Q hp hd hpr hdr)

theorem plan_spec : Plan.IsPlan Finset.univ (plan e P D Q hp hd hpr hdr) ∧
    privateScope ∈ plan e P D Q hp hd hpr hdr ∧
    Plan.restrictPlan (plan e P D Q hp hd hpr hdr) privateScope =
      P.scheme.plan.image (Finset.image Fin.castSuccEmb) ∧
    donorScope e ∈ plan e P D Q hp hd hpr hdr ∧
    Plan.restrictPlan (plan e P D Q hp hd hpr hdr) (donorScope e) =
      D.scheme.plan.image (Finset.image (onePointProj e)) :=
  Classical.choose_spec (exists_plan e P D Q hp hd hpr hdr)

/-- The ordered whole-input boundary with the requested literal placements. -/
def input : WholeDonorBoundary.Input Finset.univ privateScope (donorScope e)
    (plan e P D Q hp hd hpr hdr) n N (n + 1) where
  isPlan := (plan_spec e P D Q hp hd hpr hdr).1
  left := P
  right := D
  common := Q
  placeLeft := Fin.castSuccEmb
  placeRight := onePointProj e
  imageLeft := rfl
  imageRight := rfl
  commonLeft := e
  commonRight := Fin.castSuccEmb
  visibleLeft := hp
  visibleRight := hd
  faceLeft := hpr
  faceRight := hdr
  commute := commute e
  intersection := (root_left_image e).trans (intersection e).symm
  planLeft := (plan_spec e P D Q hp hd hpr hdr).2.2.1
  planRight := (plan_spec e P D Q hp hd hpr hdr).2.2.2.2

end
end VaughtConjecture.Knight.WholeDonorAttachment
