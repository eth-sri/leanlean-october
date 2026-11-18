/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReferenceContext

@[expose] public section

namespace VaughtConjecture.AmalgamationPlan.Plan

variable {α : Type*} [DecidableEq α]

private theorem restrict_restrict {P : Finset (Finset α)} {A B : Finset α}
    (hBA : B ⊆ A) : restrictPlan (restrictPlan P A) B = restrictPlan P B := by
  ext S
  simp only [restrictPlan, Finset.mem_inter, Finset.mem_powerset]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hBA⟩, h.2⟩⟩

private theorem restrict_self {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) : restrictPlan P A = P := by
  ext S
  simp only [restrictPlan, Finset.mem_inter, Finset.mem_powerset]
  exact ⟨And.left, fun h => ⟨h, hP.subset_of_mem h⟩⟩

private theorem coatom_over_face {A B : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) (hB : B ∈ P) (hne : B ≠ A) :
    ∃ a ∈ A, A.erase a ∈ P ∧ B ⊆ A.erase a := by
  cases hP with
  | empty =>
    exact (hne (Finset.mem_singleton.mp hB)).elim
  | singleton a =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | hB
    · exact ⟨a, by simp, by simp, Finset.empty_subset _⟩
    · exact (hne hB).elim
  | @step A a b Q R P ha hb hab hQ hR hmem hre hPeq =>
    subst P
    simp only [Finset.mem_union, Finset.mem_singleton] at hB
    rcases hB with (hB | hB) | hB
    · exact ⟨a, ha, by simp [hQ.domain_mem], hQ.subset_of_mem hB⟩
    · exact ⟨b, hb, by simp [hR.domain_mem], hR.subset_of_mem hB⟩
    · exact (hne hB).elim

private theorem restrict_glue_left {A B : Finset α} {P Q : Finset (Finset α)}
    (hP : IsPlan A P) (hQ : IsPlan B Q)
    (hres : restrictPlan P (A ∩ B) = restrictPlan Q (A ∩ B))
    {x : α} (hxB : x ∈ B) (hxA : x ∉ A) :
    restrictPlan (P ∪ Q ∪ {A ∪ B}) A = P := by
  ext S
  simp only [restrictPlan, Finset.mem_inter, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_powerset]
  constructor
  · rintro ⟨(hS | hS) | rfl, hSA⟩
    · exact hS
    · have hSAB : S ⊆ A ∩ B := by
        intro y hy
        exact Finset.mem_inter.mpr ⟨hSA hy, hQ.subset_of_mem hS hy⟩
      have hm : S ∈ restrictPlan Q (A ∩ B) :=
        Finset.mem_inter.mpr ⟨hS, Finset.mem_powerset.mpr hSAB⟩
      rw [← hres] at hm
      exact (Finset.mem_inter.mp hm).1
    · exact (hxA (hSA (Finset.mem_union_right _ hxB))).elim
  · intro hS
    exact ⟨Or.inl (Or.inl hS), hP.subset_of_mem hS⟩

private theorem attach_coatom {A : Finset α} {P Q : Finset (Finset α)}
    {a x : α} (hP : IsPlan A P) (ha : a ∈ A) (hx : x ∉ A)
    (hface : A.erase a ∈ P) (hQ : IsPlan (A.erase a ∪ {x}) Q)
    (hfaceQ : A.erase a ∈ Q)
    (hres : restrictPlan Q (A.erase a) = restrictPlan P (A.erase a)) :
    ∃ R, IsPlan (A ∪ {x}) R ∧ A ∈ R ∧ restrictPlan R A = P ∧
      A.erase a ∪ {x} ∈ R ∧ restrictPlan R (A.erase a ∪ {x}) = Q := by
  have hax : a ≠ x := fun h => hx (h ▸ ha)
  have hex : (A ∪ {x}).erase x = A := by
    rw [Finset.union_singleton, Finset.erase_insert hx]
  have hea : (A ∪ {x}).erase a = A.erase a ∪ {x} := by
    rw [Finset.union_singleton, Finset.erase_insert_of_ne hax.symm,
      Finset.union_singleton]
  have hi : A ∩ (A.erase a ∪ {x}) = A.erase a := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    aesop
  have hu : A ∪ (A.erase a ∪ {x}) = A ∪ {x} := by
    ext y
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    tauto
  have hare : a ∉ A.erase a ∪ {x} := by simp [hax]
  have hover : restrictPlan P (A ∩ (A.erase a ∪ {x})) =
      restrictPlan Q (A ∩ (A.erase a ∪ {x})) := by rw [hi, hres]
  refine ⟨P ∪ Q ∪ {A ∪ {x}}, ?_, by simp [hP.domain_mem], ?_,
    Finset.mem_union_left _ (Finset.mem_union_right _ hQ.domain_mem), ?_⟩
  · apply IsPlan.step (a := x) (b := a)
      (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      (Finset.mem_union_left _ ha) hax.symm
    · simpa only [hex] using hP
    · simpa only [hea] using hQ
    · simpa only [hex] using And.intro hface hfaceQ
    · change restrictPlan P (((A ∪ {x}).erase x).erase a) =
        restrictPlan Q (((A ∪ {x}).erase x).erase a)
      rw [hex, hres]
    · rfl
  · simpa only [hu] using restrict_glue_left hP hQ hover
      (Finset.mem_union_right _ (Finset.mem_singleton_self x)) hx
  · have hover' : restrictPlan Q ((A.erase a ∪ {x}) ∩ A) =
        restrictPlan P ((A.erase a ∪ {x}) ∩ A) := by
      rw [Finset.inter_comm]
      exact hover.symm
    simpa only [Finset.union_comm, hu] using
      restrict_glue_left hQ hP hover' ha hare

/-- Attach a prescribed one-point plan over any visible old face. Both the
old whole and the candidate face retain their plans literally. -/
theorem IsPlan.attach_one_over_face {A B : Finset α} {P Q : Finset (Finset α)}
    {x : α} (hP : IsPlan A P) (hB : B ∈ P) (hx : x ∉ A)
    (hQ : IsPlan (B ∪ {x}) Q) (hBQ : B ∈ Q)
    (hres : restrictPlan Q B = restrictPlan P B) :
    ∃ R, IsPlan (A ∪ {x}) R ∧ A ∈ R ∧ restrictPlan R A = P ∧
      B ∪ {x} ∈ R ∧ restrictPlan R (B ∪ {x}) = Q := by
  induction A using Finset.strongInductionOn generalizing B P Q with
  | _ A ih =>
    by_cases hBA : B = A
    · subst B
      exact ⟨Q, hQ, hBQ, hres.trans (restrict_self hP), hQ.domain_mem, restrict_self hQ⟩
    · obtain ⟨a, ha, hface, hBsub⟩ := coatom_over_face hP hB hBA
      have hBe : B ∈ restrictPlan P (A.erase a) :=
        Finset.mem_inter.mpr ⟨hB, Finset.mem_powerset.mpr hBsub⟩
      have hres' : restrictPlan Q B = restrictPlan (restrictPlan P (A.erase a)) B := by
        rw [restrict_restrict hBsub, hres]
      obtain ⟨E, hE, hAE, hEA, hBE, hEB⟩ := ih (A.erase a)
        (Finset.erase_ssubset ha) (restrict_isPlan hP hface) hBe
        (fun h => hx (Finset.mem_of_mem_erase h)) hQ hBQ hres'
      obtain ⟨R, hR, hAR, hRA, hER, hRE⟩ :=
        attach_coatom hP ha hx hface hE hAE hEA
      have hBEx : B ∪ {x} ⊆ A.erase a ∪ {x} :=
        Finset.union_subset_union hBsub (Finset.Subset.refl _)
      have hBR : B ∪ {x} ∈ R := by
        have hm : B ∪ {x} ∈ restrictPlan R (A.erase a ∪ {x}) := by
          rw [hRE]
          exact hBE
        exact (Finset.mem_inter.mp hm).1
      refine ⟨R, hR, hAR, hRA, hBR, ?_⟩
      calc restrictPlan R (B ∪ {x})
          = restrictPlan (restrictPlan R (A.erase a ∪ {x})) (B ∪ {x}) :=
            (restrict_restrict hBEx).symm
        _ = Q := by rw [hRE, hEB]

-- Non-vacuous regression at both ends of a three-point old domain. These
-- are separate extension plans, not simultaneous visibility claims.

-- Both inputs contribute two private points, not just one. The overlap
-- is the singleton {2}; each side retains its arbitrary prescribed plan.

end VaughtConjecture.AmalgamationPlan.Plan

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization AmalgamationPlan Value ExtOrd
open CellScheme.restrictFace (toCell)

universe w

/-! ## Exact below `β`, at least `β` above -/

section LabelSplit

variable {β : Ordinal.{0}}

end LabelSplit

/-! ## The required domain and visible face -/

section RequiredFace

variable {γ : Ordinal.{0}} {k m : ℕ}

/-- **The requested projection forces the domain**: a projection along `f` to `P` exists only if
the face `univ.image f` is visible in the domain and the domain (with its rows) restricts to
`P`'s domain there. -/
theorem face_of_typeMap_eq_some (f : Fin k ↪ Fin m) {q : S γ m} {P : S γ k}
    (h : typeMap f q = some P) :
    ∃ hv : Finset.univ.image f ∈ q.scheme.scheme.plan, q.scheme.restrictFace f hv = P.scheme := by
  have hv : Finset.univ.image f ∈ q.scheme.scheme.plan :=
    (typeMap_isSome_iff f q).mp (by rw [h]; rfl)
  refine ⟨hv, ?_⟩
  rw [typeMap_eq_some f q hv] at h
  exact congrArg StageType.scheme (Option.some_injective _ h)

/-- **Projected correctness, cellwise**: once the face is visible and the domains match,
`typeMap f q = some P` says exactly that every cell of the face reads `P`'s label at the
corresponding cell. -/
theorem typeMap_eq_some_iff_labels (f : Fin k ↪ Fin m) (q : S γ m) (P : S γ k)
    (hv : Finset.univ.image f ∈ q.scheme.scheme.plan)
    (hs : q.scheme.restrictFace f hv = P.scheme) :
    typeMap f q = some P ↔
      ∀ i : Cell (q.scheme.restrictFace f hv).scheme,
        q.label (toCell q.scheme.scheme f hv i) = P.label (SemScheme.castCell hs i) := by
  rw [typeMap_eq_some f q hv, Option.some_inj]
  constructor
  · rintro rfl i
    rfl
  · intro h
    obtain ⟨Ps, Pl, Pb, Pr⟩ := P
    dsimp only at hs h
    subst hs
    exact StageType.ext rfl (heq_of_eq (funext fun i => h i))

end RequiredFace

/-! ## The root part of every projection is the realized reduced root -/

section RootPart

variable {M : Type w} {α β : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} (C : ReferenceContext R t reqs) (hβ : β ≤ α)

end RootPart

/-! ## Geometry: the request face forces a pivot of the context's plan outside the root -/

section Geometry

variable {m : ℕ}

theorem image_castSuccEmb_univ :
    (Finset.univ : Finset (Fin m)).image Fin.castSuccEmb =
      (Finset.univ : Finset (Fin (m + 1))).erase (Fin.last m) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true,
    Fin.castSuccEmb_apply]
  exact Fin.exists_castSucc_eq

end Geometry

end VaughtConjecture.Knight

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization AmalgamationPlan Value ExtOrd

universe w

/-! ## Plans of faces -/

section PlanImage

/-- Restriction commutes with the image along an injection. -/
theorem restrictPlan_image {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (g : ι ↪ κ)
    (S : Finset (Finset ι)) (T : Finset ι) :
    Plan.restrictPlan (S.image (Finset.image g)) (T.image g) =
      (Plan.restrictPlan S T).image (Finset.image g) := by
  ext U
  simp only [Plan.restrictPlan, Finset.mem_inter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨⟨V, hV, rfl⟩, hsub⟩
    exact ⟨V, ⟨hV, (Finset.image_subset_image_iff g.injective).mp hsub⟩, rfl⟩
  · rintro ⟨V, ⟨hV, hVT⟩, rfl⟩
    exact ⟨⟨V, hV, rfl⟩, Finset.image_subset_image hVT⟩

variable {k m : ℕ}

/-- The image of a restricted scheme's plan is the restriction of the plan to the face. -/
theorem image_restrictFace_plan (D : CellScheme (ι := Fin m) Finset.univ) (f : Fin k ↪ Fin m)
    (hr : Finset.univ.image f ∈ D.plan) :
    (D.restrictFace f hr).plan.image (Finset.image f) =
      Plan.restrictPlan D.plan (Finset.univ.image f) := by
  ext S
  simp only [Finset.mem_image, CellScheme.mem_restrictFace_plan D f hr, Plan.restrictPlan,
    Finset.mem_inter, Finset.mem_powerset]
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact ⟨hT, Finset.image_subset_image (Finset.subset_univ T)⟩
  · rintro ⟨hS, hsub⟩
    obtain ⟨T, -, rfl⟩ := Finset.subset_image_iff.mp hsub
    exact ⟨T, hS, rfl⟩

theorem univ_image_onePointProj (e : Fin k ↪ Fin m) :
    (Finset.univ : Finset (Fin (k + 1))).image (onePointProj e) =
      Finset.univ.image (e.trans Fin.castSuccEmb) ∪ {Fin.last m} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last => exact Or.inr (onePointProj_last e)
    | cast i => exact Or.inl ⟨i, (onePointProj_castSucc e i).symm⟩
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨Fin.castSucc i, onePointProj_castSucc e i⟩
    · exact ⟨Fin.last k, onePointProj_last e⟩

theorem image_castSuccEmb_union_last :
    (Finset.univ : Finset (Fin m)).image Fin.castSuccEmb ∪ {Fin.last m} = Finset.univ := by
  rw [image_castSuccEmb_univ, Finset.union_comm, ← Finset.insert_eq,
    Finset.insert_erase (Finset.mem_univ _)]

end PlanImage

/-! ## The common plan over the actual context -/

section Attach

variable {M : Type w} {α β : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} (C : ReferenceContext R t reqs) (hβ : β ≤ α)


end Attach

end VaughtConjecture.Knight
