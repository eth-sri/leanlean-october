/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.AmalgamationPlan.Plan

/-! # One-point attachment along a prescribed visible face

The old plan and a candidate one-point extension of one of its visible faces
can be retained simultaneously. The induction follows a coatom containing
the requested face; it need not use the fixed branch chosen by
`isPlan_extend_one`.

This is a statement about support geometry only. It constructs no semantic
rows and does not assert amalgamation of prescribed respecting labellings.
-/

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
