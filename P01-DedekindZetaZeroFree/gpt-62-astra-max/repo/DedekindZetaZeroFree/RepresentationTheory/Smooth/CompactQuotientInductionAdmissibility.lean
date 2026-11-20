module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.EquivariantSmoothSections

@[expose] public section

namespace DedekindZetaZeroFree

open scoped Topology NNReal

section CompactQuotient

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup E] [Module ℂ E]
    (H : Subgroup G) (τ : Representation ℂ H E) (d : H →* (ℝ≥0)ˣ)

variable (hH : IsClosed (H : Set G)) (hquotient : IsCompact (Set.univ : Set (SectionCosetSpace H)))
    (J : OpenSubgroup G)

include hH hquotient in
theorem section_doubleCoset_finite_of_compact_quotient :
    Finite (DoubleCoset.Quotient (H : Set G) (J : Set G)) := by
  classical
  let q := Quotient.mk (QuotientGroup.rightRel H)
  let O := fun g => q '' ((fun u => g * u) '' J)
  have hcover : Set.univ ⊆ ⋃ g, O g := by
    intro x _
    obtain ⟨g, rfl⟩ := Quotient.mk_surjective x
    exact Set.mem_iUnion.mpr ⟨g, ⟨g, ⟨1, J.one_mem, mul_one g⟩, rfl⟩⟩
  obtain ⟨s, hs⟩ := hquotient.elim_finite_subcover O (fun g =>
    isOpenMap_quotient_mk'_mul _ (isOpenMap_mul_left g _ J.isOpen)) hcover
  apply Finite.of_surjective (fun a : s => DoubleCoset.mk H J a.val)
  intro x
  let g := x.out
  obtain ⟨a, ha, y, ⟨u, hu, rfl⟩, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ (q g)))
  refine ⟨⟨a, ha⟩, ?_⟩
  rw [← DoubleCoset.out_eq' x, DoubleCoset.eq]
  exact ⟨g * (a * u)⁻¹, (QuotientGroup.rightRel_apply.mp (Quotient.exact hx)), u, hu, by simp [g, mul_assoc]⟩

include hH hquotient in
theorem section_finite_doubleCoset_representatives :
    ∃ (n : ℕ) (r : Fin n → G),
      Function.Bijective (fun i => DoubleCoset.mk H (J : Subgroup G) (r i)) := by
  let Quotient₀ := DoubleCoset.Quotient (H : Set G) (J : Set G)
  classical
  letI := section_doubleCoset_finite_of_compact_quotient H hH hquotient J
  letI := Fintype.ofFinite (Quotient₀)
  let e := (Fintype.equivFin (Quotient₀)).symm
  refine ⟨Fintype.card (Quotient₀),
    fun i => (e i).out, ?_⟩
  simpa only [DoubleCoset.out_eq'] using e.bijective

end CompactQuotient

section Evaluation

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup E] [Module ℂ E]
    (H : Subgroup G) (τ : Representation ℂ H E) (d : H →* (ℝ≥0)ˣ)

variable {ι : Type*} (J : Subgroup G) (r : ι → G)

def smoothIndFixedEvaluation :
    fixedSubmodule (V := SmoothInd H τ d) (smoothIndRepresentation H τ d) J →ₗ[ℂ] (ι → E) where
  toFun f i := f.val.val.val (r i)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem smoothIndFixedEvaluation_apply
    (f : fixedSubmodule (V := SmoothInd H τ d) (smoothIndRepresentation H τ d) J) (i : ι) :
    smoothIndFixedEvaluation H τ d J r f i = f.val.val.val (r i) := rfl

theorem smoothIndFixedEvaluation_injective
    (hr : Function.Surjective (fun i => DoubleCoset.mk H J (r i))) :
    Function.Injective (smoothIndFixedEvaluation H τ d J r) := by
  intro x y hxy
  have hfix (z : fixedSubmodule (V := SmoothInd H τ d)
      (smoothIndRepresentation H τ d) J) (a j : G) (hj : j ∈ J) :
      z.val.val.val (a * j) = z.val.val.val a := by
    exact congrArg (fun t => t.val.val a) (z.property ⟨j, hj⟩)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  obtain ⟨i, hi⟩ := hr (DoubleCoset.mk H J g)
  obtain ⟨a, ha, j, hj, hg⟩ := DoubleCoset.eq.mp hi
  let aH : H := ⟨a, ha⟩
  rw [hg, mul_assoc, x.val.val.property aH, y.val.val.property aH]
  congr 1
  calc
    _ = x.val.val.val (r i) := hfix x (r i) j hj
    _ = y.val.val.val (r i) := congrFun hxy i
    _ = y.val.val.val (r i * j) := (hfix y (r i) j hj).symm

end Evaluation

section Admissibility

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup E] [Module ℂ E]
    (H : Subgroup G) (τ : Representation ℂ H E) (d : H →* (ℝ≥0)ˣ)

variable [Module.Finite ℂ E] (hH : IsClosed (H : Set G))
    (hquotient : IsCompact (Set.univ : Set (SectionCosetSpace H)))

include hH hquotient in
theorem smoothInd_open_fixed_finite_of_compact_quotient
    (J : OpenSubgroup G) :
    Module.Finite ℂ
      (fixedSubmodule (V := SmoothInd H τ d) (smoothIndRepresentation H τ d) (J : Subgroup G)) := by
  obtain ⟨n, r, hr⟩ := section_finite_doubleCoset_representatives H hH hquotient J
  exact Module.Finite.of_injective (smoothIndFixedEvaluation H τ d J r)
    (smoothIndFixedEvaluation_injective H τ d J r hr.2)

include hH hquotient in
theorem smoothInd_admissible_of_compact_quotient :
    Admissible (G := G) (V := SmoothInd H τ d) (smoothIndRepresentation H τ d) := fun J => smoothInd_open_fixed_finite_of_compact_quotient H τ d hH hquotient J.toOpenSubgroup

end Admissibility

end DedekindZetaZeroFree
