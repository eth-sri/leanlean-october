/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.Probability.IdentDistrib

public section

open MeasureTheory ProbabilityTheory Set

namespace DOZZ.Proofs

section
variable {ι κ : Type*} {α : ι → Type*} {β : κ → Type*}
  [∀ i, MeasurableSpace (α i)] [∀ j, MeasurableSpace (β j)]

private theorem countablySpanning_cylinders : IsCountablySpanning (measurableCylinders α) :=
  ⟨fun _ => univ, fun _ => univ_mem_measurableCylinders α, by ext x; simp⟩

/-- A finite measure on a pair of coordinate spaces is determined by its cylinder rectangles. -/
theorem measure_eq_of_cylinder_rectangles
    (μ ν : Measure ((∀ i, α i) × (∀ j, β j))) [IsFiniteMeasure μ]
    (hrect : ∀ s ∈ measurableCylinders α, ∀ t ∈ measurableCylinders β,
      μ (s ×ˢ t) = ν (s ×ˢ t)) (huniv : μ univ = ν univ) : μ = ν := by
  refine ext_of_generate_finite _ (generateFrom_eq_prod generateFrom_measurableCylinders
    generateFrom_measurableCylinders countablySpanning_cylinders countablySpanning_cylinders).symm
    (isPiSystem_measurableCylinders.prod isPiSystem_measurableCylinders) ?_ huniv
  rintro _ ⟨s, hs, t, ht, rfl⟩
  exact hrect s hs t ht

/-- Finite measures on a coordinate space are determined by their finite-dimensional marginals. -/
theorem measure_eq_of_finite_coordinate_map_eq (μ ν : Measure (∀ i, α i)) [IsFiniteMeasure μ]
    (h : ∀ s : Finset ι, μ.map s.restrict = ν.map s.restrict) : μ = ν :=
  IsProjectiveLimit.unique (P := fun s => μ.map s.restrict) (fun _ => rfl) (fun s => (h s).symm)

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P]

/-- For random vectors, equality of the finite-dimensional pushforwards implies equality in law. -/
theorem identDistrib_of_pi_fdd {f : Ω → ∀ i, α i} {g : Ω' → ∀ i, α i}
    (hf : AEMeasurable f P) (hg : AEMeasurable g P')
    (h : ∀ s : Finset ι, P.map (s.restrict ∘ f) = P'.map (s.restrict ∘ g)) : IdentDistrib f g P P' := by
  refine ⟨hf, hg, measure_eq_of_finite_coordinate_map_eq _ _ fun s => ?_⟩
  have hm : Measurable (s.restrict : (∀ i, α i) → (∀ i : s, α i)) :=
    .of_eval fun i => measurable_pi_apply i.1
  rw [AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hf,
    AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hg]
  exact h s

/-- Joint equality in law is determined by joint finite-coordinate restrictions. -/
theorem identDistrib_of_prod_pi_fdd
    {f : Ω → (∀ i, α i) × (∀ j, β j)} {g : Ω' → (∀ i, α i) × (∀ j, β j)}
    (hf : AEMeasurable f P) (hg : AEMeasurable g P')
    (h : ∀ (s : Finset ι) (t : Finset κ),
      P.map (Prod.map s.restrict t.restrict ∘ f) = P'.map (Prod.map s.restrict t.restrict ∘ g)) :
    IdentDistrib f g P P' := by
  have hrect (S) (hS : S ∈ measurableCylinders α) (T) (hT : T ∈ measurableCylinders β) :
      P.map f (S ×ˢ T) = P'.map g (S ×ˢ T) := by
    obtain ⟨s, A, hA, rfl⟩ := (mem_measurableCylinders S).mp hS
    obtain ⟨t, B, hB, rfl⟩ := (mem_measurableCylinders T).mp hT
    have hm : Measurable (Prod.map s.restrict t.restrict :
        ((∀ i, α i) × (∀ j, β j)) → ((∀ i : s, α i) × (∀ j : t, β j))) :=
      (Measurable.of_eval fun i => measurable_pi_apply i.1).prodMap
        (Measurable.of_eval fun j => measurable_pi_apply j.1)
    rw [Measure.map_apply_of_aemeasurable hf ((hA.cylinder s).prod (hB.cylinder t)),
      Measure.map_apply_of_aemeasurable hg ((hA.cylinder s).prod (hB.cylinder t))]
    exact (IdentDistrib.mk (hm.comp_aemeasurable hf) (hm.comp_aemeasurable hg)
      (h s t)).measure_mem_eq (hA.prod hB)
  exact ⟨hf, hg, measure_eq_of_cylinder_rectangles _ _ hrect (by
    simpa using hrect univ (univ_mem_measurableCylinders α) univ (univ_mem_measurableCylinders β))⟩

end

/-- A code that generates the target σ-algebra reflects equality in law. -/
theorem identDistrib_of_code {Ω Ω' α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    {P : Measure Ω} {P' : Measure Ω'} {f : Ω → α} {g : Ω' → α}
    (hf : AEMeasurable f P) (hg : AEMeasurable g P')
    {code : α → β} (hc : mβ.comap code = mα) (h : IdentDistrib (code ∘ f) (code ∘ g) P P') :
    IdentDistrib f g P P' := by
  refine ⟨hf, hg, Measure.ext fun s hs => ?_⟩
  rw [← hc] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have hs : MeasurableSet (code ⁻¹' t) := hc ▸ ⟨t, ht, rfl⟩
  rw [Measure.map_apply_of_aemeasurable hf hs, Measure.map_apply_of_aemeasurable hg hs]
  exact h.measure_mem_eq ht

/-- Two coded variables have the same joint law if their codes generate the σ-algebras
and all joint finite marginals agree. -/
theorem identDistrib_prod_of_coded_fdd {Ω Ω' A B ι κ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    {α : ι → Type*} {β : κ → Type*} [∀ i, MeasurableSpace (α i)] [∀ j, MeasurableSpace (β j)]
    {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P]
    {f : Ω → A × B} {g : Ω' → A × B} (hf : AEMeasurable f P) (hg : AEMeasurable g P')
    {C : A → ∀ i, α i} {D : B → ∀ j, β j}
    (hC : MeasurableSpace.pi.comap C = mA) (hD : MeasurableSpace.pi.comap D = mB)
    (h : ∀ (s : Finset ι) (t : Finset κ),
      P.map (Prod.map s.restrict t.restrict ∘ Prod.map C D ∘ f) =
        P'.map (Prod.map s.restrict t.restrict ∘ Prod.map C D ∘ g)) : IdentDistrib f g P P' := by
  have hc : (MeasurableSpace.pi.prod MeasurableSpace.pi).comap (Prod.map C D) = mA.prod mB := by
    rw [MeasurableSpace.comap_prodMap, hC, hD]
  have hm : Measurable (Prod.map C D) := Measurable.of_comap_le hc.le
  exact identDistrib_of_code hf hg hc
    (identDistrib_of_prod_pi_fdd (hm.comp_aemeasurable hf) (hm.comp_aemeasurable hg) h)

end DOZZ.Proofs
