module
public import DedekindZetaZeroFree.Algebra.LinearAlgebra.FiniteEvaluationReconstruction

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.SphericalCoefficientSupport
public import DedekindZetaZeroFree.Metaplectic.Intertwining.CompactOrbits.FiniteDimensionality

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal.SphericalReseeding

namespace UniformCompactSeparation

 def pointEvaluation {X : Type*} (S : Submodule ℂ (X → ℂ)) (x : X) :
    Module.Dual ℂ S := (LinearMap.proj x).comp S.subtype

private theorem finite_evaluation_dual_span {X : Type*}
    (S : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ S] :
    ∃ (m : ℕ) (x : Fin m → X),
      Submodule.span ℂ (Set.range (fun i => pointEvaluation S (x i))) = ⊤ := by apply @DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.FiniteScalarEvaluation.FiniteEvaluationReconstruction.finite_evaluation_dual_span <;> assumption

alias finite_evaluation_reconstruction := DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.FiniteScalarEvaluation.finite_evaluation_reconstruction

private theorem finite_evaluation_interpolation {X : Type*}
    (S : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ S] :
    ∃ (m : ℕ) (x : Fin m → X) (B : Fin m → X → ℂ),
      ∀ (h : S) (y : X), h.val y = ∑ i, B i y * h.val (x i) := by
  obtain ⟨n, m, x, A, b, hb⟩ := finite_evaluation_reconstruction S
  refine ⟨m, x, fun i y => ∑ j, A j i * (b j).val y, ?_⟩
  intro h y
  rw [hb]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))

def actualCompactTranslateSpace : Submodule ℂ (KPContSectorArchSphericalFibers.KInfinity F → ℂ) :=
  Submodule.span ℂ (Set.range (fun p :
    KPGlobalTorusFunctionData.finitePart F ζ hζ × KPContSectorArchSphericalFibers.KInfinity F =>
    fun k : KPContSectorArchSphericalFibers.KInfinity F =>
      t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k * p.2).val * p.1.val)))

private alias insertion_commutes_finite := DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal.insertion_commutes_finite

theorem actualCompactTranslateSpace_finiteDimensional :
    FiniteDimensional ℂ (actualCompactTranslateSpace F ζ hζ t) := by
  let O := Submodule.span ℂ (Set.range (fun u : (KPContFlatSourceRecipe.D F ζ hζ).K =>
    fun g => t.val.val (g * u.val)))
  letI : FiniteDimensional ℂ O :=
    KPGlobalResidualKernel.ScatteringResidue.source_raw_compact_orbit_finiteDimensional_public t
  obtain ⟨m, x, B, hB⟩ := finite_evaluation_interpolation O
  let L : (Fin m → O) →ₗ[ℂ] (KPContSectorArchSphericalFibers.KInfinity F → ℂ) :=
    { toFun := fun q k => ∑ i, (q i).val
        (x i * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val)
      map_add' := by intros; ext k; simp [Finset.sum_add_distrib]
      map_smul' := by intros; ext k; simp [Finset.mul_sum] }
  have hle : actualCompactTranslateSpace F ζ hζ t ≤ L.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨c, u⟩, rfl⟩
    let tu : O := ⟨fun g => t.val.val
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ u.val),
      Submodule.subset_span ⟨⟨_,
        KPContinuation.ArchCompact.archimedeanInsertion_mem_iwasawaCompact F ζ hζ u⟩, rfl⟩⟩
    refine ⟨fun i => B i c.val • tu, ?_⟩
    funext k
    let v : O := ⟨fun g => t.val.val
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k * u).val),
      Submodule.subset_span ⟨⟨_,
        KPContinuation.ArchCompact.archimedeanInsertion_mem_iwasawaCompact F ζ hζ (k * u)⟩, rfl⟩⟩
    have hv := hB v c.val
    have hi := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1 k.val u.val
    have hc := insertion_commutes_finite F ζ hζ (k * u).val c
    change (∑ i, B i c.val * t.val.val
      ((x i * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val) *
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ u.val)) = _
    have he : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k * u).val =
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val *
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ u.val := hi
    change (∑ i, B i c.val * t.val.val
      ((x i * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val) *
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ u.val)) =
      t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k * u).val * c.val)
    rw [hc.eq]
    simpa only [v, he, mul_assoc] using hv.symm
  exact Submodule.finiteDimensional_of_le hle

theorem actualCompactTranslateSpace_right_invariant
    (h : actualCompactTranslateSpace F ζ hζ t)
    (u : KPContSectorArchSphericalFibers.KInfinity F) :
    (fun k => h.val (k * u)) ∈ actualCompactTranslateSpace F ζ hζ t := by
  refine Submodule.span_induction (p := fun f _ =>
    (fun k => f (k * u)) ∈ actualCompactTranslateSpace F ζ hζ t) ?_ ?_ ?_ ?_ h.property
  · rintro f ⟨⟨c, v⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨(c, u * v), ?_⟩
    funext k
    simp only [mul_assoc]
  · exact Submodule.zero_mem _
  · intro f g hf hg htf htg
    exact Submodule.add_mem _ htf htg
  · intro a f hf htf
    exact Submodule.smul_mem _ a htf

theorem actual_source_uniform_compact_evaluation_reconstruction :
    ∃ (n m : ℕ) (k : Fin m → KPContSectorArchSphericalFibers.KInfinity F)
      (A : Fin n → Fin m → ℂ)
      (b : Fin n → actualCompactTranslateSpace F ζ hζ t),
      ∀ (a : KPContSectorArchSphericalFibers.KInfinity F)
        (c : KPGlobalTorusFunctionData.finitePart F ζ hζ),
        t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a.val * c.val) =
          ∑ j, evalCoefficient F ζ hζ t k (A j) c * (b j).val a := by
  let S := actualCompactTranslateSpace F ζ hζ t
  letI : FiniteDimensional ℂ S := actualCompactTranslateSpace_finiteDimensional F ζ hζ t
  obtain ⟨n, m, k, A, b, hb⟩ := finite_evaluation_reconstruction S
  refine ⟨n, m, k, A, b, ?_⟩
  intro a c
  have hh : (fun a : KPContSectorArchSphericalFibers.KInfinity F => t.val.val
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a.val * c.val)) ∈ S := Submodule.subset_span ⟨(c, 1), by simp⟩
  exact hb ⟨_, hh⟩ a

end UniformCompactSeparation

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal.SphericalReseeding

end
