module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.PrincipalSeries.AdjacentHarmonicPropagation

@[expose] public section

section

noncomputable section
open scoped NumberField Classical TensorProduct
open DedekindZetaZeroFree DedekindZetaZeroFree.KPGlobalResidualConstruction
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCSource

def algebra (B : Fin 6 → Module.End ℂ complexCore) :
    Subalgebra ℂ (Module.End ℂ complexCore) :=
  Algebra.adjoin ℂ {T | (∃ k, T = complexCoreCompactLinearMap k) ∨
    (∃ i, T = B i)}
instance (B : Fin 6 → Module.End ℂ complexCore) : Module (algebra B) complexCore :=
  Module.compHom _ (algebra B).val.toRingHom

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCSource

end

end

section

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCAlgebraic
open NativeComplexHCSource

variable (B : Fin 6 → Module.End ℂ complexCore)

 theorem compact_mem_algebra (k : KPCplxCharacterHaar.ComplexSU2) :
    complexCoreCompactLinearMap k ∈ algebra B :=
  Algebra.subset_adjoin (Or.inl ⟨k, rfl⟩)

 theorem derivative_mem_algebra (i : Fin 6) : B i ∈ algebra B :=
  Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)

def underlying (N : Submodule (algebra B) complexCore) : Submodule ℂ complexCore where
  carrier := N
  zero_mem' := N.zero_mem
  add_mem' := N.add_mem
  smul_mem' := by
    intro c f hf
    have h := N.smul_mem (algebraMap ℂ (algebra B) c) hf
    exact h

 theorem underlying_compact_invariant (N : Submodule (algebra B) complexCore) :
    ∀ k f, f ∈ underlying B N → complexCoreCompactLinearMap k f ∈ underlying B N := by
  intro k f hf
  exact N.smul_mem ⟨_, compact_mem_algebra B k⟩ hf

 theorem underlying_derivative_invariant (N : Submodule (algebra B) complexCore) :
    ∀ i f, f ∈ underlying B N → B i f ∈ underlying B N := by
  intro i f hf
  exact N.smul_mem ⟨_, derivative_mem_algebra B i⟩ hf

def endomorphismComplex (T : Module.End (algebra B) complexCore) :
    Module.End ℂ complexCore where
  toFun := T
  map_add' := T.map_add
  map_smul' := by
    intro c f
    exact T.map_smul (algebraMap ℂ (algebra B) c) f

 theorem endomorphism_compact_commutes (T : Module.End (algebra B) complexCore)
    (k : KPCplxCharacterHaar.ComplexSU2) (f : complexCore) :
    endomorphismComplex B T (complexCoreCompactLinearMap k f) =
      complexCoreCompactLinearMap k (endomorphismComplex B T f) :=
  T.map_smul ⟨_, compact_mem_algebra B k⟩ f

 theorem endomorphism_scalar_on_lowest (T : Module.End (algebra B) complexCore) :
    ∃ c : ℂ, ∀ f ∈ coreHarmonic 0, T f = c • f :=
  commutant_scalar_on_lowest (endomorphismComplex B T)
    (endomorphism_compact_commutes B T)

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCAlgebraic

end

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCAlgebraic
open NativeComplexHCSource

 theorem endomorphism_scalar_of_simple (B : Fin 6 → Module.End ℂ complexCore)
    (hsimple : IsSimpleOrder (Submodule (algebra B) complexCore))
    (T : Module.End (algebra B) complexCore) : ∃ c : ℂ, ∀ f, T f = c • f := by
  letI := hsimple
  obtain ⟨c, hc⟩ := endomorphism_scalar_on_lowest B T
  have hdim : 0 < Module.finrank ℂ (coreHarmonic 0) := by rw [coreHarmonic_finrank]; norm_num
  haveI : Nontrivial (coreHarmonic 0) := Module.nontrivial_of_finrank_pos hdim
  obtain ⟨v, hv⟩ := exists_ne (0 : coreHarmonic 0)
  let N : Submodule (algebra B) complexCore :=
    { carrier := {f | T f = c • f}
      zero_mem' := by simp
      add_mem' := by
        intro f g hf hg
        change T (f + g) = c • (f + g)
        rw [map_add, hf, hg, smul_add]
      smul_mem' := by
        intro a f hf
        change T (a.val f) = c • a.val f
        change T (a • f) = c • a.val f
        rw [T.map_smul a f]
        change a.val (T f) = c • a.val f
        rw [hf, a.val.map_smul] }
  have hvN : v.val ∈ N := hc v.val v.property
  have hN : N ≠ ⊥ := by
    intro hN
    have hz : v.val = 0 := by simpa only [hN, Submodule.mem_bot] using hvN
    exact hv (Subtype.ext hz)
  have htop : N = ⊤ := (eq_bot_or_eq_top N).resolve_left hN
  exact ⟨c, fun f => show f ∈ N from htop ▸ Submodule.mem_top⟩

open scoped Classical BigOperators Matrix
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPCplxIntertwinerEigenvalues
open NativeComplexHCOperators

private theorem basis_expansion (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : Matrix.trace X = 0) :
    X = ∑ i : Fin 6, (KPSmoothActualFlowData.matrixCoordinates X i : ℝ) •
      KPSmoothActualFlowData.basisMatrix i := by
  have h := PGLComplex.sl2Matrix_matrixCoordinates X hX
  calc
    X = KPSmoothActualFlowData.sl2Matrix (KPSmoothActualFlowData.matrixCoordinates X) := h.symm
    _ = _ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [KPSmoothActualFlowData.sl2Matrix, KPSmoothActualFlowData.matrixCoordinates,
          KPSmoothActualFlowData.basisMatrix, Fin.sum_univ_six, Complex.real_smul]
      all_goals apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

 theorem ambient_submodule_lie_stable
    (N : Submodule (algebra NativeComplexHCOperators.operators) complexCore)
    (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : Matrix.trace X = 0)
    (f : PrincipalSeries negativeParameter)
    (hf : f ∈ (underlying NativeComplexHCOperators.operators N).map complexCore.subtype) :
    derivative negativeParameter X f ∈
      (underlying NativeComplexHCOperators.operators N).map complexCore.subtype := by
  obtain ⟨v, hv, rfl⟩ := hf
  change direction negativeParameter v.val X ∈ _
  rw [basis_expansion X hX, map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_smul, ← algebraMap_smul ℂ (KPSmoothActualFlowData.matrixCoordinates X i)]
  apply Submodule.smul_mem
  refine ⟨NativeComplexHCOperators.operators i v,
    underlying_derivative_invariant NativeComplexHCOperators.operators N i v hv, ?_⟩
  rfl

 theorem ambient_submodule_compact_stable
    (N : Submodule (algebra NativeComplexHCOperators.operators) complexCore) :
    IsKInvariant negativeParameter
      ((underlying NativeComplexHCOperators.operators N).map complexCore.subtype) := by
  intro k f hf
  obtain ⟨l, hl⟩ := k.property
  obtain ⟨v, hv, rfl⟩ := hf
  refine ⟨complexCoreCompactLinearMap l v,
    underlying_compact_invariant NativeComplexHCOperators.operators N l v hv, ?_⟩
  change KPCplxPrincipalSeriesCharts.pi negativeParameter
    (Matrix.ProjGenLinGroup.mk (complexSU2Embedding l)) v.val = _
  change Matrix.ProjGenLinGroup.mk (complexSU2Embedding l) = (k : ComplexPGL2) at hl
  rw [hl]
  rfl

 theorem native_operators_simple :
    IsSimpleOrder (Submodule (algebra NativeComplexHCOperators.operators) complexCore) := by
  haveI : Nontrivial complexCore := by
    have hdim : 0 < Module.finrank ℂ (coreHarmonic 0) := by rw [coreHarmonic_finrank]; norm_num
    haveI : Nontrivial (coreHarmonic 0) := Module.nontrivial_of_finrank_pos hdim
    exact (coreHarmonic 0).subtype_injective.nontrivial
  apply (isSimpleOrder_iff _).mpr
  refine ⟨(Submodule.nontrivial_iff _).mpr inferInstance, fun N => ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨v, hv, hvne⟩ := N.ne_bot_iff.mp hN
  let U := (underlying NativeComplexHCOperators.operators N).map complexCore.subtype
  have hall := NativeComplexHCPropagation.all_harmonics_of_nonzero negativeParameter
    NativeComplexHCPropagation.negative_coefficients_nonzero.1
    NativeComplexHCPropagation.negative_coefficients_nonzero.2 U
    (ambient_submodule_compact_stable N) (ambient_submodule_lie_stable N)
    v.val ⟨v, hv, rfl⟩ v.property.2 (by intro h; exact hvne (Subtype.ext h))
  apply Submodule.eq_top_iff'.mpr
  intro f
  obtain ⟨x, hx, hxf⟩ := hall f.property.2
  have hxf' : x = f := Subtype.ext hxf
  rwa [hxf'] at hx

 theorem native_operators_scalar
    (T : Module.End (algebra NativeComplexHCOperators.operators) complexCore) :
    ∃ c : ℂ, ∀ f, T f = c • f :=
  endomorphism_scalar_of_simple NativeComplexHCOperators.operators native_operators_simple T

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCAlgebraic

end

end
