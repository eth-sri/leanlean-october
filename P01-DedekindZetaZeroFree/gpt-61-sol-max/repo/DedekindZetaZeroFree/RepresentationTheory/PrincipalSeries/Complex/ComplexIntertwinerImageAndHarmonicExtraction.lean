module

public import Mathlib

public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.FractionalIntegrals.InverseBounds
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicPropagationAndOrbitDifferentiation

@[expose] public section


section

namespace DedekindZetaZeroFree.KPCplxActualImageProof

open scoped NNReal

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped NNReal

private alias chart_topology := _root_.DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts.topology_withSeminorms

theorem standardIntertwiner_isInducing_of_chart_bounds (β : ℂˣ)
    (hbound : ∀ n : ℕ, ∃ (orders : Finset ℕ) (C : ℝ≥0),
      chartSeminorm positiveParameter n ≤
        (C • orders.sup (chartSeminorm negativeParameter)).comp
          (standardIntertwiner β).toLinearMap) :
    Topology.IsInducing (standardIntertwiner β) := by
  have hp : WithSeminorms (chartSeminorm positiveParameter) := chart_topology _
  have hq : WithSeminorms (chartSeminorm negativeParameter) := chart_topology _
  let f := (standardIntertwiner β).toLinearMap
  let t  :=
    TopologicalSpace.induced f inferInstance
  have ht : WithSeminorms (topology := t)
      (SeminormFamily.comp (chartSeminorm negativeParameter) f) :=
    f.withSeminorms_induced hq
  have hcont : @Continuous _ _ t (principalSeriesTopology positiveParameter)
      (LinearMap.id : PrincipalSeries positiveParameter →ₗ[ℂ]
        PrincipalSeries positiveParameter) := by
    apply WithSeminorms.continuous_of_isBounded ht hp
    intro n
    obtain ⟨orders, C, hC⟩ := hbound n
    refine ⟨orders, C, ?_⟩
    simpa only [Seminorm.comp_id, Seminorm.smul_comp,
      SeminormFamily.finset_sup_comp] using hC
  letI  :=
    principalSeriesTopology positiveParameter
  have heq : principalSeriesTopology positiveParameter = t := by
    apply le_antisymm
    · exact (standardIntertwiner β).continuous.le_induced
    · exact continuous_id_iff_le.mp hcont
  exact ⟨heq⟩

theorem chartSeminorm_dominated_by_image (β : ℂˣ) (n : ℕ) :
    ∃ s : Finset ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      chartSeminorm positiveParameter n ≤
        (C • s.sup (chartSeminorm negativeParameter)).comp
          (standardIntertwiner β).toLinearMap := by
  obtain ⟨orders, C, hC, hb⟩ := ComplexFractionalInverse.actual_chart_inverse_bound β n
  exact ⟨orders, C, hC, hb⟩

theorem standardIntertwiner_isInducing (β : ℂˣ) :
    Topology.IsInducing (standardIntertwiner β) := by
  apply standardIntertwiner_isInducing_of_chart_bounds β
  intro n
  obtain ⟨orders, C, _, hC⟩ := chartSeminorm_dominated_by_image β n
  exact ⟨orders, C, hC⟩

end DedekindZetaZeroFree.KPCplxActualImageProof

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction

open scoped BigOperators

theorem nonzero_term_of_partial_sums_tendsto {E : Type*}
    [AddCommMonoid E] [TopologicalSpace E] [T2Space E]
    (a : ℕ → E) (f : E) (hne : f ≠ 0)
    (hlim : Filter.Tendsto (fun N => ∑ ℓ ∈ Finset.range N, a ℓ)
      Filter.atTop (nhds f)) :
    ∃ ℓ : ℕ, a ℓ ≠ 0 := by
  by_contra h
  push Not at h
  have hzero : (fun N => ∑ ℓ ∈ Finset.range N, a ℓ) = fun _ => (0 : E) := by
    funext N
    exact Finset.sum_eq_zero fun ℓ _ => h ℓ
  rw [hzero] at hlim
  have h0  := tendsto_nhds_unique tendsto_const_nhds hlim
  exact hne h0.symm

end DedekindZetaZeroFree.KPCplxHarmonicExtraction

end

section

namespace DedekindZetaZeroFree.KPCplxActualImageProof

open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues

theorem extraction_invariant_inf (s : ℝ)
    (U V : Submodule ℂ (PrincipalSeries s))
    (hU : IsKInvariant s U) (hV : IsKInvariant s V) :
    IsKInvariant s (U ⊓ V) := by
  intro k f hf
  exact ⟨hU k f hf.1, hV k f hf.2⟩

section
variable (s : ℝ)
    (U : Submodule ℂ (PrincipalSeries s)) (hinv : IsKInvariant s U)
include s U hinv
theorem extraction_harmonic_le_of_inf_ne_bot  
    (ℓ : ℕ) (hne : U ⊓ harmonicKType s ℓ ≠ ⊥) :
    harmonicKType s ℓ ≤ U := by
  have htype := harmonicKType_multiplicity_one s ℓ
  have hinter := extraction_invariant_inf s U (harmonicKType s ℓ) hinv htype.1
  have heq := (htype.2.2.1 (U ⊓ harmonicKType s ℓ) inf_le_right hinter).resolve_left hne
  rw [← heq]
  exact inf_le_left

theorem extraction_compact_orbit_span_le  
    (f : PrincipalSeries s) (hf : f ∈ U) :
    Submodule.span ℂ (Set.range (fun k : compactSubgroup => pi s k f)) ≤ U := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  apply hinv <;> assumption
end


section
variable (s : ℝ)
    (U : Submodule ℂ (PrincipalSeries s))
    (hclosed : IsClosed (U : Set (PrincipalSeries s)))
    (hinv : IsKInvariant s U)
include s U hclosed hinv
def extraction_closed_compact_orbit_closure_mem   (f : PrincipalSeries s) (hf : f ∈ U)
    (v : PrincipalSeries s)
    (hv : v ∈ closure ((Submodule.span ℂ
      (Set.range (fun k : compactSubgroup => pi s k f)))))  := (closure_minimal (extraction_compact_orbit_span_le s U hinv f hf) hclosed) hv

theorem extraction_harmonic_le_of_orbit_closure   (f : PrincipalSeries s) (hf : f ∈ U)
    (ℓ : ℕ) (v : PrincipalSeries s) (hne : v ≠ 0)
    (hvtype : v ∈ harmonicKType s ℓ)
    (hvorbit : v ∈ closure ((Submodule.span ℂ
      (Set.range (fun k : compactSubgroup => pi s k f))))) :
    harmonicKType s ℓ ≤ U := by
  apply extraction_harmonic_le_of_inf_ne_bot s U hinv ℓ
  intro heq
  have hvU := extraction_closed_compact_orbit_closure_mem s U hclosed hinv f hf v hvorbit
  have hvmem : v ∈ U ⊓ harmonicKType s ℓ := ⟨hvU, hvtype⟩
  rw [heq] at hvmem
  apply hne <;> assumption

theorem closed_invariant_harmonic_extraction   (hne : U ≠ ⊥) :
    ∃ ℓ : ℕ, harmonicKType s ℓ ≤ U := by
  letI  := principalSeries_t2 s
  obtain ⟨f, hfU, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨μ, hhaar, hprob⟩ :=
    KPCplxHarmonicExtraction.exists_su2_probability_haar
  obtain ⟨a, hint, havg, htype, hlim⟩ :=
    KPCplxHarmonicExtraction.character_average_harmonic_expansion s μ hhaar hprob f
  obtain ⟨ℓ, hneℓ⟩ :=
    KPCplxHarmonicExtraction.nonzero_term_of_partial_sums_tendsto a f hf hlim
  refine ⟨ℓ, extraction_harmonic_le_of_orbit_closure s U hclosed hinv
    f hfU ℓ (a ℓ) hneℓ (htype ℓ) ?_⟩
  exact KPCplxHarmonicExtraction.character_average_mem_orbit_closure
    s μ hhaar hprob ℓ f (a ℓ) (hint ℓ) (havg ℓ)
end


end DedekindZetaZeroFree.KPCplxActualImageProof

end

section

namespace DedekindZetaZeroFree.KPCplxActualImageProof

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues

private theorem eq_bot_of_closed_invariant_ne_top
    (U : Submodule ℂ (PrincipalSeries positiveParameter))
    (hclosed : IsClosed (U : Set (PrincipalSeries positiveParameter)))
    (hinv : ∀ (g : ComplexPGL2) (f : PrincipalSeries positiveParameter),
      f ∈ U → pi positiveParameter g f ∈ U)
    (hne : U ≠ ⊤) : U = ⊥ := by
  by_cases hbot : U = ⊥
  · exact hbot
  · obtain ⟨ℓ, hℓ⟩ :=
      closed_invariant_harmonic_extraction positiveParameter U hclosed
        (fun k f hf => hinv k f hf) hbot
    exact absurd (closed_harmonic_exhaustion positiveParameter U hclosed
      (exceptional_harmonic_propagation positiveParameter (Or.inl rfl) U hclosed hinv ℓ hℓ)) hne

theorem standardIntertwiner_injective (β : ℂˣ) :
    Function.Injective (standardIntertwiner β) := by
  let U := (standardIntertwiner β).toLinearMap.ker
  have hclosed : IsClosed (U : Set (PrincipalSeries positiveParameter)) := by
    letI := principalSeries_t2 negativeParameter
    exact (standardIntertwiner β).isClosed_ker
  have hinv : ∀ (g : ComplexPGL2) (f : PrincipalSeries positiveParameter),
      f ∈ U → pi positiveParameter g f ∈ U := by
    intro g f hf
    change standardIntertwiner β (pi positiveParameter g f) = 0
    rw [standardIntertwiner_equivariant]
    change standardIntertwiner β f = 0 at hf
    rw [hf]
    induction g using Quotient.inductionOn with
    | _ g =>
      change rightTranslate negativeParameter g 0 = 0
      apply Subtype.ext
      rfl
  have hne : U ≠ ⊤ := by
    intro htop
    have hf : sphericalSection positiveParameter ∈ U := by rw [htop]; trivial
    change standardIntertwiner β (sphericalSection positiveParameter) = 0 at hf
    rw [standardIntertwiner_spherical] at hf
    have hv := congrArg (fun f : PrincipalSeries negativeParameter => (f 1).re) hf
    have hpos := characterScale_pos β
    simp [sphericalSection_one] at hv
    nlinarith
  exact LinearMap.ker_eq_bot.mp (eq_bot_of_closed_invariant_ne_top U hclosed hinv hne)

end DedekindZetaZeroFree.KPCplxActualImageProof

end

section

namespace DedekindZetaZeroFree.KPCplxActualImage

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped ContDiff Matrix.Norms.Elementwise

section
variable (β : ℂˣ)
include β
noncomputable def imageSubmodule    :=
  (standardIntertwiner β).toLinearMap.range

abbrev Theta   := ↥(imageSubmodule β)

theorem mem_imageSubmodule_iff   (h : PrincipalSeries negativeParameter) :
    h ∈ imageSubmodule β ↔ ∃ f : PrincipalSeries positiveParameter,
      standardIntertwiner β f = h := Iff.rfl

theorem imageSubmodule_invariant   (g : ComplexPGL2)
    (h : PrincipalSeries negativeParameter) (hh : h ∈ imageSubmodule β) :
    pi negativeParameter g h ∈ imageSubmodule β := by
  obtain ⟨f, rfl⟩ := hh
  exact ⟨pi positiveParameter g f, standardIntertwiner_equivariant β g f⟩

noncomputable def imageAction   (g : ComplexPGL2) (h : Theta β) : Theta β :=
  ⟨pi negativeParameter g h, imageSubmodule_invariant β g h h.property⟩

@[simp] theorem imageAction_coe   (g : ComplexPGL2) (h : Theta β) :
    (imageAction β g h : PrincipalSeries negativeParameter) = pi negativeParameter g h := rfl

noncomputable def intertwinerToImage  
    (f : PrincipalSeries positiveParameter) : Theta β :=
  ⟨standardIntertwiner β f, ⟨f, rfl⟩⟩

@[simp] theorem intertwinerToImage_coe   (f : PrincipalSeries positiveParameter) :
    (intertwinerToImage β f : PrincipalSeries negativeParameter) = standardIntertwiner β f := rfl

theorem intertwinerToImage_equivariant   (g : ComplexPGL2)
    (f : PrincipalSeries positiveParameter) :
    intertwinerToImage β (pi positiveParameter g f) =
      imageAction β g (intertwinerToImage β f) := by
  apply Subtype.ext
  apply standardIntertwiner_equivariant

theorem standardIntertwiner_topological_image_isomorphism   :
    ∃ e : PrincipalSeries positiveParameter ≃L[ℂ] Theta β,
      (∀ f : PrincipalSeries positiveParameter, e f = intertwinerToImage β f) ∧
      (∀ (g : ComplexPGL2) (f : PrincipalSeries positiveParameter),
        e (pi positiveParameter g f) = imageAction β g (e f)) := by
  let e₀ : PrincipalSeries positiveParameter ≃ₗ[ℂ] Theta β :=
    LinearEquiv.ofInjective (standardIntertwiner β).toLinearMap
      (KPCplxActualImageProof.standardIntertwiner_injective β)
  have hinv : Continuous e₀.symm := by
    apply (KPCplxActualImageProof.standardIntertwiner_isInducing β).continuous_iff.mpr
    have heq : (standardIntertwiner β) ∘ e₀.symm =
        (Subtype.val : Theta β → PrincipalSeries negativeParameter) := by
      funext h
      exact congrArg Subtype.val (e₀.apply_symm_apply h)
    rw [heq]
    exact continuous_subtype_val
  let e : PrincipalSeries positiveParameter ≃L[ℂ] Theta β :=
    { e₀ with
      continuous_toFun := (standardIntertwiner β).continuous.subtype_mk _
      continuous_invFun := hinv }
  have he : ∀ f : PrincipalSeries positiveParameter, e f = intertwinerToImage β f := by
    intro f
    apply Subtype.ext
    rfl
  refine ⟨e, he, ?_⟩
  intro g f
  rw [he, he]
  apply intertwinerToImage_equivariant

theorem imageAction_continuous   :
    Continuous (fun p : ComplexPGL2 × Theta β => imageAction β p.1 p.2) := by
  have hbase : Continuous (fun p : ComplexPGL2 × Theta β =>
      pi negativeParameter p.1 (p.2 : PrincipalSeries negativeParameter)) :=
    (pi_continuous negativeParameter).comp
      (by continuity : Continuous (fun p : ComplexPGL2 × Theta β =>
        (p.1, (p.2 : PrincipalSeries negativeParameter))))
  apply hbase.subtype_mk
end


def IsGInvariant (s : ℝ) (U : Submodule ℂ (PrincipalSeries s))  :=
  ∀ (g : ComplexPGL2) (f : PrincipalSeries s), f ∈ U → pi s g f ∈ U

def IsTopologicallyIrreducible (s : ℝ)  :=
  (∃ f : PrincipalSeries s, f ≠ 0) ∧
    ∀ U : Submodule ℂ (PrincipalSeries s),
      IsClosed (U : Set (PrincipalSeries s)) → IsGInvariant s U → U = ⊥ ∨ U = ⊤

private theorem principalSeries_irreducible_of_exceptional (s : ℝ)
    (hs : s = positiveParameter ∨ s = negativeParameter) :
    IsTopologicallyIrreducible s := by
  refine ⟨⟨sphericalSection s, ?_⟩, ?_⟩
  · intro hzero
    have hone := congrArg (fun f : PrincipalSeries s => f 1) hzero
    simp [sphericalSection_one] at hone
  · intro U hclosed hinv
    by_cases hbot : U = ⊥
    · exact Or.inl hbot
    · obtain ⟨ℓ, hℓ⟩ :=
        KPCplxActualImageProof.closed_invariant_harmonic_extraction s U hclosed
          (fun k f hf => hinv k f hf) hbot
      exact Or.inr (KPCplxActualImageProof.closed_harmonic_exhaustion s U hclosed
        (KPCplxActualImageProof.exceptional_harmonic_propagation s hs U hclosed hinv ℓ hℓ))

theorem exceptional_principalSeries_irreducible :
    IsTopologicallyIrreducible positiveParameter ∧
      IsTopologicallyIrreducible negativeParameter := ⟨principalSeries_irreducible_of_exceptional positiveParameter (Or.inl rfl),
    principalSeries_irreducible_of_exceptional negativeParameter (Or.inr rfl)⟩

private theorem imageSubmodule_closed (β : ℂˣ) : IsClosed (imageSubmodule β : Set (PrincipalSeries negativeParameter)) := by
  letI := principalSeries_complete positiveParameter
  letI := principalSeries_t2 negativeParameter
  letI : IsUniformAddGroup (PrincipalSeries positiveParameter) :=
    isUniformAddGroup_of_addCommGroup
  letI : IsUniformAddGroup (PrincipalSeries negativeParameter) :=
    isUniformAddGroup_of_addCommGroup
  letI : IsUniformAddGroup (Theta β) :=
    IsUniformInducing.isUniformAddGroup (Submodule.subtype (imageSubmodule β))
      isUniformEmbedding_subtype_val.isUniformInducing
  obtain ⟨e, _, _⟩ := standardIntertwiner_topological_image_isomorphism β
  have hemb : IsUniformEmbedding e := by
    exact e.toLinearEquiv.toEquiv.isUniformEmbedding
      (uniformContinuous_addMonoidHom_of_continuous (f := e.toLinearEquiv.toAddEquiv) e.continuous)
      (uniformContinuous_addMonoidHom_of_continuous (f := e.symm.toLinearEquiv.toAddEquiv) e.symm.continuous)
  have h : IsUniformEmbedding (fun x : PrincipalSeries positiveParameter =>
      (e x : PrincipalSeries negativeParameter)) :=
    isUniformEmbedding_subtype_val.comp hemb
  have hcl := h.isUniformInducing.isComplete_range.isClosed
  have hrange : Set.range (fun x : PrincipalSeries positiveParameter =>
      (e x : PrincipalSeries negativeParameter)) = imageSubmodule β := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).property
    · intro hy
      obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
      exact ⟨x, congrArg Subtype.val hx⟩
  rwa [hrange] at hcl
private theorem imageSubmodule_ne_bot (β : ℂˣ) : imageSubmodule β ≠ ⊥ := by
  intro hbot
  have hmem : standardIntertwiner β (sphericalSection positiveParameter) ∈ imageSubmodule β :=
    ⟨sphericalSection positiveParameter, rfl⟩
  rw [hbot, Submodule.mem_bot, standardIntertwiner_spherical] at hmem
  have hv := congrArg (fun f : PrincipalSeries negativeParameter => (f 1).re) hmem
  have hpos := characterScale_pos β
  simp [sphericalSection_one] at hv
  nlinarith

theorem imageSubmodule_eq_top (β : ℂˣ) : imageSubmodule β = ⊤ := by
  rcases exceptional_principalSeries_irreducible.2.2 (imageSubmodule β)
      (imageSubmodule_closed β) (imageSubmodule_invariant β) with h | h
  · exact False.elim (imageSubmodule_ne_bot β h)
  · exact h

section
variable (s : ℝ) (f : PrincipalSeries s)
    (p : Matrix (Fin 2) (Fin 2) ℂ × ℂ)
include s f p
noncomputable def orbitOpenCoordinate   : ℂ :=
  matrixFunction f ((weyl * upperUnipotent p.2 : ComplexGL2) * p.1)

noncomputable def orbitInfinityCoordinate    :=
  matrixFunction f ((lowerUnipotent p.2 : ComplexGL2) * p.1)
end


def HasSmoothOrbit (s : ℝ) (f : PrincipalSeries s)  :=
  ContDiffOn ℝ ∞ (orbitOpenCoordinate s f) {p | p.1.det ≠ 0} ∧
    ContDiffOn ℝ ∞ (orbitInfinityCoordinate s f) {p | p.1.det ≠ 0}

private theorem lowerSmooth : ContDiff ℝ ∞ (fun p : Matrix (Fin 2) (Fin 2) ℂ × ℂ =>
  (lowerUnipotent p.2 : Matrix (Fin 2) (Fin 2) ℂ) * p.1) := by
  change ContDiff ℝ ∞ (fun p : Matrix (Fin 2) (Fin 2) ℂ × ℂ =>
    (fun i j => ((lowerUnipotent p.2 : Matrix (Fin 2) (Fin 2) ℂ) * p.1) i j))
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two] <;> fun_prop
private theorem openSmooth : ContDiff ℝ ∞ (fun p : Matrix (Fin 2) (Fin 2) ℂ × ℂ =>
  ((weyl * upperUnipotent p.2) : Matrix (Fin 2) (Fin 2) ℂ) * p.1) := by
  change ContDiff ℝ ∞ (fun p : Matrix (Fin 2) (Fin 2) ℂ × ℂ =>
    (fun i j => (((weyl * upperUnipotent p.2 : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ) * p.1) i j))
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, upperUnipotent, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> fun_prop
section
variable (p : Matrix (Fin 2) (Fin 2) ℂ × ℂ)
    (hp : p.1.det ≠ 0)
include p hp
private theorem lowerMaps   :
    (((lowerUnipotent p.2) : Matrix (Fin 2) (Fin 2) ℂ) * p.1).det ≠ 0 := by
  rw [Matrix.det_mul]
  exact mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero _) hp
private theorem openMaps   :
    ((((weyl * upperUnipotent p.2 : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ) * p.1)).det ≠ 0 := by
  rw [Matrix.det_mul]
  exact mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero _) hp
end

private theorem principalSeries_hasSmoothOrbit (s : ℝ) (f : PrincipalSeries s) :
    HasSmoothOrbit s f := by
  obtain ⟨_, hf⟩ := (principalSeries_mem_iff s f).mp f.property
  constructor
  · have h := hf.comp openSmooth.contDiffOn (fun p hp => openMaps p hp)
    exact h
  · have h := hf.comp lowerSmooth.contDiffOn (fun p hp => lowerMaps p hp)
    exact h

theorem exceptional_principalSeries_continuous_smooth :
    (Continuous (fun p : ComplexPGL2 × PrincipalSeries positiveParameter =>
      pi positiveParameter p.1 p.2) ∧
      ∀ f : PrincipalSeries positiveParameter, HasSmoothOrbit positiveParameter f) ∧
    (Continuous (fun p : ComplexPGL2 × PrincipalSeries negativeParameter =>
      pi negativeParameter p.1 p.2) ∧
      ∀ f : PrincipalSeries negativeParameter, HasSmoothOrbit negativeParameter f) := ⟨⟨pi_continuous positiveParameter, principalSeries_hasSmoothOrbit positiveParameter⟩,
    ⟨pi_continuous negativeParameter, principalSeries_hasSmoothOrbit negativeParameter⟩⟩

def image_smooth (β : ℂˣ) (h : Theta β)  :=
  (exceptional_principalSeries_continuous_smooth.2.2) h

theorem spherical_image (β : ℂˣ) :
    (intertwinerToImage β (sphericalSection positiveParameter) :
      PrincipalSeries negativeParameter) =
        (3 * characterScale β / 2 : ℂ) • sphericalSection negativeParameter ∧
    ∀ k : compactSubgroup,
      imageAction β k (intertwinerToImage β (sphericalSection positiveParameter)) =
        intertwinerToImage β (sphericalSection positiveParameter) := by
  refine ⟨standardIntertwiner_spherical β, fun k => ?_⟩
  rw [← intertwinerToImage_equivariant β k
    (sphericalSection positiveParameter), sphericalSection_fixed]

theorem harmonicKType_source (β : ℂˣ) (ℓ : ℕ)
    (h : PrincipalSeries negativeParameter) (hh : h ∈ harmonicKType negativeParameter ℓ) :
    ∃ f : PrincipalSeries positiveParameter,
      f ∈ harmonicKType positiveParameter ℓ ∧ standardIntertwiner β f = h := by
  have hscalar : (eigenvalue β ℓ : ℂ) ≠ 0 := by
    exact_mod_cast eigenvalue_ne_zero β ℓ
  have hcompact : compactRestriction negativeParameter h ∈
      (harmonicKType positiveParameter ℓ).map (compactRestriction positiveParameter) := by
    rw [(harmonicKType_compact_identification positiveParameter negativeParameter ℓ).2]
    exact ⟨h, hh, rfl⟩
  obtain ⟨f, hf, hfrestr⟩ := hcompact
  refine ⟨(eigenvalue β ℓ : ℂ)⁻¹ • f,
    (harmonicKType positiveParameter ℓ).smul_mem _ hf, ?_⟩
  apply (harmonicKType_compact_identification negativeParameter positiveParameter ℓ).1
  rw [map_smul, map_smul, (standardIntertwiner_harmonic_eigenvalue β ℓ f hf).2,
    smul_smul, inv_mul_cancel₀ hscalar, one_smul, hfrestr]

theorem harmonicKType_le_imageSubmodule (β : ℂˣ) (ℓ : ℕ) :
    harmonicKType negativeParameter ℓ ≤ imageSubmodule β := by
  intro h hh
  obtain ⟨f, _, hf⟩ := harmonicKType_source β ℓ h hh
  exact ⟨f, hf⟩

end DedekindZetaZeroFree.KPCplxActualImage

end
