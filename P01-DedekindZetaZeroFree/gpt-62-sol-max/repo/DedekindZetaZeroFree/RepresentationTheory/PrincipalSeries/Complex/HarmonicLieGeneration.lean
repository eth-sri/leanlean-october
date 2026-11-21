module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RankOne.NormalizedCasimir

@[expose] public section

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar Matrix

abbrev RawMat := Matrix (Fin 2) (Fin 2) ℂ

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end








section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar

noncomputable instance instNormedAddCommGroupHarmonicLieRawMat : NormedAddCommGroup RawMat :=
  { Matrix.normedAddCommGroup.replaceTopology (by rfl) with
    norm := Matrix.normedAddCommGroup.norm
    dist_eq := Matrix.normedAddCommGroup.dist_eq }

noncomputable instance instNormedSpaceRealHarmonicLieRawMat : NormedSpace ℝ RawMat := Matrix.normedSpace

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar Matrix

abbrev RawWord := List RawMat

noncomputable def rawLie (X : RawMat) (f : ComplexGL2 → ℂ) (g : ComplexGL2) : ℂ :=
  fderiv ℝ (matrixFunction f) (g : RawMat) ((g : RawMat) * X)

noncomputable def rawWord (w : RawWord) (f : ComplexGL2 → ℂ) : ComplexGL2 → ℂ :=
  w.foldr rawLie f

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar

open scoped Matrix.Norms.Elementwise ContDiff
attribute [local instance] Complex.instNormedAddCommGroup
private theorem locus_open : IsOpen {g : RawMat | g.det ≠ 0} := by
  apply isOpen_ne.preimage
  change Continuous (fun g : RawMat => g.det)
  simp only [Matrix.det_fin_two]
  fun_prop
private theorem tangent_smooth (X : RawMat) : ContDiff ℝ ∞ (fun g : RawMat => g * X) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply ContDiff.sum
  intro k _
  exact ((contDiff_apply ℝ ℂ k).comp (contDiff_apply ℝ (Fin 2 → ℂ) i)).mul contDiff_const
private theorem lie_smooth (X : RawMat) (f : ComplexGL2 → ℂ)
    (hf : ContDiffOn ℝ ∞ (matrixFunction f) {g | g.det ≠ 0}) :
    ContDiffOn ℝ ∞ (matrixFunction (rawLie X f)) {g | g.det ≠ 0} := by
  have hd := (contDiffOn_infty_iff_fderiv_of_isOpen locus_open).mp hf
  apply (hd.2.clm_apply (tangent_smooth X).contDiffOn).congr
  intro g hg
  change g.det ≠ 0 at hg
  dsimp only [matrixFunction]
  rw [dif_pos hg]
  rfl
private theorem word_smooth (s : ℝ) (w : RawWord) :
    ContDiffOn ℝ ∞ (matrixFunction (rawWord w (sphericalSection s : ComplexGL2 → ℂ)))
      {g | g.det ≠ 0} := by
  induction w with
  | nil =>
    exact ((principalSeries_mem_iff s _).mp (sphericalSection s).property).2
  | cons X w ih => exact lie_smooth X _ ih
private theorem matrix_add (f h : ComplexGL2 → ℂ) :
    matrixFunction (f + h) = matrixFunction f + matrixFunction h := by
  funext g
  simp only [matrixFunction, Pi.add_apply]
  split <;> simp
private theorem matrix_smul (a : ℂ) (f : ComplexGL2 → ℂ) :
    matrixFunction (a • f) = a • matrixFunction f := by
  funext g
  simp only [matrixFunction, Pi.smul_apply]
  split <;> simp
private theorem matrix_zero : matrixFunction (0 : ComplexGL2 → ℂ) = 0 := by
  funext g
  simp [matrixFunction]
private theorem lie_add (X : RawMat) (f h : ComplexGL2 → ℂ)
    (hf : ContDiffOn ℝ ∞ (matrixFunction f) {g | g.det ≠ 0})
    (hh : ContDiffOn ℝ ∞ (matrixFunction h) {g | g.det ≠ 0}) :
    rawLie X (f + h) = rawLie X f + rawLie X h := by
  funext g
  have hgf : DifferentiableAt ℝ (matrixFunction f) (g : RawMat) :=
    (hf.differentiableOn (by simp)).differentiableAt (locus_open.mem_nhds g.det_ne_zero)
  have hgh : DifferentiableAt ℝ (matrixFunction h) (g : RawMat) :=
    (hh.differentiableOn (by simp)).differentiableAt (locus_open.mem_nhds g.det_ne_zero)
  simp only [rawLie, matrix_add, Pi.add_apply]
  convert congrArg (fun T : RawMat →L[ℝ] ℂ => T ((g : RawMat) * X))
    (fderiv_add hgf hgh) using 1 <;> rfl
private theorem lie_smul (X : RawMat) (a : ℂ) (f : ComplexGL2 → ℂ)
    (hf : ContDiffOn ℝ ∞ (matrixFunction f) {g | g.det ≠ 0}) :
    rawLie X (a • f) = a • rawLie X f := by
  funext g
  have hgf : DifferentiableAt ℝ (matrixFunction f) (g : RawMat) :=
    (hf.differentiableOn (by simp)).differentiableAt (locus_open.mem_nhds g.det_ne_zero)
  simp only [rawLie, matrix_smul, Pi.smul_apply]
  convert congrArg (fun T : RawMat →L[ℝ] ℂ => T ((g : RawMat) * X))
    (fderiv_const_smul hgf a) using 1 <;> rfl

theorem raw_spherical_span_lie_stable (s : ℝ) (X : RawMat)
    (f : PrincipalSeries s)
    (hf : (f : ComplexGL2 → ℂ) ∈ Submodule.span ℂ
      (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection s : ComplexGL2 → ℂ)))) :
    rawLie X (f : ComplexGL2 → ℂ) ∈ Submodule.span ℂ
      (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection s : ComplexGL2 → ℂ))) := by
  have h : ∀ (u : ComplexGL2 → ℂ), u ∈ Submodule.span ℂ
      (Set.range (fun w : RawWord => rawWord w (sphericalSection s : ComplexGL2 → ℂ))) →
      ContDiffOn ℝ ∞ (matrixFunction u) {g | g.det ≠ 0} ∧
      rawLie X u ∈ Submodule.span ℂ
        (Set.range (fun w : RawWord => rawWord w (sphericalSection s : ComplexGL2 → ℂ))) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      rcases hu with ⟨w, rfl⟩
      exact ⟨word_smooth s w, Submodule.subset_span ⟨X :: w, rfl⟩⟩
    | zero =>
      constructor
      · rw [matrix_zero]; exact contDiffOn_const
      · have hz : rawLie X (0 : ComplexGL2 → ℂ) = 0 := by
          funext g
          simp [rawLie, matrix_zero]
        rw [hz]
        exact Submodule.zero_mem _
    | add u v hu hv ihu ihv =>
      constructor
      · rw [matrix_add]; exact ihu.1.add ihv.1
      · rw [lie_add X u v ihu.1 ihv.1]
        exact Submodule.add_mem _ ihu.2 ihv.2
    | smul a u hu ihu =>
      constructor
      · rw [matrix_smul]; exact ihu.1.const_smul a
      · rw [lie_smul X a u ihu.1]
        exact Submodule.smul_mem _ a ihu.2
  exact (h _ hf).2

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar

private noncomputable def translate (a : ComplexGL2) :
    (ComplexGL2 → ℂ) →ₗ[ℂ] (ComplexGL2 → ℂ) where
  toFun f g := f (g * a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def matrixRight (a : ComplexGL2) : RawMat ≃L[ℝ] RawMat :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun m => m * (a : RawMat)
      invFun := fun m => m * ((a⁻¹ : ComplexGL2) : RawMat)
      left_inv := by intro m; simp [Matrix.mul_assoc, ← Units.val_mul]
      right_inv := by intro m; simp [Matrix.mul_assoc, ← Units.val_mul]
      map_add' := by intro m n; exact Matrix.add_mul _ _ _
      map_smul' := by intro c m; exact Matrix.smul_mul _ _ _ }

private lemma matrixFunction_translate (a : ComplexGL2) (f : ComplexGL2 → ℂ) :
    matrixFunction (translate a f) = matrixFunction f ∘ matrixRight a := by
  funext m
  have hd := Matrix.GeneralLinearGroup.det_ne_zero a
  have he : (m * (a : RawMat)).det ≠ 0 ↔ m.det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero_iff.trans (and_iff_left hd)
  change (if h : m.det ≠ 0 then
    translate a f (Matrix.GeneralLinearGroup.mkOfDetNeZero m h) else 0) =
    (if h : (m * (a : RawMat)).det ≠ 0 then
      f (Matrix.GeneralLinearGroup.mkOfDetNeZero (m * (a : RawMat)) h) else 0)
  by_cases hm : m.det ≠ 0
  · rw [dif_pos hm, dif_pos (he.mpr hm)]
    change f (_ * a) = f _
    congr 1
    apply Units.ext
    rfl
  · rw [dif_neg hm, dif_neg (fun h => hm (he.mp h))]

private lemma translate_rawLie (a : ComplexGL2) (X : RawMat)
    (f : ComplexGL2 → ℂ) :
    translate a (rawLie X f) =
      rawLie ((a : RawMat) * X * ((a⁻¹ : ComplexGL2) : RawMat)) (translate a f) := by
  funext g
  change fderiv ℝ (matrixFunction f) ((g * a : ComplexGL2) : RawMat)
      (((g * a : ComplexGL2) : RawMat) * X) =
    fderiv ℝ (matrixFunction (translate a f)) (g : RawMat)
      ((g : RawMat) * ((a : RawMat) * X * ((a⁻¹ : ComplexGL2) : RawMat)))
  rw [matrixFunction_translate]
  have hd := (matrixRight a).comp_right_fderiv (f := matrixFunction f) (x := (g : RawMat))
  erw [hd]
  change fderiv ℝ (matrixFunction f) ((g : RawMat) * (a : RawMat))
      (((g : RawMat) * (a : RawMat)) * X) =
    fderiv ℝ (matrixFunction f) ((g : RawMat) * (a : RawMat))
      (((g : RawMat) * ((a : RawMat) * X * ((a⁻¹ : ComplexGL2) : RawMat))) * (a : RawMat))
  congr 1
  have ha : ((a⁻¹ : ComplexGL2) : RawMat) * (a : RawMat) = 1 := a.inv_val
  simpa only [Matrix.mul_assoc, ha, Matrix.mul_one]

private lemma translate_rawWord (a : ComplexGL2) (w : RawWord)
    (f : ComplexGL2 → ℂ) :
    translate a (rawWord w f) =
      rawWord (w.map (fun X => (a : RawMat) * X * ((a⁻¹ : ComplexGL2) : RawMat))) (translate a f) := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    simp only [rawWord, List.foldr_cons, List.map_cons] at *
    rw [translate_rawLie, ih]

theorem raw_spherical_span_compact_stable (s : ℝ) (k : compactSubgroup)
    (f : PrincipalSeries s)
    (hf : (f : ComplexGL2 → ℂ) ∈ Submodule.span ℂ
      (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection s : ComplexGL2 → ℂ)))) :
    (pi s k f : ComplexGL2 → ℂ) ∈ Submodule.span ℂ
      (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection s : ComplexGL2 → ℂ))) := by
  obtain ⟨u, hu⟩ := k.property
  let a := complexSU2Embedding u
  have hk : Matrix.ProjGenLinGroup.mk a = (k : ComplexPGL2) := hu
  have hfixed : translate a (sphericalSection s : ComplexGL2 → ℂ) =
      (sphericalSection s : ComplexGL2 → ℂ) := by
    have h := sphericalSection_fixed s k
    rw [← hk, pi_mk] at h
    exact congrArg (fun t : PrincipalSeries s => (t : ComplexGL2 → ℂ)) h
  have hspan : ∀ v : ComplexGL2 → ℂ,
      v ∈ Submodule.span ℂ (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection s : ComplexGL2 → ℂ))) →
      translate a v ∈ Submodule.span ℂ (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection s : ComplexGL2 → ℂ))) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨w, rfl⟩ := hv
      rw [translate_rawWord, hfixed]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add v z hv hz iv iz =>
      rw [map_add]
      exact Submodule.add_mem _ iv iz
    | smul c v hv iv =>
      rw [map_smul]
      exact Submodule.smul_mem _ c iv
  rw [← hk, pi_mk]
  exact hspan (f : ComplexGL2 → ℂ) hf

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues KPCplxCharacterHaar

open KPCplxHarmonicPropagation.RaisingCalculation
open scoped Matrix Matrix.Norms.Elementwise

namespace Boost

theorem rawLie_section_exists (s : ℝ) (X : RawMat) (u : PrincipalSeries s) :
    ∃ v : PrincipalSeries s, (v : ComplexGL2 → ℂ) = rawLie X u := by
  let D := RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction.rightDerivativeLinear s X
  refine ⟨D u, ?_⟩
  funext g
  rw [RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction.rightDerivativeLinear_apply,
    RepresentationTheory.KPSmoothCoreCasimirEnergy.CasimirHessian.rightDerivative_fderiv]
  rfl

noncomputable def boostMatrix : RawMat := !![1, 0; 0, 0]

private theorem boost_path_hasDerivAt (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => ((g * boost t : ComplexGL2) : RawMat))
      ((g : RawMat) * boostMatrix) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hb (t : ℝ) : (boost t : RawMat) = !![(Real.exp t : ℂ), 0; 0, 1] := rfl
  change HasDerivAt (fun t : ℝ => ((g : RawMat) * (boost t : RawMat)) i j) _ 0
  simp_rw [hb]
  fin_cases j
  · simpa [boostMatrix, Matrix.mul_apply, Fin.sum_univ_two] using
      (Real.hasDerivAt_exp (0 : ℝ)).ofReal_comp.const_mul ((g : RawMat) i 0)
  · simpa [boostMatrix, Matrix.mul_apply, Fin.sum_univ_two] using
      hasDerivAt_const (0 : ℝ) ((g : RawMat) i 1)

private theorem rawLie_boost_deriv (s : ℝ) (u : PrincipalSeries s) (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => u (g * boost t)) (rawLie boostMatrix u g) 0 := by
  have hf := ((principalSeries_mem_iff s u.val).mp u.property).2
  have hcont : Continuous (fun m : RawMat => m.det) := by fun_prop
  have hd := (hf.differentiableOn (by simp)).differentiableAt
    ((isOpen_ne.preimage hcont).mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g))
  have hh := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (boost_path_hasDerivAt g)
    (by simp [boost_zero])
  have he : (fun t : ℝ => u (g * boost t)) =
      matrixFunction u.val ∘ (fun t : ℝ => ((g * boost t : ComplexGL2) : RawMat)) := by
    funext t
    simp only [Function.comp_def, matrixFunction,
      dif_pos (Matrix.GeneralLinearGroup.det_ne_zero (g * boost t))]
    apply congrArg (u : ComplexGL2 → ℂ)
    apply Units.ext
    rfl
  rw [he]
  exact hh

private theorem rawLie_harmonic_boost (s : ℝ) (ℓ : ℕ) (g : ComplexGL2) :
    rawLie boostMatrix (harmonicSection s ℓ) g =
      (-(((ℓ : ℝ) + 1 + 2 * s : ℝ) : ℂ)) * rowZ g * harmonicSection s ℓ g := by
  exact (rawLie_boost_deriv s (harmonicSection s ℓ) g).unique
    (harmonic_boost_hasDerivAt s ℓ g)

end Boost

theorem harmonic_noncompact_raising (s : ℝ) (ℓ : ℕ)
    (hcoeff : (ℓ : ℝ) + 1 + 2 * s ≠ 0) :
    ∃ (X : RawMat) (u v h : PrincipalSeries s),
      u ∈ harmonicKType s ℓ ∧
      v ∈ harmonicKType s (ℓ + 1) ∧
      v ≠ 0 ∧
      h ∈ harmonicKType s (ℓ - 1) ∧
      rawLie X (u : ComplexGL2 → ℂ) =
        (v : ComplexGL2 → ℂ) + (h : ComplexGL2 → ℂ) := by
  let c : ℂ := -(((ℓ : ℝ) + 1 + 2 * s : ℝ) : ℂ)
  have hc : c ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hcoeff)
  obtain ⟨v, hv⟩ := Boost.rawLie_section_exists s
    Boost.boostMatrix (harmonicSection s ℓ)
  have hformula (g : ComplexGL2) : v g = c * rowZ g *
      harmonicSection s ℓ g := by
    rw [show v g = rawLie Boost.boostMatrix
      (harmonicSection s ℓ) g from congrFun hv g]
    exact Boost.rawLie_harmonic_boost s ℓ g
  refine ⟨Boost.boostMatrix, harmonicSection s ℓ,
    v, 0, harmonicSection_harmonic s ℓ,
    height_harmonic_of_formula s ℓ c v hformula,
    height_ne_zero_of_formula s ℓ c hc v hformula,
    (harmonicKType s (ℓ - 1)).zero_mem, ?_⟩
  simpa using hv.symm

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues KPCplxCharacterHaar

theorem harmonic_zero_mem_raw_spherical_span
    (f : PrincipalSeries positiveParameter)
    (hf : f ∈ harmonicKType positiveParameter 0) :
    (f : ComplexGL2 → ℂ) ∈ Submodule.span ℂ
      (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection positiveParameter : ComplexGL2 → ℂ))) := by
  change compactRestriction positiveParameter f ∈
    (harmonicPolynomials 0).map polynomialCompactRestriction at hf
  obtain ⟨p, hp, he⟩ := hf
  have hp0 : p.IsHomogeneous 0 := hp.1
  have hpC : p = MvPolynomial.C (p.coeff 0) := by
    exact (MvPolynomial.homogeneousComponent_eq_self hp0).symm.trans
      (MvPolynomial.homogeneousComponent_zero p)
  have hfeq : f = (p.coeff 0) • sphericalSection positiveParameter := by
    apply (harmonicKType_compact_identification positiveParameter positiveParameter 0).1
    rw [← he, map_smul]
    ext k
    change MvPolynomial.eval (compactSphereCoordinate k) p =
      (p.coeff 0) * sphericalSection positiveParameter (complexSU2Embedding k)
    rw [hpC, MvPolynomial.eval_C, KPCplxHarmonicPropagation.RaisingCalculation.spherical_compact, mul_one]
    simp
  rw [hfeq]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨[], rfl⟩

theorem harmonic_mem_raw_spherical_span (ℓ : ℕ)
    (f : PrincipalSeries positiveParameter)
    (hf : f ∈ harmonicKType positiveParameter ℓ) :
    (f : ComplexGL2 → ℂ) ∈ Submodule.span ℂ
      (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection positiveParameter : ComplexGL2 → ℂ))) := by
  induction ℓ using Nat.strong_induction_on generalizing f with
  | h n ih =>
    cases n with
    | zero => exact harmonic_zero_mem_raw_spherical_span f hf
    | succ ℓ =>
      let S : Submodule ℂ (ComplexGL2 → ℂ) := Submodule.span ℂ
        (Set.range (fun w : RawWord =>
          rawWord w (sphericalSection positiveParameter : ComplexGL2 → ℂ)))
      let U : Submodule ℂ (PrincipalSeries positiveParameter) :=
        S.comap (principalSeriesSubmodule positiveParameter).subtype
      let W : Submodule ℂ (PrincipalSeries positiveParameter) :=
        harmonicKType positiveParameter (ℓ + 1) ⊓ U
      have hcoeff : (ℓ : ℝ) + 1 + 2 * positiveParameter ≠ 0 := by
        dsimp only [positiveParameter]
        positivity
      obtain ⟨X, u, v, h, hu, hv, hvne, hh, he⟩ :=
        harmonic_noncompact_raising positiveParameter ℓ hcoeff
      have huS : (u : ComplexGL2 → ℂ) ∈ S :=
        ih ℓ (Nat.lt_succ_self ℓ) u hu
      have hhS : (h : ComplexGL2 → ℂ) ∈ S :=
        ih (ℓ - 1) (by omega) h hh
      have hvS : (v : ComplexGL2 → ℂ) ∈ S := by
        have hlie := raw_spherical_span_lie_stable positiveParameter X u huS
        have he' : (v : ComplexGL2 → ℂ) =
            rawLie X (u : ComplexGL2 → ℂ) - (h : ComplexGL2 → ℂ) := by
          rw [he]
          abel
        rw [he']
        exact S.sub_mem hlie hhS
      have hvW : v ∈ W := ⟨hv, hvS⟩
      have hW : IsKInvariant positiveParameter W := by
        intro k g hg
        refine ⟨(harmonicKType_multiplicity_one positiveParameter (ℓ + 1)).1 k g hg.1,
          ?_⟩
        exact raw_spherical_span_compact_stable positiveParameter k g hg.2
      have hcases := (harmonicKType_multiplicity_one positiveParameter (ℓ + 1)).2.2.1
        W inf_le_left hW
      have hWeq : W = harmonicKType positiveParameter (ℓ + 1) := by
        rcases hcases with hzero | hfull
        · have : v = 0 := by
            have hvbot : v ∈ (⊥ : Submodule ℂ (PrincipalSeries positiveParameter)) := by
              rw [← hzero]
              exact hvW
            simpa only [Submodule.mem_bot] using hvbot
          exact (hvne this).elim
        · exact hfull
      have hfW : f ∈ W := by
        rw [hWeq]
        exact hf
      exact hfW.2

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end
