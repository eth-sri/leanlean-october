module

public import DedekindZetaZeroFree.Metaplectic.Weil.SchwartzBruhatStability
public import DedekindZetaZeroFree.Metaplectic.Weil.ArchimedeanProductQuadraticOperators

@[expose] public section

section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.QuadraticRawProduct.TensorKernelSteps

variable {F : Type} [Field F] [NumberField F]

private alias kernel_integrable := DedekindZetaZeroFree.QuadraticRawProduct.SchwartzBruhatStability.kernel_integrable

 section

variable (T : Finset (HeightOneSpectrum (𝓞 F)))

theorem fourier_add_testSpace
    (f g : testSpace F T) :
    fourier F T ((f : PoissonS.Space F T → ℂ) + (g : PoissonS.Space F T → ℂ)) =
      fourier F T (f : PoissonS.Space F T → ℂ) +
        fourier F T (g : PoissonS.Space F T → ℂ) := by
  funext y
  simp only [fourier, PoissonS.fourierIntegral, Pi.add_apply, add_mul]
  exact integral_add
    (kernel_integrable T f
      (testSpace_integrable T f f.2) y)
    (kernel_integrable T g
      (testSpace_integrable T g g.2) y)

 def chirpLinearMap (b : F) :
    (PoissonS.Space F T → ℂ) →ₗ[ℂ] (PoissonS.Space F T → ℂ) where
  toFun f := chirp F T b f
  map_add' f g := by
    funext x
    simp only [chirp, Pi.add_apply, mul_add]
  map_smul' a f := by
    funext x
    simp only [chirp, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

 def dilationLinearMap (c : F) :
    (PoissonS.Space F T → ℂ) →ₗ[ℂ] (PoissonS.Space F T → ℂ) where
  toFun f := dilation F T c f
  map_add' f g := by
    funext x
    simp only [dilation, Pi.add_apply]
  map_smul' a f := by
    funext x
    simp only [dilation, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

end

 def fourT (A : SArithmeticData F) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    testSpace F T →ₗ[ℂ] testSpace F T where
  toFun f := ⟨fourier F T (f : PoissonS.Space F T → ℂ),
    (testSpace_stability A T 0 (f : PoissonS.Space F T → ℂ) f.2).1⟩
  map_add' f g := by
    apply Subtype.ext
    show fourier F T ((f : PoissonS.Space F T → ℂ) + (g : PoissonS.Space F T → ℂ)) =
      fourier F T (f : PoissonS.Space F T → ℂ) + fourier F T (g : PoissonS.Space F T → ℂ)
    exact fourier_add_testSpace T f g
  map_smul' a f := by
    apply Subtype.ext
    show fourier F T (a • (f : PoissonS.Space F T → ℂ)) =
      a • fourier F T (f : PoissonS.Space F T → ℂ)
    exact fourier_smul T a (f : PoissonS.Space F T → ℂ)

 def fourTest (A : SArithmeticData F) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    testSpace F T →ₗ[ℂ] (PoissonS.Space F T → ℂ) where
  toFun f := fourier F T (f : PoissonS.Space F T → ℂ)
  map_add' f g := fourier_add_testSpace T f g
  map_smul' a f := fourier_smul T a (f : PoissonS.Space F T → ℂ)

 variable (A : SArithmeticData F) (T : Finset (HeightOneSpectrum (𝓞 F)))

def chirpT (b : F) :
    testSpace F T →ₗ[ℂ] testSpace F T where
  toFun f := ⟨chirp F T b (f : PoissonS.Space F T → ℂ),
    (testSpace_stability A T b (f : PoissonS.Space F T → ℂ) f.2).2⟩
  map_add' f g := by
    apply Subtype.ext
    show chirp F T b ((f : PoissonS.Space F T → ℂ) + (g : PoissonS.Space F T → ℂ)) =
      chirp F T b (f : PoissonS.Space F T → ℂ) + chirp F T b (g : PoissonS.Space F T → ℂ)
    exact (chirpLinearMap T b).map_add _ _
  map_smul' a f := by
    apply Subtype.ext
    show chirp F T b (a • (f : PoissonS.Space F T → ℂ)) =
      a • chirp F T b (f : PoissonS.Space F T → ℂ)
    exact (chirpLinearMap T b).map_smul a _

include A in
theorem quadratic_compositions_linear (b c d : F) (k : ℂ) :
    ∃ L R : testSpace F T →ₗ[ℂ] (PoissonS.Space F T → ℂ),
      (∀ f : testSpace F T,
        L f = fourier F T (chirp F T b (fourier F T (f : PoissonS.Space F T → ℂ)))) ∧
      (∀ f : testSpace F T,
        R f = fun y => k * chirp F T c
          (dilation F T d
            (fourier F T (chirp F T c (f : PoissonS.Space F T → ℂ)))) y) := by
  refine ⟨(fourTest A T).comp ((chirpT A T b).comp (fourT A T)),
    (k • ((chirpLinearMap T c).comp ((dilationLinearMap T d).comp (fourTest A T)))).comp
      (chirpT A T c), ?_, ?_⟩
  · intro f
    simp only [LinearMap.comp_apply]
    rfl
  · intro f
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, chirpLinearMap, dilationLinearMap, fourTest, chirpT,
      LinearMap.coe_mk, AddHom.coe_mk]

end DedekindZetaZeroFree.QuadraticRawProduct.TensorKernelSteps

end

end

section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.QuadraticRawProduct.TensorKernelSteps

variable (F : Type) [Field F] [NumberField F]

private alias recombination_phase_eq_traceCharacter := DedekindZetaZeroFree.QuadraticRawProduct.SchwartzBruhatStability.phase_eq_traceCharacter

variable {F}

private alias recombination_fieldMul_coordinates := DedekindZetaZeroFree.QuadraticRawProduct.SchwartzBruhatStability.fieldMul_coordinates

local instance recombinationCompletionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance recombinationCompletionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (A : SArithmeticData F) (T : Finset (HeightOneSpectrum (𝓞 F)))

private theorem recombination_fourier_tensor
    (hHaar : ∀ v, A.finiteTraceHaar v = localNormalizedHaar F v)
    (hCharacter : ∀ v, ResidueTrace.localTraceCharacter v = localFiniteCharacter F v)
    (fArch : PoissonArch.Space F → ℂ)
    (φ : (v : T) → v.val.adicCompletion F → ℂ) :
    fourier F T (fun z => fArch z.1 * ∏ v : T, φ v (z.2 v)) =
      fun y => PoissonArch.traceFourier F fArch y.1 *
        ∏ v : T, A.finiteTraceFourier v.val (φ v) (y.2 v) := by
  haveI : MeasureTheory.SFinite (PoissonArch.traceMeasure F) := by
    unfold PoissonArch.traceMeasure
    infer_instance
  funext y
  unfold fourier PoissonS.fourierIntegral PoissonS.productMeasure
  have hfun : (fun x : PoissonS.Space F T =>
      (fArch x.1 * ∏ v : T, φ v (x.2 v)) *
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
          (PoissonArch.tracePairing F x.1 y.1 : ℂ)) *
        ∏ v : T, (localFiniteCharacter F v.val (-x.2 v * y.2 v) : ℂ)) =
      fun x => (fArch x.1 * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        (PoissonArch.tracePairing F x.1 y.1 : ℂ))) *
        ∏ v : T, φ v (x.2 v) * (localFiniteCharacter F v.val (-x.2 v * y.2 v) : ℂ) := by
    funext x
    rw [Finset.prod_mul_distrib]
    ring
  rw [hfun]
  have hi := MeasureTheory.integral_prod_mul
    (μ := PoissonArch.traceMeasure F)
    (ν := MeasureTheory.Measure.pi (fun v : T => localNormalizedHaar F v.val))
    (fun z => fArch z * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
      (PoissonArch.tracePairing F z y.1 : ℂ)))
    (fun z : PoissonFinite.Space F T => ∏ v : T,
      φ v (z v) * (localFiniteCharacter F v.val (-z v * y.2 v) : ℂ))
  have hj := MeasureTheory.integral_fintype_prod_eq_prod
    (μ := fun v : T => localNormalizedHaar F v.val)
    (fun (v : T) z => φ v z * (localFiniteCharacter F v.val (-z * y.2 v) : ℂ))
  exact hi.trans (congrArg (fun c => PoissonArch.traceFourier F fArch y.1 * c)
    (by simpa only [SArithmeticData.finiteTraceFourier, hHaar, hCharacter] using hj))

private theorem recombination_chirp_tensor
    (hCharacter : ∀ v, ResidueTrace.localTraceCharacter v = localFiniteCharacter F v)
    (b : F) (fArch : PoissonArch.Space F → ℂ)
    (φ : (v : T) → v.val.adicCompletion F → ℂ) :
    chirp F T b (fun z => fArch z.1 * ∏ v : T, φ v (z.2 v)) =
      fun z => archChirp F b fArch z.1 * ∏ v : T,
        A.finiteQuadraticMultiplier v.val (algebraMap F (v.val.adicCompletion F) b)
          (φ v) (z.2 v) := by
  funext x
  have hphase := recombination_phase_eq_traceCharacter F T
    (PoissonS.localProductToSpace F T
      (sLocalDiagonal F T b * (PoissonS.localProductToSpace F T).symm x)) x
  rw [AddEquiv.symm_apply_apply] at hphase
  have heq : (sLocalDiagonal F T b * (PoissonS.localProductToSpace F T).symm x) *
      (PoissonS.localProductToSpace F T).symm x =
      sLocalDiagonal F T b * ((PoissonS.localProductToSpace F T).symm x) ^ 2 := by ring
  rw [heq] at hphase
  unfold chirp
  rw [← hphase]
  simp only [PoissonS.tracePhase, recombination_fieldMul_coordinates, archChirp,
    SArithmeticData.finiteQuadraticMultiplier, hCharacter, Finset.prod_mul_distrib]
  have hfin (v : T) :
      (PoissonS.localProductToSpace F T
        (sLocalDiagonal F T b * (PoissonS.localProductToSpace F T).symm x)).2 v * x.2 v =
      algebraMap F (v.val.adicCompletion F) b * (x.2 v) ^ 2 := by
    change (algebraMap F (v.val.adicCompletion F) b * x.2 v) * x.2 v = _
    ring
  simp_rw [hfin]
  ring

private theorem recombination_dilation_tensor (c : F)
    (fArch : PoissonArch.Space F → ℂ)
    (φ : (v : T) → v.val.adicCompletion F → ℂ) :
    dilation F T c (fun z => fArch z.1 * ∏ v : T, φ v (z.2 v)) =
      fun z => archDilation F c fArch z.1 * ∏ v : T,
        A.finiteDilation v.val (algebraMap F (v.val.adicCompletion F) c) (φ v) (z.2 v) := by
  funext x
  simp only [dilation, recombination_fieldMul_coordinates, archDilation,
    SArithmeticData.finiteDilation]
  rfl

theorem quadratic_operator_on_tensor (a : Fˣ)
    (fArch : SchwartzMap (PoissonArch.Space F) ℂ)
    (φ : (v : T) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v))
    (hHaar : ∀ v : HeightOneSpectrum (𝓞 F),
      A.finiteTraceHaar v = localNormalizedHaar F v)
    (hCharacter : ∀ v : HeightOneSpectrum (𝓞 F),
      ResidueTrace.localTraceCharacter v = localFiniteCharacter F v)
    (harch : PoissonArch.traceFourier F
        (archChirp F (a : F) (PoissonArch.traceFourier F fArch)) =
      fun y => ((Real.sqrt (∏ w : InfinitePlace F,
          w (2 * (a : F)) ^ w.mult))⁻¹ : ℂ) *
        archChirp F (-1 / (4 * (a : F)))
          (archDilation F (1 / (2 * (a : F)))
            (PoissonArch.traceFourier F
              (archChirp F (-1 / (4 * (a : F))) fArch))) y)
    (hfinite : let aLocal : (v : T) → (v.val.adicCompletion F)ˣ := fun v =>
        Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom a
      ∀ y : PoissonFinite.Space F T,
      (∏ v : T, A.finiteTraceFourier v.val
        (A.finiteQuadraticMultiplier v.val (aLocal v : v.val.adicCompletion F)
          (A.finiteTraceFourier v.val (φ v))) (y v)) =
        (∏ v : T, A.finiteGamma v.val (aLocal v)) *
          ((Real.sqrt (∏ v : T,
            ‖(2 : v.val.adicCompletion F) * (aLocal v : v.val.adicCompletion F)‖))⁻¹ : ℂ) *
          (∏ v : T, A.finiteQuadraticMultiplier v.val
            (-1 / (4 * (aLocal v : v.val.adicCompletion F)))
            (A.finiteDilation v.val (1 / (2 * (aLocal v : v.val.adicCompletion F)))
              (A.finiteTraceFourier v.val
                (A.finiteQuadraticMultiplier v.val
                  (-1 / (4 * (aLocal v : v.val.adicCompletion F))) (φ v)))) (y v)))
    (hmodule : ((Real.sqrt (PoissonS.productModule F T (2 * (a : F))))⁻¹ : ℂ) =
        ((Real.sqrt (∏ w : InfinitePlace F, w (2 * (a : F)) ^ w.mult))⁻¹ : ℂ) *
          ∏ v : T, ((Real.sqrt
            ‖algebraMap F (v.val.adicCompletion F) (2 * (a : F))‖)⁻¹ : ℂ)) :
    fourier F T (chirp F T (a : F)
        (fourier F T (PoissonS.tensorFunction F T fArch φ))) =
      fun y =>
        ((∏ v ∈ T, A.finiteGamma v
          (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)) *
          ((Real.sqrt (PoissonS.productModule F T (2 * (a : F))))⁻¹ : ℂ)) *
        chirp F T (-1 / (4 * (a : F)))
          (dilation F T (1 / (2 * (a : F)))
            (fourier F T (chirp F T (-1 / (4 * (a : F)))
              (PoissonS.tensorFunction F T fArch φ)))) y := by
  unfold PoissonS.tensorFunction
  rw [recombination_fourier_tensor A T hHaar hCharacter,
    recombination_chirp_tensor A T hCharacter,
    recombination_fourier_tensor A T hHaar hCharacter,
    recombination_chirp_tensor A T hCharacter,
    recombination_fourier_tensor A T hHaar hCharacter,
    recombination_dilation_tensor A T,
    recombination_chirp_tensor A T hCharacter]
  funext y
  rw [harch]
  have hf := hfinite y.2
  dsimp only at hf
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hf
  simp only [map_div₀, map_neg, map_one, map_mul, map_ofNat] at *
  rw [hf, hmodule]
  have hg : (∏ v ∈ T, A.finiteGamma v
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)) =
      ∏ v : T, A.finiteGamma v.val
        (Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom a) := (Finset.prod_attach T _).symm
  rw [hg]
  rw [Real.sqrt_prod Finset.univ (fun v _ => norm_nonneg _)]
  simp only [Complex.ofReal_prod, Finset.prod_inv_distrib,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  ac_rfl

end DedekindZetaZeroFree.QuadraticRawProduct.TensorKernelSteps

end

end

section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.QuadraticRawProduct

variable {F : Type} [Field F] [NumberField F]

theorem tensor_finiteTraceHaar_eq (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) :
    A.finiteTraceHaar v = localNormalizedHaar F v := by
  apply FiniteOscillatoryStabilization.finiteTraceHaar_eq_localNormalizedHaar_of_integerVolume
  rw [PoissonS.integerVolume,
    FiniteOscillatoryStabilization.globalDifferentExponent_eq_localDifferentExponent F v,
    zpow_natCast, localHalfDifferentFactor_eq_inv_sqrt F v,
    localDifferentNorm, Nat.cast_pow, one_div]

private alias tensor_primeBelow_eq_adapter := DedekindZetaZeroFree.SArithmeticData.OscillatoryIntegralStabilization.prime_eq

alias tensor_finiteCharacter_eq := DedekindZetaZeroFree.SArithmeticData.OscillatoryIntegralStabilization.char_eq

theorem tensor_finite_quadratic_operator (A : SArithmeticData F)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (a : (v : T) → (v.val.adicCompletion F)ˣ)
    (φ : (v : T) → v.val.adicCompletion F → ℂ)
    (hφ : ∀ v, IsLocallyConstant (φ v) ∧ HasCompactSupport (φ v))
    (y : PoissonFinite.Space F T) :
    (∏ v : T, A.finiteTraceFourier v.val
      (A.finiteQuadraticMultiplier v.val (a v : v.val.adicCompletion F)
        (A.finiteTraceFourier v.val (φ v))) (y v)) =
      (∏ v : T, A.finiteGamma v.val (a v)) *
        ((Real.sqrt (∏ v : T,
          ‖(2 : v.val.adicCompletion F) * (a v : v.val.adicCompletion F)‖))⁻¹ : ℂ) *
        (∏ v : T, A.finiteQuadraticMultiplier v.val
          (-1 / (4 * (a v : v.val.adicCompletion F)))
          (A.finiteDilation v.val (1 / (2 * (a v : v.val.adicCompletion F)))
            (A.finiteTraceFourier v.val
              (A.finiteQuadraticMultiplier v.val
                (-1 / (4 * (a v : v.val.adicCompletion F))) (φ v)))) (y v)) := by
  have hlocal (v : T) := congrFun
    (A.finiteTraceFourier_quadratic_operator v.val (a v) (φ v) (hφ v)) (y v)
  simp_rw [hlocal, Finset.prod_mul_distrib]
  congr 1
  rw [Real.sqrt_prod Finset.univ (fun v _ => norm_nonneg _)]
  simp only [Complex.ofReal_prod, Complex.ofReal_inv, Finset.prod_inv_distrib]

theorem quadratic_module_factorization
    (T : Finset (HeightOneSpectrum (𝓞 F))) (b : F) :
    ((Real.sqrt (PoissonS.productModule F T b))⁻¹ : ℂ) =
      ((Real.sqrt (∏ w : InfinitePlace F, w b ^ w.mult))⁻¹ : ℂ) *
        ∏ v : T, ((Real.sqrt ‖algebraMap F (v.val.adicCompletion F) b‖)⁻¹ : ℂ) := by
  have hfinite : (∏ v ∈ T, FinitePlace.mk v b) =
      ∏ v : T, ‖algebraMap F (v.val.adicCompletion F) b‖ := by
    rw [← Finset.prod_attach]
    apply Finset.prod_congr rfl
    intro v _
    rfl
  unfold PoissonS.productModule
  rw [hfinite, Real.sqrt_mul (Finset.prod_nonneg fun w _ => pow_nonneg (apply_nonneg w b) _)]
  rw [Complex.ofReal_mul, mul_inv_rev, mul_comm]
  congr 1
  rw [Real.sqrt_prod _ (fun v _ => norm_nonneg _), Finset.prod_inv_distrib,
    ← Complex.ofReal_prod]

theorem tensor_quadratic_operator (A : SArithmeticData F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (a : Fˣ)
    (f : PoissonS.Space F T → ℂ) (hf : f ∈ testSpace F T) :
    fourier F T (chirp F T (a : F) (fourier F T f)) =
      fun y =>
        ((∏ v ∈ T, A.finiteGamma v
          (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)) *
          ((Real.sqrt (PoissonS.productModule F T (2 * (a : F))))⁻¹ : ℂ)) *
        chirp F T (-1 / (4 * (a : F)))
          (dilation F T (1 / (2 * (a : F)))
            (fourier F T (chirp F T (-1 / (4 * (a : F))) f))) y := by
  obtain ⟨L, R, hL, hR⟩ := TensorKernelSteps.quadratic_compositions_linear A T
    (a : F) (-1 / (4 * (a : F))) (1 / (2 * (a : F))) ((∏ v ∈ T, A.finiteGamma v
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)) *
      ((Real.sqrt (PoissonS.productModule F T (2 * (a : F))))⁻¹ : ℂ))
  have heq : ∀ g (hg : g ∈ testSpace F T), L ⟨g, hg⟩ = R ⟨g, hg⟩ := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨fArch, φ, hl, hs, rfl⟩ := hg
      rw [hL, hR]
      exact TensorKernelSteps.quadratic_operator_on_tensor A T a fArch φ hl hs
        (tensor_finiteTraceHaar_eq A) tensor_finiteCharacter_eq
        (TensorKernelSteps.archimedean_quadratic_operator A a fArch)
        (fun y => tensor_finite_quadratic_operator A T
          (fun v => Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom a)
          φ (fun v => ⟨hl v, hs v⟩) y)
        (quadratic_module_factorization T (2 * (a : F)))
    | zero =>
      change L 0 = R 0
      simp only [map_zero]
    | add g h hg hh ihg ihh =>
      change L (⟨g, hg⟩ + ⟨h, hh⟩) = R (⟨g, hg⟩ + ⟨h, hh⟩)
      rw [map_add, map_add, ihg, ihh]
    | smul c g hg ih =>
      change L (c • ⟨g, hg⟩) = R (c • ⟨g, hg⟩)
      rw [map_smul, map_smul, ih]
  exact (hL ⟨f, hf⟩).symm.trans ((heq f hf).trans (hR ⟨f, hf⟩))

end DedekindZetaZeroFree.QuadraticRawProduct

end

end
