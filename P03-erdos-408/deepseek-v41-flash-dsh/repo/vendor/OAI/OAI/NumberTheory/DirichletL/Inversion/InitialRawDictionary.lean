module

public import OAI.NumberTheory.DirichletL.Inversion.InitialConjugateEnergy
public import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge
public import OAI.NumberTheory.DirichletL.Hecke.DetectorRowSpecialization

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialRawDictionary
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeRowClosure InverseInitialPoissonBridge InverseInitialConjugateEnergy ConcretePrimeRowBridge CompletedGauss UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def twistedProfile (W : ℝ → ℂ) (σ freq : ℝ) (x : ℝ) : ℂ :=
  W x*(x:ℂ)^(-shift σ freq)

theorem finite_source_cover (W : ℝ → ℂ) (D b : ℝ) (hD : 0<D)
    (hW : ∀x,W x≠0 → x≤b) (I : Ideal O) (hI : I≠0)
    (hi : W ((I.absNorm:ℝ)/D)≠0) : I∈idealsUpTo ⌈D*b⌉₊ := by
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI),?_⟩
  have hb := (div_le_iff₀ hD).mp (hW _ hi)
  have hn : (I.absNorm:ℝ)≤(⌈D*b⌉₊:ℝ) := by
    calc
      (I.absNorm:ℝ)≤D*b := by simpa only [mul_comm] using hb
      _≤(⌈D*b⌉₊:ℝ) := Nat.le_ceil _
  exact_mod_cast hn

theorem normalization_eq (Z r : ℝ) (hZ : 0<Z) :
    ((Z^r:ℝ):ℂ)^(-(1/2:ℂ))=((Z^(-r/2):ℝ):ℂ) := by
  have he : (-(1/2:ℂ))=((-(1/2:ℝ)):ℂ) := by norm_num
  calc
    _ = (((Z^r)^(-(1/2:ℝ)):ℝ):ℂ) := by
      simpa only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,
        Complex.ofReal_ofNat] using (Complex.ofReal_cpow
          (Real.rpow_nonneg hZ.le r) (-(1/2:ℝ))).symm
    _ = _ := ?_
  rw [←Real.rpow_mul hZ.le]
  congr 2
  ring

theorem inverse_eq_initial_source (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ → ℂ) (Z r σ freq : ℝ) (hZ : 0<Z) (S : Finset (Ideal O))
    (hcover : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    polynomial χ true W (Z^r) σ freq=
      originalTotalPolynomial S 1 η (fun _=>1)
        (twistedProfile W σ freq) Z r 0 u := by
  rw [polynomial_eq_finite χ true W (Z^r) σ freq S hcover,normalization_eq Z r hZ]
  unfold originalTotalPolynomial
  simp only [add_zero,map_one,mul_one]
  apply congrArg (fun x:ℂ=>((Z^(-r/2):ℝ):ℂ)*x)
  apply Finset.sum_congr rfl
  intro I hI
  simp only [coefficient,ite_true,hrow,heckeIdealCharacter_apply,
    twistedProfile]
  ring

theorem originalTotal_supported_source (S : Finset (Ideal O)) (P : Ideal O)
    (η : Ideal O →* ℂ) (hη : ∀I,¬CanonicalQuadraticSieve.Supported I → η I=0)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z : ℝ) (u : O) :
    originalTotalPolynomial S P η a W Z r z u=
      originalTotalPolynomial (S.filter CanonicalQuadraticSieve.Supported) P η a W Z r z u := by
  unfold originalTotalPolynomial
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs with hi
  · rfl
  · simp only [heckeIdealCharacter_apply,hη I hi,zero_mul,mul_zero]

def fixedBase (η : Character) (m f : O) : Ideal O →* ℂ :=
  heckeIdealCharacter (idealCoeff η).toMonoidHom (m^6*f^4)

theorem fixedBase_row (η χ : Character) (m f z : O)
    (hrow : ∀n:O,elementCoeff χ n=
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n) (I : Ideal O) :
    idealCoeff χ I=fixedBase η m f I*CanonicalRowCompletion.idealRowHom z I := by
  rw [HeckeRowClosure.idealCoeff_eq_row η χ m f z hrow,
    CanonicalRowCompletion.idealRowHom_argument_mul]
  change idealCoeff η I*(CanonicalRowCompletion.idealRowHom (m^6*f^4) I*
    CanonicalRowCompletion.idealRowHom z I)=
    (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*f^4) I)*
    CanonicalRowCompletion.idealRowHom z I
  ring

theorem fixedBase_zero_unsupported (η : Character) (m f : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (I : Ideal O) (hI : ¬CanonicalQuadraticSieve.Supported I) : fixedBase η m f I=0 := by
  by_cases hi : I=0
  · subst I
    change idealCoeff η 0*_=0
    rw [map_zero,zero_mul]
  let n := ConcretePrimeRowBridge.idealGenerator I
  have hn : n≠0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hi
  have hs : Ideal.span {n}=I := ConcretePrimeRowBridge.span_idealGenerator I
  have he := CanonicalRowCompletion.rowTwist_zero_of_not_supported
    (elementHom η) m f 1 n hmLam hm2 (by rwa [hs])
  change elementCoeff η n*CanonicalRowCompletion.idealRowHom (m^6*f^4*1)
    (Ideal.span {n})=0 at he
  rw [mul_one,hs,←idealCoeff_span η hn,hs] at he
  exact he

end SevenEighths.InverseInitialRawDictionary

end

end OAI
