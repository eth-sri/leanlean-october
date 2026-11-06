module
public import OAI.NumberTheory.DirichletL.Inversion.InitialPoissonBridge
public import OAI.NumberTheory.DirichletL.Inversion.InitialProfile
public import OAI.NumberTheory.DirichletL.Inversion.InitialArithmetic

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT EisensteinSchwartzPoisson UniqueFactorizationMonoid CanonicalQuadraticSieve SevenEighths.InverseInitialPoissonBridge SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialProfile
namespace SevenEighths.InverseInitialKernelBridge

local notation "Eis" => ActualEisensteinCubic.O
local notation "N" => fun I : Ideal Eis => (Ideal.absNorm I : ℝ)
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal Eis)
  [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
  (hg : ∀ i, goodLambda ∉ P i)

def pairRow (S T : Finset ι) (h : Eis) : ℂ :=
  finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T) h

def pairGauss (S T : Finset ι) : ℂ :=
  canonicalNormalizedGauss (activePrimes P S T)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val) (activeExponent S T)

def pairCoordinates (S T E : Finset ι) (h : Eis) : Fin 6 → ℝ :=
  ![N (∏ i ∈ S∩T,P i), N (∏ i ∈ E,P i), 1, ‖eisEmbedding h‖^2,
    N (∏ i ∈ S\T,P i), N (∏ i ∈ T\S,P i)]

def pairArithmetic (S T E : Finset ι) (h : Eis) : ℂ :=
  pairGauss P hinj hg S T * (moebius (∏ i ∈ E,P i) : ℂ) *
    pairRow P hg S T (primeSubsetGenerator P E) * star (pairRow P hg S T h)

private theorem physicalKernel_vector (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (Z D m q₀ q₁ q₂ q₃ q₄ q₅ : ℝ) :
    physicalKernel W₁ W₂ Φ Z D m ![q₀,q₁,q₂,q₃,q₄,q₅] =
      ((Z^(-D)*Z^m/(q₁*q₂*Real.sqrt (q₄*q₅)) : ℝ) : ℂ)*
        W₁ (q₀*q₂*q₄/Z^D)*W₂ (q₀*q₂*q₅/Z^D)*
          paperRadialFourier Φ (Z^m*q₃/(q₁*q₂^2*q₄*q₅)) := rfl

def bareOverlapCoefficient (P j : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (c : Ideal Eis) : ℂ :=
  (moebius c : ℂ)*η c*a (reconstruct P j c)

def residualOverlapWindow (P j : Ideal Eis) (W : ℝ → ℂ) (Z z G : ℝ) (x : ℝ) : ℂ :=
  W (((N j/Z^G)*x)/((N (residual P j))/Z^(z-G)))

theorem overlapCoefficient_residual (P j c : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) :
    overlapResidualCoefficient P j η a W Z r z G c =
      bareOverlapCoefficient P j η a c *
        residualOverlapWindow P j W Z z G (N c/Z^(r+z-2*G)) := rfl

def physicalCoordinates (C d s n₁ n₂ : Ideal Eis) (h : Eis) : Fin 6 → ℝ :=
  ![N C,N d,N s,‖eisEmbedding h‖^2,N n₁,N n₂]

theorem physicalCoordinates_pos (C d s n₁ n₂ : Ideal Eis) (h : Eis)
    (hC : C ≠ 0) (hd : d ≠ 0) (hs : s ≠ 0) (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (hh : h ≠ 0) :
    ∀ i, 0 < physicalCoordinates C d s n₁ n₂ h i := by
  have hp (I : Ideal Eis) (hI : I ≠ 0) : 0 < N I := by
    change 0 < (Ideal.absNorm I : ℝ)
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  intro i
  fin_cases i
  · exact hp C hC
  · exact hp d hd
  · exact hp s hs
  · exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh))
  · exact hp n₁ h₁
  · exact hp n₂ h₂

theorem physicalKernel_common_factor (C d s n₁ n₂ : Ideal Eis) (h : Eis)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) :
    physicalKernel W₁ W₂ Φ Z D m (physicalCoordinates C d 1 (s*n₁) (s*n₂) h) =
      physicalKernel W₁ W₂ Φ Z D m (physicalCoordinates C d s n₁ n₂ h) := by
  have hroot : Real.sqrt ((N s*N n₁)*(N s*N n₂)) = N s*Real.sqrt (N n₁*N n₂) := by
    rw [show (N s*N n₁)*(N s*N n₂) = (N s)^2*(N n₁*N n₂) from by ring_nf,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  unfold physicalCoordinates
  rw [physicalKernel_vector,physicalKernel_vector]
  simp only [map_one,Nat.cast_one,map_mul,Nat.cast_mul,mul_one,one_pow]
  rw [hroot]
  have hl : N C*(N s*N n₁)/Z^D = N C*N s*N n₁/Z^D := by ring_nf
  have hr : N C*(N s*N n₂)/Z^D = N C*N s*N n₂/Z^D := by ring_nf
  have hk : Z^m*‖eisEmbedding h‖^2/(N d*(N s*N n₁)*(N s*N n₂)) =
      Z^m*‖eisEmbedding h‖^2/(N d*(N s)^2*N n₁*N n₂) := by ring_nf
  rw [hl,hr,hk]
  push_cast
  ring_nf

open InverseInitialArithmetic SecondPassArithmetic

omit [DecidableEq ι] [∀ i, (P i).IsMaximal] in
theorem pairDivisor_span (E : Finset ι) :
    Ideal.span {primeSubsetGenerator P E} = ∏ i ∈ E,P i :=
  span_idealGenerator _

end SevenEighths.InverseInitialKernelBridge

end

end OAI
