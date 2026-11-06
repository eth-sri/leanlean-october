module
public import OAI.NumberTheory.DirichletL.CubicSieve.RadialProfiles
public import OAI.NumberTheory.DirichletL.CubicSieve.CanonicalLogEnergy

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set

namespace CubicEisenstein

section
open scoped LineDeriv

def kernelCoordinateLaplacian (f : kernelSmoothTests) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,
    fderiv ℝ (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) p
      (euclideanCoordinateVector j))+
    (p 2:ℂ)*fderiv ℝ (kernelTestField f) p (euclideanCoordinateVector 2)

lemma kernelCoreLift_laplacian (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : p∈kernelChartCore χ) :
    upperPositiveLaplacian (kernelCoreLift χ f) p=kernelCoordinateLaplacian f p := by
  have he := kernelCoreLift_eventually_eq χ f p hp
  have hd (j : Fin 3) : (fun q => fderiv ℝ (kernelCoreLift χ f) q (euclideanCoordinateVector j))=ᶠ[𝓝 p]
      (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) :=
    (he.fderiv (𝕜 := ℝ)).mono (fun q hq => congrArg (fun d => d (euclideanCoordinateVector j)) hq)
  have hdd (j : Fin 3) :
      (∂_{euclideanCoordinateVector j} (∂_{euclideanCoordinateVector j} (kernelCoreLift χ f))) p=
        fderiv ℝ (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) p
          (euclideanCoordinateVector j) := by
    change fderiv ℝ (fun q => fderiv ℝ (kernelCoreLift χ f) q (euclideanCoordinateVector j)) p
      (euclideanCoordinateVector j)=_
    rw [(hd j).fderiv_eq]
  simp only [upperPositiveLaplacian,kernelCoordinateLaplacian,hdd,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,he.fderiv_eq]

lemma kernelDirichletForm_sum_right {ι : Type*} (f : kernelSmoothTests)
    (t : Finset ι) (g : ι→kernelSmoothTests) :
    kernelDirichletForm f (∑i∈t,g i)=∑i∈t,kernelDirichletForm f (g i) := by
  induction t using Finset.induction_on with
  | empty =>
    have hz := kernelDirichletForm_smul_right 0 f (0 : kernelSmoothTests)
    simpa only [Finset.sum_empty,zero_smul,zero_mul] using hz
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi,kernelDirichletForm_add_right,ih]

end


lemma kernelL2_inner_toLp_smooth (A : KernelQuotient→ℂ)
    (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel)) (g : kernelSmoothTests) :
    inner ℂ (hA.toLp A) (kernelSmoothTestsToL2 g)=
      ∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  calc
    _ = ∫q,inner ℂ ((hA.toLp A) q) (kernelSmoothTestsToL2 g q)
        ∂integralQuotientVolume globalKubotaKernel := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hA.coeFn_toLp,(kernelSmoothTests_memLp g).coeFn_toLp] with q hq hg
      change inner ℂ ((hA.toLp A) q) (((kernelSmoothTests_memLp g).toLp g.1) q)=_
      rw [hq,hg,RCLike.inner_apply]
      simp only [RCLike.star_def,mul_comm]

end CubicEisenstein

section

namespace SecondPassIntegration
open SecondPassArithmetic

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

end SecondPassIntegration

namespace SecondPassArithmetic
open FirstPassCubeLabels

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

end SecondPassArithmetic
end


namespace CanonicalRowCompletion

open CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve

theorem finite_integral_energy_polynomial {κ : Type*} [Fintype κ]
    (b : ℝ → ℂ) (φ : κ → ℝ → ℂ) (d : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hb : Integrable (fun t => ‖b t‖*(1+|t|)^d))
    (hφ : ∀ k, Integrable (fun t => b t*φ k t))
    (hbound : ∀ t, (∑ k, ‖φ k t‖^2) ≤ E*(1+|t|)^(2*d)) :
    (∑ k, ‖∫ t : ℝ, b t*φ k t‖^2) ≤
      E*(∫ t : ℝ, ‖b t‖*(1+|t|)^d)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : ℝ → EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t*φ k t)
  have hF (t : ℝ) : ‖F t‖ ≤ (‖b t‖*(1+|t|)^d)*Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ k, ‖b t*φ k t‖^2) ≤ _
    simp only [norm_mul,mul_pow,← Finset.mul_sum,Real.sq_sqrt hE]
    have hp : (1+|t|)^(2*d) = ((1+|t|)^d)^2 := by
      rw [← pow_mul,Nat.mul_comm d 2]
    calc
      _ ≤ ‖b t‖^2 * (E*(1+|t|)^(2*d)) :=
        mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
      _ = _ := by rw [hp]; ring
  have he : (∫ t : ℝ, F t) = e.symm (fun k => ∫ t : ℝ, b t*φ k t) := by
    rw [show F = (fun t => e.symm (fun k => b t*φ k t)) from rfl,
      e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫ t : ℝ, b t*φ k t)‖ ≤
      (∫ t : ℝ, ‖b t‖*(1+|t|)^d)*Real.sqrt E := by
    rw [← he,← integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _)
      (Filter.Eventually.of_forall hF)
  have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE] at hh
  change (∑ k, ‖∫ t : ℝ, b t*φ k t‖^2) ≤
    (∫ t : ℝ, ‖b t‖*(1+|t|)^d)^2 * E at hh
  simpa only [mul_comm] using hh

theorem norm_add_sum_sq_le {κ : Type*} (s : Finset κ) (a : ℂ) (b : κ → ℂ) :
    ‖a + ∑ k ∈ s, b k‖^2 ≤ 2*(‖a‖^2 + s.card*∑ k ∈ s, ‖b k‖^2) := by
  have hs : ‖∑ k ∈ s, b k‖^2 ≤ (s.card : ℝ)*∑ k ∈ s, ‖b k‖^2 := by
    calc
      _ ≤ (∑ k ∈ s, ‖b k‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by
        simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one]
          using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun k => ‖b k‖)
  have ha := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a (∑ k ∈ s, b k)) 2
  nlinarith [sq_nonneg (‖a‖ - ‖∑ k ∈ s, b k‖)]

end CanonicalRowCompletion

namespace CanonicalCoefficientClass

section
open SecondPassArithmetic (rayMonoid conjugateRayMonoid rayMonoid_apply conjugateRayMonoid_apply
  FirstCoreIndex firstCoreTwist sideRayMonoid SecondRayIndex secondRayMinus secondRayPlus)
open RayFourExpansion (RayCharacter)

def IsBaseRayTwist (base Ψ : ActualEisensteinCubic.O→*ℂ) : Prop :=
  Ψ=base ∨ ∃χ : RayCharacter, Ψ=rayMonoid χ*base

lemma rayMonoid_mul (χ η : RayCharacter) : rayMonoid (χ*η)=rayMonoid χ*rayMonoid η := by
  ext x
  simp only [rayMonoid_apply,RayFourExpansion.rayCharacter,MulChar.mul_apply,MonoidHom.mul_apply]

lemma conjugateRayMonoid_eq (χ : RayCharacter) : conjugateRayMonoid χ=rayMonoid (star χ) := by
  ext x
  simp only [conjugateRayMonoid_apply,rayMonoid_apply,RayFourExpansion.rayCharacter,MulChar.star_apply]

lemma IsBaseRayTwist.mul_ray {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ) (χ : RayCharacter) :
    IsBaseRayTwist base (rayMonoid χ*Ψ) := by
  rcases hΨ with h|⟨η,h⟩
  · exact Or.inr ⟨χ,by rw [h]⟩
  · exact Or.inr ⟨χ*η,by rw [h,rayMonoid_mul,mul_assoc]⟩

lemma firstCoreTwist_single_ray (side : Bool) (χ : RayCharacter) (Ψ : ActualEisensteinCubic.O→*ℂ)
    (r : FirstCoreIndex) :
    firstCoreTwist side χ Ψ r =
      rayMonoid ((if side then star χ else χ)*FirstPassCubeLabels.coreRayCharacter side r.1 r.2.2)*Ψ := by
  rw [rayMonoid_mul]
  have hcore : FirstPassCubeLabels.coreRayTwist side r.1 r.2.2 =
      rayMonoid (FirstPassCubeLabels.coreRayCharacter side r.1 r.2.2) := rfl
  unfold firstCoreTwist sideRayMonoid
  rw [hcore]
  cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true,conjugateRayMonoid_eq] <;> ac_rfl

lemma IsBaseRayTwist.firstCore {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (side : Bool) (χ : RayCharacter) (r : FirstCoreIndex) :
    IsBaseRayTwist base (firstCoreTwist side χ Ψ r) := by
  rw [firstCoreTwist_single_ray]
  exact hΨ.mul_ray _

lemma secondRayMinus_single_ray (Ψ : ActualEisensteinCubic.O→*ℂ) (r : SecondRayIndex) :
    secondRayMinus Ψ r=rayMonoid (star r.2.2*star r.1.2)*Ψ := by
  rw [rayMonoid_mul]
  simp only [secondRayMinus,conjugateRayMonoid_eq,mul_assoc]

lemma secondRayPlus_single_ray (Ψ : ActualEisensteinCubic.O→*ℂ) (r : SecondRayIndex) :
    secondRayPlus Ψ r=rayMonoid (r.2.1*star r.1.1)*Ψ := by
  rw [rayMonoid_mul]
  simp only [secondRayPlus,conjugateRayMonoid_eq,mul_assoc]

lemma IsBaseRayTwist.secondMinus {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (r : SecondRayIndex) : IsBaseRayTwist base (secondRayMinus Ψ r) := by
  rw [secondRayMinus_single_ray]
  exact hΨ.mul_ray _

lemma IsBaseRayTwist.secondPlus {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (r : SecondRayIndex) : IsBaseRayTwist base (secondRayPlus Ψ r) := by
  rw [secondRayPlus_single_ray]
  exact hΨ.mul_ray _

lemma IsBaseRayTwist.norm_le {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (hbase : ∀x,‖base x‖≤1) (x : ActualEisensteinCubic.O) : ‖Ψ x‖≤1 := by
  rcases hΨ with rfl|⟨χ,rfl⟩
  · exact hbase x
  · rw [MonoidHom.mul_apply,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (FiniteRayExpansion.norm_char_le_one χ _)).trans (hbase x)

def FactorsModulo (Q : Ideal ActualEisensteinCubic.O) (Ψ : ActualEisensteinCubic.O→*ℂ) : Prop :=
  ∀x y : ActualEisensteinCubic.O,x-y∈Q → Ψ x=Ψ y

end

open ActualEisensteinCoordinates (eval coords eval_coords)
open ShortDraftLatticeCount (qNat qO_nonneg coords_eval)

lemma norm_eval_mod (m : ℕ) (a b : ℤ) :
    (Ideal.absNorm (Ideal.span {eval a b}) : ZMod m)=
      (a : ZMod m)^2-(a : ZMod m)*(b : ZMod m)+(b : ZMod m)^2 := by
  have hi : (Ideal.absNorm (Ideal.span {eval a b}) : ℤ)=a^2-a*b+b^2 := by
    rw [←qNat_eq_absNorm_span]
    change ((ShortDraftLatticeCount.q (coords (eval a b))).toNat : ℤ)=_
    rw [Int.toNat_of_nonneg (qO_nonneg _),coords_eval]
    rfl
  have hz := congrArg (fun k : ℤ => (k : ZMod m)) hi
  push_cast at hz
  exact hz

theorem normCharacter_factorsModulo {m : ℕ} (χ : DirichletCharacter ℂ m) :
    FactorsModulo (Ideal.span {(m : ActualEisensteinCubic.O)}) (InitialMeanSquare.normCharacter χ) := by
  intro x y hxy
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hxy
  let c := (coords y).1
  let d := (coords y).2
  let e := (coords z).1
  let f := (coords z).2
  have hy : y=eval c d := (eval_coords y).symm
  have hx : x=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
    calc
      x=y+(m : ActualEisensteinCubic.O)*z := by linear_combination hz
      _=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
        rw [hy,←eval_coords z]
        dsimp [eval,c,d,e,f]
        push_cast
        ring
  change χ (Ideal.absNorm (Ideal.span {x}))=χ (Ideal.absNorm (Ideal.span {y}))
  congr 1
  rw [hx,hy,norm_eval_mod,norm_eval_mod]
  simp

def fixedBaseConductor (m : ℕ) : Ideal ActualEisensteinCubic.O := Ideal.span {(m : ActualEisensteinCubic.O)}*Ideal.span {(4 : ActualEisensteinCubic.O)}

lemma fixedBaseConductor_principal (m : ℕ) :
    fixedBaseConductor m=Ideal.span {((4*m : ℕ) : ActualEisensteinCubic.O)} := by
  rw [fixedBaseConductor,Ideal.span_singleton_mul_span_singleton]
  congr 1
  push_cast
  ring_nf

lemma fixedBaseConductor_ne_zero (m : ℕ) (hm : m≠0) : fixedBaseConductor m≠0 := by
  rw [fixedBaseConductor_principal]
  change Ideal.span {((4*m : ℕ) : ActualEisensteinCubic.O)}≠⊥
  rw [ne_eq,Ideal.span_singleton_eq_bot]
  exact_mod_cast Nat.mul_ne_zero (by decide : (4:ℕ)≠0) hm
