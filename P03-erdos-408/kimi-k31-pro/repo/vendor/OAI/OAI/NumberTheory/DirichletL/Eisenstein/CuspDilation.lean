module

public import OAI.NumberTheory.DirichletL.Eisenstein.ArbitraryCuspPullback

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators Classical SchwartzMap


namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedTraceLambda : Eis := 1+2*omega

lemma ramifiedEmbedding_traceLambda : eisEmbedding ramifiedTraceLambda=eisLam := by
  change eisEmbedding (1+2*omega)=1+2*EisensteinEmbedding.omega3
  rw [map_add,map_one,map_mul,map_ofNat,eisEmbedding_omega_actual]

lemma primary_add_three (a r : Eis) (ha : lambda^2∣a-1) :
    lambda^2∣a+3*r-1 := by
  have h3 : (3:Eis)∣a-1 := three_dvd_lambda_sq.trans ha
  exact lambda_sq_dvd_three.trans (by
    convert dvd_add h3 (dvd_mul_right (3:Eis) r) using 1 ;ring)

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def ninthCuspFrequency (h : Eis) : ℂ := cuspFrequency h/3

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma cuspTransition_dilate (A : ℝ) (hA : A≠0) :
    cuspTransition A (2*A)=fun v => cuspTransition 1 2 (v/A) := by
  funext v
  unfold cuspTransition
  congr 1
  field_simp

lemma cuspTransition_dilate_deriv (A v : ℝ) (hA : A≠0) :
    deriv (cuspTransition A (2*A)) v=deriv (cuspTransition 1 2) (v/A)/A := by
  rw [cuspTransition_dilate A hA]
  have hd := (((cuspTransition_contDiff 1 2).differentiable (by simp) (v/A)).hasDerivAt).comp v
    ((hasDerivAt_id v).div_const A)
  simpa [Function.comp_def,id_eq,div_eq_mul_inv] using hd.deriv

lemma cuspTransition_dilate_second (A v : ℝ) (hA : A≠0) :
    deriv (deriv (cuspTransition A (2*A))) v=
      deriv (deriv (cuspTransition 1 2)) (v/A)/A^2 := by
  have he : deriv (cuspTransition A (2*A))=
      fun x => deriv (cuspTransition 1 2) (x/A)/A := by
    funext x
    exact cuspTransition_dilate_deriv A x hA
  rw [he]
  have hc := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff 1 2)).2
  have hd := (((hc.differentiable (by simp) (v/A)).hasDerivAt).comp v
    ((hasDerivAt_id v).div_const A)).div_const A
  simp only [Function.comp_def,id_eq] at hd
  convert hd.deriv using 1; field_simp

def cuspBaseDefectFactor (s : ℂ) (x : ℝ) : ℂ :=
  (x:ℂ)^2*(deriv (deriv (cuspTransition 1 2)) x:ℝ)+
    (2*s-1)*(x:ℂ)*(deriv (cuspTransition 1 2) x:ℝ)

lemma cuspBaseDefectFactor_continuous (s : ℂ) : Continuous (cuspBaseDefectFactor s) := by
  have h1 := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff 1 2)).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  unfold cuspBaseDefectFactor
  exact ((Complex.continuous_ofReal.pow 2).mul (Complex.continuous_ofReal.comp h2.continuous)).add
    ((continuous_const.mul Complex.continuous_ofReal).mul (Complex.continuous_ofReal.comp h1.continuous))

lemma cuspBaseDefectFactor_compact (s : ℂ) : HasCompactSupport (cuspBaseDefectFactor s) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Set.Icc (1:ℝ) 2))
  intro x hx
  by_contra hn
  have hout : x<1 ∨ 2<x := by simpa only [Set.mem_Icc,not_and_or,not_le] using hn
  obtain ⟨h1,h2⟩ := cuspTransition_derivatives 1 2 x (by norm_num) hout
  exact hx (by simp [cuspBaseDefectFactor,h1,h2])

lemma cuspSeedDefectProfile_dilate (A v : ℝ) (hA : A≠0) (s : ℂ) :
    cuspSeedDefectProfile A (2*A) s v=
      positiveHeightPower s v*cuspBaseDefectFactor s (v/A) := by
  rw [cuspSeedDefectProfile,cuspTransition_dilate_deriv A v hA,cuspTransition_dilate_second A v hA]
  unfold cuspBaseDefectFactor
  push_cast
  field_simp

theorem cuspSeedDefectProfile_dilate_bound :
    ∃C : ℝ,0≤C ∧ ∀A : ℝ,1≤A → ∀v : ℝ,
      ‖cuspSeedDefectProfile A (2*A) (4/3) v‖≤C*A^2 := by
  obtain ⟨B,hB⟩ := (cuspBaseDefectFactor_compact (4/3)).exists_bound_of_continuous
    (cuspBaseDefectFactor_continuous (4/3))
  let C := max B 0
  have hC : 0≤C := le_max_right _ _
  have hbound (x : ℝ) : ‖cuspBaseDefectFactor (4/3) x‖≤C := (hB x).trans (le_max_left _ _)
  refine ⟨4*C,by positivity,fun A hA v => ?_⟩
  have hApos : 0<A := lt_of_lt_of_le zero_lt_one hA
  by_cases hv : v∈Set.Icc A (2*A)
  · have hv1 : 1≤v := hA.trans hv.1
    have hvpos : 0<v := hApos.trans_le hv.1
    have hp : ‖positiveHeightPower (4/3) v‖≤v^2 := by
      rw [positiveHeightPower_eq_cpow _ _ hvpos,Complex.norm_cpow_eq_rpow_re_of_pos hvpos]
      norm_num
      have hh := Real.rpow_le_rpow_of_exponent_le hv1 (show (4/3:ℝ)≤2 by norm_num)
      simpa using hh
    rw [cuspSeedDefectProfile_dilate A v hApos.ne',norm_mul]
    have hm := mul_le_mul hp (hbound (v/A)) (norm_nonneg _) (sq_nonneg v)
    calc
      _ ≤ v^2*C := hm
      _ ≤ (2*A)^2*C := mul_le_mul_of_nonneg_right (sq_le_sq₀ hvpos.le (by positivity) |>.mpr hv.2) hC
      _ = (4*C)*A^2 := by ring
  · have hout : v<A ∨ 2*A<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hv
    rw [cuspSeedDefectProfile_zero A (2*A) (4/3) v (by linarith) hout,norm_zero]
    positivity

theorem smoothCuspSeedDefect_dilate_bound :
    ∃C : ℝ,0≤C ∧ ∀A : ℝ,1≤A → ∀w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤C*A^2 := by
  obtain ⟨C,hC,hbound⟩ := cuspSeedDefectProfile_dilate_bound
  exact ⟨C,hC,fun A hA w => cuspCutoffCorrection_norm_le _ _ (by positivity) (hbound A hA) w⟩

open scoped BigOperators Classical Topology InnerProductSpace

lemma movingDefect_product_bound
    (f : KernelQuotient→ℂ) (K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hdec : ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3)
    (hbound : ∀A : ℝ,1≤A → ∀w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤C*A^2)
    (A : ℝ) (hA : 1<A) (q : KernelQuotient) :
    ‖f q‖*‖kernelQuotientDefect A (2*A) (4/3) q‖≤K*C/A := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change ‖f (integralOrbitProjection globalKubotaKernel w)‖*
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤_
    have hApos : 0<A := zero_lt_one.trans hA
    by_cases hz : smoothCuspSeedDefect A (2*A) (4/3) w=0
    · rw [hz,norm_zero,mul_zero]
      positivity
    obtain ⟨r,hr,hr'⟩ := smoothCuspSeedDefect_support A (2*A) (4/3) (by linarith) w hz
    have hheight : 0<cosetHeight r w := hApos.trans_le hr
    have hf : ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/A^3 := by
      apply (hdec w r (hA.trans_le hr)).trans
      apply div_le_div_of_nonneg_left hK (pow_pos hApos 3)
      exact pow_le_pow_left₀ hApos.le hr 3
    calc
      _ ≤ (K/A^3)*(C*A^2) := mul_le_mul hf (hbound A hA.le w) (norm_nonneg _) (by positivity)
      _ = K*C/A := by field_simp

lemma movingDefect_inner_bound
    (F : KernelQuotientL2) (f : KernelQuotient→ℂ)
    (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hdec : ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3)
    (hbound : ∀A : ℝ,1≤A → ∀w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤C*A^2)
    (A : ℝ) (hA : 1<A) :
    ‖inner ℂ F (kernelL2Defect A (2*A) (by linarith) (by linarith) (4/3))‖≤
      (K*C/A)*(integralQuotientVolume globalKubotaKernel).real Set.univ := by
  rw [L2.inner_def]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hrep,kernelL2Defect_ae_eq A (2*A) (by linarith) (by linarith) (4/3)] with q hf hd
  rw [hf,hd,RCLike.inner_apply,norm_mul]
  simpa only [starRingEnd_apply,norm_star,mul_comm] using
    movingDefect_product_bound f K C hK hC hdec hbound A hA q

theorem cubicEisensteinResidue_orthogonal_of_rapid_cusp_decay
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph)
    (f : KernelQuotient→ℂ) (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (K : ℝ) (hK : 0≤K)
    (hdec : ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3) :
    inner ℂ F cubicEisensteinResidue=0 := by
  obtain ⟨C,hC,hbound⟩ := smoothCuspSeedDefect_dilate_bound
  let B : ℝ := (3/2)*(K*C)*(integralQuotientVolume globalKubotaKernel).real Set.univ
  have hB : 0≤B := by dsimp [B]; positivity
  have hb (A : ℝ) (hA : 1<A) : ‖inner ℂ F cubicEisensteinResidue‖≤B/A := by
    have he : cubicEisensteinResidue=
        kernelEisensteinResidueVector A (2*A) (by linarith) (by linarith) :=
      kernelEisensteinResidueVector_cutoff_independent 2 3 A (2*A)
        (by norm_num) (by norm_num) hA (by linarith)
    rw [he,kernelEisensteinResidueVector_pairing,norm_mul]
    norm_num
    calc
      _ ≤ (3/2)*((K*C/A)*(integralQuotientVolume globalKubotaKernel).real Set.univ) :=
        mul_le_mul_of_nonneg_left (movingDefect_inner_bound F f hrep K C hK hC hdec hbound A hA) (by norm_num)
      _ = B/A := by dsimp [B]; ring
    exact hF
  apply norm_eq_zero.mp
  by_contra hn
  have hnpos : 0<‖inner ℂ F cubicEisensteinResidue‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  let A := B/‖inner ℂ F cubicEisensteinResidue‖+2
  have hA : 1<A := by
    have hh := div_nonneg hB hnpos.le
    dsimp [A]
    linarith
  have hh := (le_div_iff₀ (zero_lt_one.trans hA)).mp (hb A hA)
  have he : ‖inner ℂ F cubicEisensteinResidue‖*A=B+2*‖inner ℂ F cubicEisensteinResidue‖ := by
    dsimp [A]
    field_simp

  rw [he] at hh
  linarith

lemma coset_decay_of_cusp_chart_decay
    (f : KernelQuotient→ℂ) (K : ℝ)
    (hdec : ∀M : CubicKubota.levelThree, ∀z : ℂ, ∀v : ℝ, ∀hv : 0<v,1<v →
      ‖f (integralOrbitProjection globalKubotaKernel
        (complexMatrix M • upperPoint z v hv))‖≤K/v^3) :
    ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3 := by
  intro w r
  induction r using Quotient.inductionOn with
  | _ M =>
    intro hr
    change 1<cosetHeight (cosetOf M) w at hr
    change _≤K/(cosetHeight (cosetOf M) w)^3
    rw [cosetHeight_cosetOf] at hr ⊢
    obtain ⟨z,v,hv,hpt⟩ := upperPoint_surjective (complexMatrix M • w)
    have hh : hyperbolicHeight (complexMatrix M • w)=v := by
      rw [←hpt,hyperbolicHeight_upperPoint]
    rw [hh] at hr ⊢
    have he : complexMatrix M⁻¹ • upperPoint z v hv=w := by
      rw [hpt,map_inv,inv_smul_smul]
    simpa only [he] using hdec M⁻¹ z v hv hr

theorem cubicEisensteinResidue_orthogonal_of_cusp_chart_decay
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph)
    (f : KernelQuotient→ℂ) (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (K : ℝ) (hK : 0≤K)
    (hdec : ∀M : CubicKubota.levelThree, ∀z : ℂ, ∀v : ℝ, ∀hv : 0<v,1<v →
      ‖f (integralOrbitProjection globalKubotaKernel
        (complexMatrix M • upperPoint z v hv))‖≤K/v^3) :
    inner ℂ F cubicEisensteinResidue=0 :=
  cubicEisensteinResidue_orthogonal_of_rapid_cusp_decay F hF f hrep K hK
    (coset_decay_of_cusp_chart_decay f K hdec)

end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicKubota

section
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma exists_congruent_cusp_completion (A : SL(2,Eis)) (x y : Eis)
    (hxy : IsCoprime x y) (hx : (3:Eis)∣x-A 0 0) (hy : (3:Eis)∣y-A 1 0) :
    ∃ N : SL(2,Eis), N 0 0=x ∧ N 1 0=y ∧ N*A⁻¹∈levelThree := by
  obtain ⟨u,v,huv⟩ := hxy
  let t := u*A 0 1+v*A 1 1
  let N : SL(2,Eis) := ⟨!![x,-v+x*t;y,u+y*t],by
    rw [Matrix.det_fin_two_of]
    linear_combination huv⟩
  have hd : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hr : (3:Eis)∣1+y*A 0 1-x*A 1 1 := by
    convert dvd_sub (dvd_mul_of_dvd_left hy (A 0 1))
      (dvd_mul_of_dvd_left hx (A 1 1)) using 1 ; linear_combination -hd
  have hmod : ∀i j,(3:Eis)∣N i j-A i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hx
    · have hv := dvd_mul_of_dvd_left hr (-v)
      convert hv using 1 ; dsimp [N,t] ; linear_combination (A 0 1)*huv
    · exact hy
    · have hu := dvd_mul_of_dvd_left hr u
      convert hu using 1 ; dsimp [N,t] ; linear_combination (A 1 1)*huv
  have hq : Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) N =
      Matrix.SpecialLinearGroup.map (n:=Fin 2)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) A := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (hmod i j))
  refine ⟨N,rfl,rfl,?_⟩
  change Matrix.SpecialLinearGroup.map (n:=Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (N*A⁻¹)=1
  rw [map_mul,map_inv,hq,mul_inv_cancel]

lemma cusp_completion_upper_factor (A N : SL(2,Eis)) (q g x y : Eis)
    (hx : A 0 0+3*q*A 1 0=g*N 0 0) (hy : x*A 1 0=g*N 1 0)
    (hg : g≠0) (hdet : x=g*y) :
    N.val⁻¹ * (!![1,3*q;0,x] * A.val) =
      !![g,(N.val⁻¹ * (!![1,3*q;0,x] * A.val)) 0 1;0,y] := by
  have hNdet : N 0 0*N 1 1-N 0 1*N 1 0=1 := by
    simpa only [Matrix.det_fin_two] using N.property
  have hAdet : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hinv : N.val⁻¹ = !![N 1 1,-N 0 1;-N 1 0,N 0 0] := by
    rw [Matrix.inv_def,Matrix.SpecialLinearGroup.det_coe,Ring.inverse_one,one_smul,Matrix.adjugate_fin_two]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · norm_num [hinv,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    rw [hx,hy]
    linear_combination g*hNdet
  · rfl
  · norm_num [hinv,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    rw [hx,hy]
    ring
  · norm_num [hinv,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    apply mul_left_cancel₀ hg
    linear_combination x*hAdet-x*(A 1 1)*hx+(A 0 1+3*q*A 1 1)*hy+hdet

end

open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

private lemma bounded_power_factor (p a : Eis) (n : ℕ) :
    ∃ j≤n,∃b,a=p^j*b ∧ (j=n ∨ ¬p∣b) := by
  induction n generalizing a with
  | zero => exact ⟨0,le_rfl,a,by simp,Or.inl rfl⟩
  | succ n ih =>
    by_cases h:p∣a
    · obtain ⟨a',rfl⟩:=h
      obtain ⟨j,hj,b,hab,hb⟩:=ih a'
      refine ⟨j+1,Nat.succ_le_succ hj,b,?_,?_⟩
      · rw [hab,pow_succ]
        ring
      · exact hb.elim (fun h=>Or.inl (congrArg (fun k=>k+1) h)) Or.inr
    · exact ⟨0,Nat.zero_le _,a,by simp,Or.inr h⟩

lemma cube_average_cusp_reduction (A : SL(2,Eis)) (p q : Eis)
    (hp : Prime p) (hprimary : lambda^2∣p-1) :
    ∃ j≤3,∃N : SL(2,Eis),
      A 0 0+3*q*A 1 0=p^j*N 0 0 ∧
      p^3*A 1 0=p^j*N 1 0 ∧ N*A⁻¹∈levelThree ∧
      (j=3 ∨ ¬p∣N 0 0) ∧
      N.val⁻¹*(!![1,3*q;0,p^3]*A.val)=
        !![p^j,(N.val⁻¹*(!![1,3*q;0,p^3]*A.val)) 0 1;0,p^(3-j)] := by
  let a:=A 0 0+3*q*A 1 0
  have haC:IsCoprime a (A 1 0) := by
    have hd : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
      simpa only [Matrix.det_fin_two] using A.property
    refine ⟨A 1 1,-(A 0 1+3*q*A 1 1),?_⟩
    dsimp [a]
    linear_combination hd
  obtain ⟨j,hj,b,hab,hb⟩:=bounded_power_factor p a 3
  have hbC:IsCoprime b (A 1 0) := by
    rw [hab] at haC
    exact haC.of_mul_left_right
  have hbY:IsCoprime b (p^(3-j)*A 1 0) := by
    rcases hb with h | h
    · simpa [h] using hbC
    · exact ((hp.coprime_iff_not_dvd.mpr h).symm.pow_right).mul_right hbC
  have hpow (k:ℕ):(3:Eis)∣p^k-1 := by
    have hd:(3:Eis)∣p-1:=CubicJacobiGlobal.three_dvd_primary_sub_one p hprimary
    simpa using hd.trans (sub_dvd_pow_sub_pow p 1 k)
  have hbA:(3:Eis)∣b-A 0 0 := by
    have h1:(3:Eis)∣a-A 0 0:=by
      refine ⟨q*A 1 0,?_⟩
      dsimp [a]
      ring
    have h2:(3:Eis)∣a-b:=by
      rw [hab]
      convert dvd_mul_of_dvd_left (hpow j) b using 1 ; ring
    convert dvd_sub h1 h2 using 1 ; ring
  have hyC:(3:Eis)∣p^(3-j)*A 1 0-A 1 0 := by
    convert dvd_mul_of_dvd_left (hpow (3-j)) (A 1 0) using 1 ; ring
  obtain ⟨N,hN0,hN1,hNA⟩:=exists_congruent_cusp_completion A b (p^(3-j)*A 1 0) hbY hbA hyC
  have hA:a=p^j*N 0 0:=by rw [hN0];exact hab
  have hC:p^3*A 1 0=p^j*N 1 0:=by
    rw [hN1,←mul_assoc,←pow_add,Nat.add_sub_of_le hj]
  refine ⟨j,hj,N,hA,hC,hNA,?_,?_⟩
  · simpa [hN0] using hb
  · exact cusp_completion_upper_factor A N q (p^j) (p^3) (p^(3-j))
      hA hC (pow_ne_zero j hp.ne_zero) (by rw [←pow_add,Nat.add_sub_of_le hj])

end CubicKubota

end

end OAI
