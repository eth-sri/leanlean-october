module
public import OAI.NumberTheory.DirichletL.Inversion.InitialRayAttachment

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseInitialConjugateEnergy
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss ConcreteTraceCRT InverseInitialOverlap InverseInitialPoissonBridge InverseInitialRayAttachment UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def conjugateIdealCharacter (η : Ideal O →* ℂ) : Ideal O →* ℂ where
  toFun I := star (η I)
  map_one' := by rw [map_one,star_one]
  map_mul' I J := by simp [map_mul]

@[simp] theorem conjugateIdealCharacter_apply (η : Ideal O →* ℂ) (I : Ideal O) :
    conjugateIdealCharacter η I = star (η I) := rfl

theorem overlapResidualCoefficient_conjugate (P j : Ideal O) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (c : Ideal O) :
    overlapResidualCoefficient P j (conjugateIdealCharacter η)
        (fun I => star (a I)) (fun x => star (W x)) Z r z G c =
      star (overlapResidualCoefficient P j η a W Z r z G c) := by
  simp [overlapResidualCoefficient, star_mul, mul_comm, mul_left_comm, mul_assoc]

def conjugatedResidual (S : Finset (Ideal O)) (P j : Ideal O) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (u : O) : ℂ :=
  residualNormalizedPolynomial S P j (conjugateIdealCharacter η)
    (fun I => star (a I)) (fun x => star (W x)) Z r z G u

theorem star_conjugatedResidual (S : Finset (Ideal O)) (P j : Ideal O)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    (Z r z G : ℝ) (u : O) :
    star (conjugatedResidual S P j η a W Z r z G u) =
      (Z^(-(r+z-2*G)/2) : ℝ) *
        rowPolynomial (columns S P j) (overlapResidualCoefficient P j η a W Z r z G) u := by
  unfold conjugatedResidual residualNormalizedPolynomial
  simp_rw [overlapResidualCoefficient_conjugate]
  simp [rowPolynomial, mul_comm]

theorem originalFixedPolynomial_eq_conjugatedResidual (S : Finset (Ideal O))
    {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (u : O) :
    originalFixedPolynomial S P j η a W Z r z u =
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) * (Z^(-G) : ℝ) *
        η j^2 * (idealRowHom u j)^2 * star (conjugatedResidual S P j η a W Z r z G u) := by
  rw [originalFixedPolynomial_eq S hP hj η a W hZ r z G,
    star_conjugatedResidual]
  unfold overlapPrefactor
  ring

theorem originalFixedPolynomial_norm_sq_conjugatedResidual (S : Finset (Ideal O))
    {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (u : O) :
    ‖originalFixedPolynomial S P j η a W Z r z u‖^2 =
      Z^(-2*G) * ‖η j‖^4 * ‖idealRowHom u j‖^4 *
        ‖conjugatedResidual S P j η a W Z r z G u‖^2 := by
  rw [originalFixedPolynomial_eq_conjugatedResidual S hP hj η a W hZ r z G]
  have hjn : ‖(moebius j : ℂ)‖=1 := by simp [(hP.squarefree_of_dvd hj).moebius_eq]
  have hpn : ‖(moebius (residual P j) : ℂ)‖=1 := by simp [(residual_squarefree hP hj).moebius_eq]
  have hp : (Z^(-G))^2=Z^(-2*G) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    ring
  simp only [norm_mul,norm_pow,norm_star,hjn,hpn,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ (-G)),mul_pow]
  rw [hp]
  ring

theorem admissible_row_four_le_one (I : Ideal O) (hI : Admissible I) (u : O) :
    ‖idealRowHom u I‖^4 ≤ 1 := by
  have he := norm_idealRowHom_four_eq_two I hI u
  have hs : 0≤‖idealRowHom u I‖^2 := sq_nonneg _
  have ht : ‖idealRowHom u I‖^4=(‖idealRowHom u I‖^2)^2 := by ring
  rw [ht] at he ⊢
  nlinarith

theorem originalFixedPolynomial_norm_sq_le (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j ∣ P) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z) (r z G : ℝ) (u : O) :
    ‖originalFixedPolynomial S P j η a W Z r z u‖^2 ≤
      Z^(-2*G) * ‖η j‖^4 * ‖conjugatedResidual S P j η a W Z r z G u‖^2 := by
  rw [originalFixedPolynomial_norm_sq_conjugatedResidual S hP.2.1 hj η a W hZ r z G]
  have hm := admissible_row_four_le_one j (admissible_of_dvd hP hj) u
  have hz := (Real.rpow_pos_of_pos hZ (-2*G)).le
  nlinarith [mul_nonneg hz (pow_nonneg (norm_nonneg (η j)) 4),
    mul_nonneg (mul_nonneg hz (pow_nonneg (norm_nonneg (η j)) 4))
      (sq_nonneg ‖conjugatedResidual S P j η a W Z r z G u‖)]

theorem finite_weighted_triangle {α β : Type*} (J : Finset α) (R : Finset β)
    (w : β → ℝ) (hw : ∀ u,0≤w u) (F : α → β → ℂ) :
    (∑ u ∈ R,w u * ‖∑ j ∈ J,F j u‖^2) ≤
      (∑ j ∈ J,Real.sqrt (∑ u ∈ R,w u*‖F j u‖^2))^2 := by
  let v (j : α) : EuclideanSpace ℂ R :=
    WithLp.toLp 2 (fun u => (Real.sqrt (w u) : ℂ)*F j u)
  have hv (j : α) : ‖v j‖^2=∑ u ∈ R,w u*‖F j u‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [v,norm_mul,mul_pow,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hw _)]
    exact Finset.sum_coe_sort R (fun u => w u*‖F j u‖^2)
  have hsum : ‖∑ j ∈ J,v j‖^2=∑ u ∈ R,w u*‖∑ j ∈ J,F j u‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [WithLp.ofLp_sum,Finset.sum_apply,v,←Finset.mul_sum,norm_mul,mul_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hw _)]
    exact Finset.sum_coe_sort R (fun u => w u*‖∑ j ∈ J,F j u‖^2)
  have hs := norm_sum_le J v
  have hn (j : α) : ‖v j‖=Real.sqrt (∑ u ∈ R,w u*‖F j u‖^2) := by
    rw [←hv,Real.sqrt_sq (norm_nonneg _)]
  have hh := pow_le_pow_left₀ (norm_nonneg _) hs 2
  simpa only [hsum,hn] using hh

theorem weighted_overlap_triangle {α β : Type*} (J : Finset α)
    (w : β → ℝ) (hw : ∀ u,0≤w u) (F : α → β → ℂ)
    (hs : ∀ j∈J,Summable (fun u => w u*‖F j u‖^2)) :
    Summable (fun u => w u*‖∑ j∈J,F j u‖^2) ∧
      (∑' u,w u*‖∑ j∈J,F j u‖^2) ≤
        (∑ j∈J,Real.sqrt (∑' u,w u*‖F j u‖^2))^2 := by
  have hn (u : β) : 0≤w u*‖∑ j∈J,F j u‖^2 := mul_nonneg (hw u) (sq_nonneg _)
  have hb (R : Finset β) : (∑ u∈R,w u*‖∑ j∈J,F j u‖^2) ≤
      (∑ j∈J,Real.sqrt (∑' u,w u*‖F j u‖^2))^2 := by
    refine (finite_weighted_triangle J R w hw F).trans ?_
    apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))
    apply Finset.sum_le_sum
    intro j hj
    apply Real.sqrt_le_sqrt
    exact (hs j hj).sum_le_tsum R (fun u _ => mul_nonneg (hw u) (sq_nonneg _))
  exact ⟨summable_of_sum_le hn hb,Real.tsum_le_of_sum_le hn hb⟩

def radialWeight (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (u : O) : ℝ :=
  (Φ (‖eisEmbedding u‖^2/Y)).re

def smoothedEnergy (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (f : O → ℂ) : ℝ :=
  ∑' u,radialWeight Φ Y u*‖f u‖^2

theorem radialWeight_nonneg (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re)
    {Y : ℝ} (hY : 0<Y) (u : O) : 0≤radialWeight Φ Y u :=
  hΦ _ (div_nonneg (sq_nonneg _) hY.le)

theorem smoothedEnergy_nonneg (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re)
    {Y : ℝ} (hY : 0<Y) (f : O → ℂ) : 0≤smoothedEnergy Φ Y f :=
  tsum_nonneg (fun u => mul_nonneg (radialWeight_nonneg Φ hΦ hY u) (sq_nonneg _))

theorem original_energy_summable (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (Φ : 𝓢(ℝ,ℂ)) {Y : ℝ} (hY : 0<Y) :
    Summable (fun u => radialWeight Φ Y u*‖originalFixedPolynomial S P j η a W Z r z u‖^2) := by
  have hs := original_fixed_overlap_smoothed_summable S hP hj hS η a W hZ r z G Φ Y hY
  simpa only [radialWeight,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero] using (Complex.hasSum_re hs.hasSum).summable

theorem conjugatedResidual_energy_summable (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (Φ : 𝓢(ℝ,ℂ)) {Y : ℝ} (hY : 0<Y) :
    Summable (fun u => radialWeight Φ Y u*‖conjugatedResidual S P j η a W Z r z G u‖^2) := by
  have hs := residual_normalized_smoothed_summable S hP hj hS (conjugateIdealCharacter η)
    (fun I => star (a I)) (fun x => star (W x)) hZ r z G Φ Y hY
  simpa only [radialWeight,conjugatedResidual,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] using (Complex.hasSum_re hs.hasSum).summable

theorem original_smoothed_contraction (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re)
    {Y : ℝ} (hY : 0<Y) :
    smoothedEnergy Φ Y (originalFixedPolynomial S P j η a W Z r z) ≤
      Z^(-2*G)*‖η j‖^4 * smoothedEnergy Φ Y (conjugatedResidual S P j η a W Z r z G) := by
  unfold smoothedEnergy
  rw [←tsum_mul_left]
  apply (original_energy_summable S hP hj hS η a W hZ r z G Φ hY).tsum_le_tsum _
    ((conjugatedResidual_energy_summable S hP hj hS η a W hZ r z G Φ hY).mul_left _)
  intro u
  have hh := mul_le_mul_of_nonneg_left
    (originalFixedPolynomial_norm_sq_le S hP hj η a W hZ r z G u)
    (radialWeight_nonneg Φ hΦ hY u)
  convert hh using 1
  ring

theorem sqrt_overlap_prefactor {Z : ℝ} (hZ : 0<Z) (G : ℝ) (ηj : ℂ) (E : ℝ) :
    Real.sqrt (Z^(-2*G)*‖ηj‖^4*E) = Z^(-G)*‖ηj‖^2*Real.sqrt E := by
  have hz : (Z^(-G))^2=Z^(-2*G) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    ring
  have hp : Z^(-2*G)*‖ηj‖^4=(Z^(-G)*‖ηj‖^2)^2 := by
    rw [mul_pow,hz]
    ring
  rw [hp,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]

def originalTotalPolynomial (S : Finset (Ideal O)) (P : Ideal O) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z : ℝ) (u : O) : ℂ :=
  (Z^(-(r+z)/2) : ℝ) * ∑ n∈S,(moebius n : ℂ)*heckeIdealCharacter η u n*
    heckeIdealCharacter η u P*a n*W ((Ideal.absNorm n : ℝ)/Z^r)

theorem originalTotalPolynomial_eq_sectors (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0<Z) (r z : ℝ) (G : Ideal O → ℝ) (u : O) :
    originalTotalPolynomial S P η a W Z r z u =
      ∑ j∈idealDivisors P,originalFixedPolynomial S P j η a W Z r z u := by
  unfold originalTotalPolynomial
  rw [original_normalized_polynomial_hecke_rows S hP η a W hZ r z G]
  apply Finset.sum_congr rfl
  intro j hj
  exact (originalFixedPolynomial_eq S hP ((mem_idealDivisors hP.ne_zero).mp hj)
    η a W hZ r z (G j) u).symm

theorem original_smoothed_overlap_triangle (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Admissible P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z : ℝ) (G : Ideal O → ℝ) (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re) {Y : ℝ} (hY : 0<Y) :
    Summable (fun u => radialWeight Φ Y u*‖originalTotalPolynomial S P η a W Z r z u‖^2) ∧
    Real.sqrt (smoothedEnergy Φ Y (originalTotalPolynomial S P η a W Z r z)) ≤
      ∑ j∈idealDivisors P,Z^(-G j)*‖η j‖^2*
        Real.sqrt (smoothedEnergy Φ Y (conjugatedResidual S P j η a W Z r z (G j))) := by
  have hjd (j : Ideal O) (hj : j∈idealDivisors P) : j∣P := (mem_idealDivisors hP.1).mp hj
  have hs := weighted_overlap_triangle (idealDivisors P) (radialWeight Φ Y)
    (radialWeight_nonneg Φ hΦ hY) (fun j => originalFixedPolynomial S P j η a W Z r z)
    (fun j hj => original_energy_summable S hP (hjd j hj) hS η a W hZ r z (G j) Φ hY)
  simp_rw [←originalTotalPolynomial_eq_sectors S hP.2.1 η a W hZ r z G] at hs
  refine ⟨hs.1,?_⟩
  have hb := Real.sqrt_le_sqrt hs.2
  rw [Real.sqrt_sq (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))] at hb
  refine hb.trans (Finset.sum_le_sum (fun j hj => ?_))
  have hc := Real.sqrt_le_sqrt (original_smoothed_contraction S hP (hjd j hj) hS
    η a W hZ r z (G j) Φ hΦ hY)
  rwa [sqrt_overlap_prefactor hZ] at hc

theorem real_smoothed_sum_eq (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → (Φ x).im=0) {Y : ℝ} (hY : 0<Y) (f : O → ℂ) :
    (∑' u : O,Φ (‖eisEmbedding u‖^2/Y)*(‖f u‖^2 : ℝ)) =
      (smoothedEnergy Φ Y f : ℂ) := by
  unfold smoothedEnergy
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro u
  have he : Φ (‖eisEmbedding u‖^2/Y) = (radialWeight Φ Y u : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hΦ _ (div_nonneg (sq_nonneg _) hY.le)
  rw [he,Complex.ofReal_mul]

end SevenEighths.InverseInitialConjugateEnergy

end

end OAI
