module
public import OAI.NumberTheory.DirichletL.Inversion.InitialOverlap

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialPoissonBridge
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge ConcreteTraceCRT EisensteinSchwartzPoisson UniqueFactorizationMonoid InverseInitialOverlap

def rowPolynomial (F : Finset (Ideal Eis)) (A : Ideal Eis → ℂ) (u : Eis) : ℂ :=
  ∑ I ∈ F, A I * idealRowHom u I

lemma pool_positive (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I) :
    ∀ I ∈ F, I ≠ 0 := fun I hI => (hF I hI).1

lemma pool_good (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I) :
    ∀ I ∈ F, ∀ Q ∈ normalizedFactors I, goodLambda ∉ Q :=
  fun I hI Q hQ => ((hF I hI).2.2 Q hQ).1

theorem idealRowHom_eq_idealSexticRow
    (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I)
    {I : Ideal Eis} (hI : I ∈ F) (u : Eis) :
    idealRowHom u I = idealSexticRow F (pool_positive F hF) (pool_good F hF) I u := by
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  conv_lhs => rw [← idealSupport_product_eq F hI (hF I hI).2.1]
  rw [map_prod]
  change (∏ q ∈ idealSupport F I, idealRowHom u q.val) =
    ∏ q ∈ idealSupport F I, CompletedGauss.actualSextic q.val (primePool_good F (pool_good F hF) q)
      (Ideal.Quotient.mk q.val u)
  apply Finset.prod_congr rfl
  intro q hq
  exact idealRowHom_prime u q.val (primePool_good F (pool_good F hF) q)

theorem indexed_smoothed_summable {β : Type*} (C : Finset β)
    (L : β → Ideal Eis) (hL : ∀ c ∈ C, Admissible (L c)) (A : β → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y) *
      (‖∑ c ∈ C, A c * idealRowHom u (L c)‖^2 : ℝ)) := by
  let F := C.image L
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
    exact hL c hc
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  have he (u : Eis) : (∑ c ∈ C, A c*idealRowHom u (L c)) =
      ∑ c ∈ C, A c*idealSexticRow F (pool_positive F hF) (pool_good F hF) (L c) u := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [idealRowHom_eq_idealSexticRow F hF (Finset.mem_image.mpr ⟨c,hc,rfl⟩)]
  simpa only [he,idealSexticRow] using finiteSquarefreeRow_smoothed_mean_square_summable
    (fun q : primePool F => q.val) (primePool_good F (pool_good F hF))
    C (fun c => idealSupport F (L c)) A Φ Y hY

theorem supported_of_dvd {I J : Ideal Eis} (hI : Supported I) (hJI : J ∣ I) : Supported J := by
  obtain ⟨K,rfl⟩ := hJI
  exact (supported_mul_iff J K).mp hI |>.1

theorem columns_admissible (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n)
    {c : Ideal Eis} (hc : c ∈ columns S P j) : Admissible c := by
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hnS,hns,hg⟩ := mem_original.mp hn
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hs := (supported_mul_iff (idealQuotient j n) (residual P j)).mpr
    ⟨supported_of_dvd (hS n hnS hns) (idealQuotient_dvd hjn),
     supported_of_dvd (admissible_supported hP) (idealQuotient_dvd hj)⟩
  exact ⟨hs.1,(column_properties hP.2.1 hj hns hg).1,hs.2⟩

theorem masked_columns_admissible (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n)
    {c : Ideal Eis} (hc : c ∈ columns S P j) : Admissible (j*c) := by
  have hjA := admissible_of_dvd hP hj
  have hcA := columns_admissible S hP hj hS hc
  have hs := (supported_mul_iff j c).mpr ⟨admissible_supported hjA,admissible_supported hcA⟩
  exact ⟨hs.1,squarefree_mul_iff.mpr
    ⟨((mem_columns hP.2.1 hj).mp hc).2.1.symm.isRelPrime,hjA.2.1,hcA.2.1⟩,hs.2⟩

theorem norm_idealRowHom_four_eq_two (I : Ideal Eis) (hI : Admissible I) (u : Eis) :
    ‖idealRowHom u I‖^4 = ‖idealRowHom u I‖^2 := by
  let F : Finset (Ideal Eis) := {I}
  have hF : ∀ J ∈ F, Admissible J := by
    intro J hJ
    have he : J=I := Finset.mem_singleton.mp hJ
    simpa only [he] using hI
  rw [idealRowHom_eq_idealSexticRow F hF (Finset.mem_singleton_self I)]
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  have he := congrArg norm (finiteSquarefreeRow_self_pair
    (fun q : primePool F => q.val) (primePool_good F (pool_good F hF)) (idealSupport F I) u)
  simp only [norm_mul,norm_star,←pow_two] at he
  change ‖idealSexticRow F (pool_positive F hF) (pool_good F hF) I u‖^2 = _ at he
  have hp : ∀ x : ℝ, x^4=(x^2)^2 := by intro x; ring
  rw [hp,he]
  unfold rowCoprimeMask
  split_ifs <;> norm_num

def heckeIdealCharacter (η : Ideal Eis →* ℂ) (u : Eis) : Ideal Eis →* ℂ :=
  η * (idealRowHom u).toMonoidHom

theorem heckeIdealCharacter_apply (η : Ideal Eis →* ℂ) (u : Eis) (I : Ideal Eis) :
    heckeIdealCharacter η u I = η I * idealRowHom u I := rfl

def originalFixedPolynomial (S : Finset (Ideal Eis)) (P j : Ideal Eis)
    (η : Ideal Eis →* ℂ) (a : Ideal Eis → ℂ) (W : ℝ → ℂ)
    (Z r z : ℝ) (u : Eis) : ℂ :=
  (Z^(-(r+z)/2) : ℝ) * ∑ n ∈ original S P j,
    (moebius n : ℂ) * heckeIdealCharacter η u n * heckeIdealCharacter η u P *
      a n * W ((Ideal.absNorm n : ℝ)/Z^r)

def overlapResidualCoefficient (P j : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (c : Ideal Eis) : ℂ :=
  (moebius c : ℂ) * η c * a (reconstruct P j c) *
    W ((((Ideal.absNorm j : ℝ)/Z^G)*((Ideal.absNorm c : ℝ)/Z^(r+z-2*G))) /
      ((Ideal.absNorm (residual P j) : ℝ)/Z^(z-G)))

def overlapPrefactor (P j : Ideal Eis) (η : Ideal Eis →* ℂ) (Z r z G : ℝ) : ℂ :=
  (moebius j : ℂ)*(moebius (residual P j) : ℂ)*(Z^(-G) : ℝ)*η j^2*
    (Z^(-(r+z-2*G)/2) : ℝ)

theorem originalFixedPolynomial_eq (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Squarefree P) (hj : j ∣ P) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) (u : Eis) :
    originalFixedPolynomial S P j η a W Z r z u =
      overlapPrefactor P j η Z r z G * (idealRowHom u j)^2 *
        rowPolynomial (columns S P j) (overlapResidualCoefficient P j η a W Z r z G) u := by
  have he := normalized_polynomial_fixed_overlap S hP hj (heckeIdealCharacter η u) a W hZ r z G
  change originalFixedPolynomial S P j η a W Z r z u = _ at he
  rw [he]
  simp only [heckeIdealCharacter_apply,
    rowPolynomial,overlapPrefactor,overlapResidualCoefficient,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem maskedResidual_eq (S : Finset (Ideal Eis)) (P j : Ideal Eis)
    (A : Ideal Eis → ℂ) (u : Eis) :
    (∑ c ∈ columns S P j, A c*idealRowHom u (j*c)) =
      idealRowHom u j * rowPolynomial (columns S P j) A u := by
  simp only [map_mul,rowPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

lemma norm_sq_square_factor (r s : ℂ) (h : ‖r‖^4=‖r‖^2) :
    ‖r^2*s‖^2=‖r*s‖^2 := by
  calc
    _ = ‖r‖^4*‖s‖^2 := by simp only [norm_mul,norm_pow]; ring
    _ = ‖r*s‖^2 := by rw [h,norm_mul,mul_pow]

theorem originalFixedPolynomial_norm_sq (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j ∣ P) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) (u : Eis) :
    ‖originalFixedPolynomial S P j η a W Z r z u‖^2 =
      ‖overlapPrefactor P j η Z r z G‖^2 *
        ‖∑ c ∈ columns S P j, overlapResidualCoefficient P j η a W Z r z G c *
          idealRowHom u (j*c)‖^2 := by
  rw [originalFixedPolynomial_eq S hP.2.1 hj η a W hZ r z G,
    maskedResidual_eq,mul_assoc,norm_mul,mul_pow]
  congr 1
  exact norm_sq_square_factor _ _ (norm_idealRowHom_four_eq_two j (admissible_of_dvd hP hj) u)

def residualNormalizedPolynomial (S : Finset (Ideal Eis)) (P j : Ideal Eis)
    (η : Ideal Eis →* ℂ) (a : Ideal Eis → ℂ) (W : ℝ → ℂ)
    (Z r z G : ℝ) (u : Eis) : ℂ :=
  (Z^(-(r+z-2*G)/2) : ℝ) * ∑ c ∈ columns S P j,
    overlapResidualCoefficient P j η a W Z r z G c * star (idealRowHom u c)

lemma norm_rpow_half_sq {Z : ℝ} (hZ : 0 < Z) (D : ℝ) :
    ‖((Z^(-D/2) : ℝ) : ℂ)‖^2=Z^(-D) := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ _),
    ←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  congr 1
  norm_num

theorem original_fixed_overlap_smoothed_summable
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y)*
      (‖originalFixedPolynomial S P j η a W Z r z u‖^2 : ℝ)) := by
  have hs := (indexed_smoothed_summable (columns S P j) (fun c => j*c)
    (fun c hc => masked_columns_admissible S hP hj hS hc)
    (overlapResidualCoefficient P j η a W Z r z G) Φ Y hY).mul_left
      ((‖overlapPrefactor P j η Z r z G‖^2 : ℝ) : ℂ)
  apply hs.congr
  intro u
  rw [originalFixedPolynomial_norm_sq S hP hj η a W hZ r z G,Complex.ofReal_mul]
  ring

theorem original_normalized_polynomial_hecke_rows
    (S : Finset (Ideal Eis)) {P : Ideal Eis} (hP : Squarefree P)
    (η : Ideal Eis →* ℂ) (a : Ideal Eis → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal Eis → ℝ) (u : Eis) :
    (Z^(-(r+z)/2) : ℝ) * (∑ n ∈ S,
      (moebius n : ℂ)*heckeIdealCharacter η u n*heckeIdealCharacter η u P*
        a n*W ((Ideal.absNorm n : ℝ)/Z^r)) =
      ∑ j ∈ IdealMobiusDivisorSum.idealDivisors P,
        overlapPrefactor P j η Z r z (G j) * (idealRowHom u j)^2 *
          rowPolynomial (columns S P j)
            (overlapResidualCoefficient P j η a W Z r z (G j)) u := by
  rw [original_normalized_polynomial S hP (heckeIdealCharacter η u) a W hZ r z G]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [heckeIdealCharacter_apply,rowPolynomial,overlapPrefactor,
    overlapResidualCoefficient,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem indexed_conjugate_smoothed_summable {β : Type*} (C : Finset β)
    (L : β → Ideal Eis) (hL : ∀ c ∈ C, Admissible (L c)) (A : β → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y) *
      (‖∑ c ∈ C, A c * star (idealRowHom u (L c))‖^2 : ℝ)) := by
  have he (u : Eis) : (∑ c ∈ C, A c * star (idealRowHom u (L c))) =
      star (∑ c ∈ C, star (A c) * idealRowHom u (L c)) := by
    simp only [star_sum,star_mul,star_star,mul_comm]
  simpa only [he,norm_star] using
    indexed_smoothed_summable C L hL (fun c => star (A c)) Φ Y hY

theorem residual_normalized_smoothed_summable
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y)*
      (‖residualNormalizedPolynomial S P j η a W Z r z G u‖^2 : ℝ)) := by
  have hs := (indexed_conjugate_smoothed_summable (columns S P j) (fun c => c)
    (fun c hc => columns_admissible S hP hj hS hc)
    (overlapResidualCoefficient P j η a W Z r z G) Φ Y hY).mul_left
      ((Z^(-(r+z-2*G)) : ℝ) : ℂ)
  apply hs.congr
  intro u
  rw [residualNormalizedPolynomial,norm_mul,mul_pow,norm_rpow_half_sq hZ,Complex.ofReal_mul]
  ring
