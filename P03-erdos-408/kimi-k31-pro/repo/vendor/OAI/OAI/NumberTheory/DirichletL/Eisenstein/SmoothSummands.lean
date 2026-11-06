module

public import OAI.NumberTheory.DirichletL.QuadraticSieve.SpatialDerivatives
public import OAI.NumberTheory.DirichletL.CubicSieve.FirstCoreCutoff

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

namespace CubicEisenstein
open scoped BigOperators Classical Topology Matrix

def smoothEisenstein (s : ℂ) (p : SpatialCoordinates) : ℂ := ∑'r, smoothSummand s r p

lemma smoothEisenstein_eq_actual (s : ℂ) (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothEisenstein s p = upperEisenstein ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hv s := by
  unfold smoothEisenstein upperEisenstein eisenstein
  exact tsum_congr (fun r => smoothSummand_eq_actual s r p hv)

theorem eisenstein_axis_termwise (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (smoothSummand s r) p j) (p j)) ∧
    Summable (fun r => deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)) ∧
    HasDerivAt (axisSlice (smoothEisenstein s) p j)
      (∑'r,deriv (axisSlice (smoothSummand s r) p j) (p j)) (p j) ∧
    HasDerivAt (deriv (axisSlice (smoothEisenstein s) p j))
      (∑'r,deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)) (p j) := by
  obtain ⟨ε,hε,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ := axis_summable_derivative_bounds s hs p hv j
  have hx : p j ∈ Metric.ball (p j) ε := Metric.mem_ball_self hε
  have hs₀ : Summable (fun r => axisSlice (smoothSummand s r) p j (p j)) :=
    Summable.of_norm_bounded hM₀ (fun r => ((hbound (p j) hx).2 r).1)
  have hs₁ : Summable (fun r => deriv (axisSlice (smoothSummand s r) p j) (p j)) :=
    Summable.of_norm_bounded hM₁ (fun r => ((hbound (p j) hx).2 r).2.1)
  have hs₂ : Summable (fun r => deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)) :=
    Summable.of_norm_bounded hM₂ (fun r => ((hbound (p j) hx).2 r).2.2)
  have hd₁ (r : CuspCosets) (t : ℝ) (ht : t∈Metric.ball (p j) ε) :
      DifferentiableAt ℝ (axisSlice (smoothSummand s r) p j) t :=
    smooth_axis_differentiable_at s r p j t (hbound t ht).1
  have hd₂ (r : CuspCosets) (t : ℝ) (ht : t∈Metric.ball (p j) ε) :
      DifferentiableAt ℝ (deriv (axisSlice (smoothSummand s r) p j)) t :=
    smooth_axis_deriv_differentiable_at s r p j t (hbound t ht).1
  refine ⟨hs₁,hs₂,?_,?_⟩
  · exact hasDerivAt_tsum_of_isPreconnected hM₁ Metric.isOpen_ball Metric.isPreconnected_ball
      (fun r t ht => (hd₁ r t ht).hasDerivAt) (fun r t ht => ((hbound t ht).2 r).2.1) hx hs₀ hx
  · exact hasDerivAt_deriv_tsum_of_bounds (fun r => axisSlice (smoothSummand s r) p j)
      M₁ M₂ _ (p j) Metric.isOpen_ball Metric.isPreconnected_ball hx hM₁ hM₂ hd₁ hd₂
      (fun r t ht => ((hbound t ht).2 r).2.1) (fun r t ht => ((hbound t ht).2 r).2.2) hs₀

def axisLaplacian (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) : ℂ :=
  (p 2:ℂ)^2 * (∑ j : Fin 3, deriv (deriv (axisSlice f p j)) (p j)) -
    (p 2:ℂ)*deriv (axisSlice f p 2) (p 2)

lemma axisSlice_zero (f : ℝ → ℝ → ℝ → ℂ) (p : SpatialCoordinates) :
    axisSlice (fun q => f (q 0) (q 1) (q 2)) p 0 = fun t => f t (p 1) (p 2) := by
  funext t
  simp [axisSlice,Function.update]
lemma axisSlice_one (f : ℝ → ℝ → ℝ → ℂ) (p : SpatialCoordinates) :
    axisSlice (fun q => f (q 0) (q 1) (q 2)) p 1 = fun t => f (p 0) t (p 2) := by
  funext t
  simp [axisSlice,Function.update]
lemma axisSlice_two (f : ℝ → ℝ → ℝ → ℂ) (p : SpatialCoordinates) :
    axisSlice (fun q => f (q 0) (q 1) (q 2)) p 2 = fun t => f (p 0) (p 1) t := by
  funext t
  simp [axisSlice,Function.update]

lemma axisLaplacian_eq_hyperbolicLaplacian (f : ℝ → ℝ → ℝ → ℂ) (p : SpatialCoordinates) :
    axisLaplacian (fun q => f (q 0) (q 1) (q 2)) p =
      hyperbolicLaplacian f (p 0) (p 1) (p 2) := by
  simp only [axisLaplacian,Fin.sum_univ_three,axisSlice_zero,axisSlice_one,axisSlice_two,
    hyperbolicLaplacian]

lemma smoothSummand_axisLaplacian (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates) (hv : 0<p 2) :
    axisLaplacian (smoothSummand s r) p = s*(s-2)*smoothSummand s r p := by
  unfold smoothSummand rowSmoothPower
  rw [axisLaplacian_eq_hyperbolicLaplacian
    (fun x y v => (cosetCharacter r)⁻¹ *
      spatialHeightPower s (Complex.normSq (embeddedRow r 0))
        ((embeddedRow r 0*star (embeddedRow r 1)).re)
        (-(embeddedRow r 0*star (embeddedRow r 1)).im)
        (Complex.normSq (embeddedRow r 1)) x y v) p,
    hyperbolicLaplacian_const_mul,spatialHeightPower_eigenfunction]
  · ring
  · exact complex_row_quadratic_relation _ _
  · exact hv.ne'
  · exact (row_denominator_pos _ (embeddedRow_ne_zero r) p hv).ne'

theorem smoothEisenstein_eigenfunction (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    axisLaplacian (smoothEisenstein s) p = s*(s-2)*smoothEisenstein s p := by
  have hterms := eisenstein_axis_termwise s hs p hv
  let second := fun (j : Fin 3) (r : CuspCosets) =>
    deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)
  let first := fun r : CuspCosets => deriv (axisSlice (smoothSummand s r) p 2) (p 2)
  have hsecond (j : Fin 3) : Summable (second j) := (hterms j).2.1
  have hfirst : Summable first := (hterms 2).1
  have hsum : Summable (fun r => ∑ j : Fin 3, second j r) := by
    simpa only [Fin.sum_univ_three] using ((hsecond 0).add (hsecond 1)).add (hsecond 2)
  have hcomm : (∑ j : Fin 3, ∑'r,second j r) = ∑'r,∑ j : Fin 3,second j r := by
    exact (Summable.tsum_finsetSum (fun j _ => hsecond j)).symm
  unfold axisLaplacian
  simp_rw [fun j => (hterms j).2.2.2.deriv]
  rw [(hterms 2).2.2.1.deriv]
  change (p 2:ℂ)^2*(∑j : Fin 3,∑'r,second j r) - (p 2:ℂ)*(∑'r,first r) = _
  rw [hcomm,← tsum_mul_left,← tsum_mul_left,← (hsum.mul_left _).tsum_sub (hfirst.mul_left _)]
  change (∑'r,axisLaplacian (smoothSummand s r) p) = _
  simp_rw [smoothSummand_axisLaplacian s _ p hv]
  rw [tsum_mul_left]
  rfl

lemma axisSlice_eventuallyEq_of_positive (f g : SpatialCoordinates → ℂ)
    (heq : ∀ q, 0<q 2 → f q=g q) (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    axisSlice f p j =ᶠ[𝓝 (p j)] axisSlice g p j := by
  have hnear : ∀ᶠ t in 𝓝 (p j), 0<(Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    change 0<(Function.update p j (p j)) 2
    simpa only [Function.update_eq_self] using hv
  filter_upwards [hnear] with t ht
  exact heq _ ht

lemma axisLaplacian_congr_positive (f g : SpatialCoordinates → ℂ)
    (heq : ∀ q, 0<q 2 → f q=g q) (p : SpatialCoordinates) (hv : 0<p 2) :
    axisLaplacian f p = axisLaplacian g p := by
  have h (j : Fin 3) := axisSlice_eventuallyEq_of_positive f g heq p hv j
  unfold axisLaplacian
  rw [(h 2).deriv_eq]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  exact (h j).deriv.deriv_eq

end CubicEisenstein

namespace SecondPassArithmetic


open FirstPassCubeLabels (columnLog primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
lemma residualPairWeight_test_ne_zero
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ) (S T : Finset ι)
    (hw : residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T ≠ 0) :
    H₁ S ≠ 0 ∧ H₂ T ≠ 0 := by
  constructor
  · intro hz
    apply hw
    simp only [residualPairWeight, secondInputCoefficient, hz, mul_zero, star_zero, zero_mul]
  · intro hz
    apply hw
    simp only [residualPairWeight, secondInputCoefficient, hz, mul_zero]

end

end SecondPassArithmetic

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic IdealMobiusDivisorSum IdealCoprimeSieveOperator

lemma divisorPool_filter (S : Finset (Ideal O)) (B : Ideal O) (hB : B ≠ 0)
    (hS : ∀ D, D ∣ B → D ∈ S) :
    S.filter (fun D => D ∣ B) = idealDivisors B := by
  ext D
  simp only [Finset.mem_filter, mem_idealDivisors hB]
  exact ⟨And.right, fun h => ⟨hS D h,h⟩⟩

lemma divisor_product_delta (S T : Finset (Ideal O)) (B C d : Ideal O)
    (hB : B ≠ 0) (hC : C ≠ 0) (hBC : IsCoprime B C)
    (hS : ∀ D, D ∣ B → D ∈ S) (hT : ∀ E, E ∣ C → E ∈ T)
    (f : Ideal O → ℂ) :
    (∑ D ∈ S, if D ∣ B then
      ∑ E ∈ T, if E ∣ C then (if D*E=d then f (D*E) else 0) else 0 else 0) =
      if d ∣ B*C then f d else 0 := by
  have hs := QuadraticDivisorSplit.sum_divisors_coprime_product B C hB hC hBC
    (fun q => if q=d then f q else 0)
  have hleft : (∑ q ∈ idealDivisors (B*C), if q=d then f q else 0) =
      if d ∣ B*C then f d else 0 := by
    simp [mem_idealDivisors (mul_ne_zero hB hC)]
  rw [hleft] at hs
  rw [← divisorPool_filter S B hB hS, ← divisorPool_filter T C hC hT] at hs
  simpa only [Finset.sum_filter] using hs.symm

private lemma four_sums_exchange {α β γ deltaLoss : Type*}
    (S : Finset α) (T : Finset β) (U : Finset γ) (V : Finset deltaLoss)
    (f : α → β → γ → deltaLoss → ℂ) :
    (∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U, ∑ d ∈ V, f a b c d) =
      ∑ c ∈ U, ∑ d ∈ V, ∑ a ∈ S, ∑ b ∈ T, f a b c d := by
  have h : (∑ ab ∈ S ×ˢ T, ∑ cd ∈ U ×ˢ V, f ab.1 ab.2 cd.1 cd.2) =
      ∑ cd ∈ U ×ˢ V, ∑ ab ∈ S ×ˢ T, f ab.1 ab.2 cd.1 cd.2 := Finset.sum_comm
  simpa only [Finset.sum_product] using h

private lemma three_sums_exchange {α β γ : Type*}
    (S : Finset α) (T : Finset β) (U : Finset γ) (f : α → β → γ → ℝ) :
    (∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U, f a b c) =
      ∑ b ∈ T, ∑ c ∈ U, ∑ a ∈ S, f a b c := by
  have h : (∑ a ∈ S, ∑ bc ∈ T ×ˢ U, f a bc.1 bc.2) =
      ∑ bc ∈ T ×ˢ U, ∑ a ∈ S, f a bc.1 bc.2 := Finset.sum_comm
  simpa only [Finset.sum_product] using h

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalTerm_product_divisor (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (d : Ideal O) (i : m) (j : n) (k : p)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T)
    (F : Ideal O → m → n → p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, if D*E=d then
      originalTerm rows left right a b D E i j k * F (D*E) i j k else 0) =
    (if d ∣ left j*right k then
      originalTerm rows left right a b 1 1 i j k * F d i j k else 0) := by
  by_cases hc : IsCoprime (left j) (right k)
  · have hd := divisor_product_delta S T (left j) (right k) d (hleft j) (hright k) hc
      (hS j) (hT k) (fun q =>
        star (quadraticRow (left j) (CompletedGauss.primaryGenerator (rows i)) * a j) *
          (quadraticRow (right k) (CompletedGauss.primaryGenerator (rows i)) * b k) * F q i j k)
    calc
      _ = (∑ D ∈ S, if D ∣ left j then ∑ E ∈ T, if E ∣ right k then
          (if D*E=d then
            star (quadraticRow (left j) (CompletedGauss.primaryGenerator (rows i)) * a j) *
              (quadraticRow (right k) (CompletedGauss.primaryGenerator (rows i)) * b k) * F (D*E) i j k
          else 0) else 0 else 0) := by
        apply Finset.sum_congr rfl
        intro D hD
        by_cases hd : D ∣ left j
        · simp only [ite_eq_left hd]
          apply Finset.sum_congr rfl
          intro E hE
          by_cases he : E ∣ right k <;> by_cases hde : D*E=d <;>
            simp [originalTerm,hc,hd,he,hde]
        · simp [originalTerm,hc,hd]
      _ = _ := by simpa [originalTerm,hc] using hd
  · simp [originalTerm,hc]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalColumnSum_product_divisor (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (d : Ideal O) (i : m)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T)
    (F : Ideal O → m → n → p → ℂ) :
    (∑ j, ∑ k, if d ∣ left j*right k then
      originalTerm rows left right a b 1 1 i j k * F d i j k else 0) =
    ∑ D ∈ S, ∑ E ∈ T, if D*E=d then
      (∑ j, ∑ k, originalTerm rows left right a b D E i j k * F (D*E) i j k) else 0 := by
  calc
    _ = ∑ j, ∑ k, ∑ D ∈ S, ∑ E ∈ T, if D*E=d then
        originalTerm rows left right a b D E i j k * F (D*E) i j k else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      exact (originalTerm_product_divisor S T rows left right a b d i j k hleft hright hS hT F).symm
    _ = ∑ D ∈ S, ∑ E ∈ T, ∑ j, ∑ k, if D*E=d then
        originalTerm rows left right a b D E i j k * F (D*E) i j k else 0 :=
      four_sums_exchange Finset.univ Finset.univ S T _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      by_cases h : D*E=d <;> simp [h]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalColumnSum_divisor_rectangles (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (i : m)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T)
    (P : Ideal O → m → Prop) [DecidablePred (fun d => P d i)]
    (F : Ideal O → m → n → p → ℂ) :
    (∑ d ∈ K, if P d i then ‖∑ j, ∑ k, if d ∣ left j*right k then
      originalTerm rows left right a b 1 1 i j k * F d i j k else 0‖ else 0) ≤
    ∑ D ∈ S, ∑ E ∈ T, if D*E ∈ K then if P (D*E) i then
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * F (D*E) i j k‖ else 0 else 0 := by
  let B := fun D E => ∑ j, ∑ k, originalTerm rows left right a b D E i j k * F (D*E) i j k
  have hpoint (d : Ideal O) :
      (if P d i then ‖∑ j, ∑ k, if d ∣ left j*right k then
        originalTerm rows left right a b 1 1 i j k * F d i j k else 0‖ else 0) ≤
      ∑ D ∈ S, ∑ E ∈ T, if D*E=d ∧ P d i then ‖B D E‖ else 0 := by
    by_cases hp : P d i
    · simp only [hp, and_true]
      rw [originalColumnSum_product_divisor S T rows left right a b d i hleft hright hS hT F]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro D hD
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro E hE
      by_cases h : D*E=d <;> simp [h,B]
    · simp [hp]
  calc
    _ ≤ ∑ d ∈ K, ∑ D ∈ S, ∑ E ∈ T, if D*E=d ∧ P d i then ‖B D E‖ else 0 :=
      Finset.sum_le_sum (fun d hd => hpoint d)
    _ = ∑ D ∈ S, ∑ E ∈ T, ∑ d ∈ K, if D*E=d ∧ P d i then ‖B D E‖ else 0 :=
      three_sums_exchange K S T _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      have heq (d : Ideal O) : (if D*E=d ∧ P d i then ‖B D E‖ else 0) =
          if d=D*E then (if P (D*E) i then ‖B D E‖ else 0) else 0 := by
        by_cases h : d=D*E
        · subst d
          simp
        · simp [h,Ne.symm h]
      simp_rw [heq]
      simp only [Finset.sum_ite_eq', B]

end


lemma positive_ideal_dyadic_exists (N : ℝ) (D : Ideal O)
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    ∃ j ∈ Finset.range (columnDyadicLength N + 1),
      (2 : ℝ)^j/2 < (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ (2 : ℝ)^j := by
  have hp : 1 ≤ Ideal.absNorm D := by exact_mod_cast hD
  exact exists_dyadic_shell (Ideal.absNorm D) (columnDyadicLength N) hp
    (hDN.trans (columnDyadicLength_cover N))

def divisorDyadicLabel (N : ℝ) (D : Ideal O) : Fin (columnDyadicLength N+1) :=
  if h : 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N then
    ⟨(positive_ideal_dyadic_exists N D h.1 h.2).choose,
      Finset.mem_range.mp (positive_ideal_dyadic_exists N D h.1 h.2).choose_spec.1⟩
  else ⟨0,by omega⟩

def divisorDyadicBin (S : Finset (Ideal O)) (N : ℝ)
    (j : Fin (columnDyadicLength N+1)) : Finset (Ideal O) :=
  S.filter (fun D => divisorDyadicLabel N D = j)

def divisorDyadicScale (j : ℕ) : ℝ := max 1 ((2 : ℝ)^j/2)

lemma divisorDyadicLabel_bounds (N : ℝ) (D : Ideal O)
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    (2 : ℝ)^(divisorDyadicLabel N D).val/2 < (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ (2 : ℝ)^(divisorDyadicLabel N D).val := by
  unfold divisorDyadicLabel
  rw [dite_eq_left ⟨hD,hDN⟩]
  exact (positive_ideal_dyadic_exists N D hD hDN).choose_spec.2

lemma divisorDyadicScale_ge_one (j : ℕ) : 1 ≤ divisorDyadicScale j := le_max_left _ _

theorem divisorDyadicBin_bounds (S : Finset (Ideal O)) (N : ℝ)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (j : Fin (columnDyadicLength N+1)) (D : Ideal O) (hD : D ∈ divisorDyadicBin S N j) :
    divisorDyadicScale j.val ≤ (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ 2 * divisorDyadicScale j.val := by
  obtain ⟨hDS,hj⟩ := Finset.mem_filter.mp hD
  have hd := hS D hDS
  have hb := divisorDyadicLabel_bounds N D hd.1 hd.2
  rw [hj] at hb
  refine ⟨max_le hd.1 hb.1.le, ?_⟩
  have hm : (2 : ℝ)^j.val/2 ≤ divisorDyadicScale j.val := le_max_right _ _
  linarith [hb.2]

theorem divisorDyadicBin_scale_le (S : Finset (Ideal O)) (N : ℝ)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (j : Fin (columnDyadicLength N+1)) (hj : (divisorDyadicBin S N j).Nonempty) :
    divisorDyadicScale j.val ≤ N := by
  obtain ⟨D,hD⟩ := hj
  exact (divisorDyadicBin_bounds S N hS j D hD).1.trans (hS D (Finset.mem_filter.mp hD).1).2

theorem sum_divisorDyadicBins {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal O)) (N : ℝ) (f : Ideal O → A) :
    (∑ D ∈ S, f D) = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j, f D := by
  simp only [divisorDyadicBin,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  simp

theorem sum_divisorDyadicRectangles {A : Type*} [AddCommMonoid A]
    (S T : Finset (Ideal O)) (N : ℝ) (f : Ideal O → Ideal O → A) :
    (∑ D ∈ S, ∑ E ∈ T, f D E) =
      ∑ j : Fin (columnDyadicLength N+1), ∑ k : Fin (columnDyadicLength N+1),
        ∑ D ∈ divisorDyadicBin S N j, ∑ E ∈ divisorDyadicBin T N k, f D E := by
  calc
    _ = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j,
        ∑ E ∈ T, f D E := sum_divisorDyadicBins S N _
    _ = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j,
        ∑ k : Fin (columnDyadicLength N+1), ∑ E ∈ divisorDyadicBin T N k, f D E := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro D hD
      exact sum_divisorDyadicBins T N (f D)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm

def columnDivisorPool {n : Type*} [Fintype n] (left : n → Ideal O) : Finset (Ideal O) :=
  Finset.univ.biUnion (fun j => IdealMobiusDivisorSum.idealDivisors (left j))

theorem mem_columnDivisorPool_of_dvd {n : Type*} [Fintype n]
    (left : n → Ideal O) (hleft : ∀ j, left j ≠ 0) (j : n) (D : Ideal O)
    (hD : D ∣ left j) : D ∈ columnDivisorPool left := by
  apply Finset.mem_biUnion.mpr
  exact ⟨j,Finset.mem_univ j,(IdealMobiusDivisorSum.mem_idealDivisors (hleft j)).mpr hD⟩

theorem columnDivisorPool_norm_bounds {n : Type*} [Fintype n]
    (left : n → Ideal O) (hleft : ∀ j, left j ≠ 0) (N : ℝ)
    (hN : ∀ j, (Ideal.absNorm (left j) : ℝ) ≤ N)
    (D : Ideal O) (hD : D ∈ columnDivisorPool left) :
    1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N := by
  obtain ⟨j,hj,hDj⟩ := Finset.mem_biUnion.mp hD
  have hd := (IdealMobiusDivisorSum.mem_idealDivisors (hleft j)).mp hDj
  have hDz : D ≠ 0 := by
    intro hz
    rw [hz,zero_dvd_iff] at hd
    exact hleft j hd
  have hDN : Ideal.absNorm D ≤ Ideal.absNorm (left j) :=
    Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (fun h => hleft j (Ideal.absNorm_eq_zero_iff.mp h)))
      (map_dvd Ideal.absNorm hd)
  refine ⟨?_,(Nat.cast_le.mpr hDN).trans (hN j)⟩
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hDz (Ideal.absNorm_eq_zero_iff.mp h))

end CanonicalQuadraticSieve

end

end OAI
