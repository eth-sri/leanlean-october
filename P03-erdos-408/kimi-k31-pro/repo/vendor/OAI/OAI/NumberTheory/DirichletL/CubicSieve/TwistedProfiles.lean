module

public import OAI.NumberTheory.DirichletL.QuadraticSieve.TruncatedSecondTransfer

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

namespace SecondPassArithmetic

section
open JointLogSeparation
open FirstPassCubeLabels (jLabel)
open SecondPassIntegration (elementNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

open FirstPassCubeLabels (columnLog primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)
open FourierBridge (logPhase)
open SecondPassIntegration (conjugateProfile)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hp

end SecondPassArithmetic

namespace CubicEisenstein
open scoped BigOperators Classical MatrixGroups Matrix Topology

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

abbrev UpperCoordinates := {p : ℂ × ℝ // 0 < p.2}

def coordinateSection (w : UpperCoordinates) : SL(2,ℂ) :=
  upperSection w.1.1 w.1.2 w.2

lemma continuous_coordinate_inverse_operator :
    Continuous (fun w : UpperCoordinates => rowOperator (coordinateSection w)⁻¹) := by
  have hroot : Continuous (fun w : UpperCoordinates => (Real.sqrt w.1.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_snd.comp continuous_subtype_val))
  have hne : ∀ w : UpperCoordinates, (Real.sqrt w.1.2 : ℂ) ≠ 0 := fun w =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr w.2).ne'
  apply continuous_clm_apply.mpr
  intro u
  apply continuous_pi
  intro i
  change Continuous (fun w : UpperCoordinates =>
    Matrix.vecMul u (Matrix.adjugate (coordinateSection w : Matrix (Fin 2) (Fin 2) ℂ)) i)
  simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,coordinateSection,upperSection,
    Matrix.SpecialLinearGroup.coe_mk,Matrix.adjugate_fin_two]
  fin_cases i
  · change Continuous (fun w : UpperCoordinates =>
      u 0 * (Real.sqrt w.1.2 : ℂ)⁻¹ + u 1 * (-0))
    exact (continuous_const.mul (hroot.inv₀ hne)).add
      (continuous_const.mul continuous_const)
  · change Continuous (fun w : UpperCoordinates =>
      u 0 * (-(w.1.1 / (Real.sqrt w.1.2 : ℂ))) + u 1 * (Real.sqrt w.1.2 : ℂ))
    exact (continuous_const.mul ((continuous_fst.comp continuous_subtype_val).div hroot hne).neg).add
      (continuous_const.mul hroot)

lemma continuous_coordinate_rowBound :
    Continuous (fun w : UpperCoordinates => rowBound (coordinateSection w)) :=
  continuous_const.mul (continuous_const.add continuous_coordinate_inverse_operator.norm)

lemma continuous_coordinate_summand (x : CuspCosets) :
    Continuous (fun p : UpperCoordinates × ℂ => summand (coordinateSection p.1) p.2 x) := by
  have hv : Continuous (fun p : UpperCoordinates × ℂ => p.1.1.2) :=
    (continuous_snd.comp continuous_subtype_val).comp continuous_fst
  have hz : Continuous (fun p : UpperCoordinates × ℂ => p.1.1.1) :=
    (continuous_fst.comp continuous_subtype_val).comp continuous_fst
  simp only [coordinateSection,summand_upperSection]
  apply continuous_const.mul
  apply Continuous.cpow
  · apply Complex.continuous_ofReal.comp
    apply hv.div
    · unfold heightDenominator
      exact ((continuous_const.mul hz).add continuous_const).norm.pow 2 |>.add
        (continuous_const.mul (hv.pow 2))
    · intro p
      exact (heightDenominator_pos _ _ p.1.2 _ (embeddedRow_ne_zero x)).ne'
  · exact continuous_snd
  · intro p
    exact Complex.ofReal_mem_slitPlane.mpr (div_pos p.1.2
      (heightDenominator_pos _ _ p.1.2 _ (embeddedRow_ne_zero x)))

lemma coordinate_summable_majorant (C a b : ℝ) (hC : 0 < C)
    (ha : 2 < a) (hb : 2 < b) :
    ∃ M : CuspCosets → ℝ, Summable M ∧ (∀ x,0 ≤ M x) ∧
      ∀ p : UpperCoordinates × ℂ,
        rowBound (coordinateSection p.1) ≤ C → a ≤ p.2.re → p.2.re ≤ b →
        ∀ x, ‖summand (coordinateSection p.1) p.2 x‖ ≤ M x := by
  let weight (t : ℝ) (x : CuspCosets) :=
    C^(2*t)*‖rowCoordinates (cosetRow x)‖^(-(2*t))
  have hsum (t : ℝ) (ht : 2<t) : Summable (weight t) := by
    have hinj : Function.Injective (fun x : CuspCosets => rowCoordinates (cosetRow x)) :=
      rowCoordinates_injective.comp cosetRow_injective
    exact ((summable_integer_four_rpow (2*t) (by linarith)).comp_injective hinj).mul_left _
  refine ⟨fun x => weight a x + weight b x,(hsum a ha).add (hsum b hb),?_,?_⟩
  · intro x
    dsimp [weight]
    positivity
  · intro p hbound hpa hpb x
    apply (norm_summand_strip (coordinateSection p.1) a b p.2 hpa hpb x).trans
    apply add_le_add
    · apply (norm_summand_bound (coordinateSection p.1) (a:ℂ) (by simpa using lt_trans (by norm_num) ha) x).trans
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (rowBound_pos _).le hbound (by simpa only [Complex.ofReal_re] using (show 0 ≤ 2*a by linarith))) (by positivity)
    · apply (norm_summand_bound (coordinateSection p.1) (b:ℂ) (by simpa using lt_trans (by norm_num) hb) x).trans
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (rowBound_pos _).le hbound (by simpa only [Complex.ofReal_re] using (show 0 ≤ 2*b by linarith))) (by positivity)

theorem coordinate_eisenstein_continuousAt (p : UpperCoordinates × ℂ) (hp : 2 < p.2.re) :
    ContinuousAt (fun q : UpperCoordinates × ℂ => eisenstein (coordinateSection q.1) q.2) p := by
  let a : ℝ := (2+p.2.re)/2
  let b : ℝ := p.2.re+1
  let C : ℝ := rowBound (coordinateSection p.1)+1
  let region : Set (UpperCoordinates × ℂ) := {q |
    rowBound (coordinateSection q.1) < C ∧ a < q.2.re ∧ q.2.re < b}
  have ha : 2<a := by dsimp [a]; linarith
  have hb : 2<b := by dsimp [b]; linarith
  have hC : 0<C := by dsimp [C]; linarith [rowBound_pos (coordinateSection p.1)]
  obtain ⟨M,hM,hMnonneg,hbound⟩ := coordinate_summable_majorant C a b hC ha hb
  have hopen : IsOpen region := by
    exact (isOpen_lt (continuous_coordinate_rowBound.comp continuous_fst) continuous_const).inter
      ((isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd)).inter
        (isOpen_lt (Complex.continuous_re.comp continuous_snd) continuous_const))
  have hmem : p ∈ region := by
    dsimp [region,a,b,C]
    constructor
    · linarith
    · constructor <;> linarith
  have hcont : ContinuousOn (fun q : UpperCoordinates × ℂ =>
      ∑' x : CuspCosets, summand (coordinateSection q.1) q.2 x) region := by
    apply continuousOn_tsum (fun x => (continuous_coordinate_summand x).continuousOn) hM
    intro x q hq
    exact hbound q hq.1.le hq.2.1.le hq.2.2.le x
  exact (hcont p hmem).continuousAt (hopen.mem_nhds hmem)

theorem upperEisenstein_joint_continuousAt (p : UpperCoordinates × ℂ)
    (hp : 2 < p.2.re) :
    ContinuousAt (fun q : UpperCoordinates × ℂ =>
      upperEisenstein q.1.1.1 q.1.1.2 q.1.2 q.2) p :=
  coordinate_eisenstein_continuousAt p hp

end CubicEisenstein

open scoped BigOperators Classical Topology

namespace CubicEisenstein

def logRatioPower (s : ℂ) (v q : ℝ) : ℂ :=
  Complex.exp (s * ((Real.log v - Real.log q : ℝ) : ℂ))

lemma logRatioPower_eq_cpow (s : ℂ) {v q : ℝ} (hv : 0<v) (hq : 0<q) :
    logRatioPower s v q = ((v/q : ℝ):ℂ)^s := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hv hq).ne'),
    ← Complex.ofReal_log (div_pos hv hq).le, Real.log_div hv.ne' hq.ne']
  unfold logRatioPower
  congr 1
  ring

lemma hasDerivAt_logRatioPower (s : ℂ) {f g : ℝ → ℝ} {x f' g' : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (hf0 : f x ≠ 0) (hg0 : g x ≠ 0) :
    HasDerivAt (fun t => logRatioPower s (f t) (g t))
      (logRatioPower s (f x) (g x) * s * ((f'/f x-g'/g x : ℝ):ℂ)) x := by
  convert (((hf.log hf0).sub (hg.log hg0)).ofReal_comp.const_mul s).cexp using 1 <;>
    dsimp [logRatioPower] ; ring

lemma hasDerivAt_deriv_logRatioPower (s : ℂ) (f g df dg : ℝ → ℝ) (x ddf ddg : ℝ)
    (hf : ∀t, HasDerivAt f (df t) t) (hg : ∀t, HasDerivAt g (dg t) t)
    (hdf : HasDerivAt df ddf x) (hdg : HasDerivAt dg ddg x)
    (hf0 : f x ≠ 0) (hg0 : g x ≠ 0) :
    HasDerivAt (deriv (fun t => logRatioPower s (f t) (g t)))
      (logRatioPower s (f x) (g x) *
        (s^2 * ((df x/f x-dg x/g x : ℝ):ℂ)^2 +
         s * (((ddf*f x-df x*df x)/(f x)^2 -
           (ddg*g x-dg x*dg x)/(g x)^2 : ℝ):ℂ))) x := by
  have hnear : ∀ᶠ t in 𝓝 x, f t ≠ 0 ∧ g t ≠ 0 :=
    ((hf x).continuousAt.eventually_ne hf0).and ((hg x).continuousAt.eventually_ne hg0)
  have heq : (deriv (fun t => logRatioPower s (f t) (g t))) =ᶠ[𝓝 x]
      (fun t => logRatioPower s (f t) (g t) * s * ((df t/f t-dg t/g t : ℝ):ℂ)) := by
    filter_upwards [hnear] with t ht
    exact (hasDerivAt_logRatioPower s (hf t) (hg t) ht.1 ht.2).deriv
  have hfirst := hasDerivAt_logRatioPower s (hf x) (hg x) hf0 hg0
  have hsecond := ((hdf.div (hf x) hf0).sub (hdg.div (hg x) hg0)).ofReal_comp
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert (hfirst.mul_const s).mul hsecond using 1 ;
    simp only [Pi.sub_apply,Pi.div_apply] ; ring

def quadraticHeightDenominator (A B C D x y v : ℝ) : ℝ :=
  A*(x^2+y^2+v^2)+2*(B*x+C*y)+D

lemma quadraticHeightDenominator_hasDerivAt_x (A B C D x y v : ℝ) :
    HasDerivAt (fun t => quadraticHeightDenominator A B C D t y v)
      (2*(A*x+B)) x := by
  convert (((((hasDerivAt_id x).pow 2).add_const (y^2)).add_const (v^2)).const_mul A).add
    ((((hasDerivAt_id x).const_mul B).add_const (C*y)).const_mul 2) |>.add_const D using 1 <;>
    dsimp [quadraticHeightDenominator] ; ring

lemma quadraticHeightDenominator_hasDerivAt_y (A B C D x y v : ℝ) :
    HasDerivAt (fun t => quadraticHeightDenominator A B C D x t v)
      (2*(A*y+C)) y := by
  convert (((((hasDerivAt_id y).pow 2).const_add (x^2)).add_const (v^2)).const_mul A).add
    ((((hasDerivAt_id y).const_mul C).const_add (B*x)).const_mul 2) |>.add_const D using 1 <;>
    dsimp [quadraticHeightDenominator] ; ring

lemma quadraticHeightDenominator_hasDerivAt_v (A B C D x y v : ℝ) :
    HasDerivAt (fun t => quadraticHeightDenominator A B C D x y t)
      (2*A*v) v := by
  convert ((((hasDerivAt_id v).pow 2).const_add (x^2+y^2)).const_mul A).add_const
    (2*(B*x+C*y)+D) using 1 <;> dsimp [quadraticHeightDenominator] <;> ring_nf

def spatialHeightPower (s : ℂ) (A B C D x y v : ℝ) : ℂ :=
  logRatioPower s v (quadraticHeightDenominator A B C D x y v)

def heightLogDx (A B C D x y v : ℝ) : ℝ :=
  -(2*(A*x+B)/quadraticHeightDenominator A B C D x y v)
def heightLogDy (A B C D x y v : ℝ) : ℝ :=
  -(2*(A*y+C)/quadraticHeightDenominator A B C D x y v)
def heightLogDv (A B C D x y v : ℝ) : ℝ :=
  1/v - 2*A*v/quadraticHeightDenominator A B C D x y v

def heightLogDxx (A B C D x y v : ℝ) : ℝ :=
  -((2*A*quadraticHeightDenominator A B C D x y v -
    (2*(A*x+B))*(2*(A*x+B)))/(quadraticHeightDenominator A B C D x y v)^2)
def heightLogDyy (A B C D x y v : ℝ) : ℝ :=
  -((2*A*quadraticHeightDenominator A B C D x y v -
    (2*(A*y+C))*(2*(A*y+C)))/(quadraticHeightDenominator A B C D x y v)^2)
def heightLogDvv (A B C D x y v : ℝ) : ℝ :=
  -(1/v^2) - ((2*A*quadraticHeightDenominator A B C D x y v -
    (2*A*v)*(2*A*v))/(quadraticHeightDenominator A B C D x y v)^2)

lemma deriv_spatialHeightPower_v (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (spatialHeightPower s A B C D x y) v =
      spatialHeightPower s A B C D x y v * s * (heightLogDv A B C D x y v : ℂ) := by
  exact (hasDerivAt_logRatioPower s (hasDerivAt_id v)
    (quadraticHeightDenominator_hasDerivAt_v A B C D x y v) hv hq).deriv

lemma deriv2_spatialHeightPower_x (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (deriv (fun t => spatialHeightPower s A B C D t y v)) x =
      spatialHeightPower s A B C D x y v *
        (s^2*(heightLogDx A B C D x y v : ℂ)^2 +
          s*(heightLogDxx A B C D x y v : ℂ)) := by
  have h := hasDerivAt_deriv_logRatioPower s (fun _ => v)
    (fun t => quadraticHeightDenominator A B C D t y v) (fun _ => 0)
    (fun t => 2*(A*t+B)) x 0 (2*A)
    (fun t => hasDerivAt_const t v)
    (fun t => quadraticHeightDenominator_hasDerivAt_x A B C D t y v)
    (hasDerivAt_const x 0) (by simpa only [id_eq,mul_one] using ((hasDerivAt_id x).const_mul A |>.add_const B).const_mul 2)
    hv hq
  simpa only [spatialHeightPower,heightLogDx,heightLogDxx,zero_div,zero_sub,zero_mul,sub_zero] using h.deriv

lemma deriv2_spatialHeightPower_y (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (deriv (fun t => spatialHeightPower s A B C D x t v)) y =
      spatialHeightPower s A B C D x y v *
        (s^2*(heightLogDy A B C D x y v : ℂ)^2 +
          s*(heightLogDyy A B C D x y v : ℂ)) := by
  have h := hasDerivAt_deriv_logRatioPower s (fun _ => v)
    (fun t => quadraticHeightDenominator A B C D x t v) (fun _ => 0)
    (fun t => 2*(A*t+C)) y 0 (2*A)
    (fun t => hasDerivAt_const t v)
    (fun t => quadraticHeightDenominator_hasDerivAt_y A B C D x t v)
    (hasDerivAt_const y 0) (by simpa only [id_eq,mul_one] using ((hasDerivAt_id y).const_mul A |>.add_const C).const_mul 2)
    hv hq
  simpa only [spatialHeightPower,heightLogDy,heightLogDyy,zero_div,zero_sub,zero_mul,sub_zero] using h.deriv

lemma deriv2_spatialHeightPower_v (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (deriv (spatialHeightPower s A B C D x y)) v =
      spatialHeightPower s A B C D x y v *
        (s^2*(heightLogDv A B C D x y v : ℂ)^2 +
          s*(heightLogDvv A B C D x y v : ℂ)) := by
  change deriv (deriv (fun t => logRatioPower s t
    (quadraticHeightDenominator A B C D x y t))) v = _
  have h := hasDerivAt_deriv_logRatioPower s (fun t => t)
    (fun t => quadraticHeightDenominator A B C D x y t) (fun _ => 1)
    (fun t => 2*A*t) v 0 (2*A)
    (fun t => hasDerivAt_id t)
    (fun t => quadraticHeightDenominator_hasDerivAt_v A B C D x y t)
    (hasDerivAt_const v 1) (by simpa only [id_eq,mul_one] using (hasDerivAt_id v).const_mul (2*A))
    hv hq
  simpa only [spatialHeightPower,heightLogDv,heightLogDvv,zero_mul,zero_sub,one_mul,neg_div] using h.deriv

lemma quadraticHeight_gradient_square (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) :
    (A*x+B)^2 + (A*y+C)^2 + (A*v)^2 =
      A*quadraticHeightDenominator A B C D x y v := by
  unfold quadraticHeightDenominator
  nlinarith [hrel]

lemma heightLog_eikonal (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : v≠0)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    v^2 * ((heightLogDx A B C D x y v)^2 +
      (heightLogDy A B C D x y v)^2 + (heightLogDv A B C D x y v)^2) = 1 := by
  calc
    _ = 1 + 4*v^2/(quadraticHeightDenominator A B C D x y v)^2 *
        ((A*x+B)^2+(A*y+C)^2+(A*v)^2 - A*quadraticHeightDenominator A B C D x y v) := by
      unfold heightLogDx heightLogDy heightLogDv
      field_simp [hv,hq]
      ; ring
    _ = 1 := by rw [quadraticHeight_gradient_square A B C D x y v hrel]; ring

lemma heightLog_laplacian (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : v≠0)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    v^2 * (heightLogDxx A B C D x y v +
      heightLogDyy A B C D x y v + heightLogDvv A B C D x y v) -
      v*heightLogDv A B C D x y v = -2 := by
  calc
    _ = -2 + 4*v^2/(quadraticHeightDenominator A B C D x y v)^2 *
        ((A*x+B)^2+(A*y+C)^2+(A*v)^2 - A*quadraticHeightDenominator A B C D x y v) := by
      unfold heightLogDxx heightLogDyy heightLogDvv heightLogDv
      field_simp [hv,hq]
      ; ring
    _ = -2 := by rw [quadraticHeight_gradient_square A B C D x y v hrel]; ring

def hyperbolicLaplacian (f : ℝ → ℝ → ℝ → ℂ) (x y v : ℝ) : ℂ :=
  (v:ℂ)^2 * (deriv (deriv (fun t => f t y v)) x +
    deriv (deriv (fun t => f x t v)) y + deriv (deriv (f x y)) v) -
    (v:ℂ)*deriv (f x y) v

theorem spatialHeightPower_eigenfunction (s : ℂ) (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : v≠0)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    hyperbolicLaplacian (spatialHeightPower s A B C D) x y v =
      s*(s-2)*spatialHeightPower s A B C D x y v := by
  have he : (v:ℂ)^2 * ((heightLogDx A B C D x y v : ℂ)^2 +
      (heightLogDy A B C D x y v : ℂ)^2 + (heightLogDv A B C D x y v : ℂ)^2) = 1 := by
    exact_mod_cast heightLog_eikonal A B C D x y v hrel hv hq
  have hl : (v:ℂ)^2 * ((heightLogDxx A B C D x y v : ℂ) +
      (heightLogDyy A B C D x y v : ℂ) + (heightLogDvv A B C D x y v : ℂ)) -
      (v:ℂ)*(heightLogDv A B C D x y v : ℂ) = -2 := by
    exact_mod_cast heightLog_laplacian A B C D x y v hrel hv hq
  unfold hyperbolicLaplacian
  rw [deriv2_spatialHeightPower_x s A B C D x y v hv hq,
    deriv2_spatialHeightPower_y s A B C D x y v hv hq,
    deriv2_spatialHeightPower_v s A B C D x y v hv hq,
    deriv_spatialHeightPower_v s A B C D x y v hv hq]
  calc
    _ = spatialHeightPower s A B C D x y v *
        (s^2*((v:ℂ)^2*((heightLogDx A B C D x y v : ℂ)^2 +
          (heightLogDy A B C D x y v : ℂ)^2 + (heightLogDv A B C D x y v : ℂ)^2)) +
        s*((v:ℂ)^2*((heightLogDxx A B C D x y v : ℂ) +
          (heightLogDyy A B C D x y v : ℂ) + (heightLogDvv A B C D x y v : ℂ)) -
          (v:ℂ)*(heightLogDv A B C D x y v : ℂ))) := by ring
    _ = _ := by rw [he,hl]; ring

lemma complex_row_quadratic_relation (c d : ℂ) :
    Complex.normSq c * Complex.normSq d = (c*star d).re^2 + (-(c*star d).im)^2 := by
  simp only [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im]
  ring

lemma heightDenominator_eq_quadratic (u : Fin 2 → ℂ) (x y v : ℝ) :
    heightDenominator ((x:ℂ)+(y:ℂ)*Complex.I) v u =
      quadraticHeightDenominator (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
        (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) x y v := by
  unfold heightDenominator quadraticHeightDenominator
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

def actualHeightPower (s : ℂ) (u : Fin 2 → ℂ) (x y v : ℝ) : ℂ :=
  ((transformedHeight ((x:ℂ)+(y:ℂ)*Complex.I) v u : ℝ) : ℂ)^s

lemma actualHeightPower_eq_spatial (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (x y v : ℝ) (hv : 0<v) :
    actualHeightPower s u x y v =
      spatialHeightPower s (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
        (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) x y v := by
  rw [actualHeightPower,spatialHeightPower,logRatioPower_eq_cpow s hv]
  · rw [transformedHeight,heightDenominator_eq_quadratic]
  · rw [← heightDenominator_eq_quadratic]
    exact heightDenominator_pos _ _ hv u hu

lemma hyperbolicLaplacian_const_mul (c : ℂ) (f : ℝ → ℝ → ℝ → ℂ) (x y v : ℝ) :
    hyperbolicLaplacian (fun x y v => c*f x y v) x y v =
      c*hyperbolicLaplacian f x y v := by
  unfold hyperbolicLaplacian
  simp only [deriv_const_mul_field',deriv_const_mul_field]
  ring

lemma eigenfunction_summand_eq_actual_series (s : ℂ) (r : CuspCosets)
    (x y v : ℝ) (hv : 0<v) :
    (cosetCharacter r)⁻¹ * actualHeightPower s (embeddedRow r) x y v =
      summand (upperSection ((x:ℂ)+(y:ℂ)*Complex.I) v hv) s r := by
  rw [summand_upperSection]
  rfl

end CubicEisenstein

end

end OAI
