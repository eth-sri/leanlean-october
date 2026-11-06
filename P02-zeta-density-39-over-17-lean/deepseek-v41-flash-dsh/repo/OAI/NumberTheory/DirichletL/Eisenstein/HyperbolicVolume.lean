module
public import OAI.NumberTheory.DirichletL.CubicSieve.ArithmeticBins

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set

namespace CubicEisenstein
open Filter MeasureTheory EuclideanGeometry
open scoped BigOperators Classical Topology InnerProductSpace ENNReal Matrix

lemma linear_preserves_hyperbolicVolume (A : EuclideanSpatial →L[ℝ] EuclideanSpatial)
    (k : ℝ) (hk : 0<k) (hh : ∀p,(A p) 2=k*p 2) (hd : |A.det|=k^3) :
    Measure.map A hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  have hdet : A.det≠0 := by intro he; rw [he,abs_zero] at hd; exact (pow_ne_zero 3 hk.ne') hd.symm
  have hker : LinearMap.ker A.toLinearMap=⊥ := by
    by_contra hn
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hn)
  have hinj : Function.Injective A := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective A := (LinearMap.injective_iff_surjective).mp hinj
  apply hyperbolic_volume_map_of_jacobian A (fun _ => A) A.continuous.measurable
    (fun p hp => A.hasFDerivAt) hinj.injOn
  · apply Set.Subset.antisymm
    · rintro q ⟨p,hp,rfl⟩
      exact show 0<(A p) 2 by rw [hh]; exact mul_pos hk hp
    · intro q hq
      obtain ⟨p,hp⟩ := hsurj q
      refine ⟨p,?_,hp⟩
      change 0<p 2
      have h := hh p
      rw [hp] at h
      exact (mul_pos_iff_of_pos_left hk).mp (h.symm ▸ hq)
  · intro p hp
    rw [hd,hyperbolicDensity,hyperbolicDensity,hh]
    rw [←ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp

lemma translation_preserves_hyperbolicVolume (u : EuclideanSpatial) (hu : u 2=0) :
    Measure.map (fun p => p+u) hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply hyperbolic_volume_map_of_jacobian (fun p => p+u) (fun _ => ContinuousLinearMap.id ℝ _)
    (continuous_id.add continuous_const).measurable
    (fun p hp => (hasFDerivAt_id p).add_const u) (add_left_injective u).injOn
  · apply Set.Subset.antisymm
    · rintro q ⟨p,hp,rfl⟩
      simpa [euclideanUpperHalf,hu] using hp
    · intro p hp
      refine ⟨p-u,?_,sub_add_cancel p u⟩
      simpa [euclideanUpperHalf,hu] using hp
  · intro p hp
    have hid : (ContinuousLinearMap.id ℝ EuclideanSpatial).det=1 := by
      change LinearMap.det (LinearMap.id : EuclideanSpatial →ₗ[ℝ] EuclideanSpatial)=1
      simp
    simp [hyperbolicDensity,hu,hid]

def euclideanMatrixOperator (M : Matrix (Fin 3) (Fin 3) ℝ) :
    EuclideanSpatial →L[ℝ] EuclideanSpatial := M.toEuclideanLin.toContinuousLinearMap

lemma euclideanMatrixOperator_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (p : EuclideanSpatial)
    (j : Fin 3) : euclideanMatrixOperator M p j=∑i,M j i*p i := rfl

lemma euclideanMatrixOperator_det (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (euclideanMatrixOperator M).det=M.det := by
  change LinearMap.det (Matrix.toEuclideanLin M)=M.det
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin]

def euclideanWeylReflection : EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  euclideanMatrixOperator !![-1,0,0;0,1,0;0,0,1]

lemma euclideanWeylReflection_apply (p : EuclideanSpatial) :
    euclideanWeylReflection p 0= -p 0 ∧ euclideanWeylReflection p 1=p 1 ∧
      euclideanWeylReflection p 2=p 2 := by
  simp [euclideanWeylReflection,euclideanMatrixOperator_apply,Fin.sum_univ_three]

lemma euclideanWeylReflection_preserves_hyperbolicVolume :
    Measure.map euclideanWeylReflection hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply linear_preserves_hyperbolicVolume euclideanWeylReflection 1 (by norm_num)
  · intro p
    simpa using (euclideanWeylReflection_apply p).2.2
  · norm_num [euclideanWeylReflection,euclideanMatrixOperator_det,Matrix.det_fin_three]

def euclideanComplexDilation (β : ℂ) : EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  euclideanMatrixOperator !![(β^2).re,-(β^2).im,0;(β^2).im,(β^2).re,0;0,0,Complex.normSq β]

lemma euclideanComplexDilation_apply (β : ℂ) (p : EuclideanSpatial) :
    euclideanComplexDilation β p 0=(β^2).re*p 0-(β^2).im*p 1 ∧
      euclideanComplexDilation β p 1=(β^2).im*p 0+(β^2).re*p 1 ∧
      euclideanComplexDilation β p 2=Complex.normSq β*p 2 := by
  simp [euclideanComplexDilation,euclideanMatrixOperator_apply,Fin.sum_univ_three,sub_eq_add_neg]

lemma euclideanComplexDilation_det (β : ℂ) :
    (euclideanComplexDilation β).det=Complex.normSq β^3 := by
  rw [euclideanComplexDilation,euclideanMatrixOperator_det,Matrix.det_fin_three]
  have h : (β^2).re^2+(β^2).im^2=(Complex.normSq β)^2 := by
    simpa [Complex.normSq_apply,sq] using map_pow Complex.normSq β 2
  change (β^2).re*(β^2).re*Complex.normSq β-(β^2).re*0*0-
    (-(β^2).im)*(β^2).im*Complex.normSq β+(-(β^2).im)*0*0+
    0*(β^2).im*0-0*(β^2).re*0=Complex.normSq β^3
  calc
    _ = ((β^2).re^2+(β^2).im^2)*Complex.normSq β := by ring
    _ = _ := by rw [h]; ring

lemma euclideanComplexDilation_preserves_hyperbolicVolume (β : ℂ) (hβ : β≠0) :
    Measure.map (euclideanComplexDilation β) hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply linear_preserves_hyperbolicVolume (euclideanComplexDilation β) (Complex.normSq β)
    (Complex.normSq_pos.mpr hβ) (fun p => (euclideanComplexDilation_apply β p).2.2)
  rw [euclideanComplexDilation_det,abs_of_nonneg (pow_nonneg (Complex.normSq_nonneg β) 3)]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

instance hyperbolicMeasurableSpace : MeasurableSpace HyperbolicSpace := borel HyperbolicSpace
instance hyperbolicBorelSpace : BorelSpace HyperbolicSpace := ⟨rfl⟩

lemma continuous_hyperbolic_action (g : SL(2,ℂ)) :
    Continuous (fun w : HyperbolicSpace => g • w) := by
  apply (QuotientGroup.isQuotientMap_mk compactSubgroup).continuous_iff.mpr
  exact continuous_hyperbolicProjection.comp (continuous_complexSL_mul g)

def positiveCoordinateHeight (p : EuclideanSpatial) : ℝ := if 0<p 2 then p 2 else 1
lemma positiveCoordinateHeight_pos (p : EuclideanSpatial) : 0<positiveCoordinateHeight p := by
  unfold positiveCoordinateHeight
  split_ifs with hp
  · exact hp
  · norm_num

def euclideanToUpperCoordinates (p : EuclideanSpatial) : UpperCoordinates :=
  ⟨((p 0:ℂ)+Complex.I*(p 1:ℂ),positiveCoordinateHeight p),positiveCoordinateHeight_pos p⟩

def euclideanToHyperbolic (p : EuclideanSpatial) : HyperbolicSpace :=
  upperPoint (euclideanToUpperCoordinates p).1.1 (euclideanToUpperCoordinates p).1.2
    (euclideanToUpperCoordinates p).2

lemma euclideanToUpperCoordinates_measurable : Measurable euclideanToUpperCoordinates := by
  apply Measurable.subtype_mk
  apply Measurable.prodMk
  · change Measurable (fun p : EuclideanSpatial => (p 0:ℂ)+Complex.I*(p 1:ℂ))
    fun_prop
  · exact Measurable.ite euclideanUpperHalf_measurable (by fun_prop) measurable_const

lemma euclideanToHyperbolic_measurable : Measurable euclideanToHyperbolic :=
  continuous_upperCoordinates.measurable.comp euclideanToUpperCoordinates_measurable

lemma euclideanToHyperbolic_positive (p : EuclideanSpatial) (hp : 0<p 2) :
    euclideanToHyperbolic p=upperPoint ((p 0:ℂ)+Complex.I*(p 1:ℂ)) (p 2) hp := by
  unfold euclideanToHyperbolic euclideanToUpperCoordinates positiveCoordinateHeight
  simp only [ite_eq_left hp]

def hyperbolicVolume : Measure HyperbolicSpace :=
  Measure.map euclideanToHyperbolic hyperbolicEuclideanVolume

lemma hyperbolicEuclideanVolume_ae_positive :
    ∀ᵐp∂hyperbolicEuclideanVolume,0<p 2 := by
  exact (ae_restrict_mem euclideanUpperHalf_measurable).filter_mono
    ((withDensity_absolutelyContinuous (volume.restrict euclideanUpperHalf) hyperbolicDensity).ae_le)

lemma hyperbolicVolume_map_of_coordinate_action (g : SL(2,ℂ))
    (f : EuclideanSpatial → EuclideanSpatial) (hf : Measurable f)
    (hvol : Measure.map f hyperbolicEuclideanVolume=hyperbolicEuclideanVolume)
    (hcompat : ∀p,0<p 2 → euclideanToHyperbolic (f p)=g • euclideanToHyperbolic p) :
    Measure.map (fun w => g • w) hyperbolicVolume=hyperbolicVolume := by
  unfold hyperbolicVolume
  rw [Measure.map_map (continuous_hyperbolic_action g).measurable euclideanToHyperbolic_measurable]
  calc
    _ = Measure.map (euclideanToHyperbolic ∘ f) hyperbolicEuclideanVolume := by
      apply Measure.map_congr
      filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
      exact (hcompat p hp).symm
    _ = _ := by rw [←Measure.map_map euclideanToHyperbolic_measurable hf,hvol]

lemma matrix_point_coordinates (g : SL(2,ℂ)) :
    (g : HyperbolicSpace)=upperPoint (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g) := by
  obtain ⟨k,hk,hg⟩ := matrix_iwasawa_factor g
  apply Eq.symm
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  change (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*g∈compactSubgroup
  have hcancel : (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*g=k := by
    calc
      _ = (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*
          (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g)*k) :=
        congrArg (fun M => (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*M) hg
      _ = k := inv_mul_cancel_left _ _
  rwa [hcancel]

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

def matrixCross (g : SL(2,ℂ)) : ℂ := g 0 0*star (g 1 0)+g 0 1*star (g 1 1)

lemma matrixHorizontal_eq_cross_height (g : SL(2,ℂ)) :
    matrixHorizontal g=matrixCross g*(liftedHeight g:ℂ) := by
  unfold matrixHorizontal matrixCross liftedHeight
  rw [Complex.ofReal_inv]
  rfl

lemma matrixCross_upperSection (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0<v) :
    matrixCross (g*upperSection z v hv)=
      ((g 0 0*z+g 0 1)*star (g 1 0*z+g 1 1)+
        g 0 0*star (g 1 0)*(v:ℂ)^2)/(v:ℂ) := by
  have hr : (Real.sqrt v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hv).ne'
  have hrs : (Real.sqrt v:ℂ)^2=(v:ℂ) := by exact_mod_cast Real.sq_sqrt hv.le
  simp only [matrixCross,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  change (g 0 0*(Real.sqrt v:ℂ)+g 0 1*0)*star (g 1 0*(Real.sqrt v:ℂ)+g 1 1*0)+
    (g 0 0*(z/(Real.sqrt v:ℂ))+g 0 1*(Real.sqrt v:ℂ)⁻¹)*
      star (g 1 0*(z/(Real.sqrt v:ℂ))+g 1 1*(Real.sqrt v:ℂ)⁻¹)=_
  simp only [mul_zero,add_zero,star_add,star_mul,Complex.star_def,
    map_inv₀,map_div₀,Complex.conj_ofReal]
  rw [←hrs]
  field_simp
  ; ring

lemma mobius_denominator_pos (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0<v) :
    0<‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2 := by
  exact heightDenominator_pos z v hv (complexBottomRow g) (complexBottomRow_ne_zero g)

lemma upperPoint_congr {z z' : ℂ} {v v' : ℝ} (hv : 0<v) (hv' : 0<v')
    (hz : z=z') (hvv : v=v') : upperPoint z v hv=upperPoint z' v' hv' := by
  subst z'
  subst v'
  rfl

theorem mobius_upperPoint (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0<v) :
    g • upperPoint z v hv=
      upperPoint
        (((g 0 0*z+g 0 1)*star (g 1 0*z+g 1 1)+g 0 0*star (g 1 0)*(v:ℂ)^2)/
          ((‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2:ℝ):ℂ))
        (v/(‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2))
        (div_pos hv (mobius_denominator_pos g z v hv)) := by
  have hh : liftedHeight (g*upperSection z v hv)=
      v/(‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2) :=
    hyperbolicHeight_action_upperPoint g z v hv
  change (QuotientGroup.mk (g*upperSection z v hv) : HyperbolicSpace)=_
  rw [matrix_point_coordinates]
  apply upperPoint_congr _ _ _ hh
  rw [matrixHorizontal_eq_cross_height,matrixCross_upperSection,hh,Complex.ofReal_div]
  have hvc : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp

def complexTranslation (b : ℂ) : SL(2,ℂ) := ⟨!![1,b;0,1],by simp [Matrix.det_fin_two]⟩
def complexDiagonal (b : ℂ) (hb : b≠0) : SL(2,ℂ) :=
  ⟨!![b,0;0,b⁻¹],by simp [Matrix.det_fin_two,hb]⟩
def complexWeyl : SL(2,ℂ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma complexTranslation_action (b z : ℂ) (v : ℝ) (hv : 0<v) :
    complexTranslation b • upperPoint z v hv=upperPoint (z+b) v hv := by
  change (QuotientGroup.mk (complexTranslation b*upperSection z v hv) : HyperbolicSpace)=
    QuotientGroup.mk (upperSection (z+b) v hv)
  apply congrArg (fun g : SL(2,ℂ) => (QuotientGroup.mk g : HyperbolicSpace))
  apply Subtype.ext
  change (complexTranslation b : Matrix (Fin 2) (Fin 2) ℂ) *
    (upperSection z v hv : Matrix (Fin 2) (Fin 2) ℂ) =
    (upperSection (z + b) v hv : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,upperSection,Matrix.mul_apply,
      Fin.sum_univ_two,div_eq_mul_inv] ; ring

lemma complexWeyl_action (z : ℂ) (v : ℝ) (hv : 0<v) :
    complexWeyl • upperPoint z v hv=
      upperPoint (-star z/((‖z‖^2+v^2:ℝ):ℂ)) (v/(‖z‖^2+v^2))
        (div_pos hv (by nlinarith [sq_nonneg ‖z‖])) := by
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · simp [complexWeyl]
  · simp [complexWeyl]

lemma complexDiagonal_action (b : ℂ) (hb : b≠0) (z : ℂ) (v : ℝ) (hv : 0<v) :
    complexDiagonal b hb • upperPoint z v hv=
      upperPoint (b^2*z) (Complex.normSq b*v) (mul_pos (Complex.normSq_pos.mpr hb) hv) := by
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · change ((b*z+0)*star (0*z+b⁻¹)+b*star 0*(v:ℂ)^2)/
        ((‖0*z+b⁻¹‖^2+‖(0:ℂ)‖^2*v^2:ℝ):ℂ)=b^2*z
    simp only [zero_mul,mul_zero,zero_add,add_zero,star_zero,norm_zero,zero_pow (by decide : 2≠0)]
    rw [norm_inv,inv_pow,Complex.ofReal_inv]
    simp only [Complex.star_def,map_inv₀]
    have hq : ((‖b‖^2:ℝ):ℂ)=b*star b := by
      simpa [Complex.normSq_eq_norm_sq,Complex.star_def] using (Complex.mul_conj b).symm
    rw [hq]
    have hbs : star b≠0 := star_ne_zero.mpr hb
    simp only [Complex.star_def] at hbs ⊢
    field_simp

  · change v/(‖0*z+b⁻¹‖^2+‖(0:ℂ)‖^2*v^2)=Complex.normSq b*v
    simp only [zero_mul,zero_add,add_zero,norm_zero,zero_pow (by decide : 2≠0),norm_inv,inv_pow]
    rw [Complex.normSq_eq_norm_sq]
    field_simp

lemma complex_bruhat_nonzero (g : SL(2,ℂ)) (hc : g 1 0≠0) :
    g=complexTranslation (g 0 0/g 1 0)*complexDiagonal (g 1 0)⁻¹ (inv_ne_zero hc)*
      complexWeyl*complexTranslation (g 1 1/g 1 0) := by
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) ℂ) =
    (complexTranslation (g 0 0 / g 1 0) : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexDiagonal (g 1 0)⁻¹ (inv_ne_zero hc) : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexWeyl : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexTranslation (g 1 1 / g 1 0) : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,complexDiagonal,complexWeyl,Matrix.mul_apply,Fin.sum_univ_two,hc] <;>
      field_simp ; linear_combination -hd

lemma complex_bruhat_zero (g : SL(2,ℂ)) (hc : g 1 0=0) :
    ∃ha : g 0 0≠0,g=complexDiagonal (g 0 0) ha*complexTranslation (g 0 1/g 0 0) := by
  have hd : g 0 0*g 1 1=1 := by simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using g.property
  have ha : g 0 0≠0 := by intro h; simp [h] at hd
  refine ⟨ha,?_⟩
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) ℂ) =
    (complexDiagonal (g 0 0) ha : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexTranslation (g 0 1 / g 0 0) : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,complexDiagonal,Matrix.mul_apply,Fin.sum_univ_two,hc] <;>
      field_simp ; linear_combination hd

def euclideanHorizontalTranslation (b : ℂ) : EuclideanSpatial := WithLp.toLp 2 ![b.re,b.im,0]

lemma complexTranslation_preserves_hyperbolicVolume (b : ℂ) :
    Measure.map (fun w => complexTranslation b • w) hyperbolicVolume=hyperbolicVolume := by
  apply hyperbolicVolume_map_of_coordinate_action (complexTranslation b)
    (fun p => p+euclideanHorizontalTranslation b) (continuous_id.add continuous_const).measurable
    (translation_preserves_hyperbolicVolume _ rfl)
  intro p hp
  have hq : 0<(p+euclideanHorizontalTranslation b) 2 := by simpa [euclideanHorizontalTranslation] using hp
  rw [euclideanToHyperbolic_positive _ hq,euclideanToHyperbolic_positive _ hp,complexTranslation_action]
  apply upperPoint_congr
  · apply Complex.ext <;> simp [euclideanHorizontalTranslation]
  · simp [euclideanHorizontalTranslation]

lemma complexDiagonal_preserves_hyperbolicVolume (b : ℂ) (hb : b≠0) :
    Measure.map (fun w => complexDiagonal b hb • w) hyperbolicVolume=hyperbolicVolume := by
  apply hyperbolicVolume_map_of_coordinate_action (complexDiagonal b hb)
    (euclideanComplexDilation b) (euclideanComplexDilation b).continuous.measurable
    (euclideanComplexDilation_preserves_hyperbolicVolume b hb)
  intro p hp
  obtain ⟨h0,h1,h2⟩ := euclideanComplexDilation_apply b p
  have hq : 0<(euclideanComplexDilation b p) 2 := by rw [h2]; exact mul_pos (Complex.normSq_pos.mpr hb) hp
  rw [euclideanToHyperbolic_positive _ hq,euclideanToHyperbolic_positive _ hp,complexDiagonal_action]
  apply upperPoint_congr
  · rw [h0,h1]
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] ; ring
  · exact h2

lemma euclidean_complex_norm_sq (p : EuclideanSpatial) :
    ‖(p 0:ℂ)+Complex.I*(p 1:ℂ)‖^2+(p 2)^2=‖p‖^2 := by
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_three,sq]

def euclideanWeylAction (p : EuclideanSpatial) : EuclideanSpatial :=
  euclideanWeylReflection (euclideanInversion p)

lemma euclideanWeylAction_measurable : Measurable euclideanWeylAction :=
  euclideanWeylReflection.continuous.measurable.comp euclideanInversion_measurable

lemma euclideanWeylAction_preserves_hyperbolicVolume :
    Measure.map euclideanWeylAction hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  rw [show euclideanWeylAction=euclideanWeylReflection ∘ euclideanInversion from rfl,
    ←Measure.map_map euclideanWeylReflection.continuous.measurable euclideanInversion_measurable,
    euclideanInversion_preserves_hyperbolicVolume,euclideanWeylReflection_preserves_hyperbolicVolume]

lemma euclideanWeylAction_apply (p : EuclideanSpatial) :
    euclideanWeylAction p 0= -((1/‖p‖)^2*p 0) ∧
      euclideanWeylAction p 1=(1/‖p‖)^2*p 1 ∧
      euclideanWeylAction p 2=(1/‖p‖)^2*p 2 := by
  simpa [euclideanWeylAction,euclideanInversion_apply] using
    euclideanWeylReflection_apply (euclideanInversion p)

lemma complexWeyl_preserves_hyperbolicVolume :
    Measure.map (fun w => complexWeyl • w) hyperbolicVolume=hyperbolicVolume := by
  apply hyperbolicVolume_map_of_coordinate_action complexWeyl euclideanWeylAction
    euclideanWeylAction_measurable euclideanWeylAction_preserves_hyperbolicVolume
  intro p hp
  have hn : ‖p‖≠0 := norm_ne_zero_iff.mpr (euclideanUpperHalf_ne_zero p hp)
  have hnc : (‖p‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn
  obtain ⟨h0,h1,h2⟩ := euclideanWeylAction_apply p
  have hq : 0<euclideanWeylAction p 2 := by
    rw [h2]
    exact mul_pos (sq_pos_of_ne_zero (one_div_ne_zero hn)) hp
  rw [euclideanToHyperbolic_positive _ hq,euclideanToHyperbolic_positive _ hp,complexWeyl_action]
  apply upperPoint_congr
  · rw [h0,h1,euclidean_complex_norm_sq]
    simp only [Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div,
      Complex.ofReal_one,Complex.star_def,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
    field_simp
    ; ring
  · rw [h2,euclidean_complex_norm_sq]
    field_simp

lemma hyperbolicVolume_invariant_mul (g h : SL(2,ℂ))
    (hg : Measure.map (fun w => g • w) hyperbolicVolume=hyperbolicVolume)
    (hh : Measure.map (fun w => h • w) hyperbolicVolume=hyperbolicVolume) :
    Measure.map (fun w => (g*h) • w) hyperbolicVolume=hyperbolicVolume := by
  rw [show (fun w : HyperbolicSpace => (g*h) • w)=(fun w => g • w) ∘ (fun w => h • w) by
    funext w; exact mul_smul g h w,
    ←Measure.map_map (continuous_hyperbolic_action g).measurable (continuous_hyperbolic_action h).measurable,
    hh,hg]

theorem hyperbolicVolume_invariant (g : SL(2,ℂ)) :
    Measure.map (fun w => g • w) hyperbolicVolume=hyperbolicVolume := by
  by_cases hc : g 1 0=0
  · obtain ⟨ha,hg⟩ := complex_bruhat_zero g hc
    rw [hg]
    exact hyperbolicVolume_invariant_mul _ _ (complexDiagonal_preserves_hyperbolicVolume _ ha)
      (complexTranslation_preserves_hyperbolicVolume _)
  · rw [complex_bruhat_nonzero g hc]
    exact hyperbolicVolume_invariant_mul _ _
      (hyperbolicVolume_invariant_mul _ _
        (hyperbolicVolume_invariant_mul _ _ (complexTranslation_preserves_hyperbolicVolume _)
          (complexDiagonal_preserves_hyperbolicVolume _ (inv_ne_zero hc)))
        complexWeyl_preserves_hyperbolicVolume)
      (complexTranslation_preserves_hyperbolicVolume _)

end CubicEisenstein

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

end SecondPassArithmetic

end

end OAI
