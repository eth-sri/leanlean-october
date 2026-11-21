module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LocalPGLCoverModules
public import DedekindZetaZeroFree.Algebra.GLTwoDiagonalAndInverseEntries
public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicRationalSplitting

@[expose] public section

noncomputable section
open scoped NumberField Classical Matrix NNReal
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalTorusFunctionData

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev G := KPAdelicCoverRestrictedProduct.CubicPGL2Adelic F ζ hζ
abbrev Ideles := KPAdelicCoverRestrictedProduct.Ideles F
abbrev Adeles := KPAdelicCoverRestrictedProduct.Adeles F
abbrev AdelicMatrixGroup := KPAdelicCoverRestrictedProduct.AdelicGL2 F

def ordinaryTorus : Subgroup (KPAdelicCoverRestrictedProduct.AdelicPGL2 F) where
  carrier := {g | ∃ A : AdelicMatrixGroup F,
    QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A = g ∧
      A 1 0 = 0 ∧ A 0 1 = 0}
  one_mem' := by
    refine ⟨1, by simp, ?_, ?_⟩ <;> simp
  mul_mem' := by
    rintro g k ⟨A, rfl, h10, h01⟩ ⟨B, rfl, k10, k01⟩
    refine ⟨A * B, map_mul _ _ _, ?_, ?_⟩
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h10, k10]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h01, k01]
  inv_mem' := by
    rintro g ⟨A, rfl, h10, h01⟩
    exact ⟨A⁻¹, map_inv _ _,
      KPGlobalTorusMatrixCertificates.inv10 A h10,
      KPGlobalTorusMatrixCertificates.inv01 A h10 h01⟩

def ordinaryBorel : Subgroup (KPAdelicCoverRestrictedProduct.AdelicPGL2 F) where
  carrier := {g | ∃ A : AdelicMatrixGroup F,
    QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A = g ∧ A 1 0 = 0}
  one_mem' := by
    refine ⟨1, by simp, ?_⟩; simp
  mul_mem' := by
    rintro g k ⟨A, rfl, h10⟩ ⟨B, rfl, k10⟩
    refine ⟨A * B, map_mul _ _ _, ?_⟩
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, k10]
  inv_mem' := by
    rintro g ⟨A, rfl, h10⟩
    exact ⟨A⁻¹, map_inv _ _, KPGlobalTorusMatrixCertificates.inv10 A h10⟩

def torus : Subgroup (G F ζ hζ) :=
  (ordinaryTorus F).comap (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ)
abbrev E := torus F ζ hζ

def borel : Subgroup (G F ζ hζ) :=
  (ordinaryBorel F).comap (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ)

theorem diagonal_entries_units (A : AdelicMatrixGroup F) (h10 : A 1 0 = 0) (h01 : A 0 1 = 0) :
    IsUnit (A 0 0) ∧ IsUnit (A 1 1) :=
  KPGlobalTorusMatrixCertificates.diagonal_units A h10

 def rawRatio (A : AdelicMatrixGroup F) (h : A 1 0 = 0) : Ideles F :=
  (KPGlobalTorusMatrixCertificates.diagonal_units A h).1.unit *
  ((KPGlobalTorusMatrixCertificates.diagonal_units A h).2.unit)⁻¹
 lemma rawRatio_mul (A B : AdelicMatrixGroup F) (h : A 1 0 = 0)
    (k : B 1 0 = 0) (ha : A 0 1 = 0)
    (hk : (A * B) 1 0 = 0) :
    rawRatio F (A * B) hk = rawRatio F A h * rawRatio F B k := by
  have h0 : (KPGlobalTorusMatrixCertificates.diagonal_units (A * B) hk).1.unit =
      (KPGlobalTorusMatrixCertificates.diagonal_units A h).1.unit *
      (KPGlobalTorusMatrixCertificates.diagonal_units B k).1.unit := by
    apply Units.ext
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha]
  have h1 : (KPGlobalTorusMatrixCertificates.diagonal_units (A * B) hk).2.unit =
      (KPGlobalTorusMatrixCertificates.diagonal_units A h).2.unit *
      (KPGlobalTorusMatrixCertificates.diagonal_units B k).2.unit := by
    apply Units.ext
    simp [Matrix.mul_apply, Fin.sum_univ_two, h]
  unfold rawRatio
  rw [h0, h1]
  simp only [mul_inv_rev]
  ac_rfl
 lemma rawRatio_same (A B : AdelicMatrixGroup F) (h : A 1 0 = 0)
    (k : B 1 0 = 0) (ha : A 0 1 = 0)
    (he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B) :
    rawRatio F A h = rawRatio F B k := by
  obtain ⟨s, hs, rfl⟩ := (QuotientGroup.mk'_eq_mk' _).mp he
  obtain ⟨u, rfl⟩ := hs
  have h0 : (KPGlobalTorusMatrixCertificates.diagonal_units
      (A * Matrix.GeneralLinearGroup.scalar (Fin 2) u) k).1.unit =
      (KPGlobalTorusMatrixCertificates.diagonal_units A h).1.unit * u := by
    apply Units.ext
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar, Matrix.diagonal]
  have h1 : (KPGlobalTorusMatrixCertificates.diagonal_units
      (A * Matrix.GeneralLinearGroup.scalar (Fin 2) u) k).2.unit =
      (KPGlobalTorusMatrixCertificates.diagonal_units A h).2.unit * u := by
    apply Units.ext
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar, Matrix.diagonal]
  unfold rawRatio
  rw [h0, h1]
  simp [mul_inv_rev, mul_assoc]

def torusRatio : ordinaryTorus F →* Ideles F where
  toFun t :=
    let A := Classical.choose t.property
    let h := Classical.choose_spec t.property
    (diagonal_entries_units F A h.2.1 h.2.2).1.unit *
      ((diagonal_entries_units F A h.2.1 h.2.2).2.unit)⁻¹
  map_one' := by
    let A := Classical.choose (1 : ordinaryTorus F).property
    have h := Classical.choose_spec (1 : ordinaryTorus F).property
    change rawRatio F A h.2.1 = 1
    have he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
        QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) 1 := by
      exact h.1.trans (map_one _).symm
    rw [rawRatio_same F A 1 h.2.1 (by simp) h.2.2 he]
    apply Units.ext
    simp [rawRatio]
  map_mul' := by
    intro t u
    let A := Classical.choose t.property
    let B := Classical.choose u.property
    let C := Classical.choose (t * u).property
    have hA := Classical.choose_spec t.property
    have hB := Classical.choose_spec u.property
    have hC := Classical.choose_spec (t * u).property
    change rawRatio F C hC.2.1 = rawRatio F A hA.2.1 * rawRatio F B hB.2.1
    have h10 : (A * B) 1 0 = 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [show A 1 0 = 0 from hA.2.1, show B 1 0 = 0 from hB.2.1]
      simp
    have he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) C =
        QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) (A * B) := by
      rw [map_mul, hA.1, hB.1]; exact hC.1
    rw [rawRatio_same F C (A * B) hC.2.1 h10 hC.2.2 he]
    exact rawRatio_mul F A B hA.2.1 hB.2.1 hA.2.2 h10

def p : E F ζ hζ →* Ideles F :=
  (torusRatio F).comp
    ((KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).restrict
      (fun t ht => ht))

theorem ratio_formula (t : ordinaryTorus F) (A : AdelicMatrixGroup F)
    (hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A = t.val)
    (h10 : A 1 0 = 0) (h01 : A 0 1 = 0) :
    (torusRatio F t : Adeles F) =
      ((diagonal_entries_units F A h10 h01).1.unit : Adeles F) *
      ↑((diagonal_entries_units F A h10 h01).2.unit)⁻¹ := by
  let B := Classical.choose t.property
  have hB := Classical.choose_spec t.property
  change (rawRatio F B hB.2.1 : Adeles F) = (rawRatio F A h10 : Adeles F)
  exact congrArg Units.val (rawRatio_same F B A hB.2.1 h10 hB.2.2
    (hB.1.trans hA.symm))

private lemma preimage_diag (A : AdelicMatrixGroup F)
    (hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A ∈
      ordinaryTorus F) : A 1 0 = 0 ∧ A 0 1 = 0 := by
  obtain ⟨B, hB, h10, h01⟩ := hA
  rw [QuotientGroup.mk'_eq_mk'] at hB
  obtain ⟨z, hz, he⟩ := hB
  obtain ⟨u, rfl⟩ := hz
  rw [← he]
  simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.mul_apply, Matrix.scalar, Fin.sum_univ_two, h01, h10]

private theorem continuous_diag_unit {X : Type*} [TopologicalSpace X]
    {A : X → AdelicMatrixGroup F} (hA : Continuous A) (i : Fin 2)
    (u : X → Ideles F) (hu : ∀ x, (u x).val = A x i i)
    (hi : ∀ x, (u x)⁻¹.val = (A x)⁻¹ i i) : Continuous u := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous (fun x => (u x).val)
    simp only [hu]
    exact (continuous_apply i).comp (Matrix.GeneralLinearGroup.continuous_apply A hA i)
  · change Continuous (fun x => (u x)⁻¹.val)
    simp only [hi]
    exact (continuous_apply i).comp (Matrix.GeneralLinearGroup.continuous_apply _ hA.inv i)

private theorem inverse_unit_entry (A : AdelicMatrixGroup F) (i : Fin 2)
    (h10 : A 1 0 = 0) (h01 : A 0 1 = 0) (u : Ideles F) (hu : u.val = A i i) :
    u⁻¹.val = A⁻¹ i i := by
  have h : A⁻¹ i i * A i i = 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) (Adeles F) => M i i) A.inv_mul
    fin_cases i <;> simpa [Matrix.mul_apply, Fin.sum_univ_two, h10, h01] using h
  rw [← hu] at h
  simpa only [mul_assoc, Units.mul_inv, mul_one, one_mul] using
    (congrArg (fun y : Adeles F => y * u⁻¹.val) h).symm

 theorem ratio_continuous : Continuous (torusRatio F) := by
  let q := QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
  let S : Set (KPAdelicCoverRestrictedProduct.AdelicPGL2 F) := ordinaryTorus F
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  apply (hq.restrictPreimage S).isQuotientMap.continuous_iff.mpr
  let u (A : q ⁻¹' S) := (diagonal_entries_units F A.val
    (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2).1.unit
  let w (A : q ⁻¹' S) := (diagonal_entries_units F A.val
    (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2).2.unit
  have hc (i : Fin 2) (v : (q ⁻¹' S) → Ideles F) (hv : ∀ A, (v A).val = A.val i i) :
      Continuous v :=
    continuous_diag_unit F continuous_subtype_val i v hv fun A =>
      inverse_unit_entry F A.val i (preimage_diag F A.val A.property).1
        (preimage_diag F A.val A.property).2 (v A) (hv A)
  have h : torusRatio F ∘ S.restrictPreimage q = fun A => u A * (w A)⁻¹ := by
    funext A
    exact Units.ext (ratio_formula F _ A.val rfl
      (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2)
  rw [h]
  exact (hc 0 u fun _ => IsUnit.unit_spec _).mul (hc 1 w fun _ => IsUnit.unit_spec _).inv

 theorem p_continuous : Continuous (p F ζ hζ) :=
  (ratio_continuous F).comp
    (((KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous.comp
      continuous_subtype_val).subtype_mk fun t => t.property)

 theorem ordinary_torus_closed :
    IsClosed (ordinaryTorus F : Set (KPAdelicCoverRestrictedProduct.AdelicPGL2 F)) := by
  let q := QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
  apply (QuotientGroup.isQuotientMap_mk (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).isClosed_preimage.mp
  change IsClosed (q ⁻¹' (ordinaryTorus F : Set _))
  rw [show q ⁻¹' (ordinaryTorus F : Set _) = {A | A 1 0 = 0 ∧ A 0 1 = 0} from
    Set.ext fun A => ⟨preimage_diag F A, fun h => ⟨A, rfl, h⟩⟩]
  have hc (i j : Fin 2) : Continuous (fun A : AdelicMatrixGroup F => A i j) :=
    (continuous_apply j).comp (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id i)
  exact (isClosed_eq (hc 1 0) continuous_const).inter (isClosed_eq (hc 0 1) continuous_const)

 theorem torus_closed : IsClosed (torus F ζ hζ : Set (G F ζ hζ)) :=
  (ordinary_torus_closed F).preimage
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous

def rationalDiagonal : Fˣ →* KubotaRankTwo.GL2 F where
  toFun y := KubotaRankTwo.d F y 1
  map_one' := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' := by
    intro x y
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

def rationalDiagonalLift : Fˣ →* G F ζ hζ :=
  (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
    ((KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ).comp (rationalDiagonal F))

theorem rationalDiagonalLift_mem (y : Fˣ) :
    rationalDiagonalLift F ζ hζ y ∈ torus F ζ hζ := by
  change KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
      (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ (rationalDiagonal F y))) ∈
    ordinaryTorus F
  refine ⟨KPAdelicCoverRestrictedProduct.rationalBase F (rationalDiagonal F y), ?_, ?_, ?_⟩
  · change _ = QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
      (KPAdelicCoverRestrictedProduct.projection F ζ hζ
        (KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ (rationalDiagonal F y)))
    rw [KPAdelicCoverRestrictedProduct.projection_rationalSection]
  · simp [KPAdelicCoverRestrictedProduct.rationalBase, rationalDiagonal]
  · simp [KPAdelicCoverRestrictedProduct.rationalBase, rationalDiagonal]

def s : Fˣ →* E F ζ hζ :=
  (rationalDiagonalLift F ζ hζ).codRestrict (torus F ζ hζ)
    (rationalDiagonalLift_mem F ζ hζ)

theorem p_rational (a : Fˣ) :
    p F ζ hζ (s F ζ hζ a) =
      IdeleGroup.unitEmbedding (𝓞 F) F a := by
  let A := KPAdelicCoverRestrictedProduct.rationalBase F (KubotaRankTwo.d F a 1)
  have hp : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
      (s F ζ hζ a).val =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A := by
    change QuotientGroup.mk' _ (KPAdelicCoverRestrictedProduct.projection F ζ hζ
      (KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ _)) = _
    rw [KPAdelicCoverRestrictedProduct.projection_rationalSection]
    rfl
  have h10 : A 1 0 = 0 := by simp [A, KPAdelicCoverRestrictedProduct.rationalBase]
  have h01 : A 0 1 = 0 := by simp [A, KPAdelicCoverRestrictedProduct.rationalBase]
  have h := ratio_formula F
    ⟨_, (s F ζ hζ a).property⟩ A hp.symm h10 h01
  apply Units.ext
  change (torusRatio F
    ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (s F ζ hζ a).val,
      (s F ζ hζ a).property⟩ : Adeles F) = _
  rw [h]
  have he1 : (diagonal_entries_units F A h10 h01).1.unit =
      IdeleGroup.unitEmbedding (𝓞 F) F a := by
    apply Units.ext
    rw [IsUnit.unit_spec]
    simp [A, KPAdelicCoverRestrictedProduct.rationalBase, NumberField.IdeleGroup.unitEmbedding]
  have he2 : (diagonal_entries_units F A h10 h01).2.unit = 1 := by
    apply Units.ext
    rw [IsUnit.unit_spec]
    simp [A, KPAdelicCoverRestrictedProduct.rationalBase]
  simp [he1, he2]

abbrev Z := Subgroup.center (E F ζ hζ)

def iota : rootsOfUnity 3 F →* ℂˣ :=
  (KPLocalCover.coefficientEmbedding F ζ hζ).comp (KPLocalCover.threeToSix F)

def rootTuple (x : Adeles F) : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ :=
  ⟨fun v => KPStandardLocalRootLifts.N F ζ hζ v
    (KPAdelicCoverRestrictedProduct.adeleEval F v x),
    KPRationalAdelicSplitting.NCoordinates_restricted F ζ hζ x⟩

def N (x : Adeles F) : G F ζ hζ :=
  KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (rootTuple F ζ hζ x))

theorem N_add (x y : Adeles F) : N F ζ hζ (x + y) = N F ζ hζ x * N F ζ hζ y := by
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPRationalAdelicSplitting.N F ζ hζ (x + y)) = _
  rw [KPRationalAdelicSplitting.N_add, map_mul]
  rfl

def Nhom : Multiplicative (Adeles F) →* G F ζ hζ where
  toFun x := N F ζ hζ x.toAdd
  map_one' := by
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ (KPRationalAdelicSplitting.N F ζ hζ 0) = 1
    rw [KPRationalAdelicSplitting.N_zero, map_one]
  map_mul' x y := N_add F ζ hζ _ _

theorem continuous_N : Continuous (N F ζ hζ) := by
  let : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  change Continuous (Nhom F ζ hζ)
  apply continuous_of_continuousAt_one
  exact QuotientGroup.continuous_mk.continuousAt.comp
    (QuotientGroup.continuous_mk.continuousAt.comp
      (KPRationalAdelicSplitting.continuousAt_NTuple_zero F ζ hζ))

def ideleAbs : Ideles F →* (ℝ≥0)ˣ :=
  (invMonoidHom : (ℝ≥0)ˣ →* (ℝ≥0)ˣ).comp
    ((IdeleGroup.absoluteNorm (K := F)).comp
      (IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm.toMonoidHom)

def delta : E F ζ hζ →* (ℝ≥0)ˣ := (ideleAbs F).comp (p F ζ hζ)

def deltaHalf (t : E F ζ hζ) : ℂ :=
  (Real.sqrt (((delta F ζ hζ t : ℝ≥0) : ℝ)) : ℂ)

section Functions
variable {T : Type*} [Group T] (H : Subgroup T) (χ : H →* ℂˣ)

def ScalarFunctions : Submodule ℂ (T → ℂ) where
  carrier := {f | ∀ (h : H) (g : T), f ((h : T) * g) = (χ h : ℂ) * f g}
  zero_mem' := by simp
  add_mem' := by intro f k hf hk h g; simp [hf h g, hk h g, mul_add]
  smul_mem' := by intro c f hf h g; simp only [Pi.smul_apply, smul_eq_mul, hf h g]; ring

def evaluation (g : T) : ScalarFunctions H χ →ₗ[ℂ] ℂ where
  toFun f := f.val g
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def rightTranslation : Representation ℂ T (ScalarFunctions H χ) where
  toFun a :=
    { toFun := fun f => ⟨fun g => f.val (g * a), by
        intro h g; simpa only [mul_assoc] using f.property h (g * a)⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f g; simp
  map_mul' := by intros; ext f g; simp [mul_assoc]

@[simp] theorem evaluation_covariance (f : ScalarFunctions H χ) (h : H) (g : T) :
    evaluation H χ ((h : T) * g) f = (χ h : ℂ) * evaluation H χ g f := f.property h g

@[simp] theorem evaluation_rightTranslation (a g : T) (f : ScalarFunctions H χ) :
    evaluation H χ g (rightTranslation H χ a f) = evaluation H χ (g * a) f := rfl

def RightLevel (J : Subgroup T) : Submodule ℂ (ScalarFunctions H χ) :=
  fixedSubmodule (rightTranslation H χ) J

theorem rightLevel_covariance (J : Subgroup T) (f : RightLevel H χ J)
    (g j : T) (hj : j ∈ J) : f.val.val (g * j) = f.val.val g := by
  have h := f.property ⟨j, hj⟩
  exact congrArg (fun u : ScalarFunctions H χ => u.val g) h
end Functions

structure Polarization where
  H : Subgroup (E F ζ hζ)
  closed : IsClosed (H : Set (E F ζ hζ))
  abelian : ∀ h k : H, h * k = k * h
  contains_center : Z F ζ hζ ≤ H
  character : ContinuousMonoidHom H ℂˣ

abbrev TorusFunctions (P : Polarization F ζ hζ) :=
  ScalarFunctions P.H P.character.toMonoidHom

def BorelFunctions (P : Polarization F ζ hζ) : Submodule ℂ (G F ζ hζ → ℂ) where
  carrier := {f | ∀ (h : P.H) (x : Adeles F) (g : G F ζ hζ),
    f (((h.val.val : G F ζ hζ) * N F ζ hζ x) * g) =
      deltaHalf F ζ hζ h.val * (P.character h : ℂ) * f g}
  zero_mem' := by simp
  add_mem' := by intro f k hf hk h x g; simp [hf h x g, hk h x g, mul_add]
  smul_mem' := by
    intro c f hf h x g
    simp only [Pi.smul_apply, smul_eq_mul, hf h x g]; ring

def borelRightTranslation (P : Polarization F ζ hζ) :
    Representation ℂ (G F ζ hζ) (BorelFunctions F ζ hζ P) where
  toFun a :=
    { toFun := fun f => ⟨fun g => f.val (g * a), by
        intro h x g; simpa only [mul_assoc] using f.property h x (g * a)⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f g; simp
  map_mul' := by intros; ext f g; simp [mul_assoc]

def finitePart : Subgroup (G F ζ hζ) :=
  (⨅ w : InfinitePlace F,
    (RestrictedProduct.evalMonoidHom
      (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v) (Sum.inl w)).ker).map
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))

abbrev FiniteLevel := CompactOpenLevel (finitePart F ζ hζ)

def globalLevel (J : FiniteLevel F ζ hζ) : Subgroup (G F ζ hζ) :=
  (J.toOpenSubgroup : Subgroup (finitePart F ζ hζ)).map (finitePart F ζ hζ).subtype

abbrev TorusArch := InfinitePlace F → ℂ

def archDiagonalTuple (z : TorusArch F) :
    KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ := by
  refine ⟨fun v => ?_, ?_⟩
  · cases v with
    | inl w =>
      let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)
      exact KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w)
        (if h : z w = 0 then 1 else Units.mk0 (e.symm (z w))
          (by exact fun h0 => h (by simpa using congrArg e h0)))
    | inr q => exact 1
  · apply Filter.Eventually.of_forall
    intro v
    cases v with
    | inl w => exact Subgroup.mem_top _
    | inr q => exact Subgroup.one_mem _

def archDiagonalLift (z : TorusArch F) : G F ζ hζ :=
  KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (archDiagonalTuple F ζ hζ z))

theorem archDiagonalLift_mem (z : TorusArch F) :
    archDiagonalLift F ζ hζ z ∈ torus F ζ hζ := by
  refine ⟨KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
    (archDiagonalTuple F ζ hζ z), rfl, ?_, ?_⟩
  · change KPAdelicCoverRestrictedProduct.matrixEntry F ζ hζ
      (archDiagonalTuple F ζ hζ z) 1 0 = 0
    apply Prod.ext
    · funext w
      simp [KPAdelicCoverRestrictedProduct.matrixEntry, archDiagonalTuple,
        KPStandardLocalRootLifts.A, KPLocalCover.sectionMap]
      rfl
    · apply RestrictedProduct.ext
      intro q
      change (1 : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)).g 1 0 = 0
      simp
  · change KPAdelicCoverRestrictedProduct.matrixEntry F ζ hζ
      (archDiagonalTuple F ζ hζ z) 0 1 = 0
    apply Prod.ext
    · funext w
      simp [KPAdelicCoverRestrictedProduct.matrixEntry, archDiagonalTuple,
        KPStandardLocalRootLifts.A, KPLocalCover.sectionMap]
      rfl
    · apply RestrictedProduct.ext
      intro q
      change (1 : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)).g 0 1 = 0
      simp

def torusArchChart (z : TorusArch F) : E F ζ hζ :=
  ⟨archDiagonalLift F ζ hζ z, archDiagonalLift_mem F ζ hζ z⟩

def torusArchDomain : Set (TorusArch F) := {z | ∀ w, z w ≠ 0}

section SmoothCharts
variable {T V : Type*} [Group T] [NormedAddCommGroup V] [NormedSpace ℝ V]
  (H : Subgroup T) (χ : H →* ℂˣ) (chart : V → T) (U : Set V)

def ArchSmooth : Submodule ℂ (ScalarFunctions H χ) where
  carrier := {f | ∀ g, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => f.val (chart z * g)) U}
  zero_mem' := by intro g; exact contDiffOn_const
  add_mem' := by intro f k hf hk g; exact (hf g).add (hk g)
  smul_mem' := by intro c f hf g; exact contDiffOn_const.smul (hf g)

def SmoothLevel (J : Subgroup T) : Submodule ℂ (ScalarFunctions H χ) :=
  ArchSmooth H χ chart U ⊓ RightLevel H χ J

def SmoothUnion {ι : Type*} (levels : ι → Subgroup T) :
    Submodule ℂ (ScalarFunctions H χ) := ⨆ i, SmoothLevel H χ chart U (levels i)

end SmoothCharts

abbrev TorusSmoothLevel (P : Polarization F ζ hζ) (J : FiniteLevel F ζ hζ) :=
  SmoothLevel P.H P.character.toMonoidHom (torusArchChart F ζ hζ)
    (torusArchDomain F) ((globalLevel F ζ hζ J).comap (torus F ζ hζ).subtype)

abbrev TorusSmoothUnion (P : Polarization F ζ hζ) :=
  SmoothUnion P.H P.character.toMonoidHom (torusArchChart F ζ hζ)
    (torusArchDomain F)
    (fun J : FiniteLevel F ζ hζ =>
      (globalLevel F ζ hζ J).comap (torus F ζ hζ).subtype)

section StageTopology
variable {T V : Type*} [Group T] [NormedAddCommGroup V] [NormedSpace ℝ V]
  (H : Subgroup T) (χ : H →* ℂˣ) (chart : V → T) (U : Set V)
  (hU : IsOpen U) (J : Subgroup T)

structure JetCompact where
  set : Set V
  compact : IsCompact set
  inside : set ⊆ U

def jetBound (g : T) (n : ℕ) (K : JetCompact U)
    (f : SmoothLevel H χ chart U J) : ℝ :=
  sSup ((fun z => ‖iteratedFDerivWithin ℝ n
    (fun y => f.val.val (chart y * g)) U z‖) '' K.set)

private lemma jet_bdd (hU : IsOpen U) (g : T) (n : ℕ) (K : JetCompact U)
    (f : SmoothLevel H χ chart U J) :
    BddAbove ((fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => f.val.val (chart y * g)) U z‖) '' K.set) := by
  apply IsCompact.bddAbove
  apply K.compact.image_of_continuousOn
  exact ((f.property.1 g).continuousOn_iteratedFDerivWithin (by simp)
    hU.uniqueDiffOn).norm.mono K.inside

theorem jetBound_add_le (_hU : IsOpen U) (g : T) (n : ℕ) (K : JetCompact U)
    (f k : SmoothLevel H χ chart U J) :
    jetBound H χ chart U J g n K (f + k) ≤
      jetBound H χ chart U J g n K f + jetBound H χ chart U J g n K k := by
  let hU := _hU
  by_cases he : K.set.Nonempty
  · apply csSup_le (he.image _)
    rintro r ⟨z, hz, rfl⟩
    change ‖iteratedFDerivWithin ℝ n
      ((fun y => f.val.val (chart y * g)) + (fun y => k.val.val (chart y * g))) U z‖ ≤ _
    rw [iteratedFDerivWithin_add_apply
      ((f.property.1 g).of_le (by simp) z (K.inside hz))
      ((k.property.1 g).of_le (by simp) z (K.inside hz)) hU.uniqueDiffOn (K.inside hz)]
    exact (norm_add_le _ _).trans (add_le_add
      (le_csSup (jet_bdd H χ chart U J hU g n K f) ⟨z, hz, rfl⟩)
      (le_csSup (jet_bdd H χ chart U J hU g n K k) ⟨z, hz, rfl⟩))
  · have he' : K.set = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    simp [jetBound, he', Real.sSup_empty]

theorem jetBound_smul (_hU : IsOpen U) (g : T) (n : ℕ) (K : JetCompact U)
    (c : ℂ) (f : SmoothLevel H χ chart U J) :
    jetBound H χ chart U J g n K (c • f) =
      ‖c‖ * jetBound H χ chart U J g n K f := by
  let hU := _hU
  by_cases he : K.set.Nonempty
  · have hp : ∀ z ∈ K.set, ‖iteratedFDerivWithin ℝ n
        (fun y => (c • f).val.val (chart y * g)) U z‖ =
      ‖c‖ * ‖iteratedFDerivWithin ℝ n (fun y => f.val.val (chart y * g)) U z‖ := by
      intro z hz
      change ‖iteratedFDerivWithin ℝ n (c • (fun y => f.val.val (chart y * g))) U z‖ = _
      rw [iteratedFDerivWithin_const_smul_apply
        ((f.property.1 g).of_le (by simp) z (K.inside hz)) hU.uniqueDiffOn (K.inside hz)]
      exact norm_smul c _
    unfold jetBound
    rw [Set.image_congr hp, ← Set.image_image]
    exact ((isLUB_csSup (he.image _) (jet_bdd H χ chart U J hU g n K f)).mul_left
      (norm_nonneg c)).csSup_eq ((he.image _).image _)
  · have he' : K.set = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    simp [jetBound, he', Real.sSup_empty]

def jetSeminorm (g : T) (n : ℕ) (K : JetCompact U) :
    Seminorm ℂ (SmoothLevel H χ chart U J) :=
  Seminorm.of (jetBound H χ chart U J g n K)
    (jetBound_add_le H χ chart U J hU g n K)
    (jetBound_smul H χ chart U J hU g n K)

def smoothLevelTopology : TopologicalSpace (SmoothLevel H χ chart U J) :=
  (SeminormFamily.moduleFilterBasis (fun i : T × ℕ × JetCompact U =>
    jetSeminorm H χ chart U hU J i.1 i.2.1 i.2.2)).topology

variable {ι : Type*} (levels : ι → Subgroup T)

def stageInclusion (i : ι) : SmoothLevel H χ chart U (levels i) →ₗ[ℂ]
    SmoothUnion H χ chart U levels :=
  Submodule.inclusion (le_iSup (fun i => SmoothLevel H χ chart U (levels i)) i)

def finalSeminorms :=
  {q : Seminorm ℂ (SmoothUnion H χ chart U levels) // ∀ i,
    @Continuous (SmoothLevel H χ chart U (levels i)) ℝ
      (smoothLevelTopology H χ chart U hU (levels i)) inferInstance
      (q ∘ stageInclusion H χ chart U levels i)}

def finalLocallyConvexTopology : TopologicalSpace (SmoothUnion H χ chart U levels) :=
  (SeminormFamily.moduleFilterBasis
    (fun q : finalSeminorms H χ chart U hU levels => q.val)).topology

theorem finalLocallyConvexTopology_locallyConvex :
    letI := finalLocallyConvexTopology H χ chart U hU levels
    LocallyConvexSpace ℝ (SmoothUnion H χ chart U levels) := by
  letI := finalLocallyConvexTopology H χ chart U hU levels
  exact (show WithSeminorms
    (fun q : finalSeminorms H χ chart U hU levels => q.val) from ⟨rfl⟩).toLocallyConvexSpace

theorem stageInclusion_continuous (i : ι) :
    @Continuous (SmoothLevel H χ chart U (levels i)) (SmoothUnion H χ chart U levels)
      (smoothLevelTopology H χ chart U hU (levels i))
      (finalLocallyConvexTopology H χ chart U hU levels)
      (stageInclusion H χ chart U levels i) := by
  letI := smoothLevelTopology H χ chart U hU (levels i)
  letI := finalLocallyConvexTopology H χ chart U hU levels
  have hp : WithSeminorms (fun j : T × ℕ × JetCompact U =>
    jetSeminorm H χ chart U hU (levels i) j.1 j.2.1 j.2.2) := ⟨rfl⟩
  letI := hp.isTopologicalAddGroup
  have hq : WithSeminorms
    (fun q : finalSeminorms H χ chart U hU levels => q.val) := ⟨rfl⟩
  apply Seminorm.continuous_of_continuous_comp
    (E := SmoothLevel H χ chart U (levels i))
    (𝕝 := ℂ) (𝕝₂ := ℂ) (τ₁₂ := RingHom.id ℂ) hq
    (stageInclusion H χ chart U levels i)
  intro q
  exact q.property i
end StageTopology

theorem torusArchDomain_open : IsOpen (torusArchDomain F) := by
  simpa only [torusArchDomain, Set.setOf_forall] using
    isOpen_iInter_of_finite (fun w => isOpen_ne_fun (continuous_apply w) continuous_const)

def torusSmoothTopology (P : Polarization F ζ hζ) :
    TopologicalSpace (TorusSmoothUnion F ζ hζ P) :=
  finalLocallyConvexTopology P.H P.character.toMonoidHom
    (torusArchChart F ζ hζ) (torusArchDomain F) (torusArchDomain_open F)
    (fun J : FiniteLevel F ζ hζ =>
      (globalLevel F ζ hζ J).comap (torus F ζ hζ).subtype)

end DedekindZetaZeroFree.KPGlobalTorusFunctionData

end
