module

public import GS.UnitarySharing.Algebra
public import GS.UnitaryManifold.KernelCayley
public import GS.OverlapGeometry.FactorChartOpen
public import GS.OverlapGeometry.HorizontalModel
public import GS.OverlapGeometry.ManifoldSmoothMaps
public import GS.Extensions.OrbitSlices
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold Set Filter
open GS.OverlapGeometry (SmoothSlice sliceChartedSpace slice_isManifold
  slice_val_contMDiff slice_val_mfderiv_eq slice_val_mfderiv_injective
  isOpen_slice_image_of_productChart horizontalComplement complementKernelEquiv
  horizontalLeftInverse horizontalRestriction horizontalLeftInverse_comp)
open scoped Topology Manifold

namespace GS.UnitarySharing
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ} {s right left : Pattern 𝕂 n}

def modelProjection (s : Pattern 𝕂 n) : SMat 𝕂 n →L[ℝ] Generator s :=
  ({ toFun := fun A => ⟨cFrobProjection (sharedSkewSpace 𝕂 s.size s.label) A, cFrobProjection_mem _ _⟩
     map_add' := fun A B => Subtype.ext (map_add _ A B)
     map_smul' := fun a A => Subtype.ext (map_smul _ a A) } : SMat 𝕂 n →ₗ[ℝ] Generator s).toContinuousLinearMap

theorem modelProjection_val_of_mem (s : Pattern 𝕂 n) (A : SMat 𝕂 n)
    (hA : A ∈ sharedSkewSpace 𝕂 s.size s.label) : (modelProjection s A).val = A :=
  cFrobProjection_of_mem _ _ hA

@[simp] theorem modelProjection_inclusion (C : Generator s) : modelProjection s C.val = C :=
  Subtype.ext (modelProjection_val_of_mem s C.val C.property)

def factorSource (Q : Factor s) : Set (Factor s) :=
  {U | admissible ((Factor.matrix Q)ᴴ * Factor.matrix U)}

def factorCoordinates (Q : Factor s) (A : SMat 𝕂 n) : Generator s :=
  modelProjection s (cayley ((Factor.matrix Q)ᴴ * A))

def reconstruct (Q : Factor s) (C : Generator s) : Factor s :=
  Q * Factor.ofMatrix (cayley C.val) (cayley_shared s.positive s.divides C.property)

@[simp] theorem reconstruct_matrix (Q : Factor s) (C : Generator s) :
    Factor.matrix (reconstruct Q C) = Factor.matrix Q * cayley C.val := rfl

theorem factorSource_open (Q : Factor s) : IsOpen (factorSource Q) :=
  admissible_open.preimage (GS.UnitaryManifold.continuous_matrix_product continuous_const Factor.continuous_matrix)

@[simp] theorem base_mem_factorSource (Q : Factor s) : Q ∈ factorSource Q := by
  change admissible ((Factor.matrix Q)ᴴ * Factor.matrix Q)
  rw [(Factor.matrix_unitary Q).1]; exact admissible_one

theorem centered_reconstruct (Q : Factor s) (C : Generator s) :
    (Factor.matrix Q)ᴴ * Factor.matrix (reconstruct Q C) = cayley C.val := by
  rw [reconstruct_matrix, ← Matrix.mul_assoc, (Factor.matrix_unitary Q).1, Matrix.one_mul]

theorem reconstruct_mem_source (Q : Factor s) (C : Generator s) : reconstruct Q C ∈ factorSource Q := by
  change admissible ((Factor.matrix Q)ᴴ * Factor.matrix (reconstruct Q C))
  rw [centered_reconstruct]; exact admissible_cayley C.val (admissible_of_isSkew C.val C.property.2.1)

theorem factorCoordinates_val (Q U : Factor s) (hU : U ∈ factorSource Q) :
    (factorCoordinates Q (Factor.matrix U)).val = cayley ((Factor.matrix Q)ᴴ * Factor.matrix U) :=
  modelProjection_val_of_mem s _ <| cayley_sharedSkew s.positive s.divides
    (shared_factor_mul s.positive s.divides (shared_factor_conjTranspose (Factor.matrix_shared Q))
      (Factor.matrix_shared U)) hU

@[simp] theorem factorCoordinates_reconstruct (Q : Factor s) (C : Generator s) :
    factorCoordinates Q (Factor.matrix (reconstruct Q C)) = C := by
  unfold factorCoordinates
  rw [centered_reconstruct, cayley_involutive C.val (admissible_of_isSkew C.val C.property.2.1)]
  exact modelProjection_inclusion C

theorem reconstruct_factorCoordinates (Q U : Factor s) (hU : U ∈ factorSource Q) :
    reconstruct Q (factorCoordinates Q (Factor.matrix U)) = U := by
  apply Factor.matrix_injective
  rw [reconstruct_matrix, factorCoordinates_val Q U hU, cayley_involutive _ hU,
    ← Matrix.mul_assoc, (Factor.matrix_unitary Q).2, Matrix.one_mul]

@[simp] theorem reconstruct_zero (Q : Factor s) : reconstruct Q 0 = Q := by
  apply Factor.matrix_injective; simp [reconstruct_matrix, cayley_zero]

theorem factorCoordinates_smooth_at (Q : Factor s) (A : SMat 𝕂 n)
    (hA : admissible ((Factor.matrix Q)ᴴ * A)) : ContDiffAt ℝ ⊤ (factorCoordinates Q) A :=
  (modelProjection s).contDiff.contDiffAt.comp A
    (smooth_cayley_comp_at (smooth_mul_at contDiffAt_const contDiffAt_id) hA)

theorem reconstruct_matrix_smooth (Q : Factor s) :
    ContDiff ℝ ⊤ (fun C : Generator s => Factor.matrix (reconstruct Q C)) :=
  contDiff_iff_contDiffAt.mpr fun C => smooth_mul_at contDiffAt_const
    (smooth_cayley_comp_at (sharedSkewSpace 𝕂 (n := n) s.size s.label).subtypeL.contDiff.contDiffAt
      (admissible_of_isSkew C.val C.property.2.1))

theorem continuous_reconstruct (Q : Factor s) : Continuous (reconstruct Q) :=
  ((reconstruct_matrix_smooth Q).continuous.subtype_mk _).subtype_mk _

def factorPartialChart (Q : Factor s) : OpenPartialHomeomorph (Factor s) (Generator s) where
  toFun U := factorCoordinates Q (Factor.matrix U)
  invFun := reconstruct Q
  source := factorSource Q
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' C _ := reconstruct_mem_source Q C
  left_inv' U hU := reconstruct_factorCoordinates Q U hU
  right_inv' C _ := factorCoordinates_reconstruct Q C
  open_source := factorSource_open Q
  open_target := isOpen_univ
  continuousOn_toFun _ hU := ((factorCoordinates_smooth_at Q _ hU).continuousAt.comp
    Factor.continuous_matrix.continuousAt).continuousWithinAt
  continuousOn_invFun := (continuous_reconstruct Q).continuousOn

def factorLift (g : Factors right left) (v : PairGenerator right left) : Factors right left :=
  (reconstruct g.1 v.1, reconstruct g.2 v.2)

@[simp] theorem factorLift_zero (g : Factors right left) : factorLift g 0 = g :=
  Prod.ext (reconstruct_zero g.1) (reconstruct_zero g.2)

theorem continuous_factorLift (g : Factors right left) : Continuous (factorLift g) :=
  ((continuous_reconstruct g.1).comp continuous_fst).prodMk ((continuous_reconstruct g.2).comp continuous_snd)

def orbitParam (g : Factors right left) (P : SMat 𝕂 n) (v : PairGenerator right left) : SMat 𝕂 n :=
  factorLift g v • P

@[simp] theorem orbitParam_zero (g : Factors right left) (P : SMat 𝕂 n) : orbitParam g P 0 = g • P := by
  simp [orbitParam]

theorem orbitParam_smooth (g : Factors right left) (P : SMat 𝕂 n) : ContDiff ℝ ⊤ (orbitParam g P) :=
  contDiff_iff_contDiffAt.mpr fun v => smooth_mul_at
    (smooth_mul_at ((reconstruct_matrix_smooth g.1).contDiffAt.comp v contDiffAt_fst) contDiffAt_const)
    (smooth_conjTranspose_at ((reconstruct_matrix_smooth g.2).contDiffAt.comp v contDiffAt_snd))

theorem reconstruct_line_hasDerivAt_zero (Q : Factor s) (v : Generator s) :
    HasDerivAt (fun t : ℝ => Factor.matrix (reconstruct Q (t • v))) ((-2 : ℝ) • (Factor.matrix Q * v.val)) 0 :=
  GS.UnitaryManifold.chartInv_line_hasDerivAt_zero Q.val ⟨v.val, v.property.1, v.property.2.1⟩

theorem orbitParam_fderiv_zero (g : Factors right left) (P : SMat 𝕂 n) (v : PairGenerator right left) :
    fderiv ℝ (orbitParam g P) 0 v =
      GS.UnitaryGeometry.tangentParam (Factor.matrix g.1) P (Factor.matrix g.2)ᴴ
        ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) := by
  have hdL := reconstruct_line_hasDerivAt_zero g.1 v.1
  have hdR := GS.UnitaryManifold.hasDerivAt_matrix_conjTranspose (reconstruct_line_hasDerivAt_zero g.2 v.2)
  have ht : ((-2 : ℝ) • (Factor.matrix g.2 * v.2.val))ᴴ = (2 : ℝ) • (v.2.val * (Factor.matrix g.2)ᴴ) := by
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul, v.2.property.2.1,
      Matrix.neg_mul, smul_neg, ← neg_smul]; norm_num
  rw [ht] at hdR
  have ha : HasDerivAt (fun t : ℝ => orbitParam g P (t • v))
      (GS.UnitaryGeometry.tangentParam (Factor.matrix g.1) P (Factor.matrix g.2)ᴴ
        ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val)) 0 := by
    simpa only [orbitParam, factorLift, action_apply, GS.UnitaryGeometry.kProduct2, zero_smul,
      reconstruct_zero, GS.UnitaryGeometry.tangentParam, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, Prod.smul_fst, Prod.smul_snd] using hasDerivAt_product2 P hdL hdR
  simpa only [one_smul] using
    ((((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt).comp_hasDerivAt_of_eq 0
      ((hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)).unique ha

theorem orbitParam_fderiv_zero_range (g : Factors right left) (P Y : SMat 𝕂 n) :
    (∃ v : PairGenerator right left, fderiv ℝ (orbitParam g P) 0 v = Y) ↔ Y ∈ pointDirections right left (g • P) := by
  change _ ↔ Y ∈ pointDirections right left (GS.UnitaryGeometry.kProduct2 (Factor.matrix g.1) P (Factor.matrix g.2)ᴴ)
  rw [← sharedDirection_iff_pointDirections P (Factor.matrix g.1) (Factor.matrix g.2)ᴴ Y
    (Factor.matrix_shared g.1) (shared_factor_conjTranspose (Factor.matrix_shared g.2))]
  constructor
  · rintro ⟨v, rfl⟩; rw [orbitParam_fderiv_zero]
    exact ⟨((-2 : ℝ) • v.1).val, ((-2 : ℝ) • v.1).property, ((2 : ℝ) • v.2).val, ((2 : ℝ) • v.2).property, rfl⟩
  · rintro ⟨C, hC, Ω, hΩ, rfl⟩
    refine ⟨((-1 / 2 : ℝ) • (⟨C, hC⟩ : Generator left), (1 / 2 : ℝ) • (⟨Ω, hΩ⟩ : Generator right)), ?_⟩
    rw [orbitParam_fderiv_zero]
    change GS.UnitaryGeometry.tangentParam (Factor.matrix g.1) P (Factor.matrix g.2)ᴴ
      ((-2 : ℝ) • ((-1 / 2 : ℝ) • C)) ((2 : ℝ) • ((1 / 2 : ℝ) • Ω)) = _
    norm_num [smul_smul, GS.UnitaryGeometry.tangentParam]

theorem orbitParam_kernel_iff_intertwine (P : SMat 𝕂 n) (v : PairGenerator right left) :
    fderiv ℝ (orbitParam (1 : Factors right left) P) 0 v = 0 ↔ v.1.val * P = P * v.2.val := by
  rw [orbitParam_fderiv_zero]
  change GS.UnitaryGeometry.tangentParam (1 : SMat 𝕂 n) P (1 : SMat 𝕂 n)ᴴ ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) = 0 ↔ _
  simp only [GS.UnitaryGeometry.tangentParam, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul]
  refine ⟨fun h => ?_, fun h => by rw [h, ← add_smul]; norm_num⟩
  have hz : (-2 : ℝ) • (v.1.val * P - P * v.2.val) = 0 := by
    simpa only [smul_sub, sub_eq_add_neg, smul_add, smul_neg, neg_smul, neg_add_rev, neg_neg] using h
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))

theorem factorLift_stabilizes_iff_kernel (P : SMat 𝕂 n) (v : PairGenerator right left) :
    factorLift (1 : Factors right left) v • P = P ↔ fderiv ℝ (orbitParam (1 : Factors right left) P) 0 v = 0 := by
  rw [orbitParam_kernel_iff_intertwine]
  have hA := admissible_of_isSkew v.1.val v.1.property.2.1
  have hB := admissible_of_isSkew v.2.val v.2.property.2.1
  have ho := cayley_unitary v.2.val v.2.property.2.1 hB
  simp only [factorLift, action_apply, reconstruct_matrix, Prod.fst_one, Prod.snd_one, Factor.matrix_one, Matrix.one_mul]
  change cayley v.1.val * P * (cayley v.2.val)ᴴ = P ↔ _
  constructor
  · intro h
    have hi : cayley v.1.val * P = P * cayley v.2.val := by
      simpa only [Matrix.mul_assoc, ho.1, Matrix.mul_one] using congrArg (· * cayley v.2.val) h
    simpa only [cayley_involutive v.1.val hA, cayley_involutive v.2.val hB] using
      GS.UnitaryManifold.cayley_intertwine (cayley v.1.val) (cayley v.2.val) P
        (admissible_cayley v.1.val hA) (admissible_cayley v.2.val hB) hi
  · intro h; rw [GS.UnitaryManifold.cayley_intertwine v.1.val v.2.val P hA hB h, Matrix.mul_assoc, ho.2, Matrix.mul_one]

def matrixReconstruct (Q : Factor s) (v : Generator s) : SMat 𝕂 n := Factor.matrix (reconstruct Q v)

@[simp] theorem matrixReconstruct_zero (Q : Factor s) : matrixReconstruct Q 0 = Factor.matrix Q := by
  simp [matrixReconstruct]

theorem matrixReconstruct_smooth (Q : Factor s) : ContDiff ℝ ⊤ (matrixReconstruct Q) := reconstruct_matrix_smooth Q

theorem matrixReconstruct_fderiv_zero (Q : Factor s) (v : Generator s) :
    fderiv ℝ (matrixReconstruct Q) 0 v = (-2 : ℝ) • (Factor.matrix Q * v.val) :=
  ((((matrixReconstruct_smooth Q).differentiable (by simp) 0).hasFDerivAt).comp_hasDerivAt_of_eq 0
    (by simpa using (hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)).unique (reconstruct_line_hasDerivAt_zero Q v)

theorem coordinateDerivative_reconstruct (Q : Factor s) (v : Generator s) :
    (fderiv ℝ (factorCoordinates Q) (matrixReconstruct Q v)).comp (fderiv ℝ (matrixReconstruct Q) v) =
      ContinuousLinearMap.id ℝ (Generator s) := by
  have hd := (((factorCoordinates_smooth_at Q (matrixReconstruct Q v)
    (reconstruct_mem_source Q v)).differentiableAt (by simp)).hasFDerivAt).comp v
    (((matrixReconstruct_smooth Q).differentiable (by simp) v).hasFDerivAt)
  change HasFDerivAt (fun w : Generator s => factorCoordinates Q (matrixReconstruct Q w)) _ v at hd
  rw [show (fun w => factorCoordinates Q (matrixReconstruct Q w)) = id from funext (factorCoordinates_reconstruct Q)] at hd
  exact hd.unique (hasFDerivAt_id v)

def pairSource (g : Factors right left) : Set (Factors right left) := factorSource g.1 ×ˢ factorSource g.2

def pairCoordinates (g h : Factors right left) : PairGenerator right left :=
  (factorCoordinates g.1 (Factor.matrix h.1), factorCoordinates g.2 (Factor.matrix h.2))

theorem pairSource_open (g : Factors right left) : IsOpen (pairSource g) :=
  (factorSource_open g.1).prod (factorSource_open g.2)

@[simp] theorem self_mem_pairSource (g : Factors right left) : g ∈ pairSource g :=
  ⟨base_mem_factorSource g.1, base_mem_factorSource g.2⟩

theorem factorLift_pairCoordinates (g h : Factors right left) (hh : h ∈ pairSource g) :
    factorLift g (pairCoordinates g h) = h :=
  Prod.ext (reconstruct_factorCoordinates g.1 h.1 hh.1) (reconstruct_factorCoordinates g.2 h.2 hh.2)

theorem factorLift_orbit_isOpenMap (g : Factors right left) (P : SMat 𝕂 n) :
    IsOpenMap (fun v : PairGenerator right left => orbitMapToOrbit right left P (factorLift g v)) :=
  (orbitMapToOrbit_isOpenMap P).comp <|
    (show IsOpenMap (reconstruct g.1) from fun U hU =>
      (factorPartialChart g.1).isOpen_image_symm_of_subset_target hU (Set.subset_univ U)).prodMap
    (show IsOpenMap (reconstruct g.2) from fun U hU =>
      (factorPartialChart g.2).isOpen_image_symm_of_subset_target hU (Set.subset_univ U))

theorem fixed_action_smooth (g : Factors right left) : ContDiff ℝ ⊤ (fun A : SMat 𝕂 n => g • A) :=
  contDiff_iff_contDiffAt.mpr fun _ => smooth_mul_at (smooth_mul_at contDiffAt_const contDiffAt_id) contDiffAt_const

def preferredFactor (P : SMat 𝕂 n) (X : MatrixOrbit right left P) : Factors right left :=
  Classical.choose X.property

@[simp] theorem preferredFactor_spec (P : SMat 𝕂 n) (X : MatrixOrbit right left P) :
    orbitMapToOrbit right left P (preferredFactor P X) = X := Subtype.ext (Classical.choose_spec X.property)

def orbitInverse (P : SMat 𝕂 n) (g : Factors right left) (v : PairGenerator right left) :
    MatrixOrbit right left P := orbitMapToOrbit right left P (factorLift g v)

@[simp] theorem orbitInverse_val (P : SMat 𝕂 n) (g : Factors right left) (v : PairGenerator right left) :
    (orbitInverse P g v).val = orbitParam g P v := rfl

theorem orbitParam_eq_translate (g : Factors right left) (P : SMat 𝕂 n) (v : PairGenerator right left) :
    orbitParam g P v = g • orbitParam (1 : Factors right left) P v := by
  have hf : factorLift g v = g * factorLift (1 : Factors right left) v :=
    Prod.ext (by change reconstruct g.1 v.1 = g.1 * reconstruct 1 v.1; simp [reconstruct])
      (by change reconstruct g.2 v.2 = g.2 * reconstruct 1 v.2; simp [reconstruct])
  unfold orbitParam; rw [hf, mul_smul]

def orbitDerivative (right left : Pattern 𝕂 n) (P : SMat 𝕂 n) : PairGenerator right left →L[ℝ] SMat 𝕂 n :=
  fderiv ℝ (orbitParam (1 : Factors right left) P) 0

abbrev OrbitKernel (right left : Pattern 𝕂 n) (P : SMat 𝕂 n) :=
  LinearMap.ker (orbitDerivative right left P).toLinearMap

abbrev HorizontalModel (right left : Pattern 𝕂 n) (P : SMat 𝕂 n) :=
  horizontalComplement (orbitDerivative right left P)

def horizontalKernelEquiv (right left : Pattern 𝕂 n) (P : SMat 𝕂 n) :
    (HorizontalModel right left P × OrbitKernel right left P) ≃L[ℝ] PairGenerator right left :=
  complementKernelEquiv (orbitDerivative right left P)

def orbitHorizontalInverse (right left : Pattern 𝕂 n) (P : SMat 𝕂 n) :
    SMat 𝕂 n →L[ℝ] HorizontalModel right left P :=
  horizontalLeftInverse (orbitDerivative right left P)

def blockProductCoordinates (s : Pattern 𝕂 n) (x : Generator s × Generator s) : Generator s :=
  factorCoordinates (1 : Factor s) (matrixReconstruct (1 : Factor s) x.1 * matrixReconstruct (1 : Factor s) x.2)

theorem blockProductCoordinates_smooth_zero (s : Pattern 𝕂 n) :
    ContDiffAt ℝ ⊤ (blockProductCoordinates s) 0 := by
  have hc : ContDiffAt ℝ ⊤ (factorCoordinates (1 : Factor s))
      ((fun x : Generator s × Generator s => matrixReconstruct (1 : Factor s) x.1 *
        matrixReconstruct (1 : Factor s) x.2) 0) := by
    simpa using factorCoordinates_smooth_at (1 : Factor s) (1 : SMat 𝕂 n) (by simpa using admissible_one (n := n))
  exact hc.comp 0 (smooth_mul_at
    ((matrixReconstruct_smooth (1 : Factor s)).contDiffAt.comp 0 contDiffAt_fst)
    ((matrixReconstruct_smooth (1 : Factor s)).contDiffAt.comp 0 contDiffAt_snd))

theorem blockProductCoordinates_hasFDerivAt_zero (s : Pattern 𝕂 n) :
    HasFDerivAt (blockProductCoordinates s)
      (ContinuousLinearMap.fst ℝ (Generator s) (Generator s) +
        ContinuousLinearMap.snd ℝ (Generator s) (Generator s)) 0 := by
  have h := ((blockProductCoordinates_smooth_zero s).differentiableAt (by simp)).hasFDerivAt
  convert h using 1
  refine ContinuousLinearMap.ext fun v => Eq.symm ?_
  have hp := hasDerivAt_matrix_mul (reconstruct_line_hasDerivAt_zero (1 : Factor s) v.1)
    (reconstruct_line_hasDerivAt_zero (1 : Factor s) v.2)
  have hc := (factorCoordinates_smooth_at (1 : Factor s) (1 : SMat 𝕂 n)
    (by simpa using admissible_one (n := n))).differentiableAt (by simp)
  have hd : HasDerivAt (fun t : ℝ => matrixReconstruct (1 : Factor s) (t • v.1) *
      matrixReconstruct (1 : Factor s) (t • v.2))
      (fderiv ℝ (matrixReconstruct (1 : Factor s)) 0 (v.1 + v.2)) 0 := by
    rw [matrixReconstruct_fderiv_zero]
    simpa only [matrixReconstruct, zero_smul, reconstruct_zero, matrixReconstruct_zero, Factor.matrix_one,
      Matrix.one_mul, Matrix.mul_one, Submodule.coe_add, smul_add] using hp
  have hinv := congrArg (fun D : Generator s →L[ℝ] Generator s => D (v.1 + v.2))
    (coordinateDerivative_reconstruct (1 : Factor s) 0)
  have he : fderiv ℝ (factorCoordinates (1 : Factor s)) (1 : SMat 𝕂 n)
      (fderiv ℝ (matrixReconstruct (1 : Factor s)) 0 (v.1 + v.2)) = v.1 + v.2 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      matrixReconstruct_zero, Factor.matrix_one] using hinv
  have hactual : HasDerivAt (fun t : ℝ => blockProductCoordinates s (t • v)) (v.1 + v.2) 0 :=
    he ▸ hc.hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (by simp)
  exact (h.comp_hasDerivAt_of_eq 0 (by simpa using (hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)).unique hactual

def factorProductCoordinates (right left : Pattern 𝕂 n)
    (x : PairGenerator right left × PairGenerator right left) : PairGenerator right left :=
  (blockProductCoordinates left (x.1.1, x.2.1), blockProductCoordinates right (x.1.2, x.2.2))

theorem factorProductCoordinates_eq (x y : PairGenerator right left) :
    factorProductCoordinates right left (x, y) =
      pairCoordinates (1 : Factors right left)
        (factorLift (1 : Factors right left) x * factorLift (1 : Factors right left) y) := rfl

section SliceAndProduct
variable (right left : Pattern 𝕂 n) (P : SMat 𝕂 n)
local instance sliceModelNormedSpace : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _

def sliceProduct (x : HorizontalModel right left P × OrbitKernel right left P) : PairGenerator right left :=
  factorProductCoordinates right left (x.1.val, x.2.val)

def sliceInclusion : (HorizontalModel right left P × OrbitKernel right left P) →L[ℝ]
    (PairGenerator right left × PairGenerator right left) :=
  ((HorizontalModel right left P).subtypeL.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((OrbitKernel right left P).subtypeL.comp (ContinuousLinearMap.snd ℝ _ _))

theorem factorProductCoordinates_smooth_zero : ContDiffAt ℝ ⊤ (factorProductCoordinates right left) 0 := by
  let rL : (PairGenerator right left × PairGenerator right left) →L[ℝ] (Generator left × Generator left) :=
    ((ContinuousLinearMap.fst ℝ (Generator left) (Generator right)).comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((ContinuousLinearMap.fst ℝ (Generator left) (Generator right)).comp (ContinuousLinearMap.snd ℝ _ _))
  let rR : (PairGenerator right left × PairGenerator right left) →L[ℝ] (Generator right × Generator right) :=
    ((ContinuousLinearMap.snd ℝ (Generator left) (Generator right)).comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((ContinuousLinearMap.snd ℝ (Generator left) (Generator right)).comp (ContinuousLinearMap.snd ℝ _ _))
  exact ((by simpa using blockProductCoordinates_smooth_zero left : ContDiffAt ℝ ⊤ _ (rL 0)).comp 0 rL.contDiff.contDiffAt).prodMk
    ((by simpa using blockProductCoordinates_smooth_zero right : ContDiffAt ℝ ⊤ _ (rR 0)).comp 0 rR.contDiff.contDiffAt)

theorem factorProductCoordinates_hasFDerivAt_zero :
    HasFDerivAt (factorProductCoordinates right left)
      (ContinuousLinearMap.fst ℝ (PairGenerator right left) (PairGenerator right left) +
        ContinuousLinearMap.snd ℝ (PairGenerator right left) (PairGenerator right left)) 0 := by
  let rL : (PairGenerator right left × PairGenerator right left) →L[ℝ] (Generator left × Generator left) :=
    ((ContinuousLinearMap.fst ℝ (Generator left) (Generator right)).comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((ContinuousLinearMap.fst ℝ (Generator left) (Generator right)).comp (ContinuousLinearMap.snd ℝ _ _))
  let rR : (PairGenerator right left × PairGenerator right left) →L[ℝ] (Generator right × Generator right) :=
    ((ContinuousLinearMap.snd ℝ (Generator left) (Generator right)).comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((ContinuousLinearMap.snd ℝ (Generator left) (Generator right)).comp (ContinuousLinearMap.snd ℝ _ _))
  have hl := (by simpa only [map_zero] using blockProductCoordinates_hasFDerivAt_zero left :
    HasFDerivAt _ _ (rL 0)).comp 0 rL.hasFDerivAt
  have hr := (by simpa only [map_zero] using blockProductCoordinates_hasFDerivAt_zero right :
    HasFDerivAt _ _ (rR 0)).comp 0 rR.hasFDerivAt
  convert hl.prodMk hr using 1 <;> first | rfl | (ext v <;> rfl)

theorem sliceProduct_smooth_zero : ContDiffAt ℝ ⊤ (sliceProduct right left P) 0 :=
  ContDiffAt.comp (f := fun x => sliceInclusion right left P x) (g := factorProductCoordinates right left) 0
    (by simpa only [map_zero] using factorProductCoordinates_smooth_zero right left)
    (@ContinuousLinearMap.contDiff ℝ (HorizontalModel right left P × OrbitKernel right left P)
      (PairGenerator right left × PairGenerator right left) _ _ _ _ _ ⊤ (sliceInclusion right left P)).contDiffAt

set_option maxHeartbeats 600000 in
theorem sliceProduct_hasFDerivAt_zero :
    HasFDerivAt (sliceProduct right left P) (horizontalKernelEquiv right left P : _ →L[ℝ] _) 0 := by
  have hd := HasFDerivAt.comp (𝕜 := ℝ) (f := fun x => sliceInclusion right left P x)
    (g := factorProductCoordinates right left) 0
    (by simpa only [map_zero] using factorProductCoordinates_hasFDerivAt_zero right left)
    (@ContinuousLinearMap.hasFDerivAt ℝ _ (HorizontalModel right left P × OrbitKernel right left P) _ _ _
      (PairGenerator right left × PairGenerator right left) _ _ _ (sliceInclusion right left P) 0)
  convert hd using 1 <;> first | rfl | (ext v <;> rfl)

def sliceProductChart :
    OpenPartialHomeomorph (HorizontalModel right left P × OrbitKernel right left P) (PairGenerator right left) :=
  (sliceProduct_smooth_zero right left P).toOpenPartialHomeomorph _ (sliceProduct_hasFDerivAt_zero right left P) (by simp)

theorem sliceProductChart_zero_mem_source :
    (0 : HorizontalModel right left P × OrbitKernel right left P) ∈ (sliceProductChart right left P).source :=
  (sliceProduct_smooth_zero right left P).mem_toOpenPartialHomeomorph_source _ (by simp)

def horizontalValue (h : HorizontalModel right left P) : SMat 𝕂 n :=
  orbitParam (1 : Factors right left) P h.val

def horizontalPoint (h : HorizontalModel right left P) : MatrixOrbit right left P :=
  orbitInverse P (1 : Factors right left) h.val

@[simp] theorem horizontalPoint_val (h : HorizontalModel right left P) :
    (horizontalPoint right left P h).val = horizontalValue right left P h := orbitInverse_val P 1 h.val

theorem horizontalValue_smooth : ContDiff ℝ ⊤ (horizontalValue right left P) :=
  (orbitParam_smooth 1 P).comp (horizontalComplement (orbitDerivative right left P)).subtypeL.contDiff

@[simp] theorem horizontalValue_zero : horizontalValue right left P 0 = P := by
  simp [horizontalValue, orbitParam_zero, one_smul]

def horizontalProjected (h : HorizontalModel right left P) : HorizontalModel right left P :=
  orbitHorizontalInverse right left P (horizontalValue right left P h - P)

theorem horizontalProjected_smooth : ContDiff ℝ ⊤ (horizontalProjected right left P) :=
  (orbitHorizontalInverse right left P).contDiff.comp ((horizontalValue_smooth right left P).sub contDiff_const)

@[simp] theorem horizontalProjected_zero : horizontalProjected right left P 0 = 0 := by simp [horizontalProjected]

theorem horizontalProjected_hasFDerivAt_zero :
    HasFDerivAt (horizontalProjected right left P) (ContinuousLinearMap.id ℝ (HorizontalModel right left P)) 0 := by
  have hv : HasFDerivAt (horizontalValue right left P) (horizontalRestriction (orbitDerivative right left P)) 0 := by
    unfold horizontalValue
    simpa only [Function.comp_def, horizontalValue, horizontalRestriction, orbitDerivative, map_zero] using
      HasFDerivAt.comp (f := fun h : HorizontalModel right left P => h.val) (g := orbitParam (1 : Factors right left) P) 0
        (((orbitParam_smooth (1 : Factors right left) P).differentiable (by simp) 0).hasFDerivAt)
        (horizontalComplement (orbitDerivative right left P)).subtypeL.hasFDerivAt
  have hh := (orbitHorizontalInverse right left P).hasFDerivAt.comp 0 (hv.sub_const P)
  unfold horizontalProjected
  simpa only [Function.comp_def, horizontalProjected, orbitHorizontalInverse, horizontalLeftInverse_comp] using hh

structure ProjectedSliceData where
  domain : Set (HorizontalModel right left P)
  coordinates : SMat 𝕂 n → HorizontalModel right left P
  open_domain : IsOpen domain
  zero_mem : 0 ∈ domain
  left_inverse : ∀ h ∈ domain, coordinates (horizontalValue right left P h) = h
  coordinates_smooth : ∀ h ∈ domain, ContDiffAt ℝ ⊤ coordinates (horizontalValue right left P h)

theorem exists_projectedSliceData : Nonempty (ProjectedSliceData right left P) := by
  let e : OpenPartialHomeomorph (HorizontalModel right left P) (HorizontalModel right left P) :=
    (horizontalProjected_smooth right left P).contDiffAt.toOpenPartialHomeomorph (horizontalProjected right left P)
      (f' := ContinuousLinearEquiv.refl ℝ (HorizontalModel right left P))
      (horizontalProjected_hasFDerivAt_zero right left P) (by simp)
  have h0s : 0 ∈ e.source := (horizontalProjected_smooth right left P).contDiffAt.mem_toOpenPartialHomeomorph_source
    (f' := ContinuousLinearEquiv.refl ℝ (HorizontalModel right left P))
    (horizontalProjected_hasFDerivAt_zero right left P) (by simp)
  have h0t : 0 ∈ e.target := by simpa [e] using e.map_source h0s
  have hinv : ContDiffAt ℝ ⊤ e.symm 0 := by
    simpa only [horizontalProjected_zero, ContDiffAt.localInverse, HasStrictFDerivAt.localInverse,
      ContDiffAt.toOpenPartialHomeomorph, e] using
      (horizontalProjected_smooth right left P).contDiffAt.to_localInverse
        (f' := ContinuousLinearEquiv.refl ℝ (HorizontalModel right left P))
        (horizontalProjected_hasFDerivAt_zero right left P) (by simp)
  obtain ⟨W, hWsub, hWopen, hWzero⟩ := mem_nhds_iff.mp
    (inter_mem (e.open_target.mem_nhds h0t) (hinv.eventually (by simp)))
  exact ⟨⟨e.source ∩ horizontalProjected right left P ⁻¹' W,
    fun A => e.symm (orbitHorizontalInverse right left P (A - P)),
    e.open_source.inter (hWopen.preimage (horizontalProjected_smooth right left P).continuous),
    ⟨h0s, by simpa using hWzero⟩,
    fun h hh => e.left_inv hh.1,
    fun h hh => by
      have hi : ContDiffAt ℝ ⊤ e.symm (horizontalProjected right left P h) := (hWsub hh.2).2
      exact hi.comp (horizontalValue right left P h)
        ((orbitHorizontalInverse right left P).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt⟩⟩

def projectedSliceData : ProjectedSliceData right left P :=
  Classical.choice (exists_projectedSliceData right left P)

theorem horizontalOrbit_fderiv_zero_range (g : Factors right left) (Z : SMat 𝕂 n) :
    (∃ h : HorizontalModel right left P,
      fderiv ℝ (fun h : HorizontalModel right left P => orbitParam g P h.val) 0 h = Z) ↔
    Z ∈ pointDirections right left (g • P) := by
  have hdf : fderiv ℝ (fun h : HorizontalModel right left P => orbitParam g P h.val) 0 =
      (fderiv ℝ (orbitParam g P) 0).comp (HorizontalModel right left P).subtypeL := by
    refine HasFDerivAt.fderiv ?_
    simpa only [map_zero, Function.comp_def] using
      HasFDerivAt.comp (f := fun h : HorizontalModel right left P => h.val) (g := orbitParam g P) 0
        (((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt)
        (HorizontalModel right left P).subtypeL.hasFDerivAt
  rw [← orbitParam_fderiv_zero_range g P Z]; constructor
  · rintro ⟨h, rfl⟩; exact ⟨h.val, by rw [hdf]; rfl⟩
  · rintro ⟨v, rfl⟩
    let z := (horizontalKernelEquiv right left P).symm v
    have hz : (z.1.val : PairGenerator right left) + z.2.val = v :=
      (horizontalKernelEquiv right left P).apply_symm_apply v
    have hk : fderiv ℝ (orbitParam g P) 0 z.2.val = 0 := by
      have hi := (orbitParam_kernel_iff_intertwine P z.2.val).mp z.2.property
      rw [orbitParam_fderiv_zero]; simp only [GS.UnitaryGeometry.tangentParam, Matrix.smul_mul, Matrix.mul_smul]
      have he : Factor.matrix g.1 * z.2.val.1.val * P * (Factor.matrix g.2)ᴴ =
          Factor.matrix g.1 * P * z.2.val.2.val * (Factor.matrix g.2)ᴴ := by
        simpa only [Matrix.mul_assoc] using congrArg (fun A => Factor.matrix g.1 * A * (Factor.matrix g.2)ᴴ) hi
      rw [he, ← add_smul]; norm_num
    exact ⟨z.1, by rw [hdf, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, ← hz, map_add, hk, add_zero]⟩

end SliceAndProduct

section IrredAtlas
variable (right left : Pattern 𝕂 n) (P : SMat 𝕂 n)
local instance orbitAtlasNormedSpace : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
attribute [local irreducible] sharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

def productFactors (z : HorizontalModel right left P × OrbitKernel right left P) : Factors right left :=
  factorLift 1 z.1.val * factorLift 1 z.2.val

def goodProductChart :
    OpenPartialHomeomorph (HorizontalModel right left P × OrbitKernel right left P) (PairGenerator right left) :=
  (sliceProductChart right left P).restrOpen (productFactors right left P ⁻¹' pairSource 1) <|
    (pairSource_open 1).preimage <|
      ((continuous_factorLift 1).comp (continuous_subtype_val.comp continuous_fst)).mul
        ((continuous_factorLift 1).comp (continuous_subtype_val.comp continuous_snd))

theorem goodProductChart_zero_source :
    (0 : HorizontalModel right left P × OrbitKernel right left P) ∈ (goodProductChart right left P).source :=
  ⟨sliceProductChart_zero_mem_source right left P, by
    change factorLift (1 : Factors right left) 0 * factorLift 1 0 ∈ pairSource 1
    simpa using self_mem_pairSource (1 : Factors right left)⟩

theorem goodProductChart_orbit (z : HorizontalModel right left P × OrbitKernel right left P)
    (hz : z ∈ (goodProductChart right left P).source) :
    orbitMapToOrbit right left P (factorLift 1 (goodProductChart right left P z)) = horizontalPoint right left P z.1 := by
  apply Subtype.ext
  change factorLift 1 (sliceProduct right left P z) • P = _
  have hz' : factorLift (1 : Factors right left) z.1.val * factorLift 1 z.2.val ∈ pairSource 1 := hz.2
  have hk : fderiv ℝ (orbitParam (1 : Factors right left) P) 0 z.2.val = 0 := by
    simpa only [orbitDerivative] using (show orbitDerivative right left P z.2.val = 0 from z.2.property)
  rw [sliceProduct, factorProductCoordinates_eq, factorLift_pairCoordinates 1 _ hz', mul_smul,
    (factorLift_stabilizes_iff_kernel P z.2.val).mpr hk]; rfl

def horizontalChartDomain : Set (HorizontalModel right left P) :=
  (projectedSliceData right left P).domain ∩
    (fun h => (h, (0 : OrbitKernel right left P))) ⁻¹' (goodProductChart right left P).source

theorem horizontalChartDomain_open : IsOpen (horizontalChartDomain right left P) :=
  (projectedSliceData right left P).open_domain.inter
    ((goodProductChart right left P).open_source.preimage (continuous_id.prodMk continuous_const))

theorem horizontalChartDomain_zero : (0 : HorizontalModel right left P) ∈ horizontalChartDomain right left P :=
  ⟨(projectedSliceData right left P).zero_mem, goodProductChart_zero_source right left P⟩

theorem horizontalChartImage_open :
    IsOpen (horizontalPoint right left P '' horizontalChartDomain right left P) :=
  isOpen_slice_image_of_productChart (goodProductChart right left P)
    (fun x => orbitMapToOrbit right left P (factorLift 1 x))
    (horizontalPoint right left P) (factorLift_orbit_isOpenMap 1 P)
    (goodProductChart_orbit right left P) _ (horizontalChartDomain_open right left P)
    fun _ hh => ⟨0, hh.2⟩

def baseOrbitSlice : SmoothSlice (E := HorizontalModel right left P) (MulAction.orbit (Factors right left) P) :=
  GS.Extensions.smoothSliceOfParametrization
    (horizontalPoint right left P) (projectedSliceData right left P).coordinates
    (horizontalChartDomain right left P) (horizontalValue_smooth right left P)
    (horizontalChartDomain_open right left P) (horizontalChartImage_open right left P)
    (fun h hh => (projectedSliceData right left P).coordinates_smooth h hh.1)
    (fun h hh => (projectedSliceData right left P).left_inverse h hh.1)

def orbitTranslate (g : Factors right left) (X : MatrixOrbit right left P) : MatrixOrbit right left P :=
  ⟨g • X.val, let ⟨h, hh⟩ := X.property; ⟨g * h, by simp [mul_smul, hh]⟩⟩

@[simp] theorem orbitTranslate_val (g : Factors right left) (X : MatrixOrbit right left P) :
    (orbitTranslate right left P g X).val = g • X.val := rfl

def translatedOrbitSlice (g : Factors right left) :
    SmoothSlice (E := HorizontalModel right left P) (MulAction.orbit (Factors right left) P) :=
  GS.Extensions.translateSmoothSlice (baseOrbitSlice right left P)
    (fun A => g • A) (fun A => g⁻¹ • A)
    (orbitTranslate right left P g) (orbitTranslate right left P g⁻¹)
    (orbitTranslate_val right left P g) (orbitTranslate_val right left P g⁻¹)
    (fun X => Subtype.ext (smul_inv_smul g X.val)) (fun X => Subtype.ext (inv_smul_smul g X.val))
    (fixed_action_smooth g) (fixed_action_smooth g⁻¹)
    ((continuous_subtype_val.const_smul g⁻¹).subtype_mk _)

theorem translatedOrbitSlice_centre_mem (g : Factors right left) :
    orbitMapToOrbit right left P g ∈ (translatedOrbitSlice right left P g).source := by
  have he : orbitTranslate right left P g⁻¹ (orbitMapToOrbit right left P g) = horizontalPoint right left P 0 := by
    apply Subtype.ext; change g⁻¹ • (g • P) = _; rw [inv_smul_smul, horizontalPoint_val, horizontalValue_zero]
  change orbitTranslate right left P g⁻¹ _ ∈ horizontalPoint right left P '' horizontalChartDomain right left P
  rw [he]; exact ⟨0, horizontalChartDomain_zero right left P, rfl⟩

theorem translatedOrbitSlice_centre_coordinates (g : Factors right left) :
    (translatedOrbitSlice right left P g).coordinates (orbitMapToOrbit right left P g).val = 0 := by
  change (projectedSliceData right left P).coordinates (g⁻¹ • (g • P)) = 0
  rw [inv_smul_smul]; simpa only [horizontalValue_zero] using
    (projectedSliceData right left P).left_inverse 0 (projectedSliceData right left P).zero_mem

def preferredOrbitSlice (X : MatrixOrbit right left P) :
    SmoothSlice (E := HorizontalModel right left P) (MulAction.orbit (Factors right left) P) :=
  translatedOrbitSlice right left P (preferredFactor P X)

theorem preferredOrbitSlice_covers (X : MatrixOrbit right left P) :
    X ∈ (preferredOrbitSlice right left P X).source := by
  simpa only [preferredFactor_spec, preferredOrbitSlice] using translatedOrbitSlice_centre_mem right left P (preferredFactor P X)

def sharedOrbitChartedSpace : ChartedSpace (HorizontalModel right left P) (MatrixOrbit right left P) :=
  sliceChartedSpace (preferredOrbitSlice right left P) (preferredOrbitSlice_covers right left P)

theorem sharedOrbitIsManifold :
    letI := sharedOrbitChartedSpace right left P
    IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤ (MatrixOrbit right left P) :=
  slice_isManifold (preferredOrbitSlice right left P) (preferredOrbitSlice_covers right left P)

theorem sharedOrbit_val_contMDiff :
    letI := sharedOrbitChartedSpace right left P
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, SMat 𝕂 n)) ⊤ (fun X : MatrixOrbit right left P => X.val) :=
  slice_val_contMDiff (preferredOrbitSlice right left P) (preferredOrbitSlice_covers right left P)

theorem sharedOrbit_val_mfderiv_eq (X : MatrixOrbit right left P) :
    letI := sharedOrbitChartedSpace right left P
    mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, SMat 𝕂 n)) (fun Y : MatrixOrbit right left P => Y.val) X =
      fderiv ℝ (fun h : HorizontalModel right left P => preferredFactor P X • horizontalValue right left P h) 0 := by
  letI := sharedOrbitChartedSpace right left P
  have hh := slice_val_mfderiv_eq (preferredOrbitSlice right left P) (preferredOrbitSlice_covers right left P) X
  have hz : (preferredOrbitSlice right left P X).coordinates X.val = 0 := by
    simpa only [preferredFactor_spec, preferredOrbitSlice] using
      translatedOrbitSlice_centre_coordinates right left P (preferredFactor P X)
  rw [hz] at hh
  simpa only [preferredOrbitSlice, translatedOrbitSlice, baseOrbitSlice,
    GS.Extensions.translateSmoothSlice, GS.Extensions.smoothSliceOfParametrization,
    orbitTranslate_val, horizontalPoint_val] using hh

theorem sharedOrbit_val_mfderiv_injective (X : MatrixOrbit right left P) :
    letI := sharedOrbitChartedSpace right left P
    Function.Injective (mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, SMat 𝕂 n))
      (fun Y : MatrixOrbit right left P => Y.val) X) :=
  slice_val_mfderiv_injective (preferredOrbitSlice right left P) (preferredOrbitSlice_covers right left P) X

end IrredAtlas

section BridgeAndSections
variable (right left : Pattern 𝕂 n) (P : SMat 𝕂 n)
local instance bridgeNormedSpace : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
local instance bridgeChartedSpace : ChartedSpace (HorizontalModel right left P) (MatrixOrbit right left P) :=
  sharedOrbitChartedSpace right left P

theorem orbit_tangent_image_iff (X : MatrixOrbit right left P) (Z : SMat 𝕂 n) :
    (∃ v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X,
      mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, SMat 𝕂 n))
        (fun Y : MatrixOrbit right left P => Y.val) X v = Z) ↔
    Z ∈ pointDirections right left X.val := by
  rw [sharedOrbit_val_mfderiv_eq right left P X]
  have he : (fun h : HorizontalModel right left P => preferredFactor P X • horizontalValue right left P h) =
      fun h : HorizontalModel right left P => orbitParam (preferredFactor P X) P h.val :=
    funext fun h => (orbitParam_eq_translate (preferredFactor P X) P h.val).symm
  rw [he]
  have hh := horizontalOrbit_fderiv_zero_range right left P (preferredFactor P X) Z
  have hg : preferredFactor P X • P = X.val := congrArg Subtype.val (preferredFactor_spec P X)
  rw [hg] at hh
  exact ⟨fun ⟨v, hv⟩ => hh.mp ⟨v, hv⟩, fun hZ => let ⟨v, hv⟩ := hh.mpr hZ; ⟨v, hv⟩⟩

theorem pointProjection_fixed_iff_tangent_image (X : MatrixOrbit right left P) (Z : SMat 𝕂 n) :
    pointProjection right left X.val Z = Z ↔
      ∃ v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X,
        mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, SMat 𝕂 n))
          (fun Y : MatrixOrbit right left P => Y.val) X v = Z := by
  rw [orbit_tangent_image_iff right left P X Z]
  exact ⟨fun h => h ▸ pointProjection_mem X.val Z, pointProjection_of_mem X.val Z⟩

theorem pointProjection_unique_tangent_lift (X : MatrixOrbit right left P) (Z : SMat 𝕂 n) :
    ∃! v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X,
      mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, SMat 𝕂 n))
        (fun Y : MatrixOrbit right left P => Y.val) X v = pointProjection right left X.val Z := by
  obtain ⟨v, hv⟩ := (orbit_tangent_image_iff right left P X _).mpr (pointProjection_mem X.val Z)
  exact ⟨v, hv, fun w hw => sharedOrbit_val_mfderiv_injective right left P X (hw.trans hv.symm)⟩

theorem sharedOrbit_contMDiff_iff_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → MatrixOrbit right left P) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, HorizontalModel right left P)) ⊤ f ↔ ContDiff ℝ ⊤ (fun x => (f x).val) :=
  GS.OverlapGeometry.slice_contMDiff_iff_contDiff (preferredOrbitSlice right left P)
    (preferredOrbitSlice_covers right left P) f

theorem sharedOrbit_contMDiff_iff_ambient {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (f : M → MatrixOrbit right left P) :
    ContMDiff I (𝓘(ℝ, HorizontalModel right left P)) ⊤ f ↔ ContMDiff I (𝓘(ℝ, SMat 𝕂 n)) ⊤ (fun x => (f x).val) :=
  GS.OverlapGeometry.slice_contMDiff_iff_ambient (preferredOrbitSlice right left P)
    (preferredOrbitSlice_covers right left P) I f

def localFactors (g : Factors right left) (A : SMat 𝕂 n) : Factors right left :=
  factorLift g ((translatedOrbitSlice right left P g).coordinates A).val

theorem localFactors_right_inverse (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    orbitMapToOrbit right left P (localFactors right left P g X.val) = X := by
  have ho : orbitMapToOrbit right left P (localFactors right left P g X.val) =
      (translatedOrbitSlice right left P g).parametrization ((translatedOrbitSlice right left P g).coordinates X.val) :=
    Subtype.ext (orbitParam_eq_translate g P _)
  exact ho.trans ((translatedOrbitSlice right left P g).left_inverse X hX)

theorem localFactors_left_matrix_smooth_at (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    ContDiffAt ℝ ⊤ (fun A : SMat 𝕂 n => Factor.matrix (localFactors right left P g A).1) X.val :=
  (reconstruct_matrix_smooth g.1).contDiffAt.comp X.val <|
    contDiffAt_fst.comp X.val <| (HorizontalModel right left P).subtypeL.contDiff.contDiffAt.comp X.val <|
      (translatedOrbitSlice right left P g).coordinates_smooth X hX

theorem localFactors_right_matrix_smooth_at (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    ContDiffAt ℝ ⊤ (fun A : SMat 𝕂 n => Factor.matrix (localFactors right left P g A).2) X.val :=
  (reconstruct_matrix_smooth g.2).contDiffAt.comp X.val <|
    contDiffAt_snd.comp X.val <| (HorizontalModel right left P).subtypeL.contDiff.contDiffAt.comp X.val <|
      (translatedOrbitSlice right left P g).coordinates_smooth X hX

end BridgeAndSections

end GS.UnitarySharing
