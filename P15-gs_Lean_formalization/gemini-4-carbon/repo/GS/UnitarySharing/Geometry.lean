module

public import GS.UnitarySharing.OrbitAtlas
public import GS.UnitaryManifold.UnitCayley
public import GS.UnitaryManifold.MatrixCalculus
public import GS.UnitaryManifold.FrobeniusDual
public import GS.Extensions.TangentSections
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold InnerProductSpace Set Filter
open scoped Topology Manifold ContDiff

namespace GS.UnitarySharing
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

section LiftAndCayley
variable {right left : Pattern 𝕂 n}

def generatorInner (v w : PairGenerator right left) : ℝ :=
  cFrobInner v.1.val w.1.val + cFrobInner v.2.val w.2.val

theorem generatorInner_add_left (u v w : PairGenerator right left) :
    generatorInner (u + v) w = generatorInner u w + generatorInner v w := by
  simp only [generatorInner, Prod.fst_add, Prod.snd_add, Submodule.coe_add, cFrobInner_add_left]; ring

theorem generatorInner_sub_left (u v w : PairGenerator right left) :
    generatorInner (u - v) w = generatorInner u w - generatorInner v w := by
  change cFrobInner (u.1.val - v.1.val) w.1.val + cFrobInner (u.2.val - v.2.val) w.2.val = _
  rw [cFrobInner_sub_left, cFrobInner_sub_left]; unfold generatorInner; ring

theorem generatorInner_smul_left (a : ℝ) (v w : PairGenerator right left) :
    generatorInner (a • v) w = a * generatorInner v w := by
  change cFrobInner (a • v.1.val) w.1.val + cFrobInner (a • v.2.val) w.2.val = _
  rw [cFrobInner_real_smul_left, cFrobInner_real_smul_left]; unfold generatorInner; ring

@[simp] theorem generatorEnergy_eq_zero_iff (v : PairGenerator right left) :
    generatorInner v v = 0 ↔ v = 0 := by
  refine ⟨fun h => ?_, fun h => by subst h; simp [generatorInner]⟩
  change cFrobSq v.1.val + cFrobSq v.2.val = 0 at h
  have h1 : cFrobSq v.1.val = 0 := by linarith [cFrobSq_nonneg v.1.val, cFrobSq_nonneg v.2.val]
  have h2 : cFrobSq v.2.val = 0 := by linarith [cFrobSq_nonneg v.1.val, cFrobSq_nonneg v.2.val]
  exact Prod.ext (Subtype.ext ((cFrobSq_eq_zero_iff _).mp h1)) (Subtype.ext ((cFrobSq_eq_zero_iff _).mp h2))

abbrev GeneratorHilbert (𝕂 : Type) [RCLike 𝕂] (n : ℕ) := WithLp 2 (KFrobCoordinates 𝕂 n × KFrobCoordinates 𝕂 n)

def generatorEncoding (right left : Pattern 𝕂 n) : PairGenerator right left →ₗ[ℝ] GeneratorHilbert 𝕂 n :=
  (WithLp.linearEquiv 2 ℝ (KFrobCoordinates 𝕂 n × KFrobCoordinates 𝕂 n)).symm.toLinearMap.comp <|
    (((encodeCFrob.comp (sharedSkewSpace 𝕂 left.size left.label).subtype).comp (LinearMap.fst ℝ _ _)).prod
     ((encodeCFrob.comp (sharedSkewSpace 𝕂 right.size right.label).subtype).comp (LinearMap.snd ℝ _ _)))

def IsHorizontal (X : SMat 𝕂 n) (v : PairGenerator right left) : Prop :=
  ∀ k : PairGenerator right left, pointMap right left X k = 0 → generatorInner v k = 0

theorem horizontal_lift_unique (X : SMat 𝕂 n) (v w : PairGenerator right left)
    (hv : IsHorizontal X v) (hw : IsHorizontal X w)
    (h : pointMap right left X v = pointMap right left X w) : v = w := by
  have hk : pointMap right left X (v - w) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp <| (generatorEnergy_eq_zero_iff (v - w)).mp <| by
    rw [generatorInner_sub_left, hv _ hk, hw _ hk, sub_self]

theorem exists_horizontal_lift (X Z : SMat 𝕂 n) :
    ∃ v : PairGenerator right left, pointMap right left X v = pointProjection right left X Z ∧ IsHorizontal X v := by
  obtain ⟨v, hv⟩ := pointProjection_mem (right := right) (left := left) X Z
  let K : Submodule ℝ (GeneratorHilbert 𝕂 n) := (pointMap right left X).ker.map (generatorEncoding right left)
  obtain ⟨k, hk0, hkeq⟩ : ∃ k : PairGenerator right left, pointMap right left X k = 0 ∧
      generatorEncoding right left k = (K.orthogonalProjection (generatorEncoding right left v) : GeneratorHilbert 𝕂 n) :=
    (K.orthogonalProjection (generatorEncoding right left v)).property
  refine ⟨v - k, by rw [map_sub, hk0, sub_zero, hv], fun u hu => ?_⟩
  have hin (a b : PairGenerator right left) : ⟪generatorEncoding right left a, generatorEncoding right left b⟫_ℝ =
      generatorInner a b := by
    change ⟪encodeCFrob a.1.val, encodeCFrob b.1.val⟫_ℝ + ⟪encodeCFrob a.2.val, encodeCFrob b.2.val⟫_ℝ = _
    rw [encodeCFrob_inner, encodeCFrob_inner]; rfl
  have h := Submodule.orthogonalProjectionFn_inner_eq_zero (K := K)
    (generatorEncoding right left v) (generatorEncoding right left u) ⟨u, hu, rfl⟩
  rw [Submodule.starProjection_apply] at h
  rw [← hin, map_sub, hkeq]; exact h

def selectedLift (right left : Pattern 𝕂 n) (X Z : SMat 𝕂 n) : PairGenerator right left :=
  Classical.choose (exists_horizontal_lift (right := right) (left := left) X Z)

theorem selectedLift_synthesis (X Z : SMat 𝕂 n) :
    pointMap right left X (selectedLift right left X Z) = pointProjection right left X Z :=
  (Classical.choose_spec (exists_horizontal_lift (right := right) (left := left) X Z)).1

theorem selectedLift_horizontal (X Z : SMat 𝕂 n) :
    IsHorizontal X (selectedLift right left X Z) :=
  (Classical.choose_spec (exists_horizontal_lift (right := right) (left := left) X Z)).2

def minimumNormLift (right left : Pattern 𝕂 n) (X : SMat 𝕂 n) : SMat 𝕂 n →L[ℝ] PairGenerator right left :=
  ({ toFun := selectedLift right left X
     map_add' := fun Z W => horizontal_lift_unique X _ _ (selectedLift_horizontal X _)
       (fun k hk => by rw [generatorInner_add_left, selectedLift_horizontal X Z k hk, selectedLift_horizontal X W k hk, add_zero])
       (by simp [map_add, selectedLift_synthesis])
     map_smul' := fun a Z => horizontal_lift_unique X _ _ (selectedLift_horizontal X _)
       (fun k hk => by rw [generatorInner_smul_left, selectedLift_horizontal X Z k hk, mul_zero])
       (by simp [map_smul, selectedLift_synthesis]) } : SMat 𝕂 n →ₗ[ℝ] PairGenerator right left).toContinuousLinearMap

theorem minimumNormLift_synthesis (X Z : SMat 𝕂 n) :
    pointMap right left X (minimumNormLift right left X Z) = pointProjection right left X Z :=
  (Classical.choose_spec (exists_horizontal_lift (right := right) (left := left) X Z)).1

theorem minimumNormLift_horizontal (X Z : SMat 𝕂 n) :
    IsHorizontal X (minimumNormLift right left X Z) :=
  (Classical.choose_spec (exists_horizontal_lift (right := right) (left := left) X Z)).2

theorem minimumNormLift_unique (X Z : SMat 𝕂 n) (v : PairGenerator right left)
    (hv : pointMap right left X v = pointProjection right left X Z) (hh : IsHorizontal X v) :
    v = minimumNormLift right left X Z :=
  horizontal_lift_unique X v _ hh (minimumNormLift_horizontal X Z) (hv.trans (minimumNormLift_synthesis X Z).symm)

@[simp] theorem minimumNormLift_projected (X Z : SMat 𝕂 n) :
    minimumNormLift right left X (pointProjection right left X Z) = minimumNormLift right left X Z :=
  minimumNormLift_unique X Z _ (by rw [minimumNormLift_synthesis, pointProjection_idempotent])
    (minimumNormLift_horizontal X _)

def generatorAction (g : Factors right left) : PairGenerator right left →ₗ[ℝ] PairGenerator right left where
  toFun v :=
    (⟨Factor.matrix g.1 * v.1.val * (Factor.matrix g.1)ᴴ,
      sharedSkew_conjugate left.positive left.divides (Factor.matrix_shared g.1) v.1.property⟩,
     ⟨Factor.matrix g.2 * v.2.val * (Factor.matrix g.2)ᴴ,
      sharedSkew_conjugate right.positive right.divides (Factor.matrix_shared g.2) v.2.property⟩)
  map_add' v w := Prod.ext (Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul]))
    (Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul]))
  map_smul' a v := Prod.ext
    (Subtype.ext (by change Factor.matrix g.1 * (a • v.1.val) * _ = a • _; rw [Matrix.mul_smul, Matrix.smul_mul]))
    (Subtype.ext (by change Factor.matrix g.2 * (a • v.2.val) * _ = a • _; rw [Matrix.mul_smul, Matrix.smul_mul]))

theorem minimumNormLift_factor_formula (g : Factors right left) (P Z : SMat 𝕂 n) :
    minimumNormLift right left (g • P) Z = generatorAction g (minimumNormLift right left P (g⁻¹ • Z)) := by
  have hcan {A C : SMat 𝕂 n} (hA : GS.KUnitary A) : Aᴴ * (A * C * Aᴴ) * A = C := by
    calc Aᴴ * (A * C * Aᴴ) * A = (Aᴴ * A) * C * (Aᴴ * A) := by simp [Matrix.mul_assoc]
      _ = C := by rw [hA.1]; simp
  have hinv_r (h : Factors right left) (v : PairGenerator right left) :
      generatorAction h (generatorAction h⁻¹ v) = v :=
    Prod.ext (Subtype.ext (by
        change Factor.matrix h.1 * ((Factor.matrix h.1)ᴴ * v.1.val * ((Factor.matrix h.1)ᴴ)ᴴ) * (Factor.matrix h.1)ᴴ = v.1.val
        simpa using hcan (Factor.matrix_unitary h.1).conjTranspose))
      (Subtype.ext (by
        change Factor.matrix h.2 * ((Factor.matrix h.2)ᴴ * v.2.val * ((Factor.matrix h.2)ᴴ)ᴴ) * (Factor.matrix h.2)ᴴ = v.2.val
        simpa using hcan (Factor.matrix_unitary h.2).conjTranspose))
  have hpm (h : Factors right left) (X : SMat 𝕂 n) (v : PairGenerator right left) :
      pointMap right left (h • X) (generatorAction h v) = h • pointMap right left X v := by
    let L := Factor.matrix h.1; let R := Factor.matrix h.2
    have hl : (L * v.1.val * Lᴴ) * (L * X * Rᴴ) = L * (v.1.val * X) * Rᴴ := by
      calc _ = L * v.1.val * (Lᴴ * L) * X * Rᴴ := by simp [Matrix.mul_assoc]
        _ = _ := by rw [(Factor.matrix_unitary h.1).1]; simp [Matrix.mul_assoc]
    have hr : (L * X * Rᴴ) * (R * v.2.val * Rᴴ) = L * (X * v.2.val) * Rᴴ := by
      calc _ = L * X * (Rᴴ * R) * v.2.val * Rᴴ := by simp [Matrix.mul_assoc]
        _ = _ := by rw [(Factor.matrix_unitary h.2).1]; simp [Matrix.mul_assoc]
    change (L * v.1.val * Lᴴ) * (L * X * Rᴴ) + (L * X * Rᴴ) * (R * v.2.val * Rᴴ) = L * (v.1.val * X + X * v.2.val) * Rᴴ
    rw [hl, hr, Matrix.mul_add, Matrix.add_mul]
  symm; refine minimumNormLift_unique (g • P) Z _ ?_ fun k hk => ?_
  · rw [hpm, minimumNormLift_synthesis, ← pointProjection_equivariant, smul_inv_smul]
  · have hb : pointMap right left P (generatorAction g⁻¹ k) = 0 := by
      have he := hpm g⁻¹ (g • P) k; rw [inv_smul_smul, hk] at he; simpa [action_apply] using he
    have hginn (u w : PairGenerator right left) : generatorInner (generatorAction g u) (generatorAction g w) = generatorInner u w := by
      unfold generatorInner; dsimp [generatorAction]
      rw [cFrobInner_right_unitary _ (Factor.matrix_unitary g.1).conjTranspose,
          cFrobInner_right_unitary _ (Factor.matrix_unitary g.2).conjTranspose,
          cFrobInner_left_unitary _ (Factor.matrix_unitary g.1),
          cFrobInner_left_unitary _ (Factor.matrix_unitary g.2)]
    calc generatorInner (generatorAction g (minimumNormLift right left P (g⁻¹ • Z))) k
      _ = generatorInner (generatorAction g (minimumNormLift right left P (g⁻¹ • Z))) (generatorAction g (generatorAction g⁻¹ k)) := by
            rw [hinv_r]
      _ = generatorInner (minimumNormLift right left P (g⁻¹ • Z)) (generatorAction g⁻¹ k) := hginn _ _
      _ = 0 := minimumNormLift_horizontal P (g⁻¹ • Z) _ hb

theorem unitCayley_shared (s : Pattern 𝕂 n) (C : Generator s) :
    KSharedFactor s.size s.label (unitCayley C.val) :=
  cayley_shared s.positive s.divides ((sharedSkewSpace 𝕂 s.size s.label).smul_mem (-1 / 2 : ℝ) C.property)

def generatorCayleyValue (right left : Pattern 𝕂 n)
    (p : SMat 𝕂 n × (PairGenerator right left × ℝ)) : SMat 𝕂 n :=
  unitCayley (p.2.2 • p.2.1.1.val) * p.1 * unitCayley (p.2.2 • p.2.1.2.val)

theorem generatorCayleyValue_smooth (right left : Pattern 𝕂 n) :
    ContDiff ℝ ⊤ (generatorCayleyValue right left) := by
  let E := SMat 𝕂 n × (PairGenerator right left × ℝ)
  have hL : ContDiff ℝ ⊤ (fun p : E => p.2.2 • p.2.1.1.val) :=
    contDiff_snd.snd.smul ((sharedSkewSpace 𝕂 (n := n) left.size left.label).subtypeL.contDiff.comp contDiff_snd.fst.fst)
  have hR : ContDiff ℝ ⊤ (fun p : E => p.2.2 • p.2.1.2.val) :=
    contDiff_snd.snd.smul ((sharedSkewSpace 𝕂 (n := n) right.size right.label).subtypeL.contDiff.comp contDiff_snd.fst.snd)
  exact GS.UnitaryManifold.smooth_matrix_product
    (GS.UnitaryManifold.smooth_matrix_product
      (unitCayley_smooth_comp _ hL fun p => skewHermitian_real_smul p.2.2 p.2.1.1.property.2.1) contDiff_fst)
    (unitCayley_smooth_comp _ hR fun p => skewHermitian_real_smul p.2.2 p.2.1.2.property.2.1)

def sharedCayleyValue (right left : Pattern 𝕂 n) (X Z : SMat 𝕂 n) (t : ℝ) : SMat 𝕂 n :=
  generatorCayleyValue right left (X, (minimumNormLift right left X Z, t))

@[simp] theorem sharedCayleyValue_projected (X Z : SMat 𝕂 n) (t : ℝ) :
    sharedCayleyValue right left X (pointProjection right left X Z) t = sharedCayleyValue right left X Z t := by
  simp [sharedCayleyValue]

@[simp] theorem sharedCayleyValue_zero_time (X Z : SMat 𝕂 n) :
    sharedCayleyValue right left X Z 0 = X := by simp [sharedCayleyValue, generatorCayleyValue]

@[simp] theorem sharedCayleyValue_zero_vector (X : SMat 𝕂 n) (t : ℝ) :
    sharedCayleyValue right left X 0 t = X := by simp [sharedCayleyValue, generatorCayleyValue]

theorem sharedCayleyValue_smul (X Z : SMat 𝕂 n) (a t : ℝ) :
    sharedCayleyValue right left X (a • Z) t = sharedCayleyValue right left X Z (t * a) := by
  unfold sharedCayleyValue; rw [map_smul]
  change unitCayley (t • (a • _)) * X * unitCayley (t • (a • _)) =
    unitCayley ((t * a) • _) * X * unitCayley ((t * a) • _)
  simp [smul_smul]

theorem sharedCayleyValue_mem_orbit (P : SMat 𝕂 n) (X : MatrixOrbit right left P)
    (Z : SMat 𝕂 n) (t : ℝ) :
    sharedCayleyValue right left X.val Z t ∈ MulAction.orbit (Factors right left) P := by
  obtain ⟨g, hg⟩ := X.property
  let v := minimumNormLift right left X.val Z
  let act : Factors right left :=
    (Factor.ofMatrix (unitCayley (t • v.1.val)) (unitCayley_shared left (t • v.1)),
     Factor.ofMatrix ((unitCayley (t • v.2.val))ᴴ) (shared_factor_conjTranspose (unitCayley_shared right (t • v.2))))
  refine ⟨act * g, ?_⟩
  change (act * g) • P = _; rw [mul_smul, show g • P = X.val from hg]
  change unitCayley (t • v.1.val) * X.val * ((unitCayley (t • v.2.val))ᴴ)ᴴ = _
  rw [Matrix.conjTranspose_conjTranspose]; rfl

theorem sharedCayleyValue_derivative (X Z : SMat 𝕂 n) :
    HasDerivAt (sharedCayleyValue right left X Z) (pointProjection right left X Z) 0 := by
  let v := minimumNormLift right left X Z
  have hd := GS.UnitaryManifold.hasDerivAt_matrix_mul
    (GS.UnitaryManifold.hasDerivAt_matrix_mul (unitCayley_line_derivative v.1.val v.1.property.2.1)
      (hasDerivAt_const (0 : ℝ) X))
    (unitCayley_line_derivative v.2.val v.2.property.2.1)
  have hv : v.1.val * X + X * v.2.val = pointProjection right left X Z :=
    minimumNormLift_synthesis X Z
  unfold sharedCayleyValue generatorCayleyValue
  simpa only [zero_smul, unitCayley_zero, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, add_zero, hv] using hd

theorem sharedCayleyValue_fixed_smooth (X : SMat 𝕂 n) :
    ContDiff ℝ ⊤ (fun p : SMat 𝕂 n × ℝ => sharedCayleyValue right left X p.1 p.2) :=
  (generatorCayleyValue_smooth right left).comp
    (contDiff_const.prodMk (((minimumNormLift right left X).contDiff.comp contDiff_fst).prodMk contDiff_snd))

end LiftAndCayley

def dualMatrixCLM (𝕂 : Type) [RCLike 𝕂] (n : ℕ) : (SMat 𝕂 n →L[ℝ] ℝ) →L[ℝ] SMat 𝕂 n :=
  ({ toFun := dualMatrix
     map_add' := fun D E => by
       have h : frobDual (dualMatrix D + dualMatrix E) = D + E := by
         ext A; rw [frobDual_apply, cFrobInner_add_left, ← functional_eq_cFrobInner, ← functional_eq_cFrobInner]; rfl
       rw [← h, dualMatrix_frobDual]
     map_smul' := fun a D => by
       have h : frobDual (a • dualMatrix D) = a • D := by
         ext A; rw [frobDual_apply, cFrobInner_real_smul_left, ← functional_eq_cFrobInner]; rfl
       rw [← h, dualMatrix_frobDual]; rfl
   } : (SMat 𝕂 n →L[ℝ] ℝ) →ₗ[ℝ] SMat 𝕂 n).toContinuousLinearMap

theorem ambientGradient_contDiff_of_loss (f : SMat 𝕂 n → ℝ) {r s : WithTop ℕ∞}
    (hf : ContDiff ℝ s f) (hrs : r + 1 ≤ s) : ContDiff ℝ r (ambientGradient f) := by
  change ContDiff ℝ r ((dualMatrixCLM 𝕂 n) ∘ fderiv ℝ f)
  exact (dualMatrixCLM 𝕂 n).contDiff.comp (hf.fderiv_right hrs)

section SmoothLiftAndProjection
variable (right left : Pattern 𝕂 n) (P : SMat 𝕂 n)
local instance smoothLiftNormedSpace : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
local instance smoothLiftChartedSpace : ChartedSpace (HorizontalModel right left P) (MatrixOrbit right left P) :=
  sharedOrbitChartedSpace right left P

def transportedMinimumNormLift (p : SMat 𝕂 n × (SMat 𝕂 n × SMat 𝕂 n)) : PairGenerator right left :=
  let v := minimumNormLift right left P (p.1ᴴ * p.2.2 * p.2.1)
  (modelProjection left (p.1 * v.1.val * p.1ᴴ), modelProjection right (p.2.1 * v.2.val * p.2.1ᴴ))

def localMinimumNormLift (g : Factors right left) (q : SMat 𝕂 n × SMat 𝕂 n) : PairGenerator right left :=
  let f := localFactors right left P g q.1
  transportedMinimumNormLift right left P (Factor.matrix f.1, (Factor.matrix f.2, q.2))

theorem transportedMinimumNormLift_smooth : ContDiff ℝ ⊤ (transportedMinimumNormLift right left P) := by
  refine contDiff_iff_contDiffAt.mpr fun p => ?_
  have hL : ContDiffAt ℝ ⊤ (fun q : SMat 𝕂 n × (SMat 𝕂 n × SMat 𝕂 n) => q.1) p := contDiffAt_fst
  have hR : ContDiffAt ℝ ⊤ (fun q : SMat 𝕂 n × (SMat 𝕂 n × SMat 𝕂 n) => q.2.1) p := contDiffAt_snd.fst
  have hZ : ContDiffAt ℝ ⊤ (fun q : SMat 𝕂 n × (SMat 𝕂 n × SMat 𝕂 n) => q.2.2) p := contDiffAt_snd.snd
  have hv := (minimumNormLift right left P).contDiff.contDiffAt.comp p
    (smooth_mul_at (smooth_mul_at (smooth_conjTranspose_at hL) hZ) hR)
  have hvL := (sharedSkewSpace 𝕂 (n := n) left.size left.label).subtypeL.contDiff.contDiffAt.comp p hv.fst
  have hvR := (sharedSkewSpace 𝕂 (n := n) right.size right.label).subtypeL.contDiff.contDiffAt.comp p hv.snd
  exact ((modelProjection left).contDiff.contDiffAt.comp p
    (smooth_mul_at (smooth_mul_at hL hvL) (smooth_conjTranspose_at hL))).prodMk
    ((modelProjection right).contDiff.contDiffAt.comp p
      (smooth_mul_at (smooth_mul_at hR hvR) (smooth_conjTranspose_at hR)))

theorem transportedMinimumNormLift_on_factors (g : Factors right left) (Z : SMat 𝕂 n) :
    transportedMinimumNormLift right left P (Factor.matrix g.1, (Factor.matrix g.2, Z)) =
      minimumNormLift right left (g • P) Z := by
  rw [minimumNormLift_factor_formula]
  have he : g⁻¹ • Z = (Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2 := by
    change (Factor.matrix g.1)ᴴ * Z * ((Factor.matrix g.2)ᴴ)ᴴ = _; rw [Matrix.conjTranspose_conjTranspose]
  rw [he]
  apply Prod.ext
  · exact modelProjection_inclusion (generatorAction g
      (minimumNormLift right left P ((Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2))).1
  · exact modelProjection_inclusion (generatorAction g
      (minimumNormLift right left P ((Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2))).2

theorem localMinimumNormLift_eq (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source) (Z : SMat 𝕂 n) :
    localMinimumNormLift right left P g (X.val, Z) = minimumNormLift right left X.val Z := by
  have he : localFactors right left P g X.val • P = X.val :=
    congrArg Subtype.val (localFactors_right_inverse right left P g X hX)
  change transportedMinimumNormLift right left P _ = _
  rw [transportedMinimumNormLift_on_factors, he]

section IrredProjSmooth
attribute [local irreducible] sharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

theorem minimumNormLift_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, SMat 𝕂 n)))
      (𝓘(ℝ, PairGenerator right left)) ⊤
      (fun p : MatrixOrbit right left P × SMat 𝕂 n => minimumNormLift right left p.1.val p.2) := by
  intro p
  let g := preferredFactor P p.1
  have h₀ : p.1 ∈ (translatedOrbitSlice right left P g).source := by
    simpa only [g, preferredFactor_spec] using translatedOrbitSlice_centre_mem right left P g
  have hloc_sm : ContDiffAt ℝ ⊤ (localMinimumNormLift right left P g) (p.1.val, p.2) :=
    (transportedMinimumNormLift_smooth right left P).contDiffAt.comp (p.1.val, p.2) <|
      ((localFactors_left_matrix_smooth_at right left P g p.1 h₀).comp (p.1.val, p.2) contDiffAt_fst).prodMk
        (((localFactors_right_matrix_smooth_at right left P g p.1 h₀).comp (p.1.val, p.2) contDiffAt_fst).prodMk
          contDiffAt_snd)
  have hinc : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, SMat 𝕂 n)))
      (𝓘(ℝ, SMat 𝕂 n × SMat 𝕂 n)) ⊤ (fun q : MatrixOrbit right left P × SMat 𝕂 n => (q.1.val, q.2)) :=
    ((sharedOrbit_val_contMDiff right left P).comp contMDiff_fst).prodMk_space contMDiff_snd
  refine (ContDiffAt.comp_contMDiffAt
    (f := fun q : MatrixOrbit right left P × SMat 𝕂 n => (q.1.val, q.2))
    (g := localMinimumNormLift right left P g) hloc_sm (hinc p)).congr_of_eventuallyEq ?_
  filter_upwards [(continuous_fst.continuousAt).eventually
    ((translatedOrbitSlice right left P g).open_source.mem_nhds h₀)] with q hq
  exact (localMinimumNormLift_eq right left P g q.1 hq q.2).symm

theorem pointProjection_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, SMat 𝕂 n)))
      (𝓘(ℝ, SMat 𝕂 n)) ⊤
      (fun p : MatrixOrbit right left P × SMat 𝕂 n => pointProjection right left p.1.val p.2) := by
  have he : (fun p : MatrixOrbit right left P × SMat 𝕂 n => pointProjection right left p.1.val p.2) =
      fun p => (minimumNormLift right left p.1.val p.2).1.val * p.1.val +
        p.1.val * (minimumNormLift right left p.1.val p.2).2.val :=
    funext fun p => (minimumNormLift_synthesis p.1.val p.2).symm
  rw [he]
  let IP := (𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, SMat 𝕂 n))
  have hX : ContMDiff IP (𝓘(ℝ, SMat 𝕂 n)) ⊤ (fun p : MatrixOrbit right left P × SMat 𝕂 n => p.1.val) :=
    (sharedOrbit_val_contMDiff right left P).comp contMDiff_fst
  have hL := ((sharedSkewSpace 𝕂 (n := n) left.size left.label).subtypeL.contDiff.comp
    (contDiff_fst (E := Generator left) (F := Generator right))).comp_contMDiff (minimumNormLift_contMDiff right left P)
  have hR := ((sharedSkewSpace 𝕂 (n := n) right.size right.label).subtypeL.contDiff.comp
    (contDiff_snd (E := Generator left) (F := Generator right))).comp_contMDiff (minimumNormLift_contMDiff right left P)
  have hm {a b : MatrixOrbit right left P × SMat 𝕂 n → SMat 𝕂 n}
      (ha : ContMDiff IP (𝓘(ℝ, SMat 𝕂 n)) ⊤ a) (hb : ContMDiff IP (𝓘(ℝ, SMat 𝕂 n)) ⊤ b) :
      ContMDiff IP (𝓘(ℝ, SMat 𝕂 n)) ⊤ (fun p => a p * b p) :=
    (GS.UnitaryManifold.smooth_matrix_product (𝕂 := 𝕂) contDiff_fst contDiff_snd).comp_contMDiff
      (ha.prodMk_space hb)
  exact (hm hL hX).add (hm hX hR)

theorem sharedCayleyValue_contMDiff :
    ContMDiff (((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, SMat 𝕂 n))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, SMat 𝕂 n)) ⊤
      (fun p : (MatrixOrbit right left P × SMat 𝕂 n) × ℝ => sharedCayleyValue right left p.1.1.val p.1.2 p.2) :=
  (generatorCayleyValue_smooth right left).comp_contMDiff <|
    ((sharedOrbit_val_contMDiff right left P).comp (contMDiff_fst.comp contMDiff_fst)).prodMk_space
      (((minimumNormLift_contMDiff right left P).comp contMDiff_fst).prodMk_space contMDiff_snd)

end IrredProjSmooth

end SmoothLiftAndProjection

section ManifoldGeometry
variable (right left : Pattern 𝕂 n) (P : SMat 𝕂 n)
local instance geomNormedSpace : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
local instance geomChartedSpace : ChartedSpace (HorizontalModel right left P) (MatrixOrbit right left P) :=
  sharedOrbitChartedSpace right left P
local instance geomIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤ (MatrixOrbit right left P) :=
  sharedOrbitIsManifold right left P

def inclusionDifferential (X : MatrixOrbit right left P) :
    TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X →L[ℝ] SMat 𝕂 n :=
  mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, SMat 𝕂 n)) (fun Y : MatrixOrbit right left P => Y.val) X

theorem inclusionDifferential_injective (X : MatrixOrbit right left P) :
    Function.Injective (inclusionDifferential right left P X) :=
  sharedOrbit_val_mfderiv_injective right left P X

def tangentProjection (X : MatrixOrbit right left P) (Z : SMat 𝕂 n) :
    TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X :=
  Classical.choose (pointProjection_unique_tangent_lift right left P X Z)

@[simp] theorem inclusion_tangentProjection (X : MatrixOrbit right left P) (Z : SMat 𝕂 n) :
    inclusionDifferential right left P X (tangentProjection right left P X Z) =
      pointProjection right left X.val Z :=
  (Classical.choose_spec (pointProjection_unique_tangent_lift right left P X Z)).1

def tangentProjectionCLM (X : MatrixOrbit right left P) :
    SMat 𝕂 n →L[ℝ] HorizontalModel right left P :=
  ({ toFun := tangentProjection right left P X
     map_add' := fun Z W => inclusionDifferential_injective right left P X <| by
       simp [map_add, inclusion_tangentProjection]
     map_smul' := fun a Z => inclusionDifferential_injective right left P X <| by
       simp [map_smul, inclusion_tangentProjection]
   } : SMat 𝕂 n →ₗ[ℝ] HorizontalModel right left P).toContinuousLinearMap

def intrinsicGradient (f : SMat 𝕂 n → ℝ) (X : MatrixOrbit right left P) :
    TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X :=
  tangentProjection right left P X (ambientGradient f X.val)

theorem intrinsicGradient_characterization (f : SMat 𝕂 n → ℝ)
    (X : MatrixOrbit right left P) (hf : DifferentiableAt ℝ f X.val)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    cFrobInner (inclusionDifferential right left P X (intrinsicGradient right left P f X))
      (inclusionDifferential right left P X v) =
    mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, ℝ)) (fun Y : MatrixOrbit right left P => f Y.val) X v := by
  have hi : MDifferentiableAt (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, SMat 𝕂 n))
      (fun Y : MatrixOrbit right left P => Y.val) X :=
    ((sharedOrbit_val_contMDiff right left P) X).mdifferentiableAt (by simp)
  have hh : mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, ℝ))
      (fun Y : MatrixOrbit right left P => f Y.val) X =
      (fderiv ℝ f X.val).comp (inclusionDifferential right left P X) := by
    have h0 := mfderiv_comp X hf.mdifferentiableAt hi
    rw [mfderiv_eq_fderiv] at h0
    convert h0 using 1 <;> first | rfl | (ext w <;> rfl)
  rw [hh]
  change cFrobInner (inclusionDifferential right left P X (tangentProjection right left P X _)) _ =
    fderiv ℝ f X.val (inclusionDifferential right left P X v)
  have hfix : pointProjection right left X.val (inclusionDifferential right left P X v) =
      inclusionDifferential right left P X v :=
    (pointProjection_fixed_iff_tangent_image right left P X _).mpr ⟨v, rfl⟩
  rw [ambientGradient_represents, inclusion_tangentProjection, pointProjection_self_adjoint, hfix]

section BundleIrred
attribute [local irreducible] sharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

def tangentAmbient
    (p : TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P)) : SMat 𝕂 n :=
  inclusionDifferential right left P p.proj p.2

theorem tangentAmbient_contMDiff :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)).tangent (𝓘(ℝ, SMat 𝕂 n)) ⊤ (tangentAmbient right left P) :=
  (contMDiff_snd_tangentBundle_modelSpace (SMat 𝕂 n) (𝓘(ℝ, SMat 𝕂 n))).comp
    ((sharedOrbit_val_contMDiff right left P).contMDiff_tangentMap (by simp))

def cayleyFibreRetraction (X : MatrixOrbit right left P)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) : MatrixOrbit right left P :=
  ⟨sharedCayleyValue right left X.val (inclusionDifferential right left P X v) 1,
    sharedCayleyValue_mem_orbit P X (inclusionDifferential right left P X v) 1⟩

@[simp] theorem cayleyFibreRetraction_zero (X : MatrixOrbit right left P) :
    cayleyFibreRetraction right left P X 0 = X := by
  apply Subtype.ext; simp [cayleyFibreRetraction]

theorem cayleyFibreRetraction_contMDiff (X : MatrixOrbit right left P) :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P)) ⊤
      (fun v : HorizontalModel right left P => cayleyFibreRetraction right left P X v) := by
  apply (sharedOrbit_contMDiff_iff_contDiff right left P
    (fun v : HorizontalModel right left P => cayleyFibreRetraction right left P X v)).mpr
  let D : HorizontalModel right left P →L[ℝ] SMat 𝕂 n := inclusionDifferential right left P X
  exact (sharedCayleyValue_fixed_smooth (right := right) (left := left) X.val).comp
    (f := fun v : HorizontalModel right left P => (D v, (1 : ℝ)))
    (D.contDiff.prodMk contDiff_const)

theorem cayleyFibreRetraction_mfderiv_zero (X : MatrixOrbit right left P) :
    mfderiv (M := HorizontalModel right left P) (M' := MatrixOrbit right left P)
      (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P))
      (fun v : HorizontalModel right left P => cayleyFibreRetraction right left P X v)
      (0 : HorizontalModel right left P) = ContinuousLinearMap.id ℝ (HorizontalModel right left P) := by
  refine ContinuousLinearMap.ext fun (v : HorizontalModel right left P) => ?_
  apply inclusionDifferential_injective right left P X
  have hd : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hlineD : @Eq (HorizontalModel right left P)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left P)) (fun t : ℝ => t • v) 0 (1 : ℝ)) v := by
    rw [mfderiv_eq_fderiv]; exact hd.deriv
  have hf := (cayleyFibreRetraction_contMDiff right left P X).mdifferentiable (by simp)
  have hi := (sharedOrbit_val_contMDiff right left P).mdifferentiable (by simp)
  have hstep : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left P)) ⊤
      (fun t : ℝ => cayleyFibreRetraction right left P X (t • v)) :=
    ContMDiff.comp (g := fun w : HorizontalModel right left P => cayleyFibreRetraction right left P X w)
      (f := fun t : ℝ => t • v) (cayleyFibreRetraction_contMDiff right left P X)
      (contDiff_id.smul_const v).contMDiff
  have hc1 := mfderiv_comp_apply_of_eq (0 : ℝ) (hf 0) hd.differentiableAt.mdifferentiableAt (zero_smul ℝ v) (1 : ℝ)
  rw [hlineD] at hc1
  have hc2 := mfderiv_comp_apply_of_eq (0 : ℝ) (hi X) (hstep.mdifferentiable (by simp) 0)
    (by simp [cayleyFibreRetraction_zero]) (1 : ℝ)
  have hval : (fun t : ℝ => (cayleyFibreRetraction right left P X (t • v)).val) =
      sharedCayleyValue right left X.val (inclusionDifferential right left P X v) := by
    funext t; change sharedCayleyValue right left X.val (inclusionDifferential right left P X (t • v)) 1 = _
    rw [map_smul, sharedCayleyValue_smul, one_mul]
  have hm0 : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, SMat 𝕂 n))
      (sharedCayleyValue right left X.val (inclusionDifferential right left P X v)) 0 (1 : ℝ) =
      inclusionDifferential right left P X v := by
    rw [mfderiv_eq_fderiv]
    exact (sharedCayleyValue_derivative X.val (inclusionDifferential right left P X v)).deriv.trans
      ((pointProjection_fixed_iff_tangent_image right left P X _).mpr ⟨v, rfl⟩)
  have hm := (congrArg (fun c : ℝ → SMat 𝕂 n => mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, SMat 𝕂 n)) c 0 (1 : ℝ)) hval).trans hm0
  exact (congrArg (inclusionDifferential right left P X) hc1).symm.trans (hc2.symm.trans hm)

def cayleyRetraction
    (p : TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P)) :
    MatrixOrbit right left P := cayleyFibreRetraction right left P p.proj p.2

theorem cayleyRetraction_contMDiff :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)).tangent
      (𝓘(ℝ, HorizontalModel right left P)) ⊤ (cayleyRetraction right left P) := by
  have ha := (sharedCayleyValue_contMDiff right left P).comp <|
    ((Bundle.contMDiff_proj (TangentSpace (𝓘(ℝ, HorizontalModel right left P)))).prodMk
      (tangentAmbient_contMDiff right left P)).prodMk (contMDiff_const (c := (1 : ℝ)))
  exact (sharedOrbit_contMDiff_iff_ambient right left P
    (𝓘(ℝ, HorizontalModel right left P)).tangent (cayleyRetraction right left P)).mpr ha

@[simp] theorem cayleyRetraction_zero_section (X : MatrixOrbit right left P) :
    cayleyRetraction right left P ⟨X, 0⟩ = X := cayleyFibreRetraction_zero right left P X

theorem cayleyRetraction_fibre_mfderiv_zero (X : MatrixOrbit right left P) :
    mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P))
      (fun v : HorizontalModel right left P => cayleyRetraction right left P ⟨X, v⟩)
      (0 : HorizontalModel right left P) = ContinuousLinearMap.id ℝ (HorizontalModel right left P) :=
  cayleyFibreRetraction_mfderiv_zero right left P X

def ambientRetraction (p : MatrixOrbit right left P × SMat 𝕂 n) : MatrixOrbit right left P :=
  cayleyFibreRetraction right left P p.1 (tangentProjection right left P p.1 p.2)

theorem ambientRetraction_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, SMat 𝕂 n)))
      (𝓘(ℝ, HorizontalModel right left P)) ⊤ (ambientRetraction right left P) := by
  apply (sharedOrbit_contMDiff_iff_ambient right left P _ (ambientRetraction right left P)).mpr
  have he : (fun p : MatrixOrbit right left P × SMat 𝕂 n => (ambientRetraction right left P p).val) =
      fun p => sharedCayleyValue right left p.1.val p.2 1 := by
    funext ⟨X, Z⟩
    change sharedCayleyValue right left X.val (inclusionDifferential right left P X (tangentProjection right left P X Z)) 1 = _
    rw [inclusion_tangentProjection]; exact sharedCayleyValue_projected X.val Z 1
  rw [he]
  exact (generatorCayleyValue_smooth right left).comp_contMDiff <|
    ((sharedOrbit_val_contMDiff right left P).comp contMDiff_fst).prodMk_space
      ((minimumNormLift_contMDiff right left P).prodMk_space (contMDiff_const (c := (1 : ℝ))))

def tangentProjectionBundle (p : MatrixOrbit right left P × SMat 𝕂 n) :
    TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P) :=
  ⟨p.1, tangentProjection right left P p.1 p.2⟩

theorem tangentProjectionBundle_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, SMat 𝕂 n)))
      (𝓘(ℝ, HorizontalModel right left P)).tangent ⊤ (tangentProjectionBundle right left P) := by
  let vin (p : MatrixOrbit right left P × SMat 𝕂 n) :
      TangentBundle ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, SMat 𝕂 n)))
        (MatrixOrbit right left P × SMat 𝕂 n) := ⟨(p.1, 0), (0, p.2)⟩
  have he : tangentProjectionBundle right left P =
      tangentMap ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, SMat 𝕂 n)))
        (𝓘(ℝ, HorizontalModel right left P)) (ambientRetraction right left P) ∘ vin := by
    funext ⟨X, Z⟩
    have hp := GS.Extensions.mfderiv_retraction_precompose_linear
      (𝓘(ℝ, HorizontalModel right left P)) (cayleyFibreRetraction right left P X)
      (tangentProjectionCLM right left P X)
      ((cayleyFibreRetraction_contMDiff right left P X).mdifferentiable (by simp) 0)
      (cayleyFibreRetraction_mfderiv_zero right left P X) Z
    have hv := (GS.Extensions.mfderiv_partial_right (𝓘(ℝ, HorizontalModel right left P))
      (ambientRetraction right left P) X
      ((ambientRetraction_contMDiff right left P).mdifferentiable (by simp) (X, 0)) Z).symm.trans hp
    simp only [Function.comp_apply, tangentProjectionBundle, vin, tangentMap, hv]
    congr 1; simp [ambientRetraction, show tangentProjection right left P X 0 = 0 from map_zero (tangentProjectionCLM right left P X)]
  rw [he]
  exact ((ambientRetraction_contMDiff right left P).contMDiff_tangentMap (by simp)).comp
    (GS.Extensions.contMDiff_vertical_input (M := MatrixOrbit right left P) (V := SMat 𝕂 n)
      (𝓘(ℝ, HorizontalModel right left P)))

theorem intrinsicGradientSection_smooth (f : SMat 𝕂 n → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P)).tangent ∞
      (fun X : MatrixOrbit right left P => (⟨X, intrinsicGradient right left P f X⟩ :
        TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P))) :=
  ((tangentProjectionBundle_contMDiff right left P).of_le le_top).comp <|
    contMDiff_id.prodMk ((ambientGradient_contDiff_of_loss f hf (r := ∞) (by simp)).comp_contMDiff
      ((sharedOrbit_val_contMDiff right left P).of_le le_top))

end BundleIrred
end ManifoldGeometry

end GS.UnitarySharing
