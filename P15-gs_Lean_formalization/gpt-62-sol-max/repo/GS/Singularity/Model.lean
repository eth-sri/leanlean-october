module

public import GS.Singularity.Anchors
public import GS.Singularity.Axis
public import Mathlib.Tactic.Module
public import GS.CompactFibres
public import GS.NonmanifoldFinal.EuclideanTransport

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Matrix Set Filter GS.NonmanifoldCompletion GS.NonmanifoldFinal
open scoped Topology ComplexOrder
namespace GS.Shared.Singularity
variable {𝕜 : Type*} [RCLike 𝕜] {q d : ℕ} {Q : FullU 𝕜 q} {o : Fin q}

abbrev Cone (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) := RankOne (Module.finrank ℝ 𝕜) (Fin d)
abbrev Box (𝕜 : Type*) [RCLike 𝕜] {q : ℕ} (o : Fin q) (d : ℕ) (r : ℝ) :=
  Outer 𝕜 q o × (Fin 2 → CBall d r) × FullU 𝕜 2

instance boxCompactSpace (o : Fin q) (d : ℕ) (r : ℝ) : CompactSpace (Box 𝕜 o d r) := by
  let : CompactSpace (CBall d r) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  infer_instance

def boxFrame (C : SliceChart Q o d) (p : Box 𝕜 o d C.radius) : Frame 𝕜 o :=
  (p.1, fun a => C.valueFactor (p.2.1 a), p.2.2)

abbrev localMiddle (C : SliceChart Q o d) (p : Box 𝕜 o d C.radius) := frameMiddle (boxFrame C p)

def familyMap (p : Parameters 𝕜 q) : shuffleFamily 𝕜 q :=
  ⟨flattenBlocks (blockImage p), by simp [shuffleFamily_eq_range]⟩

def familyCenter (Q : FullU 𝕜 q) : shuffleFamily 𝕜 q := familyMap (1,fun _ => Q,1)

@[simp] theorem familyCenter_val (Q : FullU 𝕜 q) :
    (familyCenter Q).val = flattenBlocks (baseBlocks (Factor.matrix Q)) := by
  change flattenBlocks (blockImage (1,fun _ => Q,1)) = _
  apply congrArg flattenBlocks
  funext i j
  simp [blockImage, baseBlocks, ← diagTwo_eta]

theorem familyMap_eq_iff (p p' : Parameters 𝕜 q) : familyMap p = familyMap p' ↔ blockImage p = blockImage p' :=
  Subtype.ext_iff.trans (blockFlatten (pairIndex q)).injective.eq_iff

theorem familyMap_continuous : Continuous (@familyMap 𝕜 _ q) :=
  (continuous_flattenBlocks.comp blockImage_continuous).subtype_mk _

def localF (C : SliceChart Q o d) : Box 𝕜 o d C.radius → shuffleFamily 𝕜 q :=
  familyMap ∘ frameParams ∘ boxFrame C

def normalizedMap (Q : FullU 𝕜 q) (o : Fin q) : Normalized (Factor.matrix Q) o → shuffleFamily 𝕜 q :=
  familyMap ∘ frameParams ∘ Subtype.val

theorem normalizedMap_continuous : Continuous (normalizedMap Q o) :=
  familyMap_continuous.comp (frameParams_continuous.comp continuous_subtype_val)

theorem normalizedMap_surjective : Function.Surjective (normalizedMap Q o) := by
  rintro ⟨A,hA⟩
  rw [shuffleFamily_eq_range] at hA
  obtain ⟨p,hp⟩ := hA
  obtain ⟨f,hf⟩ := normalized_representation (Factor.matrix Q) o p
  exact ⟨f, Subtype.ext ((congrArg flattenBlocks hf).trans hp)⟩

def localG {r : ℝ} (p : Box 𝕜 o d r) : Outer 𝕜 q o × Coordinate d × Cone 𝕜 d :=
  (p.1, mid ℝ (p.2.1 0).val (p.2.1 1).val,
    ⟨vecMulVec (frameCoords (Factor.matrix p.2.2)) (halfDiff ℝ (p.2.1 0).val (p.2.1 1).val).ofLp, rank_vecMulVec_le _ _⟩)

attribute [local fun_prop] Factor.continuous_matrix

theorem localF_continuous (C : SliceChart Q o d) : Continuous (localF C) := by
  apply familyMap_continuous.comp (frameParams_continuous.comp ?_)
  have h := C.continuous_factor
  unfold boxFrame
  fun_prop

theorem localG_continuous {r : ℝ} : Continuous (@localG 𝕜 _ q d o r) := by
  unfold localG mid halfDiff frameCoords frameAxis
  fun_prop

theorem localMiddle_rel (C : SliceChart Q o d) (x y x' y' : CBall d C.radius)
    (u v : Axis 𝕜) (hu : ∑ i, u i ^ 2 = 1) (hv : ∑ i, v i ^ 2 = 1) :
    (∀ i j, middle (C.value x i j) (C.value y i j) u =
      middle (C.value x' i j) (C.value y' i j) v) ↔ PairFibre x.val y.val x'.val y'.val u v := by
  let f (t : CBall d C.radius) (k : Fin q × Fin q) := C.value t k.1 k.2
  have hf : Function.Injective f := fun _ _ h => C.value_injective (Matrix.ext fun i j => congrFun h (i,j))
  have he := middle_fibres (a := f x) (b := f y) (c := f x') (d := f y') hu hv
  refine Iff.trans ⟨fun h (k : Fin q × Fin q) => h k.1 k.2, fun h i j => h (i,j)⟩ (he.trans ?_)
  simp only [PairFibre, hf.eq_iff, Subtype.ext_iff]

/-- The compact matrix parametrization and the rank-cone coordinates have exactly the same fibres. -/
theorem local_same_fibres (C : SliceChart Q o d) (p p' : Box 𝕜 o d C.radius) :
    localF C p = localF C p' ↔ localG p = localG p' := by
  have pos (a : Box 𝕜 o d C.radius) : MiddlePositive (Factor.matrix Q) o (localMiddle C a) := by
    intro k
    unfold localMiddle frameMiddle
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
    exact (Matrix.PosDef.diagonal fun j => by simpa [boxFrame, div_eq_inv_mul] using C.positive_factor (a.2.1 j) k)
      |>.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit (Factor.matrix_unitary _).isUnit)
  have hm (a : Box 𝕜 o d C.radius) (i j : Fin q) : localMiddle C a i j =
      middle (C.value (a.2.1 0) i j) (C.value (a.2.1 1) i j) (frameCoords (Factor.matrix a.2.2)) := by
    have hS := Factor.matrix_unitary a.2.2
    rw [middle_conj hS (pauli_frameCoords hS), diagTwo_eta (fun b => C.value (a.2.1 b) i j)]
    rfl
  have h₁ := frameCoords_unit (Factor.matrix_unitary p.2.2)
  have h₂ := frameCoords_unit (Factor.matrix_unitary p'.2.2)
  have rel := localMiddle_rel C (p.2.1 0) (p.2.1 1) (p'.2.1 0) (p'.2.1 1) _ _ h₁ h₂
  simp_rw [← hm] at rel
  replace rel := Matrix.ext_iff.symm.trans rel
  rw [pairFibre_iff_mid (K := ℝ)] at rel
  simp only [localF, Function.comp_apply, familyMap_eq_iff, frameImage, localG,
    Prod.mk.injEq, Subtype.mk.injEq, real_outer_fibres h₁ h₂]
  have he (a b : Coordinate d) : a.ofLp = b.ofLp ↔ a = b := (WithLp.equiv 2 _).injective.eq_iff
  simp only [SignedFibre, ← show (0 : Coordinate d).ofLp = 0 from rfl,
    ← show ∀ x : Coordinate d, (-x).ofLp = -x.ofLp from fun _ => rfl, he]
  simp only [SignedFibre] at rel
  rw [← rel]
  exact ⟨normalized_fibres (pos p) (fun k => (pos p' k).posSemidef),
    fun ⟨ha,hn⟩ => congrArg₂ outerSandwich ha hn⟩


/-- Compactness is applied to the closed, nonnegative slice rather than
requiring a continuous phase choice on the entire factor space. -/
theorem eventually_localF (C : SliceChart Q o d) {p : Normalized (Factor.matrix Q) o}
    (hp : blockImage (frameParams p.val) = baseBlocks (Factor.matrix Q)) :
    ∀ᶠ p' in 𝓝 p, normalizedMap Q o p' ∈ range (localF C) := by
  have hb : ∀ᶠ A in 𝓝 Q, NonnegativeAnchors (Factor.matrix Q) o (Factor.matrix A) → A ∈ range C.valueFactor := by
    have ho : IsOpen {A : FullU 𝕜 q | AnchorsNonzero (Factor.matrix A) o} :=
      isOpen_onAnchors o fun _ _ => isOpen_ne_fun (Factor.continuous_matrix.matrix_elem _ _) continuous_const
    filter_upwards [C.nearby,ho.mem_nhds C.anchors] with A hA hn h
    exact hA (h.positive C.anchors hn)
  have h (a : Fin 2) : ∀ᶠ p' in 𝓝 p, p'.val.2.1 a ∈ range C.valueFactor := by
    have hc : Continuous (fun p' : Normalized (Factor.matrix Q) o => p'.val.2.1 a) := by fun_prop
    have ht := hc.continuousAt (x := p)
    rw [ContinuousAt, normalized_base_middle C.anchors hp a] at ht
    exact (ht.eventually hb).mono fun p' hp' => hp' (p'.property a)
  filter_upwards [eventually_all.mpr h] with p' hp'
  choose u hu using hp'
  refine ⟨(p'.val.1,u,p'.val.2.2),?_⟩
  simp [localF, normalizedMap, boxFrame, funext hu]

open scoped Matrix.Norms.Frobenius in
/-- The outer-product coordinates contain a neighbourhood of the cone vertex. -/
theorem localG_nhds (g : Outer 𝕜 q o) {r : ℝ} (hr : 0 < r) :
    range (@localG 𝕜 _ q d o r) ∈ 𝓝 (g, 0, (rankZero : Cone 𝕜 d)) := by
  let X := Outer 𝕜 q o × Coordinate d × Cone 𝕜 d
  have h : IsOpen {p : X | ‖p.2.1‖ + ‖p.2.2.val‖ < r} := isOpen_lt (by fun_prop) continuous_const
  filter_upwards [h.mem_nhds (x := (g,0,rankZero)) (by
    change ‖(0 : Coordinate d)‖ + ‖(0 : Matrix (Fin (Module.finrank ℝ 𝕜+1)) (Fin d) ℝ)‖ < r
    simpa)]
    with ⟨a,x,W⟩ hW
  change ‖x‖ + ‖W.val‖ < r at hW
  obtain ⟨u,hu,z,he⟩ := rank_one_normalized W.val W.property
  let v : Coordinate d := WithLp.toLp 2 z
  have hv : ‖v‖ = ‖W.val‖ := by
    rw [← he, Matrix.frobenius_norm_def, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]
    simp only [vecMulVec_apply, Real.rpow_two, Real.norm_eq_abs, abs_mul, mul_pow, sq_abs,
      ← Finset.mul_sum, ← Finset.sum_mul, hu, one_mul]
    rfl
  have hz : ‖x‖ + ‖v‖ ≤ r := hv.symm ▸ hW.le
  have hp : x+v ∈ CBall d r := by simpa [Metric.mem_closedBall] using (norm_add_le x v).trans hz
  have hm : x-v ∈ CBall d r := by simpa [Metric.mem_closedBall] using (norm_sub_le x v).trans hz
  obtain ⟨S,hS⟩ := exists_frameCoords u hu
  refine ⟨(a,![⟨x+v,hp⟩,⟨x-v,hm⟩],S), ?_⟩
  refine congrArg (a, ·) (Prod.ext (mid_add_sub _ _) (Subtype.ext ?_))
  change vecMulVec (frameCoords (Factor.matrix S)) (halfDiff ℝ (x+v) (x-v)).ofLp = W.val
  rwa [hS, halfDiff_add_sub]


/-- The full shuffle image near `Q ⊗ I₂` is modeled by a smooth outer group,
 an unconstrained middle coordinate, and the appropriate rank-one cone. -/
theorem neighbourhood_model (C : SliceChart Q o d) :
    Nonempty (PointedNeighbourhoodModel (shuffleFamily 𝕜 q) (Outer 𝕜 q o × Coordinate d × Cone 𝕜 d)
      (familyCenter Q) (1,0,rankZero)) := by
  let F := localF C
  let G := @localG 𝕜 _ q d o C.radius
  obtain ⟨h,hh⟩ := exists_homeomorph_ranges_of_same_fibres F G
    (localF_continuous C) localG_continuous (local_same_fibres C)
  refine ⟨⟨range F,range G,?_,localG_nhds 1 C.radius_pos,h,?_⟩⟩
  · suffices h : ∀ᶠ y in 𝓝 (familyCenter Q), ∀ p ∈ normalizedMap Q o ⁻¹' {y}, normalizedMap Q o p ∈ range F by
      filter_upwards [h] with y hy
      obtain ⟨p,rfl⟩ := (normalizedMap_surjective (Q := Q) (o := o)) y
      exact hy p rfl
    apply normalizedMap_continuous.isClosedMap.eventually_nhds_fiber
    intro p hp
    have he : blockImage (frameParams p.val) = baseBlocks (Factor.matrix Q) := (blockFlatten (pairIndex q)).injective
      ((congrArg Subtype.val hp).trans (familyCenter_val Q))
    exact eventually_localF C he
  · intro hp
    let x : Box 𝕜 o d C.radius := (1,fun _ => ⟨0, Metric.mem_closedBall_self C.radius_pos.le⟩,1)
    have hF : F x = familyCenter Q := by
      simp [F, localF, boxFrame, frameParams, x, familyCenter, C.at_zero]; rfl
    rw [show (⟨familyCenter Q,hp⟩ : range F) = ⟨F x,⟨x,rfl⟩⟩ from Subtype.ext hF.symm, hh]
    simp [G, localG, x, mid, halfDiff, rankZero]
    ext i j; simp [vecMulVec_apply]

theorem not_euclidean (C : SliceChart Q o d)
    (hCone : ¬ EuclideanAt ((1,0,rankZero) : Outer 𝕜 q o × Coordinate d × Cone 𝕜 d)) :
    ¬ EuclideanAtSubset (shuffleFamily 𝕜 q) (familyCenter Q).val := by
  obtain ⟨g⟩ := neighbourhood_model C
  exact fun h => hCone ((euclideanAt_neighbourhoodModel g).mp
    ((euclideanAtSubset_iff _ _ (familyCenter Q).property).mp h))

end GS.Shared.Singularity
