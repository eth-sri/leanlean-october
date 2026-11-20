module

public import GS.Singularity.Blocks
public import Mathlib.Analysis.Matrix.Order
public import GS.Topology.SectionPair

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Matrix RCLike Set Filter
open scoped ComplexOrder MatrixOrder Topology
namespace GS.Shared.Singularity
variable {𝕜 : Type*} [RCLike 𝕜] {q : ℕ}

def anchorCell {o : Fin q} : Anchor o → Fin q × Fin q
  | .inl i => (i,o)
  | .inr j => (o,j.val)

abbrev OnAnchors (o : Fin q) (P : Fin q → Fin q → Prop) : Prop :=
  ∀ k : Anchor o, P (anchorCell k).1 (anchorCell k).2

theorem isOpen_onAnchors {X : Type*} [TopologicalSpace X] {P : X → Fin q → Fin q → Prop}
    (o : Fin q) (h : ∀ i j, IsOpen {x | P x i j}) : IsOpen {x | OnAnchors o (P x)} := by
  classical
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun k => h _ _

abbrev AnchorsNonzero (A : M 𝕜 q) (o : Fin q) : Prop := OnAnchors o (fun i j => A i j ≠ 0)

def PositiveAnchors (Q : M 𝕜 q) (o : Fin q) (A : M 𝕜 q) : Prop := OnAnchors o (fun i j => 0 < A i j / Q i j)

theorem positiveAnchors_self {Q : M 𝕜 q} {o : Fin q} (hQ : AnchorsNonzero Q o) :
    PositiveAnchors Q o Q := by
  intro k
  simp [hQ k]

/-- The unit phase, taking the value one at zero. -/
def phase (z : 𝕜) : unitary 𝕜 := ⟨if z = 0 then 1 else z / (‖z‖ : 𝕜), by
  apply _root_.Unitary.mem_iff_star_mul_self.mpr
  rw [RCLike.star_def, RCLike.conj_mul]
  by_cases hz : z = 0 <;> simp [hz, norm_div]⟩

@[simp] theorem star_phase_mul (z : 𝕜) : star (phase z : 𝕜) * z = (‖z‖ : 𝕜) := by
  by_cases hz : z = 0
  · simp [hz]
  simp [phase, hz, RCLike.star_def, div_mul_eq_mul_div, RCLike.conj_mul, pow_two]

def rowPhase (Q A : M 𝕜 q) (o i : Fin q) : unitary 𝕜 := phase (A i o / Q i o)
def colPhase (Q A : M 𝕜 q) (o j : Fin q) : unitary 𝕜 := star (rowPhase Q A o o) * phase (A o j / Q o j)

@[simp] theorem colPhase_anchor (Q A : M 𝕜 q) (o : Fin q) : colPhase Q A o o = 1 := _root_.Unitary.star_mul_self _

def dephase (Q A : M 𝕜 q) (o : Fin q) : M 𝕜 q :=
  (diagonal fun i => star (rowPhase Q A o i : 𝕜)) * A *
    (diagonal fun j => star (colPhase Q A o j : 𝕜))

@[simp] theorem dephase_apply (Q A : M 𝕜 q) (o i j : Fin q) : dephase Q A o i j =
    star (rowPhase Q A o i : 𝕜) * A i j * star (colPhase Q A o j : 𝕜) := by simp [dephase]

variable {Q A : M 𝕜 q} {o : Fin q}

theorem dephase_sandwich (i j : Fin q) :
    (rowPhase Q A o i : 𝕜) * dephase Q A o i j * (colPhase Q A o j : 𝕜) = A i j := by
  grind [dephase_apply, mul_assoc, _root_.Unitary.coe_mul_star_self, _root_.Unitary.coe_star_mul_self]

theorem diagonal_unitary {k : ℕ} (v : Fin k → unitary 𝕜) : Unitary (diagonal fun i => (v i : 𝕜)) := by
  apply Unitary.of_conjTranspose_mul
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact _root_.Unitary.coe_star_mul_self (v i)

theorem dephase_unitary (hA : Unitary A) : Unitary (dephase Q A o) :=
  ((diagonal_unitary (star (rowPhase Q A o))).mul hA).mul (diagonal_unitary (star (colPhase Q A o)))

abbrev NonnegativeAnchors (Q : M 𝕜 q) (o : Fin q) (A : M 𝕜 q) : Prop :=
  OnAnchors o fun i j => 0 ≤ A i j / Q i j

theorem NonnegativeAnchors.positive (h : NonnegativeAnchors Q o A)
    (hQ : AnchorsNonzero Q o) (hA : AnchorsNonzero A o) : PositiveAnchors Q o A :=
  fun k => lt_of_le_of_ne (h k) (div_ne_zero (hA k) (hQ k)).symm

theorem dephase_nonnegative : NonnegativeAnchors Q o (dephase Q A o) := by
  have hn (z : 𝕜) : (0 : 𝕜) ≤ (‖z‖ : 𝕜) := RCLike.ofReal_nonneg.mpr (norm_nonneg _)
  rintro (i | j)
  · simpa only [anchorCell, dephase_apply, colPhase_anchor, OneMemClass.coe_one, star_one,
      mul_one, mul_div_assoc, rowPhase, star_phase_mul] using hn (A i o / Q i o)
  · change 0 ≤ dephase Q A o o j.val / Q o j.val
    simp only [dephase_apply, colPhase, MulMemClass.coe_mul, _root_.Unitary.coe_star, star_mul, star_star]
    rw [show _ / Q o j.val = (star (rowPhase Q A o o : 𝕜) * rowPhase Q A o o) *
      (star (phase (A o j.val / Q o j.val) : 𝕜) * (A o j.val / Q o j.val)) by ring,
      _root_.Unitary.coe_star_mul_self, one_mul, star_phase_mul]
    exact hn _

/-- Uniqueness of the positive polar factors; positivity gives the unique
nonnegative square root of the Gram matrix. -/
theorem polar_unique {U V P R : M 𝕜 2}
    (hu : Unitary U) (hv : Unitary V) (hp : P.PosDef) (hr : R.PosSemidef)
    (he : U * P = V * R) : U = V := by
  have h := congrArg (fun T : M 𝕜 2 => Tᴴ * T) he
  have hs : P^2 = R^2 := by
    simpa only [Matrix.conjTranspose_mul, hp.isHermitian.eq, hr.isHermitian.eq, Matrix.mul_assoc,
      hu.adjoint_mul_cancel, hv.adjoint_mul_cancel, pow_two] using h
  exact hp.isUnit.mul_right_cancel ((CFC.sq_eq_sq_iff P R hp.posSemidef.nonneg hr.nonneg).mp hs ▸ he)

abbrev MiddlePositive (Q : M 𝕜 q) (o : Fin q) (N : Blocks 𝕜 q) : Prop :=
  OnAnchors o (fun i j => ((Q i j)⁻¹ • N i j).PosDef)

def baseBlocks (Q : M 𝕜 q) : Blocks 𝕜 q := fun i j => Q i j • (1 : M 𝕜 2)

def rightFactor {o : Fin q} (g : Outer 𝕜 q o) (j : Fin q) : FullU 𝕜 2 :=
  if h : j = o then 1 else g (.inr ⟨j,h⟩)

abbrev outerRight {o : Fin q} (g : Outer 𝕜 q o) (j : Fin q) := Factor.matrix (rightFactor g j)

@[simp] theorem outerRight_anchor {o : Fin q} (g : Outer 𝕜 q o) : outerRight g o = 1 := by
  simp [outerRight,rightFactor]

@[simp] theorem rightFactor_one {o : Fin q} (j : Fin q) : rightFactor (1 : Outer 𝕜 q o) j = 1 := by
  by_cases h : j = o <;> simp [rightFactor, h]

@[fun_prop] theorem continuous_rightFactor {o : Fin q} (j : Fin q) :
    Continuous (fun g : Outer 𝕜 q o => rightFactor g j) := by
  by_cases h : j = o <;> simp [rightFactor,h] <;> fun_prop

def outerSandwich {o : Fin q} (g : Outer 𝕜 q o) (N : Blocks 𝕜 q) : Blocks 𝕜 q :=
  fun i j => Factor.matrix (g (.inl i)) * N i j * outerRight g j

@[simp] theorem outerSandwich_one {o : Fin q} (N : Blocks 𝕜 q) :
    outerSandwich (1 : Outer 𝕜 q o) N = N := by
  funext i j
  simp [outerSandwich,outerRight]

/-- Two anchored decompositions have the same outer frames and middle blocks. -/
theorem normalized_fibres {o : Fin q} {Q : M 𝕜 q} {g h : Outer 𝕜 q o} {N N' : Blocks 𝕜 q}
    (hN : MiddlePositive Q o N) (hN' : OnAnchors o fun i j => ((Q i j)⁻¹ • N' i j).PosSemidef)
    (he : outerSandwich g N = outerSandwich h N') : g = h ∧ N = N' := by
  have hentry i j : Factor.matrix (g (.inl i)) * N i j * outerRight g j =
      Factor.matrix (h (.inl i)) * N' i j * outerRight h j := congrFun (congrFun he i) j
  have hL i : Factor.matrix (g (.inl i)) = Factor.matrix (h (.inl i)) := by
    apply polar_unique (Factor.matrix_unitary _) (Factor.matrix_unitary _)
      (hN (.inl i)) (hN' (.inl i))
    simpa only [anchorCell, outerRight_anchor, Matrix.mul_one, Matrix.mul_smul] using
      congrArg ((Q i o)⁻¹ • ·) (hentry i o)
  have hc i j : N i j * outerRight g j = N' i j * outerRight h j :=
    (Factor.matrix_unitary (g (.inl i))).isUnit.mul_left_cancel
      (by simpa only [← hL i, Matrix.mul_assoc] using hentry i j)
  have eh : g = h := by
    funext k
    apply Factor.matrix_injective
    rcases k with i | j
    · exact hL i
    · apply Matrix.conjTranspose_injective
      have hp : ((Q o j.val)⁻¹ • N o j.val).PosDef := hN (.inr j)
      have hs : ((Q o j.val)⁻¹ • N' o j.val).PosSemidef := hN' (.inr j)
      have hr := polar_unique (Factor.matrix_unitary (rightFactor g j.val)).conjTranspose
        (Factor.matrix_unitary (rightFactor h j.val)).conjTranspose hp hs (by
          simpa only [← Matrix.smul_mul, Matrix.conjTranspose_mul, hp.isHermitian.eq, hs.isHermitian.eq]
            using congrArg (fun X : M 𝕜 2 => ((Q o j.val)⁻¹ • X)ᴴ) (hc o j.val))
      simpa [outerRight, rightFactor, j.property] using hr
  subst h
  exact ⟨rfl, funext fun i => funext fun j =>
    (Factor.matrix_unitary (rightFactor g j)).isUnit.mul_right_cancel (hc i j)⟩

abbrev Frame (𝕜 : Type*) [RCLike 𝕜] {q : ℕ} (o : Fin q) :=
  Outer 𝕜 q o × (Fin 2 → FullU 𝕜 q) × FullU 𝕜 2

def frameParams {o : Fin q} (p : Frame 𝕜 o) : Parameters 𝕜 q :=
  (fun i => p.1 (.inl i) * p.2.2, p.2.1, fun j => p.2.2⁻¹ * rightFactor p.1 j)

theorem frameParams_continuous {o : Fin q} : Continuous (frameParams (𝕜 := 𝕜) (o := o)) := by
  unfold frameParams
  fun_prop

def frameMiddle {o : Fin q} (p : Frame 𝕜 o) : Blocks 𝕜 q := fun i j =>
  Factor.matrix p.2.2 * diagonal (fun a => Factor.matrix (p.2.1 a) i j) * (Factor.matrix p.2.2)ᴴ

@[simp] theorem frameImage {o : Fin q} (p : Frame 𝕜 o) :
    blockImage (frameParams p) = outerSandwich p.1 (frameMiddle p) := by
  funext i j
  change (Factor.matrix (p.1 (.inl i)) * Factor.matrix p.2.2) * _ *
    ((Factor.matrix p.2.2)ᴴ * outerRight p.1 j) = _
  simp only [outerSandwich, frameMiddle, Matrix.mul_assoc, rawMid, frameParams]

abbrev Normalized (Q : M 𝕜 q) (o : Fin q) :=
  {p : Frame 𝕜 o // ∀ a, NonnegativeAnchors Q o (Factor.matrix (p.2.1 a))}

instance normalizedCompactSpace (Q : M 𝕜 q) (o : Fin q) : CompactSpace (Normalized Q o) := by
  refine isCompact_iff_compactSpace.mp (IsClosed.isCompact ?_)
  change IsClosed {p : Frame 𝕜 o | ∀ a, NonnegativeAnchors Q o (Factor.matrix (p.2.1 a))}
  simp only [NonnegativeAnchors, OnAnchors, Set.ofPred_forall]
  refine isClosed_iInter fun a => isClosed_iInter fun k => isClosed_le (α := 𝕜) continuous_const ?_
  exact ((Factor.continuous_matrix.comp ((continuous_apply a).comp
    (continuous_fst.comp continuous_snd))).matrix_elem _ _).div_const _

/-- Fix the anchor frame on the right, and absorb the diagonal phases into
both outer tuples. -/
theorem normalized_representation (Q : M 𝕜 q) (o : Fin q) (p : Parameters 𝕜 q) :
    ∃ f : Normalized Q o, blockImage (frameParams f.val) = blockImage p := by
  let D (i : Fin q) := asFull (diagonal fun a => (rowPhase Q (rawMid p a) o i : 𝕜)) (diagonal_unitary _)
  let E (j : Fin q) := asFull (diagonal fun a => (colPhase Q (rawMid p a) o j : 𝕜)) (diagonal_unitary _)
  let B a := asFull (dephase Q (rawMid p a) o) (dephase_unitary (Factor.matrix_unitary (p.2.1 a)))
  let R j := E j * p.2.2 j
  let U := (R o)⁻¹
  let g : Outer 𝕜 q o := Sum.elim (fun i => p.1 i * D i * U⁻¹) (fun j => U * R j.val)
  have hg j : U⁻¹ * rightFactor g j = R j := by
    by_cases h : j = o <;> simp [h, rightFactor, g, U]
  refine ⟨⟨(g,B,U),fun _ => dephase_nonnegative⟩,?_⟩
  rw [show frameParams (g,B,U) = ((fun i => p.1 i * D i), B, R) from
    Prod.ext (funext fun _ => inv_mul_cancel_right ..) (Prod.ext rfl (funext hg))]
  funext i j
  have he : Factor.matrix (D i) * (diagonal fun a => Factor.matrix (B a) i j) *
      Factor.matrix (E j) = diagonal (fun a => rawMid p a i j) := by
    simp only [D,E,B,asFull,Factor.matrix_ofMatrix,diagonal_mul_diagonal]
    congr 1
    exact funext fun a => dephase_sandwich i j
  change (Factor.matrix (p.1 i) * Factor.matrix (D i)) * _ *
     (Factor.matrix (E j) * Factor.matrix (p.2.2 j)) = _
  simpa only [blockImage, Matrix.mul_assoc] using
    congrArg (fun T => Factor.matrix (p.1 i) * T * Factor.matrix (p.2.2 j)) he

/-- The normalized compact family has a unique middle tuple over the base. -/
theorem normalized_base_middle {Q : FullU 𝕜 q} {o : Fin q} (hQ : AnchorsNonzero (Factor.matrix Q) o)
    {p : Normalized (Factor.matrix Q) o}
    (hp : blockImage (frameParams p.val) = baseBlocks (Factor.matrix Q)) (a : Fin 2) : p.val.2.1 a = Q := by
  let S := Factor.matrix p.val.2.2
  have hS := Factor.matrix_unitary p.val.2.2
  have hN : OnAnchors o fun i j => ((Factor.matrix Q i j)⁻¹ • frameMiddle p.val i j).PosSemidef := by
    intro k
    unfold frameMiddle
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
    exact (Matrix.PosSemidef.diagonal (fun a => by simpa [div_eq_inv_mul] using p.property a k)).mul_mul_conjTranspose_same S
  have h₀ : MiddlePositive (Factor.matrix Q) o (baseBlocks (Factor.matrix Q)) := by
    intro k
    simpa [baseBlocks, smul_smul, hQ k] using (Matrix.PosDef.one : (1 : M 𝕜 2).PosDef)
  rw [frameImage, ← outerSandwich_one (baseBlocks (Factor.matrix Q))] at hp
  apply Factor.matrix_injective
  ext i j
  simpa [frameMiddle, baseBlocks, S, Matrix.mul_assoc, hS.adjoint_mul_cancel,
    Matrix.mul_smul, Matrix.smul_mul, hS.1] using congrArg (fun N : Blocks 𝕜 q => (Sᴴ * N i j * S) a a)
      (normalized_fibres h₀ hN hp.symm).2.symm

variable {d : ℕ}

abbrev Coordinate (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev CBall (d : ℕ) (r : ℝ) := Metric.closedBall (0 : Coordinate d) r

/-- A compact, injective slice parametrization containing a neighbourhood of the base. -/
structure SliceChart (Q : FullU 𝕜 q) (o : Fin q) (d : ℕ) where
  anchors : AnchorsNonzero (Factor.matrix Q) o
  radius : ℝ
  radius_pos : 0 < radius
  valueFactor : CBall d radius → FullU 𝕜 q
  at_zero : valueFactor ⟨0,Metric.mem_closedBall_self radius_pos.le⟩ = Q
  continuous_factor : Continuous valueFactor
  inj_factor : Function.Injective valueFactor
  positive_factor : ∀ x, PositiveAnchors (Factor.matrix Q) o (Factor.matrix (valueFactor x))
  nearby : ∀ᶠ A in 𝓝 Q, PositiveAnchors (Factor.matrix Q) o (Factor.matrix A) → A ∈ range valueFactor

namespace SliceChart
variable {Q : FullU 𝕜 q} {o : Fin q} (C : SliceChart Q o d)

abbrev value (x : CBall d C.radius) : M 𝕜 q := Factor.matrix (C.valueFactor x)

theorem value_injective : Function.Injective C.value := Factor.matrix_injective.comp C.inj_factor

/-- Read the positive slice directly in a product chart of the full group. -/
def ofProduct {F : Type*} [TopologicalSpace F] (e : OpenPartialHomeomorph (FullU 𝕜 q) (F × Coordinate d))
    (a : F) (hQ : AnchorsNonzero (Factor.matrix Q) o) (hQ' : Q ∈ e.source) (h0 : e Q = (a,0))
    (hp : ∀ x ∈ e.source, PositiveAnchors (Factor.matrix Q) o (Factor.matrix x) ↔ (e x).1 = a) :
    SliceChart Q o d := by
  have hc : Continuous (fun z : Coordinate d => (a,z)) := continuous_const.prodMk continuous_id
  choose δ hδ hδ' using Metric.mem_nhds_iff.mp
    (hc.continuousAt (x := 0) (e.open_target.mem_nhds (h0 ▸ e.map_source hQ')))
  have hr : 0 < δ/2 := by positivity
  have hball (z : CBall d (δ/2)) : (a,z.val) ∈ e.target :=
    hδ' (Metric.closedBall_subset_ball (by linarith) z.property)
  refine ⟨hQ,δ/2,hr,fun z => e.symm (a,z.val), h0 ▸ e.left_inv hQ',
    e.continuousOn_symm.comp_continuous (hc.comp continuous_subtype_val) hball,
    fun x y h => Subtype.ext (congrArg Prod.snd (e.symm.injOn (hball x) (hball y) h)),
    fun z => (hp _ (e.map_target (hball z))).mpr (congrArg Prod.fst (e.right_inv (hball z))), ?_⟩
  have hd := e.continuousOn.snd.continuousAt (e.open_source.mem_nhds hQ')
  have hB : CBall d (δ/2) ∈ 𝓝 (e Q).2 := h0 ▸ Metric.closedBall_mem_nhds _ hr
  filter_upwards [e.open_source.mem_nhds hQ', hd hB]
    with x hx hx' hp'
  exact ⟨⟨(e x).2,hx'⟩, (congrArg (fun a => e.symm (a,(e x).2)) ((hp _ hx).mp hp').symm).trans (e.left_inv hx)⟩

end SliceChart
end GS.Shared.Singularity
