module

public import GS.Singularity.Blocks
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Module
public import GS.Topology.RankOne

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Matrix RCLike
namespace GS.Shared.Singularity
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev Axis (𝕜 : Type*) [RCLike 𝕜] := Fin (Module.finrank ℝ 𝕜 + 1) → ℝ

def axisOffDiag (u : Axis 𝕜) : 𝕜 :=
  (stdOrthonormalBasis ℝ 𝕜).repr.symm (WithLp.toLp 2 fun i => u i.succ)

def pauli (u : Axis 𝕜) : M 𝕜 2 :=
  !![(u 0 : 𝕜), axisOffDiag u; star (axisOffDiag u), -(u 0 : 𝕜)]

def axisCoords (H : M 𝕜 2) : Axis 𝕜 :=
  Fin.cons (re (H 0 0)) (fun i => (stdOrthonormalBasis ℝ 𝕜).repr (H 0 1) i)

theorem axisOffDiag_norm_sq (u : Axis 𝕜) : ‖axisOffDiag u‖ ^ 2 = ∑ i : Fin (Module.finrank ℝ 𝕜), u i.succ ^ 2 := by
  rw [axisOffDiag, LinearIsometryEquiv.norm_map, EuclideanSpace.real_norm_sq_eq]

@[simp] theorem axisOffDiag_neg (u : Axis 𝕜) : axisOffDiag (-u) = -axisOffDiag u := by
  unfold axisOffDiag
  rw [← map_neg]
  rfl

@[simp] theorem pauli_neg (u : Axis 𝕜) : pauli (-u) = -pauli u := by
  ext i j
  fin_cases i, j <;> simp [pauli]

theorem pauli_hermitian (u : Axis 𝕜) : (pauli u).IsHermitian := by
  exact Matrix.IsHermitian.ext (fun i j => by fin_cases i, j <;> simp [pauli])

@[simp] theorem pauli_trace (u : Axis 𝕜) : (pauli u).trace = 0 := by
  simp [pauli, Matrix.trace_fin_two]

theorem pauli_det (u : Axis 𝕜) : (pauli u).det = -(↑(∑ i, u i ^ 2) : 𝕜) := by
  have hn : (‖axisOffDiag u‖ : 𝕜)^2 = (↑(∑ i : Fin (Module.finrank ℝ 𝕜), u i.succ^2) : 𝕜) := by
    rw [← RCLike.ofReal_pow, axisOffDiag_norm_sq]
  simp [pauli, det_fin_two, RCLike.star_def, RCLike.mul_conj, Fin.sum_univ_succ,
    ← pow_two, hn, sub_eq_add_neg, add_comm]

@[simp] theorem axisCoords_pauli (u : Axis 𝕜) : axisCoords (pauli u) = u := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [axisCoords, pauli]
  · simp [axisCoords, pauli, axisOffDiag]

theorem pauli_injective : Function.Injective (pauli (𝕜 := 𝕜)) :=
  Function.LeftInverse.injective axisCoords_pauli

theorem pauli_axisCoords {H : M 𝕜 2} (hH : H.IsHermitian) (ht : H.trace = 0) :
    pauli (axisCoords H) = H := by
  have hd := RCLike.conj_eq_iff_re.mp (hH.apply 0 0)
  have he := hH.apply 1 0
  have hf : -(H 0 0) = H 1 1 := (eq_neg_of_add_eq_zero_right
    (by simpa [Matrix.trace_fin_two] using ht)).symm
  have hg : axisOffDiag (axisCoords H) = H 0 1 := by
    unfold axisOffDiag
    rw [(stdOrthonormalBasis ℝ 𝕜).repr.symm_apply_eq]
    ext i
    simp [axisCoords]
  ext i j
  fin_cases i, j <;> simp [pauli, hg, he] <;> simp [axisCoords, hd, hf]

@[fun_prop] theorem continuous_axisCoords : Continuous (axisCoords (𝕜 := 𝕜)) := by
  refine continuous_pi fun i => Fin.cases ?_ (fun j => ?_) i
  · exact continuous_re.comp (continuous_apply_apply 0 0)
  · change Continuous (fun H : M 𝕜 2 => ((stdOrthonormalBasis ℝ 𝕜).repr (H 0 1)) j)
    exact Continuous.comp (PiLp.continuous_apply 2 (fun _ : Fin (Module.finrank ℝ 𝕜) => ℝ) j)
      ((stdOrthonormalBasis ℝ 𝕜).repr.continuous.comp (continuous_id.matrix_elem 0 1))

/-- Every axis on the unit sphere is a conjugate of `diag(1,-1)`. -/
theorem pauli_diagonalize (u : Axis 𝕜) (hu : ∑ i, u i^2 = 1) :
    ∃ S : M 𝕜 2, Unitary S ∧ pauli u = S * diagTwo 1 (-1) * Sᴴ := by
  let h := pauli_hermitian u
  have ht : h.eigenvalues 0 + h.eigenvalues 1 = 0 := by
    simpa [Fin.sum_univ_two] using (congrArg re h.trace_eq_sum_eigenvalues).symm
  have hd : h.eigenvalues 0 * h.eigenvalues 1 = -1 := by
    have he := h.det_eq_prod_eigenvalues
    rw [pauli_det, hu, Fin.prod_univ_two] at he
    exact_mod_cast he.symm
  have h₀ : h.eigenvalues 0 = 1 ∨ h.eigenvalues 0 = -1 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by linear_combination h.eigenvalues 0 * ht - hd)
  let p : Equiv.Perm (Fin 2) := if h.eigenvalues 0 = 1 then 1 else Equiv.swap 0 1
  have hvals : (ofReal ∘ h.eigenvalues ∘ p : Fin 2 → 𝕜) = ![1,-1] := by
    funext i
    rcases h₀ with h₀ | h₀ <;>
      have h₁ : h.eigenvalues 1 = -h.eigenvalues 0 := by linarith
    all_goals fin_cases i <;> norm_num [p, h₀, h₁, Equiv.swap_apply_right, Equiv.swap_apply_left]
  let S : M 𝕜 2 := h.eigenvectorUnitary
  refine ⟨S * permMatrix p, Unitary.mul h.eigenvectorUnitary.property (perm_unitary p), ?_⟩
  have hdiag : permMatrix (𝕜 := 𝕜) p * diagTwo 1 (-1) * (permMatrix p)ᴴ =
      diagonal (ofReal ∘ h.eigenvalues) := by
    rw [diagTwo, ← hvals]
    ext i j
    rw [perm_conjugate_apply]
    simp [diagonal_apply, p.symm.injective.eq_iff]
  simpa only [← hdiag, _root_.Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.mul_assoc] using h.spectral_theorem

def frameAxis (S : M 𝕜 2) : M 𝕜 2 := S * diagTwo 1 (-1) * Sᴴ

abbrev frameCoords (S : M 𝕜 2) := axisCoords (frameAxis S)

theorem frameAxis_det {S : M 𝕜 2} (hS : Unitary S) : (frameAxis S).det = -1 := by
  rw [frameAxis, ← inv_eq_left_inv hS.1, det_conj hS.isUnit]
  simp [diagTwo, det_diagonal, Fin.prod_univ_two]

@[simp] theorem pauli_frameCoords {S : M 𝕜 2} (hS : Unitary S) : pauli (frameCoords S) = frameAxis S := by
  apply pauli_axisCoords
  · simp [Matrix.IsHermitian, frameAxis, Matrix.conjTranspose_mul, diagTwo_conjTranspose, Matrix.mul_assoc]
  · rw [frameAxis, Matrix.trace_mul_cycle, hS.1, Matrix.one_mul]
    simp [diagTwo]

theorem frameCoords_unit {S : M 𝕜 2} (hS : Unitary S) : ∑ i, frameCoords S i ^ 2 = 1 := by
  have h := frameAxis_det hS
  rw [← pauli_frameCoords hS, pauli_det, neg_inj] at h
  exact_mod_cast h

theorem exists_frameCoords (u : Axis 𝕜) (hu : ∑ i, u i ^ 2 = 1) :
    ∃ S : FullU 𝕜 2, frameCoords (Factor.matrix S) = u := by
  obtain ⟨S,hS,he⟩ := pauli_diagonalize u hu
  exact ⟨asFull S hS, (congrArg axisCoords he.symm).trans (axisCoords_pauli u)⟩

def mid {E : Type*} (K : Type*) [Field K] [AddCommGroup E] [Module K E] (a b : E) := (1/2 : K) • (a+b)
def halfDiff {E : Type*} (K : Type*) [Field K] [AddCommGroup E] [Module K E] (a b : E) := (1/2 : K) • (a-b)

def middle (a b : 𝕜) (u : Axis 𝕜) : M 𝕜 2 :=
  mid 𝕜 a b • (1 : M 𝕜 2) + halfDiff 𝕜 a b • pauli u

theorem middle_conj {S : M 𝕜 2} (hS : Unitary S) {u : Axis 𝕜}
    (hu : pauli u = S * diagTwo 1 (-1) * Sᴴ) (a b : 𝕜) :
    middle a b u = S * diagTwo a b * Sᴴ := by
  have he : diagTwo a b = mid 𝕜 a b • (1 : M 𝕜 2) + halfDiff 𝕜 a b • diagTwo 1 (-1) := by
    ext i j
    fin_cases i, j <;> simp [diagTwo, mid, halfDiff] <;> ring
  rw [he, Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hS.2, middle, hu]


def SignedFibre {Z X : Type*} [Zero Z] [Neg Z] [Neg X] (z w : Z) (u v : X) : Prop :=
  (z = w ∧ (z = 0 ∨ u = v)) ∨ (z = -w ∧ u = -v)

/-- A quadratic normalization leaves only simultaneous sign ambiguity in
an outer product, plus collapse of the zero fibre. -/
theorem signed_fibres {K E J : Type*} [Field K] [AddCommGroup E] [Module K E]
    (Q : E → K) (hQ : ∀ (a : K) x, Q (a • x) = a ^ 2 * Q x)
    {u v : E} (hu : Q u = 1) (hv : Q v = 1) {z w : J → K} :
    (∀ j, z j • u = w j • v) ↔
      SignedFibre z w u v := by
  constructor
  · intro he
    have hvn : v ≠ 0 := by
      rintro rfl
      simpa [hv] using hQ 0 u
    have eqf {z w : J → K} : (∀ j, z j • v = w j • v) → z = w := fun h =>
      funext fun j => smul_left_injective K hvn (h j)
    by_cases hz : z = 0
    · exact Or.inl ⟨eqf (by simpa [hz] using he), Or.inl hz⟩
    obtain ⟨j,hj⟩ := Function.ne_iff.mp hz
    have hs : z j ^ 2 = w j ^ 2 := by simpa [hQ, hu, hv] using congrArg Q (he j)
    have huv : u = v ∨ u = -v := (sq_eq_sq_iff_eq_or_eq_neg.mp hs).imp
      (fun h => smul_right_injective (M := E) hj (by simpa only [h] using he j))
      (fun h => smul_right_injective (M := E) hj (by simpa only [h, smul_neg, neg_smul, neg_neg] using he j))
    rcases huv with rfl | rfl
    · exact Or.inl ⟨eqf he, Or.inr rfl⟩
    · exact Or.inr ⟨eqf (fun k => by simpa [smul_neg, neg_smul] using congrArg Neg.neg (he k)), rfl⟩
  · rintro (⟨rfl,rfl | rfl⟩ | ⟨rfl,rfl⟩) j <;> simp

theorem real_outer_fibres {ι κ : Type*} [Fintype ι] {u v : ι → ℝ} {z w : κ → ℝ}
    (hu : ∑ i, u i ^ 2 = 1) (hv : ∑ i, v i ^ 2 = 1) :
    vecMulVec u z = vecMulVec v w ↔
      SignedFibre z w u v := by
  rw [← signed_fibres (fun x : ι → ℝ => ∑ i, x i^2)
    (by simp [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]) hu hv]
  simp only [← Matrix.ext_iff, funext_iff, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  exact forall_comm

/-- The two eigenvalue families are unordered, but any swap is common to all
blocks. At the scalar locus the axis disappears entirely. -/
def PairFibre {A X : Type*} [Neg X] (a b c d : A) (u v : X) : Prop :=
  (a = c ∧ b = d ∧ (a = b ∨ u = v)) ∨ (a = d ∧ b = c ∧ u = -v)

section Midpoint
variable {E : Type*}

variable {K X : Type*} [Field K] [CharZero K] [AddCommGroup E] [Module K E] [Neg X]

@[simp] theorem mid_add_sub (a z : E) : mid K (a+z) (a-z) = a := by unfold mid; module
@[simp] theorem halfDiff_add_sub (a z : E) : halfDiff K (a+z) (a-z) = z := by unfold halfDiff; module

/-- The same sum/difference coordinates describe both the block and the cone fibres. -/
theorem pairFibre_iff_mid {a b c d : E} {u v : X} :
    PairFibre a b c d u v ↔ mid K a b = mid K c d ∧
      SignedFibre (halfDiff K a b) (halfDiff K c d) u v := by
  have eqp (x y z w : E) : (x = z ∧ y = w) ↔ mid K x y = mid K z w ∧ halfDiff K x y = halfDiff K z w := by
    constructor
    · rintro ⟨rfl,rfl⟩; exact ⟨rfl,rfl⟩
    · rintro ⟨h,k⟩
      unfold mid halfDiff at *
      exact ⟨by linear_combination (norm := module) h + k,
        by linear_combination (norm := module) h - k⟩
  have hs : mid K d c = mid K c d := by simp [mid, add_comm]
  have hd : halfDiff K d c = -halfDiff K c d := by unfold halfDiff; module
  simp only [PairFibre, SignedFibre, ← and_assoc, eqp a b c d, eqp a b d c, hs, hd,
    show halfDiff K a b = 0 ↔ a = b by simp [halfDiff, sub_eq_zero]]
  tauto

end Midpoint

theorem middle_trace (a b : 𝕜) (u : Axis 𝕜) : (middle a b u).trace = a+b := by
  simp [middle, mid, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one] <;> ring

theorem middle_fibres {κ : Type*} {a b c d : κ → 𝕜} {u v : Axis 𝕜}
    (hu : ∑ i, u i^2 = 1) (hv : ∑ i, v i^2 = 1) :
    (∀ j, middle (a j) (b j) u = middle (c j) (d j) v) ↔ PairFibre a b c d u v := by
  rw [pairFibre_iff_mid (K := 𝕜)]
  have hQ (t : 𝕜) (X : M 𝕜 2) : -(t • X).det = t^2 * -X.det := by simp
  have hu' : -(pauli u).det = 1 := by simp [pauli_det, hu]
  have hv' : -(pauli v).det = 1 := by simp [pauli_det, hv]
  have hf := signed_fibres (fun X : M 𝕜 2 => -X.det) hQ (u := pauli u) (v := pauli v)
    (z := halfDiff 𝕜 a b) (w := halfDiff 𝕜 c d) hu' hv'
  simp only [SignedFibre, ← pauli_neg, pauli_injective.eq_iff] at hf
  rw [SignedFibre, ← hf]
  constructor
  · intro h
    have hs (j : κ) : a j + b j = c j + d j := by simpa only [middle_trace] using congrArg trace (h j)
    refine ⟨funext fun j => by simp [mid, hs j], fun j => ?_⟩
    exact add_left_cancel (a := mid 𝕜 (c j) (d j) • (1 : M 𝕜 2))
      (by simpa [middle, mid, halfDiff, hs j] using h j)
  · rintro ⟨h,h'⟩ j
    exact congrArg₂ (fun (a : 𝕜) (T : M 𝕜 2) => a • 1 + T) (congrFun h j) (h' j)

end GS.Shared.Singularity
