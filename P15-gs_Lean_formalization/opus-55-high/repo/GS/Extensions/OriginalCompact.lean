module

public import GS.Extensions.FiniteTopology

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The original compact-domain construction

No polar-log replacement is made. The implication G-fibre => F-fibre is proved
from the actual definitions, including the collapsed circle. The converse is
not silently assumed proved: it is the sole hypothesis of the compact-image
homeomorphism below.
-/

noncomputable section
namespace GS.Extensions

 theorem rotation_zero : rotation 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation]

 theorem rotation_add (s t : ℝ) : rotation (s+t) = rotation s * rotation t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;>
    ring

 theorem matrixExp_zero (n : ℕ) : matrixExp (0 : Mat n) = 1 := by
  rw [matrixExp_eq_exp]
  simp

 theorem originalPsi_zero {q : ℕ} (Q₀ : Mat q) : originalPsi Q₀ 0 = Q₀ := by
  simp [originalPsi, matrixExp_zero]

/-- One entire direction of the actual f/g fibre equivalence. This has no
smallness, injectivity-of-exp, coverage, or manifold hypothesis. -/
 theorem originalF_eq_of_originalG_eq {q : ℕ} (Q₀ : Mat q)
    (ell r ell' r' : Fin q → ℝ) (c z c' w : Mat q) (u v : CircleVector)
    (hu : OnCircle u) (hv : OnCircle v)
    (h : originalG (ell,r,c,z,u) = originalG (ell',r',c',w,v)) :
    originalF Q₀ (ell,r,c,z,u) = originalF Q₀ (ell',r',c',w,v) := by
  obtain ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ :=
    (originalG_fibres ell r ell' r' c z c' w u v hu hv).mp h <;>
    simp only [originalF, add_zero, neg_zero, middleBlock_equal, sub_eq_add_neg, neg_neg, middleBlock_swap]

/-- A fixed representative of the unit circle, only for marking the basepoint. -/
def circleBase : CircleVector := ![1,0]

 def originalBaseParameters (q : ℕ) : OriginalParameters q :=
  (0,0,0,0,circleBase)

 theorem originalBaseParameters_mem (q : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    originalBaseParameters q ∈ originalK q η := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by norm_num [circleBase, OnCircle]⟩ <;>
    first | simp_all [IsSkew] | simpa [originalBaseParameters, frobSq, frobInner] using sq_nonneg η

 theorem originalF_basePoint {q : ℕ} (Q₀ : Mat q) :
    originalF Q₀ (originalBaseParameters q) = basePoint Q₀ := by
  simp [originalF, originalBaseParameters, originalPsi_zero, rotation_zero,
    middleBlock_equal, finProdFinEquiv]
  aesop

 theorem originalG_basePoint (q : ℕ) :
    originalG (originalBaseParameters q) = (0,0,0,0) := by
  simp only [originalG, originalBaseParameters, Prod.mk.injEq, true_and]
  ext i j
  simp [GS.outer]

end GS.Extensions
