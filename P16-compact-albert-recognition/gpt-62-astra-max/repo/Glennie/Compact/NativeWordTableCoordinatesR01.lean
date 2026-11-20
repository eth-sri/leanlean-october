module
public import Glennie.Compact.ExactCoordinates
public import Glennie.ObservationData
public import Glennie.Hilbert
meta import Glennie.Compact.ExactCoordinates
meta import Glennie.ObservationData

/-! Compute a coefficient matrix of the *actual list of words* in the exact
rational Albert algebra. The entries and the left inverse are checked
before scalar extension. Only a linear readout is needed: independence of its images suffices. -/
@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
open SubmissionR03 Exact

/-- Evaluation is natural under any product morphism, without assumptions on
linearity, commutativity, or dimension of its target. -/
theorem word_map {X Y : Type*} (f : X → Y) (j : X → X → X) (k : Y → Y → Y)
    (h : ∀ x y, f (j x y) = k (f x) (f y)) (e : X) (a : Fin 3 → X) (i : Fin 27) :
    f (wordValues e a j i) = wordValues (f e) (f ∘ a) k i := by
  fin_cases i <;> simp [wordValues,h]

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
def evalQ := wordValues (Exact.one : A ℚ) ![markX, markY 1, markZ] (prod (1/2))
noncomputable abbrev castQ := Rat.castHom ℝ
private theorem words_real (i) : realize castQ (evalQ i) = nativeWordValues i := by
  have marks : realize castQ ∘ ![markX, markY 1, markZ] = nativeMarks := by
    funext l; fin_cases l <;> first | apply realize_x | apply realize_y | apply realize_z
  rw [evalQ, word_map (realize castQ) _ jordan (realize_prod _ _ (by norm_num : castQ (1/2) = 1/2)), realize_one,marks]; rfl

def coeff {R : Type*} [CommRing R] : A R → Fin 27 → R
  | (a,b,c,u,v,w) =>
    let o (x : O R) := ![x.1.re,x.1.imI,x.1.imJ,x.1.imK,x.2.re,x.2.imI,x.2.imJ,x.2.imK]
    Fin.append ![a,b,c] (Fin.append (o u) (Fin.append (o v) (o w)))

noncomputable def read : Albert →ₗ[ℝ] Fin 27 → ℝ where
  toFun x := coeff (x.d0,x.d1,x.d2,x.o01,x.o02,x.o12)
  map_add' _ _ := by funext k; fin_cases k <;> rfl
  map_smul' _ _ := by funext k; fin_cases k <;> rfl

private theorem read_cast (x : A ℚ) (k : Fin 27) : read (realize castQ x) k = castQ (coeff x k) := by
  fin_cases k <;> rfl

def entries (i : Fin 27) := coeff (evalQ i)
def wordM : Matrix (Fin 27) (Fin 27) ℚ := unpack (eval% pack (Matrix.of entries))
def invQ : Matrix (Fin 27) (Fin 27) ℚ := unpack (eval% pack (inverseCandidate (·⁻¹) wordM))
private theorem check_entries : Matrix.of entries = wordM := by funext i; fin_cases i <;> decide +kernel
private theorem check_inverse : invQ * wordM = 1 := by funext i; fin_cases i <;> decide +kernel

theorem nativeWords_independent : LinearIndependent ℝ nativeWordValues := by
  apply LinearIndependent.of_comp read
  have rows : read ∘ nativeWordValues = (wordM.map castQ).row := by
    funext i k; rw [←check_entries,Function.comp_apply,←words_real]; exact read_cast ..
  rw [rows]; exact Matrix.linearIndependent_rows_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse (mapped_left_inverse castQ check_inverse)))
end Glennie.Compact.NativeWordTableR01
