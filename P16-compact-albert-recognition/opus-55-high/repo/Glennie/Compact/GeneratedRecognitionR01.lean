/- Generated-span marked recognition from finite scalar observations. -/
module
public import Glennie.Compact.MarkedModelConsumerR01
public import Glennie.Compact.ScalarResidualEntranceR01

@[expose] public section
namespace Glennie.Compact.MarkedModelConsumerCandidate
noncomputable section
open Module Glennie.Compact.NativeWordTableR01
open Glennie.Compact.NativeWordTableR01.ClosureCandidate
open scoped BigOperators

section GeneratedRecognition
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E)

/-- Symbolic exact coefficients are produced by the actual native word basis.
Literal array binding is provided separately. -/
def referenceCoeff (i k l : Fin 27) : ℝ :=
  wordBasis.repr (jordan (nativeWords i) (nativeWords k)) l

theorem reference_table (i k : Fin 27) :
    (1 : ℝ) • jordan (nativeWords i) (nativeWords k) =
      ∑ l, referenceCoeff i k l • nativeWords l := by
  simpa [one_smul, referenceCoeff, wordBasis_eq_nativeWords] using
    (wordBasis.sum_repr (jordan (nativeWords i) (nativeWords k))).symm

/-- Matching scalar observations produce actual vector-valued products. -/
theorem matched_products (h : Match27 e a j) (i k : Fin 27) :
    j (candidateWords e a j i) (candidateWords e a j k) =
      ∑ l, referenceCoeff i k l • candidateWords e a j l := by
  have ht := candidate_scaled_table_of_scalar_data
    (candidateWords e a j) j 1 referenceCoeff reference_table h.gram h.mixed h.product_sq
  simpa [one_smul] using ht i k

theorem words_mem (i : Fin 27) : candidateWords e a j i ∈ wordSpan e a j :=
  Submodule.subset_span ⟨i, rfl⟩

theorem unit_mem : e ∈ wordSpan e a j := by
  simpa [candidateWords_unit] using words_mem e a j 0

theorem marks_mem (i : Fin 3) : a i ∈ wordSpan e a j := by
  fin_cases i
  exacts [words_mem e a j 1, words_mem e a j 2, words_mem e a j 3]

theorem wordSpan_closed (h : Match27 e a j) :
    ∀ x ∈ wordSpan e a j, ∀ y ∈ wordSpan e a j, j x y ∈ wordSpan e a j := by
  intro x hx y hy
  have := Submodule.apply_mem_map₂ j hx hy
  rw [wordSpan, Submodule.map₂_span_span] at this
  refine Submodule.span_le.2 ?_ this
  rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨k, rfl⟩, rfl⟩
  dsimp
  rw [matched_products e a j h i k]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (words_mem e a j l)

/-- Every syntactic word lies in every unital marked product-closed submodule. -/
theorem eval_mem (K : Submodule ℝ E) (he : e ∈ K) (ha : ∀ i, a i ∈ K)
    (hj : ∀ x ∈ K, ∀ y ∈ K, j x y ∈ K) (w : Word) :
    eval e a (fun x y => j x y) w ∈ K := by
  induction w with
  | unit => exact he
  | mark i => exact ha i
  | mul u v ihu ihv => exact hj _ ihu _ ihv

theorem wordSpan_eq_generated (h : Match27 e a j) :
    wordSpan e a j = generated e a j := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    apply Submodule.mem_sInf.mpr
    intro K hK
    exact eval_mem e a j K hK.1 hK.2.1 hK.2.2 (words i)
  · apply sInf_le
    exact ⟨unit_mem e a j, marks_mem e a j, wordSpan_closed e a j h⟩

def spanUnit : wordSpan e a j := ⟨e, unit_mem e a j⟩
def spanMarks (i : Fin 3) : wordSpan e a j := ⟨a i, marks_mem e a j i⟩

def spanProduct (h : Match27 e a j) :
    wordSpan e a j →ₗ[ℝ] wordSpan e a j →ₗ[ℝ] wordSpan e a j :=
  LinearMap.mk₂ ℝ (fun x y => ⟨j x.1 y.1, wordSpan_closed e a j h _ x.2 _ y.2⟩)
    (fun _ _ _ => Subtype.ext (by simp)) (fun _ _ _ => Subtype.ext (by simp))
    (fun _ _ _ => Subtype.ext (by simp)) (fun _ _ _ => Subtype.ext (by simp))

def spanBasis (h : Match27 e a j) : Basis (Fin 27) ℝ (wordSpan e a j) :=
  Basis.span (candidate_words_linearIndependent (candidateWords e a j) h.gram)

@[simp] theorem spanBasis_val (h : Match27 e a j) (i : Fin 27) :
    ((spanBasis e a j h i : wordSpan e a j) : E) = candidateWords e a j i :=
  Basis.coe_span_apply _ i

def recognitionA (h : Match27 e a j) : wordSpan e a j ≃ₗ[ℝ] Albert :=
  markedLinearEquiv (spanBasis e a j h)

theorem recognitionA_basis (h : Match27 e a j) (i : Fin 27) :
    recognitionA e a j h (spanBasis e a j h i) = nativeWords i :=
  markedLinearEquiv_basis _ i

theorem span_table (h : Match27 e a j) (i k : Fin 27) :
    (1 : ℝ) • spanProduct e a j h (spanBasis e a j h i) (spanBasis e a j h k) =
      ∑ l, referenceCoeff i k l • spanBasis e a j h l := by
  simp [one_smul]
  apply Subtype.ext
  change j ((spanBasis e a j h i : wordSpan e a j) : E)
    ((spanBasis e a j h k : wordSpan e a j) : E) =
    (wordSpan e a j).subtype (∑ l, referenceCoeff i k l • spanBasis e a j h l)
  simp [map_sum, map_smul, Submodule.subtype_apply, spanBasis_val]
  exact matched_products e a j h i k

theorem recognitionA_word (h : Match27 e a j) (k : Fin 27) (x : E)
    (hx : x ∈ wordSpan e a j) (hk : candidateWords e a j k = x) :
    recognitionA e a j h ⟨x, hx⟩ = nativeWords k := by
  rw [show (⟨x, hx⟩ : wordSpan e a j) = spanBasis e a j h k from Subtype.ext (by simp [hk]),
    recognitionA_basis]

def recognizedModel (h : Match27 e a j) :
    MarkedModelEquiv (wordSpan e a j) (spanUnit e a j)
      (fun x y => spanProduct e a j h x y) (Inner.inner ℝ) (spanMarks e a j) marks where
  A := recognitionA e a j h
  map_unit := recognitionA_word e a j h 0 e _ rfl
  map_product := map_product_of_scaled_table (spanBasis e a j h) (spanProduct e a j h)
    1 one_ne_zero referenceCoeff reference_table (span_table e a j h)
  map_metric := map_metric_of_basis (spanBasis e a j h) (_root_.innerₗ (wordSpan e a j))
    (_root_.innerₗ Albert) (by
      intro i k
      change Inner.inner ℝ ((spanBasis e a j h i : wordSpan e a j) : E)
        ((spanBasis e a j h k : wordSpan e a j) : E) = _
      rw [spanBasis_val, spanBasis_val]
      exact h.gram i k)
  map_marks i := by
    fin_cases i
    exacts [recognitionA_word e a j h 1 _ _ rfl, recognitionA_word e a j h 2 _ _ rfl,
      recognitionA_word e a j h 3 _ _ rfl]

end GeneratedRecognition

section SameA
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E)

theorem unique_generated_marked_recognition (h : Match27 e a j) :
    wordSpan e a j = generated e a j ∧ Nonempty (MarkedModelEquiv (wordSpan e a j) (spanUnit e a j)
      (fun x y => spanProduct e a j h x y) (Inner.inner ℝ) (spanMarks e a j) marks) :=
  ⟨wordSpan_eq_generated e a j h, ⟨recognizedModel e a j h⟩⟩
end SameA

end
end Glennie.Compact.MarkedModelConsumerCandidate
