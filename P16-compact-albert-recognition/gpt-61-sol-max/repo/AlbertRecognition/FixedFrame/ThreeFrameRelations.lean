/- Actual three-frame coefficient relations for the bounded algebraic gate.
The coarse action data below are explicitly intermediate obligations.  They
must be constructed from the arbitrary-cubic Jacobi kernel by native frame
pullback and the derived scalar-block theorem; this file does not assume or
claim that construction, unknown invariance, or the final recognition theorem. -/
module

public import AlbertRecognition.CubicOperators

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie

/-- Intermediate coarse action data on the three actual native frames.
No full operator proportionality, Jordan identity, or unknown invariance is a
field.  Existence from A(q referenceCubic)B=0 remains a separate obligation. -/
def X (k : Fin 3) (u : Octonion) : V := ![X12 u, X02 u, X01 u] k

structure FrameScalarData (G : Module.End ℝ V) (i : Fin 3) where
  a : ℝ
  b : ℝ
  c : ℝ
  on_h_self : G (h i) = a • h i
  on_complementary_diagonal : ∀ j : Fin 3, i ≠ j →
    G (h j + (1/2 : ℝ) • h i) = b • (h j + (1/2 : ℝ) • h i)
  on_X : ∀ k u, G (X k u) = (if i = k then b else c) • X k u

abbrev ThreeFrameScalarData (B : SymmetricCubic) :=
  (i : Fin 3) → FrameScalarData (KB B (h i)) i

/-- Distinct actual h_i are independent, proved by their native diagonal values. -/
theorem h_pair_coefficients (i j : Fin 3) (hij : i ≠ j)
    (u v r s : ℝ) (heq : u • h i + v • h j = r • h i + s • h j) :
    u = r ∧ v = s := by
  have h0 := congrArg (fun x : V => (x : Albert).d0) heq
  have h1 := congrArg (fun x : V => (x : Albert).d1) heq
  have h2 := congrArg (fun x : V => (x : Albert).d2) heq
  fin_cases i <;> fin_cases j
  all_goals first | exact False.elim (hij rfl) | skip
  all_goals norm_num [h, e, unit] at h0 h1 h2
  all_goals constructor <;> linarith

/-- The complementary diagonal action gives the actual cross-h formula. -/
theorem ThreeFrameScalarData.cross_h {B : SymmetricCubic}
    (data : ThreeFrameScalarData B) (i j : Fin 3) (hij : i ≠ j) :
    KB B (h i) (h j) =
      (data i).b • h j + (((data i).b - (data i).a)/2) • h i := by
  calc
    KB B (h i) (h j) =
        KB B (h i) (h j + (1/2 : ℝ) • h i) -
          (1/2 : ℝ) • KB B (h i) (h i) := by
      rw [map_add, map_smul]
      module
    _ = (data i).b • (h j + (1/2 : ℝ) • h i) -
        (1/2 : ℝ) • ((data i).a • h i) := by
      rw [(data i).on_complementary_diagonal j hij, (data i).on_h_self]
    _ = _ := by module

/-- Actual cubic symmetry forces the two diagonal coefficients to agree. -/
theorem ThreeFrameScalarData.a_eq_b_sub_two_b {B : SymmetricCubic}
    (data : ThreeFrameScalarData B) (i j : Fin 3) (hij : i ≠ j) :
    (data i).a = (data i).b - 2 * (data j).b := by
  have hcross := KB_comm B (h i) (h j)
  rw [data.cross_h i j hij, data.cross_h j i hij.symm, add_comm] at hcross
  have hc := (h_pair_coefficients i j hij
    (((data i).b - (data i).a)/2) ((data i).b) ((data j).b)
    (((data j).b - (data j).a)/2) hcross).1
  linarith

/-- h0+h1+h2=0 gives a sum of actual unknown multiplication operators. -/
theorem KB_h_sum_zero (B : SymmetricCubic) (v : V) :
    KB B (h 0) v + KB B (h 1) v + KB B (h 2) v = 0 := by
  have hs := congrArg (fun x : V => KB B x v) h_sum_zero
  simpa only [map_add, LinearMap.add_apply, map_zero, LinearMap.zero_apply] using hs

/-- The three literal raw-slot scalar equations use native octScalar1, not the
inherited unit on a pair of quaternions. -/
theorem ThreeFrameScalarData.slot_relations {B : SymmetricCubic}
    (data : ThreeFrameScalarData B) :
    (data 0).c + (data 1).c + (data 2).b = 0 ∧
      (data 0).c + (data 1).b + (data 2).c = 0 ∧
      (data 0).b + (data 1).c + (data 2).c = 0 := by
  have hs (k : Fin 3) :
      (if 0 = k then (data 0).b else (data 0).c) +
      (if 1 = k then (data 1).b else (data 1).c) +
      (if 2 = k then (data 2).b else (data 2).c) = 0 := by
    have hh := KB_h_sum_zero B (X k (octScalar 1))
    simp only [(data 0).on_X, (data 1).on_X, (data 2).on_X,
      ← add_smul] at hh
    apply (smul_eq_zero.mp hh).resolve_right
    fin_cases k <;> intro hz <;>
      have hx := congrArg (fun x : V => (x : Albert)) hz
    all_goals simp [X, X01, X02, X12, octScalar, Albert.ext_iff, Prod.ext_iff] at hx
  exact ⟨hs 2, hs 1, hs 0⟩

/-- The actual three-frame equations force one common coefficient and the
reference ratio (-1,1,-1/2). This is an intermediate data theorem; the data
must still be derived from the Jacobi kernel, not assumed as a final endpoint. -/
theorem ThreeFrameScalarData.common_coefficients {B : SymmetricCubic}
    (data : ThreeFrameScalarData B) :
    ∃ b : ℝ, (∀ i, (data i).a = -b) ∧ (∀ i, (data i).b = b) ∧
      (∀ i, (data i).c = -b/2) := by
  have hab := data.a_eq_b_sub_two_b
  norm_num [Fin.forall_fin_succ] at hab
  obtain ⟨hc01, hc02, hc12⟩ := data.slot_relations
  refine ⟨(data 0).b, ?_, ?_, ?_⟩ <;>
    intro i <;> fin_cases i <;> linarith!

end
end AlbertRecognition.FixedFrame
