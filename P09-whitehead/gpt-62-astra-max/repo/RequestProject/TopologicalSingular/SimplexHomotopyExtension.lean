module

public import RequestProject.TopologicalSingular.SimplexPrismRetraction

@[expose] public section

noncomputable section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

variable (f : C(Domain n, X)) (H : C(I × simplexBoundary n, X))

def simplexPrismBoundaryValue (w : simplexPrismSide n) : X := by
  classical
  exact if h : w.val.2 ∈ simplexBoundary n then H (w.val.1, ⟨w.val.2, h⟩) else f w.val.2

theorem simplexPrismBoundaryValue_bottom (hH : ∀ z : simplexBoundary n, H (0, z) = f z)
    (w : simplexPrismSide n) (hw : w.val.1 = 0) : simplexPrismBoundaryValue f H w = f w.val.2 := by
  classical
  unfold simplexPrismBoundaryValue
  split_ifs with h
  · rw [hw]
    apply hH
  · rfl

theorem simplexPrismBoundaryValue_side (w : simplexPrismSide n)
    (hw : w.val.2 ∈ simplexBoundary n) :
    simplexPrismBoundaryValue f H w = H (w.val.1, ⟨w.val.2, hw⟩) := by
  simp_all [simplexPrismBoundaryValue, dif_pos]

section

variable (hH : ∀ z : simplexBoundary n, H (0, z) = f z)
include hH

theorem simplexPrismBoundaryValue_continuous :
    Continuous (simplexPrismBoundaryValue f H) := by
  let S : Set (simplexPrismSide n) := {w | w.val.1 = 0}
  let T : Set (simplexPrismSide n) := {w | w.val.2 ∈ simplexBoundary n}
  have hS : IsClosed S := isClosed_eq continuous_subtype_val.fst continuous_const
  have hT : IsClosed T := (simplexBoundary_isClosed n).preimage continuous_subtype_val.snd
  have hu : S ∪ T = Set.univ := by
    ext w
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact w.property
  have hcS : ContinuousOn (simplexPrismBoundaryValue f H) S := by
    apply (f.continuous.comp continuous_subtype_val.snd).continuousOn.congr
    apply simplexPrismBoundaryValue_bottom <;> assumption
  have hcT : ContinuousOn (simplexPrismBoundaryValue f H) T := by
    rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous (fun w : T => H (w.val.val.1, ⟨w.val.val.2, w.property⟩)) := by
      apply H.continuous.comp
      fun_prop
    convert hc using 1
    funext w
    apply simplexPrismBoundaryValue_side
  rw [← continuousOn_univ, ← hu]
  apply hcS.union_of_isClosed <;> assumption

/-- Glue the prescribed initial map and the prescribed boundary homotopy. -/
def simplexPrismBoundaryMap :
    C(simplexPrismSide n, X) :=
  ⟨simplexPrismBoundaryValue f H, simplexPrismBoundaryValue_continuous f H hH⟩

end

/-- Extension over the entire simplex prism. -/
def simplexHomotopyExtension (hH : ∀ z, H (0, z) = f z) :
    C(I × Domain n, X) :=
  (simplexPrismBoundaryMap f H hH).comp (simplexPrismRetraction n)

variable (hH : ∀ z : simplexBoundary n, H (0, z) = f z)
include hH

theorem simplexHomotopyExtension_zero
    (z : Domain n) : simplexHomotopyExtension f H hH (0, z) = f z := by
  have he := simplexPrismRetraction_fixes (0, z) (Or.inl rfl)
  change simplexPrismBoundaryValue f H _ = _
  rw [simplexPrismBoundaryValue_bottom f H hH _ (congrArg Prod.fst he)]
  rw [congrArg Prod.snd he]

theorem simplexHomotopyExtension_boundary
    (t : I) (z : simplexBoundary n) : simplexHomotopyExtension f H hH (t, z.val) = H (t, z) := by
  have he := simplexPrismRetraction_fixes (t, z.val) (Or.inr z.property)
  have hz : (simplexPrismRetraction n (t, z.val)).val.2 ∈ simplexBoundary n := by
    rw [congrArg Prod.snd he]
    exact z.property
  change simplexPrismBoundaryValue f H _ = _
  rw [simplexPrismBoundaryValue_side f H _ hz]
  apply congrArg H
  apply Prod.ext
  · exact congrArg (fun w : I × Domain n => w.1) he
  · exact Subtype.ext (congrArg (fun w : I × Domain n => w.2) he)

/-- The standard topological simplex has the homotopy extension property
relative to its entire boundary, with no restriction on the target space. -/
theorem simplex_homotopy_extension :
    ∃ g : C(Domain n, X), ∃ F : f.Homotopy g,
      ∀ (t : I) (z : simplexBoundary n), F (t, z.val) = H (t, z) := by
  let E := simplexHomotopyExtension f H hH
  refine ⟨(⟨fun z => E _, E.continuous.comp (continuous_const.prodMk continuous_id)⟩), {
    toContinuousMap := E
    map_zero_left := simplexHomotopyExtension_zero f H hH
    map_one_left := fun _ => rfl }, ?_⟩
  apply simplexHomotopyExtension_boundary

end FiniteChains.TopologicalSingular
