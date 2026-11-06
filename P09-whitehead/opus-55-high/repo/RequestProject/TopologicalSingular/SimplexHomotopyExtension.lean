import RequestProject.TopologicalSingular.SimplexPrismRetraction
noncomputable section


namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

def simplexPrismBoundaryValue (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (w : simplexPrismSide n) : X := by
  classical
  exact if h : w.val.2 ∈ simplexBoundary n then H (w.val.1, ⟨w.val.2, h⟩) else f w.val.2

theorem simplexPrismBoundaryValue_bottom f
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z, H (0, z) = f z)
    w (hw : w.val.1 = 0) : simplexPrismBoundaryValue f H w = f w.val.2 := by
  classical
  unfold simplexPrismBoundaryValue
  simp_all

theorem simplexPrismBoundaryValue_side f
    (H : C(I × simplexBoundary n, X)) w
    hw :
    simplexPrismBoundaryValue f H w = H (w.val.1, ⟨w.val.2, hw⟩) := by
  classical
  simp [simplexPrismBoundaryValue, dif_pos hw]

theorem simplexPrismBoundaryValue_continuous f
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z, H (0, z) = f z) :
    Continuous (simplexPrismBoundaryValue f H) := by
  let S : Set (simplexPrismSide n) := {w | w.val.1 = 0}
  let T : Set (simplexPrismSide n) := {w | w.val.2 ∈ simplexBoundary n}
  have hS : IsClosed S := isClosed_eq continuous_subtype_val.fst continuous_const
  have hT : IsClosed T := (simplexBoundary_isClosed n).preimage continuous_subtype_val.snd
  have hu : S ∪ T = Set.univ := by
    aesop
  have hcS : ContinuousOn (simplexPrismBoundaryValue f H) S := by
    apply (f.continuous.comp continuous_subtype_val.snd).continuousOn.congr
    intro w hw
    exact simplexPrismBoundaryValue_bottom f H hH w hw
  have hcT : ContinuousOn (simplexPrismBoundaryValue f H) T := by
    rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous (fun w : T => H (w.val.val.1, ⟨w.val.val.2, w.property⟩)) := by
      fun_prop
    convert hc using 1
    funext w
    exact simplexPrismBoundaryValue_side f H w.val w.property
  rw [← continuousOn_univ, ← hu]
  exact hcS.union_of_isClosed hcT hS hT

/-- Glue the prescribed initial map and the prescribed boundary homotopy. -/
def simplexPrismBoundaryMap (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z, H (0, z) = f z) :
    C(simplexPrismSide n, X) :=
  ⟨simplexPrismBoundaryValue f H, simplexPrismBoundaryValue_continuous f H hH⟩

/-- Extension over the entire simplex prism. -/
def simplexHomotopyExtension (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z, H (0, z) = f z) :=
  (simplexPrismBoundaryMap f H hH).comp (simplexPrismRetraction n)

theorem simplexHomotopyExtension_zero f
    (H : C(I × simplexBoundary n, X)) hH
    z : simplexHomotopyExtension f H hH (0, z) = f z := by
  have he := simplexPrismRetraction_fixes (0, z) (Or.inl rfl)
  change simplexPrismBoundaryValue f H (simplexPrismRetraction n (0, z)) = _
  rw [simplexPrismBoundaryValue_bottom f H hH _ (congrArg Prod.fst he)]
  simp_all

theorem simplexHomotopyExtension_boundary f
    (H : C(I × simplexBoundary n, X)) hH
    t z : simplexHomotopyExtension f H hH (t, z.val) = H (t, z) := by
  have he := simplexPrismRetraction_fixes (t, z.val) (Or.inr z.property)
  have hz : (simplexPrismRetraction n (t, z.val)).val.2 ∈ simplexBoundary n := by
    simp_all
  change simplexPrismBoundaryValue f H (simplexPrismRetraction n (t, z.val)) = _
  rw [simplexPrismBoundaryValue_side f H _ hz]
  simp_all

/-- The standard topological simplex has the homotopy extension property
relative to its entire boundary, with no restriction on the target space. -/
theorem simplex_homotopy_extension (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z, H (0, z) = f z) :
    ∃ g, ∃ F : f.Homotopy g,
      ∀ t z, F (t, z.val) = H (t, z) := by
  let E := simplexHomotopyExtension f H hH
  let g : C(Domain n, X) := ⟨fun z => E (1, z), E.continuous.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨g, {
    toContinuousMap := E
    map_zero_left := simplexHomotopyExtension_zero f H hH
    map_one_left := fun _ => rfl }, ?_⟩
  exact simplexHomotopyExtension_boundary f H hH
