module

public import NearlyMinimax.HistoryCoordinateTransport
public import NearlyMinimax.HistoryMaximalDelete


@[expose] public section

/-!
# Actual independent mark insertion and canonical append coordinates
-/

noncomputable section
open MeasureTheory
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

omit [Fintype J] [LinearOrder J] in
/-- The canonical appended word carries the same actual labelled dependency heap. -/
theorem historyCanonicalAppendHeapIso_exists (dependent : J → J → Prop)
    [Std.Symm dependent]
    (j : J) (g : DependenceHeap dependent) :
    ∃ e : WordHeapPiece (g.out ++ [j]) dependent ≃o
        WordHeapPiece (historyShapeAppend j g).out dependent,
      ∀ x, wordHeapLabel (e x) = wordHeapLabel x := by
  exact historyShapeRelation_heapIso (Quotient.exact ((congrArg (historyShapeAppend j) (Quotient.out_eq g)).trans (Quotient.out_eq _).symm))

/-- Choose once an actual representative coordinate transport, not a law or score bound. -/
def historyCanonicalAppendHeapIso {dependent : J → J → Prop}
    [Std.Symm dependent]
    (j : J) (g : DependenceHeap dependent) :
    WordHeapPiece (g.out ++ [j]) dependent ≃o
      WordHeapPiece (historyShapeAppend j g).out dependent :=
  (historyCanonicalAppendHeapIso_exists dependent j g).choose

omit [Fintype J] [LinearOrder J] in
theorem historyCanonicalAppendHeapIso_label (dependent : J → J → Prop)
    [Std.Symm dependent]
    (j : J) (g : DependenceHeap dependent) (x : WordHeapPiece (g.out ++ [j]) dependent) :
    wordHeapLabel (historyCanonicalAppendHeapIso j g x) = wordHeapLabel x :=
  (historyCanonicalAppendHeapIso_exists dependent j g).choose_spec x

section
variable (n : ℕ) {E : Type*} [MeasurableSpace E]

/-- Insert one genuinely independent mark at the last finite coordinate. -/
def historyFiniteMarkAppendEquiv :
    E × (Fin n → E) ≃ᵐ (Fin (n + 1) → E) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => E) (Fin.last n)).symm

theorem historyFiniteMarkAppendEquiv_preserving
    (π : Measure E) [IsProbabilityMeasure π] :
    MeasurePreserving (historyFiniteMarkAppendEquiv n)
      (π.prod (Measure.pi (fun _ => π))) (Measure.pi (fun _ => π)) :=
  (measurePreserving_piFinSuccAbove (fun _ => π) (Fin.last n)).symm _

end

section
variable {dependent : J → J → Prop} [Std.Symm dependent] (j : J) (g : DependenceHeap dependent)
    {E : Type*}

/-- The real position bijection from old coordinates plus a fresh last coordinate to the canonical append. -/
def historyCanonicalAppendCoordinates :
    Fin (historyShapeLength g + 1) ≃ Fin (historyShapeLength (historyShapeAppend j g)) :=
  (finCongr (by rw [historyShapeLength_out]; simp)).trans
    ((historyHeapCoordinateEquiv (historyCanonicalAppendHeapIso j g)).trans
      (finCongr (historyShapeLength_out (historyShapeAppend j g)).symm))

/-- Actual independent insertion followed by the actual canonical heap-coordinate permutation. -/
def historyCanonicalMarkAppendEquiv [MeasurableSpace E] :
    E × (Fin (historyShapeLength g) → E) ≃ᵐ
      (Fin (historyShapeLength (historyShapeAppend j g)) → E) :=
  (historyFiniteMarkAppendEquiv (historyShapeLength g)).trans
    (MeasurableEquiv.piCongrLeft (fun _ => E) (historyCanonicalAppendCoordinates j g))

/-- The actual canonical append adds precisely one independent pi mark. -/
theorem historyCanonicalMarkAppendEquiv_preserving [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    MeasurePreserving (historyCanonicalMarkAppendEquiv j g)
      (π.prod (Measure.pi (fun _ => π)))
      (Measure.pi (fun _ => π)) :=
  (measurePreserving_piCongrLeft (fun _ => π) (historyCanonicalAppendCoordinates j g)).comp
    (historyFiniteMarkAppendEquiv_preserving _ π)

/-- The actual maximal piece corresponding to the freshly appended update. -/
def historyCanonicalAppendedPiece :
    WordHeapPiece (historyShapeAppend j g).out dependent :=
  historyCanonicalAppendHeapIso j g (wordHeapAppendedPiece g.out dependent j)

end

omit [Fintype J] [LinearOrder J] in
theorem historyCanonicalAppendedPiece_maximal (dependent : J → J → Prop)
    [Std.Symm dependent]
    (j : J) (g : DependenceHeap dependent) :
    historyCanonicalAppendedPiece j g ∈ historyMaximalPieces Finset.univ := by
  let e := historyCanonicalAppendHeapIso j g
  have hx : e (wordHeapAppendedPiece ..) ∈ historyMaximalPieces
      (Finset.univ.map e.toEquiv.toEmbedding) := by
    rw [historyMaximalPieces_orderIso_map]
    exact Finset.mem_map.2 ⟨_, wordHeapAppendedPiece_maximal .., rfl⟩
  rw [Finset.map_univ_equiv e.toEquiv] at hx
  exact hx

omit [Fintype J] [LinearOrder J] in
@[simp] theorem historyCanonicalAppendedPiece_label (dependent : J → J → Prop)
    [Std.Symm dependent]
    (j : J) (g : DependenceHeap dependent) :
    wordHeapLabel (historyCanonicalAppendedPiece j g) = j :=
  (historyCanonicalAppendHeapIso_label dependent j g _).trans
    (wordHeapAppendedPiece_label ..)

variable {dependent : J → J → Prop}

/-- The freshly added coordinate in the canonical marked-history fiber. -/
def historyCanonicalFreshCoordinate
    [Std.Symm dependent]
    (j : J) (g : DependenceHeap dependent) :
    Fin (historyShapeLength (historyShapeAppend j g)) :=
  Fin.cast (historyShapeLength_out (historyShapeAppend j g)).symm
    (historyCanonicalAppendedPiece j g).position

theorem historyCanonicalAppendCoordinates_last (dependent : J → J → Prop)
    [Std.Symm dependent]
    (j : J) (g : DependenceHeap dependent) :
    historyCanonicalAppendCoordinates j g (Fin.last (historyShapeLength g)) =
      historyCanonicalFreshCoordinate j g := by
  let hlen : historyShapeLength g + 1 = (g.out ++ [j]).length := by
    rw [historyShapeLength_out]; simp
  have hl : (finCongr hlen) (Fin.last (historyShapeLength g)) =
      (wordHeapAppendedPiece g.out dependent j).position := by
    apply Fin.ext
    exact historyShapeLength_out g
  unfold historyCanonicalAppendCoordinates historyCanonicalFreshCoordinate historyCanonicalAppendedPiece
  simp_all

@[simp] theorem historyFiniteMarkAppendEquiv_last (n : ℕ) {E : Type*} [MeasurableSpace E]
    (fresh : E) (marks : Fin n → E) :
    historyFiniteMarkAppendEquiv n (fresh, marks) (Fin.last n) = fresh := congrArg Prod.fst ((MeasurableEquiv.piFinSuccAbove (fun _ => E) (Fin.last n)).apply_symm_apply (fresh, marks))

/-- The canonical maximal-piece mark is exactly the independent fresh mark, including after reordering. -/
@[simp] theorem historyCanonicalMarkAppendEquiv_fresh
    [Std.Symm dependent]
    (j : J) {g : DependenceHeap dependent} {E : Type*} [MeasurableSpace E]
    (fresh : E) (marks : Fin (historyShapeLength g) → E) :
    historyCanonicalMarkAppendEquiv j g (fresh, marks)
      (historyCanonicalFreshCoordinate j g) = fresh := by
  rw [← historyCanonicalAppendCoordinates_last]
  have hh := MeasurableEquiv.piCongrLeft_apply_apply
    (historyCanonicalAppendCoordinates j g)
    (β := fun _ => E) (historyFiniteMarkAppendEquiv _ (fresh, marks)) (Fin.last _)
  change MeasurableEquiv.piCongrLeft
    (fun _ => E)
    (historyCanonicalAppendCoordinates j g)
    (historyFiniteMarkAppendEquiv _ (fresh, marks))
    (historyCanonicalAppendCoordinates j g (Fin.last (historyShapeLength g))) = fresh
  rw [hh, historyFiniteMarkAppendEquiv_last]

end NearlyMinimax
