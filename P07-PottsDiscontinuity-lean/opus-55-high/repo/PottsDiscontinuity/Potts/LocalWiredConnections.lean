module

public import PottsDiscontinuity.FK.Wiring
public import PottsDiscontinuity.Potts.GhostBoxGeometry
public import PottsDiscontinuity.Potts.MergedConnectionData

/-! Finite wired connection graphs bracket the merged infinite relation. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical
noncomputable section

section
variable (n : ℕ)
/-- Restrict to the box and identify every exterior vertex with the ghost. -/
def boxGhostProjection  : Option (ℤ × ℤ) → Option ↥(box n : Set (ℤ × ℤ))
  | none => none
  | some x => if hx : x ∈ box n then some ⟨x, hx⟩ else none

def boxGhostLift  : Option ↥(box n : Set (ℤ × ℤ)) → Option (ℤ × ℤ) :=
  Option.map Subtype.val
end

/-- The actual induced open graph, with every boundary vertex joined to one ghost. -/
def finiteWiredConnectionGraph (H : SimpleGraph (ℤ × ℤ)) (n : ℕ) :
    SimpleGraph (Option ↥(box n : Set (ℤ × ℤ))) where
  Adj
    | none, none => False
    | some x, some y => H.Adj x.val y.val
    | some x, none => x.val ∈ vertexBoundary (box n)
    | none, some y => y.val ∈ vertexBoundary (box n)
  symm := by
    constructor
    intro x y hxy
    cases x <;> cases y
    · omega
    · omega
    · omega
    · exact hxy.symm
  loopless := by
    constructor
    grind

section
variable (H : SimpleGraph (ℤ × ℤ))
/-- The finite wired partition read on the whole lattice and its ghost. -/
def localWiredSetoid (n : ℕ) : Setoid (Option (ℤ × ℤ)) :=
  (finiteWiredConnectionGraph H n).reachableSetoid.comap (boxGhostProjection n)

theorem localWiredSetoid_adj (hH : H ≤ squareLattice)
    (n : ℕ) {x y : ℤ × ℤ} (hxy : H.Adj x y) :
    localWiredSetoid H n (some x) (some y) := by
  change (finiteWiredConnectionGraph H n).Reachable
    (boxGhostProjection n (some x)) (boxGhostProjection n (some y))
  by_cases hx : x ∈ box n <;> by_cases hy : y ∈ box n
  · simp only [boxGhostProjection, hx, hy, dite_true]
    exact (show (finiteWiredConnectionGraph H n).Adj (some ⟨x, hx⟩) (some ⟨y, hy⟩) from hxy).reachable
  · simp only [boxGhostProjection, hx, hy, dite_true, dite_false]
    exact (show (finiteWiredConnectionGraph H n).Adj (some ⟨x, hx⟩) none from
      ⟨hx, y, hH hxy, hy⟩).reachable
  · simp only [boxGhostProjection, hx, hy, dite_true, dite_false]
    exact (show (finiteWiredConnectionGraph H n).Adj none (some ⟨y, hy⟩) from
      ⟨hy, x, (hH hxy).symm, hx⟩).reachable
  simp_all [boxGhostProjection]

theorem localWiredSetoid_of_reachable (hH : H ≤ squareLattice)
    (n : ℕ) {x y : ℤ × ℤ} (hxy : H.Reachable x y) :
    localWiredSetoid H n (some x) (some y) := by
  have hle : H.reachableSetoid ≤ (localWiredSetoid H n).comap some :=
    FK.reachableSetoid_le_of_adj H _ (fun h => localWiredSetoid_adj H hH n h)
  tauto

theorem localWiredSetoid_of_outside (n : ℕ)
    {x : ℤ × ℤ} (hx : x ∉ box n) : localWiredSetoid H n (some x) none := by
  change (finiteWiredConnectionGraph H n).Reachable
    (boxGhostProjection n (some x)) (boxGhostProjection n none)
  simp_all [boxGhostProjection]

theorem localWiredSetoid_of_escape (hH : H ≤ squareLattice)
    (n : ℕ) {x : ℤ × ℤ} (hx : clusterEscapesBox H n x) :
    localWiredSetoid H n (some x) none := by
  obtain ⟨y, hy, hxy⟩ := hx
  exact (localWiredSetoid H n).trans (localWiredSetoid_of_reachable H hH n hxy)
    (localWiredSetoid_of_outside H n hy)

/-- Merging the actual exterior can only add fewer connections than wiring
all vertices on the finite box boundary. -/
theorem exteriorMergedSetoid_le_localWired (hH : H ≤ squareLattice)
    (n : ℕ) : exteriorMergedSetoid H n ≤ localWiredSetoid H n := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some y =>
      have hy := markedClusterSetoid_some_none _ _ y |>.mp
        ((exteriorMergedSetoid H n).symm hab)
      exact (localWiredSetoid H n).symm (localWiredSetoid_of_escape H hH n hy)
  | some x =>
    cases b with
    | none =>
      exact localWiredSetoid_of_escape H hH n ((markedClusterSetoid_some_none _ _ x).mp hab)
    | some y =>
      rcases (exteriorMergedSetoid_some_some H n x y).mp hab with hxy | ⟨hx, hy⟩
      · simp_all [localWiredSetoid_of_reachable]
      · exact (localWiredSetoid H n).trans (localWiredSetoid_of_escape H hH n hx)
          ((localWiredSetoid H n).symm (localWiredSetoid_of_escape H hH n hy))

theorem finiteWired_reachable_le_exterior (n : ℕ) :
    (finiteWiredConnectionGraph H (n + 1)).reachableSetoid ≤
      (exteriorMergedSetoid H n).comap (boxGhostLift (n + 1)) := by
  apply FK.reachableSetoid_le_of_adj
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some y =>
      apply (exteriorMergedSetoid H n).symm
      exact (markedClusterSetoid_some_none _ _ _).mpr ⟨y.val, ((outer_shell_iff_boundary n y.val y.property).mpr hab), .refl _⟩
  | some x =>
    cases b with
    | none =>
      exact (markedClusterSetoid_some_none _ _ _).mpr ⟨x.val, ((outer_shell_iff_boundary n x.val x.property).mpr hab), .refl _⟩
    | some y => exact (exteriorMergedSetoid_some_some H n x.val y.val).mpr (Or.inl (show H.Adj x.val y.val from hab).reachable)

theorem exterior_related_projection (n : ℕ)
    (a : Option (ℤ × ℤ)) :
    exteriorMergedSetoid H n a (boxGhostLift (n + 1) (boxGhostProjection (n + 1) a)) := by
  cases a with
  | none => rfl
  | some x =>
    by_cases hx : x ∈ box (n + 1)
    · simp_all [boxGhostProjection, boxGhostLift]
    · simp only [boxGhostProjection, hx, dite_false, boxGhostLift, Option.map_none]
      exact (markedClusterSetoid_some_none _ _ _).mpr ⟨x, (fun h => hx (box_subset_box_succ n h)), .refl _⟩

/-- Wiring the larger box adds no connections beyond merging all components
which reach the exterior of the smaller box. -/
theorem localWiredSetoid_succ_le_exterior (n : ℕ) :
    localWiredSetoid H (n + 1) ≤ exteriorMergedSetoid H n := by
  intro a b hab
  exact (exteriorMergedSetoid H n).trans (exterior_related_projection H n a)
    ((exteriorMergedSetoid H n).trans (finiteWired_reachable_le_exterior H n hab)
      ((exteriorMergedSetoid H n).symm (exterior_related_projection H n b)))

/-- The finite wired partitions have precisely the merged infinite limit. -/
theorem localWiredSetoid_limit (hH : H ≤ squareLattice)
    (a b : Option (ℤ × ℤ)) :
    (∀ n, localWiredSetoid H n a b) ↔ infiniteMergedSetoid H a b := by
  constructor
  · intro h
    apply (exteriorMergedSetoid_limit H a b).mp
    intro n
    exact localWiredSetoid_succ_le_exterior H n (h (n + 1))
  · intro h n
    exact exteriorMergedSetoid_le_localWired H hH n ((exteriorMergedSetoid_limit H a b).mpr h n)

theorem localWiredSetoid_antitone (hH : H ≤ squareLattice) :
    Antitone (localWiredSetoid H) := by
  apply antitone_nat_of_succ_le
  grind [localWiredSetoid_succ_le_exterior, exteriorMergedSetoid_le_localWired]
end

theorem localWiredSetoid_mono {H K : SimpleGraph (ℤ × ℤ)} (h : H ≤ K) (n : ℕ) :
    localWiredSetoid H n ≤ localWiredSetoid K n := by
  have hg : finiteWiredConnectionGraph H n ≤ finiteWiredConnectionGraph K n := by
    intro a b hab
    cases a <;> cases b
    · simp_all
    · tauto
    · tauto
    tauto
  intro a b hab
  exact hab.mono hg

end
end PottsDiscontinuity.Potts
