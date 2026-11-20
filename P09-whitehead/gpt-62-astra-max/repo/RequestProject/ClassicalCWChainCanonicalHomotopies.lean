module


public import RequestProject.ClassicalCWChainCanonicalWords
public import RequestProject.PresWordDiskComparisonNaturality

@[expose] public section

/-! Canonical attaching homotopies are chosen once, when a cell first
appears, and pushed through the later generator inclusions. Consequently
the actual disk-model comparisons form commuting squares. Unverified. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel
open Set Topology
open scoped Classical unitInterval ContinuousMap
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C]
  [TreeChoice K C]

def canonicalCellBoundary (i : Fin _) (j : CanonicalRel K C i) :=
  classicalPresCellBoundary _ j
    (canonicalWords_ne_nil K C hC hconn i)

theorem canonicalCellBoundary_natural {i k : Fin _} (hik : i ≤ k)
    (j : CanonicalRel K C i) :
    (diskRoseMap (canonicalGenInclusion K C hC hconn hik)).comp
        (canonicalCellBoundary K C hC hconn i j) =
      canonicalCellBoundary K C hC hconn k (canonicalCellInclusion K C hC hik j) := by
  ext a
  exact (canonicalWordEmbedding K C hC hconn hik).classicalPresWordAttaching_natural
    _ _ _

abbrev CanonicalTopCell := TopCell C ⊕ PUnit.{1}

def canonicalTopCell (i : Fin _) : CanonicalRel K C i → CanonicalTopCell K C
  | .inl j => .inl (topCell C hC i j)
  | .inr u => .inr u

def canonicalBirth : CanonicalTopCell K C → Fin (n + 1)
  | .inl j => birth C j
  | .inr _ => 0

def canonicalBirthCell (j : CanonicalTopCell K C) : CanonicalRel K C (canonicalBirth K C j) :=
  match j with
  | .inl j => .inl (birthCell C j)
  | .inr u => .inr u

variable (i : Fin (n + 1)) (j : CanonicalRel K C i)

omit [Choices C] [TreeChoice K C] in
theorem canonicalBirth_le :
    canonicalBirth K C (canonicalTopCell K C hC i j) ≤ i := by
  cases j with
  | inl j => exact birth_le C _ i j.property
  | inr u => exact Fin.zero_le _

omit [Choices C] [TreeChoice K C] in
theorem canonicalBirthCell_image :
    canonicalCellInclusion K C hC (canonicalBirth_le K C hC i j)
      (canonicalBirthCell K C (canonicalTopCell K C hC i j)) = j := by
  cases j <;> rfl

def canonicalBirthHomotopy (j : CanonicalTopCell K C) :
    (stabilizedCellBoundary K C hC hconn _ (canonicalBirthCell K C j)).Homotopy
      (canonicalCellBoundary K C hC hconn (canonicalBirth K C j) (canonicalBirthCell K C j)) :=
  Classical.choice (stabilizedCellBoundary_homotopic K C hC hconn
    (canonicalBirth K C j) (canonicalBirthCell K C j))

def canonicalCellHomotopy (i : Fin _) (j : CanonicalRel K C i) :
    (stabilizedCellBoundary K C hC hconn i j).Homotopy
      (canonicalCellBoundary K C hC hconn i j) where
  toContinuousMap := (diskRoseMap
    (canonicalGenInclusion K C hC hconn (canonicalBirth_le K C hC i j))).comp
      (canonicalBirthHomotopy K C hC hconn (canonicalTopCell K C hC i j)).toContinuousMap
  map_zero_left a := by
    change diskRoseMap _ _ = _
    have H := congrArg (fun f => f a) (stabilizedCellBoundary_natural K C hC hconn
      (canonicalBirth_le K C hC i j) (canonicalBirthCell K C (canonicalTopCell K C hC i j)))
    simp_all [canonicalBirthCell_image]
  map_one_left a := by
    change diskRoseMap _ _ = _
    have H := congrArg (fun f => f a) (canonicalCellBoundary_natural K C hC hconn
      (canonicalBirth_le K C hC i j) (canonicalBirthCell K C (canonicalTopCell K C hC i j)))
    simp_all [canonicalBirthCell_image]

theorem canonicalCellHomotopy_natural {i k : Fin _} (hik : i ≤ k)
    (j : CanonicalRel K C i) (t : I) (a : UnitBoundary (Fin 2 → ℝ)) :
    diskRoseMap (canonicalGenInclusion K C hC hconn hik)
        (canonicalCellHomotopy K C hC hconn i j (t, a)) =
      canonicalCellHomotopy K C hC hconn k (canonicalCellInclusion K C hC hik j) (t, a) := by
  have he : (canonicalGenInclusion K C hC hconn hik ∘
      canonicalGenInclusion K C hC hconn (canonicalBirth_le K C hC i j)) =
      canonicalGenInclusion K C hC hconn ((canonicalBirth_le K C hC i j).trans hik) := by
    funext b
    apply canonicalGenInclusion_comp
  have H := congrArg (fun f => f (canonicalBirthHomotopy K C hC hconn
    (canonicalTopCell K C hC i j) (t, a)))
      ((diskRoseMap_comp _ _).trans (congrArg diskRoseMap he))
  cases j with
  | inl j => exact H
  | inr u => exact H

variable (i : Fin (n + 1))

def canonicalAttaching :=
  classicalPresWordAttaching _ (canonicalWords_ne_nil K C hC hconn i)

def canonicalAttachingHomotopy :
    (stabilizedAttaching K C hC hconn i).Homotopy (canonicalAttaching K C hC hconn i) := by
  let H j := canonicalCellHomotopy K C hC hconn i j
  exact FiniteChains.sigmaHomotopy H

def canonicalDiskChange :
    DiskAttachment (stabilizedAttaching K C hC hconn i) ≃ₕ
      ClassicalPresWordDisks _ (canonicalWords_ne_nil K C hC hconn i) :=
  naturalDiskAttachingEquiv _ _ (canonicalAttachingHomotopy K C hC hconn i)

variable {i k : Fin (n + 1)} (hik : i ≤ k)

def stabilizedDiskInclusion :=
  StabilizedDiskPresentation.map _
    _
    _ _
    (fun z => collapsedAttaching_natural K C hC hconn hik z.1 z.2)

def canonicalDiskInclusion :=
  (canonicalWordEmbedding K C hC hconn hik).classicalWordDiskMap
    (canonicalWords_ne_nil K C hC hconn i) (canonicalWords_ne_nil K C hC hconn k)

theorem canonicalDiskChange_natural :
    (canonicalDiskInclusion K C hC hconn hik).comp (canonicalDiskChange K C hC hconn i).toFun =
      (canonicalDiskChange K C hC hconn k).toFun.comp (stabilizedDiskInclusion K C hC hconn hik) := by
  have H := naturalDiskAttachingEquiv_natural
    _ _
    (canonicalAttachingHomotopy K C hC hconn i)
    _ _
    (canonicalAttachingHomotopy K C hC hconn k)
    _
    _
    (fun j a => congrArg (fun f => f a) (stabilizedCellBoundary_natural K C hC hconn hik j))
    (fun j a => congrArg (fun f => f a) (canonicalCellBoundary_natural K C hC hconn hik j))
    (fun t j a => canonicalCellHomotopy_natural K C hC hconn hik j t a)
  assumption

theorem canonicalDiskInclusion_killsPi2_iff :
    Whitehead.KillsPi2 (canonicalDiskInclusion K C hC hconn hik) ↔
      Whitehead.KillsPi2 (⟨Set.inclusion _, continuous_inclusion (hC hik)⟩) := by
  have h₁ : Whitehead.KillsPi2 (canonicalDiskInclusion K C hC hconn hik) ↔
      Whitehead.KillsPi2 (stabilizedDiskInclusion K C hC hconn hik) := by
    apply Whitehead.killsPi2_homotopyEquiv_square_iff
      (canonicalDiskChange K C hC hconn i) (canonicalDiskChange K C hC hconn k)
    erw [canonicalDiskChange_natural]
  have he : DiskPresentationExtension.sourceMap _
      _ _
      _
      (fun z => collapsedAttaching_natural K C hC hconn hik z.1 z.2) =
      collapsedDiskInclusion K C hC hconn hik := by
    apply hom_ext _ (boundaryFamilyInclusion _ _)
    · solve_by_elim
    · solve_by_elim
  exact h₁.trans ((StabilizedDiskPresentation.map_killsPi2_iff _ _ _ _ _).trans
    (he ▸ collapsedDiskInclusion_killsPi2_iff K C hC hconn hik))

end FiniteChains.ClassicalCW.ChainWords
