module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.ClassicalCWChainCanonicalWords
public import RequestProject.NaturalDiskAttachingEquiv
public import RequestProject.PresWordDiskComparisonNaturality

@[expose] public section

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

def canonicalCellBoundary (i : Fin (n + 1)) (j : CanonicalRel K C i) :=
  classicalPresCellBoundary (canonicalWords K C hC hconn i) j
    (canonicalWords_ne_nil K C hC hconn i)

theorem canonicalCellBoundary_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : CanonicalRel K C i) :
    (diskRoseMap (canonicalGenInclusion K C hC hconn hik)).comp
        (canonicalCellBoundary K C hC hconn i j) =
      canonicalCellBoundary K C hC hconn k (canonicalCellInclusion K C hC hik j) :=
  ContinuousMap.ext fun a => (canonicalWordEmbedding K C hC hconn hik).classicalPresWordAttaching_natural
    (canonicalWords_ne_nil K C hC hconn i) (canonicalWords_ne_nil K C hC hconn k) ⟨j, a⟩

abbrev CanonicalTopCell := TopCell C ⊕ PUnit.{1}

def canonicalTopCell (i : Fin (n + 1)) : CanonicalRel K C i → CanonicalTopCell K C
  | .inl j => .inl (topCell C hC i j)
  | .inr u => .inr u

def canonicalBirth : CanonicalTopCell K C → Fin (n + 1)
  | .inl j => birth C j
  | .inr _ => 0

def canonicalBirthCell (j : CanonicalTopCell K C) : CanonicalRel K C (canonicalBirth K C j) :=
  match j with
  | .inl j => .inl (birthCell C j)
  | .inr u => .inr u

omit [Choices C] [TreeChoice K C] in
theorem canonicalBirth_le (i : Fin (n + 1)) : ∀ j : CanonicalRel K C i,
    canonicalBirth K C (canonicalTopCell K C hC i j) ≤ i
  | .inl j => birth_le C (topCell C hC i j) i j.property
  | .inr _ => Fin.zero_le _

def canonicalBirthHomotopy (j : CanonicalTopCell K C) :
    (stabilizedCellBoundary K C hC hconn (canonicalBirth K C j) (canonicalBirthCell K C j)).Homotopy
      (canonicalCellBoundary K C hC hconn (canonicalBirth K C j) (canonicalBirthCell K C j)) :=
  Classical.choice (stabilizedCellBoundary_homotopic K C hC hconn
    (canonicalBirth K C j) (canonicalBirthCell K C j))

def canonicalCellHomotopy (i : Fin (n + 1)) (j : CanonicalRel K C i) :
    (stabilizedCellBoundary K C hC hconn i j).Homotopy
      (canonicalCellBoundary K C hC hconn i j) where
  toContinuousMap := (diskRoseMap
    (canonicalGenInclusion K C hC hconn (canonicalBirth_le K C hC i j))).comp
      (canonicalBirthHomotopy K C hC hconn (canonicalTopCell K C hC i j)).toContinuousMap
  map_zero_left a := by
    change diskRoseMap _ (canonicalBirthHomotopy K C hC hconn _ (0, a)) = _
    erw [(canonicalBirthHomotopy K C hC hconn _).apply_zero]
    have H := congrArg (fun f => f a) (stabilizedCellBoundary_natural K C hC hconn
      (canonicalBirth_le K C hC i j) (canonicalBirthCell K C (canonicalTopCell K C hC i j)))
    rwa [show canonicalCellInclusion K C hC (canonicalBirth_le K C hC i j)
      (canonicalBirthCell K C (canonicalTopCell K C hC i j)) = j by cases j <;> rfl] at H
  map_one_left a := by
    change diskRoseMap _ (canonicalBirthHomotopy K C hC hconn _ (1, a)) = _
    erw [(canonicalBirthHomotopy K C hC hconn _).apply_one]
    have H := congrArg (fun f => f a) (canonicalCellBoundary_natural K C hC hconn
      (canonicalBirth_le K C hC i j) (canonicalBirthCell K C (canonicalTopCell K C hC i j)))
    rwa [show canonicalCellInclusion K C hC (canonicalBirth_le K C hC i j)
      (canonicalBirthCell K C (canonicalTopCell K C hC i j)) = j by cases j <;> rfl] at H

def canonicalAttaching (i : Fin (n + 1)) :=
  classicalPresWordAttaching (canonicalWords K C hC hconn i) (canonicalWords_ne_nil K C hC hconn i)

def canonicalAttachingHomotopy (i : Fin (n + 1)) :
    (stabilizedAttaching K C hC hconn i).Homotopy (canonicalAttaching K C hC hconn i) := by
  let H j := canonicalCellHomotopy K C hC hconn i j
  let F : C(BoundaryFamily (CanonicalRel K C i) (Fin 2 → ℝ),
      C(I, ClassicalGraphModel.Rose (CanonicalGen K C hC hconn i))) :=
    ⟨fun a => ((H a.1).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry a.2,
      continuous_sigma fun j =>
        ((H j).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry.continuous⟩
  exact {
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := fun a => (H a.1).apply_zero a.2
    map_one_left := fun a => (H a.1).apply_one a.2 }

def canonicalDiskInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :=
  (canonicalWordEmbedding K C hC hconn hik).classicalWordDiskMap
    (canonicalWords_ne_nil K C hC hconn i) (canonicalWords_ne_nil K C hC hconn k)

theorem canonicalDiskInclusion_killsPi2_iff {i k : Fin (n + 1)} (hik : i ≤ k) :
    Whitehead.KillsPi2 (canonicalDiskInclusion K C hC hconn hik) ↔
      Whitehead.KillsPi2 (⟨Set.inclusion (hC hik), continuous_inclusion (hC hik)⟩ :
        C((C i : Set K), (C k : Set K))) := by
  let cDC (m : Fin (n + 1)) :=
    naturalDiskAttachingEquiv _ _ (canonicalAttachingHomotopy K C hC hconn m)
  let sDI := StabilizedDiskPresentation.map (roseGenInclusion K C hC hconn hik)
    (subcomplexCellInclusion (hC hik) 2)
    (collapsedAttaching K C hC hconn i) (collapsedAttaching K C hC hconn k)
    (fun z => collapsedAttaching_natural K C hC hconn hik z.1 z.2)
  have h₁ : Whitehead.KillsPi2 (canonicalDiskInclusion K C hC hconn hik) ↔
      Whitehead.KillsPi2 sDI := by
    apply Whitehead.killsPi2_homotopyEquiv_square_iff (cDC i) (cDC k)
    have H := naturalDiskAttachingEquiv_natural
      (stabilizedAttaching K C hC hconn i) (canonicalAttaching K C hC hconn i)
      (canonicalAttachingHomotopy K C hC hconn i)
      (stabilizedAttaching K C hC hconn k) (canonicalAttaching K C hC hconn k)
      (canonicalAttachingHomotopy K C hC hconn k)
      (diskRoseMap (canonicalGenInclusion K C hC hconn hik))
      (canonicalCellInclusion K C hC hik)
      (fun j a => congrArg (fun f => f a) (stabilizedCellBoundary_natural K C hC hconn hik j))
      (fun j a => congrArg (fun f => f a) (canonicalCellBoundary_natural K C hC hconn hik j))
      (fun t j a => by
        change diskRoseMap _ (diskRoseMap _
            (canonicalBirthHomotopy K C hC hconn (canonicalTopCell K C hC i j) (t, a))) =
          diskRoseMap _ (canonicalBirthHomotopy K C hC hconn
            (canonicalTopCell K C hC k (canonicalCellInclusion K C hC hik j)) (t, a))
        have he : (canonicalGenInclusion K C hC hconn hik ∘
            canonicalGenInclusion K C hC hconn (canonicalBirth_le K C hC i j)) =
            canonicalGenInclusion K C hC hconn ((canonicalBirth_le K C hC i j).trans hik) :=
          funext (canonicalGenInclusion_comp K C hC hconn _ _)
        have H' := congrArg (fun f => f (canonicalBirthHomotopy K C hC hconn
          (canonicalTopCell K C hC i j) (t, a)))
            ((diskRoseMap_comp _ _).trans (congrArg diskRoseMap he))
        cases j <;> exact H')
    have he : diskFamilyMap (canonicalAttaching K C hC hconn i) (canonicalAttaching K C hC hconn k)
        (diskRoseMap (canonicalGenInclusion K C hC hconn hik)) (canonicalCellInclusion K C hC hik)
        (fun j a => congrArg (fun f => f a) (canonicalCellBoundary_natural K C hC hconn hik j)) =
        canonicalDiskInclusion K C hC hconn hik :=
      hom_ext _ (boundaryFamilyInclusion (CanonicalRel K C i) (Fin 2 → ℝ))
        (fun _ => rfl) (fun _ => by erw [diskFamilyMap_cell])
    erw [he] at H; erw [H]; rfl
  have he : DiskPresentationExtension.sourceMap (roseGenInclusion K C hC hconn hik)
      (subcomplexCellInclusion (hC hik) 2) (collapsedAttaching K C hC hconn i)
      (collapsedAttaching K C hC hconn k)
      (fun z => collapsedAttaching_natural K C hC hconn hik z.1 z.2) =
      collapsedDiskInclusion K C hC hconn hik :=
    hom_ext _ (boundaryFamilyInclusion (RelCWComplex.cell (C i : Set K) 2) (Fin 2 → ℝ))
      (fun _ => rfl) (fun _ => by erw [DiskPresentationExtension.sourceMap_cell])
  exact h₁.trans ((StabilizedDiskPresentation.map_killsPi2_iff _ _ _ _ _).trans
    (he ▸ collapsedDiskInclusion_killsPi2_iff K C hC hconn hik))
