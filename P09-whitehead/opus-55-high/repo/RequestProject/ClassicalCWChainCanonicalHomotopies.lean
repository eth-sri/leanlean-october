import RequestProject.HomeomorphContinuousMap
import RequestProject.ClassicalCWChainCanonicalWords
import RequestProject.NaturalDiskAttachingEquiv
import RequestProject.PresWordDiskComparisonNaturality
import RequestProject.Tac


/-! Canonical attaching homotopies are chosen once, when a cell first
appears, and pushed through the later generator inclusions. Consequently
the actual disk-model comparisons form commuting squares. Unverified. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalGraphModel RelativeAttachment PresModel
open Topology
open scoped unitInterval ContinuousMap
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C]
  [TreeChoice K C]

def canonicalCellBoundary (i : Fin (n + 1)) (j : CanonicalRel K C i) :=
  classicalPresCellBoundary _ j
    (canonicalWords_ne_nil K C hC hconn i)

theorem canonicalCellBoundary_natural hik
    j :
    (diskRoseMap (canonicalGenInclusion K C hC hconn hik)).comp
        (canonicalCellBoundary K C hC hconn i j) =
      canonicalCellBoundary K C hC hconn k (canonicalCellInclusion K C hC hik j) := by
  ext a
  exact (canonicalWordEmbedding K C hC hconn hik).classicalPresWordAttaching_natural
    _ _ _

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
theorem canonicalBirth_le (i : Fin (n + 1)) (j : CanonicalRel K C i) :
    canonicalBirth K C (canonicalTopCell K C hC i j) ≤ i := by
  cases j with
  | inl j => exact birth_le C _ i j.property
  | inr u => exact Fin.zero_le _


def canonicalBirthHomotopy j :
    (stabilizedCellBoundary K C hC hconn (canonicalBirth K C j) (canonicalBirthCell K C j)).Homotopy
      (canonicalCellBoundary K C hC hconn (canonicalBirth K C j) (canonicalBirthCell K C j)) :=
  Classical.choice (stabilizedCellBoundary_homotopic K C hC hconn
    _ _)

def canonicalCellHomotopy (i : Fin (n + 1)) (j : CanonicalRel K C i) :
    (stabilizedCellBoundary K C hC hconn i j).Homotopy
      (canonicalCellBoundary K C hC hconn i j) where
  toContinuousMap := (diskRoseMap
    (canonicalGenInclusion K C hC hconn (canonicalBirth_le K C hC i j))).comp
      (canonicalBirthHomotopy K C hC hconn (canonicalTopCell K C hC i j)).toContinuousMap
  map_zero_left a := by
    have H := congrArg (· a) (stabilizedCellBoundary_natural K C hC hconn
      (canonicalBirth_le K C hC i j) (canonicalBirthCell K C (canonicalTopCell K C hC i j)))
    aesop
  map_one_left a := by
    have H := congrArg (· a) (canonicalCellBoundary_natural K C hC hconn
      (canonicalBirth_le K C hC i j) (canonicalBirthCell K C (canonicalTopCell K C hC i j)))
    aesop

theorem canonicalCellHomotopy_natural hik
    j t a :
    diskRoseMap (canonicalGenInclusion K C hC hconn hik)
        (canonicalCellHomotopy K C hC hconn i j (t, a)) =
      canonicalCellHomotopy K C hC hconn k (canonicalCellInclusion K C hC hik j) (t, a) := by
  have he : (canonicalGenInclusion K C hC hconn hik ∘
      canonicalGenInclusion K C hC hconn (canonicalBirth_le K C hC i j)) =
      canonicalGenInclusion K C hC hconn ((canonicalBirth_le K C hC i j).trans hik) := by
    aesop
  have H := congrArg (· (canonicalBirthHomotopy K C hC hconn
    _ (t, a)))
      ((diskRoseMap_comp _ _).trans (congrArg diskRoseMap he))
  aesop

def canonicalAttaching (i : Fin (n + 1)) :=
  classicalPresWordAttaching _ (canonicalWords_ne_nil K C hC hconn i)

def canonicalAttachingHomotopy (i : Fin (n + 1)) :
    (stabilizedAttaching K C hC hconn i).Homotopy (canonicalAttaching K C hC hconn i) := by
  let H j := canonicalCellHomotopy K C hC hconn i j
  let F : C(BoundaryFamily (CanonicalRel K C i) (Fin 2 → ℝ),
      C(I, ClassicalGraphModel.Rose (CanonicalGen K C hC hconn i))) :=
    ⟨fun a => ((H a.1).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry a.2,
      continuous_sigma (fun j =>
        ((H j).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry.continuous)⟩
  exact {
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := by aesop
    map_one_left := by aesop }

def canonicalDiskChange i :
    DiskAttachment (stabilizedAttaching K C hC hconn i) ≃ₕ
      ClassicalPresWordDisks (canonicalWords K C hC hconn i) (canonicalWords_ne_nil K C hC hconn i) :=
  naturalDiskAttachingEquiv _ _ (canonicalAttachingHomotopy K C hC hconn i)

def stabilizedDiskInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :=
  StabilizedDiskPresentation.map _
    _
    _ _
    (fun z => collapsedAttaching_natural K C hC hconn hik z.1 z.2)

def canonicalDiskInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :=
  (canonicalWordEmbedding K C hC hconn hik).classicalWordDiskMap
    (canonicalWords_ne_nil K C hC hconn i) (canonicalWords_ne_nil K C hC hconn k)

theorem canonicalDiskChange_natural hik :
    (canonicalDiskInclusion K C hC hconn hik).comp (canonicalDiskChange K C hC hconn i).toFun =
      (canonicalDiskChange K C hC hconn k).toFun.comp (stabilizedDiskInclusion K C hC hconn hik) := by
  have H := naturalDiskAttachingEquiv_natural
    _ _
    (canonicalAttachingHomotopy K C hC hconn i)
    _ _
    (canonicalAttachingHomotopy K C hC hconn k)
    _
    _
    (fun j a => congrArg (· a) (stabilizedCellBoundary_natural K C hC hconn hik j))
    (fun j a => congrArg (· a) (canonicalCellBoundary_natural K C hC hconn hik j))
    (fun t j a => canonicalCellHomotopy_natural K C hC hconn hik j t a)
  tauto

theorem canonicalDiskInclusion_killsPi2_iff hik :
    Whitehead.KillsPi2 (canonicalDiskInclusion K C hC hconn hik) ↔
      Whitehead.KillsPi2 (⟨Set.inclusion (hC hik), continuous_inclusion (hC hik)⟩ :
        C((C i : Set K), (C k : Set K))) := by
  have h₁ : Whitehead.KillsPi2 (canonicalDiskInclusion K C hC hconn hik) ↔
      Whitehead.KillsPi2 (stabilizedDiskInclusion K C hC hconn hik) := by
    apply Whitehead.killsPi2_homotopyEquiv_square_iff
      _ _
    rwd [canonicalDiskChange_natural]
  have he : DiskPresentationExtension.sourceMap _
      _ _
      _
      (fun z => collapsedAttaching_natural K C hC hconn hik z.1 z.2) =
      collapsedDiskInclusion K C hC hconn hik := by
    rfl
  exact h₁.trans ((StabilizedDiskPresentation.map_killsPi2_iff _ _ _ _ _).trans
    (he ▸ collapsedDiskInclusion_killsPi2_iff K C hC hconn hik))
