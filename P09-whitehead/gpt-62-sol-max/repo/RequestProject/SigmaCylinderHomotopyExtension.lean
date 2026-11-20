module

public import RequestProject.CylinderBoundaryHomotopyCorrection
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-! Disk and cylinder homotopy extension for arbitrary disjoint families.
The construction never puts a finiteness condition on the family. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {J : Type u} {D : J → Type u} [∀ j, TopologicalSpace (D j)]

def sigmaCylinderHomeomorph : (Σ j, I × D j) ≃ₜ I × (Σ j, D j) where
  toFun z := (z.2.1, ⟨z.1, z.2.2⟩)
  invFun z := ⟨z.2.1, (z.1, z.2.2)⟩
  left_inv z := by cases z; rfl
  right_inv z := by tauto
  continuous_toFun := continuous_sigma (fun _ =>
    continuous_fst.prodMk (continuous_sigmaMk.comp continuous_snd))
  continuous_invFun := by
    let swapFibres : (Σ j, D j × I) → Σ j, I × D j := fun z => ⟨z.1, (z.2.2, z.2.1)⟩
    have hs : Continuous swapFibres := continuous_sigma (fun _ =>
      continuous_sigmaMk.comp continuous_swap)
    exact hs.comp ((Homeomorph.sigmaProdDistrib (X := D) (Y := I)).continuous.comp continuous_swap)

def SigmaSubspace (S : ∀ j, Set (D j)) : Set (Σ j, D j) := {d | d.2 ∈ S d.1}

theorem sigmaSubspace_isClosed (S : ∀ j, Set (D j)) (hS : ∀ j, IsClosed (S j)) :
    IsClosed (SigmaSubspace S) :=
  isClosed_sigma_iff.mpr hS

theorem sigmaSubspace_hasHomotopyExtension (S : ∀ j, Set (D j))
    (h : ∀ j, HasHomotopyExtension (Subtype.val : S j → D j)) :
    HasHomotopyExtension (Subtype.val : SigmaSubspace S → Σ j, D j) := by
  intro Z _ f H h₀
  have hex (j : J) : ∃ G : C(I × D j, Z), (∀ d, G (0, d) = f ⟨j, d⟩) ∧
      ∀ (t : I) (a : S j), G (t, a.val) = H (t, ⟨⟨j, a.val⟩, a.property⟩) := by
    let k : C(S j, SigmaSubspace S) :=
      ⟨fun a => ⟨⟨j, a.val⟩, a.property⟩,
        (continuous_sigmaMk.comp continuous_subtype_val).subtype_mk _⟩
    exact h j Z (f.comp (.sigmaMk j)) (H.comp ((ContinuousMap.id _).prodMap k)) (fun a => h₀ (k a))
  choose G hG₀ hGA using hex
  refine ⟨(ContinuousMap.sigma G).comp sigmaCylinderHomeomorph.symm.toContinuousMap, ?_, ?_⟩
  · rintro ⟨j, d⟩
    exact hG₀ j d
  · intro t ⟨⟨j, d⟩, hd⟩
    exact hGA j t ⟨d, hd⟩

theorem sigmaFullCylinder_hasHomotopyExtension (S : ∀ j, Set (D j))
    (h : ∀ j, HasHomotopyExtension
      (Subtype.val : FullCylinderBoundary (S j) → I × D j)) :
    HasHomotopyExtension
      (Subtype.val : FullCylinderBoundary (SigmaSubspace S) → I × (Σ j, D j)) :=
  (sigmaSubspace_hasHomotopyExtension _ h).homeomorph
    (sigmaCylinderHomeomorph.subtype (fun _ => Iff.rfl)) sigmaCylinderHomeomorph _ (fun _ => rfl)

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

def unitBoundarySubspaceHomeomorph :
    UnitBoundary E ≃ₜ {d : ClosedUnitBall E // ‖d.val‖ = 1} where
  toFun d := ⟨unitBoundaryInclusion E d, d.property⟩
  invFun d := ⟨d.val.val, d.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (unitBoundaryInclusion E).continuous.subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem unitBoundarySubspace_hasHomotopyExtension :
    HasHomotopyExtension
      (Subtype.val : {d : ClosedUnitBall E // ‖d.val‖ = 1} → ClosedUnitBall E) :=
  (unitBoundary_hasHomotopyExtension E).homeomorph
    (unitBoundarySubspaceHomeomorph E) (Homeomorph.refl _) Subtype.val (fun _ => rfl)

theorem diskFamilySubspace_hasHomotopyExtension (J : Type u) :
    HasHomotopyExtension
      (Subtype.val : SigmaSubspace (fun _ : J => {d : ClosedUnitBall E | ‖d.val‖ = 1}) →
        Σ _ : J, ClosedUnitBall E) :=
  sigmaSubspace_hasHomotopyExtension _ (fun _ => unitBoundarySubspace_hasHomotopyExtension E)

theorem diskFamilyFullCylinder_hasHomotopyExtension (J : Type u) :
    HasHomotopyExtension (Subtype.val :
      FullCylinderBoundary (SigmaSubspace (fun _ : J => {d : ClosedUnitBall E | ‖d.val‖ = 1})) →
        I × (Σ _ : J, ClosedUnitBall E)) :=
  sigmaFullCylinder_hasHomotopyExtension _ (fun _ =>
    fullBallCylinderBoundary_hasHomotopyExtension E)

end FiniteChains.RelativeAttachment
