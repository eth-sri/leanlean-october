module

public import RequestProject.GenusSpineMarking
public import RequestProject.ComponentComplex


@[expose] public section

/-! The genuine connected component carrying the canonical spine marking. -/
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace FiniteChains.Davis.Genus
open Comb
variable (q : ℕ) [NeZero q]

def markedSpineCx := component _ (spineBase q)

def markedSpineBase : (markedSpineCx q).V :=
  ⟨spineBase q, reach_self _ _⟩

instance : Finite (markedSpineCx q).E := by
  unfold markedSpineCx
  infer_instance

instance : Finite (markedSpineCx q).F := by
  unfold markedSpineCx
  infer_instance

theorem markedSpineCx_isConnected : IsConnected (markedSpineCx q) :=
  by apply component_isConnected

variable (x : Fin q × Bool)

def markedSpineLoop :
    Loop _ (markedSpineBase q) :=
  ⟨liftGerms _ _ _,
    isPath_liftGerms _ _ (spineMarkedLoop q x).2⟩

theorem markedSpineLoop_inclusion :
    mapPath (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineLoop q x).1 =
      (spineMarkedLoop q x).1 := map_cForget_liftGerms
    (reach_of_mem_path (spineMarkedLoop q x).2 (reach_self _ _))

theorem markedSpineLoop_inclusion_class :
    pi1Map (componentIncl (genusSpineCx q) (spineBase q)) _
      (Pi1.mk (markedSpineLoop q x)) = Pi1.mk (spineMarkedLoop q x) := by
  apply congrArg Pi1.mk
  apply Subtype.ext
  exact markedSpineLoop_inclusion q x

theorem markedSpine_exists_tree :
    ∃ T : SpanningTree _, T.root = markedSpineBase q :=
  SpanningTree.exists_of_isConnected (markedSpineCx_isConnected q) _

/-- Passing to the actual component loses no based homotopies. -/
theorem markedSpine_inclusion_pi1_injective :
    Function.Injective
      (pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q)) := by
  erw [injective_iff_map_eq_one]
  rintro ⟨p⟩ hp
  have h : Htpy _ _ _
      (mapPath (componentIncl (genusSpineCx q) (spineBase q)) p.1) [] :=
    Quotient.exact hp
  have hl := htpy_liftGerms (reach_self (genusSpineCx q) (spineBase q))
    (reach_self (genusSpineCx q) (spineBase q)) h
  erw [mapPath_componentIncl, liftGerms_map_cForget] at hl
  exact Quotient.sound hl

theorem markedSpine_inclusion_pi1_surjective :
    Function.Surjective
      (pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q)) := by
  rintro ⟨p⟩
  let lp : Loop _ (markedSpineBase q) :=
    ⟨liftGerms _ _ p.1,
      isPath_liftGerms _ _ p.2⟩
  refine ⟨Pi1.mk lp, ?_⟩
  apply congrArg Pi1.mk
  apply Subtype.ext
  exact map_cForget_liftGerms (reach_of_mem_path p.2 (reach_self _ _))

/-- The marked component has precisely the fundamental group of the full spine at its base. -/
def markedSpinePi1Equiv :
    Pi1 _ (markedSpineBase q) ≃* Pi1 _ (spineBase q) :=
  MulEquiv.ofBijective
    _
    ⟨markedSpine_inclusion_pi1_injective q, markedSpine_inclusion_pi1_surjective q⟩

end FiniteChains.Davis.Genus
