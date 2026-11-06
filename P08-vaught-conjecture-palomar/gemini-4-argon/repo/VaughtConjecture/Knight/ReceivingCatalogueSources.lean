/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PrivateCatalogueRepair
public import VaughtConjecture.Knight.ReceivingBottomCatalogue
public import VaughtConjecture.Knight.ReceivingLadderSemantics

/-! # Admitted receiving catalogues on the fixed mixed carrier

The complete field inventory, finite controllers, rank anchors, grid and reserved
ceiling are constructed from the LOW/HIGH catalogue. Admission supplies the
lawful private restriction; no source-lawfulness field is assumed. This module
specializes the committed physical rows without claiming probe bountifulness.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingCatalogueSources
open Transform Value ExtOrd CappedDonor CappedDonor.Ref
open ReceivingLadderCarrier
noncomputable section

variable {I : Type*} [Fintype I] {nP N J K : ℕ}
  {P : SemScheme (nP + 1)} {C : SemScheme J} {R : Ref I nP N J P C}
  (L : R.LowRef K)

/-- Controllers are precisely admitted canonical profiles, not added repairs. -/
abbrev Controller := ↥(ReceivingSupportedRepair.Catalogue (j := 2) L)

instance : Fintype (Controller L) := (ReceivingSupportedRepair.catalogue_finite L).fintype

/-- Even literal tops in the actual receiving state supply a proper catalogue
controller, through the already constructed terminal-block insertion. -/
instance : Nonempty (Controller L) := by
  have h := (L.actual_tadmissible 2).resync
  obtain ⟨r⟩ := ReceivingBottomCatalogue.exists_insertion (by omega : 1 ≤ 2) h
    (resync_synchronized (L.actual_tadmissible 2).adm)
  exact ⟨⟨r.encoded.profile, r.catalogue⟩⟩

def fields (a : Controller L) : TField P C → ExtOrd := a.val

def state (a : Controller L) : R.TState 2 := a.property.2.choose

theorem state_admitted (a : Controller L) : L.TAdmissible (state L a) :=
  a.property.2.choose_spec.1

theorem state_profile (a : Controller L) : (state L a).profile = fields L a :=
  a.property.2.choose_spec.2.2

def ranks (a : Controller L) (f : TField P C) : ℕ :=
  LadderScalarRendering.fieldRank (fields L a) f

def rungs : ℕ := Fintype.card (TField P C) + 1

def grid : Finset ExtOrd := PairedSlotComparison.sourceGrid 2 (Fintype.card (TField P C))

def ceiling : ExtOrd :=
  ofOrd (Ordinal.omega0 * (2 * Fintype.card (TField P C) + 1 : ℕ) + 2)

theorem grid_bot : ⊥ ∈ grid (P := P) (C := C) := PairedSlotComparison.sourceGrid_bot _ _

theorem ceiling_mem : ceiling (P := P) (C := C) ∈ grid (P := P) (C := C) :=
  PairedSlotComparison.sourceGrid_endpoint le_rfl

theorem grid_visible {x : ExtOrd} (hx : x ∈ grid (P := P) (C := C)) : SelfVis 2 x :=
  PairedSlotComparison.sourceGrid_visible hx

theorem ceiling_visible : SelfVis 2 (ceiling (P := P) (C := C)) := grid_visible ceiling_mem

theorem field_grade_pos (f : Field P C) : 1 ≤ f.grade := by
  cases f with
  | req d => exact P.scheme.grade_pos d
  | priv d => exact C.scheme.grade_pos d
  | gate => exact le_rfl

theorem fields_visible (a : Controller L) (f : TField P C) : SelfVis 1 (fields L a f) := by
  rw [← state_profile L a]
  cases f with
  | cutoff => exact (state_admitted L a).b_vis
  | field f =>
      change SelfVis 1 ((state L a).st.sourceProfile f)
      by_cases hf : f.grade ≤ 2
      · rw [State.sourceProfile_of_present _ hf]
        exact ((state_admitted L a).adm.numeric_selfVis f hf).mono (field_grade_pos f)
      · rw [State.sourceProfile_of_future _ hf]
        exact (state_admitted L a).adm.persistent_selfVis f

/-- The map uses actual private occurrences, not a recoded private display. -/
def privateField (c : Cell C.scheme) : TField P C := .field (.priv c)

theorem private_read (a : Controller L) (c : Cell C.scheme) (hc : C.scheme.grade c ≤ 2) :
    fields L a (privateField c) = (state L a).st.v (privCell c hc) := by
  rw [← state_profile L a]
  exact PrivateCatalogueRepair.profile_private (state L a) (privCell c hc)

theorem private_visible (a : Controller L) (c : Cell C.scheme) (hc : C.scheme.grade c ≤ 2) :
    SelfVis (C.scheme.grade c) (fields L a (privateField c)) := by
  rw [private_read L a c hc]
  exact ((state_admitted L a).adm.v_respects.orderly (privCell c hc)).symm

section FixedCarrier
variable {C : SemScheme 2} {R : Ref I nP 2 2 P C} (L : R.LowRef K)
  (hC : C.scheme.plan = privatePlan) (request : Cell P.scheme)

def high : TField P C := privateField R.cap

theorem high_visible (a : Controller L) : SelfVis 2 (fields L a (high (R := R))) := by
  have h := private_visible L a R.cap (by rw [R.grade_cap])
  simpa only [high, R.grade_cap] using h

/-- The existing physical plan, with actual admitted controllers and their
rank anchors. Repeated anchors are not quotiented. -/
abbrev carrier := scheme (L := rungs (P := P) (C := C))
  (X := TField P C) (Q := Controller L) (U := Controller L) C.scheme hC

local notation "G" => grid (P := P) (C := C)
local notation "H" => ceiling (P := P) (C := C)

def semantics : Semantics (carrier L hC) :=
  ReceivingLadderSemantics.semantics C.scheme hC privateField (.field (.req request))
    (high (R := R)) (ranks L) (fields L) id G H C.rows grid_bot
    (fun _ => grid_visible) ceiling_visible (fields_visible L)
    (fun a c => private_visible L a c (gradeC_le c)) (high_visible L)

end FixedCarrier
end
end VaughtConjecture.Knight.ReceivingCatalogueSources
