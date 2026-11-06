/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.OrdinaryFinalCatalogue
import VaughtConjecture.Knight.WholeDonorOrdinarySections

/-! # Ordinary catalogue sources on the literal two-face boundary

All fields are present at the final cutoff. Admission therefore supplies two
lawful whole input sections, agreeing on the literal common face. Pasting them
uses the actual ordered boundary; no auxiliary agreement or lawful extension
is assumed. The face identification below is purely an occurrence equation.
-/

namespace VaughtConjecture.Knight.OrdinaryReceivingSources
open     CappedDonor CappedDonor.Ref
open OrdinaryFinalCatalogue SourcePrefixRows OrbitPrefixSupport
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)

theorem private_lawful (a : OrdinaryFinalCatalogue.Member R) :
    RespectsSemantics C.rows (fun d => a.val (.priv d)) := by
  obtain ⟨st, hs, -, -, he⟩ := a.property.2
  have h := hs.v_respects.toRespects (fun d => (present_priv_iff).mpr (gradeC_le d))
  convert h using 1
  funext d
  rw [← he, profile_present]
  rfl

theorem request_lawful (a : OrdinaryFinalCatalogue.Member R) :
    RespectsSemantics P.rows (fun d => a.val (.req d)) := by
  obtain ⟨st, hs, -, -, he⟩ := a.property.2
  have h := hs.u_respects.toRespects (fun d => (present_req_iff).mpr (req_grade_le R d))
  convert h using 1
  funext d
  rw [← he, profile_present]
  rfl

theorem face_agreement (a : OrdinaryFinalCatalogue.Member R) d :
    a.val (.priv (R.face d).1) = a.val (.req d.1) := by
  obtain ⟨st, hs, -, -, he⟩ := a.property.2
  rw [← he, profile_present, profile_present]
  exact (hs.face d (req_grade_le R d.1)).symm

variable {ι : Type*} [DecidableEq ι] {A B T : Finset ι} {plan : VaughtConjecture.AmalgamationPlan.SupportFamily ι}
variable (W : WholeDonorBoundary.Input A B T plan nP N (nP + 1))
variable (R : Ref I nP N N W.right W.left)
variable (hface : ∀ i ,
  ∃ d ,
    d.1 = W.shared.g i ∧ (R.face d).1 = W.shared.f i)

include hface in
theorem shared (a : OrdinaryFinalCatalogue.Member R) i :
    a.val (.priv (W.shared.f i)) = a.val (.req (W.shared.g i)) := by
  obtain ⟨d, hd, he⟩ := hface i
  rw [← hd, ← he]
  exact face_agreement R a d

def boundary (a : OrdinaryFinalCatalogue.Member R) :=
  W.paste (fun d => a.val (.priv d)) (fun d => a.val (.req d))

local notation "boundary₀" => boundary W R

theorem boundary_private a d :
    boundary₀ a (W.leftFace.map d) = a.val (.priv d) :=
  W.paste_left _ _ d

local notation "shared₀" => shared W R hface

include hface in
theorem boundary_request a d :
    boundary₀ a (W.rightFace.map d) = a.val (.req d) :=
  W.paste_right _ _ (shared₀ a) d

include hface in
theorem boundary_lawful a :
    RespectsSemantics W.rows (boundary₀ a) :=
  W.paste_respects (private_lawful R a) (request_lawful R a) (shared₀ a)

include hface in
theorem boundary_bound a d :
    boundary₀ a d ≤ CanonicalFieldLayer.ceiling N (Field W.right W.left) :=
  WholeDonorOrdinarySections.paste_bound W (fun _ => member_bound R a _)
    (fun _ => member_bound R a _) (shared₀ a) d

include hface in
theorem boundary_agreement {a b : OrdinaryFinalCatalogue.Member R} {h}
    (hab : Agree a.val b.val h) :
    Agree (boundary₀ a) (boundary₀ b) h :=
  WholeDonorOrdinarySections.paste_agreement W (shared₀ a) (shared₀ b)
    (fun _ => hab _) (fun _ => hab _)

include hface in
theorem boundary_field a d :
    ∃ f , boundary₀ a d = a.val f := by
  rcases WholeDonorOrdinarySections.covered W d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact ⟨.priv c, boundary_private W R a c⟩
  · solve_by_elim [boundary_request]

include hface in
theorem boundary_support (a : OrdinaryFinalCatalogue.Member R) G
    d :
    Supported N G a.val (boundary₀ a d) := by
  obtain ⟨f, hf⟩ := boundary_field W R hface a d
  rw [hf]
  exact supported_field N G a.val f

