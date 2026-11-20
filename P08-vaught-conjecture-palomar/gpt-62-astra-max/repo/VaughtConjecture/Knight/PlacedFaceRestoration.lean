/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PlacedFace
public import VaughtConjecture.Knight.SingleFaceTailRestoration
public import VaughtConjecture.Knight.PaddedOwnerRepair

/-! # Building the successor face lift from native supply and owner repair -/

@[expose] public section
namespace VaughtConjecture.Knight.PlacedFace
open CappedDonor CoatomBoundaryExtension
variable {ι : Type*} [DecidableEq ι] {A B : Finset ι} {D : CellScheme A} {sem : Semantics D}
  {n : ℕ} {S : SemScheme n} {place : Fin n ↪ ι} {he : Finset.univ.image place = B}
  (G : ExactSemanticFace (PointImageSemantics.rows S.scheme place he S.rows) sem)
  {i k : ℕ} (lo : min (k+1) n ≤ i) (hi : i ≤ k+1) (sub : B ⊆ A)

local notation "inc" => incl G lo hi sub

/-- Bottom needs only supply; an inactive face needs only lower restoration. In the active
case maximize on the native face and restore the whole lower section above that owner's cap. -/
theorem successor (lower : CappedLift sem (GradedLe.atGrade sub k))
    (bottom : ∀ {p : S.Native i → ExtOrd}, S.rows.Lawful p → ∃ w, sem.Lawful w ∧ ∀ d, w (inc d) = p d)
    (repair : ∀ c : S.Native i, S.scheme.cell c.1 = (Finset.univ,i) → S.scheme.grade c.1 = k+1 →
      ∀ {p : S.Native i → ExtOrd} {q : D.SectionAt (A,k+1)}, S.rows.Lawful p → sem.Lawful q →
      ∀ {γ}, SelfVis (k+1) γ → ⊥ < γ → γ < p c → CappedEq (q ∘ inc) p γ →
      sem.FaceLift inc (fun d => min (p d) (p c)) q γ) :
    CappedLift sem (GradedLe.atGrade sub (k+1)) := by
  intro p q γ hp hq hv ha
  let e := equiv G lo hi
  have hp' := (lawful G lo hi p).mp hp
  by_cases hz : γ = ⊥
  · obtain ⟨r,hr,hrd⟩ := bottom hp'
    refine ⟨r,hr,fun _ => by simp [hz],?_⟩
    intro d; obtain ⟨x,rfl⟩ := e.surjective d; exact hrd x
  by_cases h : ∃ d, S.scheme.grade d.1 = k+1 ∧ γ < p (e d)
  · obtain ⟨c, hc, hg, hpc, hm, hvis, _⟩ := AmbientGradeCharts.activeOwner hp' hi h
    obtain ⟨u,hu,hrd,hcap⟩ := repair c hc hg hp' hq hv (bot_lt_iff_ne_bot.mpr hz) hpc (fun d => ha (e d))
    obtain ⟨r,hr,hrd',hcap',_⟩ := SingleFaceTailRestoration.exists_restore sem sub lower hp hu hvis
      (fun d => by obtain ⟨x,rfl⟩ := e.surjective d; exact hrd x)
      (fun d hd => by obtain ⟨x,rfl⟩ := e.surjective d; exact hm x ((grade G lo hi x).symm.trans hd))
    exact ⟨r,hr,fun d => (GradeTailRestoration.cap_below (hcap' d) hpc.le).trans (hcap d),hrd'⟩
  · apply SingleFaceTailRestoration.exists_inactive sem sub lower hp hq hv ha
    intro d hd; obtain ⟨x,rfl⟩ := e.surjective d
    exact le_of_not_gt fun hlt => h ⟨x, (grade G lo hi x).symm.trans hd, hlt⟩
end VaughtConjecture.Knight.PlacedFace
