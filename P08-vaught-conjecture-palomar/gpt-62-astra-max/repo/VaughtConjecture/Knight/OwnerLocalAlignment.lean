/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OwnerStripRetuning
public import VaughtConjecture.Knight.AlignedCutEncoding
public import VaughtConjecture.Knight.OwnerLocalEndpoint

/-! # Owner alignment without a fixed source grid

The source is an actual lawful section on the owner's lower domain. V-C's
owner-local endpoint collects precisely its saturated observations. The original
owner-locality retuning then applies without a profile-cardinality grid or an
assumed alignment conclusion. Long semantic source rows remain unchanged.
-/

@[expose] public section

namespace VaughtConjecture.Knight.OwnerLocalAlignment
open Transform Value ExtOrd SharpWitnessComposition OwnerStripRetuning OwnerLocalEndpoint
noncomputable section

theorem saturated_subcut {X : Type*} {j} {s p} {c}
    {τ} {γ h : ExtOrd} (sat : Saturation j s p c τ γ)
    (H : IsEndpoint j s τ γ h) (d : X) (hd : s d < h) (hsat : τ (s d) = γ) :
    ∃ (u : Ordinal.{0}) (n : ℕ), n < j ∧
      s d = ofOrd (limitPart u + n) ∧ h = ofOrd (limitPart u + j) := by
  have hnv := fun hv ↦
  hd.ne (((endpoint_of_selfVis hv).symm.trans (H.strip hd hsat)))
  rcases ExtOrd.cases (s d) with hb | ht | ⟨u, hu⟩
  · exact (hnv (hb ▸ selfVis_bot j)).elim
  · exact (sat.proper d ht).elim
  · have hn : finitePart u < j := by
      by_contra hn
      exact hnv (hu ▸ selfVis_ofOrd_iff.mpr (not_lt.mp hn))
    refine ⟨u, finitePart u, hn, ?_, ?_⟩
    · simpa only [limitPart_add_finitePart] using hu
    · have he := H.strip hd hsat
      rw [endpoint, hu, extVisibilityReplace_of_finitePart_lt hn] at he
      exact he.symm

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable {sem : Semantics D}

/-- Internal alignment at the constructed owner-local endpoint. -/
theorem alignment_at_endpoint c
    {s p}
    (hs : sem.Lawful s)
    (hp : sem.Lawful p)
    (hshort : ∀ e, Short (D.grade c) (s e))
    {τ} {h γ : ExtOrd}
    (hτ : Witness (gTop (D.grade c)) τ)
    (hγ : SelfVis (D.grade c) γ)
    (sat : Saturation (D.grade c) s p ⟨c, GradedLe.refl _⟩ τ γ)
    (H : IsEndpoint (D.grade c) s τ γ h) :
    ∃ (ρ : ExtOrd → ExtOrd) (δ : ExtOrd),
      Witness (gTop (D.grade c)) ρ ∧ γ ≤ δ ∧ δ ≤ p ⟨c, GradedLe.refl _⟩ ∧
      SelfVis (D.grade c) δ ∧ ρ h = δ ∧
      (∀ e, min (p e) δ = min (ρ (s e)) δ) ∧
      (∀ e, δ < min (p e) (p ⟨c, GradedLe.refl _⟩) → h ≤ s e) ∧
      (∀ z, Short (D.grade c) z → min (ρ z) γ = min (τ z) γ) ∧
      ∀ z, ρ z ≤ p ⟨c, GradedLe.refl _⟩ := by
  have hτbound := sat.bound
  have hpc := sat.cap
  have hface := sat.face
  have hreach := H.reach sat
  classical
  let self : D.RowDomain c := ⟨c, GradedLe.refl _⟩
  let M := p self
  by_cases halign : ∀ e : D.RowDomain c, γ < min (p e) M → h ≤ s e
  · refine ⟨τ, γ, hτ, le_rfl, hpc.le, hγ, hreach, ?_, halign,
      fun _ _ => rfl, fun z => (hτbound z).trans hpc.le⟩
    intro e
    rw [min_eq_left (hτbound _), hface]
  push Not at halign
  obtain ⟨d, hpd, hsub⟩ := halign
  have hsd : s d < h := hsub
  have hsat : γ ≤ τ (s d) := by
    rw [hface d, min_eq_right (lt_of_lt_of_le hpd (min_le_left _ _)).le]
  obtain ⟨u, i, hi, hdi, hendpoint⟩ := saturated_subcut sat H d hsd (le_antisymm (hτbound _) hsat)
  have howner : h ≤ s self := (H.le_of_saturated sat.owner_saturated).trans_eq (endpoint_of_selfVis sat.owner_vis)
  obtain ⟨α, hα, _, hαread⟩ := exists_bounded_exact_capped_witness
    (grade := fun x : D.RowDomain c => D.grade x.1) (p := s) (c := self)
    (fun x : D.RowDomain c => x.2.2) (hs.orderly self).symm (hs.locality self)
  obtain ⟨β, hβ, hβbound, hβread⟩ := exists_bounded_exact_capped_witness
    (grade := fun x : D.RowDomain c => D.grade x.1) (p := p) (c := self)
    (fun x : D.RowDomain c => x.2.2) (hp.orderly self).symm (hp.locality self)
  have ha (e : D.RowDomain c) (he : s e < h) : α (sem.E c e) = s e :=
    (hαread e).trans (min_eq_left (he.le.trans howner))
  obtain ⟨ρ, δ, hρ, hγδ, hδM, hδvis, hend, hstrip, habove, hcap, hbound⟩ :=
    exists_retuning_with_transfer hα hβ hτ hi ((ha d hsd).trans hdi) hγ hτbound
      (by rw [ha d hsd]; exact le_antisymm (hτbound _) hsat)
      (by rw [hβread d]; exact hpd.le) hβbound
  have hρh : ρ h = δ := hendpoint ▸ hend
  have subread (e : D.RowDomain c) (he : s e < h) :
      min (p e) M = ρ (s e) := by
    by_cases hlo : τ (s e) < γ
    · have hpread : p e = τ (s e) := AmbientGradeCharts.eq_of_cap_below
        (by rw [min_eq_left (hτbound _)]; exact (hface e).symm) hlo
      have hρread : ρ (s e) = τ (s e) :=
        AmbientGradeCharts.eq_of_cap_below (hcap _ (hshort e)) hlo
      rw [hpread, hρread, min_eq_left (hlo.le.trans hpc.le)]
    · obtain ⟨w, n, hn, heq, hwe⟩ :=
        saturated_subcut sat H e he (le_antisymm (hτbound _) (not_lt.mp hlo))
      have hfloor : limitPart w = limitPart u := by
        have heq := congrArg limitPart (ofOrd_inj.mp (hwe.symm.trans hendpoint))
        simpa only [limitPart_limitPart_add_nat] using heq
      rw [hfloor] at heq
      exact (hβread e).symm.trans
        ((hstrip (sem.E c e) n hn ((ha e he).trans heq)).symm.trans
          (congrArg ρ (ha e he)))
  refine ⟨ρ, δ, hρ, hγδ, hδM, hδvis, hρh, ?_, ?_, hcap, hbound⟩
  · intro e
    by_cases he : s e < h
    · have hc : min (min (p e) M) δ = min (p e) δ := by
        rw [min_assoc, min_eq_right hδM]
      rw [← hc, subread e he]
    · have has : ofOrd (limitPart u + D.grade c) ≤ α (sem.E c e) := by
        rw [hαread e, ← hendpoint]
        exact le_min (not_lt.mp he) howner
      have hpe : δ ≤ p e := (habove _ has).trans
        ((hβread e).le.trans (min_le_left _ _))
      rw [min_eq_right hpe, min_eq_right (hρh ▸ hρ.mono (not_lt.mp he))]
  · intro e hhigh
    by_contra hn
    have he := not_le.mp hn
    have hle : min (p e) M ≤ δ := by
      rw [subread e he, ← hρh]
      exact hρ.mono he.le
    exact not_lt_of_ge hle hhigh

/-- The endpoint and retuning are constructed from lawful owner data. No source
grid, first-reaching-grid assertion, or alignment conclusion is an input. -/
theorem exists_alignment c
    {s p}
    (hs : sem.Lawful s)
    (hp : sem.Lawful p)
    (hproper : ∀ e, s e ≠ ⊤) (hshort : ∀ e, Short (D.grade c) (s e))
    {τ} {γ}
    (hτ : Witness (gTop (D.grade c)) τ)
    (hγ : SelfVis (D.grade c) γ) (hpos : ⊥ < γ) (hτbound : ∀ z, τ z ≤ γ)
    (hface : ∀ e, τ (s e) = min (p e) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩) :
    ∃ (h : ExtOrd) (ρ : ExtOrd → ExtOrd) (δ : ExtOrd),
      IsEndpoint (D.grade c) s τ γ h ∧
      ⊥ < h ∧ h ≠ ⊤ ∧ SelfVis (D.grade c) h ∧ h ≤ s ⟨c, GradedLe.refl _⟩ ∧
      Witness (gTop (D.grade c)) ρ ∧ γ ≤ δ ∧ δ ≤ p ⟨c, GradedLe.refl _⟩ ∧
      SelfVis (D.grade c) δ ∧ ρ h = δ ∧
      CappedEq p (ρ ∘ s) δ ∧
      (∀ e, δ < min (p e) (p ⟨c, GradedLe.refl _⟩) → h ≤ s e) ∧
      (∀ z, Short (D.grade c) z → min (ρ z) γ = min (τ z) γ) ∧
      ∀ z, ρ z ≤ p ⟨c, GradedLe.refl _⟩ := by
  let sat : Saturation (D.grade c) s p ⟨c, GradedLe.refl _⟩ τ γ :=
    ⟨hτ.bot, hτ.mono, hτbound, hpos, hpc, hface, hproper, ((hs.orderly ⟨c, GradedLe.refl _⟩).symm)⟩
  obtain ⟨h, H, hhpos, hhtop, hvis, _, howner, _⟩ := exists_isEndpoint sat
  exact ⟨h, by
    obtain ⟨ρ, δ, hrest⟩ := alignment_at_endpoint c hs hp hshort hτ hγ sat H
    exact ⟨ρ, δ, H, hhpos, hhtop, hvis, howner, hrest⟩⟩

end
end VaughtConjecture.Knight.OwnerLocalAlignment
