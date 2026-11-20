/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryFinalCatalogue
public import VaughtConjecture.Knight.FinalGateChart

/-! # Capped readback from arbitrary lawful final-layer sections

Availability at the retained private cap chooses an actual installed ceiling
leaf. Its locality gives the whole-coordinate chart; one positive marked node
forces the chosen source's gate positive. Literal private retention then supplies
every cap and representative receipt in V-C's one-chart readback theorem.

Only the **chosen catalogue member** is admitted. The arbitrary physical section
is not assumed synchronized, decoded, or admitted. No LOW clause, anchor,
protected flexibility, or literal-top readback is used. The predecessor's
original occurrence maps and literal source equations remain explicit inputs;
this file does not build the predecessor or prove final-layer bountifulness.

`CappedDonorCappedReadback` is ported unchanged from V-C's `04276e9`.
-/

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryFinalReadback
open Transform Value ExtOrd CappedDonor CappedDonor.Ref OrdinaryFinalCatalogue
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (F : FinalGateLayer.Input D N (Field P C) (OrdinaryFinalCatalogue.Member R))

/-- An inherited occurrence in the final active lower set. -/
abbrev oldAt d (hd : D.grade d ≤ N) : F.carrier.below (A, N) :=
  ⟨F.old d, by
    rw [F.old_index]
    exact ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩⟩

variable (req : Cell P.scheme ↪ Cell D) (priv : Cell C.scheme ↪ Cell D)
variable (hreqGrade : ∀ d, D.grade (req d) = P.scheme.grade d)
variable (hprivGrade : ∀ d, D.grade (priv d) = C.scheme.grade d)

abbrev reqAt (d : Cell P.scheme) : F.carrier.below (A, N) :=
  oldAt R F (req d) ((hreqGrade d).trans_le (req_grade_le R d))

abbrev privAt (d : Cell C.scheme) : F.carrier.below (A, N) :=
  oldAt R F (priv d) ((hprivGrade d).trans_le (gradeC_le d))

/-- Capped correctness on **all** donor occurrences follows from the installed
rows, literal private retention, and a single positive physical gate occurrence. -/
theorem capped_readback
    (hfields : ∀ a f, F.fields a f = a.val f) (hgate : F.gate = .gate)
    (hreq : ∀ a d, F.lower a (req d) = a.val (.req d))
    (hpriv : ∀ a d, F.lower a (priv d) = a.val (.priv d))
    {v}
    (hv : F.rows.Lawful v)
    (hretain : ∀ d, v (privAt R F priv hprivGrade d) = R.vact d)
    b (hpositive : v (F.addedAt b true) ≠ ⊥)
    d :
    min (v (reqAt R F req hreqGrade d)) (R.cut R.vactL) =
      min (R.p d) (R.cut R.vactL) := by
  let c := privAt R F priv hprivGrade R.cap
  have hc : F.carrier.grade c.1 = N :=
    (congrArg Prod.snd (F.old_index (priv R.cap))).trans
      ((hprivGrade R.cap).trans (congrArg Prod.snd R.cap_cell))
  have hpos : v c ≠ ⊥ := by
    rw [hretain]
    exact ne_bot_of_gt R.cap_pos
  obtain ⟨a, hca, hga, τ, hτ, -, hr⟩ := F.exists_active_chart hv c hc hpos b hpositive
  have hm : R.vact R.cap ≤ v (F.addedAt a false) := by
    simpa only [c, hretain] using hca
  let v₀ := R.low (a.val ∘ Field.priv)
  have hread e (he : R.vact e ≤ R.vact R.cap) : τ (a.val (.priv e)) = R.vact e := by
    simpa only [privAt,oldAt,F.source_old,hpriv,hretain,min_eq_left (he.trans hm)] using hr (privAt R F priv hprivGrade e)
  have hcap := hread R.cap le_rfl
  have href i := hread (R.ref i) (R.ref_lt_cap i).le
  have hcut : τ (R.cut v₀) = R.cut R.vactL := by
    rw [← cut_map hτ le_rfl]; exact cut_congr hcap href
  have hsel : τ (R.sel v₀ d) = min (R.p d) (R.cut R.vactL) := by
    rw [← sel_map hτ le_rfl, sel_congr (v₁ := fun e => τ (v₀ e)) (v₂ := R.vactL) hcap href, sel_actual]
  rw [hgate,hfields] at hga
  have hcpos : a.val (.priv R.cap) ≠ ⊥ := fun he => R.cap_pos.ne' (hcap.symm.trans ((congrArg τ he).trans hτ.bot))
  have he := congrArg τ (a.property.2.relation hga hcpos d)
  have hu' := hr (reqAt R F req hreqGrade d)
  simp only [reqAt,oldAt,F.source_old,hreq] at hu'
  change τ (min _ (R.cut v₀)) = τ (R.sel v₀ d) at he
  rwa [hτ.mono.map_min,hu',hcut,hsel,min_assoc,min_eq_right ((R.cut_le_cap _).trans hm)] at he

end
end VaughtConjecture.Knight.OrdinaryFinalReadback
