module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

/-! # Finite real oscillation on bounded value sets -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

variable {d : ℕ} {u : KineticPoint d → ℝ} {E : Set (KineticPoint d)} (hne : E.Nonempty)
    (hE : IsCompact (closure E)) (hu : ContinuousOn u (closure E)) (hab : BddAbove (u '' E))
    (hbb : BddBelow (u '' E)) {P : KineticPoint d} (hP : P ∈ closure E)

/-- Values on a bounded image lie below its real supremum. -/
theorem le_sup_values (hE : BddAbove (u '' E)) {P : KineticPoint d}
    (hP : P ∈ E) : u P ≤ sSup (u '' E) := le_csSup hE (mem_image_of_mem u hP)

/-- Values on a bounded image lie above its real infimum. -/
theorem inf_values_le (hE : BddBelow (u '' E)) {P : KineticPoint d}
    (hP : P ∈ E) : sInf (u '' E) ≤ u P := csInf_le hE (mem_image_of_mem u hP)

include hne hab hbb in
/-- Nonempty bounded value sets have nonnegative oscillation. -/
theorem oscillationOn_nonneg : 0 ≤ oscillationOn u E := by
  obtain ⟨P, hP⟩ := hne
  exact sub_nonneg.mpr ((inf_values_le hbb hP).trans (le_sup_values hab hP))

include hab hbb in
/-- Any difference of values is controlled by the literal oscillation. -/
theorem abs_sub_le_oscillationOn
    {P Q : KineticPoint d} (hP : P ∈ E) (hQ : Q ∈ E) :
    |u P - u Q| ≤ oscillationOn u E := by
  rw [abs_le, oscillationOn]
  constructor
  · linarith only [le_sup_values hab hQ, inf_values_le hbb hP]
  · exact sub_le_sub (le_sup_values hab hP) (inf_values_le hbb hQ)

/-- Passing to a smaller nonempty set cannot increase finite oscillation. -/
theorem oscillationOn_mono
    {E F : Set (KineticPoint d)} (hne : E.Nonempty) (hEF : E ⊆ F)
    (hab : BddAbove (u '' F)) (hbb : BddBelow (u '' F)) :
    oscillationOn u E ≤ oscillationOn u F := sub_le_sub (csSup_le_csSup hab (hne.image u) (image_mono hEF))
    (csInf_le_csInf hbb (hne.image u) (image_mono hEF))

include hne in
/-- Uniform upper and lower bounds control the real oscillation. -/
theorem oscillationOn_le {a b : ℝ}
    (hlo : ∀ P ∈ E, a ≤ u P) (hhi : ∀ P ∈ E, u P ≤ b) :
    oscillationOn u E ≤ b - a := by
  apply sub_le_sub
  · exact csSup_le (hne.image u) (by simp_all)
  · exact le_csInf (hne.image u) (by simp_all)

include hne hab in
/-- Positive affine transformations transport a finite real supremum exactly. -/
theorem sup_values_pos_affine
    (a b : ℝ) (ha : 0 < a) :
    sSup ((fun P => a * u P + b) '' E) = a * sSup (u '' E) + b := by
  have h := ((OrderIso.mulLeft₀ a ha).trans (OrderIso.addRight b)).map_csSup'
    (hne.image u) hab
  simpa [image_image] using h.symm

include hu hab hP in
/-- Continuity preserves the upper value bound on the closure. -/
theorem closure_values_le_sup :
    u P ≤ sSup (u '' E) := by
  exact (closure_minimal (fun _ hv => le_csSup hab hv) isClosed_Iic) (hu.image_closure (mem_image_of_mem u hP))

include hu hbb hP in
/-- Continuity preserves the lower value bound on the closure. -/
theorem inf_le_closure_values :
    sInf (u '' E) ≤ u P := by
  exact (closure_minimal (fun _ hv => csInf_le hbb hv) isClosed_Ici) (hu.image_closure (mem_image_of_mem u hP))

include hne hE hu in
/-- Compact closure and continuity make closure oscillation equal open-set oscillation. -/
theorem oscillationOn_closure : oscillationOn u (closure E) = oscillationOn u E := by
  have hab := hE.bddAbove_image hu
  have hbb := hE.bddBelow_image hu
  have hs : sSup (u '' closure E) = sSup (u '' E) := by
    apply le_antisymm
    · apply csSup_le ((hne.mono subset_closure).image u)
      rintro _ ⟨P, hP, rfl⟩
      exact closure_values_le_sup hu (hab.mono (image_mono subset_closure)) hP
    · exact csSup_le_csSup hab (hne.image u) (image_mono subset_closure)
  have hi : sInf (u '' closure E) = sInf (u '' E) := by
    apply le_antisymm
    · exact csInf_le_csInf hbb (hne.image u) (image_mono subset_closure)
    · apply le_csInf ((hne.mono subset_closure).image u)
      rintro _ ⟨P, hP, rfl⟩
      exact inf_le_closure_values hu (hbb.mono (image_mono subset_closure)) hP
  simp only [oscillationOn, hs, hi]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
