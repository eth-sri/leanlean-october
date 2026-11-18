module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AdmissibilityCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Topology.Order.Lattice

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Set MeasureTheory


/-- Values on a bounded image lie below its real supremum. -/
theorem le_sup_values {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hE : BddAbove (u '' E)) {P : KineticPoint d}
    (hP : P ∈ E) : u P ≤ sSup (u '' E) := le_csSup hE (mem_image_of_mem u hP)

/-- Values on a bounded image lie above its real infimum. -/
theorem inf_values_le {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hE : BddBelow (u '' E)) {P : KineticPoint d}
    (hP : P ∈ E) : sInf (u '' E) ≤ u P := csInf_le hE (mem_image_of_mem u hP)

/-- Nonempty bounded value sets have nonnegative oscillation. -/
theorem oscillationOn_nonneg {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hne : E.Nonempty)
    (hab : BddAbove (u '' E)) (hbb : BddBelow (u '' E)) : 0 ≤ oscillationOn u E := by
  obtain ⟨P, hP⟩ := hne
  exact sub_nonneg.mpr ((inf_values_le hbb hP).trans (le_sup_values hab hP))

/-- Any difference of values is controlled by the literal oscillation. -/
theorem abs_sub_le_oscillationOn {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hab : BddAbove (u '' E)) (hbb : BddBelow (u '' E))
    {P Q : KineticPoint d} (hP : P ∈ E) (hQ : Q ∈ E) :
    |u P - u Q| ≤ oscillationOn u E := by
  rw [abs_le, oscillationOn]
  constructor
  · linarith only [le_sup_values hab hQ, inf_values_le hbb hP]
  · exact sub_le_sub (le_sup_values hab hP) (inf_values_le hbb hQ)

/-- Passing to a smaller nonempty set cannot increase finite oscillation. -/
theorem oscillationOn_mono {d : ℕ} {u : KineticPoint d → ℝ}
    {E F : Set (KineticPoint d)} (hne : E.Nonempty) (hEF : E ⊆ F)
    (hab : BddAbove (u '' F)) (hbb : BddBelow (u '' F)) :
    oscillationOn u E ≤ oscillationOn u F := by
  exact sub_le_sub (csSup_le_csSup hab (hne.image u) (image_mono hEF))
    (csInf_le_csInf hbb (hne.image u) (image_mono hEF))

/-- Uniform upper and lower bounds control the real oscillation. -/
theorem oscillationOn_le {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hne : E.Nonempty) {a b : ℝ}
    (hlo : ∀ P ∈ E, a ≤ u P) (hhi : ∀ P ∈ E, u P ≤ b) :
    oscillationOn u E ≤ b - a := by
  apply sub_le_sub
  · exact csSup_le (hne.image u) (by rintro _ ⟨P, hP, rfl⟩; exact hhi P hP)
  · exact le_csInf (hne.image u) (by rintro _ ⟨P, hP, rfl⟩; exact hlo P hP)



/-- Continuity preserves the upper value bound on the closure. -/
theorem closure_values_le_sup {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hu : ContinuousOn u (closure E))
    (hab : BddAbove (u '' E)) {P : KineticPoint d} (hP : P ∈ closure E) :
    u P ≤ sSup (u '' E) := by
  have hsub : u '' E ⊆ Iic (sSup (u '' E)) := fun _ hv => le_csSup hab hv
  exact (closure_minimal hsub isClosed_Iic) (hu.image_closure (mem_image_of_mem u hP))

/-- Continuity preserves the lower value bound on the closure. -/
theorem inf_le_closure_values {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hu : ContinuousOn u (closure E))
    (hbb : BddBelow (u '' E)) {P : KineticPoint d} (hP : P ∈ closure E) :
    sInf (u '' E) ≤ u P := by
  have hsub : u '' E ⊆ Ici (sInf (u '' E)) := fun _ hv => csInf_le hbb hv
  exact (closure_minimal hsub isClosed_Ici) (hu.image_closure (mem_image_of_mem u hP))

/-- Compact closure and continuity make closure oscillation equal open-set oscillation. -/
theorem oscillationOn_closure {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hne : E.Nonempty) (hE : IsCompact (closure E))
    (hu : ContinuousOn u (closure E)) : oscillationOn u (closure E) = oscillationOn u E := by
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



/-- Positive affine transformations preserve precisely the same Aleksandrov data. -/
theorem admissible_pos_affine {d : ℕ} {A : FullKineticCoefficient d}
    {O : Set (KineticPoint d)} {p C_A : ℝ} {u : KineticPoint d → ℝ}
    (hu : IsAdmissibleSupersolution A O p C_A u) (a b : ℝ) (ha : 0 < a) :
    IsAdmissibleSupersolution A O p C_A (fun P => a * u P + b)  := by
  have sup_values_pos_affine {u : KineticPoint d → ℝ} {E : Set (KineticPoint d)} (hne : E.Nonempty) (hab : BddAbove (u '' E)) (b : ℝ) :
      sSup ((fun P => a * u P + b) '' E) = a * sSup (u '' E) + b := by
    have h := ((OrderIso.mulLeft₀ a ha).trans (OrderIso.addRight b)).map_csSup'
      (hne.image u) hab
    simpa only [OrderIso.trans_apply, OrderIso.mulLeft₀_apply, OrderIso.addRight_apply,
      image_image, Function.comp_def] using h.symm
  refine ⟨continuousOn_const.mul hu.1 |>.add continuousOn_const, ?_⟩
  intro P₀ R hR hQ psi hpsi
  let phi : KineticPoint d → ℝ := fun P => a⁻¹ * psi P + (-b/a)
  have hphi : IsSmoothNear phi (closure (backwardCylinder P₀ R)) :=
    hpsi.affine _ _
  have heq : psi = fun P => a * phi P + b := by
    funext P
    dsimp [phi]
    field_simp
    ring
  have hd : (fun P => psi P - (a*u P+b)) = fun P => a*(phi P-u P) := by
    funext P
    rw [heq]
    ring
  have hm : (fun P => max (psi P-(a*u P+b)) 0) =
      fun P => a * max (phi P-u P) 0 := by
    funext P
    rw [show psi P-(a*u P+b) = a*(phi P-u P) from congrFun hd P]
    rw [mul_max_of_nonneg _ _ ha.le, mul_zero]
  have hcompact := isCompact_closure_backwardCylinder P₀ R hR
  have hcont := hphi.continuousOn.sub (hu.1.mono hQ)
  have hB : kineticBoundary P₀ R ⊆ closure (backwardCylinder P₀ R) := fun _ h => h.1
  have habB := (hcompact.bddAbove_image (hcont.sup (continuousOn_const (c := 0)))).mono
    (image_mono hB)
  have hs : sSup ((fun P => psi P-(a*u P+b)) '' closure (backwardCylinder P₀ R)) =
      a * sSup ((fun P => phi P-u P) '' closure (backwardCylinder P₀ R)) := by
    rw [hd]
    simpa using sup_values_pos_affine ((backwardCylinder_nonempty P₀ hR).mono subset_closure) (hcompact.bddAbove_image hcont) 0
  have hsB : sSup ((fun P => max (psi P-(a*u P+b)) 0) '' kineticBoundary P₀ R) =
      a * sSup ((fun P => max (phi P-u P) 0) '' kineticBoundary P₀ R) := by
    rw [hm]
    simpa using sup_values_pos_affine (kineticBoundary_nonempty P₀ hR) habB 0
  have hsource : localizedSource A psi (fun P => a*u P+b) =ᵐ[
      volume.restrict (backwardCylinder P₀ R)] a • localizedSource A phi u := by
    filter_upwards [ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet] with P hP
    have hop : backwardOperator A psi P = a * backwardOperator A phi P := by
      rw [heq]
      exact backwardOperator_affine A hphi (subset_closure hP) a b
    have hlt : a*u P+b < psi P ↔ u P < phi P := by
      rw [heq]
      exact (add_lt_add_iff_right b).trans (mul_lt_mul_iff_right₀ ha)
    simp only [localizedSource, indicator_apply, mem_ofPred_eq, hlt, hop, Pi.smul_apply,
      smul_eq_mul]
    split_ifs
    · rw [mul_max_of_nonneg _ _ ha.le, mul_zero]
    · simp
  have hn : (eLpNorm (localizedSource A psi (fun P => a*u P+b)) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₀ R))).toReal =
      a * (eLpNorm (localizedSource A phi u) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R))).toReal := by
    rw [eLpNorm_congr_ae hsource, eLpNorm_const_smul, ENNReal.toReal_mul]
    simp [Real.norm_eq_abs, abs_of_pos ha]
  rw [hs, hsB, hn]
  convert (mul_le_mul_of_nonneg_left (hu.2 P₀ R hR hQ phi hphi) ha.le) using 1
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder

