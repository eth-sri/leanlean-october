module
public import HypoellipticAleksandrov.Parabolic.Transposition.Solvability
import Mathlib

/-! # Smooth approximation of an envelope on an unbounded domain

The adjoint estimate is local to the supports of the test and its image. It persists
under uniform approximation of the second barrier from above, including barriers for
moving domains with only Lipschitz boundary motion.
-/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open Hypoellipticity Set MeasureTheory Filter
open scoped ENNReal
variable {d k : ℕ} {U : Domain d}

private theorem localize_integral (m : TimeVelocity d → ℝ) (t : Test U) {S D : Set (TimeVelocity d)}
    (hS : tsupport t ⊆ S) (hD : tsupport t ⊆ D) :
    (∫ x in S, m x * |t x|) = ∫ x in D, m x * |t x| := by
  have eq (S : Set _) (hs : tsupport t ⊆ S) : (∫ x in S, m x * |t x|) = ∫ x, m x * |t x| :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [image_eq_zero_of_notMem_tsupport (mt (@hs x) hx)]
  rw [eq S hS,eq D hD]

set_option maxHeartbeats 1500000 in
theorem solve_with_barriers (X : Fin (k+1) → Vector d)
    (span : KineticAleksandrov.LieAlgebraSpansOn ((unpack d) ⁻¹' (U : Set _)) (fun i => liftField (X i)))
    (F f : Field d) (g : TimeVelocity d → ℝ) (hc : Continuous g) {M : TimeVelocity d → ℝ} {C : ℝ} (cm : Continuous M)
    (hM : ∀ z ∈ U, 0 ≤ M z) (hF : ∀ z ∈ U, |F.val z| ≤ M z)
    (hf : ∀ z ∈ U, 0 ≤ f.val z ∧ f.val z ≤ C ∧ generator X f.val z ≤ -M z)
    (hg : ∀ z ∈ U, 0 ≤ g z)
    (ha : ∀ ε > (0 : ℝ), ∃ G : Field d, ∀ z ∈ U,
      0 ≤ G.val z ∧ generator X G.val z ≤ -M z ∧ G.val z ≤ g z + ε) :
    ∃ w : Local U, EqOn (generator X w.val) F.val U ∧ ∀ z ∈ U, |w.val z| ≤ min (f.val z) (g z) := by
  let B z := min (f.val z) (g z)
  have hB : Continuous B := f.prop.continuous.min hc
  apply solve_under X span F B hB (fun z hz => ⟨le_min (hf z hz).1 (hg z hz),(min_le_left ..).trans (hf z hz).2.1⟩)
  intro φ
  let A := adjoint X φ
  obtain ⟨r,hr⟩ := (φ.hasCompactSupport.isBounded.union A.hasCompactSupport.isBounded).subset_ball 0
  let V : Domain d := ⟨(U : Set _) ∩ Metric.ball 0 r,U.isOpen.inter Metric.isOpen_ball⟩
  have ss : (V : Set (TimeVelocity d)) ⊆ U := inter_subset_left
  have vsub : (V : Set (TimeVelocity d)) ⊆ Metric.ball 0 r := inter_subset_right
  have K : IsCompact (closure (V : Set (TimeVelocity d))) := (Metric.isBounded_ball.subset vsub).isCompact_closure
  have tφ : tsupport φ ⊆ V := subset_inter φ.tsupport_subset (union_subset_iff.mp hr).1
  have tA : tsupport A ⊆ V := subset_inter A.tsupport_subset (union_subset_iff.mp hr).2
  let ψ : Test V := ⟨φ,φ.contDiff,φ.hasCompactSupport,tφ⟩
  have hp : (adjoint X ψ : TimeVelocity d → ℝ) = A := adjoint_congr X (φ := ψ) (ψ := φ) rfl
  rw [weight_apply (F.prop.continuous.locallyIntegrable.locallyIntegrableOn U),← Real.norm_eq_abs]
  have iφ : IntegrableOn (fun z => M z * |φ z|) U :=
    ((cm.mul φ.contDiff.continuous.abs).integrable_of_hasCompactSupport (φ.hasCompactSupport.abs.mul_left)).integrableOn
  apply (norm_integral_le_of_norm_le (f := fun z => F.val z * φ z) iφ ((ae_restrict_mem U.isOpen.measurableSet).mono fun z hz => by
    rw [Real.norm_eq_abs,abs_mul]; exact mul_le_mul_of_nonneg_right (hF z hz) (abs_nonneg _))).trans
  rw [localize_integral _ φ φ.tsupport_subset tφ, localize_integral _ A A.tsupport_subset tA]
  apply discard_error (C := ∫ z in V, |A z|); intro ε hε
  obtain ⟨G,hG⟩ := ha ε hε
  apply (min_adjoint_estimate K X f G cm (fun z hz => hM z (ss hz)) (fun z hz => ⟨(hf z (ss hz)).1,(hf z (ss hz)).2.2⟩)
    (fun z hz => ⟨(hG z (ss hz)).1,(hG z (ss hz)).2.1⟩) ψ).trans
  rw [hp,← integral_const_mul]
  have cA := A.contDiff.continuous.abs
  erw [← integral_add (int_cont K (hB.mul cA)) (int_cont K (continuous_const.mul cA))]
  apply setIntegral_mono_on (int_cont K ((f.prop.continuous.min G.prop.continuous).mul cA))
    (int_cont K ((hB.mul cA).add (continuous_const.mul cA))) V.isOpen.measurableSet
  intro z hz; rw [← add_mul]; apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  simpa [B,min_add_add_right] using min_le_min (le_add_of_nonneg_right hε.le (a := f.val z)) (hG z (ss hz)).2.2

end HypoellipticAleksandrov.Parabolic.Transposition
