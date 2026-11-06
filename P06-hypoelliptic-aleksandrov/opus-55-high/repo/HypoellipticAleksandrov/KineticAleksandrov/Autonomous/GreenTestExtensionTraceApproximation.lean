module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionGap
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense
import Mathlib.Topology.TietzeExtension

/-! # Genuine smooth compact approximation of bounded continuous future slab traces -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov Topology
open SectionTwo TheoremA Evolution
open scoped CompactlySupported

/-- A bounded continuous future slab trace admits uniformly bounded smooth compact probes,
with arbitrary accuracy on every specified finite position box. -/
theorem exists_reconstruction_smooth_trace_probe
    (H : Interval) (a T : ℝ) (ha : a < T) (u : Point → ℝ)
    (hc : ContinuousOn u (reconstructionClosedSlab H a T)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ p ∈ reconstructionClosedSlab H a T, |u p| ≤ M)
    (R eps : ℝ) (heps : 0 < eps) :
    ∃ F : exitProbeSubmodule,
      (∀ p, |exitProbePhysical F p| ≤ M + eps) ∧
      ∀ p ∈ reconstructionClosedSlab H a T, |p.position 0| ≤ R →
        |exitProbePhysical F p - u p| ≤ eps := by
  let D := reconstructionClosedSlab H a T
  have hD : IsClosed D := by
    change IsClosed (reconstructionClosedSlab H a T)
    rw [← closure_reconstructionStrip H a T ha]
    simp
  let f : BoundedContinuousFunction D ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => u p.1) (continuousOn_iff_continuous_domRestrict.mp hc) M
    (fun p => by simp_all)
  let j : D → EvolutionVec 1 := fun p => reconstructionPhysicalHomeomorph.symm p.1
  have hj : IsClosedEmbedding j := reconstructionPhysicalHomeomorph.symm.isClosedEmbedding.comp
    hD.isClosedEmbedding_subtypeVal
  obtain ⟨G, hGb, hG⟩ :=
    BoundedContinuousFunction.exists_extension_forall_mem_Icc_of_isClosedEmbedding f
      (fun p => abs_le.mp (hb p.1 p.2)) (by linarith) hj
  let pack (q : ℝ × ℝ × ℝ) : EvolutionVec 1 :=
    packPoint q.1 (fun _ => q.2.2) (fun _ => q.2.1)
  let K  := pack '' (Icc a T ×ˢ (Icc (-R) R ×ˢ Icc H.lo H.hi))
  have hp : Continuous pack := by
    change Continuous (fun q : ℝ × ℝ × ℝ =>
      (evolutionProdCLE 1).symm (q.1, (fun _ => q.2.2), (fun _ => q.2.1)))
    fun_prop
  have hK : IsCompact K := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image hp
  obtain ⟨chi, hchi, hcc, _, hcb, hone⟩ :=
    exists_smooth_bump_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ _)
  let g : C_c(EvolutionVec 1, ℝ) :=
    ⟨⟨fun x => chi x * G x, hchi.continuous.mul G.continuous⟩, hcc.mul_right⟩
  obtain ⟨s, hs, hclose⟩ := exists_smooth_compact_probe_close g eps heps
  let F : exitProbeSubmodule := ⟨s, hs, s.hasCompactSupport⟩
  have hg (x : EvolutionVec 1) : |g x| ≤ M := by
    change |chi x * G x| ≤ M
    rw [abs_mul, abs_of_nonneg (hcb x).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hcb x).2).trans (abs_le.mpr (hGb x))
  refine ⟨F, ?_, ?_⟩
  · intro p
    change |s (reconstructionPhysicalHomeomorph.symm p)| ≤ _
    grind
  · intro p hpd hpr
    have hpk : reconstructionPhysicalHomeomorph.symm p ∈ K := by
      refine ⟨(p.time, p.position 0, p.velocity 0),
        ⟨⟨hpd.1, hpd.2.1⟩, abs_le.mp hpr, hpd.2.2⟩, ?_⟩
      ext i
      fin_cases i <;> rfl
    have hGp : G (reconstructionPhysicalHomeomorph.symm p) = u p :=
      congrFun hG ⟨p, hpd⟩
    have hgp : g (reconstructionPhysicalHomeomorph.symm p) = u p := by
      change chi _ * G _ = _
      simp_all
    change |s (reconstructionPhysicalHomeomorph.symm p) - u p| ≤ _
    grind

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
