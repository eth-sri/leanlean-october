module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrinciplePiecewise
import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrincipleSlab

/-!
# Maximum principle on a moving ball or bounded interval

This is the finite-subdivision maximum principle.
The theorem needs only continuous motion, slice regularity, and positive
semidefinite diffusion; the source's stronger hypotheses imply these directly.
The transported coordinate remains unrestricted throughout.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

/- The source's bounded admissible domains have compact closure. -/
theorem isCompact_closure_of_maximumPrinciple_domain {d Ω}
    (hΩ : (∃ c R, 0 < R ∧ Ω = PDE.euclideanBall c R) ∨
      (∃ hd : d = 1, ∃ a b, a < b ∧ hd ▸ Ω = PDE.oneDimensionalAxisBox a b)) :
    IsCompact (closure Ω) := by
  rcases hΩ with ⟨c, R, hR, rfl⟩ | ⟨hd, a, b, hab, heq⟩
  · exact (Metric.isBounded_ball.subset (PDE.euclideanBall_subset_supBall hR)).isCompact_closure
  · cases hd
    have heq' : Ω = PDE.oneDimensionalAxisBox a b := by simpa using heq
    rw [heq']
    exact (PDE.isBoundedDomain_axisBox (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)).isBounded
      |>.isCompact_closure

/- Maximum principle on the entire closed moving tube over a finite subdivision.
This includes initial, terminal, lateral, and subdivision slices. The source's
piecewise C¹ curve assumption can be weakened to continuity. -/
theorem movingDomain_maximumPrinciple {d Ω γ B drift u}
    (hΩ : (∃ c R, 0 < R ∧ Ω = PDE.euclideanBall c R) ∨
      (∃ hd : d = 1, ∃ a b, a < b ∧ hd ▸ Ω = PDE.oneDimensionalAxisBox a b))
    (n : ℕ) :
    ∀ (r : Fin (n + 2) → ℝ) (_ : StrictMono r)
    (_ : ContinuousOn γ (Icc (r 0) (r (Fin.last (n + 1)))))
    (_ : ContinuousOn u (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))))
    (_ : IsTransportIndependentOn u (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))) ∨
      IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))))
    (_ : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube Ω γ (r i.castSucc) (r i.succ),
      DifferentiableAt ℝ (fun t => u ⟨t, p.position, p.velocity⟩) p.time ∧
      ContDiffAt ℝ 2 (fun v => u ⟨p.time, v, p.velocity⟩) p.position ∧
      DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (_ : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube Ω γ (r i.castSucc) (r i.succ),
      (B p.time p.position p.velocity).PosSemidef)
    (_ : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube Ω γ (r i.castSucc) (r i.succ),
      0 ≤ transportedForwardOperator B drift u p)
    (_ : ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))),
      p.time = r (Fin.last (n + 1)) → u p ≤ 0)
    (_ : ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))),
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p ≤ 0),
    ∀ q ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))), u q ≤ 0 := by
  have hopen := isOpen_of_isAdmissibleEvolutionDomain (Or.inr hΩ)
  have hcΩ := (isCompact_closure_of_maximumPrinciple_domain hΩ)
  induction n with
  | zero =>
    intro r hr hγ hu hc hreg hB hsub ht hl
    exact nonpos_on_maximumClosedTube (hr (by decide)) hopen hcΩ hγ hu hc
      (hreg 0) (hB 0) (hsub 0) ht hl
  | succ n ih =>
    intro r hr hγ hu hc hreg hB hsub ht hl
    let s : Fin (n + 2) → ℝ := fun i => r i.succ
    have hs : StrictMono s := hr.comp Fin.strictMono_succ
    have htail : maximumClosedTube Ω γ (s 0) (s (Fin.last (n + 1))) ⊆
        maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 2))) := by
      intro p hp
      exact ⟨⟨(hr.monotone (Fin.zero_le _)).trans hp.1.1, hp.1.2⟩, hp.2⟩
    have hcTail : IsTransportIndependentOn u
        (maximumClosedTube Ω γ (s 0) (s (Fin.last (n + 1)))) ∨
        IsUniformlyNegAtInfinityOn u
        (maximumClosedTube Ω γ (s 0) (s (Fin.last (n + 1)))) := by
      rcases hc with hi | hn
      · exact Or.inl (fun p hp => hi p (htail hp))
      · right
        intro M
        obtain ⟨R, hR, hb⟩ := hn M
        exact ⟨R, hR, fun p hp => hb p (htail hp)⟩
    have htailResult := ih s hs
      (hγ.mono (Icc_subset_Icc (hr.monotone (Fin.zero_le _)) le_rfl))
      (hu.mono htail) hcTail
      (fun i => hreg i.succ) (fun i => hB i.succ) (fun i => hsub i.succ)
      (fun p hp => ht p (htail hp)) (fun p hp => hl p (htail hp))
    have hhead : maximumClosedTube Ω γ (r 0) (s 0) ⊆
        maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 2))) := by
      intro p hp
      exact ⟨⟨hp.1.1, hp.1.2.trans (hr.monotone (Fin.le_last _))⟩, hp.2⟩
    have hcHead : IsTransportIndependentOn u (maximumClosedTube Ω γ (r 0) (s 0)) ∨
        IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ (r 0) (s 0)) := by
      rcases hc with hi | hn
      · exact Or.inl (fun p hp => hi p (hhead hp))
      · right
        intro M
        obtain ⟨R, hR, hb⟩ := hn M
        exact ⟨R, hR, fun p hp => hb p (hhead hp)⟩
    have hheadResult := nonpos_on_maximumClosedTube
      (hr (show (0 : Fin (n + 3)) < (0 : Fin (n + 2)).succ by simp)) hopen hcΩ
      (hγ.mono (Icc_subset_Icc le_rfl (hr.monotone (Fin.le_last _))))
      (hu.mono hhead) hcHead (hreg 0) (hB 0) (hsub 0)
      (fun p hp heq => htailResult p
        ⟨⟨heq.ge, (hhead hp).1.2⟩, hp.2⟩)
      (fun p hp => hl p (hhead hp))
    intro q hq
    by_cases hqtime : q.time ≤ s 0
    · exact hheadResult q ⟨⟨hq.1.1, hqtime⟩, hq.2⟩
    · exact htailResult q ⟨⟨(lt_of_not_ge hqtime).le, hq.1.2⟩, hq.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Decay
