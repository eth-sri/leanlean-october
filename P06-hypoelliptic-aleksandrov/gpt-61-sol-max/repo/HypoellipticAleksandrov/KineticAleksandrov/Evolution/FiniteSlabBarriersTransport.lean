module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierChain
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveLipschitz

/-!
# Finite-slab transport for the collar comparison

The collar comparison `collar_piece` assumes that the boundary curve is globally
Lipschitz.  A continuous piecewise `C¹` curve is only Lipschitz on compact intervals, so for
the two barriers (companion paper, (A.1), on a finite slab) we use the constant extension
`slabExtension γ t₁ t₂` of the curve past a smooth piece `[t₁, t₂]`: it agrees with `γ` on the
piece, hence has the same moving slabs, collar regions and supersolution values there, but is
globally Lipschitz.

This file proves the transport lemmas and `collar_piece_of_lipschitzOn`,
`collar_chain_of_lipschitzOn`, the finite-slab versions of `collar_piece` and `collar_chain`
whose only change is that the Lipschitz hypothesis is required on the time interval of the slab.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov

open Set
open scoped MatrixOrder

variable {n : ℕ}

variable {Ω : PDE.VelocityRegion n} {γ γ' : ℝ → PDE.Vec n}

/-- The moving domain only depends on the value of the curve at the given time. -/
theorem movingDomain_congr_of_eq   {σ : ℝ}
    (h : γ' σ = γ σ) : movingDomain Ω γ' σ = movingDomain Ω γ σ := by
  unfold movingDomain
  rw [h]

section
variable {a b : ℝ} (h : ∀ σ ∈ Icc a b, γ' σ = γ σ)

include h
/-- Curves agreeing on `[a, b]` have the same closed moving slab. -/
theorem movingClosedSlab_congr    :
    movingClosedSlab Ω γ' a b = movingClosedSlab Ω γ a b := by
  ext p
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rwa [movingDomain_congr_of_eq (h _ ⟨h1, h2⟩)] at h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rwa [movingDomain_congr_of_eq (h _ ⟨h1, h2⟩)]

/-- Curves agreeing on `[a, b]` have the same active moving slab. -/
theorem movingActiveSlab_congr    :
    movingActiveSlab Ω γ' a b = movingActiveSlab Ω γ a b := by
  ext p
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rwa [movingDomain_congr_of_eq (h _ ⟨h1, h2.le⟩)] at h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rwa [movingDomain_congr_of_eq (h _ ⟨h1, h2.le⟩)]
end


variable {c : PDE.Vec n}

/-- The squared distance to the moving centre only depends on the curve at the given time. -/
theorem centreSq_congr_of_eq   {γ γ' : ℝ → PDE.Vec n} {p : KineticPoint n}
    (h : γ' p.time = γ p.time) : centreSq c γ' p = centreSq c γ p := by
  unfold centreSq
  rw [h]

/-- Curves agreeing on `[a, b]` have the same closed collar region. -/
theorem collarClosed_congr   {r₀ dstar : ℝ} {γ γ' : ℝ → PDE.Vec n}
    {a b : ℝ} (h : ∀ σ ∈ Icc a b, γ' σ = γ σ) :
    collarClosed c r₀ dstar γ' a b = collarClosed c r₀ dstar γ a b := by
  ext p
  unfold collarClosed
  rw [movingClosedSlab_congr h]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [Set.mem_ofPred_eq, centreSq_congr_of_eq (h _ ⟨h1.1, h1.2.1⟩)] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [Set.mem_ofPred_eq, centreSq_congr_of_eq (h _ ⟨h1.1, h1.2.1⟩)]

/-- The collar supersolution only depends on the curve at the time of the point. -/
theorem collarSupersolution_congr_of_eq   {r₀ dstar Lγ lam FB : ℝ}
    {γ γ' : ℝ → PDE.Vec n} {p : KineticPoint n} (h : γ' p.time = γ p.time) :
    collarSupersolution c r₀ dstar Lγ lam FB γ' p =
      collarSupersolution c r₀ dstar Lγ lam FB γ p := by
  unfold collarSupersolution collarBarrier
  simp only [h]

variable {r₀ dstar : ℝ} (hd : 0 < dstar) (hdr : dstar < r₀) {γ : ℝ → PDE.Vec n}

include hd hdr
/-- Collar comparison on one smooth piece `[t₁, t₂]`, with the Lipschitz bound of the curve only
on `[t₁, t₂]`. -/
theorem collar_piece_of_lipschitzOn    (hγ : Continuous γ) {Lγ : ℝ} (hLγ : 0 ≤ Lγ)
    {t₁ t₂ : ℝ} (hγL : CurveLipschitzOn γ Lγ (Icc t₁ t₂)) (ht : t₁ < t₂)
    (hdiff : ∀ σ ∈ Ioo t₁ t₂, DifferentiableAt ℝ γ σ)
    {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.VectorField n}
    (hb : HasEuclideanLipschitzDrift Lb b) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {FB : ℝ} (hFB : 0 ≤ FB) {v : HypoellipticAleksandrov.KineticScalarField n}
    (hbdd : ∃ M, ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ t₁ t₂, v p ≤ M)
    (hcont : ContinuousOn v (movingClosedSlab (PDE.euclideanBall c r₀) γ t₁ t₂))
    (hreg : ∀ p ∈ movingActiveSlab (PDE.euclideanBall c r₀) γ t₁ t₂, IsSliceRegularAt v p)
    (hop : ∀ p ∈ movingActiveSlab (PDE.euclideanBall c r₀) γ t₁ t₂,
      0 ≤ viscousTransportedOperator B b ε v p)
    (hlat : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ t₁ t₂,
      p.position ∈ frontier (movingDomain (PDE.euclideanBall c r₀) γ p.time) → v p ≤ 0)
    (hFBle : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ t₁ t₂, v p ≤ FB)
    (htop : ∀ p ∈ collarClosed c r₀ dstar γ t₁ t₂, p.time = t₂ →
      v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p) :
    ∀ p ∈ collarClosed c r₀ dstar γ t₁ t₂, v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := by
  have hext : ∀ σ ∈ Icc t₁ t₂, slabExtension γ t₁ t₂ σ = γ σ := fun σ hσ =>
    slabExtension_eq γ hσ
  have hS := movingClosedSlab_congr (Ω := PDE.euclideanBall c r₀) hext
  have hA := movingActiveSlab_congr (Ω := PDE.euclideanBall c r₀) hext
  have hK := collarClosed_congr (c := c) (r₀ := r₀) (dstar := dstar) hext
  have hdiff'  := fun σ hσ =>
    (hdiff σ hσ).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (Icc_mem_nhds hσ.1 hσ.2) hext)
  have key := collar_piece hd hdr (continuous_slabExtension hγ t₁ t₂) hLγ
    (slabExtension_lipschitz ht.le hLγ hγL) ht hdiff' hlam hB hb hε0 hε1 hFB (v := v)
    (by rw [hS]; exact hbdd) (by rw [hS]; exact hcont) (by rw [hA]; exact hreg)
    (by rw [hA]; exact hop)
    (fun p hp hfr => by
      rw [hS] at hp
      rw [movingDomain_congr_of_eq (hext _ ⟨hp.1, hp.2.1⟩)] at hfr
      exact hlat p hp hfr)
    (by rw [hS]; exact hFBle)
    (fun p hp hpt => by
      rw [hK] at hp
      rw [collarSupersolution_congr_of_eq (hext _ ⟨hp.1.1, hp.1.2.1⟩)]
      exact htop p hp hpt)
  intro p hp

  have := key p (by rw [hK]; exact hp)
  rwa [collarSupersolution_congr_of_eq (hext _ ⟨hp.1.1, hp.1.2.1⟩)] at this

/-- Collar comparison across the pieces of a piecewise `C¹` curve that is Lipschitz on the
finite slab `[a, τ]` only. -/
theorem collar_chain_of_lipschitzOn    (hγpw : IsContinuousPiecewiseC1 γ) {Lγ : ℝ}
    (hLγ : 0 ≤ Lγ) {a τ : ℝ} (hγL : CurveLipschitzOn γ Lγ (Icc a τ)) (haτ : a < τ)
    {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.VectorField n}
    (hb : HasEuclideanLipschitzDrift Lb b) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {FB : ℝ} (hFB : 0 ≤ FB) {v : HypoellipticAleksandrov.KineticScalarField n}
    (hbdd : ∃ M, ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ a τ, v p ≤ M)
    (hcont : ContinuousOn v (movingClosedSlab (PDE.euclideanBall c r₀) γ a τ))
    (hreg : ∀ p ∈ movingActiveSlab (PDE.euclideanBall c r₀) γ a τ, IsSliceRegularAt v p)
    (hop : ∀ p ∈ movingActiveSlab (PDE.euclideanBall c r₀) γ a τ,
      0 ≤ viscousTransportedOperator B b ε v p)
    (hlat : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ a τ,
      p.position ∈ frontier (movingDomain (PDE.euclideanBall c r₀) γ p.time) → v p ≤ 0)
    (hFBle : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ a τ, v p ≤ FB)
    (htop : ∀ p ∈ collarClosed c r₀ dstar γ a τ, p.time = τ →
      v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p) :
    ∀ p ∈ collarClosed c r₀ dstar γ a τ, v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := by
  obtain ⟨N, t, ht, h0, hl, hdiff⟩ := exists_partition_differentiableAt hγpw haτ
  let motive  := fun i =>
    ∀ p ∈ collarClosed c r₀ dstar γ (t i) τ, v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p


  have h' : ∀ p ∈ collarClosed c r₀ dstar γ (t 0) τ,
      v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := ((show ∀ i, motive i by
          intro i
          refine Fin.reverseInduction (motive := motive) ?_ ?_ i
          · intro p hp
            have hpτ : p.time = τ := by
              have h1 := hp.1.1

              rw [hl] at h1
              exact le_antisymm hp.1.2.1 h1
            exact htop p ⟨⟨by rw [hpτ]; exact haτ.le, hp.1.2.1, hp.1.2.2⟩, hp.2⟩ hpτ
          · intro i hprev p hp

            have ha : a ≤ t i.castSucc := by
              rw [← h0]
              exact ht.monotone (Fin.zero_le _)
            have hτ : t i.succ ≤ τ := by
              rw [← hl]
              exact ht.monotone (Fin.le_last _)
            by_cases hge : t i.succ ≤ p.time
            · exact hprev p ⟨⟨hge, hp.1.2.1, hp.1.2.2⟩, hp.2⟩
            ·
              have hres := collar_piece_of_lipschitzOn hd hdr hγpw.1 hLγ
                (fun s hs s' hs' => hγL s ⟨ha.trans hs.1, hs.2.trans hτ⟩ s'
                  ⟨ha.trans hs'.1, hs'.2.trans hτ⟩) (ht Fin.castSucc_lt_succ) (hdiff i) hlam hB hb hε0 hε1 hFB
                (v := v)
                ((Exists.casesOn hbdd fun M hM => Exists.intro M fun q hq => hM q (movingClosedSlab_mono ha hτ hq)))
                (hcont.mono (movingClosedSlab_mono ha hτ))
                (fun q hq => hreg q (movingActiveSlab_mono ha hτ hq))
                (fun q hq => hop q (movingActiveSlab_mono ha hτ hq))
                (fun q hq => hlat q (movingClosedSlab_mono ha hτ hq))
                (fun q hq => hFBle q (movingClosedSlab_mono ha hτ hq))
                (fun q hq hqt => hprev q ⟨⟨hqt.ge, by rw [hqt]; exact hτ, hq.1.2.2⟩, hq.2⟩)
              exact hres p ⟨⟨hp.1.1, (not_le.mp hge).le, hp.1.2.2⟩, hp.2⟩) 0)
  rw [h0] at h'
  exact h'

end HypoellipticAleksandrov.KineticAleksandrov
