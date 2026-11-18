module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierChain
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveLipschitz
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FiniteSlabBarriersTerminal

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology MatrixOrder


/-- The moving domain only depends on the value of the curve at the given time. -/
theorem movingDomain_congr_of_eq {n : ℕ} {Ω : Set (PDE.Vec n)} {γ γ' : ℝ → PDE.Vec n} {σ : ℝ}
    (h : γ' σ = γ σ) : movingDomain Ω γ' σ = movingDomain Ω γ σ := by
  unfold movingDomain
  rw [h]

/-- Curves agreeing on `[a, b]` have the same closed moving slab. -/
theorem movingClosedSlab_congr {n : ℕ} {Ω : Set (PDE.Vec n)} {γ γ' : ℝ → PDE.Vec n} {a b : ℝ}
    (h : ∀ σ ∈ Icc a b, γ' σ = γ σ) :
    movingClosedSlab Ω γ' a b = movingClosedSlab Ω γ a b := by
  ext p
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rwa [movingDomain_congr_of_eq (h _ ⟨h1, h2⟩)] at h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rwa [movingDomain_congr_of_eq (h _ ⟨h1, h2⟩)]



/-- Curves agreeing on `[a, b]` have the same closed collar region. -/
theorem collarClosed_congr {n : ℕ} {c : PDE.Vec n} {r₀ dstar : ℝ} {γ γ' : ℝ → PDE.Vec n}
    {a b : ℝ} (h : ∀ σ ∈ Icc a b, γ' σ = γ σ) :
    collarClosed c r₀ dstar γ' a b = collarClosed c r₀ dstar γ a b  := by
  have centreSq_congr_of_eq {γ γ' : ℝ → PDE.Vec n} {p : KineticPoint n} (h : γ' p.time = γ p.time) :
      centreSq c γ' p = centreSq c γ p := by
    unfold centreSq
    rw [h]
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


/-- Collar comparison on one smooth piece `[t₁, t₂]`, with the Lipschitz bound of the curve only
on `[t₁, t₂]`. -/
theorem collar_piece_of_lipschitzOn {n : ℕ} {c : PDE.Vec n} {r₀ dstar : ℝ} (hd : 0 < dstar)
    (hdr : dstar < r₀) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {Lγ : ℝ} (hLγ : 0 ≤ Lγ)
    {t₁ t₂ : ℝ} (hγL : CurveLipschitzOn γ Lγ (Icc t₁ t₂)) (ht : t₁ < t₂)
    (hdiff : ∀ σ ∈ Ioo t₁ t₂, DifferentiableAt ℝ γ σ)
    {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n}
    (hb : HasEuclideanLipschitzDrift Lb b) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {FB : ℝ} (hFB : 0 ≤ FB) {v : KineticPoint n → ℝ}
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
    ∀ p ∈ collarClosed c r₀ dstar γ t₁ t₂, v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p   := by
  have collarSupersolution_congr_of_eq {r₀ dstar Lγ lam FB : ℝ} {γ γ' : ℝ → PDE.Vec n} {p : KineticPoint n} (h : γ' p.time = γ p.time) :
      collarSupersolution c r₀ dstar Lγ lam FB γ' p =
      collarSupersolution c r₀ dstar Lγ lam FB γ p := by
    unfold collarSupersolution collarBarrier
    simp only [h]
  have movingActiveSlab_congr {Ω : Set (PDE.Vec n)} {γ γ' : ℝ → PDE.Vec n} {a : ℝ} {b : ℝ} (h : ∀ σ ∈ Icc a b, γ' σ = γ σ) :
      movingActiveSlab Ω γ' a b = movingActiveSlab Ω γ a b := by
    ext p
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rwa [movingDomain_congr_of_eq (h _ ⟨h1, h2.le⟩)] at h3
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rwa [movingDomain_congr_of_eq (h _ ⟨h1, h2.le⟩)]
  have hext : ∀ σ ∈ Icc t₁ t₂, slabExtension γ t₁ t₂ σ = γ σ := fun σ hσ =>
    slabExtension_eq γ hσ
  have hS := movingClosedSlab_congr (Ω := PDE.euclideanBall c r₀) hext
  have hA := movingActiveSlab_congr (Ω := PDE.euclideanBall c r₀) hext
  have hK := collarClosed_congr (c := c) (r₀ := r₀) (dstar := dstar) hext
  have hdiff' : ∀ σ ∈ Ioo t₁ t₂, DifferentiableAt ℝ (slabExtension γ t₁ t₂) σ := fun σ hσ =>
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
  have hp' : p ∈ collarClosed c r₀ dstar (slabExtension γ t₁ t₂) t₁ t₂ := by rw [hK]; exact hp
  have := key p hp'
  rwa [collarSupersolution_congr_of_eq (hext _ ⟨hp.1.1, hp.1.2.1⟩)] at this





/-- (companion paper, A.1)., finite-slab form.  The two barriers for a viscous classical
terminal solution on the moving ball, with the Lipschitz bound of `γ` and the operator bound `M`
required only on the finite slab `[a, τ]`. -/
theorem two_barriers_on_finite_slab
    {n : ℕ} {c : PDE.Vec n} {r : ℝ} (hr : 0 < r)
    {γ : ℝ → PDE.Vec n} (hγ : IsContinuousPiecewiseC1 γ)
    (a τ : ℝ) (haτ : a < τ) (L : ℝ) (hL : 0 ≤ L)
    (hγL : ∀ s ∈ Icc a τ, ∀ t ∈ Icc a τ,
      PDE.vecEuclideanNorm (γ s - γ t) ≤ L * |s - t|)
    {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B)
    {L_b : ℝ} {b : PDE.Vec n → PDE.Vec n}
    (hb : HasEuclideanLipschitzDrift L_b b)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall c r) γ τ F)
    (d : ℝ) (hd : 0 < d) (hdr : d < r / 4)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * d ≤ r - PDE.vecEuclideanNorm (q.1 - (γ τ + c)))
    (C M : ℝ) (hC : ∀ q, |F q| ≤ C)
    (hM : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r) γ a τ,
      |viscousTransportedOperator B b ε
        (fun q => F (q.position, q.velocity)) p| ≤ M)
    {u : KineticPoint n → ℝ}
    (hu : IsClassicalViscousTerminalSolution (PDE.euclideanBall c r) γ B b ε τ F u) :
    (∀ p ∈ movingClosedSlab (PDE.euclideanBall c r) γ a τ,
      |u p| ≤ C * min 1
        (barrierW (collarKappa L lam)
          (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
          barrierW (collarKappa L lam) d)) ∧
    (∀ p ∈ movingClosedSlab (PDE.euclideanBall c r) γ a τ,
      τ - d / (1 + L) ≤ p.time →
        |u p - F (p.position, p.velocity)| ≤ (τ - p.time) * M)  := by
  have classical_le_collarSupersolution_of_lipschitzOn {c : PDE.Vec n} {r₀ dstar : ℝ} (hd : 0 < dstar) (hdr : dstar < r₀) {γ : ℝ → PDE.Vec n} (hγpw : IsContinuousPiecewiseC1 γ) {Lγ : ℝ} (hLγ : 0 ≤ Lγ) {a τ : ℝ} (haτ : a < τ) (hγL : CurveLipschitzOn γ Lγ (Icc a τ)) {lam : ℝ} {Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ} (hu : IsClassicalViscousTerminalSolution (PDE.euclideanBall c r₀) γ B b ε τ F u) {FB : ℝ} (hFB : 0 ≤ FB) (hle : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ a τ, u p ≤ FB) (hterm0 : ∀ p ∈ evolutionTerminalClosure (PDE.euclideanBall c r₀) γ τ,
      (r₀ - dstar) ^ 2 ≤ centreSq c γ p → u p ≤ 0) :
      ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ a τ,
      (r₀ - dstar) ^ 2 ≤ centreSq c γ p → u p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := by
    have collar_chain_of_lipschitzOn {c : PDE.Vec n} {r₀ dstar : ℝ} (hd : 0 < dstar) (hdr : dstar < r₀) {γ : ℝ → PDE.Vec n} (hγpw : IsContinuousPiecewiseC1 γ) {Lγ : ℝ} (hLγ : 0 ≤ Lγ) {a τ : ℝ} (hγL : CurveLipschitzOn γ Lγ (Icc a τ)) (haτ : a < τ) {lam : ℝ} {Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {FB : ℝ} (hFB : 0 ≤ FB) {v : KineticPoint n → ℝ} (hbdd : ∃ M, ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ a τ, v p ≤ M) (hcont : ContinuousOn v (movingClosedSlab (PDE.euclideanBall c r₀) γ a τ)) (hreg : ∀ p ∈ movingActiveSlab (PDE.euclideanBall c r₀) γ a τ, IsSliceRegularAt v p) (hop : ∀ p ∈ movingActiveSlab (PDE.euclideanBall c r₀) γ a τ,
        0 ≤ viscousTransportedOperator B b ε v p) (hlat : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ a τ,
        p.position ∈ frontier (movingDomain (PDE.euclideanBall c r₀) γ p.time) → v p ≤ 0) (hFBle : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ a τ, v p ≤ FB) (htop : ∀ p ∈ collarClosed c r₀ dstar γ a τ, p.time = τ →
        v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p) :
        ∀ p ∈ collarClosed c r₀ dstar γ a τ, v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := by
      obtain ⟨N, t, ht, h0, hl, hdiff⟩ := exists_partition_differentiableAt hγpw haτ
      let motive : Fin (N + 2) → Prop := fun i =>
        ∀ p ∈ collarClosed c r₀ dstar γ (t i) τ, v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p
      have hmain : ∀ i, motive i := by
        intro i
        refine Fin.reverseInduction ?_ ?_ i
        · intro p hp
          have hpτ : p.time = τ := by
            have h1 := hp.1.1
            have h2 := hp.1.2.1
            rw [hl] at h1
            exact le_antisymm h2 h1
          exact htop p ⟨⟨by rw [hpτ]; exact haτ.le, hp.1.2.1, hp.1.2.2⟩, hp.2⟩ hpτ
        · intro i hprev p hp
          have hlt : t i.castSucc < t i.succ := ht Fin.castSucc_lt_succ
          have ha : a ≤ t i.castSucc := by
            rw [← h0]
            exact ht.monotone (Fin.zero_le _)
          have hτ : t i.succ ≤ τ := by
            rw [← hl]
            exact ht.monotone (Fin.le_last _)
          by_cases hge : t i.succ ≤ p.time
          · exact hprev p ⟨⟨hge, hp.1.2.1, hp.1.2.2⟩, hp.2⟩
          · have hlt' : p.time < t i.succ := not_le.mp hge
            have hres := collar_piece_of_lipschitzOn hd hdr hγpw.1 hLγ
              (fun s hs s' hs' => hγL s ⟨ha.trans hs.1, hs.2.trans hτ⟩ s'
                ⟨ha.trans hs'.1, hs'.2.trans hτ⟩) hlt (hdiff i) hlam hB hb hε0 hε1 hFB

              (by
                obtain ⟨M, hM⟩ := hbdd
                exact ⟨M, fun q hq => hM q (movingClosedSlab_mono ha hτ hq)⟩)
              (hcont.mono (movingClosedSlab_mono ha hτ))
              (fun q hq => hreg q (movingActiveSlab_mono ha hτ hq))
              (fun q hq => hop q (movingActiveSlab_mono ha hτ hq))
              (fun q hq => hlat q (movingClosedSlab_mono ha hτ hq))
              (fun q hq => hFBle q (movingClosedSlab_mono ha hτ hq))
              (fun q hq hqt => hprev q ⟨⟨hqt.ge, by rw [hqt]; exact hτ, hq.1.2.2⟩, hq.2⟩)
            exact hres p ⟨⟨hp.1.1, hlt'.le, hp.1.2.2⟩, hp.2⟩
      have h := hmain 0
      have h' : ∀ p ∈ collarClosed c r₀ dstar γ (t 0) τ,
          v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := h
      rw [h0] at h'
      exact h'
    have hΩo : IsOpen (PDE.euclideanBall c r₀) := PDE.isOpen_euclideanBall c r₀
    have hγ : Continuous γ := hγpw.1
    have hκ : 0 < collarKappa Lγ lam := div_pos (by linarith) hlam
    have hr₀ : 0 ≤ r₀ := by linarith
    have hGnn : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ a τ,
        0 ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := by
      intro p hp
      exact mul_nonneg (div_nonneg hFB (barrierW_pos hκ hd).le) (collarBarrier_nonneg hκ hr₀
        (vecNormSq_le_of_mem_closure_movingDomain hp.2.2))
    have hslab : movingClosedSlab (PDE.euclideanBall c r₀) γ a τ ⊆
        evolutionPastClosedCylinder (PDE.euclideanBall c r₀) γ τ :=
      fun p hp => ⟨hp.2.1, hp.2.2⟩
    have hact : movingActiveSlab (PDE.euclideanBall c r₀) γ a τ ⊆
        evolutionPastOpenCylinder (PDE.euclideanBall c r₀) γ τ :=
      fun p hp => ⟨hp.2.1, hp.2.2⟩
    obtain ⟨C₁, -, hC₁⟩ := hu.1
    have hchain := collar_chain_of_lipschitzOn hd hdr hγpw hLγ hγL haτ hlam hB hb hε0
      hε1 hFB
      ⟨C₁, fun p hp => (le_abs_self _).trans (hC₁ p (hslab hp))⟩
      (hu.2.1.mono hslab)
      (fun p hp => hu.isSliceRegularAt hΩo hγ (hact hp))
      (fun p hp => by rw [hu.2.2.2.1 p (hact hp)])
      (fun p hp hfr => by
        rw [hu.2.2.2.2.2 p ⟨hp.2.1, hfr⟩])
      hle
      (fun p hp hpt => by
        have h1 := hterm0 p ⟨hpt, hpt ▸ hp.1.2.2⟩ hp.2
        have h2 := hGnn p hp.1
        linarith)
    exact fun p hp hS => hchain p ⟨hp, hS⟩
  have hΩo : IsOpen (PDE.euclideanBall c r) := PDE.isOpen_euclideanBall c r
  have hdr' : d < r := by linarith
  have hκ : 0 < collarKappa L lam := div_pos (by linarith) hlam
  have hC0 := le_trans (abs_nonneg _) (hC 0)
  have hγL' : CurveLipschitzOn γ L (Icc a τ) := hγL
  have hslab : movingClosedSlab (PDE.euclideanBall c r) γ a τ ⊆
      evolutionPastClosedCylinder (PDE.euclideanBall c r) γ τ :=
    fun p hp => ⟨hp.2.1, hp.2.2⟩
  refine ⟨?_, ?_⟩
  · intro p hp
    have hAbs := classical_abs_le_const hΩo hγ.1 hlam hB hb hε hε1 hu hC
    have hnu := hu.neg hΩo hγ.1
    rcases le_total 1 (barrierW (collarKappa L lam)
        (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
          barrierW (collarKappa L lam) d) with h1 | h1
    · rw [min_eq_left h1]
      have := hAbs p (hslab hp)
      linarith
    · rw [min_eq_right h1]
      have hle : barrierW (collarKappa L lam)
          (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) ≤
            barrierW (collarKappa L lam) d := by
        rwa [div_le_one (barrierW_pos hκ hd)] at h1
      have hd' := le_of_barrierW_le hκ hle
      have hnorm : r - d ≤ PDE.vecEuclideanNorm (p.position - (γ p.time + c)) := by
        linarith
      have hS : (r - d) ^ 2 ≤ centreSq c γ p := by
        have h2 :=
          pow_le_pow_left₀ (by linarith) hnorm 2
        rw [PDE.vecEuclideanNorm_sq] at h2
        exact h2
      have hup := classical_le_collarSupersolution_of_lipschitzOn hd hdr' hγ hL haτ
        hγL' hlam hB hb hε hε1 hu hC0 (fun q hq => (le_abs_self _).trans (hAbs q (hslab hq)))
        (fun q hq hqS => by
          rw [hu.2.2.2.2.1 q hq, terminalDatum_eq_zero_of_collar hd hdr' hsupp hq.1 hqS])
        p hp hS
      have hdown := classical_le_collarSupersolution_of_lipschitzOn hd hdr' hγ hL haτ
        hγL' hlam hB hb hε hε1 hnu hC0
        (fun q hq => (neg_le_abs _).trans (hAbs q (hslab hq)))
        (fun q hq hqS => by
          have h := hnu.2.2.2.2.1 q hq
          simp only [BoundedBorel.neg_apply] at h
          show -u q ≤ 0
          rw [h, terminalDatum_eq_zero_of_collar hd hdr' hsupp hq.1 hqS]
          simp)
        p hp hS
      have hG : collarSupersolution c r d L lam C γ p =
          C * (barrierW (collarKappa L lam)
              (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
            barrierW (collarKappa L lam) d) := by
        have : collarBarrier (collarKappa L lam) r (fun t => γ t + c) p =
            barrierW (collarKappa L lam)
              (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) := rfl
        unfold collarSupersolution
        rw [this]
        ring
      rw [← hG]
      have hdown' := hdown
      exact abs_le.mpr ⟨by linarith, hup⟩
  · intro p₀ hp₀ hδ
    have hL1 : 0 < 1 + L := by linarith
    have hFzero : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r) γ (max a (τ - d / (1 + L))) τ,
        p.position ∈ frontier (movingDomain (PDE.euclideanBall c r) γ p.time) →
          F (p.position, p.velocity) = 0 := by
      intro p hp hfr
      have hp1 := (le_max_right _ _).trans hp.1
      have hp0 := (le_max_left _ _).trans hp.1
      by_contra hne
      have hmem :=
        subset_tsupport _ (Function.mem_support.mpr hne)
      have h3 := hsupp _ hmem
      simp only at h3
      have hS := vecNormSq_eq_of_mem_frontier_movingDomain hfr
      have hnorm : PDE.vecEuclideanNorm (p.position - (γ p.time + c)) = r := by
        unfold PDE.vecEuclideanNorm
        rw [hS, Real.sqrt_sq hr.le]
      have htri : p.position - (γ p.time + c) =
          (p.position - (γ τ + c)) + (γ τ - γ p.time) := by abel
      have h4 := PDE.vecEuclideanNorm_add_le (p.position - (γ τ + c)) (γ τ - γ p.time)
      rw [← htri, hnorm] at h4
      have h5 := hγL τ ⟨haτ.le, le_rfl⟩ p.time ⟨hp0, hp.2.1⟩
      have h6 : |τ - p.time| = τ - p.time := abs_of_nonneg (by linarith [hp.2.1])
      rw [h6] at h5
      have h7 : L * (τ - p.time) ≤ L * (d / (1 + L)) :=
        mul_le_mul_of_nonneg_left (by linarith) hL
      have h8 : L * (d / (1 + L)) < d := by
        rw [← mul_div_assoc, div_lt_iff₀ hL1]
        nlinarith
      linarith
    exact classical_sub_terminalDatum_le_core_of_slab hΩo hγ.1 hlam hB hb hε hε1 hF.1 hC

      (fun p hp => hM p ⟨(le_max_left _ _).trans hp.1, hp.2.1, hp.2.2⟩) hu hFzero p₀
      ⟨max_le hp₀.1 hδ, hp₀.2.1, hp₀.2.2⟩

end HypoellipticAleksandrov.KineticAleksandrov

