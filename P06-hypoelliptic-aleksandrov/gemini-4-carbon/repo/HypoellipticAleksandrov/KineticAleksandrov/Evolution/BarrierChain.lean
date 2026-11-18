module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierCollar
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonNodes

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov Filter Set HypoellipticAleksandrov.Parabolic
open scoped Topology MatrixOrder


/-- The profile `w(t) = (1 - exp (-κ t))/κ`. -/
def barrierW (κ t : ℝ) : ℝ := (1 - Real.exp (-κ * t)) / κ

/-- The constant `κ = (1 + L_γ)/λ`. -/
def collarKappa (Lγ lam : ℝ) : ℝ := (1 + Lγ) / lam

/-- The squared distance of the position from the moving centre `γ(σ) + c`. -/
def centreSq {n : ℕ} (c : PDE.Vec n) (γ : ℝ → PDE.Vec n) (p : KineticPoint n) : ℝ :=
  PDE.vecNormSq (p.position - (γ p.time + c))

/-- The closed collar region of the moving ball on the time slab `[a, b]`. -/
def collarClosed {n : ℕ} (c : PDE.Vec n) (r₀ dstar : ℝ) (γ : ℝ → PDE.Vec n) (a b : ℝ) :
    Set (KineticPoint n) :=
  movingClosedSlab (PDE.euclideanBall c r₀) γ a b ∩ {p | (r₀ - dstar) ^ 2 ≤ centreSq c γ p}


/-- The scaled supersolution `FB * w(d)/w(d_*)`, with `d = r₀ - |y - γ(σ) - c|`. -/
def collarSupersolution {n : ℕ} (c : PDE.Vec n) (r₀ dstar Lγ lam FB : ℝ)
    (γ : ℝ → PDE.Vec n) (p : KineticPoint n) : ℝ :=
  FB / barrierW (collarKappa Lγ lam) dstar *
    collarBarrier (collarKappa Lγ lam) r₀ (fun t => γ t + c) p

/-- The profile `w` is positive on positive arguments. -/
theorem barrierW_pos {κ t : ℝ} (hκ : 0 < κ) (ht : 0 < t) : 0 < barrierW κ t := by
  unfold barrierW
  have : Real.exp (-κ * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  exact div_pos (by linarith) hκ

/-- Continuity of the squared distance to the moving centre. -/
theorem continuous_centreSq {n : ℕ} (c : PDE.Vec n) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) :
    Continuous (centreSq c γ) := by
  have h1 : Continuous (fun p : KineticPoint n => p.position - (γ p.time + c)) :=
    continuous_position.sub ((hγ.comp continuous_time).add continuous_const)
  have : centreSq c γ = fun p => ∑ i, (p.position i - (γ p.time + c) i) ^ 2 := by
    funext p
    unfold centreSq
    rw [PDE.vecNormSq_eq_sum_sq]
    rfl
  rw [this]
  refine continuous_finsetSum _ (fun i _ => ?_)
  exact ((continuous_apply i).comp h1).pow 2


/-- Continuity of the scaled collar supersolution. -/
theorem continuous_collarSupersolution {n : ℕ} (c : PDE.Vec n) (r₀ dstar Lγ lam FB : ℝ)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) :
    Continuous (collarSupersolution c r₀ dstar Lγ lam FB γ)  := by
  have continuous_collarBarrier (κ r₀ : ℝ) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) :
      Continuous (collarBarrier κ r₀ (fun t => γ t + c)) := by
    unfold collarBarrier collarProfile
    have h' : Continuous (fun p : KineticPoint n => PDE.vecNormSq (p.position - (γ p.time + c))) := (continuous_centreSq c hγ)
    fun_prop
  exact continuous_const.mul (continuous_collarBarrier _ r₀ hγ)

/-- The collar barrier is nonnegative inside the closed ball. -/
theorem collarBarrier_nonneg {n : ℕ} {c : PDE.Vec n} {κ r₀ : ℝ} (hκ : 0 < κ) (hr₀ : 0 ≤ r₀)
    {γ : ℝ → PDE.Vec n} {p : KineticPoint n} (hS : centreSq c γ p ≤ r₀ ^ 2) :
    0 ≤ collarBarrier κ r₀ (fun t => γ t + c) p := by
  unfold collarBarrier collarProfile
  have h1 : Real.sqrt (PDE.vecNormSq (p.position - (γ p.time + c))) ≤ r₀ :=
    Real.sqrt_le_iff.mpr ⟨hr₀, hS⟩
  have h2 : Real.exp (-κ * (r₀ - Real.sqrt (PDE.vecNormSq (p.position - (γ p.time + c))))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  exact div_nonneg (by linarith) hκ.le

/-- On the inner edge of the collar the barrier equals `w(d_*)`. -/
theorem collarBarrier_inner {n : ℕ} {c : PDE.Vec n} {κ r₀ dstar : ℝ} (hd : dstar < r₀)
    {γ : ℝ → PDE.Vec n} {p : KineticPoint n} (hS : centreSq c γ p = (r₀ - dstar) ^ 2) :
    collarBarrier κ r₀ (fun t => γ t + c) p = barrierW κ dstar := by
  unfold collarBarrier collarProfile barrierW
  have h : PDE.vecNormSq (p.position - (γ p.time + c)) = (r₀ - dstar) ^ 2 := hS
  rw [h, Real.sqrt_sq (by linarith)]
  congr 3
  ring

/-- On the inner edge of the collar the supersolution equals `‖F‖`. -/
theorem collarSupersolution_inner {n : ℕ} {c : PDE.Vec n} {r₀ dstar Lγ lam FB : ℝ}
    (hd : dstar < r₀) (hκ : 0 < collarKappa Lγ lam) (hdpos : 0 < dstar)
    {γ : ℝ → PDE.Vec n} {p : KineticPoint n} (hS : centreSq c γ p = (r₀ - dstar) ^ 2) :
    collarSupersolution c r₀ dstar Lγ lam FB γ p = FB := by
  unfold collarSupersolution
  rw [collarBarrier_inner hd hS]
  have := (barrierW_pos hκ hdpos).ne'
  field_simp



/-- Inset comparison on the collar region of `[α, t₂]`, `t₁ < α < t₂`. -/
theorem collar_piece_inset {n : ℕ} {c : PDE.Vec n} {r₀ dstar : ℝ} (hd : 0 < dstar)
    (hdr : dstar < r₀) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {Lγ : ℝ} (hLγ : 0 ≤ Lγ)
    (hγL : ∀ s t, PDE.vecEuclideanNorm (γ s - γ t) ≤ Lγ * |s - t|)
    {t₁ t₂ α : ℝ} (hα : t₁ < α)
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
    ∀ p ∈ collarClosed c r₀ dstar γ α t₂, v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p  := by
  let collarActive (r₀ dstar : ℝ) (γ : ℝ → PDE.Vec n) (a : ℝ) (b : ℝ) :=
    movingActiveSlab (PDE.euclideanBall c r₀) γ a b ∩ {p | (r₀ - dstar) ^ 2 < centreSq c γ p}
  have hΩo : IsOpen (PDE.euclideanBall c r₀) := PDE.isOpen_euclideanBall c r₀
  have hκ : 0 < collarKappa Lγ lam := div_pos (by linarith) hlam
  have hc0 :=
    div_nonneg hFB (barrierW_pos hκ hd).le
  have hr₀ : 0 ≤ r₀ := by linarith
  have hKsub : collarClosed c r₀ dstar γ α t₂ ⊆ movingClosedSlab (PDE.euclideanBall c r₀) γ t₁ t₂ :=
    fun p hp => ⟨hα.le.trans hp.1.1, hp.1.2.1, hp.1.2.2⟩
  have hDsub : collarActive r₀ dstar γ α t₂ ⊆ movingActiveSlab (PDE.euclideanBall c r₀) γ t₁ t₂ :=
    fun p hp => ⟨hα.le.trans hp.1.1, hp.1.2.1, hp.1.2.2⟩
  have hGnn : ∀ p ∈ collarClosed c r₀ dstar γ α t₂,
      0 ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := by
    intro p hp
    exact mul_nonneg hc0 (collarBarrier_nonneg hκ hr₀
      (vecNormSq_le_of_mem_closure_movingDomain hp.1.2.2))
  have hmdiff : ∀ p ∈ collarActive r₀ dstar γ α t₂,
      DifferentiableAt ℝ (fun t => γ t + c) p.time := fun p hp =>
    (hdiff _ ⟨hα.trans_le hp.1.1, hp.1.2.1⟩).add_const c
  have hSpos : ∀ p ∈ collarActive r₀ dstar γ α t₂,
      0 < PDE.vecNormSq (p.position - ((fun t => γ t + c) p.time)) := fun p hp =>
    lt_of_le_of_lt (sq_nonneg _) hp.2
  have hGreg : ∀ p ∈ collarActive r₀ dstar γ α t₂,
      IsSliceRegularAt (collarSupersolution c r₀ dstar Lγ lam FB γ) p := fun p hp =>
    (isSliceRegularAt_collarBarrier (collarKappa Lγ lam) r₀ (hmdiff p hp) (hSpos p hp)).const_mul _
  have key := le_zero_of_viscous_nonneg_growth (ε := ε)
    (K := collarClosed c r₀ dstar γ α t₂) (D := collarActive r₀ dstar γ α t₂)
    (u := fun q => v q - collarSupersolution c r₀ dstar Lγ lam FB γ q)
    hε0 hε1 (fun σ y z => (hB σ y z).2) hb
    ((isClosed_movingClosedSlab hγ α t₂).inter
      (isClosed_le continuous_const (continuous_centreSq c hγ)))
    (fun p hp => ⟨hp.1.1, hp.1.2.1⟩)
    ?hfut ?hcont ?hbdd ?hreg ?hpsd ?hsub ?hbdry
  · intro p hp
    have : v p - collarSupersolution c r₀ dstar Lγ lam FB γ p ≤ 0 := key p hp
    linarith
  case hfut =>
    intro p hp
    obtain ⟨⟨hat, htb, hpm⟩, hpS⟩ := hp
    have h1 := eventually_future_mem_movingClosedSlab hΩo hγ
      (p := p) ⟨hat, htb, hpm⟩
    have h2 :=
      (isOpen_lt continuous_const (continuous_centreSq c hγ)).mem_nhds hpS
    filter_upwards [h1, h2] with q hq1 hq2 hqt
    exact ⟨hq1 hqt, hq2.le⟩
  case hcont =>
    exact (hcont.mono hKsub).sub
      (continuous_collarSupersolution c r₀ dstar Lγ lam FB hγ).continuousOn
  case hbdd =>
    obtain ⟨M, hM⟩ := hbdd
    refine ⟨M, fun p hp => ?_⟩
    have h1 := hM p (hKsub hp)
    have h2 := hGnn p hp
    show v p - collarSupersolution c r₀ dstar Lγ lam FB γ p ≤ M
    linarith
  case hreg =>
    intro p hp
    exact (hreg p (hDsub hp)).sub (hGreg p hp)
  case hpsd =>
    intro p _
    exact posSemidef_of_hasEverywhereLoewnerBounds hlam.le hB _ _ _
  case hsub =>
    intro p hp
    rw [viscousTransportedOperator_sub (hreg p (hDsub hp)) (hGreg p hp)]
    have hpt : p.time ∈ Ioo t₁ t₂ := ⟨hα.trans_le hp.1.1, hp.1.2.1⟩
    have hm' :=
      (hdiff _ hpt).hasDerivAt.add_const c
    have hκlam : collarKappa Lγ lam * lam = 1 + Lγ := div_mul_cancel₀ _ hlam.ne'
    have hBlam : lam • 1 ≤ B p.time p.position p.velocity := (hB _ _ _).1
    have hLcb := viscousTransportedOperator_collarBarrier_nonpos (b := b) ε hκ hlam.le hκlam r₀
      hm' (vecEuclideanNorm_le_of_hasDerivAt_lipschitz hLγ (hdiff _ hpt).hasDerivAt hγL) (hSpos p hp) hBlam
    have e : viscousTransportedOperator B b ε (collarSupersolution c r₀ dstar Lγ lam FB γ) p =
        FB / barrierW (collarKappa Lγ lam) dstar *
          viscousTransportedOperator B b ε
            (collarBarrier (collarKappa Lγ lam) r₀ (fun t => γ t + c)) p :=
      viscousTransportedOperator_const_mul _
        (isSliceRegularAt_collarBarrier (collarKappa Lγ lam) r₀ (hmdiff p hp) (hSpos p hp))
    have hLG : viscousTransportedOperator B b ε
        (collarSupersolution c r₀ dstar Lγ lam FB γ) p ≤ 0 := by
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos hc0 hLcb
    have := hop p (hDsub hp)
    linarith
  case hbdry =>
    intro p hpK hpD
    by_cases hact : p ∈ movingActiveSlab (PDE.euclideanBall c r₀) γ α t₂
    · have hS : centreSq c γ p = (r₀ - dstar) ^ 2 :=
        le_antisymm (not_lt.mp (fun h => hpD ⟨hact, h⟩)) hpK.2
      have h1 := collarSupersolution_inner (Lγ := Lγ) (FB := FB) hdr hκ hd hS
      have h2 := hFBle p (hKsub hpK)
      show v p - collarSupersolution c r₀ dstar Lγ lam FB γ p ≤ 0
      linarith
    · rcases mem_boundary_of_movingClosedSlab hΩo hpK.1 hact with h | h
      · have h1 := htop p ⟨⟨hα.le.trans hpK.1.1, hpK.1.2.1, hpK.1.2.2⟩, hpK.2⟩ h
        show v p - collarSupersolution c r₀ dstar Lγ lam FB γ p ≤ 0
        linarith
      · have h1 := hlat p (hKsub hpK) h
        have h2 := hGnn p hpK
        show v p - collarSupersolution c r₀ dstar Lγ lam FB γ p ≤ 0
        linarith

/-- Collar comparison on the whole closed piece `[t₁, t₂]`. -/
theorem collar_piece {n : ℕ} {c : PDE.Vec n} {r₀ dstar : ℝ} (hd : 0 < dstar)
    (hdr : dstar < r₀) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {Lγ : ℝ} (hLγ : 0 ≤ Lγ)
    (hγL : ∀ s t, PDE.vecEuclideanNorm (γ s - γ t) ≤ Lγ * |s - t|)
    {t₁ t₂ : ℝ} (ht : t₁ < t₂)
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
    ∀ p ∈ collarClosed c r₀ dstar γ t₁ t₂, v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := by
  intro p hp
  have inset := fun α (hα : t₁ < α) => collar_piece_inset hd hdr hγ hLγ hγL hα hdiff hlam hB hb
    hε0 hε1 hFB hbdd hcont hreg hop hlat hFBle htop
  by_cases h2 : p.time = t₂
  · exact htop p hp h2
  by_cases h1 : t₁ < p.time
  · exact inset p.time h1 p ⟨⟨le_rfl, hp.1.2.1, hp.1.2.2⟩, hp.2⟩
  have hpt := le_antisymm (not_lt.mp h1) hp.1.1
  -- limit from later times along the translated curve
  let q : ℝ → KineticPoint n := fun α => ⟨α, p.position + γ α - γ t₁, p.velocity⟩
  have hqc : Continuous q :=
    KineticPoint.continuous_mk continuous_id ((continuous_const.add hγ).sub continuous_const)
      continuous_const
  have hq1 : q t₁ = p := by
    ext
    · exact hpt.symm
    · simp [q]
    · rfl
  have hqslab : ∀ᶠ α in 𝓝[>] t₁, q α ∈ collarClosed c r₀ dstar γ α t₂ := by
    filter_upwards [Ioo_mem_nhdsGT ht] with α hα
    refine ⟨⟨le_rfl, hα.2.le, ?_⟩, ?_⟩
    · rw [mem_closure_movingDomain_iff]
      have := mem_closure_movingDomain_iff.mp hp.1.2.2
      rw [hpt] at this
      have e : (p.position + γ α - γ t₁) - γ α = p.position - γ t₁ := by abel
      show (p.position + γ α - γ t₁) - γ α ∈ closure (PDE.euclideanBall c r₀)
      rw [e]
      exact this
    · have e : (q α).position - (γ (q α).time + c) = p.position - (γ p.time + c) := by
        show p.position + γ α - γ t₁ - (γ α + c) = _
        rw [hpt]
        abel
      have := hp.2
      show (r₀ - dstar) ^ 2 ≤ PDE.vecNormSq ((q α).position - (γ (q α).time + c))
      rw [e]
      exact this
  have hle : ∀ᶠ α in 𝓝[>] t₁, v (q α) ≤ collarSupersolution c r₀ dstar Lγ lam FB γ (q α) := by
    filter_upwards [Ioo_mem_nhdsGT ht, hqslab] with α hα hα'
    exact inset α hα.1 _ hα'
  have htend : Tendsto q (𝓝[>] t₁)
      (𝓝[movingClosedSlab (PDE.euclideanBall c r₀) γ t₁ t₂] p) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := (hqc.tendsto t₁).mono_left (nhdsWithin_le_nhds (s := Ioi t₁))
      rwa [hq1] at this
    · filter_upwards [Ioo_mem_nhdsGT ht, hqslab] with α hα hα'
      exact ⟨hα.1.le, hα.2.le, hα'.1.2.2⟩
  have hv := (hcont p hp.1).tendsto.comp htend
  have hG : Tendsto (fun α => collarSupersolution c r₀ dstar Lγ lam FB γ (q α)) (𝓝[>] t₁)
      (𝓝 (collarSupersolution c r₀ dstar Lγ lam FB γ p)) := by
    have := (((continuous_collarSupersolution c r₀ dstar Lγ lam FB hγ).comp hqc).tendsto t₁).mono_left (nhdsWithin_le_nhds (s := Ioi t₁))
    simp [hq1] at this
    exact this
  exact le_of_tendsto_of_tendsto hv hG hle



/-- Monotonicity of the closed moving slab in its time interval. -/
theorem movingClosedSlab_mono {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {a a' b b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    movingClosedSlab Ω γ a' b' ⊆ movingClosedSlab Ω γ a b :=
  fun _ hp => ⟨ha.trans hp.1, hp.2.1.trans hb, hp.2.2⟩

/-- Monotonicity of the active moving slab in its time interval. -/
theorem movingActiveSlab_mono {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {a a' b b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    movingActiveSlab Ω γ a' b' ⊆ movingActiveSlab Ω γ a b :=
  fun _ hp => ⟨ha.trans hp.1, hp.2.1.trans_le hb, hp.2.2⟩

end HypoellipticAleksandrov.KineticAleksandrov

