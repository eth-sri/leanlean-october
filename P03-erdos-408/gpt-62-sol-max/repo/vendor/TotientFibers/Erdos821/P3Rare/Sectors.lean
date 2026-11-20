module

public import Erdos821.P3Rare.Base
public import Erdos821.P3Edge.LargeX
public import Erdos821.P3Edge.Polylog
public import Erdos821.P3Edge.PromoBound
public import Erdos821.P3Edge.SmallFresh

@[expose] public section

set_option autoImplicit false

/-! Final assembly of the rare-transfer estimate `MemoryRareTask`
(source §2, `lem:memory-rare`): the promotion sector is sparse in source
omissions and the store-only sector is sparse in target omissions; each is
bounded by contextwise weighted Schur, and the context constants sum to the
pattern mass times a `J`-independent power of `L(x)`. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Rare

open Erdos821.Blueprint.Graph Erdos821.S2Core


section

variable {α Ω κ : Type*} [Fintype Ω] [Fintype κ]
  (mass w : α → ℝ) (keep : α → Prop)
  (K : κ → Ω → α → α → ℝ)

/-- For an average of projected kernels, each context gains from sparse row
and column supports before their bounds are added. Only retained entries need
obey the support restrictions. -/
theorem normBound_projected_average_support
    (rows cols : κ → α → Finset Ω) (R C : κ → ℝ) (B₁ B₂ : ℕ)
    (hm : ∀ a, 0 ≤ mass a) (hw : ∀ a, 0 < w a)
    (hK : ∀ j ω a b, 0 ≤ K j ω a b)
    (hR : ∀ j, 0 ≤ R j) (hC : ∀ j, 0 ≤ C j)
    (hD : 0 < (Fintype.card Ω : ℝ))
    (hrow : ∀ j a ω t, ∑ b ∈ t, K j ω a b * w b ≤ R j * w a)
    (hcol : ∀ j b ω s, ∑ a ∈ s, mass a * K j ω a b * w a ≤ C j * mass b * w b)
    (hrows : ∀ j a, (rows j a).card ≤ B₁) (hcols : ∀ j b, (cols j b).card ≤ B₂)
    (hz₁ : ∀ j a ω, keep a → ω ∉ rows j a → ∀ b, K j ω a b = 0)
    (hz₂ : ∀ j b ω, keep b → ω ∉ cols j b → ∀ a, K j ω a b = 0) :
    NormBound mass
      (projectKernel keep (fun a b => ((Fintype.card Ω : ℝ)⁻¹ * ∑ j, ∑ ω, K j ω a b : ℝ)))
      (∑ j, Real.sqrt ((R j * (B₁ / (Fintype.card Ω : ℝ))) * (C j * (B₂ / (Fintype.card Ω : ℝ))))) := by
  classical
  let K' := fun j ω a b => if keep a ∧ keep b then K j ω a b else 0
  have he : projectKernel keep (fun a b => ((Fintype.card Ω : ℝ)⁻¹ * ∑ j, ∑ ω, K j ω a b : ℝ)) =
      fun a b => ∑ j, (((Fintype.card Ω : ℝ)⁻¹ * ∑ ω, K' j ω a b : ℝ) : ℂ) := by
    funext a b
    by_cases h : keep a ∧ keep b <;> simp [projectKernel, K', h, Finset.mul_sum, Complex.ofReal_sum]
  rw [he]
  apply normBound_fintype_sum
  intro j
  refine normBound_average_support mass w (K' j) (rows j) (cols j) (R j) (C j) B₁ B₂
    hm hw (fun ω a b => by dsimp [K']; split_ifs <;> simp [hK]) (hR j) (hC j) hD
    ?_ ?_ (hrows j) (hcols j) ?_ ?_
  · intro a ω t
    by_cases ha : keep a
    · simpa [K', ha, Finset.sum_filter] using hrow j a ω (t.filter keep)
    · simpa [K', ha] using mul_nonneg (hR j) (hw a).le
  · intro b ω s
    by_cases hb : keep b
    · simpa [K', hb, Finset.sum_filter] using hcol j b ω (s.filter keep)
    · simpa [K', hb] using mul_nonneg (mul_nonneg (hC j) (hm b)) (hw b).le
  · intro a ω hω b
    by_cases h : keep a ∧ keep b
    · simp [K', h, hz₁ j a ω h.1 hω b]
    · simp [K', h]
  · intro b ω hω a
    by_cases h : keep a ∧ keep b
    · simp [K', h, hz₂ j b ω h.2 hω a]
    · simp [K', h]

end

section

variable {F : FixedData} {P : PrimeGroups}
  {J m n : ℕ}

theorem promotionContextKernel_nonneg (A : Model F P J m) (r : MemoryParameters F) (theta : ℝ) (i : Fin n)
    (ctx : EdgeTransferContext A) (O : OmissionChoices P (J + F.ell) F.ell)
    (s t : P.MemoryState (J + F.ell)) :
    0 ≤ promotionContextKernel A r theta i ctx O s t := by
  unfold promotionContextKernel
  apply mul_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) (edgeSymmetryFactor_nonneg P _)
  · apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    apply Finset.sum_nonneg
    intro c _
    dsimp only
    split_ifs
    · exact norm_nonneg _
    rfl

theorem storeOnlyContextKernel_nonneg (A : Model F P J m) (r : MemoryParameters F) (theta : ℝ) (i : Fin n)
    (ctx : EdgeTransferContext A) (O : OmissionChoices P (J + F.ell) F.ell)
    (s t : P.MemoryState (J + F.ell)) :
    0 ≤ storeOnlyContextKernel A r theta i ctx O s t := by
  unfold storeOnlyContextKernel
  apply mul_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) (edgeSymmetryFactor_nonneg P _)
  · apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    apply Finset.sum_nonneg
    intro c _
    dsimp only
    split_ifs
    · exact norm_nonneg _
    rfl

theorem promotionOmissionAverage_projectedNormBound'
    (A : Model F P J m) (r : MemoryParameters F) (theta : ℝ) (i : Fin n)
    (keep : P.MemoryState (J + F.ell) → Prop)
    (mass w : P.MemoryState (J + F.ell) → ℝ)
    (R C : EdgeTransferContext A → ℝ) (B : ℕ)
    (hm : ∀ s, 0 ≤ mass s) (hw : ∀ s, 0 < w s)
    (hD : 0 < (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ))
    (hR : ∀ ctx, 0 ≤ R ctx) (hC : ∀ ctx, 0 ≤ C ctx)
    (hrow : ∀ ctx O s T,
      ∑ t ∈ T, promotionContextKernel A r theta i ctx O s t * w t ≤ R ctx * w s)
    (hcol : ∀ ctx O t S,
      ∑ s ∈ S, mass s * promotionContextKernel A r theta i ctx O s t * w s ≤
        C ctx * mass t * w t)
    (hbad : ∀ ctx s,
      (Finset.univ.filter (fun O => keep s ∧ promotionContextBadOmission A i ctx s O)).card ≤ B) :
    NormBound mass
      (projectKernel keep (fun s t =>
        (promotionOmissionAverageKernel A r.rho theta i s t : ℂ)))
      (∑ ctx : EdgeTransferContext A,
        Real.sqrt ((R ctx * ((B : ℝ) /
          (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ))) * C ctx)) := by
  classical
  let Ω := OmissionChoices P (J + F.ell) F.ell
  let bad ctx a (ω : Ω) := keep a ∧ promotionContextBadOmission A i ctx a ω
  have hzero (j a ω) (ha : keep a) (hω : ω ∉ Finset.univ.filter (bad j a)) (b) :=
    promotionContextKernel_zero_of_not_bad A r theta i j ω a b
      (fun hh => hω (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,hh⟩))
  have h := normBound_projected_average_support (Ω := Ω) mass w keep
    (fun j ω a b => promotionContextKernel A r theta i j ω a b)
    (fun j a => Finset.univ.filter (bad j a)) (fun _ _ => Finset.univ) R C B (Fintype.card Ω) hm hw (promotionContextKernel_nonneg A r theta i) hR hC hD
    (fun j a ω t => hrow j ω a t) (fun j b ω s => hcol j ω b s)
    hbad (fun _ _ => Finset.card_univ.le) hzero
    (fun _ _ ω _ hω _ => (hω (Finset.mem_univ ω)).elim)
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := hD.ne'
  simpa only [promotionOmissionAverageKernel_context_sum A r, div_self hΩ, mul_one] using h

theorem storeOnlyOmissionAverage_projectedNormBound'
    (A : Model F P J m) (r : MemoryParameters F) (theta : ℝ) (i : Fin n)
    (keep : P.MemoryState (J + F.ell) → Prop)
    (mass w : P.MemoryState (J + F.ell) → ℝ)
    (R C : EdgeTransferContext A → ℝ) (B : ℕ)
    (hm : ∀ s, 0 ≤ mass s) (hw : ∀ s, 0 < w s)
    (hD : 0 < (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ))
    (hR : ∀ ctx, 0 ≤ R ctx) (hC : ∀ ctx, 0 ≤ C ctx)
    (hrow : ∀ ctx O s T,
      ∑ t ∈ T, storeOnlyContextKernel A r theta i ctx O s t * w t ≤ R ctx * w s)
    (hcol : ∀ ctx O t S,
      ∑ s ∈ S, mass s * storeOnlyContextKernel A r theta i ctx O s t * w s ≤
        C ctx * mass t * w t)
    (hbad : ∀ ctx t,
      (Finset.univ.filter (fun O => keep t ∧ storeOnlyContextBadOmission A i ctx t O)).card ≤ B) :
    NormBound mass
      (projectKernel keep (fun s t =>
        (storeOnlyOmissionAverageKernel A r.rho theta i s t : ℂ)))
      (∑ ctx : EdgeTransferContext A,
        Real.sqrt (R ctx * (C ctx * ((B : ℝ) /
          (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ))))) := by
  classical
  let Ω := OmissionChoices P (J + F.ell) F.ell
  let bad ctx a (ω : Ω) := keep a ∧ storeOnlyContextBadOmission A i ctx a ω
  have hzero (j a ω) (ha : keep a) (hω : ω ∉ Finset.univ.filter (bad j a)) (b) :=
    storeOnlyContextKernel_zero_of_not_bad A r theta i j ω b a
      (fun hh => hω (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,hh⟩))
  have h := normBound_projected_average_support (Ω := Ω) mass w keep
    (fun j ω a b => storeOnlyContextKernel A r theta i j ω a b)
    (fun _ _ => Finset.univ) (fun j b => Finset.univ.filter (bad j b)) R C (Fintype.card Ω) B hm hw (storeOnlyContextKernel_nonneg A r theta i) hR hC hD
    (fun j a ω t => hrow j ω a t) (fun j b ω s => hcol j ω b s)
    (fun _ _ => Finset.card_univ.le) hbad
    (fun _ _ ω _ hω _ => (hω (Finset.mem_univ ω)).elim) hzero
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := hD.ne'
  simpa only [storeOnlyOmissionAverageKernel_context_sum A r, div_self hΩ, mul_one] using h

/-- Projected dirty edge kernel from projected sector bounds. -/
theorem normBound_projected_dirty_of_sectorBounds (A : Model F P J m) (rho theta : ℝ)
    (i : Fin n) (phi : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ)
    (hphi : ∀ s t c, ‖phi s t c‖ ≤ 1)
    (mass : P.MemoryState (J + F.ell) → ℝ) (keep : P.MemoryState (J + F.ell) → Prop)
    (c₁ c₂ : ℝ) (hmass : ∀ s, 0 ≤ mass s)
    (hprom : NormBound mass
      (projectKernel keep (fun s t => (promotionOmissionAverageKernel A rho theta i s t : ℂ))) c₁)
    (hstore : NormBound mass
      (projectKernel keep (fun s t => (storeOnlyOmissionAverageKernel A rho theta i s t : ℂ))) c₂) :
    NormBound mass (projectKernel keep (memoryEdgeKernel A n rho theta i .dirty phi))
      (c₁ + c₂) := by
  classical
  let K₁  := fun s t =>
    if keep s ∧ keep t then promotionOmissionAverageKernel A rho theta i s t else 0
  let K₂  := fun s t =>
    if keep s ∧ keep t then storeOnlyOmissionAverageKernel A rho theta i s t else 0
  have e₁ : (fun s t => ((K₁ s t : ℝ) : ℂ)) =
      projectKernel keep (fun s t => (promotionOmissionAverageKernel A rho theta i s t : ℂ)) := by
    funext s t
    simp only [K₁, projectKernel]
    split_ifs <;> simp
  have e₂ : (fun s t => ((K₂ s t : ℝ) : ℂ)) =
      projectKernel keep (fun s t => (storeOnlyOmissionAverageKernel A rho theta i s t : ℂ)) := by
    funext s t
    simp only [K₂, projectKernel]
    split_ifs <;> simp
  apply normBound_of_two_positive_dominations mass _ K₁ K₂ c₁ c₂ hmass
  · intro s t
    simp only [K₁]
    split_ifs
    · exact promotionOmissionAverageKernel_nonneg A rho theta i s t
    rfl
  · intro s t
    simp only [K₂]
    split_ifs
    · exact storeOnlyOmissionAverageKernel_nonneg A rho theta i s t
    rfl
  · intro s t
    simp only [K₁, K₂, projectKernel]
    split_ifs
    · simpa [promotionOmissionAverageKernel, storeOnlyOmissionAverageKernel] using
        memoryEdgeKernel_dirty_omission_domination A rho theta i phi hphi s t
    · simp
  · rw [e₁]
    exact hprom
  · rw [e₂]
    exact hstore

end

theorem normBound_mono' {α : Type*} {mass : α → ℝ} {K : α → α → ℂ} {c c' : ℝ}
    (h : NormBound mass K c) (hc : c ≤ c') : NormBound mass K c' := by
  intro S T f g
  refine le_trans (h S T f g) ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end Erdos821.P3Rare
