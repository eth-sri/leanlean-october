module

public import PottsDiscontinuity.TorusCrossing.SubGraph
public import PottsDiscontinuity.TorusCrossing.Square

/-!
# The conditional crossing bound given the two explorations

Conditionally on the state of all explored edges of the two explorations (a *fiber*), the
probability of a crossing from the lower boundary to the upper boundary is at least the
mixed-boundary square crossing probability.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity MeasureTheory
open scoped Classical

namespace Rect

variable {Q : Rect} {bB bT : ℕ}

/-- The crossing event used by the fibre argument: an open path from a cell of the rows
`≤ y0 + bB - 1` to a cell of the rows `≥ y0 + h - bT + 1`. -/
def crossEv (Q : Rect) (bB bT : ℕ) (A : Finset Cell) : Prop :=
  ∃ u v : Cell, u.2 ≤ Q.y0 + bB - 1 ∧ Q.y0 + Q.h - bT + 1 ≤ v.2 ∧
    Relation.ReflTransGen (StepRel primalEnds A) u v

private theorem extend_to_endpoints {R : Rect} {S A : Finset Cell} (hS : S ⊆ R.inner)
    (hA : S ⊆ A) {x : Cell} (hx : Vtx S x) :
    (∃ u : Cell, u.2 < R.y0 + R.h ∧ Relation.ReflTransGen (StepRel primalEnds A) u x) ∧
      (∃ v : Cell, R.y0 < v.2 ∧ Relation.ReflTransGen (StepRel primalEnds A) x v) := by
  obtain ⟨e, he, h⟩ := hx
  have hr := Rect.mem_inner.1 (hS he)
  have hs := Relation.ReflTransGen.single (stepRel_symm (step_of_mem (hA he)))
  have hlow : (primalEnds e).2.2 < R.y0 + R.h := by rw [primalEnds_snd_row]; omega
  have hup : R.y0 < (primalEnds e).1.2 := by rw [primalEnds_fst_row]; omega
  rcases h with rfl | rfl
  · exact ⟨⟨_, hlow, hs⟩, _, hup, .refl⟩
  · exact ⟨⟨_, hlow, .refl⟩, _, hup, hs⟩

private theorem crossEv_of_success {A₀ A S : Finset Cell}
    (hB : Q.barrier .lower bB A₀ ⊆ A) (hT : Q.barrier .upper bT A₀ ⊆ A)
    (hS : S ⊆ A) (hs : S ∈ Success (Q.barrier .lower bB A₀) (Q.barrier .upper bT A₀)) :
    Q.crossEv bB bT A := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hs
  obtain ⟨u, hu, hux⟩ := (extend_to_endpoints
    (R := Q.endBoard .lower bB) (fun _ h => ((Q.endBoard .lower bB).mem_expBd_iff.1 h).1) hB hx).1
  obtain ⟨v, hv, hyv⟩ := (extend_to_endpoints
    (R := Q.endBoard .upper bT) (fun _ h => ((Q.endBoard .upper bT).mem_expBd_iff.1 h).1) hT hy).2
  have hi := Finset.union_subset (Finset.union_subset hS hB) hT
  simp only [endBoard] at hu hv
  exact ⟨u, v, by omega, by omega, hux.trans ((Relation.ReflTransGen.mono (fun _ _ => stepRel_mono hi) _ _ hxy).trans hyv)⟩

theorem comp_of_path (ξ : FK.BoundaryCondition Q.pcells) {H₀ S : Finset Cell}
    (hH : H₀ ⊆ Q.inner) (hS : S ⊆ H₀) {x y : Q.pcells}
    (h : Relation.ReflTransGen (StepRel primalEnds S) x.1 y.1) :
    (FK.componentSetoid Q.pG ξ (cfgOf Q.pData H₀)).r x y := by
  apply FK.actualConnected_component
  rw [actualConnected_iff Q.pData, openMedials_cfgOf Q.pData H₀ hH]
  exact Relation.ReflTransGen.mono (fun a b hab => stepRel_mono hS hab) x.1 y.1 h

attribute [local instance] FK.configurationMeasurableSpace

/-- **Conditional crossing bound on a fibre.** -/
theorem fiber_bound (q : Set.Ici (1 : ℝ)) (hg : Q.Geo bB bT)
    (η : FK.BoundaryCondition Q.pcells) {A₀ : Finset Cell}
    (hbar : Q.barAll bB bT A₀) :
    (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal *
      (FK.measure Q.pG (critParams q) η
        {C | openMedials Q.pData C ∩ Q.exAll bB bT A₀ = A₀ ∩ Q.exAll bB bT A₀}).toReal ≤
    (FK.measure Q.pG (critParams q) η
        {C | openMedials Q.pData C ∩ Q.exAll bB bT A₀ = A₀ ∩ Q.exAll bB bT A₀ ∧
          Q.crossEv bB bT (openMedials Q.pData C)}).toReal := by
  let EX := Q.exAll bB bT A₀
  let H₀ := A₀ ∩ EX
  let θ := critParams q
  let 𝒮 := Success (Q.barrier .lower bB A₀) (Q.barrier .upper bT A₀)
  let A := openMedials Q.pData
  let U : Set (FK.Configuration Q.pG) := {C | A C ∩ Q.unx EX ∈ 𝒮}
  let F (H : Finset Cell) : Set (FK.Configuration Q.pG) := {C | A C ∩ EX = H}
  have hEX : EX ⊆ Q.inner := exAll_subset_inner A₀ hg
  have hH : H₀ ⊆ EX := Finset.inter_subset_right
  have hbd (s : Side) (b : ℕ) (h : Q.explored s b A₀ ⊆ EX) : Q.barrier s b A₀ ⊆ H₀ :=
    Finset.subset_inter ((Q.endBoard s b).expBd_subset _ _ A₀) ((barrier_subset_explored Q s b A₀).trans h)
  have hB := hbd .lower bB Finset.subset_union_left
  have hT := hbd .upper bT Finset.subset_union_right
  have h𝒮 : ∀ a b : Finset Cell, a ⊆ b → a ∈ 𝒮 → b ∈ 𝒮 := by
    rintro a b hab ⟨x, y, hx, hy, hxy⟩
    exact ⟨x, y, hx, hy, Relation.ReflTransGen.mono (fun _ _ => stepRel_mono
      (Finset.union_subset_union (Finset.union_subset_union hab (subset_refl _)) (subset_refl _))) _ _ hxy⟩
  have hmark (ξ : FK.BoundaryCondition Q.pcells) (H : Finset Cell) (h : H ⊆ EX) :
      (FK.measure Q.pG θ ξ (F H ∩ U)).toReal =
        (nuMeasure Q EX θ (FK.componentSetoid Q.pG ξ (cfgOf Q.pData H)) 𝒮).toReal *
          (FK.measure Q.pG θ ξ (F H)).toReal := by
    rw [← ENNReal.toReal_mul, ← markov_cell θ ξ hEX h 𝒮]; rfl
  let Pψ := FK.componentSetoid Q.pG Q.sepBC (cfgOf Q.pData EX)
  let Pη := FK.componentSetoid Q.pG η (cfgOf Q.pData H₀)
  have hPP : ∀ x y : Q.pcells, Vtx (Q.unx EX) x.1 → Vtx (Q.unx EX) y.1 → Pψ.r x y → Pη.r x y := by
    intro x y hx hy hxy
    rcases kc hg hbar hx hy hxy with rfl | ⟨hxB, hyB⟩ | ⟨hxT, hyT⟩
    · exact Setoid.refl' _ _
    · exact comp_of_path η (hH.trans hEX) hB (Vtx_barrier_connected hg.hbB hg.hw hbar.1 hxB hyB)
    · exact comp_of_path η (hH.trans hEX) hT (Vtx_barrier_connected hg.hbT hg.hw hbar.2 hxT hyT)
  have hν := nu_mono (Q := Q) (Ex := EX) θ hPP h𝒮
  have hκ : (FK.measure Q.pG θ Q.sepBC Q.crossP).toReal ≤ (nuMeasure Q EX θ Pψ 𝒮).toReal := by
    have hin : F EX ∩ Q.crossP ⊆ F EX ∩ U := by
      rintro C ⟨hC, u, v, hu, hv, huv⟩
      rw [actualConnected_iff Q.pData] at huv
      have hA := openMedials_subset Q.pData C
      have hr : A C ∩ Q.unx EX = A C \ EX := by ext m; grind [mem_unx]
      refine ⟨hC, ?_⟩
      change A C ∩ Q.unx EX ∈ 𝒮
      rw [hr]
      exact cross_to_success hg hbar hA hu hv huv
    have hE : F EX = {C | EX ⊆ A C} := by ext; simp [F]
    have hpos : 0 < (FK.measure Q.pG θ Q.sepBC (F EX)).toReal := by
      rw [hE]
      refine ENNReal.toReal_pos ((FK.measure_pos_iff _ _ _ _).2 ⟨Finset.univ, ?_⟩).ne' (measure_ne_top _ _)
      exact fun m hm => (mem_openMedials Q.pData _ m).2 ⟨hEX hm, Finset.mem_univ _⟩
    have hFKG := FK.measure_positive_association θ Q.sepBC (F EX) Q.crossP
      (by rw [hE]; exact fun _ _ h h' => h'.trans (openMedials_mono' h)) Q.isUpperSet_crossP
    have hm := measureReal_mono (μ := FK.measure Q.pG θ Q.sepBC) hin
    rw [measureReal_def, measureReal_def, hmark _ _ (subset_refl _)] at hm
    exact le_of_mul_le_mul_right (by nlinarith) hpos
  have hf : F H₀ ∩ U ⊆ {C | A C ∩ EX = H₀ ∧ Q.crossEv bB bT (A C)} := by
    rintro C ⟨hC, hU⟩
    have hO : H₀ ⊆ A C := hC ▸ Finset.inter_subset_left
    exact ⟨hC, crossEv_of_success (hB.trans hO) (hT.trans hO) Finset.inter_subset_left hU⟩
  refine (mul_le_mul_of_nonneg_right (hκ.trans hν) ENNReal.toReal_nonneg).trans ?_
  rw [← hmark η H₀ hH]
  exact measureReal_mono hf

end Rect

/-- Summation over fibres of a function: a lower bound on every fibre of `E` gives the same bound
on `E`. -/
theorem sum_fibers {X β : Type*} [Fintype X] [DecidableEq β] [MeasurableSpace X]
    (hms : ∀ s : Set X, MeasurableSet s) (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] (key : X → β) (E Y : Set X) (κ : ℝ)
    (hE : ∀ x ∈ E, ∀ x', key x' = key x → x' ∈ E)
    (hfib : ∀ x ∈ E, κ * μ.real {x' | key x' = key x} ≤ μ.real (Y ∩ {x' | key x' = key x})) :
    κ * μ.real E ≤ μ.real (Y ∩ E) := by
  let K := (Finset.univ.filter (· ∈ E)).image key
  let F (k : β) := key ⁻¹' {k}
  have hK (k : β) : k ∈ K ↔ ∃ x ∈ E, key x = k := by simp [K]
  have hdisj := Set.pairwiseDisjoint_fiber key (K : Set β)
  have hdisj' : (K : Set β).PairwiseDisjoint (fun k => Y ∩ F k) :=
    fun a ha b hb hab => (hdisj ha hb hab).mono Set.inter_subset_right Set.inter_subset_right
  have hEdec : E = ⋃ k ∈ K, F k := by
    ext x
    simp only [Set.mem_iUnion, hK, F, Set.mem_preimage, Set.mem_singleton_iff, exists_prop]
    constructor
    · exact fun hx => ⟨key x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨k, ⟨y, hy, rfl⟩, hx⟩
      exact hE y hy x hx
  rw [hEdec, measureReal_biUnion_finset hdisj (fun _ _ => hms _), Finset.mul_sum]
  simp_rw [Set.inter_iUnion]
  rw [measureReal_biUnion_finset hdisj' (fun _ _ => hms _)]
  apply Finset.sum_le_sum
  intro k hk
  obtain ⟨x, hx, rfl⟩ := (hK k).mp hk
  exact hfib x hx

namespace Rect

variable {Q : Rect} {bB bT : ℕ}

attribute [local instance] FK.configurationMeasurableSpace

/-- **Board-level bound** ("BL"): for every boundary condition, the probability of the crossing
event is at least the mixed square crossing probability times the probability of the two
barriers. -/
theorem board_bl (q : Set.Ici (1 : ℝ)) (hg : Q.Geo bB bT)
    (η : FK.BoundaryCondition Q.pcells) :
    (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal *
      (FK.measure Q.pG (critParams q) η
        {C | Q.barAll bB bT (openMedials Q.pData C)}).toReal ≤
    (FK.measure Q.pG (critParams q) η
        {C | Q.crossEv bB bT (openMedials Q.pData C)}).toReal := by
  let : Fintype Q.pG.edgeSet := Fintype.ofFinite _
  have : MeasureTheory.IsFiniteMeasure (FK.measure Q.pG (critParams q) η) := inferInstance
  let key := fun C =>
    (Q.exAll bB bT (openMedials Q.pData C),
      openMedials Q.pData C ∩ Q.exAll bB bT (openMedials Q.pData C))
  have hfibre : ∀ x : FK.Configuration Q.pG, {x' | key x' = key x} =
      {C | openMedials Q.pData C ∩ Q.exAll bB bT (openMedials Q.pData x) =
        openMedials Q.pData x ∩ Q.exAll bB bT (openMedials Q.pData x)} := by
    intro x
    ext x'
    simp only [Set.mem_ofPred_eq]
    constructor
    · grind
    · intro h
      have := exAll_congr (bB := bB) (bT := bT) (Q := Q) h
      simp only [key]
      rw [this.1, h]
  have key_main := sum_fibers (fun s => MeasurableSpace.measurableSet_top)
    (FK.measure Q.pG (critParams q) η) key
    {C | Q.barAll bB bT (openMedials Q.pData C)} {C | Q.crossEv bB bT (openMedials Q.pData C)}
    (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal
    (by
      intro x hx x' hx'
      have hx'' : x' ∈ {x' | key x' = key x} := hx'
      rw [hfibre] at hx''
      have := exAll_congr (bB := bB) (bT := bT) (Q := Q) hx''
      exact this.2.2 hx)
    (by
      intro x hx
      rw [hfibre]
      have := fiber_bound q hg η hx
      have heq : {C : FK.Configuration Q.pG | Q.crossEv bB bT (openMedials Q.pData C)} ∩
          {C | openMedials Q.pData C ∩ Q.exAll bB bT (openMedials Q.pData x) =
            openMedials Q.pData x ∩ Q.exAll bB bT (openMedials Q.pData x)} =
          {C | openMedials Q.pData C ∩ Q.exAll bB bT (openMedials Q.pData x) =
            openMedials Q.pData x ∩ Q.exAll bB bT (openMedials Q.pData x) ∧
            Q.crossEv bB bT (openMedials Q.pData C)} := by
        ext C; simp [and_comm]
      rw [heq]
      exact this)
  calc _ ≤ _ := key_main
    _ ≤ _ := ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) (MeasureTheory.measure_mono Set.inter_subset_left)

end Rect

end PottsDiscontinuity.TorusCrossing
