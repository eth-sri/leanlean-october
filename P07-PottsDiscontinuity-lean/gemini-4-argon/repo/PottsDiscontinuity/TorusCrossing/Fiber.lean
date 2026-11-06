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

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable {Q : Rect} {bB bT : ℕ}

def crossEv (Q : Rect) (bB bT : ℕ) (A : Finset Cell) : Prop :=
  ∃ u v : Cell, u.2 ≤ Q.y0 + bB - 1 ∧ Q.y0 + Q.h - bT + 1 ≤ v.2 ∧
    Relation.ReflTransGen (StepRel primalEnds A) u v

theorem extend_low {A₀ A : Finset Cell} (hbdA : Q.bdB bB A₀ ⊆ A) {x : Cell}
    (hx : Vtx (Q.bdB bB A₀) x) :
    ∃ u : Cell, u.2 ≤ Q.y0 + bB - 1 ∧ Relation.ReflTransGen (StepRel primalEnds A) u x := by
  obtain ⟨e, he, hxe⟩ := hx
  have hr := Rect.mem_inner.1 ((Q.botB bB).mem_expBd_iff.1 he).1
  simp only [botB_x0, botB_y0, botB_w, botB_h] at hr
  have hlow : (primalEnds e).2.2 ≤ Q.y0 + bB - 1 := by rw [primalEnds_snd_row]; omega
  rcases hxe with rfl | rfl
  · exact ⟨_, hlow, Relation.ReflTransGen.single (stepRel_symm (step_of_mem (hbdA he)))⟩
  · exact ⟨_, hlow, Relation.ReflTransGen.refl⟩

theorem extend_up {A₀ A : Finset Cell} (hbdA : Q.bdT bT A₀ ⊆ A) {y : Cell}
    (hy : Vtx (Q.bdT bT A₀) y) :
    ∃ v : Cell, Q.y0 + Q.h - bT + 1 ≤ v.2 ∧ Relation.ReflTransGen (StepRel primalEnds A) y v := by
  obtain ⟨e, he, hye⟩ := hy
  have hr := Rect.mem_inner.1 ((Q.topT bT).mem_expBd_iff.1 he).1
  simp only [topT_x0, topT_y0, topT_w, topT_h] at hr
  have hup : Q.y0 + Q.h - bT + 1 ≤ (primalEnds e).1.2 := by rw [primalEnds_fst_row]; omega
  rcases hye with rfl | rfl
  · exact ⟨_, hup, Relation.ReflTransGen.refl⟩
  · exact ⟨_, hup, Relation.ReflTransGen.single (stepRel_symm (step_of_mem (hbdA he)))⟩

theorem crossEv_of_success {A₀ A : Finset Cell} (hbdB : Q.bdB bB A₀ ⊆ A) (hbdT : Q.bdT bT A₀ ⊆ A)
    (hD : (A ∩ Q.unx (Q.exAll bB bT A₀)) ∪ Q.bdB bB A₀ ∪ Q.bdT bT A₀ ⊆ A)
    (hs : ∃ x y, Vtx (Q.bdB bB A₀) x ∧ Vtx (Q.bdT bT A₀) y ∧
      Relation.ReflTransGen (StepRel primalEnds
        ((A ∩ Q.unx (Q.exAll bB bT A₀)) ∪ Q.bdB bB A₀ ∪ Q.bdT bT A₀)) x y) :
    Q.crossEv bB bT A := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hs
  obtain ⟨u, hu, hux⟩ := extend_low hbdB hx
  obtain ⟨v, hv, hyv⟩ := extend_up hbdT hy
  exact ⟨u, v, hu, hv, (hux.trans (Relation.ReflTransGen.mono
    (fun _ _ => stepRel_mono hD) x y hxy)).trans hyv⟩

theorem comp_of_path (ξ : FK.BoundaryCondition Q.pcells) {H₀ S : Finset Cell}
    (hH : H₀ ⊆ Q.inner) (hS : S ⊆ H₀) {x y : Q.pcells}
    (h : Relation.ReflTransGen (StepRel primalEnds S) x.1 y.1) :
    (FK.componentSetoid Q.pG ξ (cfgOf Q.pData H₀)).r x y := by
  apply FK.actualConnected_component
  rw [actualConnected_iff Q.pData, openMedials_cfgOf Q.pData H₀ hH]
  exact Relation.ReflTransGen.mono (fun _ _ => stepRel_mono hS) x.1 y.1 h

attribute [local instance] FK.configurationMeasurableSpace

theorem fiber_bound (q : Set.Ici (1 : ℝ)) (hg : Q.Geo bB bT)
    (η : FK.BoundaryCondition Q.pcells) {A₀ : Finset Cell}
    (hbar : Q.barAll bB bT A₀) :
    (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal *
      (FK.measure Q.pG (critParams q) η
        {C | openMedials Q.pData C ∩ Q.exAll bB bT A₀ = A₀ ∩ Q.exAll bB bT A₀}).toReal ≤
    (FK.measure Q.pG (critParams q) η
        {C | openMedials Q.pData C ∩ Q.exAll bB bT A₀ = A₀ ∩ Q.exAll bB bT A₀ ∧
          Q.crossEv bB bT (openMedials Q.pData C)}).toReal := by
  set EX := Q.exAll bB bT A₀
  have hEXin : EX ⊆ Q.inner := exAll_subset_inner A₀ hg
  set H₀ := A₀ ∩ EX
  have hHsub : H₀ ⊆ EX := Finset.inter_subset_right
  have hBDB_H : Q.bdB bB A₀ ⊆ H₀ := Finset.subset_inter ((Q.botB bB).expBd_subset _ _ A₀)
    ((bdB_subset_exB Q bB A₀).trans Finset.subset_union_left)
  have hBDT_H : Q.bdT bT A₀ ⊆ H₀ := Finset.subset_inter ((Q.topT bT).expBd_subset _ _ A₀)
    ((bdT_subset_exT Q bT A₀).trans Finset.subset_union_right)
  have hHin : H₀ ⊆ Q.inner := hHsub.trans hEXin
  let 𝒮 : Set (Finset Cell) := {A' | ∃ x y, Vtx (Q.bdB bB A₀) x ∧ Vtx (Q.bdT bT A₀) y ∧
    Relation.ReflTransGen (StepRel primalEnds (A' ∪ Q.bdB bB A₀ ∪ Q.bdT bT A₀)) x y}
  have h𝒮 : ∀ A B : Finset Cell, A ⊆ B → A ∈ 𝒮 → B ∈ 𝒮 := by
    rintro A B hAB ⟨x, y, hx, hy, hxy⟩
    exact ⟨x, y, hx, hy, Relation.ReflTransGen.mono (fun _ _ => stepRel_mono
      (Finset.union_subset_union_left (Finset.union_subset_union_left hAB))) x y hxy⟩
  set θ := critParams q
  have hsub : {C | openMedials Q.pData C ∩ EX = H₀ ∧ openMedials Q.pData C ∩ Q.unx EX ∈ 𝒮} ⊆
      {C | openMedials Q.pData C ∩ EX = H₀ ∧ Q.crossEv bB bT (openMedials Q.pData C)} := by
    rintro C ⟨h1, h2⟩
    have hH : H₀ ⊆ openMedials Q.pData C := h1 ▸ Finset.inter_subset_left
    exact ⟨h1, crossEv_of_success (hBDB_H.trans hH) (hBDT_H.trans hH)
      (Finset.union_subset (Finset.union_subset Finset.inter_subset_left (hBDB_H.trans hH))
        (hBDT_H.trans hH)) h2⟩
  have h1 := ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
    (MeasureTheory.measure_mono (μ := FK.measure Q.pG θ η) hsub)
  rw [markov_cell θ η hEXin hHsub 𝒮, ENNReal.toReal_mul] at h1
  set Pψ := FK.componentSetoid Q.pG Q.sepBC (cfgOf Q.pData EX)
  set Pη := FK.componentSetoid Q.pG η (cfgOf Q.pData H₀)
  have h2 := nu_mono (Q := Q) (Ex := EX) θ
    (show ∀ x y : Q.pcells, Vtx (Q.unx EX) x.1 → Vtx (Q.unx EX) y.1 → Pψ.r x y → Pη.r x y from
      fun x y hx hy hxy => by
        rcases kc hg hbar hx hy hxy with rfl | ⟨hxB, hyB⟩ | ⟨hxT, hyT⟩
        · exact Setoid.refl' _ _
        · exact comp_of_path η hHin hBDB_H (Vtx_bdB_connected hg hbar.1 hxB hyB)
        · exact comp_of_path η hHin hBDT_H (Vtx_bdT_connected hg hbar.2 hxT hyT)) h𝒮
  have hfrozS := markov_cell θ Q.sepBC hEXin (subset_refl EX) 𝒮
  have hevent : {C | EX ⊆ openMedials Q.pData C} ∩ Q.crossP ⊆
      {C | EX ⊆ openMedials Q.pData C ∧ openMedials Q.pData C ∩ Q.unx EX ∈ 𝒮} := by
    rintro C ⟨hC1, u, v, hu, hv, huv⟩
    rw [actualConnected_iff Q.pData] at huv
    obtain ⟨x, y, hx, hy, hxy⟩ := cross_to_success hg hbar (openMedials_subset Q.pData C) hu hv huv
    refine ⟨hC1, x, y, hx, hy, ?_⟩
    rwa [show openMedials Q.pData C ∩ Q.unx EX = openMedials Q.pData C \ EX by
      ext m; simp only [Finset.mem_inter, Finset.mem_sdiff, mem_unx]
      exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, openMedials_subset Q.pData C h1, h3⟩⟩]
  have hFKG := FK.measure_positive_association (G := Q.pG) θ Q.sepBC
    {C | EX ⊆ openMedials Q.pData C} Q.crossP
    (fun _ _ hCC' hC => hC.trans (openMedials_mono' hCC')) Q.isUpperSet_crossP
  have hpos : 0 < (FK.measure Q.pG θ Q.sepBC {C | EX ⊆ openMedials Q.pData C}).toReal := by
    refine ENNReal.toReal_pos ((FK.measure_pos_iff _ _ _ _).2 ?_).ne'
      (MeasureTheory.measure_ne_top _ _)
    exact ⟨Finset.univ, fun m hm => (mem_openMedials Q.pData _ m).2 ⟨hEXin hm, by simp⟩⟩
  have h3 := ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
    (MeasureTheory.measure_mono (μ := FK.measure Q.pG θ Q.sepBC) hevent)
  have hfrozS' : (FK.measure Q.pG θ Q.sepBC {C | EX ⊆ openMedials Q.pData C ∧
        openMedials Q.pData C ∩ Q.unx EX ∈ 𝒮}).toReal =
      (nuMeasure Q EX θ Pψ 𝒮).toReal *
        (FK.measure Q.pG θ Q.sepBC {C | EX ⊆ openMedials Q.pData C}).toReal := by
    have := congrArg ENNReal.toReal hfrozS
    simp only [Finset.inter_eq_right, ENNReal.toReal_mul] at this
    exact this
  have hκ : (FK.measure Q.pG θ Q.sepBC Q.crossP).toReal ≤ (nuMeasure Q EX θ Pψ 𝒮).toReal := by
    nlinarith [hFKG, h3, hfrozS']
  exact (mul_le_mul_of_nonneg_right (hκ.trans h2) ENNReal.toReal_nonneg).trans h1

end Rect

theorem sum_fibers {X β : Type*} [Fintype X] [DecidableEq β] [MeasurableSpace X]
    (hms : ∀ s : Set X, MeasurableSet s) (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] (key : X → β) (E Y : Set X) (κ : ℝ)
    (hE : ∀ x ∈ E, ∀ x', key x' = key x → x' ∈ E)
    (hfib : ∀ x ∈ E, κ * μ.real {x' | key x' = key x} ≤ μ.real (Y ∩ {x' | key x' = key x})) :
    κ * μ.real E ≤ μ.real (Y ∩ E) := by
  set K : Finset β := (Finset.univ.filter (fun x => x ∈ E)).image key
  have hKmem (k : β) (hk : k ∈ K) : ∃ x ∈ E, key x = k := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hk
    exact ⟨x, (Finset.mem_filter.1 hx).2, rfl⟩
  have hdisj : (↑K : Set β).PairwiseDisjoint (fun k => {x' : X | key x' = k}) :=
    fun _ _ _ _ hab => Set.disjoint_left.2 fun _ hxa hxb => hab (hxa.symm.trans hxb)
  have hEdec : E = ⋃ k ∈ K, {x' : X | key x' = k} := by
    ext x; simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    exact ⟨fun hx => ⟨key x, Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩, rfl⟩, rfl⟩,
      fun ⟨k, hk, hxk⟩ => by obtain ⟨x0, hx0, rfl⟩ := hKmem k hk; exact hE x0 hx0 x hxk⟩
  have hYdec : Y ∩ E = ⋃ k ∈ K, (Y ∩ {x' : X | key x' = k}) := by
    rw [hEdec, Set.inter_iUnion₂]
  have h1 : μ.real E = ∑ k ∈ K, μ.real {x' : X | key x' = k} := by
    conv_lhs => rw [hEdec]
    exact MeasureTheory.measureReal_biUnion_finset hdisj (fun _ _ => hms _)
  have h2 : μ.real (Y ∩ E) = ∑ k ∈ K, μ.real (Y ∩ {x' : X | key x' = k}) := by
    conv_lhs => rw [hYdec]
    exact MeasureTheory.measureReal_biUnion_finset
      (fun a ha b hb hab => (hdisj ha hb hab).mono Set.inter_subset_right Set.inter_subset_right)
      (fun _ _ => hms _)
  rw [h1, h2, Finset.mul_sum]
  exact Finset.sum_le_sum fun k hk => by obtain ⟨x, hx, rfl⟩ := hKmem k hk; exact hfib x hx

namespace Rect

variable {Q : Rect} {bB bT : ℕ}

attribute [local instance] FK.configurationMeasurableSpace

theorem board_bl (q : Set.Ici (1 : ℝ)) (hg : Q.Geo bB bT)
    (η : FK.BoundaryCondition Q.pcells) :
    (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal *
      (FK.measure Q.pG (critParams q) η
        {C | Q.barAll bB bT (openMedials Q.pData C)}).toReal ≤
    (FK.measure Q.pG (critParams q) η
        {C | Q.crossEv bB bT (openMedials Q.pData C)}).toReal := by
  let : Fintype Q.pG.edgeSet := Fintype.ofFinite _
  have : MeasureTheory.IsFiniteMeasure (FK.measure Q.pG (critParams q) η) := inferInstance
  let key : FK.Configuration Q.pG → Finset Cell × Finset Cell := fun C =>
    (Q.exAll bB bT (openMedials Q.pData C),
      openMedials Q.pData C ∩ Q.exAll bB bT (openMedials Q.pData C))
  have hfibre (x : FK.Configuration Q.pG) : {x' | key x' = key x} =
      {C | openMedials Q.pData C ∩ Q.exAll bB bT (openMedials Q.pData x) =
        openMedials Q.pData x ∩ Q.exAll bB bT (openMedials Q.pData x)} := by
    ext x'; simp only [Set.mem_ofPred_eq, key, Prod.mk.injEq]
    exact ⟨fun ⟨h1, h2⟩ => by rwa [h1] at h2, fun h => by rw [(exAll_congr h).1, h]; exact ⟨rfl, rfl⟩⟩
  have key_main := sum_fibers (fun _ => MeasurableSpace.measurableSet_top)
    (FK.measure Q.pG (critParams q) η) key
    {C | Q.barAll bB bT (openMedials Q.pData C)} {C | Q.crossEv bB bT (openMedials Q.pData C)}
    (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal
    (fun x hx x' hx' => by
      have hx'' : x' ∈ {x' | key x' = key x} := hx'
      rw [hfibre] at hx''
      have := exAll_congr (bB := bB) (bT := bT) (Q := Q) hx''
      exact ⟨this.2.2.2.2.2.1.2 hx.1, this.2.2.2.2.2.2.2 hx.2⟩)
    (fun x hx => by
      rw [hfibre, show {C : FK.Configuration Q.pG | Q.crossEv bB bT (openMedials Q.pData C)} ∩
          {C | openMedials Q.pData C ∩ Q.exAll bB bT (openMedials Q.pData x) =
            openMedials Q.pData x ∩ Q.exAll bB bT (openMedials Q.pData x)} =
          {C | openMedials Q.pData C ∩ Q.exAll bB bT (openMedials Q.pData x) =
            openMedials Q.pData x ∩ Q.exAll bB bT (openMedials Q.pData x) ∧
            Q.crossEv bB bT (openMedials Q.pData C)} by ext; simp [and_comm]]
      exact fiber_bound q hg η hx)
  exact key_main.trans (ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
    (MeasureTheory.measure_mono Set.inter_subset_left))

end Rect

end PottsDiscontinuity.TorusCrossing
