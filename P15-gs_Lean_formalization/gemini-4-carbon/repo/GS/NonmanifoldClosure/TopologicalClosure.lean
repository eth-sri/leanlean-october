module

public import GS.Topology.PuncturedSphereObstruction
public import GS.NonmanifoldClosure.ChartRetractions
public import GS.NonmanifoldFinal.ConditionalGS
public import GS.NonmanifoldFinal.FiniteCoordinates
public import GS.NonmanifoldFinal.EuclideanTransport
public import GS.Specifications
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

noncomputable section
open Matrix GS GS.GlobalGeometry GS.Nonmanifold GS.NonmanifoldObstruction GS.NonmanifoldFinal
open scoped BigOperators Topology

namespace GS.NonmanifoldClosure

theorem uniform_neighbourhood_of_compact_parameter
    {A K X : Type*} [TopologicalSpace A] [TopologicalSpace K]
    [TopologicalSpace X] [CompactSpace K]
    (F : A × K → X) (hF : Continuous F) (a : A) (U : Set X)
    (hU : IsOpen U) (ha : ∀ k, F (a, k) ∈ U) :
    ∃ V : Set A, IsOpen V ∧ a ∈ V ∧ ∀ t ∈ V, ∀ k, F (t, k) ∈ U := by
  let C : Set (A × K) := F ⁻¹' Uᶜ
  refine ⟨(Prod.fst '' C)ᶜ, (isClosedMap_fst_of_compactSpace C (hU.isClosed_compl.preimage hF)).isOpen_compl,
    ?_, fun t ht k => by_contra fun hn => ht ⟨(t, k), hn, rfl⟩⟩
  rintro ⟨⟨t, k⟩, htk, rfl⟩; exact htk (ha k)

structure IsolatedEuclideanRetract (X : Type*) [TopologicalSpace X] (x₀ : X) (m : ℕ) where
  sectionMap : Eucl m → X
  projectionMap : X → Eucl m
  section_continuous : Continuous sectionMap
  projection_continuous : Continuous projectionMap
  projection_section : ∀ x, projectionMap (sectionMap x) = x
  section_zero : sectionMap 0 = x₀
  projection_zero_iff : ∀ x, projectionMap x = 0 ↔ x = x₀

theorem IsolatedEuclideanRetract.punctured_sphere {X : Type} [TopologicalSpace X] {x₀ : X} {m : ℕ}
    (r : IsolatedEuclideanRetract X x₀ m) (U : Set X) (hU : IsOpen U) (hx : x₀ ∈ U) :
    Nonempty (ContinuousSectionPair (UnitSphere (Fin m)) (PuncturedIn U x₀)) := by
  haveI : CompactSpace (UnitSphere (Fin m)) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Eucl m) 1)
  let F : ℝ × UnitSphere (Fin m) → X := fun p => r.sectionMap (p.1 • p.2.val)
  have hF : Continuous F := r.section_continuous.comp
    (Continuous.smul continuous_fst (continuous_subtype_val.comp continuous_snd))
  obtain ⟨V, hV, h0, hVsub⟩ := uniform_neighbourhood_of_compact_parameter F hF 0 U hU
    fun v => by simpa [F, r.section_zero] using hx
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hV 0 h0
  let t := δ / 2
  have ht : 0 < t := by positivity
  have htV : t ∈ V := hball <| by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]; dsimp [t]; linarith
  have hnorm (v : UnitSphere (Fin m)) : ‖v.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using v.property
  have hne (p : PuncturedIn U x₀) : r.projectionMap p.val ≠ 0 :=
    fun he => p.property.2 ((r.projection_zero_iff p.val).mp he)
  refine ⟨{
    sectionMap := fun v => ⟨r.sectionMap (t • v.val), hVsub t htV v, fun he => by
      have hp := congrArg (fun x => ‖r.projectionMap x‖) he
      rw [r.projection_section, (r.projection_zero_iff x₀).mpr rfl,
        norm_smul, Real.norm_eq_abs, abs_of_pos ht, hnorm v, mul_one, norm_zero] at hp
      exact (ne_of_gt ht) hp⟩
    retractionMap := fun x => ⟨‖r.projectionMap x.val‖⁻¹ • r.projectionMap x.val, by
      simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr (hne x))),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hne x))]⟩
    section_continuous := ?_
    retraction_continuous := ?_
    retraction_section := fun v => Subtype.ext <| by
      change ‖r.projectionMap (r.sectionMap (t • v.val))‖⁻¹ •
        r.projectionMap (r.sectionMap (t • v.val)) = v.val
      rw [r.projection_section, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        hnorm v, mul_one, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul] }⟩
  · exact (r.section_continuous.comp (continuous_subtype_val.const_smul t)).subtype_mk _
  · apply Continuous.subtype_mk
    exact (((r.projection_continuous.comp continuous_subtype_val).norm).inv₀
      fun x => norm_ne_zero_iff.mpr (hne x)).smul
      (r.projection_continuous.comp continuous_subtype_val)

theorem chart_dimension_of_sphereRetractions {X : Type} [TopologicalSpace X] {m n : ℕ}
    (c : OpenEuclideanChart X n) (x : X) (hx : x ∈ c.source)
    (O : Set X) (hO : IsOpen O) (hxO : x ∈ O) (hret : SphereRetractionsOn O x m) : n = m := by
  obtain ⟨b, hb⟩ := exists_centeredChart_within c x hx O hO hxO
  obtain ⟨p⟩ := hret b.source b.source_open b.source_point (fun _ h => (hb h).2)
  exact GS.Topology.sphere_retract_ball_dimension m n b.radius_pos
    (transportSectionPair p (Homeomorph.refl _) b.punctured)

theorem dimensions_of_overlapping_charts {X : Type} [TopologicalSpace X] {m n : ℕ}
    (c : OpenEuclideanChart X n) (d : OpenEuclideanChart X m)
    (x : X) (hx : x ∈ c.source) (hy : x ∈ d.source) : n = m :=
  chart_dimension_of_sphereRetractions c x hx d.source d.source_open hy (d.sphereRetractions x hy)

theorem not_euclidean_of_retract_regular_charts {X : Type} [TopologicalSpace X] {x₀ : X} {m : ℕ}
    (r : IsolatedEuclideanRetract X x₀ m) (k : ℕ) (hmk : m ≠ k)
    (hregular : ∀ U : Set X, IsOpen U → x₀ ∈ U →
      ∃ c : OpenEuclideanChart X k, ∃ x : X, x ∈ U ∧ x ∈ c.source) :
    ¬ EuclideanAt x₀ := by
  intro he
  obtain ⟨n, c, hc⟩ := (euclideanAt_iff_chart x₀).mp he
  have hn : n = m := chart_dimension_of_sphereRetractions c x₀ hc Set.univ isOpen_univ
    (Set.mem_univ _) fun U hU hx _ => r.punctured_sphere U hU hx
  obtain ⟨d, x, hxc, hxd⟩ := hregular c.source c.source_open hc
  exact hmk (hn.symm.trans (dimensions_of_overlapping_charts c d x hxc hxd))

section GenPivot
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

abbrev GenRankCone (s : ℕ) (κ : Type*) [Fintype κ] :=
  {W : Matrix (Fin (s + 1)) κ ℝ // W.rank ≤ 1}

def genProductZero (s : ℕ) : (ι → ℝ) × GenRankCone s κ := (0, ⟨0, by simp⟩)

def genPivotSource (s : ℕ) (j : κ) : Set ((ι → ℝ) × GenRankCone s κ) :=
  {p | p.2.val 0 j ≠ 0}

def genPivotDomain (s : ℕ) (j : κ) : Set ((ι → ℝ) × ((κ → ℝ) × (Fin s → ℝ))) :=
  {q | q.2.1 j ≠ 0}

def genOuter {s : ℕ} (u : Fin (s + 1) → ℝ) (z : κ → ℝ) : Matrix (Fin (s + 1)) κ ℝ :=
  fun i k => u i * z k

omit [DecidableEq κ] in
theorem gen_rank_outer_le_one {s : ℕ} (u : Fin (s + 1) → ℝ) (z : κ → ℝ) :
    (genOuter u z).rank ≤ 1 := by
  let U : Matrix (Fin (s + 1)) (Fin 1) ℝ := fun i _ => u i
  let Z : Matrix (Fin 1) κ ℝ := fun _ k => z k
  have h : genOuter u z = U * Z := by
    ext i k; simp [genOuter, U, Z, Matrix.mul_apply]
  rw [h]
  exact (Matrix.rank_mul_le_left U Z).trans (by simpa using Matrix.rank_le_card_width U)

theorem gen_rank_le_one_minor {s : ℕ} (W : Matrix (Fin (s + 1)) κ ℝ) (hW : W.rank ≤ 1)
    (i k : Fin (s + 1)) (j l : κ) : W i j * W k l = W i l * W k j := by
  let R : Matrix (Fin 2) (Fin (s + 1)) ℝ := fun a b => if ![i, k] a = b then 1 else 0
  have he : R * W = W.submatrix ![i, k] id := by ext a b; simp [R, Matrix.mul_apply]
  have hr : (W.submatrix ![i, k] id).rank ≤ 1 := he ▸ (Matrix.rank_mul_le_right R W).trans hW
  simpa using rank_le_one_two_column_minor (W.submatrix ![i, k] id) hr j l

def genRegularCoordsEuclidean (s : ℕ) :
    ((ι → ℝ) × ((κ → ℝ) × (Fin s → ℝ))) ≃ₜ Eucl (Fintype.card ι + Fintype.card κ + s) := by
  have hcard : Fintype.card (ι ⊕ (κ ⊕ Fin s)) = Fintype.card ι + Fintype.card κ + s := by
    simp [Nat.add_assoc]
  exact (((Homeomorph.refl _).prodCongr sumCoordinates).trans sumCoordinates).trans
    ((reindexReal ((Fintype.equivFin _).trans (Equiv.cast (congrArg Fin hcard)))).trans
      (EuclideanSpace.equiv _ ℝ).symm.toHomeomorph)

def genPivotHomeomorph (s : ℕ) (j : κ) :
    genPivotSource (ι := ι) s j ≃ₜ genPivotDomain (ι := ι) s j where
  toFun p := ⟨(p.val.1, (p.val.2.val 0, fun i => p.val.2.val i.succ j / p.val.2.val 0 j)), p.property⟩
  invFun q := ⟨(q.val.1, ⟨genOuter (Fin.cases 1 q.val.2.2) q.val.2.1, gen_rank_outer_le_one _ _⟩),
    by change genOuter (Fin.cases 1 q.val.2.2) q.val.2.1 0 j ≠ 0; simp only [genOuter, Fin.cases_zero, one_mul]; exact q.property⟩
  left_inv p := by
    apply Subtype.ext; apply Prod.ext
    · rfl
    · apply Subtype.ext; ext i k
      refine Fin.cases (by simp [genOuter]) (fun i => ?_) i
      have hm := gen_rank_le_one_minor p.val.2.val p.val.2.property 0 i.succ j k
      change (p.val.2.val i.succ j / p.val.2.val 0 j) * p.val.2.val 0 k = p.val.2.val i.succ k
      have hp0 : p.val.2.val 0 j ≠ 0 := p.property
      field_simp [hp0]; nlinarith [hm]
  right_inv q := by
    apply Subtype.ext; apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext k; simp [genOuter]
      · funext i; simp [genOuter, show q.val.2.1 j ≠ 0 from q.property]
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine (continuous_fst.comp continuous_subtype_val).prodMk ?_
    let hp2 : Continuous (fun p : genPivotSource (ι := ι) s j => p.val.2.val) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
    let hp0j : Continuous (fun p : genPivotSource (ι := ι) s j => p.val.2.val 0 j) :=
      (continuous_apply j).comp ((continuous_apply 0).comp hp2)
    exact ((continuous_apply 0).comp hp2).prodMk (continuous_pi fun i =>
      (((continuous_apply j).comp ((continuous_apply i.succ).comp hp2)).div hp0j fun p => p.property))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      apply continuous_pi; intro i; apply continuous_pi; intro k
      have hqk : Continuous (fun q : genPivotDomain (ι := ι) s j => q.val.2.1 k) :=
        (continuous_apply k).comp (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))
      refine Fin.cases ?_ (fun i => ?_) i <;> dsimp [genOuter]
      · exact continuous_const.mul hqk
      · exact (((continuous_apply i).comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val))).mul hqk)

def genPivotChart (s : ℕ) (j : κ) :
    OpenEuclideanChart ((ι → ℝ) × GenRankCone s κ) (Fintype.card ι + Fintype.card κ + s) where
  source := genPivotSource s j
  target := genRegularCoordsEuclidean s '' genPivotDomain s j
  source_open := (isClosed_eq
    ((continuous_apply j).comp ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_snd)))
    continuous_const).isOpen_compl
  target_open := (genRegularCoordsEuclidean s).isOpenMap _ <|
    (isClosed_eq ((continuous_apply j).comp (continuous_fst.comp continuous_snd)) continuous_const).isOpen_compl
  chart := (genPivotHomeomorph s j).trans (restrictImage (genRegularCoordsEuclidean s) (genPivotDomain s j))

def genRegularRay (s : ℕ) (j : κ) (t : ℝ) : (ι → ℝ) × GenRankCone s κ :=
  (0, ⟨genOuter (Fin.cases t (fun _ => 0)) (fun k => if k = j then 1 else 0), gen_rank_outer_le_one _ _⟩)

theorem exists_gen_regular_in_open (s : ℕ) (j : κ)
    (U : Set ((ι → ℝ) × GenRankCone s κ)) (hU : IsOpen U) (hzero : genProductZero s ∈ U) :
    ∃ p : (ι → ℝ) × GenRankCone s κ, p ∈ U ∧ p ∈ (genPivotChart (ι := ι) s j).source := by
  have hcont : Continuous (genRegularRay (ι := ι) s j) := by
    apply Continuous.prodMk continuous_const
    apply Continuous.subtype_mk
    apply continuous_pi; intro i; apply continuous_pi; intro k
    refine Fin.cases ?_ (fun _ => ?_) i <;> dsimp [genRegularRay, genOuter] <;> fun_prop
  have hr0 : genRegularRay (ι := ι) s j 0 = genProductZero s := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext; ext i k
      refine Fin.cases (by simp [genRegularRay, genOuter, genProductZero])
        (fun _ => by simp [genRegularRay, genOuter, genProductZero]) i
  have hz : (0 : ℝ) ∈ genRegularRay (ι := ι) s j ⁻¹' U := by
    simpa only [Set.mem_preimage, hr0] using hzero
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ((hU.preimage hcont).mem_nhds hz)
  refine ⟨genRegularRay s j (δ / 2), hball ?_, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith
  · simp [genPivotChart, genPivotSource, genRegularRay, genOuter]; linarith

end GenPivot
end GS.NonmanifoldClosure

namespace GS.NonmanifoldTopology
open GS.NonmanifoldClosure

def planeProductRetract (e d : ℕ) :
    IsolatedEuclideanRetract (ConeSpace (Fin e) (Fin (d + 2))) productZero (e + 2) := by
  have hc : Fintype.card (Fin e ⊕ Fin 2) = e + 2 := by simp
  let eqv : ((Fin e → ℝ) × CircleVector) ≃ₜ Eucl (e + 2) :=
    (sumCoordinates.trans (reindexReal ((Fintype.equivFin _).trans (Equiv.cast (congrArg Fin hc))))).trans
      (EuclideanSpace.equiv (Fin (e + 2)) ℝ).symm.toHomeomorph
  have hz0 : eqv (0, 0) = 0 := by ext i; simp [eqv, sumCoordinates, reindexReal]
  exact
    { sectionMap := (fun p => (p.1, planeToCone d p.2)) ∘ eqv.symm
      projectionMap := eqv ∘ fun p => (p.1, coneToPlane p.2)
      section_continuous := (continuous_fst.prodMk ((continuous_planeToCone d).comp continuous_snd)).comp eqv.symm.continuous
      projection_continuous := eqv.continuous.comp (continuous_fst.prodMk (continuous_coneToPlane.comp continuous_snd))
      projection_section := fun x => by
        simp [Function.comp_apply, coneToPlane_planeToCone]
      section_zero := by
        rw [Function.comp_apply, eqv.symm_apply_eq.mpr hz0.symm]; exact Prod.ext rfl (planeToCone_zero d)
      projection_zero_iff := fun p => by
        rw [Function.comp_apply, ← hz0, eqv.injective.eq_iff, Prod.ext_iff, coneToPlane_zero_iff, Prod.ext_iff]
        rfl }

theorem cone_not_euclidean (e d : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAt (productZero : ConeSpace (Fin e) (Fin d)) := by
  let d' := Fintype.card (Fin d) - 2
  have hn : ¬ EuclideanAt (productZero : ConeSpace (Fin e) (Fin (d' + 2))) := by
    refine not_euclidean_of_retract_regular_charts (planeProductRetract e d')
      (Fintype.card (Fin e) + Fintype.card (Fin (d' + 2)) + 1) (by simp)
      fun U hU h0 => ?_
    obtain ⟨p, hp, hpc⟩ := exists_gen_regular_in_open (ι := Fin e) 1 (0 : Fin (d' + 2)) U hU h0
    exact ⟨genPivotChart (ι := Fin e) 1 0, p, hp, hpc⟩
  intro hE
  have hκ : 2 ≤ Fintype.card (Fin d) := by simpa using hd
  exact hn (by simpa only [coneCoordinatesExtra_zero] using
    (euclideanAt_homeomorph (coneCoordinatesExtra (ι := Fin e) hκ) productZero).mp hE)

theorem coneProductNonManifold : GS.Specifications.ConeProductNonManifoldGoal := by
  intro d e hd hE
  let S : Set ((Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) := {p | p.2.rank ≤ 1}
  have hz : ((0, 0) : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) ∈ S := by simp [S]
  exact cone_not_euclidean e d (by omega)
    ((euclideanAt_homeomorph (flattenConeProduct (ι := Fin e) (κ := Fin d)) productZero).mpr
      ((euclideanAtSubset_iff S (0, 0) hz).mp hE))

end GS.NonmanifoldTopology
