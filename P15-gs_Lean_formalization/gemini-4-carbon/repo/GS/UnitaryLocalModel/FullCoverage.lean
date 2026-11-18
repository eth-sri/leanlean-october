module

public import GS.UnitaryLocalModel.RankCone
public import GS.UnitaryLocalModel.Dephasing
public import GS.CompactFibres
public import GS.NonmanifoldCompletion.NeighbourhoodModel
public import GS.Continuation.CompactCoverageTools
public import Mathlib.Topology.Order.Compact

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix GS GS.UnitaryManifold GS.UnitaryNonmanifold Set Filter
open scoped BigOperators Topology ComplexOrder

namespace GS.UnitaryLocalModel

abbrev SmallBlockParameters (q : ℕ) := (Fin q → CMat 2) × CMat q × CMat q × (Fin q → CMat 2)

def smallFactorSet (q : ℕ) : Set (SmallBlockParameters q) :=
  {p | (∀ i, GS.Unitary (p.1 i)) ∧ GS.Unitary p.2.1 ∧ GS.Unitary p.2.2.1 ∧ (∀ j, GS.Unitary (p.2.2.2 j))}

def smallFactorMap {q : ℕ} (p : SmallBlockParameters q) : CMat (q * 2) :=
  flattenBlocks (GS.UnitaryNonmanifold.blockMatrix p.1 * centralPair p.2.1 p.2.2.1 * GS.UnitaryNonmanifold.blockMatrix p.2.2.2)

theorem smallFactorMap_block {q : ℕ} (p : SmallBlockParameters q) (i j : Fin q) (a b : Fin 2) :
    smallFactorMap p (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) =
      (p.1 i * diagTwo (p.2.1 i j) (p.2.2.1 i j) * p.2.2.2 j) a b := by
  rw [smallFactorMap, flattenBlocks_apply, small_block_sandwich]

theorem continuous_smallFactorMap (q : ℕ) : Continuous (@smallFactorMap q) := by
  have he : (@smallFactorMap q) = fun p i j =>
      let x : Fin q × Fin 2 := finProdFinEquiv.symm i
      let y : Fin q × Fin 2 := finProdFinEquiv.symm j
      (p.1 x.1 * diagTwo (p.2.1 x.1 y.1) (p.2.2.1 x.1 y.1) * p.2.2.2 y.1) x.2 y.2 :=
    funext fun p => funext fun i => funext fun j => small_block_sandwich _ _ _ _ _ _ _ _
  rw [he]
  have hdiag (i j : Fin q) : Continuous fun p : SmallBlockParameters q => diagTwo (p.2.1 i j) (p.2.2.1 i j) :=
    continuous_pi fun a => continuous_pi fun b => by fin_cases a <;> fin_cases b <;> simp [diagTwo] <;> fun_prop
  fun_prop

theorem isCompact_smallFactorSet (q : ℕ) : IsCompact (smallFactorSet q) := by
  have hu (n : ℕ) : IsCompact {A : CMat n | GS.Unitary A} := by
    simpa [GS.UnitaryGeometry.KSSupported, GS.kUnitary_complex_iff] using
      GS.UnitaryManifold.compact_blockU_set (𝕂 := ℂ) (fun _ : Fin n => 0)
  have ho : IsCompact {U : Fin q → CMat 2 | ∀ i, GS.Unitary (U i)} := isCompact_pi_infinite fun _ => hu 2
  exact ho.prod ((hu q).prod ((hu q).prod ho))

theorem image_smallFactorMap (q : ℕ) : (@smallFactorMap q) '' smallFactorSet q = GS.UnitaryNonmanifold.localFamily q := by
  ext M; exact ⟨fun ⟨⟨U, A, B, V⟩, ⟨hU, hA, hB, hV⟩, h⟩ => h ▸ block_sandwich_mem_localFamily U V A B hU hV hA hB,
    fun hM => let ⟨U, V, A, B, hU, hV, hA, hB, he⟩ := (mem_localFamily_iff_block_sandwich M).mp hM
      ⟨(U, A, B, V), ⟨hU, hA, hB, hV⟩, he.symm⟩⟩

abbrev SmallFactorSpace (q : ℕ) := {p : SmallBlockParameters q // p ∈ smallFactorSet q}

instance smallFactorSpace_compactSpace (q : ℕ) : CompactSpace (SmallFactorSpace q) :=
  isCompact_iff_compactSpace.mp (isCompact_smallFactorSet q)

def smallFactorValue (q : ℕ) (p : SmallFactorSpace q) : CMat (q * 2) := smallFactorMap p.val

theorem continuous_smallFactorValue (q : ℕ) : Continuous (smallFactorValue q) :=
  (continuous_smallFactorMap q).comp continuous_subtype_val

def localEnergy {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ i, x i ^ 2

abbrev LocalParameters (d : ℕ) := (Fin d → ℝ) × (Fin d → ℝ) × AxisVector

def localParameterBox (d : ℕ) (r : ℝ) : Set (LocalParameters d) :=
  {p | localEnergy p.1 ≤ r ^ 2 ∧ localEnergy p.2.1 ≤ r ^ 2 ∧ OnSphere p.2.2}

theorem localEnergy_coordinate_bound {d : ℕ} (x : Fin d → ℝ) (r : ℝ)
    (hx : localEnergy x ≤ r ^ 2) (i : Fin d) : |x i| ≤ |r| := by
  have hi : x i ^ 2 ≤ localEnergy x := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  nlinarith [sq_abs (x i), sq_abs r, abs_nonneg (x i), abs_nonneg r]

theorem isCompact_localParameterBox (d : ℕ) (r : ℝ) : IsCompact (localParameterBox d r) := by
  have hle : Continuous (@localEnergy d) := by unfold localEnergy; fun_prop
  have hcl : IsClosed (localParameterBox d r) :=
    (isClosed_le (hle.comp continuous_fst) continuous_const).inter <|
      (isClosed_le (hle.comp (by fun_prop)) continuous_const).inter <|
        isClosed_eq (show Continuous fun p : LocalParameters d => p.2.2 0 ^ 2 + p.2.2 1 ^ 2 + p.2.2 2 ^ 2 by fun_prop)
          continuous_const
  let lo : LocalParameters d := (fun _ => -|r|, fun _ => -|r|, fun _ => -1)
  let hi : LocalParameters d := (fun _ => |r|, fun _ => |r|, fun _ => 1)
  refine (isCompact_Icc (a := lo) (b := hi)).of_isClosed_subset hcl fun p hp => ?_
  have hc (i) := abs_le.mp (localEnergy_coordinate_bound p.1 r hp.1 i)
  have hz (i) := abs_le.mp (localEnergy_coordinate_bound p.2.1 r hp.2.1 i)
  have hu (i : Fin 3) : |p.2.2 i| ≤ 1 := by
    have hsph : p.2.2 0 ^ 2 + p.2.2 1 ^ 2 + p.2.2 2 ^ 2 = 1 := hp.2.2
    have hs : p.2.2 i ^ 2 ≤ 1 := by
      fin_cases i <;> dsimp <;> nlinarith [sq_nonneg (p.2.2 0), sq_nonneg (p.2.2 1), sq_nonneg (p.2.2 2), hsph]
    nlinarith [sq_abs (p.2.2 i), abs_nonneg (p.2.2 i)]
  exact ⟨⟨fun i => (hc i).1, fun i => (hz i).1, fun i => (abs_le.mp (hu i)).1⟩,
    ⟨fun i => (hc i).2, fun i => (hz i).2, fun i => (abs_le.mp (hu i)).2⟩⟩

abbrev ConeCoordinates (d : ℕ) := (Fin d → ℝ) × {W : Matrix (Fin 3) (Fin d) ℝ // W.rank ≤ 1}

def parameterCone {d : ℕ} (p : LocalParameters d) : ConeCoordinates d :=
  (p.1, ⟨sphereOuter p.2.2 p.2.1, rank_sphereOuter_le_one _ _⟩)

theorem continuous_parameterCone (d : ℕ) : Continuous (@parameterCone d) :=
  continuous_fst.prodMk ((continuous_sphereOuter.comp (continuous_snd.snd.prodMk continuous_snd.fst)).subtype_mk _)

def boundedConeCoordinates (d : ℕ) (r : ℝ) : Set (ConeCoordinates d) :=
  {p | localEnergy p.1 ≤ r ^ 2 ∧ frobSq p.2.val ≤ r ^ 2}

theorem parameterCone_image (d : ℕ) (r : ℝ) : parameterCone '' localParameterBox d r = boundedConeCoordinates d r := by
  ext p; constructor
  · rintro ⟨⟨c, z, u⟩, hp, rfl⟩
    exact ⟨hp.1, by change frobSq (sphereOuter u z) ≤ r ^ 2; rw [frobSq_sphereOuter hp.2.2]; exact hp.2.1⟩
  · rintro ⟨hc, hW⟩
    obtain ⟨u, hu, z, hz⟩ := exists_sphereOuter_of_rank_le_one p.2.val p.2.property
    refine ⟨(p.1, z, u), ⟨hc, by rw [show localEnergy z = frobSq p.2.val by rw [← hz, frobSq_sphereOuter hu]; rfl]; exact hW, hu⟩,
      Prod.ext rfl (Subtype.ext hz)⟩

def coneCoordinatesZero (d : ℕ) : ConeCoordinates d := (0, ⟨0, by simp⟩)

theorem boundedConeCoordinates_mem_nhds (d : ℕ) {r : ℝ} (hr : 0 < r) :
    boundedConeCoordinates d r ∈ 𝓝 (coneCoordinatesZero d) := by
  have hc : Continuous fun p : ConeCoordinates d => localEnergy p.1 := by unfold localEnergy; fun_prop
  have hv : Continuous fun p : ConeCoordinates d => p.2.val := continuous_subtype_val.comp continuous_snd
  have hW : Continuous fun p : ConeCoordinates d => frobSq p.2.val := by
    unfold frobSq frobInner
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (((continuous_apply j).comp ((continuous_apply i).comp hv))).mul
        (((continuous_apply j).comp ((continuous_apply i).comp hv)))
  refine Filter.mem_of_superset (((isOpen_lt hc continuous_const).inter (isOpen_lt hW continuous_const)).mem_nhds ?_)
    fun _ hp => ⟨hp.1.le, hp.2.le⟩
  simp [coneCoordinatesZero, localEnergy, frobSq, frobInner, sq_pos_of_pos hr]

theorem exists_parameterBox_in_chart {d : ℕ} (U : Set (Fin d → ℝ)) (hU : IsOpen U) (h0 : 0 ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ localParameterBox d r, p.1 + p.2.1 ∈ U ∧ p.1 - p.2.1 ∈ U := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  refine ⟨ε / 3, by positivity, fun p hp => ?_⟩
  have hnb (x : Fin d → ℝ) (hx : localEnergy x ≤ (ε / 3) ^ 2) : ‖x‖ ≤ ε / 3 :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ ε / 3 by positivity)] using
        localEnergy_coordinate_bound x (ε / 3) hx i
  have hc := hnb p.1 hp.1; have hz := hnb p.2.1 hp.2.1
  exact ⟨hsub (by rw [Metric.mem_ball, dist_zero_right]; exact (norm_add_le _ _).trans_lt (by linarith)),
         hsub (by rw [Metric.mem_ball, dist_zero_right]; exact (norm_sub_le _ _).trans_lt (by linarith))⟩

abbrev BlockFamily (q : ℕ) := Fin q → Fin q → CMat 2

def flattenBlockFamily {q : ℕ} (N : BlockFamily q) : CMat (q * 2) :=
  fun i j => N (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2

def extractBlockFamily {q : ℕ} (M : CMat (q * 2)) : BlockFamily q :=
  fun i j a b => M (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b))

@[simp] theorem extract_flattenBlockFamily {q : ℕ} (N : BlockFamily q) :
    extractBlockFamily (flattenBlockFamily N) = N := by funext i j a b; simp [extractBlockFamily, flattenBlockFamily]

def blockFamilyHomeomorph (q : ℕ) : BlockFamily q ≃ₜ CMat (q * 2) where
  toFun := flattenBlockFamily
  invFun := extractBlockFamily
  left_inv := extract_flattenBlockFamily
  right_inv M := by
    ext i j
    change M (finProdFinEquiv (finProdFinEquiv.symm i)) (finProdFinEquiv (finProdFinEquiv.symm j)) = M i j
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  continuous_toFun := by unfold flattenBlockFamily; fun_prop
  continuous_invFun := by unfold extractBlockFamily; fun_prop

abbrev OuterFactors (q : ℕ) (o : Fin q) :=
  (Fin q → BlockU (fun _ : Fin 2 => 0)) × ({j : Fin q // j ≠ o} → BlockU (fun _ : Fin 2 => 0))

def outerLeft {q : ℕ} {o : Fin q} (g : OuterFactors q o) (i : Fin q) : CMat 2 := (g.1 i).val
def outerRight {q : ℕ} {o : Fin q} (g : OuterFactors q o) (j : Fin q) : CMat 2 := if h : j = o then 1 else (g.2 ⟨j, h⟩).val

theorem outerLeft_unitary {q : ℕ} {o : Fin q} (g : OuterFactors q o) (i : Fin q) : GS.Unitary (outerLeft g i) :=
  (g.1 i).property.2

theorem outerRight_unitary {q : ℕ} {o : Fin q} (g : OuterFactors q o) (j : Fin q) : GS.Unitary (outerRight g j) := by
  unfold outerRight; split; exacts [GS.Unitary.one, (g.2 _).property.2]

@[simp] theorem outerRight_anchor {q : ℕ} {o : Fin q} (g : OuterFactors q o) : outerRight g o = 1 := by simp [outerRight]

def outerOfMatrices {q : ℕ} {o : Fin q} (L R : Fin q → CMat 2)
    (hL : ∀ i, GS.Unitary (L i)) (hR : ∀ j, GS.Unitary (R j)) : OuterFactors q o :=
  (fun i => ⟨L i, fun _ _ h => (h rfl).elim, hL i⟩, fun j => ⟨R j.val, fun _ _ h => (h rfl).elim, hR j.val⟩)

def chartBlockFamily {q d : ℕ} (ψ : (Fin d → ℝ) → CMat q) (p : LocalParameters d) : BlockFamily q :=
  fun i j => chartMiddle (fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2) p.1 p.2.1 p.2.2 (i, j)

def fullBlockImage {q d : ℕ} {o : Fin q} (ψ : (Fin d → ℝ) → CMat q)
    (g : OuterFactors q o) (p : LocalParameters d) : CMat (q * 2) :=
  flattenBlockFamily fun i j => outerLeft g i * chartBlockFamily ψ p i j * outerRight g j

abbrev FullCompactParameters (q : ℕ) (o : Fin q) (d : ℕ) (r : ℝ) := OuterFactors q o × localParameterBox d r

def fullCompactMiddle {q d : ℕ} (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ)
    (p : FullCompactParameters q o d r) : CMat (q * 2) := fullBlockImage ψ p.1 p.2.val

abbrev FullCompactImage {q d : ℕ} (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ) :=
  Set.range (fullCompactMiddle ψ o r)

instance fullCompactParameters_compactSpace (q : ℕ) (o : Fin q) (d : ℕ) (r : ℝ) :
    CompactSpace (FullCompactParameters q o d r) := by
  letI : CompactSpace (localParameterBox d r) := isCompact_iff_compactSpace.mp (isCompact_localParameterBox d r)
  exact inferInstance

theorem continuous_fullCompactMiddle {q d : ℕ} (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ)) (o : Fin q) (r : ℝ)
    (hψ : ContinuousOn ψ U) (hargs : ∀ p ∈ localParameterBox d r, p.1 + p.2.1 ∈ U ∧ p.1 - p.2.1 ∈ U) :
    Continuous (fullCompactMiddle ψ o r) := by
  have hψ' : ContinuousOn (fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2) U := by
    apply continuousOn_pi.mpr; intro ij
    exact ((continuous_apply ij.2).comp (continuous_apply ij.1)).comp_continuousOn hψ
  have hp : Continuous fun p : localParameterBox d r => (fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2) (p.val.1 + p.val.2.1) :=
    hψ'.comp_continuous (by fun_prop) fun p => (hargs p.val p.property).1
  have hm : Continuous fun p : localParameterBox d r => (fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2) (p.val.1 - p.val.2.1) :=
    hψ'.comp_continuous (by fun_prop) fun p => (hargs p.val p.property).2
  have hmid : Continuous fun p : localParameterBox d r => chartMiddle (fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2) p.val.1 p.val.2.1 p.val.2.2 := by
    unfold chartMiddle middleBlock
    exact continuous_pi fun j =>
      ((((continuous_apply j).comp hp).add ((continuous_apply j).comp hm)).div_const 2 |>.smul continuous_const).add
        (((((continuous_apply j).comp hp).sub ((continuous_apply j).comp hm)).div_const 2).smul (continuous_pauli.comp (by fun_prop)))
  have hoL : Continuous (@outerLeft q o) := by unfold outerLeft; fun_prop
  have hoR : Continuous (@outerRight q o) := continuous_pi fun j => by
    by_cases hj : j = o <;> simp only [outerRight, hj, ↓reduceDIte] <;> fun_prop
  apply (show Continuous (@flattenBlockFamily q) by unfold flattenBlockFamily; fun_prop).comp
  apply continuous_pi; intro i; apply continuous_pi; intro j
  exact continuous_matrix_product
    (continuous_matrix_product (((continuous_apply i).comp hoL).comp continuous_fst)
      (((continuous_apply (i, j)).comp hmid).comp continuous_snd))
    (((continuous_apply j).comp hoR).comp continuous_fst)

def PositiveChartAnchors {q d : ℕ} (Q : CMat q) (o : Fin q) (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ)) : Prop :=
  ∀ x ∈ U, (∀ i, ∃ a : ℝ, 0 < a ∧ ψ x i o / Q i o = a) ∧ (∀ j, ∃ a : ℝ, 0 < a ∧ ψ x o j / Q o j = a)

def fullCompactSource {q d : ℕ} (F : Set (CMat (q * 2))) (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ) : Set F :=
  {M | M.val ∈ FullCompactImage ψ o r}

theorem full_compact_pointed_neighbourhood_model {q d : ℕ}
    (F : Set (CMat (q * 2))) (x : F) (Q : CMat q) (o : Fin q)
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ))
    (hψc : ContinuousOn ψ U) (hψi : Set.InjOn ψ U)
    (hpos : PositiveChartAnchors Q o ψ U) (r : ℝ) (hr : 0 < r)
    (hargs : ∀ p ∈ localParameterBox d r, p.1 + p.2.1 ∈ U ∧ p.1 - p.2.1 ∈ U)
    (hsub : FullCompactImage ψ o r ⊆ F) (hcover : fullCompactSource F ψ o r ∈ 𝓝 x)
    (p₀ : FullCompactParameters q o d r) (hbase : fullCompactMiddle ψ o r p₀ = x.val)
    (hzero : parameterCone p₀.2.val = coneCoordinatesZero d) :
    Nonempty (GS.NonmanifoldCompletion.PointedNeighbourhoodModel F
      (OuterFactors q o × ConeCoordinates d) x (p₀.1, coneCoordinatesZero d)) := by
  let fcCone (p : FullCompactParameters q o d r) : OuterFactors q o × boundedConeCoordinates d r :=
    (p.1, ⟨parameterCone p.2.val, (parameterCone_image d r) ▸ ⟨p.2.val, p.2.property, rfl⟩⟩)
  have hfc_cont : Continuous fcCone :=
    continuous_fst.prodMk (((continuous_parameterCone d).comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _)
  have hfc_surj : Function.Surjective fcCone := fun ⟨g, w⟩ => by
    have hw : w.val ∈ parameterCone '' localParameterBox d r := by
      simpa only [parameterCone_image] using w.property
    obtain ⟨p, hp, he⟩ := hw
    exact ⟨(g, ⟨p, hp⟩), Prod.ext rfl (Subtype.ext he)⟩
  have hfib (p p' : FullCompactParameters q o d r) :
      fullCompactMiddle ψ o r p = fullCompactMiddle ψ o r p' ↔ fcCone p = fcCone p' := by
    have hψ' : Set.InjOn (fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2) U :=
      fun a ha b hb he => hψi ha hb (funext fun i => funext fun j => congrFun he (i, j))
    have hcpos (q₀ : LocalParameters d) (hq₀ : q₀ ∈ localParameterBox d r) :
        NormalizedPositiveAnchors Q o (chartBlockFamily ψ q₀) :=
      ⟨fun i => middleBlock_ratio_posDef _ _ _ _ hq₀.2.2 ((hpos _ (hargs _ hq₀).1).1 i) ((hpos _ (hargs _ hq₀).2).1 i),
       fun j => middleBlock_ratio_posDef _ _ _ _ hq₀.2.2 ((hpos _ (hargs _ hq₀).1).2 j) ((hpos _ (hargs _ hq₀).2).2 j)⟩
    have hh := normalized_chart_fibres_on Q o (fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2) U hψ'
      (outerLeft p.1) (outerRight p.1) (outerLeft p'.1) (outerRight p'.1)
      p.2.val.1 p.2.val.2.1 p'.2.val.1 p'.2.val.2.1 p.2.val.2.2 p'.2.val.2.2
      (outerLeft_unitary p.1) (outerRight_unitary p.1) (outerLeft_unitary p'.1) (outerRight_unitary p'.1)
      (outerRight_anchor p.1) (outerRight_anchor p'.1)
      (hargs _ p.2.property).1 (hargs _ p.2.property).2 (hargs _ p'.2.property).1 (hargs _ p'.2.property).2
      p.2.property.2.2 p'.2.property.2.2 (hcpos _ p.2.property) (hcpos _ p'.2.property)
    have hflat : fullCompactMiddle ψ o r p = fullCompactMiddle ψ o r p' ↔
        normalizedBlockImage (outerLeft p.1) (outerRight p.1) (chartBlockFamily ψ p.2.val) =
          normalizedBlockImage (outerLeft p'.1) (outerRight p'.1) (chartBlockFamily ψ p'.2.val) :=
      ⟨fun he => by
          have he' := congrArg (@extractBlockFamily q) he
          unfold normalizedBlockImage
          simpa only [fullCompactMiddle, fullBlockImage, extract_flattenBlockFamily, normalizedBlockImage] using he',
       congrArg (@flattenBlockFamily q)⟩
    rw [hflat, show normalizedBlockImage (outerLeft p.1) (outerRight p.1) (chartBlockFamily ψ p.2.val) =
        normalizedBlockImage (outerLeft p'.1) (outerRight p'.1) (chartBlockFamily ψ p'.2.val) ↔ _ from hh]
    simp only [fcCone, parameterCone, Prod.mk.injEq, Subtype.mk.injEq]
    refine ⟨fun ⟨hL, hR, hc, hz⟩ => ⟨Prod.ext (funext fun i => Subtype.ext (congrFun hL i))
      (funext fun j => Subtype.ext (by simpa [outerRight, j.property] using congrFun hR j.val)), hc, hz⟩,
      fun ⟨hg, hc, hz⟩ => ⟨congrArg outerLeft hg, congrArg outerRight hg, hc, hz⟩⟩
  obtain ⟨h, hh⟩ := exists_homeomorph_ranges_of_same_fibres (fullCompactMiddle ψ o r) fcCone
    (continuous_fullCompactMiddle ψ U o r hψc hargs) hfc_cont hfib
  let eSrc : fullCompactSource F ψ o r ≃ₜ FullCompactImage ψ o r :=
    { toFun := fun y => ⟨y.val.val, y.property⟩, invFun := fun y => ⟨⟨y.val, hsub y.property⟩, y.property⟩
      left_inv := fun _ => rfl, right_inv := fun _ => rfl
      continuous_toFun := by fun_prop, continuous_invFun := by fun_prop }
  let eRng : Set.range fcCone ≃ₜ (OuterFactors q o × boundedConeCoordinates d r) :=
    { toFun := Subtype.val, invFun := fun y => ⟨y, hfc_surj y⟩
      left_inv := fun _ => rfl, right_inv := fun _ => rfl
      continuous_toFun := continuous_subtype_val, continuous_invFun := continuous_id.subtype_mk _ }
  let tgt : Set (OuterFactors q o × ConeCoordinates d) := {p | p.2 ∈ boundedConeCoordinates d r}
  let eTgt : (OuterFactors q o × boundedConeCoordinates d r) ≃ₜ tgt :=
    { toFun := fun p => ⟨(p.1, p.2.val), p.2.property⟩, invFun := fun p => (p.val.1, ⟨p.val.2, p.property⟩)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl
      continuous_toFun := by fun_prop, continuous_invFun := by fun_prop }
  refine ⟨{
    source := fullCompactSource F ψ o r
    target := tgt
    source_nhds := hcover
    target_nhds := continuous_snd.continuousAt.preimage_mem_nhds (boundedConeCoordinates_mem_nhds d hr)
    chart := ((eSrc.trans h).trans eRng).trans eTgt
    map_point := fun hx => by
      have he : eSrc ⟨x, hx⟩ = ⟨fullCompactMiddle ψ o r p₀, ⟨p₀, rfl⟩⟩ := Subtype.ext hbase.symm
      change (eTgt (eRng (h (eSrc ⟨x, hx⟩)))).val = _
      rw [he, hh p₀]; exact Prod.ext rfl hzero }⟩

def scalarBlockBase {q : ℕ} (Q : CMat q) : CMat (q * 2) :=
  flattenBlockFamily fun i j => Q i j • (1 : CMat 2)

def identityOuter (q : ℕ) (o : Fin q) : OuterFactors q o := (fun _ => 1, fun _ => 1)

def parameterZero (d : ℕ) : LocalParameters d := (0, 0, ![1, 0, 0])

theorem parameterZero_mem (d : ℕ) (r : ℝ) : parameterZero d ∈ localParameterBox d r := by
  simp [parameterZero, localParameterBox, localEnergy, OnSphere, sq_nonneg]

@[simp] theorem parameterCone_zero (d : ℕ) : parameterCone (parameterZero d) = coneCoordinatesZero d :=
  Prod.ext rfl (Subtype.ext (by ext i j; simp [parameterCone, parameterZero, coneCoordinatesZero, sphereOuter]))

def fullParameterZero (q d : ℕ) (o : Fin q) (r : ℝ) : FullCompactParameters q o d r :=
  (identityOuter q o, ⟨parameterZero d, parameterZero_mem d r⟩)

@[simp] theorem fullCompactMiddle_zero {q d : ℕ} (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ) :
    fullCompactMiddle ψ o r (fullParameterZero q d o r) = scalarBlockBase (ψ 0) := by
  have hir (j : Fin q) : outerRight (identityOuter q o) j = 1 := by unfold outerRight identityOuter; split <;> rfl
  have hil (i : Fin q) : outerLeft (identityOuter q o) i = 1 := rfl
  unfold fullCompactMiddle fullBlockImage scalarBlockBase
  exact congrArg (@flattenBlockFamily q) (funext fun i => funext fun j => by
    simp [fullParameterZero, hil, hir, chartBlockFamily, chartMiddle, parameterZero, middleBlock_equal])

theorem fullBlockImage_mem_localFamily {q d : ℕ} {o : Fin q} (ψ : (Fin d → ℝ) → CMat q)
    (g : OuterFactors q o) (p : LocalParameters d)
    (hp : GS.Unitary (ψ (p.1 + p.2.1))) (hm : GS.Unitary (ψ (p.1 - p.2.1))) (hu : OnSphere p.2.2) :
    fullBlockImage ψ g p ∈ GS.UnitaryNonmanifold.localFamily q := by
  obtain ⟨S, hS, hdiag⟩ := middleBlock_unitary_diagonalization p.2.2 hu
  let v : SmallBlockParameters q := (fun i => outerLeft g i * Sᴴ, ψ (p.1 + p.2.1), ψ (p.1 - p.2.1), fun j => S * outerRight g j)
  have hv : v ∈ smallFactorSet q :=
    ⟨fun i => (outerLeft_unitary g i).mul hS.conjTranspose, hp, hm, fun j => hS.mul (outerRight_unitary g j)⟩
  have he : smallFactorMap v = fullBlockImage ψ g p := by
    apply (blockFamilyHomeomorph q).symm.injective
    change extractBlockFamily (smallFactorMap v) = extractBlockFamily (fullBlockImage ψ g p)
    unfold fullBlockImage; rw [extract_flattenBlockFamily]
    funext i j a b
    change smallFactorMap v (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) = _
    rw [smallFactorMap_block]
    change ((outerLeft g i * Sᴴ) * diagTwo (ψ (p.1 + p.2.1) i j) (ψ (p.1 - p.2.1) i j) * (S * outerRight g j)) a b =
      (outerLeft g i * middleBlock (ψ (p.1 + p.2.1) i j) (ψ (p.1 - p.2.1) i j) p.2.2 * outerRight g j) a b
    rw [← hdiag]; simp only [Matrix.mul_assoc]
  rw [← he, ← image_smallFactorMap]; exact ⟨v, hv, rfl⟩

theorem fullCompactImage_subset_localFamily {q d : ℕ} (ψ : (Fin d → ℝ) → CMat q) (o : Fin q)
    (U : Set (Fin d → ℝ)) (hψ : ∀ x ∈ U, GS.Unitary (ψ x)) (r : ℝ)
    (hargs : ∀ p ∈ localParameterBox d r, p.1 + p.2.1 ∈ U ∧ p.1 - p.2.1 ∈ U) :
    FullCompactImage ψ o r ⊆ GS.UnitaryNonmanifold.localFamily q := by
  rintro _ ⟨p, rfl⟩
  exact fullBlockImage_mem_localFamily ψ p.1 p.2.val (hψ _ (hargs _ p.2.property).1) (hψ _ (hargs _ p.2.property).2) p.2.property.2.2

theorem scalarBlockBase_mem_localFamily {q : ℕ} (Q : CMat q) (hQ : GS.Unitary Q) (o : Fin q) :
    scalarBlockBase Q ∈ GS.UnitaryNonmanifold.localFamily q := by
  have he : fullBlockImage (d := 0) (fun _ => Q) (identityOuter q o) (parameterZero 0) = scalarBlockBase Q :=
    fullCompactMiddle_zero (d := 0) (fun _ => Q) o 0
  exact he ▸ fullBlockImage_mem_localFamily (d := 0) (fun _ => Q) (identityOuter q o) (parameterZero 0) hQ hQ
    (by simp [parameterZero, OnSphere])

def anchorFactorSet {q : ℕ} (Q : FullUnitary q) (o : Fin q) : Set (SmallFactorSpace q) :=
  {p | AnchorNonzero Q.val p.val.2.1 o ∧ AnchorNonzero Q.val p.val.2.2.1 o}

def dephasedFirst {q : ℕ} (Q : FullUnitary q) (o : Fin q) (p : anchorFactorSet Q o) : DephasedUnitary Q o :=
  ⟨fullUnitary (dephase Q.val p.val.val.2.1 o) (dephase_unitary p.val.property.2.1 p.property.1),
    (dephased_constraints_iff _ _ _).mpr ⟨dephase_anchor_column_positive p.property.1, dephase_anchor_row_positive p.property.1⟩⟩

def dephasedSecond {q : ℕ} (Q : FullUnitary q) (o : Fin q) (p : anchorFactorSet Q o) : DephasedUnitary Q o :=
  ⟨fullUnitary (dephase Q.val p.val.val.2.2.1 o) (dephase_unitary p.val.property.2.2.1 p.property.2),
    (dephased_constraints_iff _ _ _).mpr ⟨dephase_anchor_column_positive p.property.2, dephase_anchor_row_positive p.property.2⟩⟩

def smallDephasedSource {q : ℕ} (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) :
    Set (DephasedUnitary Q o) :=
  {A | A ∈ dephasedChartSource Q o hQ ∧ localEnergy (euclideanDephasedCoordinates Q o hQ A) < r ^ 2}

def smallFullFactors {q : ℕ} (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) :
    Set (SmallFactorSpace q) :=
  Subtype.val '' {p : anchorFactorSet Q o |
    dephasedFirst Q o p ∈ smallDephasedSource Q o hQ r ∧ dephasedSecond Q o p ∈ smallDephasedSource Q o hQ r}

theorem exists_open_full_compact_coverage {q : ℕ} (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) (hr : 0 < r) :
    ∃ W : Set (CMat (q * 2)), IsOpen W ∧ scalarBlockBase Q.val ∈ W ∧
      ∀ M ∈ GS.UnitaryNonmanifold.localFamily q, M ∈ W →
        M ∈ FullCompactImage (euclideanDephasedParametrization Q o hQ) o r := by
  have hsds_open : IsOpen (smallDephasedSource Q o hQ r) := by
    have hc : Continuous fun A : dephasedChartSource Q o hQ => euclideanDephasedCoordinates Q o hQ A.val :=
      (dephasedCoordinateEquiv Q o hQ).continuous.comp
        (((unitaryConstraintChart Q o hQ).continuousOn.comp_continuous
          (continuous_subtype_val.comp continuous_subtype_val) fun x => x.property).snd)
    have hle : Continuous (@localEnergy ((q - 1) ^ 2)) := by unfold localEnergy; fun_prop
    have he : smallDephasedSource Q o hQ r = Subtype.val ''
        {A : dephasedChartSource Q o hQ | localEnergy (euclideanDephasedCoordinates Q o hQ A.val) < r ^ 2} := by
      ext A; exact ⟨fun ⟨hA, h⟩ => ⟨⟨A, hA⟩, h, rfl⟩, fun ⟨A, h, heq⟩ => heq ▸ ⟨A.property, h⟩⟩
    rw [he]; exact (dephasedChartSource_open Q o hQ).isOpenMap_subtype_val _ (isOpen_lt (hle.comp hc) continuous_const)
  have haf_open : IsOpen (anchorFactorSet Q o) :=
    ((isOpen_anchorNonzero Q.val o).preimage (by fun_prop)).inter ((isOpen_anchorNonzero Q.val o).preimage (by fun_prop))
  have hdf1 : Continuous (dephasedFirst Q o) :=
    ((continuous_iff_continuousAt.mpr fun p => ContinuousAt.comp (f := fun p : anchorFactorSet Q o => p.val.val.2.1)
      (continuousAt_dephase p.property.1) (by fun_prop)).subtype_mk _).subtype_mk _
  have hdf2 : Continuous (dephasedSecond Q o) :=
    ((continuous_iff_continuousAt.mpr fun p => ContinuousAt.comp (f := fun p : anchorFactorSet Q o => p.val.val.2.2.1)
      (continuousAt_dephase p.property.2) (by fun_prop)).subtype_mk _).subtype_mk _
  have hsff_open : IsOpen (smallFullFactors Q o hQ r) :=
    haf_open.isOpenMap_subtype_val _ ((hsds_open.preimage hdf1).inter (hsds_open.preimage hdf2))
  have hbase_s : dephasedBase Q o hQ ∈ smallDephasedSource Q o hQ r :=
    ⟨base_mem_unitaryConstraintChart_source Q o hQ, by
      simpa [euclideanDephasedCoordinates, dephasedCoordinates, dephasedBase, unitaryConstraintChart_base, localEnergy]
        using sq_pos_of_pos hr⟩
  obtain ⟨W, hW, hbase, hcover⟩ := GS.Continuation.compact_full_fibre_neighbourhood
    (smallFactorValue q) (continuous_smallFactorValue q) Set.univ isCompact_univ
    (smallFullFactors Q o hQ r) hsff_open (scalarBlockBase Q.val) fun p _ he => by
      have hb (i j) : p.val.1 i * diagTwo (p.val.2.1 i j) (p.val.2.2.1 i j) * p.val.2.2.2 j = Q.val i j • (1 : CMat 2) := by
        have hv : extractBlockFamily (smallFactorValue q p) = fun i j =>
            p.val.1 i * diagTwo (p.val.2.1 i j) (p.val.2.2.1 i j) * p.val.2.2.2 j :=
          funext fun i => funext fun j => funext fun a => funext fun b => smallFactorMap_block p.val i j a b
        have hh := congrArg (@extractBlockFamily q) he
        rw [hv, scalarBlockBase, extract_flattenBlockFamily] at hh; exact congrFun (congrFun hh i) j
      obtain ⟨ha, hd1, hd2⟩ := base_fibre_anchor_and_dephase p.val.1 p.val.2.2.2 Q.val p.val.2.1 p.val.2.2.1 o
        p.property.1 p.property.2.2.2 (fun i => (hQ.1 i).1) (fun j => (hQ.2 j).1) hb
      refine ⟨⟨p, ha⟩, ⟨?_, ?_⟩, rfl⟩
      · rwa [show dephasedFirst Q o ⟨p, ha⟩ = dephasedBase Q o hQ from Subtype.ext (Subtype.ext hd1)]
      · rwa [show dephasedSecond Q o ⟨p, ha⟩ = dephasedBase Q o hQ from Subtype.ext (Subtype.ext hd2)]
  refine ⟨W, hW, hbase, fun M hM hMW => ?_⟩
  have himg : M ∈ smallFactorValue q '' Set.univ := by
    obtain ⟨p, hp, rfl⟩ := (image_smallFactorMap q).symm ▸ hM
    exact ⟨⟨p, hp⟩, trivial, rfl⟩
  obtain ⟨_, ⟨_, ⟨p, hp, rfl⟩⟩, rfl⟩ := hcover M hMW himg
  let a := euclideanDephasedCoordinates Q o hQ (dephasedFirst Q o p)
  let b := euclideanDephasedCoordinates Q o hQ (dephasedSecond Q o p)
  let c : Fin ((q - 1) ^ 2) → ℝ := fun i => (a i + b i) / 2
  let z : Fin ((q - 1) ^ 2) → ℝ := fun i => (a i - b i) / 2
  have hc : localEnergy c ≤ r ^ 2 := by
    have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      show ((a i + b i) / 2) ^ 2 ≤ (a i ^ 2 + b i ^ 2) / 2 by nlinarith [sq_nonneg (a i - b i)]
    have hm : localEnergy c ≤ (localEnergy a + localEnergy b) / 2 := by
      simpa only [localEnergy, c, ← Finset.sum_div, Finset.sum_add_distrib] using h
    linarith [hp.1.2, hp.2.2]
  have hz : localEnergy z ≤ r ^ 2 := by
    have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      show ((a i - b i) / 2) ^ 2 ≤ (a i ^ 2 + b i ^ 2) / 2 by nlinarith [sq_nonneg (a i + b i)]
    have hm : localEnergy z ≤ (localEnergy a + localEnergy b) / 2 := by
      simpa only [localEnergy, z, ← Finset.sum_div, Finset.sum_add_distrib] using h
    linarith [hp.1.2, hp.2.2]
  have hea := euclideanDephasedParametrization_coordinates Q o hQ (dephasedFirst Q o p) hp.1.1
  have heb := euclideanDephasedParametrization_coordinates Q o hQ (dephasedSecond Q o p) hp.2.1
  let U := p.val.val.1; let V := p.val.val.2.2.2; let A := p.val.val.2.1; let B := p.val.val.2.2.1
  have hU := p.val.property.1; have hV := p.val.property.2.2.2
  let L := phaseGaugeLeft U V Q.val A B o; let R := phaseGaugeRight V Q.val A B o
  have hL := phaseGaugeLeft_unitary U V Q.val A B o hU hV p.property.1 p.property.2
  have hR := phaseGaugeRight_unitary V Q.val A B o hV p.property.1 p.property.2
  have hRo := phaseGaugeRight_anchor V Q.val A B o (hV o) p.property.1 p.property.2
  obtain ⟨u, hu, hdiag⟩ := exists_axis_of_unitary (V o) (hV o)
  let g : OuterFactors q o := outerOfMatrices L R hL hR
  refine ⟨(g, ⟨(c, z, u), hc, hz, hu⟩), (blockFamilyHomeomorph q).symm.injective ?_⟩
  change extractBlockFamily (fullCompactMiddle _ o r _) = extractBlockFamily (smallFactorValue q p.val)
  rw [fullCompactMiddle, fullBlockImage, extract_flattenBlockFamily]
  funext i j
  have hright : outerRight g = R := funext fun k => by
    by_cases hk : k = o
    · subst hk; simp only [outerRight, ↓reduceDIte]; exact hRo.symm
    · simp [outerRight, hk, g, outerOfMatrices]
  rw [show outerLeft g = L from rfl, hright]
  have hmid : chartBlockFamily (euclideanDephasedParametrization Q o hQ) (c, z, u) i j =
      middleBlock (dephase Q.val A o i j) (dephase Q.val B o i j) u := by
    change middleBlock (euclideanDephasedParametrization Q o hQ (c + z) i j)
      (euclideanDephasedParametrization Q o hQ (c - z) i j) u = _
    rw [show c + z = a by ext k; dsimp [c, z]; ring, show c - z = b by ext k; dsimp [c, z]; ring, hea, heb]; rfl
  rw [hmid]
  have he : L i * middleBlock (dephase Q.val A o i j) (dephase Q.val B o i j) u * R j =
      U i * diagTwo (A i j) (B i j) * V j := by
    rw [← hdiag, ← phase_normalization_block U V Q.val A B o i j (hU i) (hV j)]
    calc _ = (L i * (L i)ᴴ) * (U i * diagTwo (A i j) (B i j) * V j) * ((R j)ᴴ * R j) := by
          dsimp only [L, R]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [(hL i).2, (hR j).1]; simp
  rw [he]; ext k l; exact (smallFactorMap_block p.val.val i j k l).symm

end GS.UnitaryLocalModel
