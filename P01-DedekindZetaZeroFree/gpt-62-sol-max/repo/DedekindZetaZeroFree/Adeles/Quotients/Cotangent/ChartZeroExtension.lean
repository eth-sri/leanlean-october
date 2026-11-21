module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.ChartRestriction

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentChartZeroExtension

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualCotangentCountableShrinking
open KPContActualCotangentMeasurableFamilies
open KPContActualCotangentIntrinsicHilbertIntegral
open KPContActualCotangentPieceHilbertSum
open KPContActualCotangentChartRestriction
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentActualOverlap
open KPContCotangentOverlapRationalBranches

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (cover : CountableCover F ζ hζ U R P H)
variable (a : ShrunkChart F ζ hζ U R P H)

def PointwiseEquivariant (f : a.domain → E F) : Prop :=
  ∀ (γ : Gamma a) (y : a.domain),
    f (actualActionEquiv a γ y) = actualTensor a γ y (f y)

private theorem q_coordinates_ext (y : a.domain) :
    KPContCotangentOverlapRationalBranches.q a (coordinates a y).val = a.toBase y := by
  have hi : ∀ z : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
    intro z; funext k; simp [labeledA, labeledAInv]
  simp only [ShrunkChart.toBase, KPContCotangentOverlapRationalBranches.q,
    coordinates, Subtype.coe_mk]
  rw [hi]

 def directEnumeration (b a : ShrunkChart F ζ hζ U R P H) :
    KPContCotangentCorrectedNullEquivalence.NonsingularEnumeration2 b a :=
  KPContCotangentCorrectedNullEquivalence.withNonsingularity2
    (Classical.choice (enumeration_exists b a))

 theorem directDomainExists (b a : ShrunkChart F ζ hζ U R P H) (x : omega b)
    (h : q b x.val ∈ a.baseDomain) :
    ∃ k, x.val ∈ ((directEnumeration b a).branch k).domain := by
  have hm : x.val ∈ ⋃ k, ((directEnumeration b a).branch k).domain := by
    rw [(directEnumeration b a).covers]
    grind
  exact Set.mem_iUnion.mp hm

def extendedFields (f : a.domain → E F) : ChartFields F ζ hζ U R P H :=
  fun b x =>
    if h : q b x.val ∈ a.baseDomain then
      let k := Nat.find (directDomainExists b a x h)
      let e := (directEnumeration b a).branch k
      let he : x.val ∈ e.domain := Nat.find_spec (directDomainExists b a x h)
      let y : omega a := ⟨e.psi x.val,
        ((directEnumeration b a).properties k).target_subset ⟨x.val, he, rfl⟩⟩
      (e.transport x.val he).symm
        (f (KPContActualCotangentPieceReconstruction.originalPoint a y))
    else 0

private theorem originalPoint_coordinates_ext (y : a.domain) :
    KPContActualCotangentPieceReconstruction.originalPoint a (coordinates a y) = y := by
  apply Subtype.ext
  funext k
  simp [KPContActualCotangentPieceReconstruction.originalPoint, coordinates, labeledA, labeledAInv]

private theorem coordinates_originalPoint_ext (x : omega a) :
    coordinates a (KPContActualCotangentPieceReconstruction.originalPoint a x) = x := by
  apply Subtype.ext
  simp [KPContActualCotangentPieceReconstruction.originalPoint, coordinates, labeledA, labeledAInv]

 def localAmbient (f : a.domain → E F) (x : M F) : E F :=
  if hx : x ∈ omega a then
    f (KPContActualCotangentPieceReconstruction.originalPoint a ⟨x, hx⟩) else 0

private theorem localAmbient_covariant (f : a.domain → E F)
    (he : PointwiseEquivariant a f) (γ : Gamma a) (x : M F) (hx : x ∈ omega a) :
    localAmbient a f ((isotropyArrow a γ).psi x) =
      T (isotropyArrow a γ) x
        (KPContActualCotangentMeasurableFamilies.omega_subset_larger a hx) (localAmbient a f x) := by
  let y := KPContActualCotangentPieceReconstruction.originalPoint a ⟨x, hx⟩
  have hxy : coordinates a y = ⟨x, hx⟩ := coordinates_originalPoint_ext a ⟨x, hx⟩
  have hact : KPContActualCotangentPieceReconstruction.originalPoint a
      ⟨(isotropyArrow a γ).psi x, isotropy_mem a γ x hx⟩ = actualActionEquiv a γ y := by
    apply_fun coordinates a
    · rw [coordinates_originalPoint_ext]
      apply Subtype.ext
      rw [coordinates_action, hxy]
    · intro u v huv
      simpa only [originalPoint_coordinates_ext] using
        congrArg (KPContActualCotangentPieceReconstruction.originalPoint a) huv
  simp only [localAmbient, dite_eq_left hx, dite_eq_left (isotropy_mem a γ x hx)]
  rw [hact, he γ y]
  simp only [actualTensor, hxy]
  rfl

 def sourceCover : CountableCover F ζ hζ U R P H :=
  let c := Classical.choice (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  { chart := fun n => match n with | 0 => a | k+1 => c.chart k
    properties := fun n => match n with
      | 0 => every_shrunkChart_properties F ζ hζ U R P H a
      | k+1 => c.properties k
    covers := by
      apply Set.Subset.antisymm (Set.subset_univ _)
      intro z hz
      have hz' : z ∈ ⋃ n, (c.chart n).baseDomain := by rw [c.covers]; exact hz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz'
      exact Set.mem_iUnion.mpr ⟨n+1, hn⟩ }

 def sourceSequence (f : a.domain → E F) : ℕ → M F → E F
  | 0 => localAmbient a f
  | _+1 => fun _ => 0

private theorem source_transport (f : a.domain → E F) (he : PointwiseEquivariant a f) :
    KPContActualCotangentTransportChoiceAlgebra.Properties (sourceCover a) (sourceSequence a f) := by
  apply kp_cont_actual_cotangent_transport_choice_algebra F ζ hζ
    R.adelicHaar R.adelic_isHaar U R rfl P H
  intro n γ x hx
  cases n with
  | zero => exact localAmbient_covariant a f he γ x hx
  | succ n => exact (map_zero _).symm

 lemma q_actualBranch {a b : ShrunkChart F ζ hζ U R P H}
    (e : ActualBranch a b) (x : M F) : q b (e.arrow.psi x) = q a x := by
  rcases a with ⟨i, ca, oa, da, dao, dac, das, dai⟩
  rcases b with ⟨j, cb, ob, db, dbo, dbc, dbs, dbi⟩
  rcases e with ⟨h, e, hs, ht, hl⟩
  dsimp at h
  subst j
  unfold KPContCotangentOverlapRationalBranches.q
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i))
  simp only [Arrow.psi, coordinateMap, targetChart, isotropyChart,
    ChartKind.representative, inv_one, one_mul, mul_one]
  have ha (v : KPCuspGenuineMonodromy.SymmetricSpace F) :
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) v) = v := by
    funext k
    simp [labeledA, labeledAInv]
  rw [ha]
  apply Quotient.sound
  exact ⟨e.gamma, rfl⟩

private theorem extendedFields_at_branch (f : a.domain → E F)
    (he : PointwiseEquivariant a f) (b : ShrunkChart F ζ hζ U R P H)
    (e : ActualBranch b a) (x : omega b) (hx : x.val ∈ e.arrow.domain) :
    extendedFields a f b x =
      KPContActualCotangentTransportChoiceAlgebra.inverseTransport (some e) (localAmbient a f) x.val hx := by
  have hbase : q b x.val ∈ a.baseDomain := by
    rw [← q_actualBranch e x.val]
    let y : omega a := ⟨e.arrow.psi x.val, e.target_shrinking hx⟩
    have hq := q_coordinates_ext a (KPContActualCotangentPieceReconstruction.originalPoint a y)
    rw [coordinates_originalPoint_ext] at hq
    rw [hq]
    exact Set.mem_range_self _
  simp only [extendedFields, dite_eq_left hbase]
  let k := Nat.find (directDomainExists b a x hbase)
  let d := (directEnumeration b a).branch k
  have hd : x.val ∈ d.domain := Nat.find_spec (directDomainExists b a x hbase)
  have ht : d.psi x.val ∈ omega a :=
    ((directEnumeration b a).properties k).target_subset ⟨x.val, hd, rfl⟩
  change (d.transport x.val hd).symm
    (f (KPContActualCotangentPieceReconstruction.originalPoint a ⟨d.psi x.val, ht⟩)) = _
  have hc := (source_transport a f he).choice_independent b 0 d (some e) x.val hd hx
  change (d.transport x.val hd).symm (localAmbient a f (d.psi x.val)) = _ at hc
  rw [localAmbient, dite_eq_left ht] at hc
  exact hc

 theorem continuous_labeledA_placeEquiv : Continuous (labeledA (placeEquiv F ζ hζ)) :=
  labeledA_continuous (placeEquiv F ζ hζ)

 def identityBranch (a : ShrunkChart F ζ hζ U R P H) : ActualBranch a a where
  component_eq := rfl
  arrow := { KPContCotangentActualOverlap.identity (isotropyChart a) with
    domain := omega a
    isOpen_domain := continuous_labeledA_placeEquiv.isOpen_preimage _ a.domain_open
    source := KPContActualCotangentMeasurableFamilies.omega_subset_larger a
    target := by
      intro x hx
      change (KPContCotangentActualOverlap.identity (isotropyChart a)).psi x ∈ (isotropyChart a).omega
      rw [KPContCotangentActualGroupoidIdentities.identity_psi]
      exact KPContActualCotangentMeasurableFamilies.omega_subset_larger a hx }
  source_shrinking := Set.Subset.refl _
  target_shrinking := by
    intro x hx
    change (KPContCotangentActualOverlap.identity (isotropyChart a)).psi x ∈ omega a
    rwa [KPContCotangentActualGroupoidIdentities.identity_psi]
  target_larger := by
    intro x hx
    change (KPContCotangentActualOverlap.identity (isotropyChart a)).psi x ∈ (isotropyChart a).omega
    rw [KPContCotangentActualGroupoidIdentities.identity_psi]
    exact KPContActualCotangentMeasurableFamilies.omega_subset_larger a hx

theorem extendedFields_source (f : a.domain → E F)
    (hf : Measurable f) (he : PointwiseEquivariant a f) (y : a.domain) :
    extendedFields a f a (coordinates a y) = f y := by
  rw [extendedFields_at_branch a f he a (identityBranch a) (coordinates a y)
    (coordinates a y).property]
  change (T (identityBranch a).arrow (coordinates a y).val (coordinates a y).property).symm
    (localAmbient a f ((identityBranch a).arrow.psi (coordinates a y).val)) = _
  have hpsi : (identityBranch a).arrow.psi = (identity (isotropyChart a)).psi := rfl
  rw [hpsi, KPContCotangentActualGroupoidIdentities.identity_psi]
  have hT : T (identityBranch a).arrow (coordinates a y).val (coordinates a y).property =
      T (identity (isotropyChart a)) (coordinates a y).val
        (KPContActualCotangentMeasurableFamilies.omega_subset_larger a (coordinates a y).property) := by
    apply LinearIsometryEquiv.ext
    intro v
    rfl
  rw [hT, T_identity]
  change localAmbient a f (coordinates a y).val = f y
  rw [localAmbient, dite_eq_left (coordinates a y).property, originalPoint_coordinates_ext]

theorem extendedFields_overlap (f : a.domain → E F)
    (hf : Measurable f) (he : PointwiseEquivariant a f)
    (b : ShrunkChart F ζ hζ U R P H) (e : ActualBranch b a)
    (x : M F) (hx : x ∈ e.arrow.domain) :
    extendedFields a f b ⟨x, e.source_shrinking hx⟩ =
      (T e.arrow x hx).symm
        (f (KPContActualCotangentPieceReconstruction.originalPoint a
          ⟨e.arrow.psi x, e.target_shrinking hx⟩)) := by
  rw [extendedFields_at_branch a f he b e ⟨x, e.source_shrinking hx⟩ hx]
  dsimp only [KPContActualCotangentTransportChoiceAlgebra.inverseTransport,
    Branch.transport, Branch.psi]
  rw [localAmbient, dite_eq_left (e.target_shrinking hx)]

theorem extendedFields_zero_off (f : a.domain → E F)
    (b : ShrunkChart F ζ hζ U R P H) (x : omega b)
    (hx : KPContCotangentOverlapRationalBranches.q b x.val ∉ a.baseDomain) :
    extendedFields a f b x = 0 := by
  simp only [extendedFields]
  exact dite_eq_right hx

 lemma measurable_q (a : ShrunkChart F ζ hζ U R P H) : Measurable (q a) :=
  (KPContCotangentOverlapRationalBranches.continuous_chartProjection a).measurable

private lemma T_apply_twisted {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H) i}
    (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain) (v : E F) :
    T ψ x hx v = twistedOperator ψ x v :=
  congrArg (fun (f : E F →L[ℂ] E F) => f v) (T_toContinuousLinearMap ψ x hx)

private lemma T_symm_coord {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H) i}
    (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain) (w : E F)
    (k : Fin (d F) × Fin 3) :
    (T ψ x hx).symm w k =
      inner ℂ (twistedOperator ψ x (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k)) w := by
  have hb : T ψ x hx (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k)
      = twistedOperator ψ x (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k) :=
    T_apply_twisted ψ x hx _
  have h1 : (T ψ x hx).symm w k
      = inner ℂ ((EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k)) ((T ψ x hx).symm w) := by
    simpa using (EuclideanSpace.basisFun_inner (ι := Fin (d F) × Fin 3) (𝕜 := ℂ)
      ((T ψ x hx).symm w) k).symm
  rw [h1, ← inner_conj_symm]
  conv_lhs =>
    rw [← (T ψ x hx).symm_apply_apply (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k),
      LinearIsometryEquiv.inner_map_map (T ψ x hx).symm w
        (T ψ x hx (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k))]
  rw [inner_conj_symm, hb]

private theorem continuous_originalPoint_ext :
    Continuous (KPContActualCotangentPieceReconstruction.originalPoint a) := by
  exact continuous_labeledA_placeEquiv.comp continuous_subtype_val |>.subtype_mk _

private theorem measurable_localAmbient (f : a.domain → E F) (hf : Measurable f) :
    Measurable (localAmbient a f) := by
  exact Measurable.dite (hf.comp (continuous_originalPoint_ext a).measurable) measurable_const
    (continuous_labeledA_placeEquiv.isOpen_preimage _ a.domain_open).measurableSet

private theorem measurable_branch_inverse (f : a.domain → E F) (hf : Measurable f)
    (b : ShrunkChart F ζ hζ U R P H) (k : ℕ) :
    Measurable (fun x : ((directEnumeration b a).branch k).domain =>
      KPContActualCotangentTransportChoiceAlgebra.inverseTransport
        ((directEnumeration b a).branch k) (localAmbient a f) x.val x.property) := by
  let e := (directEnumeration b a).branch k
  have hp := (directEnumeration b a).properties k
  change Measurable (fun x : e.domain =>
    KPContActualCotangentTransportChoiceAlgebra.inverseTransport e (localAmbient a f) x.val x.property)
  cases he : e with
  | none =>
    change Measurable (fun x : (∅ : Set (M F)) => _)
    exact Subsingleton.measurable
  | some e' =>
    change Measurable (fun x : e'.arrow.domain =>
      (T e'.arrow x.val x.property).symm (localAmbient a f (e'.arrow.psi x.val)))
    have hψ : Continuous (fun x : e'.arrow.domain => e'.arrow.psi x.val) := by
      have hs : ContinuousOn e.psi e.domain := hp.smooth.continuousOn
      rw [he] at hs
      exact continuousOn_iff_continuous_restrict.mp hs
    have ht : Continuous (fun x : e'.arrow.domain => twistedOperator e'.arrow x.val) :=
      continuousOn_iff_continuous_restrict.mp (smooth_operators e'.arrow).2.continuousOn
    suffices hm : Measurable (fun x : e'.arrow.domain =>
        WithLp.ofLp ((T e'.arrow x.val x.property).symm (localAmbient a f (e'.arrow.psi x.val)))) from
      (WithLp.measurable_toLp 2 _).comp hm
    apply measurable_pi_iff.mpr
    intro j
    have hcoord : (fun x : e'.arrow.domain =>
        (T e'.arrow x.val x.property).symm (localAmbient a f (e'.arrow.psi x.val)) j) =
        (fun x : e'.arrow.domain => inner ℂ
          (twistedOperator e'.arrow x.val (EuclideanSpace.basisFun _ ℂ j))
          (localAmbient a f (e'.arrow.psi x.val))) := by
      funext x
      exact T_symm_coord e'.arrow x.val x.property _ j
    rw [hcoord]
    exact (ht.clm_apply continuous_const).measurable.inner
      ((measurable_localAmbient a f hf).comp hψ.measurable)

set_option maxHeartbeats 800000 in
private theorem measurable_extendedFields (f : a.domain → E F) (hf : Measurable f)
    (b : ShrunkChart F ζ hζ U R P H) : Measurable (extendedFields a f b) := by
  let S : Set (omega b) := {x | q b x.val ∈ a.baseDomain}
  have hS : MeasurableSet S := ((measurable_q b).comp measurable_subtype_coe)
    (every_shrunkChart_properties F ζ hζ U R P H a).base_measurable
  let branchValue (k : ℕ) (x : S) : E F :=
    if hx : x.val.val ∈ ((directEnumeration b a).branch k).domain then
      KPContActualCotangentTransportChoiceAlgebra.inverseTransport
        ((directEnumeration b a).branch k) (localAmbient a f) x.val.val hx else 0
  have hm : ∀ k, Measurable (branchValue k) := by
    intro k
    let D : Set S := {x | x.val.val ∈ ((directEnumeration b a).branch k).domain}
    have hD : MeasurableSet D := (measurable_subtype_coe.comp measurable_subtype_coe)
      ((directEnumeration b a).properties k).source_open.measurableSet
    have hinc : Measurable (fun x : D =>
        (⟨x.val.val.val, x.property⟩ : ((directEnumeration b a).branch k).domain)) :=
      (measurable_subtype_coe.comp (measurable_subtype_coe.comp measurable_subtype_coe)).subtype_mk
    have hpos : Measurable (fun x : D =>
        KPContActualCotangentTransportChoiceAlgebra.inverseTransport
          ((directEnumeration b a).branch k) (localAmbient a f) x.val.val.val x.property) :=
      (measurable_branch_inverse a f hf b k).comp hinc
    exact Measurable.dite hpos (measurable_const (a := (0 : E F))) hD
  have hfind : Measurable (fun x : S =>
      branchValue (Nat.find (directDomainExists b a x.val x.property)) x) :=
    Measurable.find hm (fun k => (measurable_subtype_coe.comp measurable_subtype_coe)
      ((directEnumeration b a).properties k).source_open.measurableSet)
      (fun x => directDomainExists b a x.val x.property)
  have hchosen : Measurable (fun x : S => extendedFields a f b x.val) := by
    convert hfind using 1
    funext x
    symm
    dsimp only [branchValue]
    rw [dite_eq_left (Nat.find_spec (directDomainExists b a x.val x.property))]
    dsimp only [extendedFields]
    rw [dite_eq_left (show q b x.val.val ∈ a.baseDomain from x.property)]
    dsimp only [KPContActualCotangentTransportChoiceAlgebra.inverseTransport]
    rw [localAmbient, dite_eq_left
      (((directEnumeration b a).properties _).target_subset
        ⟨x.val.val, Nat.find_spec (directDomainExists b a x.val x.property), rfl⟩)]
  convert (Measurable.dite hchosen (measurable_const (a := (0 : E F))) hS) using 1
  funext x
  by_cases hx : x ∈ S
  · rw [dite_eq_left hx]
  · rw [dite_eq_right hx]
    exact extendedFields_zero_off a f b x hx

private theorem extendedFields_selected (f : a.domain → E F)
    (b : ShrunkChart F ζ hζ U R P H) (x : omega b)
    (hb : q b x.val ∈ a.baseDomain) :
    extendedFields a f b x =
      KPContActualCotangentTransportChoiceAlgebra.inverseTransport
        ((directEnumeration b a).branch (Nat.find (directDomainExists b a x hb)))
        (localAmbient a f) x.val (Nat.find_spec (directDomainExists b a x hb)) := by
  dsimp only [extendedFields]
  rw [dite_eq_left hb]
  dsimp only [KPContActualCotangentTransportChoiceAlgebra.inverseTransport]
  rw [localAmbient, dite_eq_left (((directEnumeration b a).properties _).target_subset
    ⟨x.val, Nat.find_spec (directDomainExists b a x hb), rfl⟩)]

private theorem extendedFields_covariant (f : a.domain → E F)
    (he : PointwiseEquivariant a f) (b c : ShrunkChart F ζ hζ U R P H)
    (e : ActualBranch b c) (x : M F) (hx : x ∈ e.arrow.domain) :
    extendedFields a f c ⟨e.arrow.psi x, e.target_shrinking hx⟩ =
      T e.arrow x hx (extendedFields a f b ⟨x, e.source_shrinking hx⟩) := by
  let y : omega c := ⟨e.arrow.psi x, e.target_shrinking hx⟩
  let z : omega b := ⟨x, e.source_shrinking hx⟩
  by_cases hb : q b x ∈ a.baseDomain
  · have hc : q c y.val ∈ a.baseDomain := by rwa [q_actualBranch e x]
    let j := Nat.find (directDomainExists c a y hc)
    let k := Nat.find (directDomainExists b a z hb)
    have hj : y.val ∈ ((directEnumeration c a).branch j).domain :=
      Nat.find_spec (directDomainExists c a y hc)
    have hk : z.val ∈ ((directEnumeration b a).branch k).domain :=
      Nat.find_spec (directDomainExists b a z hb)
    have hmix := (source_transport a f he).mixed_charts b c 0 (some e)
      ((directEnumeration b a).branch k) ((directEnumeration c a).branch j) x hx hk hj
    have hleft := extendedFields_selected a f c y hc
    have hright := extendedFields_selected a f b z hb
    rw [hleft, hright]
    exact hmix
  · have hc : q c y.val ∉ a.baseDomain := by rwa [q_actualBranch e x]
    rw [extendedFields_zero_off a f c y hc, extendedFields_zero_off a f b z hb, map_zero]

 def isotropyBranch (a : ShrunkChart F ζ hζ U R P H) (γ : Gamma a) :
    ActualBranch a a where
  component_eq := rfl
  arrow := { isotropyArrow a γ with
    domain := omega a
    isOpen_domain := by
      exact (continuous_labeledA_placeEquiv.isOpen_preimage _ a.domain_open)
    source := KPContActualCotangentMeasurableFamilies.omega_subset_larger a
    target := fun x hx => (isotropyArrow a γ).target
      (KPContActualCotangentMeasurableFamilies.omega_subset_larger a hx) }
  source_shrinking := Set.Subset.refl _
  target_shrinking := fun x hx => isotropy_mem a γ x hx
  target_larger := fun x hx => (isotropyArrow a γ).target
    (KPContActualCotangentMeasurableFamilies.omega_subset_larger a hx)

theorem extendedFields_isFamily (f : a.domain → E F)
    (hf : Measurable f) (he : PointwiseEquivariant a f) :
    IsMeasurableCotangentFamily (extendedFields a f) := by
  refine ⟨measurable_extendedFields a f hf, ?_, extendedFields_covariant a f he⟩
  intro b γ x hx
  have h := extendedFields_covariant a f he b b (isotropyBranch b γ) x hx
  convert h using 1
  · rfl
  · apply congrArg (fun t : E F ≃ₗᵢ[ℂ] E F => t (extendedFields a f b ⟨x, hx⟩))
    apply LinearIsometryEquiv.ext
    intro v
    rfl

def extendedFamily (f : a.domain → E F)
    (hf : Measurable f) (he : PointwiseEquivariant a f) : Family (U := U) (H := H) :=
  ⟨extendedFields a f, extendedFields_isFamily a f hf he⟩

private theorem base_lift_exists (z : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ (b : ShrunkChart F ζ hζ U R P H) (x : omega b), q b x.val = z := by
  let c := Classical.choice
    (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  have hz : z ∈ ⋃ n, (c.chart n).baseDomain := by rw [c.covers]; trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
  obtain ⟨y, hy⟩ := Set.mem_range.mp hn
  exact ⟨c.chart n, coordinates (c.chart n) y, (q_coordinates_ext (c.chart n) y).trans hy⟩

private theorem extended_normSquare_off (f : a.domain → E F)
    (hf : Measurable f) (he : PointwiseEquivariant a f)
    (z : KPFiniteCuspAtlas.rawXU F ζ hζ U) (hz : z ∉ a.baseDomain) :
    normSquare (extendedFamily a f hf he) z = 0 := by
  obtain ⟨b, x, hx⟩ := base_lift_exists z
  rw [← hx, normSquare_chart]
  change ‖extendedFields a f b x‖₊ ^ 2 = 0
  rw [extendedFields_zero_off a f b x (by rwa [hx])]
  simp

theorem extendedFamily_square_integral (f : a.domain → E F)
    (hf : Measurable f) (he : PointwiseEquivariant a f) :
    (∫⁻ x, ENNReal.ofReal ((normSquare (extendedFamily a f hf he) x : ℝ))
      ∂(KPContActualCotangentMeasurableFamilies.baseMeasure (R := R) (P := P) (U := U))) =
    ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂a.liftedMeasure := by
  let r := extendedFamily a f hf he
  have hP := every_shrunkChart_properties F ζ hζ U R P H a
  have hpull : ∀ y : a.domain,
      ENNReal.ofReal (normSquare r (a.toBase y) : ℝ) = ENNReal.ofReal (‖f y‖ ^ 2) := by
    intro y
    rw [← q_coordinates_ext a y, normSquare_chart]
    change ENNReal.ofReal (↑(‖extendedFields a f a (coordinates a y)‖₊ ^ 2) : ℝ) = _
    rw [extendedFields_source a f hf he y]
    rfl
  calc
    _ = ∫⁻ z in a.baseDomain, ENNReal.ofReal (normSquare r z : ℝ) ∂baseMeasure := by
      symm
      apply setLIntegral_eq_of_support_subset
      intro z hz
      by_contra hnot
      exact hz (by simp [r, extended_normSquare_off a f hf he z hnot])
    _ = ∫⁻ z, ENNReal.ofReal (normSquare r z : ℝ) ∂Measure.map a.toBase a.liftedMeasure := by
      rw [hP.exact_pushforward]
    _ = ∫⁻ y, ENNReal.ofReal (normSquare r (a.toBase y) : ℝ) ∂a.liftedMeasure :=
      lintegral_map' ((measurable_normSquare r).coe_nnreal_real.ennreal_ofReal.aemeasurable)
        hP.measurable.aemeasurable
    _ = _ := lintegral_congr (hpull)

theorem extendedFamily_squareFinite (f : a.domain → E F)
    (hf : Measurable f) (he : PointwiseEquivariant a f)
    (hLp : MemLp f 2 a.liftedMeasure) : squareFinite (extendedFamily a f hf he) := by
  unfold squareFinite
  rw [extendedFamily_square_integral]
  have hint := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hLp
  have hfin := hasFiniteIntegral_iff_enorm.mp hint.2
  simpa only [Real.enorm_eq_ofReal (sq_nonneg _)] using hfin

def extendedSquareFamily (f : a.domain → E F)
    (hf : Measurable f) (he : PointwiseEquivariant a f)
    (hLp : MemLp f 2 a.liftedMeasure) : SquareFiniteFamily (U := U) (H := H) :=
  ⟨extendedFamily a f hf he, extendedFamily_squareFinite a f hf he hLp⟩

def localRepresentative (f : Q a) : a.domain → E F :=
  KPMeasurableLocalL2.representative (localData a) (fullPiece a) f

theorem localRepresentative_measurable (f : Q a) : Measurable (localRepresentative a f) :=
  (KPMeasurableLocalL2.representative_spec (localData a) (fullPiece a) f).1

theorem localRepresentative_equivariant (f : Q a) :
    PointwiseEquivariant a (localRepresentative a f) :=
  (KPMeasurableLocalL2.representative_spec (localData a) (fullPiece a) f).2.2.2

theorem localRepresentative_memLp (f : Q a) :
    MemLp (localRepresentative a f) 2 a.liftedMeasure :=
  KPMeasurableLocalL2.representative_memLp (localData a) (fullPiece a) f

def extensionRepresentative (f : Q a) : SquareFiniteFamily (U := U) (H := H) :=
  extendedSquareFamily a (localRepresentative a f)
    (localRepresentative_measurable a f) (localRepresentative_equivariant a f)
    (localRepresentative_memLp a f)

private theorem extendedFamily_sub (f g : a.domain → E F)
    (hf : Measurable f) (hg : Measurable g)
    (he : PointwiseEquivariant a f) (hge : PointwiseEquivariant a g) :
    extendedFamily a f hf he - extendedFamily a g hg hge =
      extendedFamily a (f - g) (hf.sub hg) (by
        intro γ y
        change f _ - g _ = actualTensor a γ y (f y - g y)
        rw [he, hge, map_sub]) := by
  apply Subtype.ext
  funext b x
  change extendedFields a f b x - extendedFields a g b x = extendedFields a (f - g) b x
  unfold extendedFields
  by_cases hx : q b x.val ∈ a.baseDomain
  · simp only [dite_eq_left hx, Pi.sub_apply, map_sub]
  · simp only [dite_eq_right hx, sub_zero]

 theorem extendedFamily_ae (f g : a.domain → E F)
    (hf : Measurable f) (hg : Measurable g)
    (he : PointwiseEquivariant a f) (hge : PointwiseEquivariant a g)
    (hfg : f =ᵐ[a.liftedMeasure] g) :
    AeEquivalent (extendedFamily a f hf he) (extendedFamily a g hg hge) := by
  have hsub : PointwiseEquivariant a (f-g) := by
    intro γ y
    change f _ - g _ = actualTensor a γ y (f y - g y)
    rw [he γ y, hge γ y, map_sub]
  have hint : (∫⁻ z, ENNReal.ofReal (normSquare
      (extendedFamily a (f-g) (hf.sub hg) hsub) z : ℝ)
        ∂(baseMeasure (R := R) (P := P) (U := U))) = 0 := by
    rw [extendedFamily_square_integral a (f-g) (hf.sub hg) hsub]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hfg] with y hy
    simp [hy]
  have hz := (lintegral_eq_zero_iff
    (measurable_normSquare _).coe_nnreal_real.ennreal_ofReal).mp hint
  unfold AeEquivalent
  rw [extendedFamily_sub]
  filter_upwards [hz] with z hz
  change ENNReal.ofReal (normSquare (extendedFamily a (f-g) (hf.sub hg) hsub) z : ℝ) = 0 at hz
  simpa only [ENNReal.ofReal_coe_nnreal, ENNReal.coe_eq_zero] using hz

 theorem extendedFamily_add (f g : a.domain → E F)
    (hf : Measurable f) (hg : Measurable g)
    (he : PointwiseEquivariant a f) (hge : PointwiseEquivariant a g) :
    extendedFamily a (f+g) (hf.add hg) (by
      intro γ y
      change f _ + g _ = actualTensor a γ y (f y + g y)
      rw [he, hge, map_add]) = extendedFamily a f hf he + extendedFamily a g hg hge := by
  apply Subtype.ext
  funext b x
  change extendedFields a (f+g) b x = extendedFields a f b x + extendedFields a g b x
  unfold extendedFields
  by_cases hx : q b x.val ∈ a.baseDomain
  · simp only [dite_eq_left hx, Pi.add_apply, map_add]
  · simp only [dite_eq_right hx, add_zero]

 theorem extendedFamily_smul (c : ℂ) (f : a.domain → E F)
    (hf : Measurable f) (he : PointwiseEquivariant a f) :
    extendedFamily a (c • f) (hf.const_smul c) (by
      intro γ y
      change c • f _ = actualTensor a γ y (c • f y)
      rw [he, map_smul]) = c • extendedFamily a f hf he := by
  apply Subtype.ext
  funext b x
  change extendedFields a (c • f) b x = c • extendedFields a f b x
  unfold extendedFields
  by_cases hx : q b x.val ∈ a.baseDomain
  · simp only [dite_eq_left hx, Pi.smul_apply, map_smul]
  · simp only [dite_eq_right hx, smul_zero]

def extensionLinear : Q a →ₗ[ℂ] IntrinsicHilbert cover where
  toFun f := (intrinsicClass cover).symm (toAeQuotient (extensionRepresentative a f))
  map_add' := by
    intro f g
    apply (intrinsicClass cover).injective
    change toAeQuotient (extensionRepresentative a (f+g)) =
      toAeQuotient (extensionRepresentative a f) + toAeQuotient (extensionRepresentative a g)
    rw [← toAeQuotient_add, toAeQuotient_eq_iff]
    let rf := localRepresentative a f
    let rg := localRepresentative a g
    have hae : localRepresentative a (f+g) =ᵐ[a.liftedMeasure] rf + rg := by
      filter_upwards [(KPMeasurableLocalL2.representative_spec (localData a) (fullPiece a) (f+g)).2.1,
        (KPMeasurableLocalL2.representative_spec (localData a) (fullPiece a) f).2.1,
        (KPMeasurableLocalL2.representative_spec (localData a) (fullPiece a) g).2.1,
        Lp.coeFn_add (f : Lp (E F) 2 a.liftedMeasure) (g : Lp (E F) 2 a.liftedMeasure)] with y h1 h2 h3 h4
      exact h1.trans (h4.trans (congrArg₂ (·+·) h2.symm h3.symm))
    have h := extendedFamily_ae a _ _ (localRepresentative_measurable a (f+g))
      ((localRepresentative_measurable a f).add (localRepresentative_measurable a g))
      (localRepresentative_equivariant a (f+g)) (by
        intro γ y
        change localRepresentative a f _ + localRepresentative a g _ =
          actualTensor a γ y (localRepresentative a f y + localRepresentative a g y)
        rw [localRepresentative_equivariant a f, localRepresentative_equivariant a g, map_add]) hae
    rw [extendedFamily_add a _ _ (localRepresentative_measurable a f)
      (localRepresentative_measurable a g) (localRepresentative_equivariant a f)
      (localRepresentative_equivariant a g)] at h
    exact h
  map_smul' := by
    intro c f
    apply (intrinsicClass cover).injective
    change toAeQuotient (extensionRepresentative a (c • f)) = c • toAeQuotient (extensionRepresentative a f)
    rw [← toAeQuotient_smul, toAeQuotient_eq_iff]
    have hae : localRepresentative a (c • f) =ᵐ[a.liftedMeasure] c • localRepresentative a f := by
      filter_upwards [(KPMeasurableLocalL2.representative_spec (localData a) (fullPiece a) (c • f)).2.1,
        (KPMeasurableLocalL2.representative_spec (localData a) (fullPiece a) f).2.1,
        Lp.coeFn_smul c (f : Lp (E F) 2 a.liftedMeasure)] with y h1 h2 h3
      exact h1.trans (h3.trans (congrArg (c • ·) h2.symm))
    have h := extendedFamily_ae a _ _ (localRepresentative_measurable a (c • f))
      ((localRepresentative_measurable a f).const_smul c)
      (localRepresentative_equivariant a (c • f)) (by
        intro γ y
        change c • localRepresentative a f _ = actualTensor a γ y (c • localRepresentative a f y)
        rw [localRepresentative_equivariant a f, map_smul]) hae
    rw [extendedFamily_smul a c _ (localRepresentative_measurable a f)
      (localRepresentative_equivariant a f)] at h
    exact h

theorem extensionLinear_norm (f : Q a) : ‖extensionLinear cover a f‖ = ‖f‖ := by
  let r := extensionRepresentative a f
  have hP := every_shrunkChart_properties F ζ hζ U R P H a
  have hnorm : ‖extensionLinear cover a f‖ ^ 2 =
      ∫ y, ‖localRepresentative a f y‖ ^ 2 ∂a.liftedMeasure := by
    rw [norm_sq_eq_integral cover (extensionLinear cover a f) r rfl]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := a.baseDomain)
      (fun z hz => by simp [r, extensionRepresentative, extendedSquareFamily,
        extended_normSquare_off a _ _ _ z hz])]
    rw [← hP.exact_pushforward]
    rw [integral_map hP.measurable.aemeasurable
      (measurable_normSquare r.val).coe_nnreal_real.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards with y
    rw [← q_coordinates_ext a y, normSquare_chart]
    change (↑(‖extendedFields a (localRepresentative a f) a (coordinates a y)‖₊ ^ 2) : ℝ) = _
    rw [extendedFields_source a _ (localRepresentative_measurable a f)
      (localRepresentative_equivariant a f) y]
    rfl
  have hlocal : ‖f‖ ^ 2 = ∫ y, ‖localRepresentative a f y‖ ^ 2 ∂a.liftedMeasure := by
    have hi := KPMeasurableLocalL2.Q_integrable_inner (localData a) (fullPiece a) f f
    change Integrable (fun y => inner ℂ ((f : Lp (E F) 2 a.liftedMeasure) y)
      ((f : Lp (E F) 2 a.liftedMeasure) y)) a.liftedMeasure at hi
    calc
      ‖f‖ ^ 2 = RCLike.re (inner ℂ f f) :=
        InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) f
      _ = RCLike.re (∫ y, inner ℂ ((f : Lp (E F) 2 a.liftedMeasure) y)
          ((f : Lp (E F) 2 a.liftedMeasure) y) ∂a.liftedMeasure) :=
        congrArg RCLike.re (KPMeasurableLocalL2.Q_inner_eq_integral (localData a) (fullPiece a) f f)
      _ = _ := by
        rw [← integral_re hi]
        apply integral_congr_ae
        filter_upwards [(KPMeasurableLocalL2.representative_spec (localData a) (fullPiece a) f).2.1]
          with y hy
        change localRepresentative a f y = (f : Lp (E F) 2 a.liftedMeasure) y at hy
        rw [← hy]
        exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  nlinarith [norm_nonneg (extensionLinear cover a f), norm_nonneg f]

def ext : Q a →ₗᵢ[ℂ] IntrinsicHilbert cover where
  __ := extensionLinear cover a
  norm_map' := extensionLinear_norm cover a





def indicatorFamily (r : Family (U := U) (H := H)) : Family (U := U) (H := H) :=
  ⟨fun b x => if KPContCotangentOverlapRationalBranches.q b x.val ∈ a.baseDomain
    then coefficient r b x else 0, by
    refine ⟨?_, ?_, ?_⟩
    · intro b
      exact Measurable.ite (((measurable_q b).comp measurable_subtype_coe)
        (every_shrunkChart_properties F ζ hζ U R P H a).base_measurable)
        (r.property.1 b) measurable_const
    · intro b γ x hx
      have hq : KPContCotangentOverlapRationalBranches.q b
          ((isotropyArrow b γ).psi x) = KPContCotangentOverlapRationalBranches.q b x :=
        q_actualBranch (isotropyBranch b γ) x
      have hcoe := r.property.2.1 b γ x hx
      change (if KPContCotangentOverlapRationalBranches.q b ((isotropyArrow b γ).psi x)
          ∈ a.baseDomain then
            coefficient r b ⟨(isotropyArrow b γ).psi x, isotropy_mem b γ x hx⟩ else 0) =
        T (isotropyArrow b γ) x
          (KPContActualCotangentMeasurableFamilies.omega_subset_larger b hx)
          (if KPContCotangentOverlapRationalBranches.q b x ∈ a.baseDomain
            then coefficient r b ⟨x, hx⟩ else 0)
      rw [hq]
      by_cases h : KPContCotangentOverlapRationalBranches.q b x ∈ a.baseDomain
      · rw [if_pos h, if_pos h]
        exact hcoe
      · rw [if_neg h, if_neg h, map_zero]
    · intro b c e x hx
      have hq : KPContCotangentOverlapRationalBranches.q c (e.arrow.psi x)
          = KPContCotangentOverlapRationalBranches.q b x := q_actualBranch e x
      have hcoe := r.property.2.2 b c e x hx
      change (if KPContCotangentOverlapRationalBranches.q c (e.arrow.psi x)
          ∈ a.baseDomain then
            coefficient r c ⟨e.arrow.psi x, e.target_shrinking hx⟩ else 0) =
        T e.arrow x hx
          (if KPContCotangentOverlapRationalBranches.q b x ∈ a.baseDomain
            then coefficient r b ⟨x, e.source_shrinking hx⟩ else 0)
      rw [hq]
      by_cases h : KPContCotangentOverlapRationalBranches.q b x ∈ a.baseDomain
      · rw [if_pos h, if_pos h]
        exact hcoe
      · rw [if_neg h, if_neg h, map_zero]⟩

 theorem coefficient_indicatorFamily (r : Family (U := U) (H := H))
    (b : ShrunkChart F ζ hζ U R P H) (x : omega b) :
    coefficient (indicatorFamily a r) b x =
      if KPContCotangentOverlapRationalBranches.q b x.val ∈ a.baseDomain
        then coefficient r b x else 0 := rfl

theorem indicatorFamily_squareFinite (r : SquareFiniteFamily (U := U) (H := H)) :
    squareFinite (indicatorFamily a r.val) := by
  have hle : ∀ z, normSquare (indicatorFamily a r.val) z ≤ normSquare r.val z := by
    intro z
    obtain ⟨b, x, hx⟩ := base_lift_exists z
    rw [← hx, normSquare_chart (indicatorFamily a r.val) b x, normSquare_chart r.val b x]
    by_cases h : KPContCotangentOverlapRationalBranches.q b x.val ∈ a.baseDomain
    · rw [show coefficient (indicatorFamily a r.val) b x = coefficient r.val b x from by
        simp only [coefficient, indicatorFamily]
        exact ite_eq_left h]
    · rw [show coefficient (indicatorFamily a r.val) b x = 0 from by
        simp only [coefficient, indicatorFamily]
        exact ite_eq_right h]
      simp
  unfold squareFinite
  refine lt_of_le_of_lt (lintegral_mono fun z => ?_) r.property
  rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  exact ENNReal.coe_le_coe.mpr (hle z)

def indicatorSquareFamily (r : SquareFiniteFamily (U := U) (H := H)) :
    SquareFiniteFamily (U := U) (H := H) :=
  ⟨indicatorFamily a r.val, indicatorFamily_squareFinite a r⟩

 theorem indicatorFamily_add (r s : Family (U := U) (H := H)) :
    indicatorFamily a (r + s) = indicatorFamily a r + indicatorFamily a s := by
  apply Subtype.ext
  funext b x
  show (if KPContCotangentOverlapRationalBranches.q b x.val ∈ a.baseDomain
      then coefficient (r + s) b x else 0) =
    (if KPContCotangentOverlapRationalBranches.q b x.val ∈ a.baseDomain
      then coefficient r b x else 0) +
    (if KPContCotangentOverlapRationalBranches.q b x.val ∈ a.baseDomain
      then coefficient s b x else 0)
  by_cases h : KPContCotangentOverlapRationalBranches.q b x.val ∈ a.baseDomain
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
    show coefficient (r + s) b x = coefficient r b x + coefficient s b x
    rfl
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, add_zero]

 theorem indicatorFamily_smul (c : ℂ) (r : Family (U := U) (H := H)) :
    indicatorFamily a (c • r) = c • indicatorFamily a r := by
  apply Subtype.ext
  funext b x
  show (if KPContCotangentOverlapRationalBranches.q b x.val ∈ a.baseDomain
      then coefficient (c • r) b x else 0) =
    c • (if KPContCotangentOverlapRationalBranches.q b x.val ∈ a.baseDomain
      then coefficient r b x else 0)
  by_cases h : KPContCotangentOverlapRationalBranches.q b x.val ∈ a.baseDomain
  · rw [ite_eq_left h, ite_eq_left h]
    show coefficient (c • r) b x = c • coefficient r b x
    rfl
  · rw [ite_eq_right h, ite_eq_right h, smul_zero]

def cutoff : IntrinsicHilbert cover →ₗ[ℂ] IntrinsicHilbert cover where
  toFun := Quotient.lift (fun r =>
    (intrinsicClass cover).symm (toAeQuotient (indicatorSquareFamily a r))) (by
    intro r s hrs
    have hae : AeEquivalent r.val s.val :=
      (toAeQuotient_eq_iff (U := U) (H := H) r s).mp
        (Quotient.sound hrs : toAeQuotient (U := U) (H := H) r = toAeQuotient s)
    show toAeQuotient (indicatorSquareFamily a r) = toAeQuotient (indicatorSquareFamily a s)
    rw [toAeQuotient_eq_iff]
    refine (aeEquivalent_iff_all_charts (U := U) (H := H) _ _).mpr fun b => ?_
    filter_upwards [(aeEquivalent_iff_all_charts (U := U) (H := H) r.val s.val).mp hae b]
      with x hx
    show coefficient (indicatorFamily a r.val) b x = coefficient (indicatorFamily a s.val) b x
    by_cases h : KPContCotangentOverlapRationalBranches.q b x.val ∈ a.baseDomain
    · rw [coefficient_indicatorFamily, coefficient_indicatorFamily, ite_eq_left h, ite_eq_left h]
      exact hx
    · rw [coefficient_indicatorFamily, coefficient_indicatorFamily, ite_eq_right h,
        ite_eq_right h])
  map_add' := by
    intro v w
    obtain ⟨r, hr⟩ := toAeQuotient_surjective (U := U) (H := H) v
    obtain ⟨s, hs⟩ := toAeQuotient_surjective (U := U) (H := H) w
    change toAeQuotient (U := U) (H := H) r = v at hr
    change toAeQuotient (U := U) (H := H) s = w at hs
    rw [← hr, ← hs]
    have hab : (toAeQuotient (U := U) (H := H) (r+s) : IntrinsicHilbert cover) =
        toAeQuotient r + toAeQuotient s := toAeQuotient_add r s
    erw [← hab]
    change toAeQuotient (indicatorSquareFamily a (r+s)) =
      toAeQuotient (indicatorSquareFamily a r) + toAeQuotient (indicatorSquareFamily a s)
    rw [← toAeQuotient_add]
    congr 1
    apply Subtype.ext
    exact indicatorFamily_add a r.val s.val
  map_smul' := by
    intro c v
    obtain ⟨r, hr⟩ := toAeQuotient_surjective (U := U) (H := H) v
    change toAeQuotient (U := U) (H := H) r = v at hr
    rw [← hr]
    have hsm : (toAeQuotient (U := U) (H := H) (c • r) : IntrinsicHilbert cover) =
        c • toAeQuotient r := toAeQuotient_smul c r
    erw [← hsm]
    change toAeQuotient (indicatorSquareFamily a (c • r)) = c • toAeQuotient (indicatorSquareFamily a r)
    rw [← toAeQuotient_smul]
    congr 1
    apply Subtype.ext
    exact indicatorFamily_smul a c r.val





def liftField (f : omega a → E F) : a.domain → E F := fun y => f (coordinates a y)

def ambientField (b : ShrunkChart F ζ hζ U R P H) (f : omega b → E F) : M F → E F :=
  fun x => if hx : x ∈ omega b then f ⟨x, hx⟩ else 0



end DedekindZetaZeroFree.KPContActualCotangentChartZeroExtension

namespace DedekindZetaZeroFree

open KPContActualCotangentCountableShrinking KPContActualCotangentMeasurableFamilies
open KPContActualCotangentIntrinsicHilbertIntegral KPContActualCotangentChartRestriction
open KPContActualCotangentChartZeroExtension KPContCotangentActualGenuineTwistIsotropy
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContActualCotangentPieceHilbertSum

end DedekindZetaZeroFree

end
