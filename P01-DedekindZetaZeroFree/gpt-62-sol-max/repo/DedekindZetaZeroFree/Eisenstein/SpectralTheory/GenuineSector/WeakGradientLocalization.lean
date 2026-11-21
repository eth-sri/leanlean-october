module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSectors.CoordinateBallRestriction
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSectors.BoundedCutoffMultiplication
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSectors.CompactCutoffDifferentialBounds
public import DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.ClassicalToWeakSolutions
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Friedrichs.ClosedGradientCutoffProduct

public import DedekindZetaZeroFree.Analysis.Sobolev.WeakDerivatives.TestPairings

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualCotangentMeasurableFamilies KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContActualCotangentChartRestriction
open KPContActualSectorChartEquivariantInputs KPContSectorLineL2Isometry
open KPContLocalNorm
open KPContActualCotangentCountableShrinking KPContActualCotangentPieceHilbertSum

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

def coordinateDomain (a : ActualChart (U := U) (H := H)) : Set (Space (3 * d F)) :=
  (baseReindex (F := F)).symm ⁻¹' omega a

def InteriorBall (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F)) : Prop :=
  IsCompact (closure B.carrier) ∧ closure B.carrier ⊆ coordinateDomain a

private theorem base_direction (j : Fin (3*d F)) :
    (baseReindex (F:=F)).symm (EuclideanSpace.single j 1) =
      HyperbolicChart.coordinateVector (d F) ((coefficientIndex (F:=F)).symm j).1
        ((coefficientIndex (F:=F)).symm j).2 := by
  ext ik
  simp only [baseReindex, LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.symm_symm, HyperbolicChart.coordinateVector,
    WithLp.ofLp_toLp]
  simp [EuclideanSpace.single_apply, Pi.single_apply, ← Equiv.apply_eq_iff_eq_symm_apply]
private theorem decoder_differential (a : ActualChart (U:=U) (H:=H)) (f : omega a → ℂ)
    (x : Space (3*d F)) (hx : x ∈ coordinateDomain a) (j : Fin (3*d F)) :
    (let p := (baseReindex (F:=F)).symm x
     let ik := (coefficientIndex (F:=F)).symm j
     let v := chartDifferential a f ⟨p,hx⟩
     ![(Real.exp (-p (ik.1,2)):ℂ) * v (ik.1,1),
       (Real.exp (-p (ik.1,2)):ℂ) * v (ik.1,2), v (ik.1,0)] ik.2) =
    HyperbolicChart.coordinateDerivative (d F) ((coefficientIndex (F:=F)).symm j).1
      ((coefficientIndex (F:=F)).symm j).2 (liftExtension a f) ((baseReindex (F:=F)).symm x) := by
  generalize hi : (coefficientIndex (F:=F)).symm j = ik
  obtain ⟨i,k⟩ := ik
  fin_cases k <;> simp [chartDifferential, CotangentLogCoframe.j_apply,
    HyperbolicChart.differential, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
    ← Complex.exp_add]

private theorem flattened_differential (a : ActualChart (U := U) (H := H))
    (f : omega a → ℂ) (x : Space (3 * d F)) (hx : x ∈ coordinateDomain a)
    (hf : DifferentiableAt ℝ (liftExtension a f) ((baseReindex (F := F)).symm x))
    (j : Fin (3 * d F)) :
    fderiv ℝ (fun y => liftExtension a f ((baseReindex (F := F)).symm y)) x
      (EuclideanSpace.single j 1) =
    HyperbolicChart.coordinateDerivative (d F) ((coefficientIndex (F := F)).symm j).1
      ((coefficientIndex (F := F)).symm j).2 (liftExtension a f)
        ((baseReindex (F := F)).symm x) := by
  have hd := hf.hasFDerivAt.comp x
    ((baseReindex (F := F)).symm.toContinuousLinearEquiv.hasFDerivAt)
  change HasFDerivAt (fun y => liftExtension a f ((baseReindex (F := F)).symm y)) _ x at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  rw [base_direction]
  rfl

private theorem coordinateDomain_isOpen (a : ActualChart (U := U) (H := H)) :
    IsOpen (coordinateDomain a) := by
  change IsOpen ((toActual (F := F) (ζ := ζ) (hζ := hζ)) ⁻¹' a.domain)
  apply a.domain_open.preimage
  unfold toActual labeledA
  fun_prop

private theorem smooth_liftExtension (a : ActualChart (U := U) (H := H))
    (f : omega a → ℂ) (hf : SmoothOnLift a f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (liftExtension a f) (omega a) := by
  obtain ⟨g, hg, he⟩ := hf
  apply hg.congr
  intro x hx
  simpa only [liftExtension, dif_pos hx] using (he ⟨x, hx⟩).symm

private theorem smooth_flattened (a : ActualChart (U := U) (H := H))
    (f : omega a → ℂ) (hf : SmoothOnLift a f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => liftExtension a f ((baseReindex (F := F)).symm x))
      (coordinateDomain a) :=
  (smooth_liftExtension a f hf).comp (baseReindex (F := F)).symm.contDiff.contDiffOn
    (fun _ hx => hx)

private theorem smooth_coordinate_sobolev (a : ActualChart (U := U) (H := H))
    (B : LocalBall (3 * d F)) (hB : InteriorBall a B)
    (f : omega a → ℂ) (hf : SmoothOnLift a f) :
    ∃ h : IntegerSobolev B 1, ∀ α,
      (fun x => h.derivatives α x) =ᵐ[volume.restrict B.carrier]
        coordinateDerivative α (fun x => liftExtension a f ((baseReindex (F := F)).symm x)) := by
  let u := fun x => liftExtension a f ((baseReindex (F := F)).symm x)
  have hu := smooth_flattened a f hf
  have hclosed : Metric.closedBall B.center B.radius ⊆ coordinateDomain a := by
    rw [← closure_ball B.center (ne_of_gt B.radius_pos)]
    exact hB.2
  have hL2 := fun α : MultiIndex (3 * d F) 1 =>
    KPContLocalEnergy.SobolevEnergyEstimates.coordinateDerivative_memLp_of_closedBall B
      (coordinateDomain_isOpen a) hclosed hu α
  obtain ⟨h, hh⟩ := smooth_has_integerSobolev_data B u
    (hu.mono (subset_closure.trans hB.2)) hL2
  exact ⟨h, fun α => (hh α).symm ▸ (hL2 α).coeFn_toLp⟩

def scalarCoordinate (s : BorelL2Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : Space (3 * d F)) : ℂ :=
  liftExtension a (sectionFields s.val a) ((baseReindex (F := F)).symm x)

def covariantCoordinate (W : Family (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (x : Space (3 * d F))
    (j : Fin (3 * d F)) : ℂ :=
  let p := (baseReindex (F := F)).symm x
  let ik := (coefficientIndex (F := F)).symm j
  let v := liftExtension a (coefficient W a) p
  ![(Real.exp (-p (ik.1, 2)) : ℂ) * v (ik.1, 1),
    (Real.exp (-p (ik.1, 2)) : ℂ) * v (ik.1, 2), v (ik.1, 0)] ik.2

def zeroIndex (n : ℕ) : MultiIndex n 1 := ⟨fun _ => 0, by simp⟩

def WeakChartData (s : BorelL2Sections F ζ hζ U R P H)
    (W : Family (U := U) (H := H)) : Prop :=
  ∀ (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F)),
    InteriorBall a B → ∀ ε : rootsOfUnity 3 F,
    ∃ h : IntegerSobolev B 1,
      (fun x => h.derivatives (zeroIndex (3 * d F)) x) =ᵐ[volume.restrict B.carrier]
        (fun x => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * scalarCoordinate s a x) ∧
      ∀ (α : MultiIndex (3 * d F) 1) (j : Fin (3 * d F)), (α.val j).val = 1 →
        (fun x => h.derivatives α x) =ᵐ[volume.restrict B.carrier]
          (fun x => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
            covariantCoordinate W a x j)

def IsActualWeakGradient (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (v : KPContActualSectorCotangentL2.V F ζ hζ U R P H) : Prop :=
  ∃ (s : BorelL2Sections F ζ hζ U R P H) (r : SquareFiniteFamily (U := U) (H := H)),
    sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s ∧
    KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r = v ∧ WeakChartData s r.val

 def firstIndex {n : ℕ} (j : Fin n) : MultiIndex n 1 :=
  ⟨Pi.single j 1, by simp [Pi.single_apply, apply_ite Fin.val]⟩

private theorem firstIndex_eq_raw {n : ℕ} (j : Fin n) :
    firstIndex j = KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j := by
  apply Subtype.ext
  funext k
  simp only [firstIndex, KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, Pi.single_apply]

private theorem firstIndex_directions {n : ℕ} (j : Fin n) : (firstIndex j).directions = [j] := by
  rw [firstIndex_eq_raw]
  exact KPContLocalEnergy.SobolevEnergyEstimates.firstIndex_directions j

private theorem index_one_eq_first {n : ℕ} (α : MultiIndex n 1) (j : Fin n)
    (hj : (α.val j).val = 1) : α = firstIndex j := by
  have hs := Finset.sum_le_one_iff.mp α.property
  apply Subtype.ext
  funext k
  apply Fin.ext
  by_cases hkj : k = j
  · subst k
    simpa [firstIndex] using hj
  · have hk : (α.val k).val = 0 := by
      by_contra hk
      exact hkj (hs k j (Finset.mem_univ _) (Finset.mem_univ _) hk (by omega)).1
    simpa [firstIndex, Pi.single_apply, hkj] using hk

private theorem test_smooth_local_data (f : S_U F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F)) (hB : InteriorBall a B) :
    ∃ h : IntegerSobolev B 1,
      (fun x => h.derivatives (zeroIndex (3 * d F)) x) =ᵐ[volume.restrict B.carrier]
        (fun x => liftExtension a (f.val a) ((baseReindex (F := F)).symm x)) ∧
      ∀ (α : MultiIndex (3 * d F) 1) (j : Fin (3 * d F)), (α.val j).val = 1 →
        (fun x => h.derivatives α x) =ᵐ[volume.restrict B.carrier]
          (fun x => covariantCoordinate (D_U f).val a x j) := by
  obtain ⟨h, hh⟩ := smooth_coordinate_sobolev a B hB (f.val a) (f.property.1 a)
  refine ⟨h, ?_, ?_⟩
  · change (fun x => h.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex (3 * d F) 1) x) =ᵐ[_] _
    simpa only [KPContLocalEnergy.SobolevEnergyEstimates.coordinateDerivative_zeroIndex] using
      hh (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex (3 * d F) 1)
  · intro α j hj
    have heq := index_one_eq_first α j hj
    rw [heq]
    apply (hh (firstIndex j)).trans
    filter_upwards [ae_restrict_mem B.toOpens.isOpen.measurableSet] with x hx
    have hx' : x ∈ coordinateDomain a := hB.2 (subset_closure hx)
    have hp := (smooth_liftExtension a (f.val a) (f.property.1 a)).differentiableOn
      (by simp) ((baseReindex (F := F)).symm x) hx'
    have hopen : IsOpen (omega a) := by
      change IsOpen (labeledA (KPContCotangentActualOverlap.placeEquiv F ζ hζ) ⁻¹' a.domain)
      apply a.domain_open.preimage
      unfold labeledA
      fun_prop
    have hp' := hp.differentiableAt (hopen.mem_nhds hx')
    rw [coordinateDerivative, firstIndex_directions]
    change fderiv ℝ (fun y => liftExtension a (f.val a) ((baseReindex (F := F)).symm y)) x
      (EuclideanSpace.single j 1) = _
    rw [flattened_differential a (f.val a) x hx' hp' j]
    have hdecoder := decoder_differential a (f.val a) x hx' j
    unfold covariantCoordinate
    have hxomega : (baseReindex (F := F)).symm x ∈ omega a := hx'
    simp only [liftExtension, dif_pos hxomega]
    exact hdecoder.symm

private theorem scalarBall_test (a : ActualChart (U := U) (H := H))
    (B : LocalBall (3 * d F)) (hB : InteriorBall a B) (f : S_U F ζ hζ U R P H) :
    (fun x => KPContActualSectorBallRestriction.scalarBall a B hB
      (KPContActualSectorTestEmbeddings.iota f) x) =ᵐ[volume.restrict B.carrier]
        (fun x => liftExtension a (f.val a) ((baseReindex (F := F)).symm x)) := by
  have hspec := (Classical.choose_spec (scalar_gluing f)).1
  have hcont : Continuous (scalarCovered f).val := by
    exact (continuous_iff F ζ hζ U R P H (scalarSections f)).mp
      (fun i => (hspec.1 i).continuous)
  let b : BorelL2Scalars F ζ hζ U R := ⟨scalarCovered f, hcont.measurable,
    KPContActualSectorTestEmbeddings.scalar_memLp f⟩
  have hb := sectorLineIsometry_representative F ζ hζ U R P H
    (KPContActualSectorTestEmbeddings.iota f) b (by rfl)
  have hae := KPContActualSectorBallRestriction.scalarBall_ae a B hB _
    (borelS F ζ hζ U R P H b) hb
  have hval : (borelS F ζ hζ U R P H b).val = scalarSections f := by
    change KPContSectorScalarLineAlgebra.S F ζ hζ U R P H (scalarCovered f) = _
    change KPContSectorScalarLineAlgebra.S F ζ hζ U R P H
      ((KPContSectorScalarLineAlgebra.S F ζ hζ U R P H).symm (scalarSections f)) = _
    exact (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H).apply_symm_apply _
  have hfields : sectionFields (scalarSections f) = f.val := hspec.2.2
  simpa only [KPContActualSectorCoordinateNullEquivalence.scalar, hval, hfields] using hae

private theorem index_cases {n : ℕ} (α : MultiIndex n 1) :
    α = zeroIndex n ∨ ∃ j, α = firstIndex j := by
  by_cases hz : ∀ j, (α.val j).val = 0
  · left
    apply Subtype.ext
    funext j
    exact Fin.ext (hz j)
  · obtain ⟨j, hj⟩ := not_forall.mp hz
    have hj1 : (α.val j).val = 1 := by
      have := (α.val j).isLt
      omega
    exact Or.inr ⟨j, index_one_eq_first α j hj1⟩

private theorem first_ne_zero {n : ℕ} (j : Fin n) : firstIndex j ≠ zeroIndex n := by
  intro he
  have h := congrArg (fun α : MultiIndex n 1 => (α.val j).val) he
  simp [firstIndex, zeroIndex] at h

private theorem first_injective {n : ℕ} : Function.Injective (firstIndex (n := n)) := by
  intro i j hij
  by_contra h
  have he := congrArg (fun α : MultiIndex n 1 => (α.val i).val) hij
  simp [firstIndex, Pi.single_apply, h] at he

 def ballDerivative (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F))
    (hB : InteriorBall a B) (α : MultiIndex (3 * d F) 1) :
    (KPContSectorClosedLpSubspace.H F ζ hζ R U × KPContActualSectorCotangentL2.V F ζ hζ U R P H)
      →L[ℂ] BallL2 B :=
  if h : ∃ j, α = firstIndex j then
    (KPContActualSectorBallRestriction.coordinateBall a B hB h.choose).comp
      (ContinuousLinearMap.snd ℂ _ _) else
    (KPContActualSectorBallRestriction.scalarBall a B hB).comp
      (ContinuousLinearMap.fst ℂ _ _)

private theorem ballDerivative_zero (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F))
    (hB : InteriorBall a B) (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (v : KPContActualSectorCotangentL2.V F ζ hζ U R P H) :
    ballDerivative a B hB (zeroIndex (3 * d F)) (u,v) =
      KPContActualSectorBallRestriction.scalarBall a B hB u := by
  have hn : ¬∃ j, zeroIndex (3 * d F) = firstIndex j := by
    rintro ⟨j,hj⟩
    exact first_ne_zero j hj.symm
  simp [ballDerivative, hn]

private theorem ballDerivative_first (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F))
    (hB : InteriorBall a B) (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (v : KPContActualSectorCotangentL2.V F ζ hζ U R P H) (j : Fin (3 * d F)) :
    ballDerivative a B hB (firstIndex j) (u,v) =
      KPContActualSectorBallRestriction.coordinateBall a B hB j v := by
  have he : ∃ i, firstIndex j = firstIndex i := ⟨j,rfl⟩
  simp only [ballDerivative, dif_pos he, ContinuousLinearMap.comp_apply]
  rw [← first_injective he.choose_spec]
  rfl

 theorem ballDerivative_test_weak (a : ActualChart (U := U) (H := H))
    (B : LocalBall (3 * d F)) (hB : InteriorBall a B) (f : S_U F ζ hζ U R P H)
    (α : MultiIndex (3 * d F) 1) :
    IsWeakDerivative B α
      (ballDerivative a B hB (zeroIndex (3 * d F))
        (KPContActualSectorTestEmbeddings.iota f, KPContActualSectorTestEmbeddings.j (D_U f)))
      (ballDerivative a B hB α
        (KPContActualSectorTestEmbeddings.iota f, KPContActualSectorTestEmbeddings.j (D_U f))) := by
  obtain ⟨h, hh0, hh1⟩ := test_smooth_local_data f a B hB
  have h0 : h.derivatives (zeroIndex (3 * d F)) =
      ballDerivative a B hB (zeroIndex (3 * d F))
        (KPContActualSectorTestEmbeddings.iota f, KPContActualSectorTestEmbeddings.j (D_U f)) := by
    rw [ballDerivative_zero]
    apply Lp.ext
    exact hh0.trans (scalarBall_test a B hB f).symm
  have ha : h.derivatives α = ballDerivative a B hB α
      (KPContActualSectorTestEmbeddings.iota f, KPContActualSectorTestEmbeddings.j (D_U f)) := by
    rcases index_cases α with rfl | ⟨j,rfl⟩
    · exact h0
    · rw [ballDerivative_first]
      apply Lp.ext
      exact (hh1 _ j (by simp [firstIndex])).trans
        (KPContActualSectorBallRestriction.coordinateBall_ae a B hB j _
          (KPContActualSectorTestEmbeddings.cotangentSquareFamily (D_U f)) rfl).symm
  have hw := h.weak_derivatives α
  change IsWeakDerivative B α (h.derivatives (zeroIndex (3 * d F))) (h.derivatives α) at hw
  rwa [h0, ha] at hw

abbrev CompactMultiplier :=
  {η : RealSmoothCutoff F ζ hζ U R P H // HasCompactSupport η.val}

variable (F ζ hζ)
variable (U R P H)
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

local notation "A" => KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization
local notation "Q" => KPContActualSectorFriedrichsSynthesis.formDomain F ζ hζ U R P H μG hμG hR realization

private theorem closedGradient_weak_chart (u : Q)
    (s : BorelL2Sections F ζ hζ U R P H) (r : SquareFiniteFamily (U := U) (H := H))
    (hs : sectorLineIsometry F ζ hζ U R P H (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) =
      mk F ζ hζ U R P H s)
    (hr : KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r = (A).closure u) :
    WeakChartData s r.val := by
  obtain ⟨fs, hfs, hgrad, -⟩ :=
    (kp_cont_actual_sector_friedrichs_synthesis F ζ hζ μG hμG U R hR P H realization).form_core u
  have hp := hfs.prodMk_nhds hgrad
  intro a B hB ε
  let c : ℂ := KPCuspGenuineMonodromy.chi F ζ hζ ε
  let v := (A).closure u
  have hweak : ∀ α, IsWeakDerivative B α
      (ballDerivative a B hB (zeroIndex (3 * d F)) (u.val,v))
      (ballDerivative a B hB α (u.val,v)) := by
    intro α
    apply weakDerivative_of_tendsto B α
      (fun m => ballDerivative a B hB (zeroIndex (3 * d F))
        (KPContActualSectorTestEmbeddings.iota (fs m), KPContActualSectorTestEmbeddings.j (D_U (fs m))))
      (fun m => ballDerivative a B hB α
        (KPContActualSectorTestEmbeddings.iota (fs m), KPContActualSectorTestEmbeddings.j (D_U (fs m))))
    · exact ((ballDerivative a B hB _).continuous.tendsto _).comp hp
    · exact ((ballDerivative a B hB α).continuous.tendsto _).comp hp
    · exact fun m => ballDerivative_test_weak a B hB (fs m) α
  let h : IntegerSobolev B 1 := ⟨fun α => c • ballDerivative a B hB α (u.val,v), by
    intro α
    exact weak_derivative_smul B α c _ _ (hweak α)⟩
  refine ⟨h, ?_, ?_⟩
  · have hz := ballDerivative_zero a B hB u.val v
    have heq := KPContActualSectorBallRestriction.scalarBall_ae a B hB u.val s hs
    filter_upwards [Lp.coeFn_smul c (ballDerivative a B hB (zeroIndex (3 * d F)) (u.val,v)), heq]
      with x hx he
    change (c • ballDerivative a B hB (zeroIndex (3 * d F)) (u.val,v)) x = _
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul, hz, he]
    rfl
  · intro α j hj
    have hα := index_one_eq_first α j hj
    have hf := ballDerivative_first a B hB u.val v j
    have heq := KPContActualSectorBallRestriction.coordinateBall_ae a B hB j v r hr
    filter_upwards [Lp.coeFn_smul c (ballDerivative a B hB α (u.val,v)), heq] with x hx he
    change (c • ballDerivative a B hB α (u.val,v)) x = _
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul, hα, hf, he]
    rfl

theorem closedGradient_isActualWeak (u : Q) :
    IsActualWeakGradient (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) ((A).closure u) := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep
    (sectorLineIsometry F ζ hζ U R P H (u : KPContSectorClosedLpSubspace.H F ζ hζ R U))
  change mk F ζ hζ U R P H s = _ at hs
  obtain ⟨r,hr⟩ := KPContActualSectorCotangentL2.ofFamily_surjective F ζ hζ U R P H ((A).closure u)
  exact ⟨s,r,hs.symm,hr,closedGradient_weak_chart F ζ hζ U R P H μG hμG hR realization u s r hs.symm hr⟩

theorem closedGradient_form_integral (u v : Q)
    (r s : SquareFiniteFamily (U := U) (H := H))
    (hr : KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r = (A).closure u)
    (hs : KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H s = (A).closure v) :
    closedGradientForm A u v = ∫ x, pair r.val s.val x
      ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P :=
  (kp_cont_actual_sector_cotangent_l2 F ζ hζ μG hμG U R hR P H realization).inner_integral
    _ _ r s hr hs

end DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization

end
