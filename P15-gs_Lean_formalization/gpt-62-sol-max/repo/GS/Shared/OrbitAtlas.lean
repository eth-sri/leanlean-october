module

public import GS.Shared.FactorCharts
public import GS.OverlapGeometry.SliceAtlas
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Module.ContinuousInverse

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false
universe u

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix Set Filter GS.OverlapGeometry
open scoped Topology Manifold ContDiff
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {right left : Pattern 𝕜 n}

/-- The factor pair uses the product of the two full-target Cayley charts. -/
def pairChart (g : Factors right left) :
    OpenPartialHomeomorph (Factors right left) (PairGenerator right left) :=
  (factorPartialChart g.1).prod (factorPartialChart g.2)

@[simp] theorem pairChart_self_source (g : Factors right left) : g ∈ (pairChart g).source :=
  ⟨base_mem_factorSource g.1, base_mem_factorSource g.2⟩

/-- Smooth linear action of any fixed shared factor pair on ambient matrices. -/
theorem fixed_action_smooth (g : Factors right left) :
    ContDiff ℝ ⊤ (fun A : M 𝕜 n => g • A) :=
  (actionLinearEquiv g).toContinuousLinearEquiv.contDiff

/-- A fixed representative is used only to centre a chart.  No continuity
of this choice function is asserted or used. -/
def preferredFactor (P : M 𝕜 n) (X : MatrixOrbit right left P) : Factors right left :=
  Classical.choose X.property

@[simp] theorem preferredFactor_spec (P : M 𝕜 n) (X : MatrixOrbit right left P) :
    preferredFactor P X • P = X.val := Classical.choose_spec X.property

abbrev HorizontalModel (right left : Pattern 𝕜 n) (P : M 𝕜 n) :=
  horizontalComplement (orbitDerivative right left P)

section Factor
variable (s : Pattern 𝕜 n)
local notation "U" => (1 : Factor s)
local notation "R" => matrixReconstruct U
local notation "C" => factorCoordinates U

theorem factorProduct_smooth_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v w : E → Generator s} {x : E} (hv : ContDiffAt ℝ ⊤ v x) (hw : ContDiffAt ℝ ⊤ w x)
    (h₁ : v x = 0) (h₂ : w x = 0) :
    ContDiffAt ℝ ⊤ (fun y => C (R (v y) * R (w y))) x := by
  apply ContDiffAt.comp x (g := C) (f := fun y => R (v y) * R (w y))
  · simpa [h₁,h₂] using factorCoordinates_smooth_at U 1 (by simp)
  · fun_prop

end Factor

variable (right left : Pattern 𝕜 n) (P : M 𝕜 n)
local notation "H" => HorizontalModel right left P
local notation "K" => LinearMap.ker (ContinuousLinearMap.toLinearMap (orbitDerivative right left P))
local notation "V" => PairGenerator right left
local notation "eHK" => complementKernelEquiv (orbitDerivative right left P)
local instance : NormedSpace ℝ H := Submodule.normedSpace _
local instance : NormedSpace ℝ K := Submodule.normedSpace _

private def pairProduct (x : H × K) : Factors right left :=
  factorLift 1 x.1.val * factorLift 1 x.2.val

private def sliceProduct (x : H × K) : V :=
  pairChart 1 (pairProduct right left P x)

private theorem sliceProduct_smooth_zero : ContDiffAt ℝ ⊤ (sliceProduct right left P) 0 := by
  have h := (H).subtypeL.contDiff (n := ⊤) |>.contDiffAt.comp (0 : H × K) contDiffAt_fst
  have k := (K).subtypeL.contDiff (n := ⊤) |>.contDiffAt.comp (0 : H × K) contDiffAt_snd
  exact (factorProduct_smooth_at left h.fst k.fst rfl rfl).prodMk
    (factorProduct_smooth_at right h.snd k.snd rfl rfl)

private theorem hasFDerivAt_of_axes {E F : Type u} {G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E × F → G} {D : E × F →L[ℝ] G} (hd : DifferentiableAt ℝ f 0)
    (h₁ : f ∘ ContinuousLinearMap.inl ℝ E F = D ∘ ContinuousLinearMap.inl ℝ E F)
    (h₂ : f ∘ ContinuousLinearMap.inr ℝ E F = D ∘ ContinuousLinearMap.inr ℝ E F) :
    HasFDerivAt f D 0 := by
  have h {A : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
      (L : A →L[ℝ] E × F) (he : f ∘ L = D ∘ L) : (fderiv ℝ f 0).comp L = D.comp L := by
    simpa only [he, ← ContinuousLinearMap.coe_comp, ContinuousLinearMap.fderiv, map_zero] using
      (fderiv_comp (f := ⇑L) (g := f) (0 : A) (by simpa using hd) L.differentiableAt).symm
  exact hd.hasFDerivAt.congr_fderiv (ContinuousLinearMap.prod_ext (h _ h₁) (h _ h₂))

private theorem chart_lift (v : V) : pairChart 1 (factorLift 1 v) = v :=
  Prod.ext (factorCoordinates_reconstruct _ _) (factorCoordinates_reconstruct _ _)

/-- On either coordinate axis, the product map is the submodule inclusion. -/
private theorem sliceProduct_hasFDerivAt_zero :
    HasFDerivAt (sliceProduct right left P) (eHK : _ →L[ℝ] _) 0 := by
  apply hasFDerivAt_of_axes ((sliceProduct_smooth_zero right left P).differentiableAt (by simp)) <;>
    funext x <;> simp [sliceProduct, pairProduct, chart_lift, complementKernelEquiv]

/-- A local product decomposition into horizontal and stabilizing factors. -/
private def sliceProductChart :
    {f : OpenPartialHomeomorph (H × K) (Factors right left) //
      0 ∈ f.source ∧ EqOn f (pairProduct right left P) f.source} := by
  let c := pairChart (1 : Factors right left)
  have hs := sliceProduct_smooth_zero right left P
  have hd := sliceProduct_hasFDerivAt_zero right left P
  let e := hs.toOpenPartialHomeomorph _ hd (by simp)
  let f := (e.restrOpen (pairProduct right left P ⁻¹' c.source)
    (c.open_source.preimage (by unfold pairProduct; fun_prop))).trans c.symm
  refine ⟨f, ⟨⟨hs.mem_toOpenPartialHomeomorph_source hd (by simp), ?_⟩, ?_⟩, ?_⟩
  · change pairProduct right left P 0 ∈ c.source
    simp [pairProduct, c]
  · simp [c, pairChart, factorPartialChart]
  · exact fun z hz => c.left_inv hz.1.2

def horizontalValue (h : HorizontalModel right left P) : M 𝕜 n :=
  orbitParam (1 : Factors right left) P h.val

def horizontalPoint (h : HorizontalModel right left P) :
    MatrixOrbit right left P :=
  orbitMapToOrbit right left P (factorLift 1 h.val)

theorem horizontalValue_smooth : ContDiff ℝ ⊤ (horizontalValue right left P) := by
  unfold horizontalValue
  exact (orbitParam_smooth (1 : Factors right left)).comp₂
    (contDiff_const (c := P)) (H).subtypeL.contDiff

theorem horizontalValue_hasFDerivAt_zero :
    HasFDerivAt (horizontalValue right left P)
      (horizontalRestriction (orbitDerivative right left P)) 0 :=
  HasFDerivAt.comp (f := ⇑(HorizontalModel right left P).subtypeL) 0
    (orbitParam_hasFDerivAt_zero P) (HorizontalModel right left P).subtypeL.hasFDerivAt

/-- A slice whose parameters are the Cayley generators complementary to the stabilizer. -/
private def OrbitPatch (g : Factors right left) :=
  {s : SmoothSlice (E := HorizontalModel right left P) (MulAction.orbit (Factors right left) P) //
    0 ∈ s.target ∧ s.parametrization = fun h => g • horizontalPoint right left P h}

private theorem exists_orbitPatch (g : Factors right left) : Nonempty (OrbitPatch right left P g) := by
  let D := horizontalRestriction (orbitDerivative right left P)
  let v :=  horizontalValue right left P
  let patch := sliceProductChart right left P
  let f := patch.val
  obtain ⟨L,hL⟩ : D.HasLeftInverse :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional (horizontalRestriction_injective _)
  have hs : ContDiffAt ℝ ⊤ (L ∘ v) (0 : H) := (L.contDiff.comp (horizontalValue_smooth right left P)).contDiffAt
  have hc : L.comp D = (ContinuousLinearEquiv.refl ℝ H : H →L[ℝ] H) := ContinuousLinearMap.ext hL
  have hd := L.hasFDerivAt.comp 0 (horizontalValue_hasFDerivAt_zero right left P)
  change HasFDerivAt (L ∘ v) (L.comp D) 0 at hd
  rw [hc] at hd
  let e := hs.toOpenPartialHomeomorph (L ∘ v) hd (by simp)
  have h0 : 0 ∈ e.source := hs.mem_toOpenPartialHomeomorph_source hd (by simp)
  have he : ContDiffAt ℝ ⊤ e.symm ((L ∘ v) 0) := hs.to_localInverse hd (by simp)
  have hf : ∀ᶠ h : H in 𝓝 0, (h,(0 : K)) ∈ f.source :=
    (continuous_id.prodMk continuous_const).continuousAt.eventually
      (f.open_source.mem_nhds patch.property.1)
  obtain ⟨W,hW,ho,hz⟩ := mem_nhds_iff.mp <|
    Filter.Eventually.and (e.open_source.mem_nhds h0)
      ((hs.continuousAt.tendsto.eventually (he.eventually (by simp))).and hf)
  let S := f.source ∩ Prod.fst ⁻¹' W
  let q := orbitMapToOrbit right left P
  have hq (z : H × K) (hz : z ∈ f.source) : q (f z) = horizontalPoint right left P z.1 := by
    rw [patch.property.2 hz]
    apply Subtype.ext
    change (factorLift 1 z.1.val * factorLift 1 z.2.val) • P = factorLift 1 z.1.val • P
    rw [mul_smul, factorLift_stabilizes_of_kernel P _ z.2.property]
  have heq : q '' (f '' S) = horizontalPoint right left P '' W := by
    rw [image_image]
    refine image_congr (fun z hz => hq z hz.1) |>.trans ?_
    rw [← image_image]
    congr 1
    ext h
    exact ⟨by rintro ⟨z,hz,rfl⟩; exact hz.2, fun hh => ⟨(h,0),⟨(hW hh).2.2,hh⟩,rfl⟩⟩
  have hO := orbitMapToOrbit_isOpenMap P _
    (f.isOpen_image_of_subset_source (f.open_source.inter (ho.preimage continuous_fst)) inter_subset_left)
  rw [heq] at hO
  refine ⟨⟨{
    target := W
    parametrization h := g • horizontalPoint right left P h
    coordinates A := e.symm (L (g⁻¹ • A))
    open_target := ho
    open_source := by simpa only [image_image, Function.comp_def] using isOpenMap_smul g _ hO
    parametrization_smooth := (fixed_action_smooth g).comp (horizontalValue_smooth right left P)
    coordinates_smooth_at := ?_
    right_inverse := ?_ },hz,rfl⟩⟩
  · intro h hh
    apply ContDiffAt.comp _ _ (L.contDiff.comp (fixed_action_smooth g⁻¹)).contDiffAt
    change ContDiffAt ℝ ⊤ e.symm (L (g⁻¹ • (g • v h)))
    rw [inv_smul_smul]
    exact (hW hh).2.1
  · intro h hh
    exact (congrArg (e.symm ∘ L) (inv_smul_smul g (v h))).trans (e.left_inv (hW hh).1)

private def orbitPatch (g : Factors right left) : OrbitPatch right left P g :=
  Classical.choice (exists_orbitPatch right left P g)

@[no_expose] def preferredOrbitSlice (X : MatrixOrbit right left P) :
    SmoothSlice (E := HorizontalModel right left P) (MulAction.orbit (Factors right left) P) :=
  (orbitPatch right left P (preferredFactor P X)).val

private theorem preferredOrbitSlice_zero (X : MatrixOrbit right left P) :
    0 ∈ (preferredOrbitSlice right left P X).target ∧
    (preferredOrbitSlice right left P X).parametrization 0 = X := by
  let h := (orbitPatch right left P (preferredFactor P X)).property
  refine ⟨h.1, Subtype.ext ?_⟩
  change ((orbitPatch right left P (preferredFactor P X)).val.parametrization 0).val = _
  rw [h.2]
  change preferredFactor P X • horizontalValue right left P 0 = X.val
  simp only [horizontalValue, Submodule.coe_zero, orbitParam_zero, one_smul, preferredFactor_spec]

theorem preferredOrbitSlice_covers (X : MatrixOrbit right left P) :
    X ∈ (preferredOrbitSlice right left P X).source :=
  ⟨0, preferredOrbitSlice_zero right left P X⟩

/-- The shared orbit atlas in its original matrix-subtype topology.  This
is an explicit structure, not a global instance changing older geometries. -/
def sharedOrbitChartedSpace :
    ChartedSpace (HorizontalModel right left P) (MatrixOrbit right left P) :=
  sliceChartedSpace (preferredOrbitSlice right left P) (preferredOrbitSlice_covers right left P)

theorem sharedOrbitIsManifold :
    letI := sharedOrbitChartedSpace right left P
    IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤ (MatrixOrbit right left P) :=
  slice_isManifold (preferredOrbitSlice right left P) (preferredOrbitSlice_covers right left P)

theorem sharedOrbit_val_contMDiff :
    letI := sharedOrbitChartedSpace right left P
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, M 𝕜 n)) ⊤
      (fun X : MatrixOrbit right left P => X.val) :=
  slice_val_contMDiff (preferredOrbitSlice right left P) (preferredOrbitSlice_covers right left P)

local notation "O" => MatrixOrbit right left P
local instance : ChartedSpace H O := sharedOrbitChartedSpace right left P

def inclusionDifferential (X : O) : H →L[ℝ] M 𝕜 n :=
  mfderiv (𝓘(ℝ, H)) (𝓘(ℝ, M 𝕜 n)) (fun Y : O => Y.val) X

theorem inclusionDifferential_eq (X : O) :
    inclusionDifferential right left P X =
      (actionLinearEquiv (preferredFactor P X)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (horizontalRestriction (orbitDerivative right left P)) := by
  have h := slice_val_mfderiv_eq (preferredOrbitSlice right left P)
    (preferredOrbitSlice_covers right left P) X
  obtain ⟨hm,h0⟩ := preferredOrbitSlice_zero right left P X
  have hz := (preferredOrbitSlice right left P X).right_inverse 0 hm
  rw [h0] at hz
  rw [hz] at h
  change _ = fderiv ℝ (fun y => ((orbitPatch right left P (preferredFactor P X)).val.parametrization y).val) 0 at h
  rw [(orbitPatch right left P (preferredFactor P X)).property.2] at h
  exact h.trans (((actionLinearEquiv (preferredFactor P X)).toContinuousLinearEquiv.hasFDerivAt.comp 0
    (horizontalValue_hasFDerivAt_zero right left P)).fderiv)

theorem inclusionDifferential_injective (X : O) :
    Function.Injective (inclusionDifferential right left P X) := by
  rw [inclusionDifferential_eq]
  exact (actionLinearEquiv _).injective.comp (horizontalRestriction_injective _)

end GS.Shared
