module
public import GS.Isometric.LocalProduct
public import GS.Isometric.ParamAtlas
@[expose] public section

/-! Push neighbourhoods through the local product, then through the open orbit
map. The kernel factor disappears. Thus every translated horizontal map is
open at its centre in the *inherited matrix topology*. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter GS.OverlapGeometry
open scoped Topology Manifold
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (r l : Layer 𝕜 n) (P : Square 𝕜 n)
local notation "H" => HorizontalModel r l P
local notation "K" => OrbitKernel r l P
local notation "G" => Factors r l
local notation "M" => MatrixOrbit r l P
local notation "d" => orbitDerivative r l P
local instance : NormedSpace ℝ H := Submodule.normedSpace _

def localParam (g : G) (v : H) : M := g • orbitMapToOrbit r l P (frames v.val)
lemma openParam (g : G) : map (localParam r l P g) (𝓝 0) = 𝓝 (orbitMapToOrbit r l P g) := by
  let q (k : G) := orbitMapToOrbit r l P (g*k)
  have h (z : H × K) : q (frames z.1.val * frames z.2.val) = localParam r l P g z.1 := by
    apply Subtype.ext
    change (g * (frames z.1.val * frames z.2.val)) • P = g • (frames z.1.val • P)
    rw [mul_smul,mul_smul,stabilizes _ _ z.2.property]
  rw [← show map Prod.fst (𝓝 (0:H×K)) = 𝓝 (0:H) from map_fst_nhds _,map_map,show localParam r l P g ∘ Prod.fst = q ∘ _ from funext fun z => (h z).symm,
    ← map_map,product_nhds]
  have op : IsOpenMap q := (orbitMapToOrbit_isOpenMap P).comp (isOpenMap_mul_left g)
  simpa [q] using! op.map_nhds_eq (x := 1) ((continuous_orbitMapToOrbit P).comp (continuous_const.mul continuous_id)).continuousAt

def orbitPatch (X : M) : ParamAt H X :=
  let g : G := X.property.choose
  let e := (actionLinearEquiv g).toContinuousLinearEquiv
  have hg : orbitMapToOrbit r l P g = X := Subtype.ext X.property.choose_spec
  { param := localParam r l P g
    centre := by rw [← hg]; apply Subtype.ext; change g • (frames 0 • P) = g • P; rw [frames_zero,one_smul]
    openAt := (openParam r l P g).trans (congrArg nhds hg)
    D := e.toContinuousLinearMap.comp (horizontalRestriction d)
    regular := .of_injective_of_finiteDimensional (e.injective.comp (splits d).injective)
    smooth := e.contDiff.comp (f := fun v : H => frames v.val • P) ((move_smooth (r := r) (l := l)).comp
      (f := fun v : H => (P,v.val)) (contDiff_const.prodMk (H).subtypeL.contDiff))
    deriv := by
      have hd : HasFDerivAt (fun v : H => frames v.val • P) (horizontalRestriction d) 0 :=
        (move_deriv P (r := r) (l := l)).comp (f := (H).subtypeL) 0 (H).subtypeL.hasFDerivAt
      exact e.hasFDerivAt.comp (f := fun v : H => frames v.val • P) 0 hd }

abbrev sharedOrbitChartedSpace := ParamAt.atlas (orbitPatch r l P)

lemma action_directions (g : G) : (pointDirections r l P).map (actionLinearEquiv g).toLinearMap = pointDirections r l (g • P) := by
  ext z; constructor
  · rintro ⟨v,hv,rfl⟩; exact action_mem_pointDirections g P v hv
  · intro hz; exact ⟨g⁻¹ • z,by change g⁻¹ • z ∈ pointDirections r l P; simpa only [inv_smul_smul] using action_mem_pointDirections g⁻¹ _ _ hz, smul_inv_smul g z⟩

lemma patch_range (X : M) : (orbitPatch r l P X).D.range = pointDirections r l X.val := by
  let g : G := X.property.choose
  have he : g • P = X.val := X.property.choose_spec
  rw [← he,← action_directions]
  change LinearMap.range ((actionLinearEquiv g).toLinearMap.comp ((d).toLinearMap.comp (H).subtype)) = _
  rw [LinearMap.range_comp,LinearMap.range_comp,Submodule.range_subtype,Submodule.map_eq_range_iff.mpr (horizontalComplement_isCompl d).codisjoint]
  rfl
end GS.Isometric
