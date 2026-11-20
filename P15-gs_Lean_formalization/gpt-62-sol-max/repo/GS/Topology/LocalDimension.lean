module

public import GS.NonmanifoldFinal.EuclideanTransport

public import GS.Topology.SectionPair

public import GS.Topology.SphereVolume

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

public import Mathlib.Analysis.Convex.Contractible

@[expose] public section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Set Topology ContinuousMap GS.NonmanifoldFinal GS.NonmanifoldObstruction
namespace GS.Topology

variable {X : Type*} [TopologicalSpace X]

/-- Polar coordinates split the punctured space into a sphere and a contractible ray. -/
def puncturedEuclidean (n : ℕ) : ({0}ᶜ : Set (Eucl n)) ≃ₕ UnitSphere (Fin n) := by
  letI : ContractibleSpace (Ioi (0 : ℝ)) := (convex_Ioi _).contractibleSpace ⟨1, by simp⟩
  exact (homeomorphUnitSphereProd _).toHomotopyEquiv.trans
    (((HomotopyEquiv.refl _).prodCongr (Classical.choice (ContractibleSpace.hequiv_unit _))).trans
      (Homeomorph.prodUnique _ Unit).toHomotopyEquiv)

/-- A sphere that retracts off a space of the homotopy type of another sphere
has the same dimension. -/
theorem dimension_of_punctured_retract {m n : ℕ} (h : X ≃ₕ UnitSphere (Fin n))
    (p : ContinuousSectionPair (UnitSphere (Fin m)) X) : n = m := by
  let a := p.sectionMap
  let b := p.retractionMap
  let s := h.toFun.comp a
  let t := b.comp h.invFun
  have hb : b.comp a = ContinuousMap.id _ := ContinuousMap.ext p.retraction_section
  have hid : (t.comp s).Homotopic (ContinuousMap.id _) := by
    have h' := (.refl b : b.Homotopic b).comp (h.left_inv.comp (.refl a))
    simpa only [s,t,ContinuousMap.comp_assoc, ContinuousMap.id_comp, hb] using h'
  by_contra hne
  have hn : (t.comp s).Nullhomotopic := by
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · exact (sphereMap_nullhomotopic_of_finrank_lt (by simpa using hnm) t).comp_left s
    · exact (sphereMap_nullhomotopic_of_finrank_lt (by simpa using hmn) s).comp_right t
  obtain ⟨z,hz⟩ := hn
  exact sphere_id_not_nullhomotopic ⟨z,hid.symm.trans hz⟩

/-- Puncturing a partial homeomorphism at a point preserves its actual open sets. -/
def puncturedChart {Y : Type*} [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    (x : X) (hx : x ∈ e.source) : PuncturedIn e.source x ≃ₜ PuncturedIn e.target (e x) :=
  (subtypeOpenIntersection _ {x}ᶜ).symm.trans
    ((e.toHomeomorphSourceTarget.subtype (fun z => not_congr <|
      ⟨congrArg e, fun hz => e.injOn z.property hx hz⟩)).trans (subtypeOpenIntersection _ {e x}ᶜ))

/-- Restrict a chart to an arbitrarily small ball, then replace the ball by all
of Euclidean space, sending the marked point to zero. -/
theorem exists_centered_partial {n : ℕ} (e : OpenPartialHomeomorph X (Eucl n))
    (x : X) (hx : x ∈ e.source) :
    ∃ d : OpenPartialHomeomorph X (Eucl n), x ∈ d.source ∧ d.source ⊆ e.source ∧
      d.target = univ ∧ d x = 0 := by
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hx))
  let b : OpenPartialHomeomorph (Eucl n) (Eucl n) := OpenPartialHomeomorph.univBall (e x) r
  have ht : b.target = Metric.ball (e x) r := OpenPartialHomeomorph.univBall_target (E := Eucl n) _ hr
  have h0 : e x ∈ b.target := by rw [ht]; exact Metric.mem_ball_self hr
  have hsub : b.target ⊆ e.target := ht ▸ hrsub
  refine ⟨e.trans b.symm, ⟨hx,h0⟩, fun _ h => h.1, ?_, ?_⟩
  · change b.source ∩ b ⁻¹' e.target = univ
    exact (inter_eq_left.mpr (show b.source ⊆ b ⁻¹' e.target from fun _ hy =>
      hsub (b.map_source hy))).trans (OpenPartialHomeomorph.univBall_source (E := Eucl n) _ _)
  aesop

end GS.Topology

namespace GS.UnitaryTopology

structure IsolatedEuclideanRetract (X : Type*) [TopologicalSpace X]
    (x₀ : X) (m : ℕ) extends ContinuousSectionPair (Eucl m) X where
  section_zero : sectionMap 0 = x₀
  projection_zero_iff : ∀ x, retractionMap x = 0 ↔ x = x₀

variable {X : Type*} [TopologicalSpace X] {x₀ : X} {m : ℕ}

theorem IsolatedEuclideanRetract.punctured_sphere
    (r : IsolatedEuclideanRetract X x₀ m)
    (U : Set X) (hU : IsOpen U) (hx : x₀ ∈ U) :
    Nonempty (ContinuousSectionPair (UnitSphere (Fin m)) (PuncturedIn U x₀)) := by
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
    ((hU.preimage r.sectionMap.continuous).mem_nhds (show r.sectionMap 0 ∈ U by rwa [r.section_zero]))
  let t := δ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hnorm (v : UnitSphere (Fin m)) : ‖t • v.val‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht,
      mem_sphere_zero_iff_norm.mp v.property, mul_one]
  have hne (v : UnitSphere (Fin m)) : r.sectionMap (t • v.val) ≠ x₀ := by
    intro h
    have he := (r.projection_zero_iff _).mpr h
    rw [r.retraction_section, ← norm_eq_zero, hnorm] at he
    exact ht.ne' he
  let s (v : UnitSphere (Fin m)) : PuncturedIn U x₀ :=
    ⟨r.sectionMap (t • v.val), hball (by aesop), hne v⟩
  let p : C(PuncturedIn U x₀, Eucl m) := ⟨r.retractionMap ∘ Subtype.val,
    r.retractionMap.continuous.comp continuous_subtype_val⟩
  let ret := GS.Topology.sphereNormalize p fun v => mt (r.projection_zero_iff v.val).mp v.property.2
  refine ⟨⟨⟨s, (r.sectionMap.continuous.comp (continuous_subtype_val.const_smul t)).subtype_mk _⟩,
    ret, fun v => Subtype.ext ?_⟩⟩
  change NormedSpace.normalize (r.retractionMap (r.sectionMap (t • v.val))) = v.val
  rw [r.retraction_section, NormedSpace.normalize_smul_of_pos ht]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp v.property)

end GS.UnitaryTopology

namespace GS.Topology
variable {X : Type*} [TopologicalSpace X]

/-- A Euclidean chart has a small sphere retract in any punctured open neighbourhood. -/
theorem normSphere_retract_open' {n : ℕ} (U : Set (Eucl n)) (hU : IsOpen U)
    (y : Eucl n) (hy : y ∈ U) : Nonempty (ContinuousSectionPair (UnitSphere (Fin n)) (PuncturedIn U y)) :=
  (GS.UnitaryTopology.IsolatedEuclideanRetract.mk (x₀ := y) (m := n)
    ⟨⟨(y + ·), by fun_prop⟩, ⟨(· - y), by fun_prop⟩, by simp⟩ (by simp) (fun _ => sub_eq_zero)).punctured_sphere U hU hy

abbrev SphereGerm (O : Set X) (x : X) (m : ℕ) :=
  ∀ U : Set X, IsOpen U → x ∈ U → U ⊆ O →
    Nonempty (ContinuousSectionPair (UnitSphere (Fin m)) (PuncturedIn U x))

theorem openChart_sphereGerm {n : ℕ} (e : OpenPartialHomeomorph X (Eucl n)) (x : X) :
    SphereGerm e.source x n := by
  intro U hU hxU hsub
  let d := e.restrOpen U hU
  have hD : d.source = U := inter_eq_right.mpr hsub
  have hxD : x ∈ d.source := hD ▸ hxU
  obtain ⟨p⟩ := normSphere_retract_open' d.target d.open_target (d x) (d.map_source hxD)
  exact ⟨transportSectionPair p ((puncturedChart d x hxD).symm.trans
    (Homeomorph.setCongr (by simp [hD])))⟩

/-- The dimension of a Euclidean chart is detected by the punctured germs. -/
theorem local_dimension {m n : ℕ} (e : OpenPartialHomeomorph X (Eucl n))
    (x : X) (hx : x ∈ e.source) (hret : SphereGerm e.source x m) : n = m := by
  obtain ⟨d,hd,hsub,ht,hz⟩ := exists_centered_partial e x hx
  obtain ⟨p⟩ := hret d.source d.open_source hd hsub
  let h : PuncturedIn d.source x ≃ₜ ({0}ᶜ : Set (Eucl n)) :=
    (puncturedChart d x hd).trans (Homeomorph.setCongr (by aesop))
  exact dimension_of_punctured_retract (h.toHomotopyEquiv.trans (puncturedEuclidean n)) p

end GS.Topology
