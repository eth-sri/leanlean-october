/-
Fundamental groups of arbitrary two-cell attachments, after
Arthur Freitas Ramos, David Barros Hulak and Ruy Jose Guerra Barretto de Queiroz.
Released under Apache-2.0.
-/
module
public import Solution.Space
public import Solution.Transport

@[expose] public noncomputable section
namespace CellAttachment
open CategoryTheory Mark unitInterval Set
set_option backward.isDefEq.respectTransparency false
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {x : X}
  (A : ι → Leg (1 : Circle) x) {K : Type*} [TopologicalSpace K]
-- The whiskers and attaching maps constitute a single family of based maps.
local notation "f" => (fun i => Leg.map (A i))

abbrev baseLeg := Leg.ofMap (inclusion f) x
/-- Transfer the inclusion whisker to the disk side of the attaching square. -/
def diskPath (i : ι) := ((baseLeg A).comp (A i)).extend boundaryInclusion (characteristic f i)
  (by ext; exact (characteristic_boundary ..).symm)
abbrev cap (i) := Leg.mk (characteristic f i) (diskPath A i).1
abbrev relations := Subgroup.normalClosure (range fun i => (A i).loops circleGeneratorClass)
abbrev projection := QuotientGroup.mk' (relations A)
lemma rim_null (i) (g) : projection A ((A i).loops g) = 1 := by
  obtain ⟨n, rfl⟩ := circle_generated g
  rw [map_zpow, map_zpow, show projection A _ = 1 from
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (mem_range_self i)), one_zpow]

variable [PathConnectedSpace X]
/-- Pull the collar radially onto X. Only its restriction to the outer patch
is asserted to be continuous. -/
def radial := glue f id (fun i z => f i (angle z)) (fun i z => congrArg (f i) (Circle.exp_arg z))
/-- Mark a collar point by the whisker and then a path around its circle. -/
def outside (y : Space f) : Mark x := ⟨radial A y, visit f y
  (fun a => (pick x a).path) (fun i z _ => (A i).trail (angle z))⟩
/-- Coordinates after radial expansion in the actual quotient. -/
def total : C(Space f, Mark (inclusion f x)) :=
  ⟨fun y => ⟨movie f y 1, visit f y
    (baseLeg A).trail
    (fun i z _ => (cap A i).trail (expand (z, 1)))⟩,
   continuous_induced_rng.mpr (by fun_prop)⟩

def outer (p : C(K, Space f)) (h : ∀ t, p t ∈ patch f none) : C(K, Mark x) :=
  ⟨outside A ∘ p, continuous_induced_rng.mpr <|
    (cont_parts f (g := radial A) (patch f none) continuous_id.continuousOn
      fun i => (f i).continuous.comp_continuousOn angle_cont).comp_continuous p.continuous h⟩

lemma match_outer {y} (h : y ∈ patch f none) : total A y = (baseLeg A).act (outside A y) := by
  induction y using visit with
  | l => rfl
  | r i z hz =>
    simp [total, outside, hz]
    change (cap A i).act (pick _ (expand (z, 1))) = _
    erw [← Leg.comp_act _ _ (pick 1 (angle z)), ← (diskPath A i).2, Leg.comp_act, ← angle_spec h]
    exact congrArg (cap A i).act (congrArg (Mark.mk _) (Subsingleton.elim ..))

lemma small_range (p : C(I, Space f)) (k) (h : ∀ t, p t ∈ patch f k) :
    edge ((total A).comp p) ∈ (inclusionPi1 f x).range := by
  cases k with
  | none =>
    refine ⟨edge (outer A p h), ?_⟩
    rw [(baseLeg A).edge_act (outer A p h) (fun t => match_outer A (h t)), Leg.ofMap_loops]; rfl
  | some i =>
    obtain ⟨z, rfl⟩ := disk_lift f p h
    let d := expand.comp (z.prodMk (.const I 1))
    rw [(cap A i).edge_act ((pick _).comp d) (fun t => by simp [total, (h t).1, d]; rfl), Leg.loops_one]
    exact Subgroup.one_mem _

/-- The radial movie fixes X. Its time-one image therefore reads each loop in
the same homotopy class, and all its small edges come from the inclusion. -/
lemma onto : Function.Surjective (inclusionPi1 f x) := by
  rintro ⟨p⟩
  let s := total A
  have hh : Path.Homotopic.Quotient.mk p = move (endpoint.comp s) (.mk p) := Quotient.sound ⟨{
    toFun q := movie f (p q.2) q.1
    map_zero_left := by simp
    map_one_left := fun _ => rfl
    prop' := by rintro t a (rfl | rfl) <;> simp <;> rfl }⟩
  have hr := generated (patch_cover f) (small_range A)
    (primitive (s.comp p.toContinuousMap) (.id _))
  have base : (s (inclusion f x)).path = 𝟙 _ := by
    change 𝟙 _ ≫ move _ (pick x x).path = _
    simp; rfl
  erw [edge_path, Mark.read, base, ← hh, Category.id_comp, Category.comp_id] at hr
  exact hr

open scoped Classical in
/-- Only small edges need a label. The two prescriptions (transport in X,
resp. 1 inside a disk) agree when both apply. -/
def weight (p : C(I, Space f)) := if h : ∀ t, p t ∈ patch f none then
  projection A (edge (outer A p h)) else 1

/-- All chart labels are exact on a simply connected test domain (both the
initial interval and the little parameter squares will use this). -/
lemma flat [SimplyConnectedSpace K] (F : C(K, Space f)) (k) (h : ∀ t, F t ∈ patch f k) : Potential (weight A) F := by
  cases k with
  | none =>
    obtain ⟨v, hv⟩ := primitive (outer A F h) (projection A)
    exact ⟨v, fun e => (dite_eq_left (fun t => h (e t))).trans (hv e)⟩
  | some i =>
    -- In the overlap, the outer label comes from the attaching circle and
    -- is killed by the projection. All other interior edges already read 1.
    obtain ⟨z, rfl⟩ := disk_lift f F h
    refine ⟨fun _ => 1, fun e => ?_⟩
    rw [weight]; split_ifs with hu
    · let a : C(I, Circle) := ⟨_, angle_cont.comp_continuous (z.comp e).continuous hu⟩
      rw [(A i).edge_act ((pick 1).comp a) (fun t => by simp [outer, outside, (h (e t)).1, a]; rfl), rim_null]; simp
    · simp

/-- The quotient-valued weight reads an included loop modulo the relators.
A filling disk forces that reading to be trivial; conversely every actual
relator factors through its own characteristic disk. -/
lemma kernel : (inclusionPi1 f x).ker = relations A := by
  apply le_antisymm
  · rintro ⟨p⟩ hg
    obtain ⟨H⟩ := Path.Homotopic.Quotient.exact (q := .refl _) hg
    let F := (inclusion f).comp p.toContinuousMap
    have h (t) : F t ∈ patch f none := trivial
    have he := null_boundary (patch_cover f) H (flat A) (flat A F none h)
    apply (QuotientGroup.eq_one_iff _).mp
    change weight A F = 1 at he
    rw [weight, dite_eq_left h] at he
    change projection A (edge ((pick x).comp p.toContinuousMap)) = 1 at he
    erw [edge_path, Mark.read, pick_self, Category.id_comp, Category.comp_id] at he
    exact he
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    change FundamentalGroup.map _ _ _ = _
    rw [← Leg.ofMap_loops, ← Leg.comp_loops, ← (diskPath A i).2, Leg.comp_loops, Leg.loops_one]

/-- Attaching any family of two-cells imposes exactly the whiskered boundary loops. -/
theorem two_cell_attachment : completeStatement.{u, v} := by
  intro X _ _ ι attach x γ
  let A (i : ι) : Leg (1 : Circle) x := ⟨attach i, .mk (γ i)⟩
  have hs := onto A
  have hk := kernel A
  exact ⟨hs, hk, QuotientGroup.liftEquiv _ hs hk.symm, rfl⟩
end CellAttachment
