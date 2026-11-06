module

public meta import Chazelle.Arithmetic

public import Chazelle.Mountain.Orientation
public import Chazelle.Chain.Sides

/-!
# Mirror symmetry (F-D7), part 1: the reflection `x ↦ -x` of points and polygons

The down phase handles a clockwise geometry polygon `Q` by working in its mirror image
`Q.mir` (vertices reflected in the vertical axis, same order), which is counterclockwise, and
carrying the results back (design `docs/design-downphase-driver.md` §8, F-D7).

* `mir p = (-p.1, p.2)`: an involutive isometry preserving heights;
* `Polygon.mir`: vertices, edges, boundary, simplicity (`mir_simple`), filled region
  (`mir_filled`, via the image of connected components), and the orientation flips
  (`leftInside_mir`);
* the local geometry: `lerp`, `offset` (the side flips), `det` (the sign flips), `sideCcw` (the
  arc of directions is traversed backwards: `sideCcw_mir`), `sideLeftOf`.
-/

namespace Chazelle.Core

namespace Mir

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Geometry (lerp)
open Chazelle.Jordan (offset nrm)

/-- **The reflection** in the vertical axis. -/
def mir (p : Point) : Point := (-p.1, p.2)

section
variable (p : Point)
@[simp] theorem mir_fst : (mir p).1 = -p.1 := rfl
@[simp] theorem mir_snd : (mir p).2 = p.2 := rfl

@[simp] theorem mir_mir : mir (mir p) = p := by
  aesop


end

theorem mir_injective : Function.Injective mir := fun p q h => by
  grind [mir_mir]

theorem mir_eq_iff {p q : Point} : mir p = q ↔ p = mir q := by
  constructor
  all_goals aesop

theorem mem_image_mir {A : Set Point} {x : Point} : x ∈ mir '' A ↔ mir x ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩; simp_all
  · intro h; exact ⟨mir x, h, mir_mir x⟩

theorem image_mir_image_mir (A : Set Point) : mir '' (mir '' A) = A := by
  grind [mem_image_mir, mir_mir]

theorem dist_mir (p q : Point) : dist (mir p) (mir q) = dist p q := by
  simp_all [Prod.dist_eq, Real.dist_eq, mir_fst, mir_snd, abs_neg] 

theorem continuous_mir : Continuous mir := by
  unfold mir; fun_prop

/-- The reflection as a homeomorphism. -/
def mirHomeo : Point ≃ₜ Point where
  toFun := mir
  invFun := mir
  left_inv := mir_mir
  right_inv := mir_mir
  continuous_toFun := continuous_mir
  continuous_invFun := continuous_mir


theorem image_connectedComponentIn_mir (A : Set Point) (x : Point) :
    mir '' connectedComponentIn A x = connectedComponentIn (mir '' A) (mir x) := by
  by_cases hx : x ∈ A
  · exact mirHomeo.image_connectedComponentIn hx
  grind [image_empty, connectedComponentIn_eq_empty, mem_image_mir, mir_mir]

theorem mir_lerp (a b : Point) (t : ℝ) : mir (lerp a b t) = lerp (mir a) (mir b) t := by
  grind [mir, lerp]

theorem mir_offset (u v : Point) (t δ : ℝ) :
    mir (offset u v t δ) = offset (mir u) (mir v) t (-δ) := by
  grind [mir_fst, mir_snd, Chazelle.Jordan.offset_fst, Chazelle.Jordan.offset_snd]

theorem mir_sub (p q : Point) : mir p - mir q = mir (p - q) := by
  simp_all [mir] <;> nlinarith

theorem mir_segment (a b : Point) : mir '' Chazelle.segment a b = Chazelle.segment (mir a) (mir b) := by
  ext x
  rw [mem_image_mir]
  constructor
  · rintro ⟨t, ht0, ht1, h⟩
    refine ⟨t, ht0, ht1, ?_⟩
    grind [mir]
  · rintro ⟨t, ht0, ht1, h⟩
    refine ⟨t, ht0, ht1, ?_⟩
    grind [mir]

/-! ## Polygons -/

/-- **The mirror image of a polygon** (same vertex order). -/
def _root_.Chazelle.Polygon.mir (P : Polygon) : Polygon := ⟨P.vertices.map Chazelle.Core.Mir.mir⟩

variable (P : Polygon)

@[simp] theorem mir_n : P.mir.n = P.n := by
  simp [Polygon.mir, Polygon.n]

theorem mir_vtx (i : ℕ) : P.mir.vtx i = mir (P.vtx i) := by
  grind [Polygon.mir, Polygon.vtx, List.getD_eq_getElem?_getD, List.getElem?_map, mir]

theorem mir_edge (i : ℕ) : P.mir.edge i = mir '' P.edge i := by
  grind [Polygon.edge, mir_segment, mir_n, mir_vtx]

theorem mir_boundary : P.mir.boundary = mir '' P.boundary := by
  ext x
  rw [mem_image_mir]
  constructor
  · rintro ⟨i, hi, hx⟩
    rw [mir_n] at hi
    rw [mir_edge, mem_image_mir] at hx
    exact ⟨i, hi, hx⟩
  · rintro ⟨i, hi, hx⟩
    refine ⟨i, by simp_all, ?_⟩
    grind [mir_edge, mem_image_mir]

theorem mir_commonEndpoints (i j : ℕ) :
    P.mir.commonEndpoints i j = mir '' P.commonEndpoints i j := by
  ext x
  rw [mem_image_mir]
  simp only [Polygon.commonEndpoints, mem_ofPred_eq, mir_n, mir_vtx, ← mir_eq_iff]

/-- **The mirror image of a simple polygon is simple.** -/
theorem mir_simple (hP : P.Simple) : P.mir.Simple := by
  obtain ⟨h3, hinj, hedge⟩ := hP
  refine ⟨by core_grind, fun i j hi hj h => ?_, fun i j hi hj hij => ?_⟩
  · rw [mir_n] at hi hj
    rw [mir_vtx, mir_vtx] at h
    exact hinj i j hi hj (mir_injective h)
  · rw [mir_n] at hi hj
    rw [mir_edge, mir_edge, ← image_inter mir_injective, hedge i j hi hj hij,
      mir_commonEndpoints]

theorem isBoundedSet_mir {A : Set Point} (h : IsBoundedSet A) : IsBoundedSet (mir '' A) := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R, fun p hp => ?_⟩
  rw [mem_image_mir] at hp
  have := hR _ hp
  simp_all

/-- **The filled region of the mirror image is the mirror image of the filled region.** -/
theorem mir_filled : P.mir.filled = mir '' P.filled := by
  have key : ∀ x : Point, IsBoundedSet (connectedComponentIn P.mir.boundaryᶜ x) ↔
      IsBoundedSet (connectedComponentIn P.boundaryᶜ (mir x)) := by
    intro x
    have e : connectedComponentIn P.mir.boundaryᶜ x =
        mir '' connectedComponentIn P.boundaryᶜ (mir x) := by
      rw [image_connectedComponentIn_mir, mir_mir, mir_boundary,
        image_compl_eq ⟨mir_injective, fun y => ⟨mir y, mir_mir y⟩⟩]
    rw [e]
    constructor
    · intro h
      have := isBoundedSet_mir h
      grind [image_mir_image_mir]
    · exact isBoundedSet_mir
  ext x
  rw [mem_image_mir]
  show x ∈ P.mir.boundary ∪ {p | IsBoundedSet (connectedComponentIn P.mir.boundaryᶜ p)} ↔
    mir x ∈ P.boundary ∪ {p | IsBoundedSet (connectedComponentIn P.boundaryᶜ p)}
  grind [mem_union, mem_ofPred_eq, mir_boundary, mem_image_mir]

/-- **The orientation flips.** -/
theorem leftInside_mir (hP : P.Simple) : Mountain.LeftInside P.mir ↔ ¬ Mountain.LeftInside P := by
  have hn := Chazelle.Jordan.simple_three_le hP
  have hev := Mountain.eventually_offset_orient hP (i := 0) (by omega) (t := 1 / 2)
    ⟨by norm_num, by norm_num⟩
  have e : ∀ δ : ℝ, Chazelle.Jordan.leftPoint P.mir 0 (1 / 2) δ ∈ P.mir.filled ↔
      offset (P.vtx 0) (P.vtx ((0 + 1) % P.n)) (1 / 2) (-δ) ∈ P.filled := by
    intro δ
    unfold Chazelle.Jordan.leftPoint
    rw [mir_filled, mem_image_mir, mir_n, mir_vtx, mir_vtx, ← neg_neg δ, ← mir_offset, mir_mir,
      neg_neg]
  have ho1 : Mountain.LeftInside P → Mountain.orient P = 1 := fun hL => by
    grind [Mountain.orient]
  have ho2 : ¬ Mountain.LeftInside P → Mountain.orient P = -1 := fun hL => by
    grind [Mountain.orient]
  unfold Mountain.LeftInside
  simp only [e]
  constructor
  · intro h hL
    have ho : Mountain.orient P = 1 := ho1 hL
    rw [ho] at hev
    obtain ⟨δ, h1, h2⟩ := (h.and hev).exists
    simp_all
  · intro hL
    have ho : Mountain.orient P = -1 := ho2 hL
    simp_all

end

end Mir

end Chazelle.Core
