module

public import Chazelle.Golf

public import Chazelle.Core.ShootCutShK1M
public import Chazelle.Core.ShootCutOrig

/-!
# WP-G, part 50: the origin of a Lemma 3.6 query

A kind-1 piece is a set `S` of points of the chain `C` (`InC`: inside the box of `C`, not above
its top).  The ray-shooter queries the Lemma 3.6 structure of the piece from a **query origin**
(`QOrigin`) related to the origin `z` of the ray (`QRel`): the same symbolic point, or, for `z`
on the side of the box of `C` behind the ray, the point at the same height on the side of the
box of the piece's chain (`box_shift`).  Otherwise the piece has no hit: `z` on the side ahead of
the ray (`noHit_ahead_side`), above the top of `C` (`noHit_above`), or on the line of the top or
bottom of the box (`noHit_ext`).
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Geometry (lerp lerp_fst lerp_snd)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)

namespace ShootCut

/-- A point of the chain `C`: inside the box of `C` and not above the top of `C`. -/
def InC (C : Chain) (x : Point) : Prop := |x.1| < C.radius ∧ |x.2| < C.radius ∧ x.2 ≤ C.top.2

theorem inC_of_mem {C : Chain} {x : Point} (h : x ∈ C.set) : InC C x :=
  ⟨lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set h).1 C.coordBound_lt_radius,
    lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set h).2 C.coordBound_lt_radius,
    C.snd_le_top_of_mem_set h⟩

theorem conv_gt {lo a b t : ℝ} (ha : lo < a) (hb : lo < b) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    lo < (1 - t) * a + t * b := by
  rcases h0.lt_or_eq with h | h
  · nlinarith [mul_pos h (sub_pos.2 hb), mul_nonneg (sub_nonneg.2 h1) (sub_pos.2 ha).le]
  · subst h; simp; linarith

theorem conv_lt {hi a b t : ℝ} (ha : a < hi) (hb : b < hi) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (1 - t) * a + t * b < hi := by
  have := conv_gt (lo := -hi) (a := -a) (b := -b) (⟡) (by linarith) h0 h1
  linarith

/-- A segment between two points of `C` is in `InC C`. -/
theorem inC_seg {C : Chain} {a b x : Point} (ha : a ∈ C.set) (hb : b ∈ C.set)
    (hx : x ∈ Chazelle.segment a b) : InC C x := by
  have la := inC_of_mem ha
  have lb := inC_of_mem hb
  obtain ⟨t, h0, h1, rfl⟩ := hx
  simp only [InC] at la lb ⊢
  have e1 : a.1 + t * (b.1 - a.1) = (1 - t) * a.1 + t * b.1 := ⋆
  have e2 : a.2 + t * (b.2 - a.2) = (1 - t) * a.2 + t * b.2 := ⋆
  Ξ e1, e2
  obtain ⟨a1, a2, a3⟩ := la
  obtain ⟨b1, b2, b3⟩ := lb
  rw [abs_lt] at a1 a2 b1 b2 ⊢
  Ξ abs_lt
  refine ⟨⟨conv_gt a1.1 b1.1 h0 h1, conv_lt a1.2 b1.2 h0 h1⟩,
    ⟨conv_gt a2.1 b2.1 h0 h1, conv_lt a2.2 b2.2 h0 h1⟩, ⊞⟩

/-- **The points of a block of tour edges** are points of `C`. -/
theorem block_inC {C : Chain} {p₀ w : ℕ} (hw : 1 ≤ w) (hp6 : 6 ≤ p₀) (hp : p₀ + w ≤ 2 * C.m + 6)
    {x : Point} (hx : x ∈ (chainModel C).arcSet (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ)) : InC C x := by
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  obtain ⟨d, hd, hxd⟩ := (arcSet_nat (M := chainModel C) (p₀ := p₀) hw (⋄) x).1 hx
  have hv : ∀ q, 6 ≤ q → q ≤ 2 * C.m + 6 → (chainModel C).W.vtx q ∈ C.set := fun q h1 h2 => by
    obtain ⟨i, rfl⟩ : ∃ i, q = i + 6 := ⟨q - 6, ⋄⟩
    rw [SweepPrim.walk_vtx_tour C (⋄)]
    exact C.vertex_mem_set (C.sideIdx_le _ _)
  exact inC_seg (hv _ (⋄) (by omega)) (hv _ (by omega) (by omega)) hxd

variable {C : Chain} {S : Set Point} {z : Point} {σ : ℝ}

/-- **No hit from the side of the box ahead of the ray.** -/
theorem noHit_ahead_side (hσ : σ = 1 ∨ σ = -1) (hz : z.1 = σ * C.radius)
    (hS : ∀ x ∈ S, InC C x) : NoHit S z σ := fun t ht hm => by
  have h := (hS _ hm).1
  simp only [rayPt_fst, hz] at h
  rw [abs_lt] at h
  rcases hσ with rfl | rfl <;> [linarith [h.2]; linarith [h.1]]

/-- **No hit above the top of `C`.** -/
theorem noHit_above (hz : C.top.2 < z.2) (hS : ∀ x ∈ S, InC C x) : NoHit S z σ :=
  fun t _ hm => by
    have h := (hS _ hm).2.2
    simp only [rayPt_snd] at h
    linarith

/-- **No hit on the line of the top or of the bottom of the box.** -/
theorem noHit_ext (hz : C.radius ≤ |z.2|) (hS : ∀ x ∈ S, InC C x) : NoHit S z σ :=
  fun t _ hm => by
    have h := (hS _ hm).2.1
    simp only [rayPt_snd] at h
    linarith

/-- **Shifting the origin along the side of the box behind the ray.** -/
theorem box_shift (hσ : σ = 1 ∨ σ = -1) {R R' : ℝ} {z' : Point} (hz : z.1 = -σ * R)
    (hz' : z'.1 = -σ * R') (hy : z.2 = z'.2) (hS : ∀ x ∈ S, |x.1| < R ∧ |x.1| < R') :
    (∀ t', FirstHit S z' σ t' → FirstHit S z σ (t' + σ * (z'.1 - z.1))) ∧
      (NoHit S z' σ → NoHit S z σ) := by
  refine firstHit_shift hσ hy fun x hx _ => ?_
  have h := hS x hx
  simp only [abs_lt] at h
  Ξ hz, hz'
  rcases hσ with rfl | rfl
  · constructor <;> linarith [h.1.1, h.2.1]
  · constructor <;> linarith [h.1.2, h.2.2]

/-- **The relation of a query origin to the origin of the ray.** -/
def QRel (P : Polygon) (C : Chain) (σ : ℝ) (z : Point) : QOrigin → Prop
  | .sym s => s.eval (Qof P) = z
  | .box h => z = (-σ * C.radius, ((Qof P).vtx h).2)

/-- **The answer of a query** for the origin of the ray, from the answer for a related query
origin. -/
theorem query_transfer {P : Polygon} (hσ : σ = 1 ∨ σ = -1) {Cα : Chain} {o : QOrigin}
    (hrel : QRel P C σ z o) (hS : S ⊆ Cα.set) (hSC : ∀ x ∈ S, InC C x) :
    (∀ t', FirstHit S (o.eval (Qof P) Cα σ) σ t' →
      FirstHit S z σ (σ * ((rayPt (o.eval (Qof P) Cα σ) σ t').1 - z.1)) ∧
        rayPt z σ (σ * ((rayPt (o.eval (Qof P) Cα σ) σ t').1 - z.1)) =
          rayPt (o.eval (Qof P) Cα σ) σ t') ∧
      (NoHit S (o.eval (Qof P) Cα σ) σ → NoHit S z σ) := by
  have hσ2 := sigma_sq hσ
  cases o with
  | sym s =>
    simp only [QRel] at hrel
    simp only [QOrigin.eval, hrel]
    refine ⟨fun t' ht' => ?_, id⟩
    have : σ * ((rayPt z σ t').1 - z.1) = t' := by
      rw [rayPt_fst]; ring_nf; rw [show σ ^ 2 = σ * σ by ring, hσ2]; ring
    rw [this]; exact ⟨ht', rfl⟩
  | box h =>
    simp only [QRel] at hrel
    simp only [QOrigin.eval]
    have hsh := box_shift (S := S) (z := z) hσ (R := C.radius) (R' := Cα.radius)
      (z' := (-σ * Cα.radius, ((Qof P).vtx h).2)) (by rw [hrel]) rfl (by rw [hrel])
      (fun x hx => ⟨(hSC x hx).1, (Cα.set_subset_box (hS hx)).1⟩)
    refine ⟨fun t' ht' => ?_, hsh.2⟩
    have hf := hsh.1 t' ht'
    have e : σ * ((rayPt (-σ * Cα.radius, ((Qof P).vtx h).2) σ t').1 - z.1) =
        t' + σ * ((-σ * Cα.radius, ((Qof P).vtx h).2).1 - z.1) := by
      rw [rayPt_fst]; ring_nf; rw [show σ ^ 2 = σ * σ by ring, hσ2]; ring
    rw [e]
    refine ⟨hf, ?_⟩
    ext
    · simp only [rayPt_fst]; linear_combination (-σ * Cα.radius - z.1) * hσ2
    · simp only [rayPt_snd]; rw [hrel]

end ShootCut

end

end Chazelle.Core
