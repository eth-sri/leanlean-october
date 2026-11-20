module

public import RequestProject.SurfaceCells
public import RequestProject.OrderCocycleFlatSections

@[expose] public section

/-! Extending a flat boundary section across the actual triangulated collar. -/
namespace FiniteChains.Comb.OrdCocycle
universe u v w
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  {Ω : Type w} [MulAction G Ω] (c : OrdCocycle P G) (s : P → Ω)

variable {a b d : P} (hab : a ≤ b) (hbd : b ≤ d)
include hab hbd

theorem flat_edge_trans
    (h₁ : c.val a b • s b = s a) (h₂ : c.val b d • s d = s b) :
    c.val a d • s d = s a := by
  rw [← c.comp hab hbd, mul_smul, h₂, h₁]

theorem flat_edge_of_top
    (h₁ : c.val a d • s d = s a) (h₂ : c.val b d • s d = s b) :
    c.val a b • s b = s a := by
  rw [← h₂, ← mul_smul, c.comp hab hbd, h₁]

theorem flat_edge_of_bottom
    (h₁ : c.val a b • s b = s a) (h₂ : c.val a d • s d = s a) :
    c.val b d • s d = s b := by
  calc
    c.val b d • s d = (c.val a b)⁻¹ • (c.val a d • s d) := by
      grind [c.comp, mul_smul, inv_smul_smul]
    _ = (c.val a b)⁻¹ • s a := by simp [h₂]
    _ = s b := by rw [← h₁, inv_smul_smul]

end FiniteChains.Comb.OrdCocycle

namespace FiniteChains.Davis.SurfaceSection
open RACG Mirror Comb Cell
universe u v w
variable {κ ι : Type u} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  {G : Type v} [Group G] {Ω : Type w} [MulAction G Ω]
  (c : OrdCocycle (SCell vc ec hc) G) (rv : κ → Ω) (re : ι → Ω)

def collarValue (p : Fin M) :=
  c.val (cW hc p) (cD hc p) • ((c.val (cV hc p) (cD hc p))⁻¹ • rv (vc p))

/-- Values on all actual surface cells. The centre is chosen after proving
that the collar data propagate consistently through the fan. -/
def surfaceSection (centre : Ω) : SCell vc ec hc → Ω
  | .vtx v => rv v
  | .bed e => re e
  | .cvx p => collarValue hc c rv p
  | .ced p => (c.val (cW hc p) (cF hc p))⁻¹ • collarValue hc c rv p
  | .dia p => (c.val (cV hc p) (cD hc p))⁻¹ • rv (vc p)
  | .gdi p => (c.val (cV hc p) (cG hc p))⁻¹ • rv (vc p)
  | .tr1 p => (c.val (cE hc p) (cT1 hc p))⁻¹ • re (ec p)
  | .tr2 p => (c.val (cV hc p) (cT2 hc p))⁻¹ • rv (vc p)
  | .ctr => centre
  | .rad p => (c.val (cC hc) (cR hc p))⁻¹ • centre
  | .inn p => (c.val (cC hc) (cI hc p))⁻¹ • centre

variable (k : Ω)

local notation "s" => surfaceSection hc c rv re k

variable (p : Fin M)

theorem v_d : c.val (cV hc p) (cD hc p) • s (cD hc p) = s (cV hc p) := by
  apply smul_inv_smul

theorem w_d : c.val (cW hc p) (cD hc p) • s (cD hc p) = s (cW hc p) := rfl

theorem v_g : c.val (cV hc p) (cG hc p) • s (cG hc p) = s (cV hc p) := by
  apply smul_inv_smul

theorem w_f : c.val (cW hc p) (cF hc p) • s (cF hc p) = s (cW hc p) := by
  apply smul_inv_smul

theorem e_t1 : c.val (cE hc p) (cT1 hc p) • s (cT1 hc p) = s (cE hc p) := by
  apply smul_inv_smul

theorem v_t2 : c.val (cV hc p) (cT2 hc p) • s (cT2 hc p) = s (cV hc p) := by
  apply smul_inv_smul

variable (hb : ∀ p : Fin M,
  c.val (cV hc p) (cE hc p) • re (ec p) = rv (vc p) ∧
  c.val (cV hc (p + 1)) (cE hc p) • re (ec p) = rv (vc (p + 1)))

variable (p : Fin M)

include hb in
theorem v_t1 : c.val (cV hc p) (cT1 hc p) • s (cT1 hc p) = s (cV hc p) :=
  c.flat_edge_trans s (cV_le_cE hc p) (cE_le_cT1 hc p)
    (hb p).1 (e_t1 hc c rv re k p)

include hb in
theorem v1_t1 :
    c.val (cV hc (p + 1)) (cT1 hc p) • s (cT1 hc p) = s (cV hc (p + 1)) :=
  c.flat_edge_trans s (cV1_le_cE hc p) (cE_le_cT1 hc p)
    (hb p).2 (e_t1 hc c rv re k p)

include hb in
theorem d1_t1 :
    c.val (cD hc (p + 1)) (cT1 hc p) • s (cT1 hc p) = s (cD hc (p + 1)) :=
  c.flat_edge_of_bottom s (cV_le_cD hc (p + 1)) (cD1_le_cT1 hc p)
    (v_d hc c rv re k (p + 1)) (v1_t1 hc c rv re k hb p)

include hb in
theorem w1_t1 :
    c.val (cW hc (p + 1)) (cT1 hc p) • s (cT1 hc p) = s (cW hc (p + 1)) :=
  c.flat_edge_trans s (cW_le_cD hc (p + 1)) (cD1_le_cT1 hc p)
    (w_d hc c rv re k (p + 1)) (d1_t1 hc c rv re k hb p)

include hb in
theorem g_t1 : c.val (cG hc p) (cT1 hc p) • s (cT1 hc p) = s (cG hc p) :=
  c.flat_edge_of_bottom s (cV_le_cG hc p) (cG_le_cT1 hc p)
    (v_g hc c rv re k p) (v_t1 hc c rv re k hb p)

include hb in
theorem w1_g :
    c.val (cW hc (p + 1)) (cG hc p) • s (cG hc p) = s (cW hc (p + 1)) :=
  c.flat_edge_of_top s (cW1_le_cG hc p) (cG_le_cT1 hc p)
    (w1_t1 hc c rv re k hb p) (g_t1 hc c rv re k hb p)

theorem d_t2 : c.val (cD hc p) (cT2 hc p) • s (cT2 hc p) = s (cD hc p) :=
  c.flat_edge_of_bottom s (cV_le_cD hc p) (cD_le_cT2 hc p)
    (v_d hc c rv re k p) (v_t2 hc c rv re k p)

theorem w_t2 : c.val (cW hc p) (cT2 hc p) • s (cT2 hc p) = s (cW hc p) :=
  c.flat_edge_trans s (cW_le_cD hc p) (cD_le_cT2 hc p)
    (w_d hc c rv re k p) (d_t2 hc c rv re k p)

theorem g_t2 : c.val (cG hc p) (cT2 hc p) • s (cT2 hc p) = s (cG hc p) :=
  c.flat_edge_of_bottom s (cV_le_cG hc p) (cG_le_cT2 hc p)
    (v_g hc c rv re k p) (v_t2 hc c rv re k p)

include hb in
theorem w1_t2 :
    c.val (cW hc (p + 1)) (cT2 hc p) • s (cT2 hc p) = s (cW hc (p + 1)) :=
  c.flat_edge_trans s (cW1_le_cG hc p) (cG_le_cT2 hc p)
    (w1_g hc c rv re k hb p) (g_t2 hc c rv re k p)

theorem f_t2 : c.val (cF hc p) (cT2 hc p) • s (cT2 hc p) = s (cF hc p) :=
  c.flat_edge_of_bottom s (cW_le_cF hc p) (cF_le_cT2 hc p)
    (w_f hc c rv re k p) (w_t2 hc c rv re k p)

include hb in
theorem w1_f :
    c.val (cW hc (p + 1)) (cF hc p) • s (cF hc p) = s (cW hc (p + 1)) :=
  c.flat_edge_of_top s (cW1_le_cF hc p) (cF_le_cT2 hc p)
    (w1_t2 hc c rv re k hb p) (f_t2 hc c rv re k p)

end FiniteChains.Davis.SurfaceSection
