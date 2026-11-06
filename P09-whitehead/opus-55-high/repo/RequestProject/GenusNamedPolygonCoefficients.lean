import RequestProject.GenusNamedSurfaceCover
import RequestProject.SurfaceCoverPolygonEquivariance
import RequestProject.OrderUniversalDeck
import RequestProject.Tac


/-!
Actual group-ring polygon coefficients for the named quotient's surface cover.
The pole-fibre parametrization is proved from regularity of the genuine
universal cover. No group-faithfulness or sheet-parametrization premise is used.

Written proof terms; no Lean verification has been run.
-/
noncomputable section
open scoped Classical
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

abbrev NamedPolygonDeckGroup :=
  Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)

/-- The genuine deck action on the first coordinate of the actual surface
pullback cover; the surface cell itself remains fixed. -/
def namedSurfaceDeck (g : NamedPolygonDeckGroup ρ q u) :
    NamedSurfaceCover ρ q u ≃o NamedSurfaceCover ρ q u where
  toFun p := ⟨(uOrderDeck g p.1.1, p.1.2), (uOrderDeck_end g p.1.1).trans p.2⟩
  invFun p := ⟨(uOrderDeck g⁻¹ p.1.1, p.1.2), (uOrderDeck_end g⁻¹ p.1.1).trans p.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change deckV g⁻¹ (deckV g p.1.1) = p.1.1
      rw [← deckV_mul, inv_mul_cancel, deckV_one]
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change deckV g (deckV g⁻¹ p.1.1) = p.1.1
      rw [← deckV_mul, mul_inv_cancel, deckV_one]
    · rfl
  map_rel_iff' {p r} := and_congr (uOrderDeckOrderIso g).map_rel_iff Iff.rfl

@[simp] theorem namedSurfaceDeck_projection g
    p :
    namedSurfaceProjection ρ q u (namedSurfaceDeck ρ q u g p) =
      namedSurfaceProjection ρ q u p := rfl

@[simp] theorem namedSurfaceDeck_one p :
    namedSurfaceDeck ρ q u 1 p = p := by
  apply Subtype.ext
  exact Prod.ext (deckV_one p.1.1) rfl

theorem namedSurfaceDeck_mul g h
    p :
    namedSurfaceDeck ρ q u (g * h) p =
      namedSurfaceDeck ρ q u g (namedSurfaceDeck ρ q u h p) := by
  apply Subtype.ext
  exact Prod.ext (deckV_mul g h p.1.1) rfl

abbrev NamedPolygonPole := PolygonCoverPole _ (namedSurfaceProjection ρ q u)

/-- One actual pole lift, chosen from the proved surjectivity of the actual
surface projection. -/
def namedPolygonPole : NamedPolygonPole ρ q u :=
  ⟨Classical.choose ((namedSurfaceProjection_isPosetCover ρ q u).surj (cC (gc q))),
    by grind⟩

def namedPolygonPoleOrbit (g : NamedPolygonDeckGroup ρ q u) : NamedPolygonPole ρ q u :=
  ⟨namedSurfaceDeck ρ q u g (namedPolygonPole ρ q u).1, (namedPolygonPole ρ q u).2⟩

/-- Regularity applies on the exact original universal-cover endpoint fibre;
the pullback's surface coordinate is fixed at the polygon centre. -/
theorem namedPolygonPoleOrbit_bijective :
    Function.Bijective (namedPolygonPoleOrbit ρ q u) := by
  constructor
  · intro g h he
    have hfirst := congrArg (·.1.1.1) he
    obtain ⟨d, _, hd⟩ := (isRegular_univProj
      (X := orderCx (namedQuotientPos ρ q u)) (x₀ := namedQuotientBase ρ q u)).simply_transitive
      _
      _
      (endV_deckV g _).symm
    exact (hd g rfl).trans (hd h hfirst.symm).symm
  · intro v
    let v₀ := namedPolygonPole ρ q u
    have hcell : v₀.1.1.2 = v.1.1.2 := v₀.2.trans v.2.symm
    have hend : uOrderEnd v₀.1.1.1 = uOrderEnd v.1.1.1 :=
      by grind
    obtain ⟨g, hg, _⟩ := (isRegular_univProj
      (X := orderCx (namedQuotientPos ρ q u)) (x₀ := namedQuotientBase ρ q u)).simply_transitive
      v₀.1.1.1 v.1.1.1 hend
    refine ⟨g, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hg hcell

/-- The actual quotient fundamental group, rather than any hypothesized block
embedding, indexes the complete pole fibre. -/
def namedPolygonPoleEquiv :=
  Equiv.ofBijective _ (namedPolygonPoleOrbit_bijective ρ q u)

@[simp] theorem namedPolygonPoleEquiv_apply g :
    (namedPolygonPoleEquiv ρ q u g).1 =
      namedSurfaceDeck ρ q u g (namedPolygonPole ρ q u).1 := rfl

@[simp] theorem namedPolygonPoleEquiv_one :
    namedPolygonPoleEquiv ρ q u 1 = namedPolygonPole ρ q u := by
  apply Subtype.ext
  exact namedSurfaceDeck_one ρ q u _

def namedPolygonFilling :=
  polygonCoverFilling _ _
    (namedSurfaceProjection_isPosetCover ρ q u) (namedPolygonPole ρ q u)

/-- The actual group-ring action obtained from the actual quotient deck maps. -/
def namedPolygonMultiple : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u) →ₗ[ℤ]
    (StrictOrdTri (NamedSurfaceCover ρ q u) →₀ ℤ) :=
  (Finsupp.linearCombination ℤ (fun g => chain2
    (strictOrderCxMap _ (namedSurfaceDeck ρ q u g).strictMono)
    (namedPolygonFilling ρ q u))).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

/-- Rebase the actual sheet coordinates at any prescribed actual pole. This
allows the reference pole to be transported from the pre-substitution cover. -/
def namedPolygonPoleEquivAt (v : NamedPolygonPole ρ q u) :=
  (Equiv.mulRight ((namedPolygonPoleEquiv ρ q u).symm v)).trans
    (namedPolygonPoleEquiv ρ q u)

theorem namedPolygonPoleEquivAt_apply v
    g :
    (namedPolygonPoleEquivAt ρ q u v g).1 = namedSurfaceDeck ρ q u g v.1 := by
  change (namedPolygonPoleEquiv ρ q u (g * (namedPolygonPoleEquiv ρ q u).symm v)).1 = _
  rw [namedPolygonPoleEquiv_apply, namedSurfaceDeck_mul]
  have he := congrArg Subtype.val ((namedPolygonPoleEquiv ρ q u).apply_symm_apply v)
  tauto

@[simp] theorem namedPolygonPoleEquivAt_one v :
    namedPolygonPoleEquivAt ρ q u v 1 = v := by
  apply Subtype.ext
  rw [namedPolygonPoleEquivAt_apply, namedSurfaceDeck_one]

def namedPolygonCoefficientAt (v : NamedPolygonPole ρ q u)
    (c : StrictOrdTri (NamedSurfaceCover ρ q u) →₀ ℤ) :=
  polygonCoverGroupCoefficient _ _
    (namedSurfaceProjection_isPosetCover ρ q u) (namedPolygonPoleEquivAt ρ q u v).symm c

def namedPolygonFillingAt (v : NamedPolygonPole ρ q u) :=
  polygonCoverFilling _ _
    (namedSurfaceProjection_isPosetCover ρ q u) v

def namedPolygonMultipleAt (v : NamedPolygonPole ρ q u) :
    MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u) →ₗ[ℤ]
      (StrictOrdTri (NamedSurfaceCover ρ q u) →₀ ℤ) :=
  (Finsupp.linearCombination ℤ (fun g => chain2
    (strictOrderCxMap _ (namedSurfaceDeck ρ q u g).strictMono)
    (namedPolygonFillingAt ρ q u v))).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

/-- The actual scalar reconstruction can be based at the particular pole
arising from the chosen pre-substitution geometric reference. -/
theorem namedPolygon_reconstruct_at_pole v
    c
    (hrel : PolygonRelativeChain (gc q) (namedSurfaceProjection ρ q u) c) :
    c = namedPolygonMultipleAt ρ q u v (namedPolygonCoefficientAt ρ q u v c) :=
  polygonRelative_eq_deck_sum _ _
    _ (genus_polygonData q)
    _ (namedSurfaceDeck_projection ρ q u)
    v _ (namedPolygonPoleEquivAt_apply ρ q u v) c hrel
