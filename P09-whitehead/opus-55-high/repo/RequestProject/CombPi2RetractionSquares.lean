import RequestProject.ComponentComplex
import RequestProject.ZeroPi2Descent


/-! Transfer vanishing through a commuting square whose target vertical
map admits a cellular left inverse. Pending final Lean verification. -/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
variable {X Y Z X' Y' : Complex2.{u}}

theorem zeroPi2_comp_left (g : Hom Y Z) (f : Hom X Y) (hz : ZeroPi2 f) :
    ZeroPi2 (g.comp f) := by
  intro x c hc
  have he : Finsupp.mapDomain (univLift X (g.comp f) x).onF c =
      Finsupp.mapDomain (univLift Y g _).onF
        (Finsupp.mapDomain (univLift X f x).onF c) := by
    rw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun F _ => (univLiftF_comp g f x F).symm
  have hz' := hz x c hc
  simp_all

theorem hom_retraction_square f (g : Hom X' Y')
    (a : Hom X X') (b : Hom Y Y') (r : Hom Y' Y)
    (hV : ∀ y, r.onV (b.onV y) = y)
    (hE : ∀ y, r.onE (b.onE y) = y)
    (hF : ∀ y, r.onF (b.onF y) = y)
    (hsq : b.comp f = g.comp a) : r.comp (g.comp a) = f := by
  rw [← hsq]
  apply Hom.ext'
  · exact funext (by tauto)
  · exact funext (by tauto)
  · exact funext (by tauto)

theorem zeroPi2_of_retraction_square f g
    (a : Hom X X') (b : Hom Y Y') (r : Hom Y' Y)
    (hV : ∀ y, r.onV (b.onV y) = y)
    (hE : ∀ y, r.onE (b.onE y) = y)
    (hF : ∀ y, r.onF (b.onF y) = y)
    (hsq : b.comp f = g.comp a) (hz : ZeroPi2 g) : ZeroPi2 f := by
  have H := zeroPi2_comp_left r _ (zeroPi2_comp_right g a hz)
  grind [hom_retraction_square f g a b r hV hE hF hsq]

theorem pi1Trivial_comp_right (g : Hom Y Z) (f : Hom X Y) (hz : Pi1Trivial g) :
    Pi1Trivial (g.comp f) := by
  intro x p hp
  simpa [mapPath_comp, Hom.comp, Function.comp_def] using hz _ _ (isPath_mapPath f hp)

theorem pi1Trivial_of_retraction_square f g
    (a : Hom X X') (b : Hom Y Y') (r : Hom Y' Y)
    (hV : ∀ y, r.onV (b.onV y) = y)
    (hE : ∀ y, r.onE (b.onE y) = y)
    (hF : ∀ y, r.onF (b.onF y) = y)
    (hsq : b.comp f = g.comp a) (hz : Pi1Trivial g) : Pi1Trivial f := by
  have H := Pi1Trivial.comp_left r (pi1Trivial_comp_right g a hz)
  grind [hom_retraction_square f g a b r hV hE hF hsq]
