import RequestProject.CombPi2


/-! An injective fundamental-group inclusion embeds its genuine universal-cover vertices. -/
namespace FiniteChains.Comb
universe u
variable {X Y : Complex2.{u}}

theorem univLiftV_deckV (f : Hom X Y) a g v :
    univLiftV a f (deckV g v) = deckV (pi1Map f a g) (univLiftV a f v) := by
  induction g using Quotient.ind with
  | _ p =>
    induction v using UV.ind with
    | h q =>
      change UV.mk (mapPathFrom a f (deckP p q)) =
        UV.mk (deckP ⟨mapPath f p.1, isPath_mapPath f p.2⟩ (mapPathFrom a f q))
      congr 1
      apply Subtype.ext
      exact mapPath_append f p.1 q.1

theorem deckV_free a g (v : UV X a)
    (h : deckV g v = v) : g = 1 := by
  obtain ⟨d, _, hu⟩ := (isRegular_univProj (X := X) (x₀ := a)).simply_transitive v v rfl
  exact (hu g h).trans (hu 1 (deckV_one v)).symm
