import RequestProject.Pi2GenerationDescent
import RequestProject.Tac


/-! Change the base vertex in an actual spherical generation statement.
Both directions are genuine universal-cover path transports. Unverified source. -/

bwd

namespace FiniteChains.Comb
universe u
variable {X : Complex2.{u}} {x y : X.V} {p : List (X.E × Bool)}

theorem shiftV_reverse_cancel (hp : IsPathX X p x y) v :
    shiftV hp (shiftV (isPath_revPath hp) v) = v := by
  induction v using UV.ind with
  | h q =>
      apply Quotient.sound
      change Htpy X x (endpt X x (shiftP hp (shiftP (isPath_revPath hp) q)).val)
        (p ++ (revPath p ++ q.val)) q.val
      rw [endpt_shiftP, endpt_shiftP]
      have h := Htpy.append_congr (hp.append (isPath_revPath hp)) q.property
        (htpy_append_revPath hp) (Htpy.refl q.val)
      simp_all

theorem shiftF_reverse_cancel (hp : IsPathX X p x y) f :
    shiftF hp (shiftF (isPath_revPath hp) f) = f :=
  Subtype.ext (Prod.ext (shiftV_reverse_cancel hp f.val.1) rfl)

theorem chain2_shift_reverse_cancel (hp : IsPathX X p x y) (c : UF X x →₀ ℤ) :
    chain2 (shiftHom hp) (chain2 (shiftHom (isPath_revPath hp)) c) = c := by
  change Finsupp.mapDomain (shiftF hp) (Finsupp.mapDomain (shiftF (isPath_revPath hp)) c) = c
  rw [← Finsupp.mapDomain_comp]
  have hf : shiftF hp ∘ shiftF (isPath_revPath hp) = id := funext (shiftF_reverse_cancel hp)
  rw [hf, Finsupp.mapDomain_id]

theorem pi2FromSub_shift (f : Hom L X)
    (hp : IsPathX X p x y) {c : UF X y →₀ ℤ}
    (hc : c ∈ Pi2FromSub f y) : chain2 (shiftHom hp) c ∈ Pi2FromSub f x := by
  obtain ⟨l, φ, hV, hE, hF, z, hz, rfl⟩ := hc
  refine ⟨l, (shiftHom hp).comp φ, ?_, hE, hF, z, hz, ?_⟩
  · intro v
    change endV (shiftV hp (φ.onV v)) = _
    simp_all
  · change Finsupp.mapDomain (shiftF hp) (Finsupp.mapDomain φ.onF z) =
      Finsupp.mapDomain ((shiftHom hp).comp φ).onF z
    rw [← Finsupp.mapDomain_comp]
    rfl

theorem pi2Generated_changeBase (f : Hom L X)
    (hp : IsPathX X p x y)
    (hgen : ∀ c : UF X y →₀ ℤ, bdry2 (uCover X y) c = 0 → c ∈ Submodule.span ℤ (Pi2FromSub f y))
    (c : UF X x →₀ ℤ) (hc : bdry2 (uCover X x) c = 0) :
    c ∈ Submodule.span ℤ (Pi2FromSub f x) := by
  let d := chain2 (shiftHom (isPath_revPath hp)) c
  have hd : bdry2 _ d = 0 := by rw [bdry2_chain2, hc, map_zero]
  have hg := hgen d hd
  have hm : chain2 (shiftHom hp) d ∈ Submodule.span ℤ (Pi2FromSub f x) := by
    have hle : Submodule.span ℤ (Pi2FromSub f y) ≤
        (Submodule.span ℤ (Pi2FromSub f x)).comap (chain2 (shiftHom hp)) := by
      apply Submodule.span_le.mpr
      intro z hz
      exact Submodule.subset_span (pi2FromSub_shift f hp hz)
    exact hle hg
  simp_all [show chain2 (shiftHom hp) d = c from chain2_shift_reverse_cancel hp c]
