module

public import RequestProject.CombPi2
public import RequestProject.CombCoveringLift

@[expose] public section

/-! A genuine covering induces bijective universal-cover vertices and two-cells. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {X Y : Complex2.{u}} {p : Hom X Y} (hp : IsCovering p) (a : X.V)
include hp

theorem univLiftV_injective_of_covering : Function.Injective (univLiftV a p) := by
  intro v w h
  induction v using UV.ind with
  | h m =>
    induction w using UV.ind with
    | h n =>
      have hh : Htpy Y (p.onV a) (p.onV (endpt X a m.1))
          (mapPath p m.1) (mapPath p n.1) := by
        have ht := Quotient.exact h
        change Htpy Y (p.onV a) (endpt Y (p.onV a) (mapPath p m.1))
          (mapPath p m.1) (mapPath p n.1) at ht
        rwa [endpt_mapPath] at ht
      obtain ⟨l, hl, hmap, hml⟩ := lift_htpy hp.uniqueLifts m.2 hh
      have hn  := liftPath_unique hp.uniqueLifts l n.1 a _ _ hl n.2 hmap
      apply UV.sound
      rwa [hn] at hml

theorem univLiftV_surjective_of_covering : Function.Surjective (univLiftV a p) := by
  intro v
  induction v using UV.ind with
  | h n =>
    obtain ⟨l, b, hl, hmap⟩ := exists_liftPathAt hp.uniqueLifts n.1 a _ n.2
    have hl' : IsPath X.src X.tgt l a (endpt X a l) := by
      simp_all [endpt_eq_of_isPath hl]
    refine ⟨UV.mk ⟨l, hl'⟩, ?_⟩
    rw [univLiftV_mk]
    congr 1
    exact Subtype.ext hmap

theorem univLiftF_injective_of_covering : Function.Injective (univLiftF a p) :=
  univLiftF_injective p (univLiftV_injective_of_covering hp a) (fun _ _ => hp.uniqueLifts.face_eq)

theorem univLiftF_surjective_of_covering : Function.Surjective (univLiftF a p) := by
  intro t
  obtain ⟨v, hv⟩ := univLiftV_surjective_of_covering hp a t.1.1
  have he : p.onV (endV v) = endV t.1.1 := by
    rw [← endV_univLiftV, hv]
  obtain ⟨f, ⟨hf, hb⟩, _⟩ := exists_unique_liftCell hp.uniqueLifts t.1.2 (t.2.symm.trans he.symm)
  refine ⟨⟨(v, f), hb.symm⟩, ?_⟩
  exact Subtype.ext (Prod.ext hv hf)

theorem univLiftE_injective_of_covering : Function.Injective (univLiftE a p) :=
  univLiftE_injective p (univLiftV_injective_of_covering hp a) (fun _ _ => hp.uniqueLifts.edge_eq)

theorem univLift_cycle_iff_of_covering (c : UF X a →₀ ℤ) :
    bdry2 (uCover Y (p.onV a)) (chain2 (univLift X p a) c) = 0 ↔
      bdry2 (uCover X a) c = 0 := by
  rw [bdry2_chain2]
  constructor
  · intro h
    apply Finsupp.mapDomain_injective (univLiftE_injective_of_covering hp a)
    tauto
  · intro h
    rw [h, map_zero]

theorem exists_unique_cycle_lift_of_covering (c : UF Y (p.onV a) →₀ ℤ)
    (hc : bdry2 (uCover Y (p.onV a)) c = 0) :
    ∃! d : UF X a →₀ ℤ,
      chain2 (univLift X p a) d = c ∧ bdry2 (uCover X a) d = 0 := by
  obtain ⟨d, hd⟩ := Finsupp.mapDomain_surjective (univLiftF_surjective_of_covering hp a) c
  have hd' : chain2 (univLift X p a) d = c := hd
  refine ⟨d, ⟨hd', (univLift_cycle_iff_of_covering hp a d).mp (by rw [hd']; exact hc)⟩, ?_⟩
  intro e he
  exact Finsupp.mapDomain_injective (univLiftF_injective_of_covering hp a)
    (he.1.trans hd'.symm)

end FiniteChains.Comb
