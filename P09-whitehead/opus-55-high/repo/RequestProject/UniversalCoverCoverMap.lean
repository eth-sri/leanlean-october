import RequestProject.CombPi2
import RequestProject.CombCoveringLift
import RequestProject.Tac


/-! A genuine covering induces bijective universal-cover vertices and two-cells. -/
bwd

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
        grind [endpt_mapPath]
      obtain ⟨l, hl, hmap, hml⟩ := lift_htpy hp m.2 hh
      have hn := liftPath_unique hp l n.1 a _ _ hl n.2 hmap
      apply UV.sound
      simp_all

theorem univLiftV_surjective_of_covering : Function.Surjective (univLiftV a p) := by
  intro v
  induction v using UV.ind with
  | h n =>
    obtain ⟨l, b, hl, hmap⟩ := exists_liftPathAt hp n.1 a _ n.2
    have hl' : IsPathX X l a (endpt X a l) := by
      grind [endpt_eq_of_isPath hl]
    refine ⟨UV.mk ⟨l, hl'⟩, ?_⟩
    rw [univLiftV_mk]
    congr 1
    exact Subtype.ext hmap

theorem univLiftF_injective_of_covering : Function.Injective (univLiftF a p) := by
  intro v w h
  have hv := univLiftV_injective_of_covering hp a
    (congrArg (·.1.1) h)
  have hf :=
    congrArg (·.1.2) h
  have hb : X.base v.1.2 = X.base w.1.2 := by grind
  have hc := hp.cell.1 (by aesop)
  exact Subtype.ext (Prod.ext hv hc)

theorem univLiftF_surjective_of_covering : Function.Surjective (univLiftF a p) := by
  intro t
  cases' univLiftV_surjective_of_covering hp a t.1.1 with v hv
  have he : p.onV (endV v) = endV t.1.1 := by
    rw [← endV_univLiftV, hv]
  obtain ⟨f, ⟨hf, hb⟩, _⟩ := exists_unique_liftCell hp t.1.2 (t.2.symm.trans he.symm)
  refine ⟨⟨(v, f), hb.symm⟩, ?_⟩
  exact Subtype.ext (Prod.ext hv hf)

theorem univLiftE_injective_of_covering : Function.Injective (univLiftE a p) := by
  intro v w h
  have hv := univLiftV_injective_of_covering hp a
    (congrArg (·.1.1) h)
  have he :=
    congrArg (·.1.2) h
  have hs :=
    w.2.symm.trans (congrArg endV hv.symm)
  have hg := liftGerm_unique hp (a := endV v.1.1) (x := (v.1.2, true))
    (y := (w.1.2, true)) v.2.symm hs (Prod.ext he rfl)
  exact Subtype.ext (by grind)

theorem univLift_cycle_iff_of_covering (c : UF X a →₀ ℤ) :
    bdry2 (uCover Y (p.onV a)) (chain2 (univLift X p a) c) = 0 ↔
      bdry2 (uCover X a) c = 0 := by
  rw [bdry2_chain2]
  constructor
  · intro h
    apply Finsupp.mapDomain_injective (univLiftE_injective_of_covering hp a)
    tauto
  simp_all

theorem exists_unique_cycle_lift_of_covering (c : UF Y (p.onV a) →₀ ℤ)
    (hc : bdry2 (uCover Y (p.onV a)) c = 0) :
    ∃! d : UF X a →₀ ℤ,
      chain2 (univLift X p a) d = c ∧ bdry2 (uCover X a) d = 0 := by
  cases' Finsupp.mapDomain_surjective (univLiftF_surjective_of_covering hp a) c with d hd
  have hd' : chain2 (univLift X p a) d = c := hd
  refine ⟨d, ⟨hd', (univLift_cycle_iff_of_covering hp a d).mp (by simp_all)⟩, ?_⟩
  intro e he
  exact Finsupp.mapDomain_injective (univLiftF_injective_of_covering hp a)
    (he.1.trans hd'.symm)
