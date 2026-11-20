module

public import RequestProject.ChamberZCoverDegreeLocal

@[expose] public section

/-! Degree-two generation on actual poset covers of the modified chamber construction. -/
namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] [Nonempty X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}

theorem generatesDegreeIn_cover_zupto (hf : IsPosetCover f) :
    ∀ n : ℕ, GeneratesDegreeIn (fun p : P => ZUpto n (f p)) (fun p => InZBase (f p)) 3 := by
  apply chamberInduction A
    (fun S => GeneratesDegreeIn (fun p => chamberUnion InZChamber S (f p)) (fun p => InZBase (f p)) 3)
  · refine generatesDegreeIn_congr (fun p => ?_) (generatesDegreeIn_cover_chamber hf 1)
    exact Iff.of_eq (congrFun (chamberUnion_singleton InZChamber 1).symm (f p))
  · intro n S x hx hl hs hne h
    rw [chamberUnion_insert]
    refine generatesDegreeIn_union_of_unmixed (n := 2) (fun _ => Iff.rfl) ?_ h
      (generatesDegreeIn_cover_chamber hf x)
      (fillsDegreeIn_congr (fun p => (zUpto_overlap hx hl hs (f p)).symm)
        (fillsDegreeIn_cover_attaching_intersection hf x hne))
    intro p q hpq hp _
    exact unmixed_of_upper (C := InZChamber x) (chamberUnion_up (C := InZChamber) (fun _ _ _ h => inZChamber_of_le h))
      (fun _ _ h => inZChamber_of_le h) (hf.mono hpq) hp

/-- Every homogeneous two-cycle in an actual covering poset is a cycle on the
actual preimage of the inserted bases plus a genuine finite three-boundary. -/
theorem exists_cover_base_twoCycle (hf : IsPosetCover f) {c : Nerve.Ch P}
    (hc : c ∈ Nerve.Inc P) (hd : lengthProjection 3 c = c) (hcyc : Nerve.bdry c = 0) :
    ∃ d ∈ IncOn (fun p => InZBase (f p)), ∃ y ∈ Nerve.Inc P,
      Nerve.bdry d = 0 ∧ c = d + Nerve.bdry y := by
  obtain ⟨n, hn⟩ := exists_incOn_bound (zlen ∘ f) hc
  obtain ⟨d, hdb, y, hy, hdd, he⟩ := generatesDegreeIn_cover_zupto hf n c
    (incOn_mono (fun p hp => by
      obtain ⟨w, hw, hm⟩ := zUpto_zlen (f p)
      exact ⟨w, hw.trans hp, hm⟩) hn) hd hcyc
  exact ⟨d, hdb, y, incOn_le_inc _ hy, hdd, he⟩

end FiniteChains.Davis
