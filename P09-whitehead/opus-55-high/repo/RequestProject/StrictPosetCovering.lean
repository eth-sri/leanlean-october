import RequestProject.OrderPosetCovering
import RequestProject.PosetCoverUpTransform
import RequestProject.StrictOrderComplex


/-! A poset covering restricts to the genuine nondegenerate cellular
two-skeleton. This is the cover used with strict cellular acyclicity.
Unverified source. -/

namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
  (hf : IsPosetCover f)

def strictMap := strictOrderCxMap f hf.strictMono

theorem strictMap_isCovering : IsCovering hf.strictMap := by
  refine ⟨hf.surj, ?_, ?_⟩
  · intro a
    change P at a
    constructor
    · rintro ⟨⟨e, b⟩, he⟩ ⟨⟨e', b'⟩, he'⟩ hEq
      have hb : b = b' := congrArg (·.val.2) hEq
      subst b'
      have hpair :=
        congrArg (·.val.1.val) hEq
      have h₁ := congrArg Prod.fst hpair
      have h₂ := congrArg Prod.snd hpair
      apply Subtype.ext
      refine Prod.ext ?_ rfl
      cases b with
      | false =>
          have hea : e.val.2 = a := he
          have hea' : e'.val.2 = a := he'
          have hfst := hf.down_inj (a := a)
            (by grind)
            (by grind) h₁
          exact Subtype.ext (Prod.ext hfst (hea.trans hea'.symm))
      | true =>
          have hea : e.val.1 = a := he
          have hea' : e'.val.1 = a := he'
          have hsnd := hf.up_inj (a := a)
            (by grind)
            (by grind) h₂
          exact Subtype.ext (Prod.ext (hea.trans hea'.symm) hsnd)
    · rintro ⟨⟨d, b⟩, hd⟩
      cases b with
      | true =>
          have hfa : f a = d.val.1 := hd.symm
          obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a d.val.2 (by grind)
          have hac' := lt_of_le_of_ne hac (by grind)
          refine ⟨⟨(⟨(a, c), hac'⟩, true), rfl⟩, ?_⟩
          exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hfa hfc)) rfl)
      | false =>
          have hfa : f a = d.val.2 := hd.symm
          obtain ⟨c, ⟨hca, hfc⟩, _⟩ := hf.down a d.val.1 (by grind)
          have hca' := lt_of_le_of_ne hca (by grind)
          refine ⟨⟨(⟨(c, a), hca'⟩, false), rfl⟩, ?_⟩
          exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hfc hfa)) rfl)
  · constructor
    · intro t t' hEq
      have hbase : t.val.1 = t'.val.1 := congrArg (·.val.2) hEq
      have htri := congrArg (·.val.1.val) hEq
      have hmid := hf.up_inj t.property.1.le
        (by grind)
        (congrArg (·.2.1) htri)
      have htop := hf.up_inj (t.property.1.trans t.property.2).le
        (by grind)
        (congrArg (·.2.2) htri)
      exact Subtype.ext (Prod.ext hbase (Prod.ext hmid htop))
    · rintro ⟨⟨s, a⟩, hs⟩
      change P at a
      have hfa : f a = s.val.1 := hs.symm
      obtain ⟨b, ⟨hab, hfb⟩, _⟩ := hf.up a s.val.2.1 (by grind)
      obtain ⟨c, ⟨hbc, hfc⟩, _⟩ := hf.up b s.val.2.2 (by grind)
      have hab' := lt_of_le_of_ne hab (by grind)
      have hbc' := lt_of_le_of_ne hbc (by grind)
      refine ⟨⟨(a, b, c), hab', hbc'⟩, ?_⟩
      exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hfa (Prod.ext hfb hfc))) rfl)
