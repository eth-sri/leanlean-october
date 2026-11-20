/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CommonChartSupply
public import VaughtConjecture.Knight.ChartLanguage
public import InfinitaryLogic.Karp.PotentialIso

@[expose] public section

namespace VaughtConjecture.Knight

open FirstOrder Language TypeTower

universe w

namespace KnightRealization

variable {M₁ M₂ : Type w}

variable {α : LimitStage}

variable {A₁ : KnightRealization α M₁} {A₂ : KnightRealization α M₂}

/-- Read tuple pairs from one good chart, allowing repetitions and omissions. -/
private def selected (Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop) :
    Set (TuplePair M₁ M₂) :=
  {x | ∃ nd, Good nd ∧ ∃ σ : Fin x.1 → Fin nd.arity,
    nd.tuple₁ ∘ σ = x.2.1 ∧ nd.tuple₂ ∘ σ = x.2.2}

private theorem selected_step {Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop}
    (supply : RestrictedCommonChartStepSupply Good) {x : TuplePair M₁ M₂}
    (hx : x ∈ selected Good) (z : M₁ ⊕ M₂) :
    ∃ m n, (match z with | .inl t => m = t | .inr t => n = t) ∧
      ⟨_, Fin.snoc x.2.1 m, Fin.snoc x.2.2 n⟩ ∈ selected Good := by
  obtain ⟨nd, hnd, σ, h₁, h₂⟩ := hx
  obtain ⟨d⟩ := supply nd hnd z
  obtain ⟨i, hi⟩ := d.served
  refine ⟨d.next.tuple₁ i, d.next.tuple₂ i, ?_, d.next, d.good_next, Fin.snoc (d.emb ∘ σ) i, ?_, ?_⟩
  · cases z <;> exact hi
  · rw [Fin.comp_snoc, ← h₁, ← d.trans₁]; rfl
  · rw [Fin.comp_snoc, ← h₂, ← d.trans₂]; rfl

/-- A closed family of good common charts gives an isomorphism carrying the seed. -/
theorem exists_iso_of_selectedCommonCharts [Countable M₁] [Countable M₂]
    (hA₁ : A₁.IsExactParentConsistent) (hA₂ : A₂.IsExactParentConsistent)
    {Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop}
    (seed : CommonChartNode (A₁ := A₁) (A₂ := A₂)) (hs : Good seed)
    (supply : RestrictedCommonChartStepSupply Good) :
    ∃ e : A₁.Iso A₂, ∀ i, e.1 (seed.tuple₁ i) = seed.tuple₂ i := by
  letI := stageStructureOf A₁
  letI := stageStructureOf A₂
  let p : TuplePair M₁ M₂ := ⟨seed.arity, seed.tuple₁, seed.tuple₂⟩
  have hp : p ∈ selected Good := ⟨seed, hs, id, rfl, rfl⟩
  let P : PotentialIso (stageLang α) M₁ M₂ :=
    { family := selected Good
      nonempty := ⟨p, hp⟩
      compatible := by
        rintro _ ⟨nd, -, σ, h₁, h₂⟩
        exact sameAtomicType_of_commonChart hA₁ hA₂
          ⟨nd.arity, nd.tuple₁, nd.tuple₂, σ, nd.type, nd.eval₁, nd.eval₂, h₁, h₂⟩
      forth := fun _ hx m => by
        obtain ⟨m', n, hm, h⟩ := selected_step supply hx (.inl m)
        exact ⟨n, hm ▸ h⟩
      back := fun _ hx n => by
        obtain ⟨m, n', hn, h⟩ := selected_step supply hx (.inr n)
        exact ⟨m, hn ▸ h⟩ }
  obtain ⟨e, he⟩ := P.exists_equiv_of_mem hp
  exact ⟨⟨e.toEquiv, isIsoOfStageStructureEquiv e⟩, he⟩

end KnightRealization

end VaughtConjecture.Knight
