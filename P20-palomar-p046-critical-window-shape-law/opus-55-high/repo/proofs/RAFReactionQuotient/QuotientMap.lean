module

public import proofs.OverlapCorrectedRAF.Source.KauffmanRepositoryCRS
public import proofs.RAFReactionQuotient.ClosureProjection

@[expose] public section

namespace RAFReactionQuotient
open Classical RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

abbrev OrderedChannel (n : ℕ) :=
  {uv : Molecule n × Molecule n // molLength uv.1 + molLength uv.2 ≤ n}

def orderedCRS (n t : ℕ) : ReversibleCRS (Molecule n) (OrderedChannel n) where
  lhs r := {r.val.1, r.val.2}
  rhs r := {concatMolecule r.val.1 r.val.2 r.property}
  food := binaryFood n t

theorem precedes_total {n : ℕ} (u v : Molecule n) :
    moleculePrecedes u v ∨ moleculePrecedes v u := by
  omega

def canonical {n : ℕ} (r : OrderedChannel n) : RepositoryChannel n :=
  if h : displayedConcat r.val.1 r.val.2 ≠ displayedConcat r.val.2 r.val.1 ∨
      moleculePrecedes r.val.1 r.val.2 then
    ⟨r.val, r.property, h⟩
  else
    ⟨(r.val.2, r.val.1), (Nat.add_comm (molLength r.val.2) $ molLength r.val.1).le.trans r.property,
      Or.inr $ (precedes_total r.val.1 r.val.2).resolve_left $ fun hp => h $ Or.inr hp⟩

theorem molecule_ext {n : ℕ} {x y : Molecule n}
    (hl : molLength x = molLength y) (hc : x.2.val = y.2.val) : x = y := by
  rcases x with ⟨⟨i, _⟩, x⟩
  rcases y with ⟨⟨j, _⟩, y⟩
  obtain rfl : i = j := by simp only [molLength] at hl; omega
  simp_all [Fin.ext_iff]

theorem concat_code {n : ℕ} (u v : Molecule n)
    (h : molLength u + molLength v ≤ n) :
    (concatMolecule u v h).2.val = displayedConcat u v := by
  simp [concatMolecule, moleculeOfCode, concatCode, displayedConcat, Nat.add_comm, Nat.mul_comm]

theorem concat_comm_of_code {n : ℕ} (u v : Molecule n)
    (h : molLength u + molLength v ≤ n)
    (hc : displayedConcat u v = displayedConcat v u) :
    concatMolecule u v h = concatMolecule v u (by omega) := by
  apply molecule_ext
  · simp [concatMolecule, Nat.add_comm]
  · simpa only [concat_code] using hc

variable {n t : ℕ} (r : OrderedChannel n)

theorem canonical_lhs  :
    (repositoryCRS n t).lhs (canonical r) = (orderedCRS n t).lhs r := by
  unfold canonical
  split <;> simp [repositoryCRS, orderedCRS, Finset.pair_comm]

theorem canonical_rhs  :
    (repositoryCRS n t).rhs (canonical r) = (orderedCRS n t).rhs r := by
  unfold canonical
  split
  · rfl
  · simp only [repositoryCRS, orderedCRS]
    rw [concat_comm_of_code r.val.1 r.val.2 r.property $ by omega]


theorem canonical_val_cases {n : ℕ} (r : OrderedChannel n) :
    (canonical r).val = r.val ∨ (canonical r).val = r.val.swap := by
  unfold canonical
  grind

theorem canonical_surjective (n : ℕ) : Function.Surjective (@canonical n) := by
  intro j
  refine ⟨⟨j.val,j.property.1⟩, ?_⟩
  simp only [canonical, dite_eq_left j.property.2]

theorem canonical_fibre_le_two {n : ℕ} (j : RepositoryChannel n) :
    (Finset.univ.filter (fun r : OrderedChannel n => canonical r = j)).card ≤ 2 := by
  let a : OrderedChannel n := ⟨j.val,j.property.1⟩
  let b : OrderedChannel n := ⟨j.val.swap, by grind⟩
  refine (Finset.card_le_card (t := {a, b}) fun r hr => ?_).trans Finset.card_le_two
  have := canonical_val_cases r
  grind

end RAFReactionQuotient
