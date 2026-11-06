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
  unfold moleculePrecedes
  omega

def canonical {n : ℕ} (r : OrderedChannel n) : RepositoryChannel n :=
  if h : displayedConcat r.val.1 r.val.2 ≠ displayedConcat r.val.2 r.val.1 ∨
      moleculePrecedes r.val.1 r.val.2 then
    ⟨r.val, r.property, h⟩
  else
    ⟨(r.val.2, r.val.1), (Nat.add_comm (molLength r.val.2) (molLength r.val.1)).le.trans r.property,
      Or.inr ((precedes_total r.val.1 r.val.2).resolve_left (fun hp => h (Or.inr hp)))⟩

theorem molecule_ext {n : ℕ} {x y : Molecule n}
    (hl : molLength x = molLength y) (hc : x.2.val = y.2.val) : x = y := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  have hij : i = j := by apply Fin.ext; dsimp [molLength] at hl; omega
  subst j
  exact congrArg (Sigma.mk i) (Fin.ext hc)

theorem concat_code {n : ℕ} (u v : Molecule n)
    (h : molLength u + molLength v ≤ n) :
    (concatMolecule u v h).2.val = displayedConcat u v := by
  simp [concatMolecule, moleculeOfCode, concatCode, displayedConcat,
    finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

theorem canonical_lhs {n t : ℕ} (r : OrderedChannel n) :
    (repositoryCRS n t).lhs (canonical r) = (orderedCRS n t).lhs r := by
  unfold canonical
  split
  · rfl
  · simp [repositoryCRS, orderedCRS, Finset.pair_comm]

theorem canonical_rhs {n t : ℕ} (r : OrderedChannel n) :
    (repositoryCRS n t).rhs (canonical r) = (orderedCRS n t).rhs r := by
  unfold canonical; split
  · rfl
  · rename_i h
    simp only [repositoryCRS, orderedCRS]
    congr 1
    exact molecule_ext (by simp [concatMolecule, Nat.add_comm])
      (by simpa only [concat_code] using (Classical.byContradiction fun hn => h (Or.inl hn)).symm)

theorem canonical_surjective (n : ℕ) : Function.Surjective (@canonical n) := fun j =>
  ⟨⟨j.val, j.property.1⟩, by simp only [canonical, dite_eq_left j.property.2]⟩

theorem canonical_fibre_le_two {n : ℕ} (j : RepositoryChannel n) :
    (Finset.univ.filter (fun r : OrderedChannel n => canonical r = j)).card ≤ 2 := by
  let a : OrderedChannel n := ⟨j.val, j.property.1⟩
  let b : OrderedChannel n := ⟨j.val.swap, (Nat.add_comm _ _).le.trans j.property.1⟩
  refine (Finset.card_le_card (t := {a, b}) fun r hr => ?_).trans Finset.card_le_two
  have he := congrArg Subtype.val (Finset.mem_filter.mp hr).2
  unfold canonical at he; split at he
  · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext he))
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext (congrArg Prod.swap he))))

end RAFReactionQuotient
