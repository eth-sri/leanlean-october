module
public import Mathlib.Tactic

public import Erdos821.S2.MemoryEdge
public import Erdos821.Leaves

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

section
variable (ν : Pattern P J F.ell m)

/-- Non-shared slots fit in `t_g = ell + changed`. -/
lemma nonshared_card_le    g  :
    (Finset.univ.filter (fun i : Fin (J + F.ell) => ¬ ν.shared g i)).card
      ≤ ν.t g := by
  classical
  have hslot_inj : Function.Injective ν.slot := by
    intro a b h
    have hval : (ν.slot a).val = (ν.slot b).val := congrArg Fin.val h
    have hval2 : a.val = b.val := hval
    exact Fin.ext hval2
  have himg_card : (((Finset.univ \ ν.changed g).map
      ⟨ν.slot, hslot_inj⟩)).card = J - (ν.changed g).card := by
    rw [Finset.card_map, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin]
  have hsub : (((Finset.univ \ ν.changed g).map
      ⟨ν.slot, hslot_inj⟩)) ⊆
      Finset.univ.filter (fun i : Fin (J + F.ell) => ν.shared g i) := by
    intro i hi
    simp only [Finset.mem_map, Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨j, rfl, hj⟩
  have hcard := Finset.card_le_card hsub
  rw [himg_card] at hcard
  have htot : (Finset.univ.filter (fun i : Fin (J + F.ell) => ¬ ν.shared g i)).card +
      (Finset.univ.filter (fun i : Fin (J + F.ell) => ν.shared g i)).card
      = J + F.ell := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (J + F.ell)))) (ν.shared g)
    rw [Finset.card_univ, Fintype.card_fin] at h
    linarith
  
  unfold Pattern.t
  omega

lemma prom_card_le   (g : P.BigGroup)
    (B : Finset (Fin (J + F.ell))) (hB : ∀ i ∈ B, ¬ ν.shared g.val i) :
    B.card ≤ F.ell + m := by
  have h1 : B.card ≤ (Finset.univ.filter
    (fun i : Fin (J + F.ell) => ¬ ν.shared g.val i)).card := by
    apply Finset.card_le_card
    grind
  have h2 := nonshared_card_le ν g.val
  have h3 : (ν.changed g.val).card ≤ m := ν.bound g.val
  unfold Pattern.t at h2
  omega

/-- Transfer subset pairs live in a `J`-independent powerset. -/
lemma transfer_pairs_card_le   (g : P.BigGroup) :
    ((Finset.univ.filter (fun i : Fin (J + F.ell) => ¬ ν.shared g.val i)).powerset ×ˢ
      (Finset.univ.filter (fun i : Fin (J + F.ell) => ¬ ν.shared g.val i)).powerset).card
      ≤ 4 ^ (F.ell + m) := by
  have htg : (Finset.univ.filter
      (fun i : Fin (J + F.ell) => ¬ ν.shared g.val i)).card ≤ F.ell + m := by
    have h2 := nonshared_card_le ν g.val
    have h3 : (ν.changed g.val).card ≤ m := ν.bound g.val
    unfold Pattern.t at h2
    omega
  calc ((Finset.univ.filter (fun i : Fin (J + F.ell) => ¬ ν.shared g.val i)).powerset ×ˢ
        (Finset.univ.filter (fun i : Fin (J + F.ell) => ¬ ν.shared g.val i)).powerset).card
      = 2 ^ (Finset.univ.filter _).card * 2 ^ (Finset.univ.filter _).card := by
        rw [Finset.card_product, Finset.card_powerset]
    _ ≤ 2 ^ (F.ell + m) * 2 ^ (F.ell + m) :=
        (by gcongr <;> first | assumption | positivity | linarith)
    _ = 4 ^ (F.ell + m) := by
        calc 2 ^ (F.ell+m) * 2 ^ (F.ell+m)
            = (2 * 2) ^ (F.ell+m) := (mul_pow (2:Nat) 2 (F.ell+m)).symm
          _ = 4 ^ (F.ell+m) := by
              rfl

end

/-- Promotion coefficients are bounded via `vMin`, uniformly for `a ≤ ell+m`. -/
lemma Vinv_pow_le (hv : 0 < F.vMin)  V  (hV : F.vMin ≤ V)
     a  (ha : a ≤ F.ell + m) :
    V ^ (-(a : ℤ)) ≤ max 1 (F.vMin⁻¹ ^ (F.ell + m)) :=
  Erdos821.GraphLemmas.vinv_bound F.vMin V hv hV a (F.ell + m) ha

end Erdos821.P3Edge
