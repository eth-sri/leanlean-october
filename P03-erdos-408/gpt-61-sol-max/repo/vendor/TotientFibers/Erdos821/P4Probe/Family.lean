module
public import Mathlib.Tactic

public import Erdos821.Blueprint.Ideal

@[expose] public section

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

variable {P : PrimeGroups} {J ell m : ℕ}

lemma selectedProduct_aux_ext (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool)  side  (u v : P.BigAux J)
    (huv : ∀ g i, i ∈ ν.changed g.val → u g i = v g i) :
    selectedProduct ν block side u = selectedProduct ν block side v := by
  unfold selectedProduct
  grind

def ProbeChoice (P : PrimeGroups) (m ) (block : P.BigGroup → Bool) :=
  {c : P.BigGroup → Finset (Fin m) //
    ∀ side : Bool, ∃ g : P.BigGroup, block g = side ∧ (c g).Nonempty}

instance (P : PrimeGroups) (m : ℕ) (block : P.BigGroup → Bool) :
    Fintype (ProbeChoice P m block) :=
  inferInstanceAs (Fintype {c : P.BigGroup → Finset (Fin m) //
    ∀ side : Bool, ∃ g : P.BigGroup, block g = side ∧ (c g).Nonempty})



def liftChoice (hj : m ≤ J) (c : P.BigGroup → Finset (Fin m))
    (g : P.Group)  :=
  if hg : P.big g = true then (c ⟨g, hg⟩).image (Fin.castLE hj) else ∅

section
variable (hj : m ≤ J) (c : P.BigGroup → Finset (Fin m))
include hj c

@[simp] lemma liftChoice_big    
    (g : P.BigGroup) :
    liftChoice hj c g.val = (c g).image (Fin.castLE hj) := by
  simp [liftChoice, g.property]

section
variable (g : P.Group)
include g

lemma liftChoice_small    
      (hg : P.big g = false) : liftChoice hj c g = ∅ := by
  simp [liftChoice, hg]

lemma liftChoice_bound    
      : (liftChoice hj c g).card ≤ m := by
  unfold liftChoice
  split_ifs
  · exact Finset.card_image_le.trans (by simpa using Finset.card_le_univ (c ⟨g, by assumption⟩))
  · simp

lemma liftChoice_probe    
      (i : Fin J) (hi : i ∈ liftChoice hj c g) : i.val < m := by
  unfold liftChoice at hi
  grind

end

end

def rawPattern (P : PrimeGroups) (J ell m : ℕ) : Pattern P J ell m where
  changed := fun _ => ∅
  small := by intros; rfl
  bound := by intros; simp
  coefficient := fun _ _ _ => 1
  coefficient_aux_ext := by intros; rfl

def choiceBase (hj : m ≤ J) (c : P.BigGroup → Finset (Fin m)) :
    Pattern P J ell m where
  changed := liftChoice hj c
  small := liftChoice_small hj c
  bound := liftChoice_bound hj c
  coefficient := fun _ _ _ => 0
  coefficient_aux_ext := by intros; rfl

def signedPattern (hj : m ≤ J) (block )
    (Q : ℕ) (h ξ : ℝ) (c : ProbeChoice P m block)  :=
  let ν : Pattern P J ell m := choiceBase hj c.val
  { ν with
    coefficient := fun a b u =>
      -((-1 : ℂ) ^ (∑ g, (ν.changed g).card)) *
      selectedKernel ν block false Q h ξ (selectedProduct ν block false u)
        (selectedEndpoint ν block false b) *
      selectedKernel ν block true Q h ξ (selectedProduct ν block true u)
        (selectedEndpoint ν block true a)
    coefficient_aux_ext := by
      grind [selectedProduct_aux_ext] }

def probeFamily (F : FixedData) (P : PrimeGroups) (J m : ℕ) (hj : m ≤ J)
    (block : P.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ) : Family F P J m where
  count := Fintype.card (Option (ProbeChoice P m block))
  pattern := fun v =>
    match (Fintype.equivFin (Option (ProbeChoice P m block))).symm v with
    | none => rawPattern P J F.ell m
    | some c => signedPattern hj block Q h ξ c

theorem probeFamily_residual  F   P   J m 
     hj   block   Q   h ξ  :
    (probeFamily F P J m hj block Q h ξ).Residual Q h ξ := by
  let e := Fintype.equivFin (Option (ProbeChoice P m block))
  refine ⟨e none, block, ?_, ?_, ?_⟩
  · intro g
    simp [probeFamily, e, rawPattern]
  · intro a b u
    simp [probeFamily, e, rawPattern]
  · intro v hv
    have hn : e.symm v ≠ none := by
      intro he
      apply hv
      apply e.symm.injective
      simpa using he
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hn
    have hp : (probeFamily F P J m hj block Q h ξ).pattern v =
        signedPattern hj block Q h ξ c := by
      change (match e.symm v with
        | none => rawPattern P J F.ell m
        | some c => signedPattern hj block Q h ξ c) = _
      rw [hc]
    rw [hp]
    refine ⟨?_, ?_, ?_⟩
    · intro g i hi
      exact liftChoice_probe hj c.val g i hi
    · intro side
      obtain ⟨g, hg, hc⟩ := c.property side
      refine ⟨g, hg, ?_⟩
      simpa [signedPattern, choiceBase] using hc.image (Fin.castLE hj)
    · intro a b u
      rfl

end
end Erdos821.P4Probe
