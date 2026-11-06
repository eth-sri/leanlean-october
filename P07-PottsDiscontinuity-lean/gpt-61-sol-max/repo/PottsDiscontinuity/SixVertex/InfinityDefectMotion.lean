module
public import Mathlib

public import PottsDiscontinuity.SixVertex.InfinitySupport

/-!
# Exact local motion of defects through a transfer row

Horizontal arrows give a canonical labelled motion of every defect. The image
identity is cyclic and includes defects crossing the seam.
-/

@[expose] public section

open Finset

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ}

@[simp] theorem mem_defects_iff (x : Finset (Fin N)) (i : Fin N) :
    i ∈ defects x ↔ i ∉ x ∧ prv i ∉ x := by
  simp_all [defects]

/-- For disjoint vertical states, the only up/down changes of the horizontal
arrow are precisely the lower/upper up arrows. -/
theorem Flux.local_disjoint {x y : Finset (Fin N)} {h : Fin N → Bool}
    (hf : Flux x y h) (hd : Disjoint x y) (i : Fin N) :
    (i ∈ x ↔ h (prv i) = false ∧ h i = true) ∧
      (i ∈ y ↔ h (prv i) = true ∧ h i = false) := by
  have he := hf i
  have hn := hd.notMem_of_mem_left_finset (a := i)
  
  by_cases hx : i ∈ x <;> by_cases hy : i ∈ y <;>
    cases hp : h (prv i) <;> cases hc : h i <;> simp_all [toInt]

/-- A defect at `i` moves left exactly when the horizontal arrow before `i` points right. -/
def defectMotion (h : Fin N → Bool) (i : Fin N)  :=
  if h (prv i) then prv i else nxt i

/-- Exact two-preimage description of a point under a defect motion map. -/
theorem mem_image_defectMotion (x : Finset (Fin N)) (h : Fin N → Bool) (j : Fin N) :
    j ∈ (defects x).image (defectMotion h) ↔
       nxt j ∈ defects x ∧ h j = true  ∨
         prv j ∈ defects x ∧ h (prv (prv j)) = false  := by
  grind +locals

/-- The ice rule gives the exact moved defect set, including seam crossings. -/
theorem Flux.defects_eq_image {x y : Finset (Fin N)} {h : Fin N → Bool}
    (hf : Flux x y h) (hd : Disjoint x y) :
    defects y = (defects x).image (defectMotion h) := by
  ext j
  rw [mem_image_defectMotion]
  simp only [mem_defects_iff, (finRotate N).symm_apply_apply j]
  rw [(hf.local_disjoint hd j).2, (hf.local_disjoint hd (prv j)).2,
    (hf.local_disjoint hd (nxt j)).1, (hf.local_disjoint hd j).1,
    (hf.local_disjoint hd (prv j)).1, (hf.local_disjoint hd (prv (prv j))).1]
  grind

private theorem defectMotion_preimage (h : Fin N → Bool) (i : Fin N) :
     i = nxt (defectMotion h i) ∧ h (defectMotion h i) = true  ∨
       i = prv (defectMotion h i) ∧ h (prv (prv (defectMotion h i))) = false  := by
  grind +locals

section

variable {x y : Finset (Fin N)} {h : Fin N → Bool} (hf : Flux x y h) (hd : Disjoint x y)
include hf hd

private theorem no_double_motion_preimage  (z : Fin N)
    (hl : nxt z ∈ defects x) (hr : prv z ∈ defects x)
    (hz : h z = true) (hp2 : h (prv (prv z)) = false) : False := by
  have hx0 := (mem_defects_iff x (nxt z)).mp hl |>.2
  have hx1 := (mem_defects_iff x (prv z)).mp hr |>.1
  rw [show prv (nxt z) = z from (finRotate N).symm_apply_apply z] at hx0
  rw [(hf.local_disjoint hd z).1] at hx0
  rw [(hf.local_disjoint hd (prv z)).1] at hx1
  cases hp : h (prv z)
  · exact hx0 ⟨hp, hz⟩
  · exact hx1 ⟨hp2, hp⟩

/-- On the actual source defects, the local motion has no duplicate endpoints. -/
theorem Flux.defectMotion_injective  :
    Set.InjOn (defectMotion h) (defects x) := by
  intro i hi j hj he
  let z := defectMotion h i
  
  have hjp :  j = nxt z ∧ h z = true  ∨
       j = prv z ∧ h (prv (prv z)) = false  := by
    grind +locals
  rcases  defectMotion_preimage h i  with ⟨hei, hzi⟩ | ⟨hei, hzi⟩ <;>
    rcases hjp with ⟨hej, hzj⟩ | ⟨hej, hzj⟩
  · exact hei.trans hej.symm
  · exact (no_double_motion_preimage hf hd z (hei ▸ hi) (hej ▸ hj) hzi hzj).elim
  · exact (no_double_motion_preimage hf hd z (hej ▸ hj) (hei ▸ hi) hzj hzi).elim
  · exact hei.trans hej.symm

end

end PottsDiscontinuity.SixVertex
