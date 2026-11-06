import RequestProject.CollapseChainMap
import RequestProject.SpineCollapse


/-!
# Lemma 3.3 (iii) in the form used by the capping argument: the cut surface is the zero
chain of the spine

`RequestProject/TruncatedCube.lean` proves the chain-level half of Lemma 3.3 (iii): in the
truncated complex `M = C(L) ∖ (neighbourhood of the corner)` the fundamental cycle of the cut
surface is the boundary of the signed sum of the three-cubes
(`FiniteChains.cutSurface_isBoundary`).  `RequestProject/SpineCollapse.lean` proves Lemma
3.3 (ii): all three-cubes of `M` are removed by elementary collapses, leaving a
two-dimensional spine.

This file combines the two, through the chain map of a collapse
(`RequestProject/CollapseChainMap.lean`): the collapse carries the fundamental cycle of the
cut surface to the **zero** cellular chain of the spine.  This is exactly the form in which
the proof of (B3) uses Lemma 3.3 (iii): the block part of the boundary of the cone
three-cell, which is the image of `[Σ_q]`, is the zero chain, hence has zero augmentation.

The cells are those of `RequestProject/SpineCollapse.lean`: the three-cells are the cubes
with a triangle as free set, and the codimension one faces are the squares of `C(L)`
together with the cut cells created by the truncation.  `FiniteChains.cubeBdry` is the
cellular boundary of a three-cube, read off from the boundary operator `bdryT` of the
truncated complex.
-/

namespace FiniteChains

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The cellular boundary of the three-cube `t` in the truncated complex, as a coefficient
function on the codimension one faces used by the collapse (squares and cut cells). -/
noncomputable def cubeBdry (t : Cube V) :=
  Sum.elim (bdry (if · = t then 1 else 0))
    (fun τ => cutSign τ * (if posCube τ = t then 1 else 0))

theorem cubeBdry_inl (t g : Cube V) :
    cubeBdry t (Sum.inl g)
      = ∑ j ∈ univ.filter (g · ≠ CubeCoord.free),
          incid g j * (if Function.update g j CubeCoord.free = t then 1 else 0) := rfl

theorem cubeBdry_inr t (τ : Finset V) :
    cubeBdry t (Sum.inr τ) = cutSign τ * (if posCube τ = t then 1 else 0) := rfl

omit [Fintype V] [LinearOrder V] in
/-- Freeing a coordinate of a square determines that coordinate: distinct coordinates give
distinct cubes above it. -/
theorem update_free_injective {g : Cube V} {j k : V} (hj : g j ≠ CubeCoord.free)
    (h : Function.update g j CubeCoord.free = Function.update g k CubeCoord.free) : j = k := by
  by_contra hjk
  have hval := congrFun h j
  simp_all

omit [DecidableEq V] in
/-- The incidence number of a cube with a codimension one face is a unit. -/
theorem incid_eq_unit {g : Cube V} {j : V} (hj : g j ≠ CubeCoord.free) :
    incid g j = 1 ∨ incid g j = -1 := by
  have hs : (g j).sgn = 1 ∨ (g j).sgn = -1 := by
    rcases h : g j with _ | _ | _ <;> aesop
  rcases Nat.even_or_odd _ with he | ho
  · rw [incid, he.neg_one_pow, one_mul]
    exact hs
  · rw [incid, ho.neg_one_pow]
    omega

/-- **The boundary of a three-cube on a square face is `±1` when the cube lies above that
face.** -/
theorem cubeBdry_inl_eq_unit {g t : Cube V} (ht : t ∈ cofaces L g) :
    cubeBdry t (Sum.inl g) = 1 ∨ cubeBdry t (Sum.inl g) = -1 := by
  classical
  obtain ⟨j, hj, -, rfl⟩ := mem_cofaces.1 ht
  rw [cubeBdry_inl, Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_one]
    exact incid_eq_unit hj
  · intro k hk hkj
    have hk' : g k ≠ CubeCoord.free := by simpa using hk
    rw [if_neg, mul_zero]
    intro hcon
    exact hkj (update_free_injective hk' hcon)
  simp_all

/-- **A three-cube not lying above a square has zero boundary coefficient there.** -/
theorem cubeBdry_inl_eq_zero {g t : Cube V} (htop : t ∈ topCubes L)
    (ht : t ∉ cofaces L g) : cubeBdry t (Sum.inl g) = 0 := by
  classical
  rw [cubeBdry_inl]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : g j ≠ CubeCoord.free := by simpa using hj
  rw [if_neg, mul_zero]
  intro hcon
  refine ht (mem_cofaces.2 ⟨j, hj', ?_, hcon.symm⟩)
  have hfree : freeSet (Function.update g j CubeCoord.free) = insert j (freeSet g) := by
    ext i
    by_cases hij : i = j <;> simp [hij]
  rw [← hfree, hcon]
  exact (mem_topCubes.1 htop).1

/-- **The boundary of the truncated corner cube over a triangle on its cut face is `-1`.** -/
theorem cubeBdry_inr_eq_neg_one {τ : Finset V} (hτ : τ.card = 3) :
    cubeBdry (posCube τ) (Sum.inr τ) = -1 := by
  rw [cubeBdry_inr, if_pos rfl, mul_one, cutSign, hτ]
  norm_num

/-- A three-cube other than the truncated corner cube over `τ` has zero coefficient on the
cut face of `τ`. -/
theorem cubeBdry_inr_eq_zero {τ : Finset V} (h : t ≠ posCube τ) :
    cubeBdry t (Sum.inr τ) = 0 := by
  rw [cubeBdry_inr, if_neg h.symm, mul_zero]

/-! ### From a combinatorial collapse to a chain collapse -/

/-- A collapse removes every cell of the collapsed set. -/
theorem Collapse.mem_list_of_isCollapse {T F} [DecidableEq T] {inc : F → Finset T}
    {l} {S} (h : Collapse.IsCollapse inc l S) : ∀ t ∈ S, t ∈ l := by
  induction l generalizing S with
  | nil =>
      simp [show S = ∅ from h]
  | cons u l ih =>
      obtain ⟨huS, -, hrest⟩ := h
      intro t ht
      by_cases htu : t = u
      · simp_all
      aesop

/-! ### The boundary of a three-chain, cell by cell -/

/-- The boundary of a three-chain of the truncated complex, written as the combination of the
boundaries of its three-cubes. -/
theorem bdryT_eq_sum (hc : ∀ t, c t ≠ 0 → t ∈ S)
    (f : Cube V ⊕ Finset V) :
    Sum.elim (bdryT (c, 0)).1 (bdryT (c, 0)).2 f = ∑ t ∈ S, c t * cubeBdry t f := by
  classical
  cases f with
  | inl g =>
      show bdry c g = _
      rw [bdry]
      have hswap : ∑ t ∈ S, c t * cubeBdry t (Sum.inl g)
          = ∑ j ∈ univ.filter (g · ≠ CubeCoord.free),
              incid g j * c (Function.update g j CubeCoord.free) := by
        simp only [cubeBdry_inl, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        have : ∀ t ∈ S, c t * (incid g j * if Function.update g j CubeCoord.free = t then 1
            else 0) = if t = Function.update g j CubeCoord.free then
              c t * incid g j else 0 := by
          grind
        rw [Finset.sum_congr rfl this, S.sum_ite_eq'
          _ _]
        grind
      omega
  | inr τ =>
      show cutSign τ * c (posCube τ) + simpBdry 0 τ = _
      have hz : simpBdry (0) τ = 0 := by simp [simpBdry]
      have : ∀ t ∈ S, c t * cubeBdry t (Sum.inr τ)
          = if t = posCube τ then cutSign τ * c t else 0 := by
        grind [cubeBdry_inr]
      rw [Finset.sum_congr rfl this,
        S.sum_ite_eq' _ _]
      grind

/-! ### Lemma 3.3 (iii) after the collapse -/

/-- **The cut surface collapses to the zero chain.**  Let `o` be the fundamental cycle of an
oriented triangulated closed surface `L`, so that the cut surface of the truncated complex
`M = C(L) ∖ (neighbourhood of the corner)` carries the cycle `-o` on its cut cells.  Then
after the collapse of all three-cubes of `M` — the collapse of Lemma 3.3 (ii) — the cellular
chain of the cut surface is zero.  This is Lemma 3.3 (iii) in the form used by the capping
argument of (B3): the image of `[Σ_q]` in the two-dimensional spine is the zero chain. -/
theorem cutSurface_cmap_eq_zero {o} (hcyc : simpBdry o = 0)
    (hsupp : ∀ σ : Finset V, σ.card ≠ 3 → o σ = 0)
    (hfaces : ∀ σ : Finset V, σ ∉ L.faces → o σ = 0)
    {l} (hl : Collapse.IsCollapse (spineInc L) l (topCubes L))
    {lp} (hmap : lp.map Prod.fst = l)
    (hchain : CollapseChain.IsChainCollapse (cubeBdry (V := V)) lp) :
    CollapseChain.cmap (cubeBdry (V := V)) lp (Sum.elim 0 (fun τ => -o τ)) = 0 := by
  classical
  have hc : ∀ t, cubeChain o t ≠ 0 → t ∈ topCubes L := by
    intro t ht
    rw [mem_topCubes]
    refine ⟨?_, ?_⟩
    · by_contra hcon
      exact ht (by simp [cubeChain, hfaces _ hcon])
    · by_contra hcon
      exact ht (by simp [cubeChain, hsupp _ hcon])
  have hx : ∀ f,
      Sum.elim (0 : Cube V → ℤ) (fun τ => -o τ) f
        = ∑ t ∈ topCubes L, cubeChain o t * cubeBdry t f := by
    intro f
    rw [← bdryT_eq_sum hc f, cutSurface_isBoundary hcyc hsupp]
    rfl
  have hsub : ∀ t ∈ topCubes L, ∃ f, (t, f) ∈ lp := by
    intro t ht
    have htl := Collapse.mem_list_of_isCollapse hl t ht
    grind
  exact CollapseChain.cmap_eq_zero_of_isBoundary hchain hsub hx
