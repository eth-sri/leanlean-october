module

public import RequestProject.CollapseChainMap
public import RequestProject.SpineCollapse

@[expose] public section

namespace FiniteChains

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable def cubeBdry (t : Cube V) : Cube V ⊕ Finset V → ℤ :=
  Sum.elim (fun g => bdry (fun f => if f = t then 1 else 0) g)
    (fun τ => cutSign τ * (if posCube τ = t then 1 else 0))

theorem cubeBdry_inl (t g : Cube V) :
    cubeBdry t (Sum.inl g)
      = ∑ j ∈ univ.filter (fun j => g j ≠ CubeCoord.free),
          incid g j * (if Function.update g j CubeCoord.free = t then 1 else 0) := rfl

theorem cubeBdry_inr (t : Cube V) (τ : Finset V) :
    cubeBdry t (Sum.inr τ) = cutSign τ * (if posCube τ = t then 1 else 0) := rfl

omit [Fintype V] [LinearOrder V] in
theorem update_free_injective {g : Cube V} {j k : V} (hj : g j ≠ CubeCoord.free)
    (h : Function.update g j CubeCoord.free = Function.update g k CubeCoord.free) : j = k := by
  by_contra hjk
  have hval := congrFun h j
  rw [Function.update_apply, if_pos rfl, Function.update_apply, if_neg hjk] at hval
  exact hj hval.symm

theorem cubeBdry_inl_eq_unit {L : ASC V} {g t : Cube V} (ht : t ∈ cofaces L g) :
    cubeBdry t (Sum.inl g) = 1 ∨ cubeBdry t (Sum.inl g) = -1 := by
  classical
  obtain ⟨j, hj, -, rfl⟩ := mem_cofaces.1 ht
  rw [cubeBdry_inl, Finset.sum_eq_single j
    (fun k hk hkj => by
      rw [if_neg (fun hcon => hkj (update_free_injective (by simpa using hk) hcon)), mul_zero])
    (fun hcon => absurd (by simp [hj]) hcon), if_pos rfl, mul_one]
  have hs : (g j).sgn = 1 ∨ (g j).sgn = -1 := by
    rcases h : g j with _ | _ | _
    exacts [absurd h hj, .inl rfl, .inr rfl]
  rcases Nat.even_or_odd ((freeSet g).filter (fun i => i < j)).card with he | ho
  · rw [incid, he.neg_one_pow, one_mul]; exact hs
  · rw [incid, ho.neg_one_pow]; rcases hs with h | h <;> rw [h] <;> simp

theorem cubeBdry_inl_eq_zero {L : ASC V} {g t : Cube V} (htop : t ∈ topCubes L)
    (ht : t ∉ cofaces L g) : cubeBdry t (Sum.inl g) = 0 := by
  classical
  rw [cubeBdry_inl]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [if_neg (fun hcon => ht (mem_cofaces.2 ⟨j, by simpa using hj, by
    rw [show insert j (freeSet g) = freeSet (Function.update g j CubeCoord.free) by
      ext i; by_cases hij : i = j <;> simp [hij], hcon]
    exact (mem_topCubes.1 htop).1, hcon.symm⟩)), mul_zero]

theorem cubeBdry_inr_eq_neg_one {τ : Finset V} (hτ : τ.card = 3) :
    cubeBdry (posCube τ) (Sum.inr τ) = -1 := by
  rw [cubeBdry_inr, if_pos rfl, mul_one, cutSign, hτ]; norm_num

theorem cubeBdry_inr_eq_zero {t : Cube V} {τ : Finset V} (h : t ≠ posCube τ) :
    cubeBdry t (Sum.inr τ) = 0 := by
  rw [cubeBdry_inr, if_neg (Ne.symm h), mul_zero]

theorem Collapse.mem_list_of_isCollapse {T F : Type*} [DecidableEq T] {inc : F → Finset T}
    {l : List T} {S : Finset T} (h : Collapse.IsCollapse inc l S) : ∀ t ∈ S, t ∈ l := by
  induction l generalizing S with
  | nil => intro t ht; exact absurd (h ▸ ht) (Finset.notMem_empty t)
  | cons u l ih =>
      intro t ht
      exact if htu : t = u then htu ▸ List.mem_cons_self
        else List.mem_cons_of_mem _ (ih h.2.2 t (Finset.mem_erase.2 ⟨htu, ht⟩))

theorem cutSurface_cmap_eq_zero {L : ASC V} {o : Finset V → ℤ} (hcyc : simpBdry o = 0)
    (hsupp : ∀ σ : Finset V, σ.card ≠ 3 → o σ = 0)
    (hfaces : ∀ σ : Finset V, σ ∉ L.faces → o σ = 0)
    {l : List (Cube V)} (hl : Collapse.IsCollapse (spineInc L) l (topCubes L))
    {lp : List (Cube V × (Cube V ⊕ Finset V))} (hmap : lp.map Prod.fst = l)
    (hchain : CollapseChain.IsChainCollapse (cubeBdry (V := V)) lp) :
    CollapseChain.cmap (cubeBdry (V := V)) lp (Sum.elim 0 (fun τ => -o τ)) = 0 := by
  classical
  have hc (t : Cube V) (ht : cubeChain o t ≠ 0) : t ∈ topCubes L :=
    mem_topCubes.2 ⟨by by_contra hcon; exact ht (by simp [cubeChain, hfaces _ hcon]),
      by by_contra hcon; exact ht (by simp [cubeChain, hsupp _ hcon])⟩
  have hsum (f : Cube V ⊕ Finset V) :
      Sum.elim (bdryT (cubeChain o, 0)).1 (bdryT (cubeChain o, 0)).2 f =
        ∑ t ∈ topCubes L, cubeChain o t * cubeBdry t f := by
    cases f with
    | inl g =>
        show bdry (cubeChain o) g = _
        simp only [bdry, cubeBdry_inl, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_congr rfl (show ∀ t ∈ topCubes L,
            cubeChain o t * (incid g j * if Function.update g j CubeCoord.free = t then 1 else 0) =
            if t = Function.update g j CubeCoord.free then cubeChain o t * incid g j else 0 from
          fun t _ => by
            by_cases htj : t = Function.update g j CubeCoord.free
            · subst htj; simp
            · rw [if_neg htj, if_neg (Ne.symm htj), mul_zero, mul_zero]),
          Finset.sum_ite_eq' (topCubes L) (Function.update g j CubeCoord.free)
            (fun t => cubeChain o t * incid g j)]
        by_cases hmem : Function.update g j CubeCoord.free ∈ topCubes L
        · rw [if_pos hmem, mul_comm]
        · rw [if_neg hmem, show cubeChain o (Function.update g j CubeCoord.free) = 0 by
            by_contra hcon; exact hmem (hc _ hcon), mul_zero]
    | inr τ =>
        show cutSign τ * cubeChain o (posCube τ) + simpBdry 0 τ = _
        rw [show simpBdry (0 : Finset V → ℤ) τ = 0 by simp [simpBdry], add_zero,
          Finset.sum_congr rfl (show ∀ t ∈ topCubes L,
              cubeChain o t * cubeBdry t (Sum.inr τ) =
              if t = posCube τ then cutSign τ * cubeChain o t else 0 from
            fun t _ => by
              rw [cubeBdry_inr]
              by_cases htp : t = posCube τ
              · subst htp; ring_nf; simp
              · rw [if_neg (Ne.symm htp), if_neg htp, mul_zero, mul_zero]),
          Finset.sum_ite_eq' (topCubes L) (posCube τ) (fun t => cutSign τ * cubeChain o t)]
        by_cases hmem : posCube τ ∈ topCubes L
        · rw [if_pos hmem]
        · rw [if_neg hmem, show cubeChain o (posCube τ) = 0 by
            by_contra hcon; exact hmem (hc _ hcon), mul_zero]
  refine CollapseChain.cmap_eq_zero_of_isBoundary (c := cubeChain o) (s := topCubes L)
    hchain (fun t ht => ?_) fun f => ?_
  · obtain ⟨p, hp, hp1⟩ := List.mem_map.1 (hmap ▸ Collapse.mem_list_of_isCollapse hl t ht)
    exact ⟨p.2, hp1 ▸ hp⟩
  · rw [← hsum f, cutSurface_isBoundary hcyc hsupp]
    cases f <;> rfl

end FiniteChains
