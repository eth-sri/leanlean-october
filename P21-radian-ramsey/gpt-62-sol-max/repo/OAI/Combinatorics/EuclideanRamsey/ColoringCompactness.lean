/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/ColoringCompactness.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Adapted to the Lean module system and simplified for this proof.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.CornerGroup
public import OAI.Combinatorics.EuclideanRamsey.PathSynchronization

@[expose] public section

namespace OAI.EuclideanRamsey

noncomputable section

open Filter

attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

/-- An ultrafilter tuple represents a path if each product neighborhood contains a string
family with the prescribed energy. -/
private def UltraPath {ι : Type*} (a : ι → Hilbert) (U : ι → Ultrafilter Strings) (u : ℝ) : Prop :=
  ∀ B : ι → Set Strings, (∀ i, B i ∈ U i) → ∃ x, StringFamily a u x ∧ ∀ i, x i ∈ B i

private lemma UltraPath.common {ι : Type*} [Finite ι] (a : ι → Hilbert) (U : Ultrafilter Strings) :
    UltraPath a (fun _ => U) 0 := by
  intro B hB
  obtain ⟨x,hx⟩ := (Filter.eventually_all.mpr hB).exists
  exact ⟨_, by simp [StringFamily], hx⟩

private lemma UltraPath.copy {ι : Type*} {a b : ι → Hilbert} {u : ℝ} (h : CopyPath a u b) :
    UltraPath a (fun i => pure (FreeMonoid.of (b i))) u := by
  intro B hB
  refine ⟨_, ⟨fun _ _ => rfl,fun i j => ?_⟩, hB⟩
  simpa [FreeMonoid.toList_of,Hilbert.flatten_cons_dist] using h.2 i j

private lemma UltraPath.mul {ι : Type*} {a : ι → Hilbert} {U V : ι → Ultrafilter Strings}
    {u v : ℝ} (h : UltraPath a U u) (h' : UltraPath a V v) : UltraPath a (U*V) (u+v) := by
  intro B hB
  have hh (i : ι) : {x | {y | x*y ∈ B i} ∈ V i} ∈ U i :=
    (Ultrafilter.eventually_mul _ _ _).mp (hB i)
  obtain ⟨x,hx,hBx⟩ := h _ hh
  obtain ⟨y,hy,hBy⟩ := h' _ hBx
  exact ⟨x*y, hx.mul hy, hBy⟩

private lemma Path.ultra {ι : Type*} [Finite ι] {a : ι → Hilbert} {w u}
    (h : Path a w u) (Ψ : LetterGroup →ₙ* Ultrafilter Strings) (p : Ultrafilter Strings)
    (hgen : ∀ z, Ψ (FreeGroup.of z) = p * pure (FreeMonoid.of z) * p) :
    UltraPath a (fun i => Ψ (w i)) u := by
  induction h with
  | diag g => exact UltraPath.common a _
  | copy b hb =>
    simpa only [Pi.mul_def, hgen, zero_add, add_zero] using
      ((UltraPath.common a p).mul (UltraPath.copy hb)).mul (UltraPath.common a p)
  | mul _ _ ih ih' => simpa only [Pi.mul_def, map_mul] using ih.mul ih'

theorem paths_ramsey {s d : ℕ} (a : Fin s → Space d)
    (hpaths : let A i := Hilbert.embed (Fin d) (a i)
      ∀ ε > (0:ℝ), ∃ w lmb μ, Path A w lmb ∧ Path A w μ ∧ 0 < lmb ∧ μ/lmb < ε) : Ramsey a := by
  classical
  intro r _
  by_contra! hc
  let u : Hilbert := lp.single 2 0 1
  have hu : u ≠ 0 := fun h => by simpa [u] using congrArg (fun x : Hilbert => x 0) h
  let V (S : Finset Hilbert) := Submodule.span ℝ ((insert u S : Finset Hilbert) : Set Hilbert)
  have mem_V (S : Finset Hilbert) {x : Hilbert} (hx : x ∈ S) : x ∈ V S :=
    Submodule.subset_span (Finset.mem_insert_of_mem hx)
  have (S : Finset Hilbert) : FiniteDimensional ℝ (V S) := FiniteDimensional.span_of_finite ℝ (Finset.finite_toSet _)
  have hpos (S : Finset Hilbert) : 1 ≤ Module.finrank ℝ (V S) := by
    exact Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨u,Submodule.subset_span (Finset.mem_insert_self ..)⟩, fun h => hu (congrArg Subtype.val h)⟩
  choose C₀ hC₀ using hc
  let g (S : Finset Hilbert) := (stdOrthonormalBasis ℝ (V S)).repr
  let f (S : Finset Hilbert) (x : S) : Fin r := C₀ _ (hpos S) (g S ⟨x,mem_V S x.property⟩)
  obtain ⟨c,hc'⟩ := Finset.rado_selection_subtype (β:=fun _ : Hilbert => Fin r) f
  let A i := Hilbert.embed (Fin d) (a i)
  obtain ⟨β,hβ,hHJ⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin s) (Fin r)
  let := hβ
  obtain ⟨w,lmb,μ,hp,hm,hlmb,hratio⟩ := hpaths (1/((Fintype.card β+1:ℕ):ℝ)) (by positivity)
  obtain ⟨W,hW⟩ := synchronize_paths (Fintype.card β+1) (by omega) hp hm hlmb hratio
  obtain ⟨p,Ψ,hgen⟩ := exists_corner_hom Ultrafilter.continuous_mul_left (fun z : Hilbert => pure (FreeMonoid.of z))
  let coloring : Strings → (Fin r) := fun x => c (Hilbert.flatten x.toList)
  let L : List β := Finset.univ.toList
  let word (x : β → Fin s) := (L.map (fun j => W (x j))).prod
  have hcolor (x : β → Fin s) : ∃ k,{l | coloring l=k} ∈ Ψ (word x) :=
    Ultrafilter.eventually_exists_iff.mp (Eventually.of_forall fun l => ⟨coloring l,rfl⟩)
  choose C hC using hcolor
  obtain ⟨line,k,hline⟩ := hHJ C
  let S : Finset β := Finset.univ.filter (fun j => line.idxFun j=none)
  let t := S.card
  have ht : 1 ≤ t := Finset.card_pos.mpr (line.proper.imp fun j hj => by simp [S,hj])
  have ht' : t ≤ Fintype.card β+1 := (Finset.card_le_univ S).trans (Nat.le_succ _)
  let u (j : β) : ℝ := if line.idxFun j=none then 1/(t:ℝ) else 0
  have hloc (j : β) : Path A (fun i => W (line i j)) (u j) := by
    cases hj : line.idxFun j with
    | none => simpa [u,hj] using hW t ht ht'
    | some i => simpa [u,hj] using Path.diag (a:=A) (W i)
  have hweight : (L.map u).sum=1 := by
    have h := (show (L.map u).sum = ∑ j,u j by simp [L])
    rw [h]
    simp only [u,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_one_div_cancel (by positivity)
  have hp : Path A (fun i => word (line i)) 1 := hweight ▸ Path.list_prod L _ u (fun j _ => hloc j)
  obtain ⟨xs,hxs,hmono⟩ := hp.ultra Ψ p hgen (fun _ => {x | coloring x=k}) (fun i => hline i ▸ hC (line i))
  let b i := Hilbert.flatten (xs i).toList
  obtain ⟨T,hT,hCT⟩ := hc' (Finset.univ.image b)
  let z (i : Fin s) : V T := ⟨b i,mem_V T (hT (by simp))⟩
  obtain ⟨i,hi⟩ := hC₀ _ (hpos T) (g T ∘ z) (fun i j => by
    rw [← sq_eq_sq₀ dist_nonneg dist_nonneg]
    simpa [dist_eq_norm,Function.comp_def,z,b,A,← map_sub] using hxs.2 i j) k
  exact hi ((hCT ⟨b i,by simp⟩).symm.trans (hmono i))
end
end OAI.EuclideanRamsey
