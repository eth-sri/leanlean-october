module

public import AnalyticESC.Conjugation.Characterisation
public import AnalyticESC.Separation

public section

set_option hygiene false
local notation "𝖓" => List.replicate n k

/-!
# Exact overlaps and sub-conjugation

The remark on exact overlaps in Section 1.2.3: an analytic IFS with a non-singleton attractor and
an exact overlap is sub-conjugated to a self-similar IFS.

The attractor `Λ` is invariant under every composition `f_w`. If `Λ` is finite, then the iterates
of a single map repeat on any two points of `Λ`; as the map is a contraction, injective on `I`,
the two points agree. So a non-singleton attractor is infinite, and an exact overlap `f_i = f_j`
on `Λ` holds on `[0,1]` by the identity theorem. Neither of `i`, `j` is a prefix of the other, so
`ij` and `ji` are distinct words of the same length with `f_{ij} = f_j ∘ f_j = f_{ji}` on `[0,1]`.
The map conjugating `f_{ij}` to a similarity (Theorem 1.12) conjugates the pair.
-/

namespace AnalyticESC

variable {x : ℝ}

open Set Filter

namespace IFS

variable (Φ : IFS N ε) (a : 𝔚 N)

/-! ## Compositions on `I` -/

/-- `f_{uv}(x) = f_u(f_v(x))`, with `f_v(x)` real, for `x ∈ I`. -/
theorem exact_comp_append_ofReal u v (hx : x ∈ I) :
    Φ.comp (u ++ v) x = Φ.comp u ((Φ.comp v x).re : ℂ) := by
  rw [Φ.comp_append, Function.comp_apply, ← Φ.comp_ofReal v hx]

/-! ## The attractor -/

/-- `π(a w) = f_a(π(w))` for a finite word `a` and an infinite word `w`. -/
theorem exact_natProj_prepend w :
    Φ.natProj (fun n => if h : n < a.length then a[n] else w (n - a.length)) =
      (Φ.comp a (Φ.natProj w)).re := by
  set v : 𝔖 N := fun n => if h : n < a.length then a[n] else w (n - a.length)
  have hlist : ∀ n, (List.ofFn fun k : Fin (n + a.length) => v k) =
      a ++ List.ofFn fun k : Fin n => w k := fun n =>
    List.ext_getElem (by grind) fun l h1 h2 => by grind
  have hc : ContinuousAt (fun t : ℝ => (Φ.comp a t).re) (Φ.natProj w) :=
    Complex.continuous_re.continuousAt.comp ((Φ.differentiableAt_comp a
      (Φ.ofReal_mem_cl (Φ.attractor_subset_I ⟨w, rfl⟩))).continuousAt.comp
      Complex.continuous_ofReal.continuousAt)
  refine tendsto_nhds_unique (((tendsto_add_atTop_iff_nat a.length).2
    (Φ.tendsto_natProj v)).congr fun n => ?_) (hc.tendsto.comp (Φ.tendsto_natProj w))
  rw [Function.comp_apply, hlist n, ← Complex.ofReal_zero,
    Φ.exact_comp_append_ofReal _ _ zero_mem_I]

/-- The attractor is invariant under every composition `f_a`. -/
theorem exact_re_comp_mem_attractor
    (hx : x ∈ Φ.attractor) : (Φ.comp a x).re ∈ Φ.attractor := by
  obtain ⟨w, rfl⟩ := hx
  exact ⟨_, Φ.exact_natProj_prepend a w⟩

/-- If the attractor is `{p}`, every map fixes `p`. -/
theorem fixedPoint_of_attractor_singleton (hp : Φ.attractor = {p}) k :
    Φ.f k p = p := by
  have hpA : p ∈ Φ.attractor := by simp_all
  have h := Φ.exact_re_comp_mem_attractor [k] hpA
  have hr : (Φ.f k p).re = p := by simp_all
  have hi := (Φ.inClass k).im_eq_zero p
    (Φ.ofReal_mem_nbhd2 (Φ.attractor_subset_I hpA))
  exact Complex.ext (by omega) (by omega)

/-- A finite attractor has at most one point. -/
theorem exact_attractor_subsingleton (k : Fin N) (hfin : Φ.attractor.Finite) :
    Φ.attractor.Subsingleton := by
  intro x hx y hy
  have hxI := Φ.attractor_subset_I hx
  have hyI := Φ.attractor_subset_I hy
  -- if the iterates `f_k^n` and `f_k^m`, `n < m`, agree at `x` and at `y`, then `f_k^n(x)` and
  -- `f_k^n(y)` are fixed by `f_k^{m-n}`
  have key : ∀ n m, n < m →
      (Φ.comp 𝖓 x).re = (Φ.comp (List.replicate m k) x).re →
      (Φ.comp 𝖓 y).re = (Φ.comp (List.replicate m k) y).re → x = y := by
    intro n m hlt hx' hy'
    obtain ⟨d, rfl⟩ : ∃ d, m = d + n := ⟨m - n, by omega⟩
    have hfix : ∀ z ∈ I,
        (Φ.comp 𝖓 z).re = (Φ.comp (List.replicate (d + n) k) z).re →
        (Φ.comp (List.replicate d k) ((Φ.comp 𝖓 z).re : ℂ)).re =
          (Φ.comp 𝖓 z).re := by
      intro z hz h
      rw [← Φ.exact_comp_append_ofReal _ _ hz, ← List.replicate_add]
      exact h.symm
    exact Φ.injOn_re_comp _ hxI hyI (eq_of_re_eq_self (div_pos Φ.ε_pos four_pos) (Φ.inClass_comp (by aesop)) (Φ.re_comp_mem_I _ hxI)
      (Φ.re_comp_mem_I _ hyI) (hfix x hxI hx') (hfix y hyI hy'))
  have := hfin.to_subtype
  obtain ⟨n, m, hnm, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (β := Φ.attractor × Φ.attractor) fun n =>
      (⟨_, Φ.exact_re_comp_mem_attractor 𝖓 hx⟩,
        ⟨_, Φ.exact_re_comp_mem_attractor 𝖓 hy⟩)
  grind

/-- The attractor of a system with at least one map is infinite unless it is a singleton. -/
theorem attractor_infinite (hN : 0 < N) (hnd : ¬ ∃ x, Φ.attractor = {x}) :
    Φ.attractor.Infinite := by
  intro hfin
  have hk : Φ.natProj (fun _ => (⟨0, hN⟩ : Fin N)) ∈ Φ.attractor := ⟨_, rfl⟩
  rcases (Φ.exact_attractor_subsingleton ⟨0, hN⟩ hfin).eq_empty_or_singleton with he | he
  · grind
  · grind

/-! ## Words of the same length -/

end IFS

end AnalyticESC
