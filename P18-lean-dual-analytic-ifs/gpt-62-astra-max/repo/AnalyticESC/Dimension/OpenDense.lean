module
public import AnalyticESC.Dimension.Rapaport
public import AnalyticESC.Generic.OpenDense

@[expose] public section
namespace AnalyticESC
open Set Metric
variable {N : ℕ}
private abbrev Fixed (f : Maps N) := ∃ x : I, ∀ i, (f i x).re = x

namespace IFS
variable (Φ : IFS N)

/-- Project the closed fixed-point relation along the compact interval. -/
private lemma fixed_closed : IsClosed {A : IFS N | Fixed A.f} := by
  have ev (i : Fin N) : Continuous (fun p : IFS N × I => p.1.f i p.2) := (continuous_jet continuous_fst continuous_const 0).eval continuous_snd
  have hc : IsClosed {p : IFS N × I | ∀ i, (p.1.f i p.2).re = p.2} := by
    rw [ofPred_forall]; exact isClosed_iInter fun i => isClosed_eq (by fun_prop) (continuous_subtype_val.comp continuous_snd)
  exact closed_exists hc

private lemma fixed_unique (i : Fin N) {x y : I} (hx : (Φ.f i x).re = x) (hy : (Φ.f i y).re = y) : x = y := by
  have H := Φ.R_lip [i] x.2 y.2
  change |(Φ.f i x).re - (Φ.f i y).re| ≤ _ at H
  rw [hx,hy,List.length_singleton,pow_one] at H
  apply Subtype.ext
  by_contra hn
  nlinarith [Φ.cmax_lt_one,abs_pos.mpr (sub_ne_zero.mpr (show (x:ℝ) ≠ y from by assumption))] -- via strict contraction

/-- If all letters fix `p`, blend towards `p` for all but one letter. The
unchanged fixed point and the moved one then cannot coincide. -/
private lemma nofix_near (hN : 2 ≤ N) (r : ℝ) (hr : 0 < r) : ∃ Ψ : IFS N, dist Φ Ψ < r ∧ ¬ Fixed Ψ.f := by
  by_cases h : Fixed Φ.f
  swap; · exact ⟨Φ,by simpa using hr,h⟩
  obtain ⟨p,hp⟩ := h
  let j : Fin N := ⟨0,by omega⟩
  let k : Fin N := ⟨1,by omega⟩
  have kj : k ≠ j := by grind
  obtain ⟨q,hq⟩ : ∃ q : I, q ≠ p := exists_ne p
  obtain ⟨t,ht,Ψ,hd,e⟩ := Φ.blend hr fun i => if i=j then q else p
  refine ⟨Ψ,hd,?_⟩; rintro ⟨x,hx⟩
  have ek : (Ψ.f k p).re = p := by rw [e,ite_eq_right kj,hp k]; ring
  have hx' := Ψ.fixed_unique k (hx k) ek
  grind [hp j]

end IFS

theorem corollary_1_7 (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) (hN : 2 ≤ N) :
    Generic (@Challenge.DimEquality N) := by
  obtain ⟨U,ho,hd,H⟩ := sesc_region N
  have op := (IFS.fixed_closed (N := N)).isOpen_compl
  have de : Dense {A : IFS N | Fixed A.f}ᶜ := Metric.dense_iff.mpr fun Φ r hr => by
    obtain ⟨Ψ,d,h⟩ := Φ.nofix_near hN r hr; exact ⟨Ψ,mem_ball'.mpr d,h⟩
  apply generic_region (ho.inter op) (hd.inter_of_isOpen_left de ho)
  rintro Φ ⟨h,hf⟩
  have pos : 0 < N := by omega
  refine Φ.theorem_1_6 hM hS pos ?_ (Φ.esc_of_sesc (H Φ h))
  rw [Φ.exists_attractor_eq_singleton_iff pos]; exact fun ⟨x,hx,e⟩ => hf ⟨⟨x,hx⟩,e⟩

end AnalyticESC
