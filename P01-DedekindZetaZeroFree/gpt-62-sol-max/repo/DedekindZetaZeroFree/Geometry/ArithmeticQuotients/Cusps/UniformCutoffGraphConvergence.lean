module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.CutoffGraphConvergence

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Filter
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
  (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
  (a : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

 theorem highEnds_subset_closedHighEnds (T : ℝ) :
    highEnds F ζ hζ hF U a T ⊆ closedHighEnds F ζ hζ hF U a T := by
  intro x hx
  simp only [highEnds, closedHighEnds, Set.mem_iUnion, Set.mem_image] at hx ⊢
  rcases hx with ⟨i,c,y,hy,hxy⟩
  refine ⟨i,c,y,?_,hxy⟩
  rcases hy with ⟨z,hz,rfl⟩
  rcases hz with ⟨w,hw,rfl⟩
  refine ⟨_,⟨w,?_,rfl⟩,rfl⟩
  change T ≤ KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) w
  exact le_of_lt (show T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) w from hw)

theorem cutoff_next_eventually_one {r s : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ}
    (n : ℕ) (i : Fin a.componentCount) (x : Arch F)
    (hc : ContinuousAt (fun y => r (basePoint F ζ hζ hF U a i y)) x)
    (hx : r (basePoint F ζ hζ hF U a i x) = 1)
    (hs : ∀ y ∉ highEnds F ζ hζ hF U a (↑(n+1)), s y = 1)
    (hr : ∀ y ∈ closedHighEnds F ζ hζ hF U a (n+1), r y = 0) :
    (fun y => s (basePoint F ζ hζ hF U a i y)) =ᶠ[nhds x] fun _ => 1 := by
  filter_upwards [hc.eventually (lt_mem_nhds (by rw [hx]; norm_num :
    0 < r (basePoint F ζ hζ hF U a i x)))] with y hy
  apply hs
  intro hy'
  have hz := highEnds_subset_closedHighEnds F ζ hζ hF U a (↑(n+1)) hy'
  exact hy.ne' (hr _ (by simpa only [Nat.cast_add, Nat.cast_one] using hz))

 theorem laplacian_congr_nhds (d : ℕ) {f g : HyperbolicChart.Space d → ℂ}
    {x : HyperbolicChart.Space d} (h : f =ᶠ[nhds x] g) :
    HyperbolicChart.laplacian d f x = HyperbolicChart.laplacian d g x := by
  have hd (i : Fin d) (k : Fin 3) :
      HyperbolicChart.coordinateDerivative d i k f =ᶠ[nhds x]
        HyperbolicChart.coordinateDerivative d i k g := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun A : HyperbolicChart.Space d →L[ℝ] ℂ =>
      A (HyperbolicChart.coordinateVector d i k)) hy
  unfold HyperbolicChart.laplacian
  apply Finset.sum_congr rfl
  intro i hi
  have h2 (k : Fin 3) := (hd i k).fderiv_eq (𝕜 := ℝ)
  simp only [HyperbolicChart.coordinateDerivative, h2, h.fderiv_eq (𝕜 := ℝ)]

end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

end
