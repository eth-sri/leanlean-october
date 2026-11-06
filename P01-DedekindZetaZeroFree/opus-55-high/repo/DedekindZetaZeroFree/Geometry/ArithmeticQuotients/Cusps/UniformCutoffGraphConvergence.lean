module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.CutoffGraphConvergence

@[expose] public section

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

 theorem cutoff_next_eventually_one (r : Cutoffs F ζ hζ hF U a)
    (n : ℕ) (hn : r.height_bound ≤ n) (i : Fin a.componentCount) (x : Arch F)
    (hx : basePoint F ζ hζ hF U a i x ∉ highEnds F ζ hζ hF U a n) :
    (fun y : Arch F => r.rho (n+1) (basePoint F ζ hζ hF U a i y)) =ᶠ[nhds x] fun _ => 1 := by
  have hrx := r.on_sublevel n hn _ hx
  have hpos : ∀ᶠ y : Arch F in nhds x, 0 < r.rho n (basePoint F ζ hζ hF U a i y) :=
    (r.smooth n i).continuous.continuousAt.eventually (lt_mem_nhds (by simpa [hrx] : (0:ℝ) < r.rho n (basePoint F ζ hζ hF U a i x)))
  filter_upwards [hpos] with y hy
  apply r.on_sublevel (n+1) (by omega)
  intro hhigh
  have hclosed := highEnds_subset_closedHighEnds F ζ hζ hF U a (↑(n+1)) hhigh
  have hz := r.above_next n hn _ (by simpa only [Nat.cast_add, Nat.cast_one] using hclosed)
  linarith

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
