module
public import Solution.LocalTransport
public import Solution.OrbitChart
public import Solution.BasedCubic

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
set_option autoImplicit false
open AlbertGeometry RecognitionFromCurvature
set_option maxHeartbeats 1800000 in
private theorem reconstruct {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] (P : BasedCubic E) (e : E) (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) (A : E ≃ₗ[ℝ] Albert) (hu : A e = 1)
    (h : ∀ x y z, 6 * P.form ![x,y,z] = newton3 (A x) (A y) (A z)) :
    Nonempty (ReconstructionResult P e) := by
  have ht (x : E) : traceAt P e x = trace (A x) := by
    have H := h e e x; simp only [hu,newton3,jordan_unit_left,inner_unit_left,Glennie.trace_unit] at H
    simp only [trace_eq,ContinuousLinearMap.smul_apply,smul_eq_mul,tri_apply]; linarith
  have hb (x y : E) : rawPair P e x y = inner (A x) (A y) := by
    have H := h e x y; simp only [hu,newton3,jordan_unit_left,inner_unit_left,Glennie.trace_unit] at H
    rw [rawPair_apply,ht,ht,tri_apply]; linarith
  have prod (x y : E) : A (product P e x y) = jordan (A x) (A y) := by
    apply _root_.ext_inner_right ℝ; intro w; obtain ⟨z,rfl⟩ := A.surjective w
    change inner _ _ = inner _ _
    rw [← hb,product_pair P he hp,ht,ht,hb,hb,hb,ht,tri_apply]
    have H := h x y z; unfold newton3 at H; linarith
  have conn (x y : E) : A (ambientConnection P e x y) = -jordan (A x) (A y) := by rw [connection_product P he hp,map_neg,prod]
  let J : Local.ChartIso e (fun x => traceAt P e x) (product P e) := ⟨A,hu,ht,prod⟩
  apply J.result
  · intro x; change nativeCubic (A x) = cubic P x
    simp only [nativeCubic,cubic_diag,tri_apply,inner_comm (A x) (jordan _ _)]
    have H := h x x x; unfold newton3 at H; linarith
  · intro x y; change _ = inner (A x) (A y) / 3; linarith [raw_metric P he x y,hb x y]
  · exact hb
  · exact conn
  · intro x y z; change A (ambientCurvature P e x y z) = _
    rw [curvature_comm P (by simp [he]) (invertible_of_positive _ hp), map_neg,map_sub,conn,conn,conn,conn,
      jordan_neg_right,jordan_neg_right,neg_neg,neg_neg]

theorem intrinsic_local_reconstruction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (P : BasedCubic E) (e : E) (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x)
    (hMatch : ∃ F : NativeTangent ≃ₗ[ℝ] tangent P e,
      (∀ x y : NativeTangent,
        metric P e (F x : E) (F y : E) = nativeMetric x y) ∧
      (∀ x y z : NativeTangent,
        independentCurvature P e (F x) (F y) (F z) =
          F (nativeCurvature x y z))) :
    Nonempty (ReconstructionResult P e) := by
  obtain ⟨F, hm, hc⟩ := hMatch
  obtain ⟨A,hu,h⟩ := polarized_of_match P e he hp F hm hc
  exact reconstruct P e he hp A hu h

end
end Glennie.SubmissionR04Intrinsic
