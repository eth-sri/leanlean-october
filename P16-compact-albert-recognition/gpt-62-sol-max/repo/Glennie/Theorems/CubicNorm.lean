module

public import Glennie.Compact.ObservationData
/- The explicit compact cubic norm and its frame-encoder vanishing. -/

@[expose] public section

namespace Glennie
noncomputable section
open Glennie.SubmissionR04Intrinsic

set_option maxHeartbeats 2000000

/-- The native Cayley–Dickson coordinate formula, with the fixed triangle order. -/
theorem newtonCubicNorm_coordinates (x : Albert) :
    nativeCubic x = x.d0 * x.d1 * x.d2 - x.d0 * octNormSq x.o12 -
      x.d1 * octNormSq x.o02 - x.d2 * octNormSq x.o01 +
      2 * octRe (octMul (octMul x.o01 x.o12) (octConj x.o02)) := by
  simp [nativeCubic, inner, trace, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj,
    octRe, octNormSq, Quaternion.normSq_def', 
       smul_eq_mul]
  ring

/-- Every actual frame encoder has zero cubic norm, directly from its frame laws. -/
theorem frame_encoder_cubicNorm (p : Fin 3 → Albert) (hp : Frame p) :
    nativeCubic (encoder p) = 0 := by
  simp [nativeCubic, inner, frame_encoder_trace p hp, frame_encoder_cube p hp]

end
end Glennie
