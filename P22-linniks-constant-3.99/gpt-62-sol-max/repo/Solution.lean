module
import GradedNear.Builder
import GradedNear.Cert.Sound
import GradedNear.Conj

/-!
# The graded near lemma and the leaf-certificate checker

`comparator.json` lists the compared theorems. The analytic estimate is assembled in
`GradedNear.Statement`; `GradedNear.Response` and `GradedNear.ZeroForm` give its zero form.
`GradedNear.Builder` and `GradedNear.Conj` handle the entry bounds and the bridge to the LP.
`GradedNear.Cert.Sound` proves soundness of the integer certificate checker.
-/
