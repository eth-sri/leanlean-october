module
public import GuthMaynard.SecondOrderMeanValue
public import GuthMaynard.NativeSource.GuthMaynard.SecondDerivative

@[expose] public section

open Set

namespace GuthMaynard.NativeMoment

-- Share the classical exponential-sum implementation.
export RiemannZeta.GuthMaynard (
  second_order_mean_value
)

end GuthMaynard.NativeMoment
