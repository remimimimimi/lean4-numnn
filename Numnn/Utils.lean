import Numnn.Matrix

namespace Numnn.Utils

def uniformDistribution (low high : Float) : IO Float := do
  let diff := high - low
  let scale := 10000.0
  let scaled_difference := diff * scale
  let rand ← IO.rand 0 (scaled_difference.toUSize.toNat)
  return low + (1.0 * rand.toFloat / scale)
