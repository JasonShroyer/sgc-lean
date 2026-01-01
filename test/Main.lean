import SGC.Spectral.Envelope
import Mathlib.LinearAlgebra.Matrix.Notation

open Matrix SGC Real

/-- 
Smoke Test: 
Instantiate the HeatKernel for a simple 2-state system (Coin Flip).
If this compiles, our typeclass inference for [Fintype V] and Matrix algebra is working.
-/
def main : IO Unit := do
  -- 1. Define the space V = {0, 1}
  let _ : Fintype (Fin 2) := inferInstance
  
  -- 2. Define a simple Laplacian L = -I (Decay)
  let L : Matrix (Fin 2) (Fin 2) ℝ := ![![-1, 0], ![0, -1]]
  
  -- 3. Define a time t
  let t : ℝ := 1.0

  -- 4. Attempt to compute the HeatKernel (this triggers the MatrixExponential library)
  let K := HeatKernel L t

  -- 5. Print a success message
  IO.println "Environment is healthy. HeatKernel compiled successfully for Fin 2 system."
