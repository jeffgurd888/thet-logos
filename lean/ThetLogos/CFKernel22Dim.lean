import ThetLogos.CFKernelRetarget

/-!
# T4 Closure: Dimension bound for the order-one kernel (shim)

The 8 color-universality identifications (`ident_yU_*`) and their sparsity
helpers used to live in this module. They were moved into
`ThetLogos.CFKernelRetarget` (§T4b½, 2026-09-30) because §T4c there uses
them directly and this module imports `ThetLogos.CFKernel22`, which
imports `CFKernelRetarget` — importing back would be a cycle.
This module is kept as a thin shim so the name still resolves.
-/
