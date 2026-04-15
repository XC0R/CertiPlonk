import ArkLib.ProofSystem.ConstraintSystem.Plonk

/-! ## Reusable gate constructors for AIR → Plonk translation

Standard Plonk gates (add, mul, bool, eq) are defined in ArkLib. These additional
gate types arise naturally when flattening AIR constraints into degree-2 Plonk gates:

- `scalarMul k a c`: constrains `x(c) = k * x(a)`
- `wireEq a c`: constrains `x(c) = x(a)` (special case of scalarMul with k=1)

Both are degree-1 and need no intermediate wires themselves.
-/

namespace Plonk.Gate

variable {𝓡 : Type} [CommRing 𝓡] {numWires : ℕ}

def scalarMul (k : 𝓡) (a c : Fin numWires) : Gate 𝓡 numWires :=
  { qL := k, qR := 0, qO := -1, qM := 0, qC := 0, a := a, b := a, c := c }

def wireEq (a c : Fin numWires) : Gate 𝓡 numWires :=
  { qL := 1, qR := 0, qO := -1, qM := 0, qC := 0, a := a, b := a, c := c }

variable {a c : Fin numWires} {x : Fin numWires → 𝓡}

@[simp]
theorem scalarMul_accepts_iff {k : 𝓡} :
    (scalarMul k a c).accepts x ↔ x c = k * x a := by
  simp [scalarMul, Gate.accepts, Gate.eval, add_neg_eq_zero, eq_comm]

@[simp]
theorem wireEq_accepts_iff :
    (wireEq a c).accepts x ↔ x c = x a := by
  simp [wireEq, Gate.accepts, Gate.eval, add_neg_eq_zero, eq_comm]

end Plonk.Gate
