import ArkLib.ProofSystem.ConstraintSystem.Plonk
import CertiPlonk.Add8Air.Constraints
import CertiPlonk.Fundamentals.BabyBear

open BabyBear Plonk Add8Air.constraints

namespace CertiPlonk.Bridge

variable [Field ExtF]

/-! ## Wire layout (28 wires, 27 gates)

  Original columns (12):
    0=a, 1=b, 2=c, 3=r, 4=c₀, 5=c₁, 6=c₂, 7=c₃, 8=c₄, 9=c₅, 10=c₆, 11=c₇

  Intermediate wires for constraint_0 (a + b = r*256 + c):
    12 = r*256,  13 = a+b

  Intermediate wires for constraint_2 (c = c₀ + c₁*2 + ... + c₇*128):
    14..20 = cᵢ * 2^i for i=1..7
    21..27 = partial sums
-/

private def Gate.scalarMul (k : FBB) (a c : Fin 28) : Gate FBB 28 :=
  { qL := k, qR := 0, qO := -1, qM := 0, qC := 0, a := a, b := a, c := c }

private def Gate.wireEq (a c : Fin 28) : Gate FBB 28 :=
  { qL := 1, qR := 0, qO := -1, qM := 0, qC := 0, a := a, b := a, c := c }

@[reducible] def add8airCS : ConstraintSystem FBB 28 27
  | ⟨0, _⟩ => Gate.scalarMul 256 ⟨3, by omega⟩ ⟨12, by omega⟩
  | ⟨1, _⟩ => Gate.add ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨13, by omega⟩
  | ⟨2, _⟩ => Gate.add ⟨12, by omega⟩ ⟨2, by omega⟩ ⟨13, by omega⟩
  | ⟨3, _⟩ => Gate.bool ⟨3, by omega⟩
  | ⟨4, _⟩ => Gate.scalarMul 2 ⟨5, by omega⟩ ⟨14, by omega⟩
  | ⟨5, _⟩ => Gate.scalarMul 4 ⟨6, by omega⟩ ⟨15, by omega⟩
  | ⟨6, _⟩ => Gate.scalarMul 8 ⟨7, by omega⟩ ⟨16, by omega⟩
  | ⟨7, _⟩ => Gate.scalarMul 16 ⟨8, by omega⟩ ⟨17, by omega⟩
  | ⟨8, _⟩ => Gate.scalarMul 32 ⟨9, by omega⟩ ⟨18, by omega⟩
  | ⟨9, _⟩ => Gate.scalarMul 64 ⟨10, by omega⟩ ⟨19, by omega⟩
  | ⟨10, _⟩ => Gate.scalarMul 128 ⟨11, by omega⟩ ⟨20, by omega⟩
  | ⟨11, _⟩ => Gate.add ⟨4, by omega⟩ ⟨14, by omega⟩ ⟨21, by omega⟩
  | ⟨12, _⟩ => Gate.add ⟨21, by omega⟩ ⟨15, by omega⟩ ⟨22, by omega⟩
  | ⟨13, _⟩ => Gate.add ⟨22, by omega⟩ ⟨16, by omega⟩ ⟨23, by omega⟩
  | ⟨14, _⟩ => Gate.add ⟨23, by omega⟩ ⟨17, by omega⟩ ⟨24, by omega⟩
  | ⟨15, _⟩ => Gate.add ⟨24, by omega⟩ ⟨18, by omega⟩ ⟨25, by omega⟩
  | ⟨16, _⟩ => Gate.add ⟨25, by omega⟩ ⟨19, by omega⟩ ⟨26, by omega⟩
  | ⟨17, _⟩ => Gate.add ⟨26, by omega⟩ ⟨20, by omega⟩ ⟨27, by omega⟩
  | ⟨18, _⟩ => Gate.wireEq ⟨2, by omega⟩ ⟨27, by omega⟩
  | ⟨19, _⟩ => Gate.bool ⟨4, by omega⟩
  | ⟨20, _⟩ => Gate.bool ⟨5, by omega⟩
  | ⟨21, _⟩ => Gate.bool ⟨6, by omega⟩
  | ⟨22, _⟩ => Gate.bool ⟨7, by omega⟩
  | ⟨23, _⟩ => Gate.bool ⟨8, by omega⟩
  | ⟨24, _⟩ => Gate.bool ⟨9, by omega⟩
  | ⟨25, _⟩ => Gate.bool ⟨10, by omega⟩
  | ⟨26, _⟩ => Gate.bool ⟨11, by omega⟩
  | ⟨n + 27, h⟩ => absurd h (by omega)

@[reducible] def extWireAssignment (air : Valid_Add8Air FBB ExtF) (row : ℕ) : Fin 28 → FBB
  | ⟨0, _⟩ => air.a row 0
  | ⟨1, _⟩ => air.b row 0
  | ⟨2, _⟩ => air.c row 0
  | ⟨3, _⟩ => air.r row 0
  | ⟨4, _⟩ => air.c₀ row 0
  | ⟨5, _⟩ => air.c₁ row 0
  | ⟨6, _⟩ => air.c₂ row 0
  | ⟨7, _⟩ => air.c₃ row 0
  | ⟨8, _⟩ => air.c₄ row 0
  | ⟨9, _⟩ => air.c₅ row 0
  | ⟨10, _⟩ => air.c₆ row 0
  | ⟨11, _⟩ => air.c₇ row 0
  | ⟨12, _⟩ => air.r row 0 * 256
  | ⟨13, _⟩ => air.a row 0 + air.b row 0
  | ⟨14, _⟩ => air.c₁ row 0 * 2
  | ⟨15, _⟩ => air.c₂ row 0 * 4
  | ⟨16, _⟩ => air.c₃ row 0 * 8
  | ⟨17, _⟩ => air.c₄ row 0 * 16
  | ⟨18, _⟩ => air.c₅ row 0 * 32
  | ⟨19, _⟩ => air.c₆ row 0 * 64
  | ⟨20, _⟩ => air.c₇ row 0 * 128
  | ⟨21, _⟩ => air.c₀ row 0 + air.c₁ row 0 * 2
  | ⟨22, _⟩ => air.c₀ row 0 + air.c₁ row 0 * 2 + air.c₂ row 0 * 4
  | ⟨23, _⟩ => air.c₀ row 0 + air.c₁ row 0 * 2 + air.c₂ row 0 * 4 + air.c₃ row 0 * 8
  | ⟨24, _⟩ => air.c₀ row 0 + air.c₁ row 0 * 2 + air.c₂ row 0 * 4 + air.c₃ row 0 * 8 +
               air.c₄ row 0 * 16
  | ⟨25, _⟩ => air.c₀ row 0 + air.c₁ row 0 * 2 + air.c₂ row 0 * 4 + air.c₃ row 0 * 8 +
               air.c₄ row 0 * 16 + air.c₅ row 0 * 32
  | ⟨26, _⟩ => air.c₀ row 0 + air.c₁ row 0 * 2 + air.c₂ row 0 * 4 + air.c₃ row 0 * 8 +
               air.c₄ row 0 * 16 + air.c₅ row 0 * 32 + air.c₆ row 0 * 64
  | ⟨27, _⟩ => air.c₀ row 0 + air.c₁ row 0 * 2 + air.c₂ row 0 * 4 + air.c₃ row 0 * 8 +
               air.c₄ row 0 * 16 + air.c₅ row 0 * 32 + air.c₆ row 0 * 64 + air.c₇ row 0 * 128
  | ⟨n + 28, h⟩ => absurd h (by omega)

set_option maxHeartbeats 8000000 in
theorem air_implies_plonk
    {air : Valid_Add8Air FBB ExtF} {row}
    (r_le : row ≤ air.last_row)
    (h : allHold_simplified air row r_le)
  : add8airCS.accepts (extWireAssignment air row) := by
  simp [Add8Air_constraint_and_interaction_simplification] at h
  obtain ⟨_, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  rw [sub_eq_zero] at h0 h2
  intro gate
  fin_cases gate <;> {
    simp only [add8airCS, extWireAssignment, Gate.scalarMul, Gate.wireEq,
               Gate.add, Gate.bool, Gate.accepts, Gate.eval]
    try ring
    try linear_combination -h0
    try linear_combination h2
    try (linear_combination is_bool.mpr h1)
    try (linear_combination is_bool.mpr h3)
    try (linear_combination is_bool.mpr h4)
    try (linear_combination is_bool.mpr h5)
    try (linear_combination is_bool.mpr h6)
    try (linear_combination is_bool.mpr h7)
    try (linear_combination is_bool.mpr h8)
    try (linear_combination is_bool.mpr h9)
    try (linear_combination is_bool.mpr h10)
  }

end CertiPlonk.Bridge
