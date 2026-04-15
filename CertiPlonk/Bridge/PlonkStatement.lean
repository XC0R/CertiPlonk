import CertiPlonk.Bridge.AIRToPlonk
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

@[reducible] def airConstraintsOnWires (w : Fin 28 → FBB) : Prop :=
  w ⟨0, by omega⟩ + w ⟨1, by omega⟩ - (w ⟨3, by omega⟩ * 256 + w ⟨2, by omega⟩) = 0 ∧
  w ⟨3, by omega⟩ * w ⟨3, by omega⟩ - w ⟨3, by omega⟩ = 0 ∧
  w ⟨2, by omega⟩ - (w ⟨4, by omega⟩ + w ⟨5, by omega⟩ * 2 + w ⟨6, by omega⟩ * 4 +
    w ⟨7, by omega⟩ * 8 + w ⟨8, by omega⟩ * 16 + w ⟨9, by omega⟩ * 32 +
    w ⟨10, by omega⟩ * 64 + w ⟨11, by omega⟩ * 128) = 0 ∧
  w ⟨4, by omega⟩ * w ⟨4, by omega⟩ - w ⟨4, by omega⟩ = 0 ∧
  w ⟨5, by omega⟩ * w ⟨5, by omega⟩ - w ⟨5, by omega⟩ = 0 ∧
  w ⟨6, by omega⟩ * w ⟨6, by omega⟩ - w ⟨6, by omega⟩ = 0 ∧
  w ⟨7, by omega⟩ * w ⟨7, by omega⟩ - w ⟨7, by omega⟩ = 0 ∧
  w ⟨8, by omega⟩ * w ⟨8, by omega⟩ - w ⟨8, by omega⟩ = 0 ∧
  w ⟨9, by omega⟩ * w ⟨9, by omega⟩ - w ⟨9, by omega⟩ = 0 ∧
  w ⟨10, by omega⟩ * w ⟨10, by omega⟩ - w ⟨10, by omega⟩ = 0 ∧
  w ⟨11, by omega⟩ * w ⟨11, by omega⟩ - w ⟨11, by omega⟩ = 0

set_option maxHeartbeats 8000000 in
theorem plonk_implies_air (w : Fin 28 → FBB) (h : add8airCS.accepts w) :
    airConstraintsOnWires w := by
  unfold airConstraintsOnWires
  have g0 := h ⟨0, by omega⟩; have g1 := h ⟨1, by omega⟩; have g2 := h ⟨2, by omega⟩
  have g3 := h ⟨3, by omega⟩
  have g4 := h ⟨4, by omega⟩; have g5 := h ⟨5, by omega⟩; have g6 := h ⟨6, by omega⟩
  have g7 := h ⟨7, by omega⟩; have g8 := h ⟨8, by omega⟩; have g9 := h ⟨9, by omega⟩
  have g10 := h ⟨10, by omega⟩
  have g11 := h ⟨11, by omega⟩; have g12 := h ⟨12, by omega⟩; have g13 := h ⟨13, by omega⟩
  have g14 := h ⟨14, by omega⟩; have g15 := h ⟨15, by omega⟩; have g16 := h ⟨16, by omega⟩
  have g17 := h ⟨17, by omega⟩
  have g18 := h ⟨18, by omega⟩
  have g19 := h ⟨19, by omega⟩; have g20 := h ⟨20, by omega⟩; have g21 := h ⟨21, by omega⟩
  have g22 := h ⟨22, by omega⟩; have g23 := h ⟨23, by omega⟩; have g24 := h ⟨24, by omega⟩
  have g25 := h ⟨25, by omega⟩; have g26 := h ⟨26, by omega⟩
  simp only [add8airCS, Gate.scalarMul, Gate.wireEq, Gate.add, Gate.bool, Gate.accepts, Gate.eval] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination g1 - g2 - g0
  · linear_combination g3
  · linear_combination g18 - g17 - g16 - g15 - g14 - g13 - g12 - g11
      - g10 - g9 - g8 - g7 - g6 - g5 - g4
  · linear_combination g19
  · linear_combination g20
  · linear_combination g21
  · linear_combination g22
  · linear_combination g23
  · linear_combination g24
  · linear_combination g25
  · linear_combination g26

end CertiPlonk.Bridge
