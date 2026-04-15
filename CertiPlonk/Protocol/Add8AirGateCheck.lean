import CertiPlonk.Protocol.PlonkPIOP
import CertiPlonk.Bridge.PlonkStatement

/-! # Add8Air Gate-Check Instantiation

Connects the CertiPlonk bridge theorems to the Plonk gate-check protocol.
-/

noncomputable section

open BabyBear Plonk Add8Air.constraints CertiPlonk.Bridge CertiPlonk.Protocol

variable [Field ExtF]

theorem CertiPlonk.Protocol.add8air_in_gateCheckRelIn
    {air : Valid_Add8Air FBB ExtF} {row}
    (r_le : row ≤ air.last_row)
    (h : allHold_simplified air row r_le) :
    (add8airCS, extWireAssignment air row) ∈
      gateCheckRelIn (𝓡 := FBB) (numWires := 28) (numGates := 27) :=
  air_implies_plonk r_le h

theorem CertiPlonk.Protocol.gateCheck_implies_airConstraints
    (w : Fin 28 → FBB)
    (h : (add8airCS, w) ∈
      gateCheckRelIn (𝓡 := FBB) (numWires := 28) (numGates := 27)) :
    airConstraintsOnWires w :=
  plonk_implies_air w h

end
