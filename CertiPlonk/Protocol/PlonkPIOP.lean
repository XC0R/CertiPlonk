import ArkLib.OracleReduction.Security.Basic
import ArkLib.ProofSystem.ConstraintSystem.Plonk

/-! # Plonk Gate-Check Protocol

The Plonk gate-check is the first component of the Plonk PIOP: the prover sends the
wire assignment, the verifier checks all gate equations in the constraint system.

Modeled as a 1-round `Reduction` using ArkLib's OracleReduction framework. This
protocol forms the foundation for the full Plonk PIOP — composition with the
permutation argument (copy constraints) is handled separately.

## Protocol structure

- **ProtocolSpec**: 1 round, P → V, message type `Fin numWires → 𝓡`
- **Statement**: `Plonk.ConstraintSystem 𝓡 numWires numGates`
- **Witness**: `Fin numWires → 𝓡` (wire assignment)
- **Input relation**: `cs.accepts w` (all gate equations satisfied)
- **Output**: `(cs, w)` pair (for composition with downstream reductions)
-/

noncomputable section

namespace CertiPlonk.Protocol

open OracleComp OracleSpec ProtocolSpec Plonk

section GateCheck

variable (𝓡 : Type) [CommRing 𝓡] (numWires numGates : ℕ)

@[reducible]
def gateCheckPSpec : ProtocolSpec 1 :=
  ⟨!v[.P_to_V], !v[Fin numWires → 𝓡]⟩

instance : ∀ i, VCVCompatible ((gateCheckPSpec 𝓡 numWires).Challenge i)
  | ⟨0, h⟩ => nomatch h

instance : ∀ i, SampleableType ((gateCheckPSpec 𝓡 numWires).Challenge i)
  | ⟨0, h⟩ => nomatch h

instance : ProverOnly (gateCheckPSpec 𝓡 numWires) where
  prover_first' := rfl

variable {𝓡} {numWires} {numGates}

@[inline, specialize]
def gateCheckProver :
    Prover []ₒ
      (ConstraintSystem 𝓡 numWires numGates) (Fin numWires → 𝓡)
      (ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (gateCheckPSpec 𝓡 numWires) where
  PrvState
  | 0 => ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)
  | 1 => ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)
  input := id
  sendMessage | ⟨0, _⟩ => fun ⟨cs, w⟩ => pure (w, ⟨cs, w⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨cs, w⟩ => pure (⟨cs, w⟩, ())

variable [DecidableEq 𝓡]

instance acceptsDecidable (cs : ConstraintSystem 𝓡 numWires numGates) (w : Fin numWires → 𝓡) :
    Decidable (cs.accepts w) :=
  inferInstanceAs (Decidable (∀ i : Fin numGates, (cs i).eval w = 0))

@[inline, specialize]
def gateCheckVerifier :
    Verifier []ₒ
      (ConstraintSystem 𝓡 numWires numGates)
      (ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡))
      (gateCheckPSpec 𝓡 numWires) where
  verify := fun cs transcript => do
    let w : Fin numWires → 𝓡 := transcript 0
    guard (cs.accepts w)
    return ⟨cs, w⟩

@[inline, specialize]
def gateCheckReduction :
    Reduction []ₒ
      (ConstraintSystem 𝓡 numWires numGates) (Fin numWires → 𝓡)
      (ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (gateCheckPSpec 𝓡 numWires) where
  prover := gateCheckProver
  verifier := gateCheckVerifier

@[reducible, simp]
def gateCheckRelIn :
    Set (ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) :=
  { p | p.1.accepts p.2 }

@[reducible, simp]
def gateCheckRelOut :
    Set ((ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) × Unit) :=
  Prod.fst ⁻¹' gateCheckRelIn

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

-- Same blocker as ArkLib's own SendWitness.reduction_completeness: after unfolding
-- Reduction.run_of_prover_first and pushing simulateQ through binds/pure, the remaining
-- goal requires proving `Pr[event | init >>= StateT.run' (pure (some result))] = 1`.
-- The OptionT/StateT/ProbComp stack doesn't reduce without additional lemmas about
-- `probEvent` on deterministic OptionT computations parameterized by `init : ProbComp σ`.
set_option maxHeartbeats 1600000 in
open Classical in
theorem gateCheck_perfectCompleteness :
    (gateCheckReduction (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates)).perfectCompleteness
      init impl gateCheckRelIn gateCheckRelOut := by
  rw [Reduction.perfectCompleteness_eq_prob_one]
  intro cs w hIn
  simp only [gateCheckRelIn, Set.mem_setOf_eq] at hIn
  rw [Reduction.run_of_prover_first]
  simp only [gateCheckReduction, gateCheckProver, gateCheckVerifier, Verifier.run]
  simp only [guard, if_pos hIn]
  erw [simulateQ_bind]
  simp only [simulateQ_pure, pure_bind]
  erw [simulateQ_pure]
  simp only [pure_bind]
  sorry

end GateCheck

end CertiPlonk.Protocol

end
