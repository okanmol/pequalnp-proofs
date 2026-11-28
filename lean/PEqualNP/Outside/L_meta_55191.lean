import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55191

private def witness : PEqualNP.CircuitLowerBounds.Circuit :=
{ gates := [
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 4] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 4] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 0] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 0] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 8] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [12] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 9] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 6] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 14] }
  ],
  output := 16 }

end PEqualNP.Outside.L_meta_55191

theorem PEqualNP.Outside.L_meta_55191 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198450 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_55191.witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_55191.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
