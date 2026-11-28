import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55189

private def witness : PEqualNP.CircuitLowerBounds.Circuit :=
{ gates := [
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 6] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 4] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 1] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 9] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [9] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 13] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 15] }
  ],
  output := 16 }

end PEqualNP.Outside.L_meta_55189

theorem PEqualNP.Outside.L_meta_55189 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198330 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_55189.witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_55189.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
