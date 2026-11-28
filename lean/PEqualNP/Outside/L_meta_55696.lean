import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55696

private def witness : PEqualNP.CircuitLowerBounds.Circuit :=
{ gates := [
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 6] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 3] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 5] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 4] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 9] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 8] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [12] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 14] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }
  ],
  output := 16 }

end PEqualNP.Outside.L_meta_55696

theorem PEqualNP.Outside.L_meta_55696 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6491964 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_55696.witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_55696.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
