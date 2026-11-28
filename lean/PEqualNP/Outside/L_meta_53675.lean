import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53675

private def witness : PEqualNP.CircuitLowerBounds.Circuit :=
{ gates := [
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 9] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 11] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 13] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 12] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 16] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 17] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 18] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 19] }
  ],
  output := 20 }

end PEqualNP.Outside.L_meta_53675

theorem PEqualNP.Outside.L_meta_53675 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4062195 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨PEqualNP.Outside.L_meta_53675.witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_53675.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
