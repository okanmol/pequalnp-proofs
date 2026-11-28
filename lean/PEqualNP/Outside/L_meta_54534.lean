import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54534

private def witness : PEqualNP.CircuitLowerBounds.Circuit :=
{ gates := [
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 13] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 12] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 17] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 19] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 20] }
  ],
  output := 21 }

end PEqualNP.Outside.L_meta_54534

theorem PEqualNP.Outside.L_meta_54534 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1867517 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨PEqualNP.Outside.L_meta_54534.witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_54534.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
