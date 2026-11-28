import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56071

private def witness : PEqualNP.CircuitLowerBounds.Circuit :=
{ gates := [
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 2] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 1] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [5] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 9] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 3] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 7] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [13] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 1] },
  { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }
  ],
  output := 16 }

end PEqualNP.Outside.L_meta_56071

theorem PEqualNP.Outside.L_meta_56071 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270716347 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_56071.witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_56071.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
