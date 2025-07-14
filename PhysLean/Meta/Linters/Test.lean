import PhysLean.Meta.Linters.Sorry


@[pseudo]
theorem decide_test : 1 + 2 = 3 := by
  native_decide


-- Lean.ofReduceBool

#lint
