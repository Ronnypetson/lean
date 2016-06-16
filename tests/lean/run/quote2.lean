open tactic list

example (a : nat) : a = a :=
by do a : expr ← get_local "a",
      exact `{ eq.refl (%%a : nat) }
