/-! A seeded random generator for the test generators. -/

namespace MiseTest

/-- A 64-bit linear congruential generator, so runs are reproducible. -/
structure Rng where
  state : UInt64

def Rng.next (g : Rng) : Nat × Rng :=
  let s := g.state * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat, ⟨s⟩)

abbrev GenM := StateM Rng

def rand (n : Nat) : GenM Nat := do
  let (x, g) := (← get).next
  set g
  pure (if n = 0 then 0 else x % n)

def pick {α} [Inhabited α] (xs : List α) : GenM α := do
  pure (xs[← rand xs.length]!)

def chance (num den : Nat) : GenM Bool := do pure ((← rand den) < num)

end MiseTest
