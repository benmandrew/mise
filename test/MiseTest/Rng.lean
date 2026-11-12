/-!
A random source for the test generators: a seeded generator, or a fixed
sequence of bytes.

Seeded runs are reproducible from the seed. A byte sequence lets a fuzzer
steer the generators: each `rand n` reads the next one to four bytes as a
big-endian number and takes it modulo `n`, so changing one byte changes one
choice, and a sequence that runs out reads zeros. A generator therefore
turns every byte sequence into a valid case, and the empty sequence gives the
case of all first choices, which is usually the smallest.
-/

namespace MiseTest

/-- A random source. With `bytes`, choices come from `bytes` from position
`pos` on, and `state` is unused. -/
structure Rng where
  state : UInt64
  bytes : Option ByteArray := none
  pos : Nat := 0

/-- A seeded source. -/
def Rng.ofSeed (seed : UInt64) : Rng := { state := seed }

/-- A source that reads its choices from `b`. -/
def Rng.ofBytes (b : ByteArray) : Rng := { state := 0, bytes := some b }

/-- One step of a 64-bit linear congruential generator. -/
def Rng.next (g : Rng) : Nat × Rng :=
  let s := g.state * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat, { g with state := s })

/-- How many bytes a number below `n` needs, from one to four. -/
def byteWidth (n : Nat) : Nat :=
  if n ≤ 0x100 then 1 else if n ≤ 0x10000 then 2 else if n ≤ 0x1000000 then 3 else 4

/-- `k` bytes of `b` from `pos` as a big-endian number, with zeros past the
end. -/
def readBE (b : ByteArray) (pos k : Nat) : Nat :=
  (List.range k).foldl (fun acc i => acc * 256 + (if h : pos + i < b.size then b[pos + i].toNat else 0)) 0

/-- A number below `n`, or `0` when `n` is `0`. A byte source reads nothing
when there is only one choice. -/
def Rng.draw (g : Rng) (n : Nat) : Nat × Rng :=
  match g.bytes with
  | none =>
    let (x, g') := g.next
    (if n = 0 then 0 else x % n, g')
  | some b =>
    if n ≤ 1 then (0, g)
    else
      let k := byteWidth n
      (readBE b g.pos k % n, { g with pos := g.pos + k })

abbrev GenM := StateM Rng

def rand (n : Nat) : GenM Nat := do
  let (x, g) := (← get).draw n
  set g
  pure x

def pick {α} [Inhabited α] (xs : List α) : GenM α := do
  pure (xs[← rand xs.length]!)

def chance (num den : Nat) : GenM Bool := do pure ((← rand den) < num)

/-- Run a generator on a byte sequence. -/
def GenM.runBytes {α} (m : GenM α) (b : ByteArray) : α := (m.run (Rng.ofBytes b)).1

end MiseTest
