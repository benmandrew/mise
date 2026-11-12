import MiseTest.DiffGen

/-! Tests for the byte source in `MiseTest.Rng`. -/

namespace MiseTest.BytesTest
open MiseTest MiseTest.DiffTest Mise.Syntax

def draws (b : List UInt8) (ns : List Nat) : List Nat × Nat :=
  let (xs, g) := (ns.mapM rand).run (Rng.ofBytes ⟨b.toArray⟩)
  (xs, g.pos)

-- One byte per choice below 256, big-endian bytes above, zeros past the end.
#guard draws [7, 1, 2] [10, 300] == ([7, 258], 3)
#guard draws [200] [10] == ([0], 1)
#guard draws [] [10, 1000] == ([0, 0], 3)
#guard draws [1] [2, 256, 257] == ([1, 0, 0], 4)
-- A single choice reads nothing.
#guard draws [9] [1, 0, 10] == ([0, 0, 9], 1)

-- Seeded draws are those of the generator before the byte source existed.
#guard (((List.replicate 4 1000).mapM rand).run (Rng.ofSeed 1)).1 == [774, 153, 196, 870]

-- Every byte sequence gives a well-formed manifest that round-trips through
-- the parser model, the empty one included.
def inputs : List ByteArray :=
  [.empty, ⟨#[255]⟩, ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩, ⟨(List.range 200).toArray.map (·.toUInt8)⟩,
   ⟨(List.range 400).toArray.map fun i => (i * 37 + 11).toUInt8⟩, ⟨(List.replicate 300 255).toArray⟩]

#guard inputs.all fun b =>
  let m := genManifest.runBytes b
  decide m.WellFormed && parse (print m) == some m

end MiseTest.BytesTest
