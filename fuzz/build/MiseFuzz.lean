import MiseTest.Fuzz

/-!
# In-process build fuzzer: the Lean side

`harness.cc` links this module, the case generator `MiseTest.Fuzz` and the
model into one process with Ninja's build logic. For each fuzzer input it
calls `mise_fuzz_case`, which turns the input into a case and runs the
model on it, and replays the case against Ninja in memory.

Until `MiseTest.Rng` can read a choice sequence, the input only seeds the
generator: its FNV-1a hash is the seed, so the fuzzer's mutations do not
keep a case's structure. The low bit of the first byte turns on
`Opts.absent`.
-/

namespace MiseFuzz
open MiseTest.Fuzz Lean

def fnv (b : ByteArray) : UInt64 :=
  b.foldl (fun h x => (h ^^^ x.toUInt64) * 1099511628211) 14695981039346656037

def optsOf (b : ByteArray) : Opts := { absent := b.size > 0 && b[0]! % 2 == 1 }

/-- Set the edges that finished, and whether the failing edge was tried, of
the stopped steps that `fins` names. Each line of `fins` is `I TRIED OUT...`:
the index of the step in the description, `1` or `0`, and the first output
of every edge that finished. -/
def withFinished (steps : List StepD) (fins : String) : List StepD := Id.run do
  let mut out := steps.toArray
  for line in fins.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | i :: tried :: outs =>
      let i := i.toNat!
      if h : i < out.size then
        out := out.set i { out[i] with finished := some outs, tried := tried == "1" }
    | _ => pure ()
  out.toList

/-- The case for a fuzzer input as `fuzzgen` writes it, with the stopped
steps that `fins` names fixed as `withFinished` says, or `error: ...` when
the model rejects the case. `strict` is `runCase`'s: whether the model
checks itself, which mutation testing turns off. -/
@[export mise_fuzz_case]
def fuzzCase (input : ByteArray) (fins : String) (strict : UInt8) : String :=
  let o := optsOf input
  let (c, steps) := genOne o (fnv input).toNat 0
  match runCase (strict != 0) c (withFinished steps fins) (checkToml := false) with
  | .ok j => (j.setObjVal! "missingOk" (toJson false)).compress
  | .error e => "error: " ++ e

end MiseFuzz
