instance : Repr ByteArray where
  reprPrec bs p := reprPrec bs.toList p

abbrev ByteArrayParser := ReaderT ByteArray <| StateT Nat <| Except String

deriving instance Repr for Except
def Nat.align8 (pos : Nat) : Nat :=
  let rem := pos % 8
  if rem = 0 then pos else pos + (8 - rem)

namespace ByteArrayParser

def run (p : ByteArrayParser α) (b : ByteArray) (pos := 0) : Except String (α × Nat) :=
  (ReaderT.run p b).run pos

def run' (p : ByteArrayParser α) (b : ByteArray) (pos := 0) : Except String α := do
  return (← p.run b pos).1

def peek : ByteArrayParser UInt8 := do
  let ba ← read
  let pos ← get
  if h : pos < ba.size then
    pure <| ba.get ⟨pos, h⟩
  else
    throw "eof"

def read8 : ByteArrayParser UInt8 :=
  peek <* modify (· + 1)

def expectB (b : UInt8) : ByteArrayParser Unit := do
  let b' ← read8
  unless b = b' do throw s!"got {b'}, expected {b}"

def expectBs (bs : ByteArray) : ByteArrayParser Unit := do
  for b in bs do expectB b

def read16LE : ByteArrayParser UInt16 := do
  let a ← read8
  let b ← read8
  return a.toUInt16 ||| (b.toUInt16 <<< 8)

def read32LE : ByteArrayParser UInt32 := do
  let a ← read8
  let b ← read8
  let c ← read8
  let d ← read8
  return a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) ||| (d.toUInt32 <<< 24)

def read64LE : ByteArrayParser UInt64 := do
  return (← read32LE).toUInt64 ||| ((← read32LE).toUInt64 <<< 32)

def readNLE (n : Nat) : ByteArrayParser UInt64 := do
  match n with
  | 1 => return (← read8).toUInt64
  | 2 => return (← read16LE).toUInt64
  | 4 => return (← read32LE).toUInt64
  | 8 => read64LE
  | _ => throw "unsupported width"

def readBytes (sz : Nat) : ByteArrayParser ByteArray := do
  let pos ← get
  let ba ← read
  if pos + sz <= ba.size then
    (pure <| ba.extract pos (pos + sz)) <* modify (· + sz)
  else
    throw s!"eof before {sz} bytes"

def readArray (n : Nat) (elem : ByteArrayParser α) : ByteArrayParser (Array α) := do
  let mut arr := #[]
  for _i in [0:n] do
    arr := arr.push (← elem)
  return arr

def remaining : ByteArrayParser Nat :=
  return (← read).size - (← get)
