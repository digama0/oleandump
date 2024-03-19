import OLeanDump.Object
import OLeanDump.ByteArrayParser
open IO
open ByteArrayParser

def ObjPtr.parse (ptr : UInt64) : ObjPtr :=
  if ptr &&& 1 = 1 then
    ObjPtr.scalar <| ptr.toNat >>> 1
  else
    ObjPtr.ptr ptr

def parseArrayElems (n : Nat) : ByteArrayParser (Array ObjPtr) := do
  let mut arr := #[]
  for _i in [0:n] do
    arr := arr.push (.parse (← read64LE))
  pure <| arr

def parseObj : ByteArrayParser Obj := do
  let rc ← read32LE
  unless rc = 0 do panic! s!"nonpersistent object: rc={rc}"
  let cs_sz ← read16LE
  let other ← read8
  let tag ← read8
  match tag with
  | 245 => panic! "closure" -- cannot be compacted
  | 246 =>
    let size ← read64LE
    let capacity ← read64LE
    unless size = capacity do
      panic! s!"array has different capacity={capacity} than size={size}"
    let fields ← parseArrayElems size.toNat
    pure <| Obj.array fields
  | 247 => panic! "struct array"
  | 248 =>
    let size ← read64LE
    let capacity ← read64LE
    unless size = capacity do
      panic! s!"scalar array has different capacity={capacity} than size={size}"
    let data ← readBytes capacity.toNat
    pure <| Obj.sarray <| data.extract 0 size.toNat
  | 249 =>
    let size ← read64LE
    let capacity ← read64LE
    let _length ← read64LE
    unless size = capacity do
      panic! s!"string has different capacity={capacity} than size={size}"
    let utf8 ← readBytes size.toNat
    let utf8 := utf8.extract 0 (utf8.size - 1) -- drop zero terminator
    pure <| Obj.string <| String.fromUTF8Unchecked utf8 -- TODO
  | 250 =>
    let capacity ← read32LE
    let signSize ← read32LE
    let (size, sign) := -- TODO: implement Int32
      if (signSize >>> 31) == 0 then
        (signSize, 1)
      else
        (0-signSize, -1)
    unless size = capacity do
      panic! s!"mpz has different capacity={capacity} than size={size}"
    let _limbsPtr ← read64LE
    -- TODO: verify that limbsPtr starts here
    let limbs ← readArray size.toNat read64LE -- mb_limb_t
    let nat : Nat := limbs.foldr (init := 0) -- limbs are little-endian
      fun limb acc => (acc <<< 64) ||| limb.toNat
    pure <| Obj.mpz (sign * nat)
  | 251 =>
    let value ← read64LE
    let closure ← read64LE
    unless closure = 0 do
      panic! s!"thunk has non-zero closure"
    pure <| Obj.thunk <| .parse value
  | 252 =>
    let value ← read64LE
    let imp ← read64LE
    unless imp = 0 do
      panic! s!"task has non-zero implementation"
    pure <| Obj.task <| .parse value
  | 253 =>
    pure <| Obj.ref (.parse (← read64LE))
  | 254 => panic! "external"
  | 255 => panic! "reserved"
  | ctor =>
    let numFields := other.toNat
    let lenExceptSFields := 8 + 8*numFields
    if lenExceptSFields > cs_sz.toNat then
      panic! s!"cs_sz={cs_sz} not correct, should be larger than 8+8*{numFields}"
    let lenSFields := cs_sz.toNat - lenExceptSFields
    let mut fields := #[]
    for _ in [0:numFields] do
      let ptr ← read64LE
      fields := fields.push (.parse ptr)
    let sfields ← readBytes lenSFields
    -- dbg_trace s!"obj {cs_sz} {ctor} {numFields} {lenSFields} {other} {tag}"
    pure <| Obj.ctor ctor.toNat fields sfields

structure OLeanFile where
  githash : String
  base : UInt64
  objs : ObjLookup
  root : ObjPtr

def parseOLean : ByteArrayParser OLeanFile := do
  let pos0 ← get
  expectBs "olean".toUTF8
  expectB 1 -- v1 olean
  let githash := String.mk <| (← readBytes 40).toList.takeWhile (· ≠ 0) |>.map (Char.ofNat ·.toNat)
  expectBs [0, 0].toByteArray -- reserved
  let base ← read64LE
  let mut objs : ObjLookup := {}
  let root ← read64LE
  modify (·.align8)
  while (← remaining) > 0 do
    let pos ← get
    let obj ← parseObj
    modify (·.align8)
    objs := objs.insert (base + (pos - pos0).toUInt64) (obj, (← get) - pos)
  pure { githash, base, objs, root := .ptr root }

open Process

-- #eval show IO Obj from do
--   let cnt ← IO.FS.readBinFile "/home/mario/Documents/lean/lean4/build/release/stage1/lib/lean/Init/Core.olean"
--   let (obj, last) ← ofExcept <| parseOLean.run cnt
--   pure obj
