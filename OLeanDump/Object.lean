import Lean
import Qq
import OLeanDump.ByteArrayParser

open Std Lean Meta ByteArrayParser Qq
abbrev RefMap (α) := Lean.HashMap UInt64 α
abbrev RefSet := Lean.HashSet UInt64

inductive ObjPtr
  | scalar (n : Nat)
  | ptr (n : UInt64)
  deriving Inhabited, BEq, Hashable, Repr

inductive Obj
  | ctor (ctor : Nat) (fields : Array ObjPtr) (sfields : ByteArray)
  | array (data : Array ObjPtr)
  | sarray (data : ByteArray)
  | string (data : String)
  | thunk (value : ObjPtr)
  | task (value : ObjPtr)
  | ref (ref : ObjPtr)
  | mpz (value : Int)
  deriving Inhabited

def ObjLookup := Lean.HashMap UInt64 (Obj × Nat)
  deriving EmptyCollection

namespace ObjLookup
variable (self : ObjLookup)

inductive LayoutVal where
  | uint (sz : Nat) (off : Nat)
  | usize (off : Nat)
  | float (off : Nat)
  | enum (e : Name) (sz : Nat) (off : Nat)
  -- | array (l : LayoutVal) (i : Nat)
  | other (e : Expr) (i : Nat)
  | irrelevant
  | unknown (i : Nat)
  deriving Repr

def LayoutVal.repr : LayoutVal → Format
  | .uint n _ => f!"UInt{8 * n}"
  | .usize _ => f!"USize"
  | .float _ => f!"Float"
  | .enum c _ _
  | .other c _ => f!"{c}"
  | .irrelevant => f!"*"
  | .unknown _ => f!"?"

def isIrrelevant (ty : Expr) : MetaM Bool := do
  if ty.isSort then return true
  if (← whnf ty).isProp then return true
  unless ty.isForall do return false
  forallTelescopeReducing ty fun _ ty =>
    return (← whnf ty).isSort

def isEnum (c : Name) : MetaM (Option Nat) := do
  let env ← getEnv
  let some (.inductInfo iv) := env.find? c | return none
  if c == ``Decidable then return some 1
  let n := iv.ctors.length
  if n == 1 then return none
  if iv.ctors.any fun c => (env.find? c).get!.type.isForall then return none
  return some <| if n < 2^8 then 1 else if n < 2^16 then 2 else 4

partial def LayoutVal.get (ty : Expr) (params : Array Expr) : MetaM LayoutVal := do
  if ← isIrrelevant ty then
    return .irrelevant
  let ty ← whnf ty
  match ty with
  | .const ``UInt8 _ => pure <|.uint 1 0
  | .const ``UInt16 _ => pure <| .uint 2 0
  | .const ``UInt32 _ => pure <| .uint 4 0
  | .const ``UInt64 _ => pure <| .uint 8 0
  | .const ``Float _ => pure <| .float 0
  | .const ``USize _ => pure <| .usize 0
  | _ =>
    if let .const c _ := ty.getAppFn then
      if let some n ← isEnum c then return .enum c n 0
    pure <| .other (← mkLambdaFVars params ty) 0

inductive Layout where
  | newtype (active : Option Nat) (nfields : Nat) (ty : Expr)
  | ctor (scalars ptrs : Nat) (fields : Array LayoutVal)
  | special (ctor : Name)
  | string
  deriving Repr

partial def mkLayout (ctor : Name) (extra : Option Nat := none) : MetaM Layout := do
  let ct ← getConstInfoCtor ctor
  if let some ctor' := Compiler.getImplementedBy? (← getEnv) ctor then
    if ctor' == ctor ++ `_override then
      return ← mkLayout (ctor ++ `_impl) ct.numFields
  forallTelescopeReducing ct.type fun args _ => do
    let mut out := #[]
    let mut uoff := 0
    let params := args[:ct.numParams].toArray
    let mut active := none
    let iv ← getConstInfoInduct ct.induct
    if iv.name matches ``Array | ``String | ``Nat then return .special ctor
    let mut two := iv.ctors.length != 1
    let extra := extra.map (ct.numFields - ·)
    for i in [ct.numParams:args.size] do
      let ty ← inferType args[i]!
      let val ← LayoutVal.get ty params
      if !val matches .irrelevant then
        if let some _ := active then
          two := true
        else
          active := some (i - ct.numParams, ← mkLambdaFVars params ty)
      if let .usize .. := val then
        out := out.push (.usize uoff)
        uoff := uoff + 8
      else
        out := out.push val
    return if two || active.isNone then
      let (fields, scalars, ptrs) := Id.run <| StateT.run (s := (uoff, 0)) <|
        out.mapM fun val (off, i) =>
          match val with
          | .uint n _ => (.uint n off, off + n, i)
          | .float _ => (.float off, off + 8, i)
          | .enum c n _ => (.enum c n off, off + n, i)
          | .other c _ => (.other c i, off, i + 1)
          | .unknown _ => (.unknown i, off, i + 1)
          | .usize n => (.usize n, off, i)
          | .irrelevant => (.irrelevant, off, i)
      match extra with
      | none => .ctor scalars ptrs fields
      | some n => .ctor scalars ptrs fields[n:]
    else
      let (i, ty) := active.get!
      match extra with
      | none => .newtype i out.size ty
      | some n => .newtype (if n ≤ i then some (i - n) else none) (out.size - n) ty

inductive Parse where
  | str (s : String)
  | name (f : Name)
  | emptyArr
  | other (f : Format) (diff : Nat := 0)
  deriving Inhabited

def Parse.toFormat : Parse → Format
  | .str n => repr n
  | .name n => repr n
  | emptyArr => "#[]"
  | .other f _ => f

unsafe def evalNameUnsafe (e : Expr) : MetaM Name := evalExpr' Name ``Name e .unsafe
@[implemented_by evalNameUnsafe] opaque evalName (e : Expr) : MetaM Name

variable (attrs : IO.Ref (NameMap (Expr × Expr × Expr)))
mutual
partial def findAttrsE (e : Expr) (whnfed := false) : MetaM Unit := do
  match e.getAppFn with
  | .const ``bind _ =>
    let args := e.getAppArgs
    if args.size == 6 then do
      findAttrsE args[4]!
      lambdaLetTelescope args[5]! fun _ e =>
        findAttrsE e
  | .const c' ls' =>
    try findAttrs c' ls' e.getAppArgs
    catch _ => if !whnfed then findAttrsE (← whnf e) true
  | _ => pure ()

partial def findAttrs (c : Name) (ls : List Level) (args : Array Expr) : MetaM Unit := do
  if c == ``registerPersistentEnvExtension then
    let e ← mkAppM ``PersistentEnvExtensionDescr.name #[args[4]!]
    try
      let n ← evalName (← whnf e)
      if !args[0]!.hasFVar && !args[1]!.hasFVar && !args[2]!.hasFVar then
      attrs.modify fun s => s.insert n (args[0]!, args[1]!, args[2]!)
    catch _ => pure ()
    return
  let ci ← getConstInfo c
  if let .defnInfo info := ci then
    unless (← forallBoundedTelescope ci.type args.size fun _ ty => return ty.isAppOf ``IO) do
      return
    let e := info.value.instantiateLevelParams ci.levelParams ls
    let e ← instantiateLambda e args
    findAttrsE e
  else if let some decl := Compiler.getImplementedBy? (← getEnv) c then
    findAttrs decl ls args

end

variable (keep : UInt64 → Bool) in
partial def mark : ObjPtr → StateM (RefSet × Nat) Unit
  | .scalar _ => pure ()
  | .ptr ptr => do
    unless keep ptr do return
    if (← get).1.contains ptr then return
    let (o, sz) := self.find! ptr
    modify fun s => (s.1.insert ptr, s.2 + sz)
    match o with
    | .ctor _ fs _
    | .array fs => fs.forM mark
    | .thunk p
    | .task p
    | .ref p => mark p
    | .sarray _
    | .string _
    | .mpz _ => pure ()

structure ReprState where
  base : UInt64
  attrs : NameMap (Expr × Expr × Expr)
  layoutCache : NameMap Layout := {}
  theoremVals : RefSet := {}
  ids : RefMap Parse := {}
  size : Nat := 0

abbrev ReprM := StateRefT ReprState MetaM

def getLayoutCache (n : Name) : ReprM Layout := do
  match (← get).layoutCache.find? n with
  | some l => pure l
  | none =>
    let l ← mkLayout n
    modify fun st => { st with layoutCache := st.layoutCache.insert n l }
    pure l

mutual
partial def reprCore (ptr : ObjPtr) (layout : LayoutVal := .unknown 0) : ReprM Format :=
  return (← parse ptr layout).toFormat

partial def parse (ptr : ObjPtr) (layout : LayoutVal := .unknown 0) : ReprM Parse := do
  let iv ← try
    let .other ty _ := layout | pure none
    let ty ← whnf ty
    let .const c _ := ty.getAppFn | pure none
    let iv ← getConstInfoInduct c
    pure (some (iv, ty.getAppArgs))
  catch _ => pure none
  if let some ({ ctors := [n], .. }, params) := iv then
    if let .newtype i nfields ty ← getLayoutCache n then
      let mut out := mkArray nfields (.other f!"*")
      let ty ← instantiateLambda ty params
      if let some i := i then
        out := out.set! i (← parse ptr (.other ty 0))
      return .other f!"{n}{Format.line}{out.map Parse.toFormat}"
  match ptr with
  | .scalar n =>
    if let some (iv, _) := iv then
      if let some n := iv.ctors.get? n then
        let layout ← getLayoutCache n
        if let .ctor _ _ #[] := layout then
          return if n == ``Name.anonymous then
            .name .anonymous
          else
            .other f!"{n}"
    pure <| .other <| repr n
  | .ptr ptr =>
    if let some res := (← get).ids.find? ptr then return res
    let start := (← get).size
    let (o, sz) := self.find! ptr
    let mut parsed := none
    let res ← match o with
      | Obj.ctor idx fields sfields =>
        let res ← try
          let some (iv, params) := iv
            | let .other ty _ := layout | throwError "not inductive: {layout.repr}"
              let ty ← whnf ty
              let .const c _ := ty.getAppFn | throwError "not inductive: {ty}"
              throwError "not inductive: {c}"
          let some n := iv.ctors.get? idx | throwError "not inductive: {iv.name}.{idx}"
          pure (some (n, params, ← getLayoutCache n))
        catch _e =>
          -- println! "{← e.toMessageData.toString}"
          pure none
        match res with
        | some (n, params, .ctor scalars ptrs fields') =>
          let mut out : Array Parse := #[]
          if n == ``TheoremVal.mk then
            if let some (LayoutVal.other _ i) := fields'[1]? then
              if let .ptr p := fields[i]! then
                modify fun s => { s with theoremVals := s.theoremVals.insert p }
          for l in fields' do
            let runP p off k := do
              match ByteArrayParser.run' p sfields off with
              | .ok p => return .other (← k p)
              | .error e => pure <| .other f!"??? {e}"
            let f ← match l with
            | .irrelevant => pure <| Parse.other f!"*"
            | .uint n off => runP (readNLE n) off (pure ∘ format)
            | .usize off => runP read64LE off (pure ∘ format)
            | .float off => runP read64LE off (pure ∘ format)
            | .enum c n off =>
              runP (readNLE n) off fun idx => do
                let iv ← getConstInfoInduct c
                let some n := iv.ctors.get? idx.toNat | pure f!"??? {c}.{idx}"
                pure f!"{n}"
            | .other c i =>
              let e ← instantiateLambda c params
              (do
                if e.isAppOfArity ``Array 1 && e.appArg!.isAppOf ``Lean.EnvExtensionEntry then
                  let .other ty _ := layout | unreachable!
                  if ← isDefEq ty q(Name × Array Lean.EnvExtensionEntry) then
                    if let .name n := out[0]! then
                      if let some (α, _β, _σ) := (← get).attrs.find? n then
                        return ← parse fields[i]! (.other (← mkAppM ``Array #[α]) 0)
                parse fields[i]! (.other e 0))
            | .unknown i => parse fields[i]! (.unknown 0)
            out := out.push f
          let r ← (do
            if n == ``Name.str then
              if let #[.name n, .str s] := out then
                return .name (n.str s)
            pure <| .other f!"{n}{Format.line}{out.map Parse.toFormat}")
          match r with
          | Parse.other msg _ =>
            let mut msg := msg
            if ptrs < fields.size || scalars.align8 < sfields.size then
              msg := f!"{msg} ??? {← fields.mapM reprCore}[{ptrs}:] {sfields.1}[{scalars}:]"
            pure msg
          | _ => parsed := r; pure r.toFormat
        | some (n, params, .newtype i a ty) =>
          pure f!"??? newtype {i} {a} {ty} {n} {params}"
        | _ =>
          pure f!"Obj.ctor {idx}{Format.line}{← fields.mapM reprCore}{Format.line}{sfields}"
      | Obj.array fields =>
        if fields.isEmpty then parsed := some .emptyArr
        let arg :=
          if let .other (.app (.const ``Array _) l) _ := layout then .other l 0
          else .unknown 0
        pure f!"array {fields.size} {← fields.mapM (reprCore · arg)}"
      | Obj.string s =>
        parsed := some (.str s)
        pure <| repr s
      | Obj.thunk v => pure <| f!"Obj.thunk{Format.line}{← reprCore v}"
      | Obj.task v => pure <| f!"Obj.task{Format.line}{← reprCore v}"
      | Obj.ref r => pure <| f!"Obj.ref{Format.line}{← reprCore r}"
      | Obj.sarray bs => pure <| f!"Obj.sarray'{Format.line}{bs}"
      | Obj.mpz v => pure f!"Obj.mpz{Format.line}{v}"
    let res := res.fill.nest 2
    modify fun st => { st with size := st.size + sz }
    let diff := (← get).size - start
    let newDeclId := s!"x{String.mk (Nat.toDigits 16 ((ptr - (← get).base).toNat % 2^32))}\{{diff}}"
    let result := parsed.getD (.other newDeclId diff)
    modify fun st => { st with ids := st.ids.insert ptr result }
    if parsed.isNone then
      IO.println f!"let {newDeclId} : {layout.repr} :={Format.line}{res}".group
    return result

end

def main (base : UInt64) (root : ObjPtr) : MetaM Unit := do
  let attrs ← IO.mkRef {}
  for attr in [builtinInitAttr, regularInitAttr] do
    for entries in attr.ext.toEnvExtension.getState (← getEnv) |>.importedEntries do
      for (n, initFn) in entries do
        findAttrs attrs (if initFn.isAnonymous then n else initFn) [] #[]
  let (_, s) ← StateRefT'.run (s := { base, attrs := ← attrs.get }) do
    let .other p _ ← self.parse root (.other q(ModuleData) 0) | throwError ""
    IO.println p
  let (_, _, sz) := self.mark (!s.theoremVals.contains ·) root |>.run ({}, 0)
  IO.println s!"size without theorems: {sz}"
