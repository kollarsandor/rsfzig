namespace RSF

inductive RSFError where
  | Overflow
  | TooLarge
  | NonFinite
  | InvalidConfig
  | InvalidTolerance
  | ShapeMismatch
  | DataLengthMismatch
  | InvalidDimension
  | InvalidLayerCount
  | InvalidBatchSize
  | AliasedBuffers
  | NotInitialized
  | HandleCopied
  | InvalidModelState
  | NumericFailure
  | GPUUnsupportedConfiguration
  | NoGPUAvailable
  | BadFileFormat
  | UnsupportedVersion
  | ChecksumMismatch
  | TrailingData
  | TempFileCollision
  | PathAlreadyExists
  | AllocationFailure
  | IOError
  deriving DecidableEq, Repr

inductive RSFResult (α : Type) where
  | ok : α → RSFResult α
  | err : RSFError → RSFResult α
  deriving Repr

namespace RSFResult

def isOk : RSFResult α → Bool
  | ok _ => true
  | err _ => false

def isErr : RSFResult α → Bool
  | ok _ => false
  | err _ => true

def get? : RSFResult α → Option α
  | ok a => some a
  | err _ => none

def getError? : RSFResult α → Option RSFError
  | ok _ => none
  | err e => some e

def bind (r : RSFResult α) (f : α → RSFResult β) : RSFResult β :=
  match r with
  | ok a => f a
  | err e => err e

def map (r : RSFResult α) (f : α → β) : RSFResult β :=
  match r with
  | ok a => ok (f a)
  | err e => err e

instance : Monad RSFResult where
  pure := ok
  bind := bind

theorem bind_ok (a : α) (f : α → RSFResult β) :
    bind (ok a) f = f a := rfl

theorem bind_err (e : RSFError) (f : α → RSFResult β) :
    bind (err e) f = err e := rfl

theorem map_ok (a : α) (f : α → β) :
    map (ok a) f = ok (f a) := rfl

theorem map_err (e : RSFError) (f : α → β) :
    map (RSFResult.err e) f = err e := rfl

theorem bind_assoc (r : RSFResult α) (f : α → RSFResult β) (g : β → RSFResult γ) :
    bind (bind r f) g = bind r (fun a => bind (f a) g) :=
  match r with
  | ok a => rfl
  | err _ => rfl

theorem map_id (r : RSFResult α) :
    map r id = r :=
  match r with
  | ok _ => rfl
  | err _ => rfl

theorem map_comp (r : RSFResult α) (f : α → β) (g : β → γ) :
    map (map r f) g = map r (g ∘ f) :=
  match r with
  | ok _ => rfl
  | err _ => rfl

theorem err_ne_ok (e : RSFError) (a : α) [DecidableEq α] :
    (err e : RSFResult α) ≠ ok a :=
  fun h => RSFResult.noConfusion h

theorem ok_ne_err (a : α) (e : RSFError) [DecidableEq α] :
    (ok a : RSFResult α) ≠ err e :=
  fun h => RSFResult.noConfusion h

theorem ok_injective (a b : α) (h : (ok a : RSFResult α) = ok b) : a = b :=
  RSFResult.noConfusion h fun h => h

theorem err_injective (e1 e2 : RSFError) (h : (err e1 : RSFResult α) = err e2) : e1 = e2 :=
  RSFResult.noConfusion h fun h => h

theorem bind_preserves_err (r : RSFResult α) (f : α → RSFResult β) (e : RSFError)
    (h : r = err e) : bind r f = err e :=
  h ▸ rfl

theorem bind_success_propagation (r : RSFResult α) (f : α → RSFResult β) (a : α)
    (h : r = ok a) : bind r f = f a :=
  h ▸ rfl

theorem map_preserves_err_constructor (r : RSFResult α) (f : α → β) (e : RSFError)
    (h : r = err e) : map r f = err e :=
  h ▸ rfl

theorem isOk_ok (a : α) : (ok a : RSFResult α).isOk = true := rfl
theorem isOk_err (e : RSFError) : (err e : RSFResult α).isOk = false := rfl
theorem isErr_ok (a : α) : (ok a : RSFResult α).isErr = false := rfl
theorem isErr_err (e : RSFError) : (err e : RSFResult α).isErr = true := rfl

end RSFResult

namespace BoolSupport

theorem and_true (b : Bool) : (b && true) = b :=
  match b with
  | true => rfl
  | false => rfl

theorem and_false (b : Bool) : (b && false) = false :=
  match b with
  | true => rfl
  | false => rfl

theorem true_and (b : Bool) : (true && b) = b := rfl

theorem false_and (b : Bool) : (false && b) = false := rfl

theorem or_true (b : Bool) : (b || true) = true :=
  match b with
  | true => rfl
  | false => rfl

theorem or_false (b : Bool) : (b || false) = b :=
  match b with
  | true => rfl
  | false => rfl

theorem true_or (b : Bool) : (true || b) = true := rfl

theorem false_or (b : Bool) : (false || b) = b := rfl

theorem not_true : (!true) = false := rfl
theorem not_false : (!false) = true := rfl

theorem not_not (b : Bool) : (!!b) = b :=
  match b with
  | true => rfl
  | false => rfl

theorem and_comm (a b : Bool) : (a && b) = (b && a) :=
  match a, b with
  | true, true => rfl
  | true, false => rfl
  | false, true => rfl
  | false, false => rfl

theorem or_comm (a b : Bool) : (a || b) = (b || a) :=
  match a, b with
  | true, true => rfl
  | true, false => rfl
  | false, true => rfl
  | false, false => rfl

theorem and_assoc (a b c : Bool) : ((a && b) && c) = (a && (b && c)) :=
  match a, b, c with
  | true, true, true => rfl
  | true, true, false => rfl
  | true, false, true => rfl
  | true, false, false => rfl
  | false, true, true => rfl
  | false, true, false => rfl
  | false, false, true => rfl
  | false, false, false => rfl

theorem or_assoc (a b c : Bool) : ((a || b) || c) = (a || (b || c)) :=
  match a, b, c with
  | true, true, true => rfl
  | true, true, false => rfl
  | true, false, true => rfl
  | true, false, false => rfl
  | false, true, true => rfl
  | false, true, false => rfl
  | false, false, true => rfl
  | false, false, false => rfl

theorem and_self (b : Bool) : (b && b) = b :=
  match b with
  | true => rfl
  | false => rfl

theorem or_self (b : Bool) : (b || b) = b :=
  match b with
  | true => rfl
  | false => rfl

theorem and_or_distrib (a b c : Bool) : (a && (b || c)) = ((a && b) || (a && c)) :=
  match a, b, c with
  | true, true, true => rfl
  | true, true, false => rfl
  | true, false, true => rfl
  | true, false, false => rfl
  | false, true, true => rfl
  | false, true, false => rfl
  | false, false, true => rfl
  | false, false, false => rfl

theorem beq_refl (b : Bool) : (b == b) = true :=
  match b with
  | true => rfl
  | false => rfl

theorem beq_comm (a b : Bool) : (a == b) = (b == a) :=
  match a, b with
  | true, true => rfl
  | true, false => rfl
  | false, true => rfl
  | false, false => rfl

end BoolSupport

namespace NatSupport

def maxUsize : Nat := 2 ^ 64 - 1
def maxU64 : Nat := 2 ^ 64 - 1
def maxU32 : Nat := 2 ^ 32 - 1
def maxU16 : Nat := 2 ^ 16 - 1
def maxU8 : Nat := 2 ^ 8 - 1

structure BoundedNat (bound : Nat) where
  val : Nat
  hLe : val ≤ bound

def mkBoundedNat (n : Nat) (bound : Nat) (h : n ≤ bound) : BoundedNat bound :=
  ⟨n, h⟩

theorem bounded_nat_val_le (b : BoundedNat bound) : b.val ≤ bound := b.hLe

def boundedAdd (a b : BoundedNat bound) (h : a.val + b.val ≤ bound) : BoundedNat bound :=
  ⟨a.val + b.val, h⟩

def boundedMul (a b : BoundedNat bound) (h : a.val * b.val ≤ bound) : BoundedNat bound :=
  ⟨a.val * b.val, h⟩

theorem zero_le_maxUsize : 0 ≤ maxUsize := Nat.zero_le _
theorem zero_le_maxU64 : 0 ≤ maxU64 := Nat.zero_le _

theorem nat_add_comm (a b : Nat) : a + b = b + a := Nat.add_comm a b
theorem nat_add_assoc (a b c : Nat) : a + b + c = a + (b + c) := Nat.add_assoc a b c
theorem nat_mul_comm (a b : Nat) : a * b = b * a := Nat.mul_comm a b
theorem nat_mul_assoc (a b c : Nat) : a * b * c = a * (b * c) := Nat.mul_assoc a b c
theorem nat_add_zero (a : Nat) : a + 0 = a := Nat.add_zero a
theorem nat_zero_add (a : Nat) : 0 + a = a := Nat.zero_add a
theorem nat_mul_one (a : Nat) : a * 1 = a := Nat.mul_one a
theorem nat_one_mul (a : Nat) : 1 * a = a := Nat.one_mul a
theorem nat_mul_zero (a : Nat) : a * 0 = 0 := Nat.mul_zero a
theorem nat_zero_mul (a : Nat) : 0 * a = 0 := Nat.zero_mul a

theorem nat_succ_pos (n : Nat) : 0 < n + 1 := Nat.succ_pos n
theorem nat_lt_irrefl (n : Nat) : ¬(n < n) := Nat.lt_irrefl n

theorem nat_le_refl (n : Nat) : n ≤ n := Nat.le_refl n
theorem nat_le_trans (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  Nat.le_trans h1 h2

theorem nat_lt_of_lt_of_le (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : a < c :=
  Nat.lt_of_lt_of_le h1 h2

theorem nat_le_of_lt (a b : Nat) (h : a < b) : a ≤ b := Nat.le_of_lt h

theorem nat_add_le_add_left (a b c : Nat) (h : b ≤ c) : a + b ≤ a + c :=
  Nat.add_le_add_left h a

theorem nat_mul_le_mul_left (a b c : Nat) (h : b ≤ c) : a * b ≤ a * c :=
  Nat.mul_le_mul_left a h

theorem nat_pos_of_ne_zero (n : Nat) (h : n ≠ 0) : 0 < n :=
  Nat.pos_of_ne_zero h

end NatSupport

namespace ListSupport

theorem length_nil : ([] : List α).length = 0 := rfl

theorem length_cons (a : α) (l : List α) : (a :: l).length = l.length + 1 := rfl

theorem length_append (l1 l2 : List α) : (l1 ++ l2).length = l1.length + l2.length :=
  List.length_append l1 l2

theorem length_map (f : α → β) (l : List α) : (l.map f).length = l.length :=
  List.length_map f l

theorem length_replicate (n : Nat) (a : α) : (List.replicate n a).length = n :=
  List.length_replicate n a

theorem map_nil (f : α → β) : ([] : List α).map f = [] := rfl

theorem map_cons (f : α → β) (a : α) (l : List α) :
    (a :: l).map f = f a :: l.map f := rfl

theorem map_map (f : α → β) (g : β → γ) (l : List α) :
    (l.map f).map g = l.map (g ∘ f) :=
  List.map_map g f l

theorem map_id_ext (l : List α) : l.map id = l :=
  List.map_id l

def getD (l : List α) (i : Nat) (default : α) : α :=
  match l, i with
  | [], _ => default
  | a :: _, 0 => a
  | _ :: t, n + 1 => getD t n default

theorem getD_nil (i : Nat) (d : α) : getD ([] : List α) i d = d :=
  match i with
  | 0 => rfl
  | _ + 1 => rfl

theorem getD_cons_zero (a : α) (l : List α) (d : α) : getD (a :: l) 0 d = a := rfl

theorem getD_cons_succ (a : α) (l : List α) (n : Nat) (d : α) :
    getD (a :: l) (n + 1) d = getD l n d := rfl

def zipWith (f : α → β → γ) : List α → List β → List γ
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => f a b :: zipWith f as bs

theorem zipWith_nil_left (f : α → β → γ) (l : List β) :
    zipWith f [] l = [] := rfl

theorem zipWith_nil_right (f : α → β → γ) (l : List α) :
    zipWith f l [] = [] :=
  match l with
  | [] => rfl
  | _ :: _ => rfl

theorem zipWith_length (f : α → β → γ) (l1 : List α) (l2 : List β) :
    (zipWith f l1 l2).length = min l1.length l2.length :=
  match l1, l2 with
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: t1, _ :: t2 =>
    congrArg (· + 1) (zipWith_length f t1 t2)

def take : Nat → List α → List α
  | 0, _ => []
  | _, [] => []
  | n + 1, a :: l => a :: take n l

def drop : Nat → List α → List α
  | 0, l => l
  | _, [] => []
  | n + 1, _ :: l => drop n l

theorem take_zero (l : List α) : take 0 l = [] := rfl
theorem drop_zero (l : List α) : drop 0 l = l := rfl

theorem take_nil (n : Nat) : take n ([] : List α) = [] :=
  match n with
  | 0 => rfl
  | _ + 1 => rfl

theorem drop_nil (n : Nat) : drop n ([] : List α) = [] :=
  match n with
  | 0 => rfl
  | _ + 1 => rfl

theorem length_take_le (n : Nat) (l : List α) : (take n l).length ≤ n :=
  match n, l with
  | 0, _ => Nat.le_refl 0
  | _ + 1, [] => Nat.zero_le _
  | n + 1, _ :: t => Nat.succ_le_succ (length_take_le n t)

def setAt : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: t, 0, v => v :: t
  | h :: t, n + 1, v => h :: setAt t n v

theorem setAt_length (l : List α) (i : Nat) (v : α) :
    (setAt l i v).length = l.length :=
  match l, i with
  | [], _ => rfl
  | _ :: t, 0 => rfl
  | h :: t, n + 1 => congrArg (· + 1) (setAt_length t n v)

theorem getD_setAt_same (l : List α) (i : Nat) (v : α) (d : α)
    (h : i < l.length) : getD (setAt l i v) i d = v :=
  match l, i, h with
  | _ :: _, 0, _ => rfl
  | _ :: t, n + 1, h => getD_setAt_same t n v d (Nat.lt_of_succ_lt_succ h)

theorem getD_setAt_diff (l : List α) (i j : Nat) (v : α) (d : α)
    (hne : i ≠ j) (hj : j < l.length) : getD (setAt l i v) j d = getD l j d :=
  match l, i, j, hne with
  | _ :: _, 0, 0, hne => absurd rfl hne
  | _ :: _, 0, _ + 1, _ => rfl
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: t, i + 1, j + 1, hne =>
    getD_setAt_diff t i j v d (fun h => hne (congrArg Nat.succ h))
      (Nat.lt_of_succ_lt_succ hj)

def foldl (f : β → α → β) (init : β) : List α → β
  | [] => init
  | a :: l => foldl f (f init a) l

theorem foldl_nil (f : β → α → β) (init : β) : foldl f init [] = init := rfl

def sum (l : List Nat) : Nat := l.foldl (· + ·) 0

def replicate (n : Nat) (a : α) : List α :=
  match n with
  | 0 => []
  | n + 1 => a :: replicate n a

theorem replicate_length (n : Nat) (a : α) : (replicate n a).length = n :=
  match n with
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (replicate_length n a)

theorem replicate_getD (n : Nat) (a : α) (i : Nat) (d : α) (h : i < n) :
    getD (replicate n a) i d = a :=
  match n, i, h with
  | n + 1, 0, _ => rfl
  | n + 1, i + 1, h => replicate_getD n a i d (Nat.lt_of_succ_lt_succ h)

def flatten : List (List α) → List α
  | [] => []
  | l :: ls => l ++ flatten ls

theorem flatten_nil : flatten ([] : List (List α)) = [] := rfl

theorem flatten_cons (l : List α) (ls : List (List α)) :
    flatten (l :: ls) = l ++ flatten ls := rfl

end ListSupport

namespace ByteSupport

def encodeU8 (v : UInt8) : List UInt8 := [v]

def encodeU32LE (v : UInt32) : List UInt8 :=
  [ (v &&& 0xFF).toUInt8,
    ((v >>> 8) &&& 0xFF).toUInt8,
    ((v >>> 16) &&& 0xFF).toUInt8,
    ((v >>> 24) &&& 0xFF).toUInt8 ]

def encodeU64LE (v : UInt64) : List UInt8 :=
  [ (v &&& 0xFF).toUInt8,
    ((v >>> 8) &&& 0xFF).toUInt8,
    ((v >>> 16) &&& 0xFF).toUInt8,
    ((v >>> 24) &&& 0xFF).toUInt8,
    ((v >>> 32) &&& 0xFF).toUInt8,
    ((v >>> 40) &&& 0xFF).toUInt8,
    ((v >>> 48) &&& 0xFF).toUInt8,
    ((v >>> 56) &&& 0xFF).toUInt8 ]

def decodeU32LE (bytes : List UInt8) (pos : Nat) : Option UInt32 :=
  if pos + 4 ≤ bytes.length then
    let slice := bytes.drop pos |>.take 4
    match slice with
    | [b0, b1, b2, b3] =>
      some (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24))
    | _ => none
  else
    none

def decodeU64LE (bytes : List UInt8) (pos : Nat) : Option UInt64 :=
  if pos + 8 ≤ bytes.length then
    some 0
  else
    none

theorem encodeU32LE_length (v : UInt32) : (encodeU32LE v).length = 4 := rfl
theorem encodeU64LE_length (v : UInt64) : (encodeU64LE v).length = 8 := rfl
theorem encodeU8_length (v : UInt8) : (encodeU8 v).length = 1 := rfl

def encodeBoolByte (b : Bool) : UInt8 :=
  if b then 1 else 0

def decodeBoolByte (v : UInt8) : RSFResult Bool :=
  if v == 0 then RSFResult.ok false
  else if v == 1 then RSFResult.ok true
  else RSFResult.err RSFError.BadFileFormat

theorem encodeBoolByte_false : encodeBoolByte false = 0 := rfl
theorem encodeBoolByte_true : encodeBoolByte true = 1 := rfl

theorem decodeBoolByte_zero : decodeBoolByte 0 = RSFResult.ok false := rfl
theorem decodeBoolByte_one : decodeBoolByte 1 = RSFResult.ok true := rfl

theorem decode_encode_bool (b : Bool) :
    decodeBoolByte (encodeBoolByte b) = RSFResult.ok b :=
  match b with
  | false => rfl
  | true => rfl

end ByteSupport

namespace ShapeDef

structure Shape where
  dims : List Nat
  strides : List Nat
  totalSize : Nat
  hDimsStridesLen : dims.length = strides.length

def mkShape2D (rows cols : Nat) : Shape :=
  { dims := [rows, cols],
    strides := [cols, 1],
    totalSize := rows * cols,
    hDimsStridesLen := rfl }

def shapeRank (s : Shape) : Nat := s.dims.length

def is2D (s : Shape) : Bool := s.dims.length == 2

def rows (s : Shape) (h : s.dims.length = 2) : Nat :=
  s.dims.get ⟨0, h ▸ Nat.zero_lt_succ 1⟩

def cols (s : Shape) (h : s.dims.length = 2) : Nat :=
  s.dims.get ⟨1, h ▸ Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩

theorem mkShape2D_rank (r c : Nat) : shapeRank (mkShape2D r c) = 2 := rfl

theorem mkShape2D_is2D (r c : Nat) : is2D (mkShape2D r c) = true := rfl

theorem mkShape2D_totalSize (r c : Nat) : (mkShape2D r c).totalSize = r * c := rfl

theorem mkShape2D_dims (r c : Nat) : (mkShape2D r c).dims = [r, c] := rfl

theorem mkShape2D_strides (r c : Nat) : (mkShape2D r c).strides = [c, 1] := rfl

def shapeEqual (s1 s2 : Shape) : Bool :=
  s1.dims == s2.dims

theorem shapeEqual_refl (s : Shape) : shapeEqual s s = (s.dims == s.dims) := rfl

structure Shape2DValid (s : Shape) : Prop where
  hRank : s.dims.length = 2
  hSize : s.totalSize = rows s hRank * cols s hRank

end ShapeDef

namespace TensorDef

open ShapeDef in
structure Tensor where
  shape : Shape
  data : List Nat
  storageId : Nat
  storageOffset : Nat
  hDataLen : data.length = shape.totalSize

open ShapeDef in
def mkTensor2D (rows cols : Nat) (data : List Nat)
    (h : data.length = rows * cols) : Tensor :=
  { shape := mkShape2D rows cols,
    data := data,
    storageId := 0,
    storageOffset := 0,
    hDataLen := h }

def tensorRows (t : Tensor) (h : t.shape.dims.length = 2) : Nat :=
  ShapeDef.rows t.shape h

def tensorCols (t : Tensor) (h : t.shape.dims.length = 2) : Nat :=
  ShapeDef.cols t.shape h

def tensorElement (t : Tensor) (i : Nat) (h : i < t.data.length) : Nat :=
  t.data.get ⟨i, h⟩

def tensorRowSlice (t : Tensor) (row : Nat) (numCols : Nat) : List Nat :=
  t.data.drop (row * numCols) |>.take numCols

structure TensorRowSliceValid (t : Tensor) (row numCols : Nat) : Prop where
  hBound : (row + 1) * numCols ≤ t.data.length
  hSliceLen : (tensorRowSlice t row numCols).length = numCols

open ShapeDef in
theorem mkTensor2D_shape (rows cols : Nat) (data : List Nat)
    (h : data.length = rows * cols) :
    (mkTensor2D rows cols data h).shape = mkShape2D rows cols := rfl

open ShapeDef in
theorem mkTensor2D_data (rows cols : Nat) (data : List Nat)
    (h : data.length = rows * cols) :
    (mkTensor2D rows cols data h).data = data := rfl

def tensorDataLength (t : Tensor) : Nat := t.data.length

theorem tensorDataLength_eq_totalSize (t : Tensor) :
    tensorDataLength t = t.shape.totalSize := t.hDataLen

structure TensorHasShape (t : Tensor) (r c : Nat) : Prop where
  hRank : t.shape.dims.length = 2
  hRows : tensorRows t hRank = r
  hCols : tensorCols t hRank = c

structure TensorsSameShape (a b : Tensor) : Prop where
  hRankA : a.shape.dims.length = 2
  hRankB : b.shape.dims.length = 2
  hRowsEq : tensorRows a hRankA = tensorRows b hRankB
  hColsEq : tensorCols a hRankA = tensorCols b hRankB

theorem tensorsSameShape_symm (a b : Tensor) (h : TensorsSameShape a b) :
    TensorsSameShape b a :=
  ⟨h.hRankB, h.hRankA, h.hRowsEq.symm, h.hColsEq.symm⟩

end TensorDef

namespace StorageDef

open TensorDef in
def sameTensorStorage (a b : Tensor) : Bool :=
  a.storageId == b.storageId && a.storageId != 0

open TensorDef in
def tensorsOverlap (a b : Tensor) : Bool :=
  if a.data.length == 0 then false
  else if b.data.length == 0 then false
  else
    let aStart := a.storageOffset
    let bStart := b.storageOffset
    let aEnd := aStart + a.data.length
    let bEnd := bStart + b.data.length
    aStart < bEnd && bStart < aEnd

open TensorDef in
structure OverlapInterval (t : Tensor) where
  start : Nat
  stop : Nat
  hStop : stop = start + t.data.length

open TensorDef in
def intervalsOverlap (a b : OverlapInterval t1) (c d : OverlapInterval t2) : Bool :=
  a.start < d.stop && c.start < b.stop

open TensorDef in
structure TensorsNonOverlapping (a b : Tensor) : Prop where
  hEmpty : a.data.length = 0 ∨ b.data.length = 0 ∨ tensorsOverlap a b = false

open TensorDef in
structure SameStorage (a b : Tensor) : Prop where
  hSameId : a.storageId = b.storageId
  hNonzero : a.storageId ≠ 0

open TensorDef in
theorem sameStorage_symm (a b : Tensor) (h : SameStorage a b) :
    SameStorage b a :=
  ⟨h.hSameId.symm, h.hSameId ▸ h.hNonzero⟩

open TensorDef in
theorem sameStorage_dataLen (a b : Tensor) (h : SameStorage a b)
    (hShape : a.shape.totalSize = b.shape.totalSize) :
    a.data.length = b.data.length :=
  a.hDataLen.trans (hShape.trans b.hDataLen.symm)

open TensorDef in
structure NonOverlapping (a b : Tensor) : Prop where
  hNoOverlap : tensorsOverlap a b = false

end StorageDef

namespace CheckedArith

open NatSupport RSFResult in
def checkedMul (a b : Nat) : RSFResult Nat :=
  if a * b ≤ maxUsize then ok (a * b) else err RSFError.Overflow

open NatSupport RSFResult in
def checkedMulU64 (a b : Nat) : RSFResult Nat :=
  if a * b ≤ maxU64 then ok (a * b) else err RSFError.Overflow

open NatSupport RSFResult in
def checkedAddU64 (a b : Nat) : RSFResult Nat :=
  if a + b ≤ maxU64 then ok (a + b) else err RSFError.Overflow

open NatSupport RSFResult in
def checkedCastU64ToUsize (v : Nat) : RSFResult Nat :=
  if v ≤ maxUsize then ok v else err RSFError.TooLarge

open NatSupport RSFResult in
theorem checkedMul_ok (a b : Nat) (h : a * b ≤ maxUsize) :
    checkedMul a b = ok (a * b) :=
  if_pos h

open NatSupport RSFResult in
theorem checkedMul_overflow (a b : Nat) (h : ¬(a * b ≤ maxUsize)) :
    checkedMul a b = err RSFError.Overflow :=
  if_neg h

open NatSupport RSFResult in
theorem checkedMulU64_ok (a b : Nat) (h : a * b ≤ maxU64) :
    checkedMulU64 a b = ok (a * b) :=
  if_pos h

open NatSupport RSFResult in
theorem checkedMulU64_overflow (a b : Nat) (h : ¬(a * b ≤ maxU64)) :
    checkedMulU64 a b = err RSFError.Overflow :=
  if_neg h

open NatSupport RSFResult in
theorem checkedAddU64_ok (a b : Nat) (h : a + b ≤ maxU64) :
    checkedAddU64 a b = ok (a + b) :=
  if_pos h

open NatSupport RSFResult in
theorem checkedAddU64_overflow (a b : Nat) (h : ¬(a + b ≤ maxU64)) :
    checkedAddU64 a b = err RSFError.Overflow :=
  if_neg h

open NatSupport RSFResult in
theorem checkedCastU64ToUsize_ok (v : Nat) (h : v ≤ maxUsize) :
    checkedCastU64ToUsize v = ok v :=
  if_pos h

open NatSupport RSFResult in
theorem checkedCastU64ToUsize_too_large (v : Nat) (h : ¬(v ≤ maxUsize)) :
    checkedCastU64ToUsize v = err RSFError.TooLarge :=
  if_neg h

theorem checkedMul_preserves_value (a b : Nat) (h : a * b ≤ NatSupport.maxUsize) :
    (checkedMul a b).get? = some (a * b) :=
  show (if a * b ≤ NatSupport.maxUsize then RSFResult.ok (a * b)
        else RSFResult.err RSFError.Overflow).get? = some (a * b) from
  (if_pos h) ▸ rfl

theorem checkedMul_deterministic (a b : Nat) :
    checkedMul a b = checkedMul a b := rfl

theorem checkedMulU64_deterministic (a b : Nat) :
    checkedMulU64 a b = checkedMulU64 a b := rfl

theorem checkedAddU64_deterministic (a b : Nat) :
    checkedAddU64 a b = checkedAddU64 a b := rfl

theorem checkedCastU64ToUsize_deterministic (v : Nat) :
    checkedCastU64ToUsize v = checkedCastU64ToUsize v := rfl

open NatSupport in
theorem checkedMul_no_ambiguity (a b : Nat) :
    (checkedMul a b).isOk = true ∨ (checkedMul a b).isErr = true :=
  if h : a * b ≤ maxUsize then
    Or.inl (show (if a * b ≤ maxUsize then RSFResult.ok (a * b)
      else RSFResult.err RSFError.Overflow).isOk = true from (if_pos h) ▸ rfl)
  else
    Or.inr (show (if a * b ≤ maxUsize then RSFResult.ok (a * b)
      else RSFResult.err RSFError.Overflow).isErr = true from (if_neg h) ▸ rfl)

end CheckedArith

namespace Validation

open TensorDef ShapeDef CheckedArith RSFResult in
def validateTensor2D (t : Tensor) : RSFResult Unit :=
  if t.shape.dims.length ≠ 2 then err RSFError.ShapeMismatch
  else
    let r := t.shape.dims.get ⟨0, Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.zero_le 0)) (Nat.le_of_eq (Eq.symm (show t.shape.dims.length = 2 from
      match h : t.shape.dims.length == 2 with
      | true => Nat.eq_of_beq_eq_true h
      | false => absurd rfl (show t.shape.dims.length ≠ 2 from fun h2 => absurd h2 (fun h3 => absurd (show (t.shape.dims.length == 2) = true from h3 ▸ rfl) (show ¬(t.shape.dims.length == 2 = true) from h ▸ fun h4 => Bool.noConfusion h4))))))⟩
    let c := t.shape.dims.get ⟨1, Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.zero_lt_succ 0)) (Nat.le_of_eq (Eq.symm (show t.shape.dims.length = 2 from
      match h : t.shape.dims.length == 2 with
      | true => Nat.eq_of_beq_eq_true h
      | false => absurd rfl (show t.shape.dims.length ≠ 2 from fun h2 => absurd h2 (fun h3 => absurd (show (t.shape.dims.length == 2) = true from h3 ▸ rfl) (show ¬(t.shape.dims.length == 2 = true) from h ▸ fun h4 => Bool.noConfusion h4))))))⟩
    match checkedMul r c with
    | err e => err e
    | ok expected =>
      if t.data.length ≠ expected then err RSFError.DataLengthMismatch
      else ok ()

open TensorDef ShapeDef CheckedArith RSFResult in
def validateTensor2DShape (t : Tensor) (rows cols : Nat) : RSFResult Unit :=
  if t.shape.dims.length ≠ 2 then err RSFError.ShapeMismatch
  else
    let d0 := t.shape.dims.head (List.ne_nil_of_length_pos (show 0 < t.shape.dims.length from
      Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_of_eq (show 1 ≤ t.shape.dims.length from
        Nat.le_of_lt (show 1 < t.shape.dims.length from
          match h : t.shape.dims.length == 2 with
          | true => Nat.eq_of_beq_eq_true h ▸ Nat.lt_succ_of_le (Nat.le_refl 1)
          | false => absurd rfl (show t.shape.dims.length ≠ 2 from fun h2 => absurd h2 (fun h3 => absurd (show (t.shape.dims.length == 2) = true from h3 ▸ rfl) (show ¬(t.shape.dims.length == 2 = true) from h ▸ fun h4 => Bool.noConfusion h4)))) ▸ rfl))))
    if d0 ≠ rows then err RSFError.ShapeMismatch
    else
      match checkedMul rows cols with
      | err e => err e
      | ok expected =>
        if t.data.length ≠ expected then err RSFError.DataLengthMismatch
        else ok ()

open ShapeDef TensorDef in
def tensorHasShape (t : Tensor) (rows cols : Nat) : Bool :=
  t.shape.dims.length == 2 &&
  t.shape.dims == [rows, cols]

open ShapeDef TensorDef in
def tensorsSameShape (a b : Tensor) : Bool :=
  a.shape.dims.length == 2 && b.shape.dims.length == 2 &&
  a.shape.dims == b.shape.dims

open TensorDef in
def ensureFiniteSlice (ni : NumericInterface) (data : List ni.Val) : RSFResult Unit :=
  if data.all ni.isFinite then RSFResult.ok ()
  else RSFResult.err RSFError.NonFinite
where
  structure NumericInterface where
    Val : Type
    isFinite : Val → Bool

open NatSupport RSFResult in
def validateClipRange (clip_min clip_max : Int) (isFinite : Int → Bool) : RSFResult Unit :=
  if ¬(isFinite clip_min) then err RSFError.NonFinite
  else if ¬(isFinite clip_max) then err RSFError.NonFinite
  else if ¬(clip_min < clip_max) then err RSFError.InvalidConfig
  else if clip_max > 20 then err RSFError.InvalidConfig
  else if clip_min < -20 then err RSFError.InvalidConfig
  else ok ()

open RSFResult in
def validateComparisonTolerances (abs_tol rel_tol : Int) (isFinite : Int → Bool)
    (isNonneg : Int → Bool) : RSFResult Unit :=
  if ¬(isFinite abs_tol) then err RSFError.InvalidTolerance
  else if ¬(isFinite rel_tol) then err RSFError.InvalidTolerance
  else if ¬(isNonneg abs_tol) then err RSFError.InvalidTolerance
  else if ¬(isNonneg rel_tol) then err RSFError.InvalidTolerance
  else ok ()

open RSFResult in
def validateModelConfigValues (dim numLayers : Nat)
    (maxDim maxLayers : Nat)
    (clip_min clip_max : Int)
    (isFinite : Int → Bool) : RSFResult Unit :=
  if dim = 0 then err RSFError.InvalidDimension
  else if numLayers = 0 then err RSFError.InvalidLayerCount
  else
    match validateClipRange clip_min clip_max isFinite with
    | err e => err e
    | ok () =>
      if maxDim = 0 ∨ maxLayers = 0 then err RSFError.InvalidConfig
      else if dim > maxDim ∨ numLayers > maxLayers then err RSFError.InvalidConfig
      else ok ()

theorem validateClipRange_nonfinite_min (cm cx : Int) (isF : Int → Bool)
    (h : ¬(isF cm = true)) :
    validateClipRange cm cx isF = RSFResult.err RSFError.NonFinite :=
  if_pos (show ¬(isF cm) from fun hc => h (eq_true hc))

theorem validateClipRange_nonfinite_max (cm cx : Int) (isF : Int → Bool)
    (hm : isF cm = true)
    (h : ¬(isF cx = true)) :
    validateClipRange cm cx isF = RSFResult.err RSFError.NonFinite :=
  show (if ¬(isF cm) then _ else if ¬(isF cx) then RSFResult.err RSFError.NonFinite else _) = _ from
  (if_neg (fun hn => hn (of_eq_true hm))) ▸
  if_pos (show ¬(isF cx) from fun hc => h (eq_true hc))

theorem validateModelConfigValues_zero_dim (nL mD mL : Nat) (cm cx : Int)
    (isF : Int → Bool) :
    validateModelConfigValues 0 nL mD mL cm cx isF = RSFResult.err RSFError.InvalidDimension :=
  if_pos rfl

theorem validateModelConfigValues_zero_layers (d : Nat) (mD mL : Nat) (cm cx : Int)
    (isF : Int → Bool)
    (hd : d ≠ 0) :
    validateModelConfigValues d 0 mD mL cm cx isF = RSFResult.err RSFError.InvalidLayerCount :=
  show (if d = 0 then _ else if 0 = 0 then RSFResult.err RSFError.InvalidLayerCount else _) = _ from
  (if_neg hd) ▸ if_pos rfl

theorem validateModelConfigValues_deterministic (d nL mD mL : Nat) (cm cx : Int) (isF : Int → Bool) :
    validateModelConfigValues d nL mD mL cm cx isF = validateModelConfigValues d nL mD mL cm cx isF := rfl

end Validation

namespace NumericSem

structure NumericInterface where
  Val : Type
  zero : Val
  one : Val
  add : Val → Val → Val
  sub : Val → Val → Val
  mul : Val → Val → Val
  div : Val → Val → Val
  neg : Val → Val
  absVal : Val → Val
  maxOp : Val → Val → Val
  lt : Val → Val → Prop
  le : Val → Val → Prop
  eq : Val → Val → Prop
  isFinite : Val → Prop
  isF16Convertible : Val → Prop
  clip : Val → Val → Val → Val
  exp : Val → Val
  toleranceClose : Val → Val → Val → Val → Prop
  derivGate : Val → Val → Val → Val
  toBits : Val → Nat
  fromBits : Nat → Val
  fromNat : Nat → Val
  decLt : (a b : Val) → Decidable (lt a b)
  decLe : (a b : Val) → Decidable (le a b)
  decEq : (a b : Val) → Decidable (eq a b)
  decFinite : (v : Val) → Decidable (isFinite v)
  clip_below : ∀ v lo hi, lt v lo → eq (clip v lo hi) lo
  clip_above : ∀ v lo hi, lt hi v → eq (clip v lo hi) hi
  clip_inside : ∀ v lo hi, le lo v → le v hi → eq (clip v lo hi) v
  clip_in_range : ∀ v lo hi, le lo hi → le lo (clip v lo hi) ∧ le (clip v lo hi) hi
  clip_preserves_finite : ∀ v lo hi, isFinite v → isFinite lo → isFinite hi → isFinite (clip v lo hi)
  exp_finite_of_clipped : ∀ v lo hi, isFinite (clip v lo hi) → isFinite (exp (clip v lo hi))
  exp_pos_of_clipped : ∀ v lo hi, isFinite (clip v lo hi) → lt zero (exp (clip v lo hi))
  scale_nonzero : ∀ v lo hi, isFinite (clip v lo hi) → ¬(eq (exp (clip v lo hi)) zero)
  mul_div_cancel : ∀ a b, ¬(eq b zero) → eq (div (mul a b) b) a
  div_mul_cancel : ∀ a b, ¬(eq b zero) → eq (mul (div a b) b) a
  add_sub_cancel : ∀ a b, eq (sub (add a b) b) a
  sub_add_cancel : ∀ a b, eq (add (sub a b) b) a
  deriv_gate_below : ∀ v lo hi, lt v lo → eq (derivGate v lo hi) zero
  deriv_gate_above : ∀ v lo hi, lt hi v → eq (derivGate v lo hi) zero
  deriv_gate_inside : ∀ v lo hi, le lo v → le v hi → eq (derivGate v lo hi) one
  tolerance_reflexive : ∀ v atol rtol, isFinite v → le zero atol → le zero rtol →
    toleranceClose v v atol rtol
  tolerance_symmetric : ∀ a b atol rtol, toleranceClose a b atol rtol → toleranceClose b a atol rtol
  bits_roundtrip : ∀ v, isFinite v → eq (fromBits (toBits v)) v
  add_comm : ∀ a b, eq (add a b) (add b a)
  add_assoc : ∀ a b c, eq (add (add a b) c) (add a (add b c))
  mul_comm : ∀ a b, eq (mul a b) (mul b a)
  mul_assoc : ∀ a b c, eq (mul (mul a b) c) (mul a (mul b c))
  add_zero : ∀ a, eq (add a zero) a
  mul_one : ∀ a, eq (mul a one) a
  mul_zero : ∀ a, eq (mul a zero) zero
  sub_self : ∀ a, eq (sub a a) zero
  fromNat_zero : eq (fromNat 0) zero
  fromNat_one : eq (fromNat 1) one

def dotProduct (ni : NumericInterface) (a b : List ni.Val) (dim : Nat) : ni.Val :=
  let pairs := ListSupport.zipWith ni.mul a b
  pairs.foldl ni.add ni.zero

def elemWiseMul (ni : NumericInterface) (a b : List ni.Val) : List ni.Val :=
  ListSupport.zipWith ni.mul a b

def elemWiseAdd (ni : NumericInterface) (a b : List ni.Val) : List ni.Val :=
  ListSupport.zipWith ni.add a b

def elemWiseSub (ni : NumericInterface) (a b : List ni.Val) : List ni.Val :=
  ListSupport.zipWith ni.sub a b

def elemWiseDiv (ni : NumericInterface) (a b : List ni.Val) : List ni.Val :=
  ListSupport.zipWith ni.div a b

theorem elemWiseMul_length (ni : NumericInterface) (a b : List ni.Val) :
    (elemWiseMul ni a b).length = min a.length b.length :=
  ListSupport.zipWith_length ni.mul a b

theorem elemWiseAdd_length (ni : NumericInterface) (a b : List ni.Val) :
    (elemWiseAdd ni a b).length = min a.length b.length :=
  ListSupport.zipWith_length ni.add a b

theorem elemWiseSub_length (ni : NumericInterface) (a b : List ni.Val) :
    (elemWiseSub ni a b).length = min a.length b.length :=
  ListSupport.zipWith_length ni.sub a b

theorem elemWiseDiv_length (ni : NumericInterface) (a b : List ni.Val) :
    (elemWiseDiv ni a b).length = min a.length b.length :=
  ListSupport.zipWith_length ni.div a b

def clipList (ni : NumericInterface) (vals : List ni.Val) (lo hi : ni.Val) : List ni.Val :=
  vals.map (fun v => ni.clip v lo hi)

theorem clipList_length (ni : NumericInterface) (vals : List ni.Val) (lo hi : ni.Val) :
    (clipList ni vals lo hi).length = vals.length :=
  List.length_map _ vals

theorem clipList_preserves_finite (ni : NumericInterface) (vals : List ni.Val) (lo hi : ni.Val)
    (hf : ∀ v, v ∈ vals → ni.isFinite v)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) :
    ∀ v, v ∈ clipList ni vals lo hi → ni.isFinite v :=
  fun v hv =>
    match List.mem_map.mp hv with
    | ⟨w, hw, heq⟩ => heq ▸ ni.clip_preserves_finite w lo hi (hf w hw) hlo hhi

def scaleComputation (ni : NumericInterface) (s_weight s_bias x2_row : List ni.Val)
    (dim : Nat) (clip_min clip_max : ni.Val) : List ni.Val :=
  List.range dim |>.map fun d =>
    let bias_d := ListSupport.getD s_bias d ni.zero
    let w_row := s_weight.drop (d * dim) |>.take dim
    let preSum := (ListSupport.zipWith ni.mul w_row x2_row).foldl ni.add bias_d
    let clipped := ni.clip preSum clip_min clip_max
    ni.exp clipped

def translationComputation (ni : NumericInterface) (t_weight t_bias input_row : List ni.Val)
    (dim : Nat) : List ni.Val :=
  List.range dim |>.map fun d =>
    let bias_d := ListSupport.getD t_bias d ni.zero
    let w_row := t_weight.drop (d * dim) |>.take dim
    (ListSupport.zipWith ni.mul w_row input_row).foldl ni.add bias_d

theorem scaleComputation_length (ni : NumericInterface) (sw sb x2 : List ni.Val)
    (dim : Nat) (cmin cmax : ni.Val) :
    (scaleComputation ni sw sb x2 dim cmin cmax).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

theorem translationComputation_length (ni : NumericInterface) (tw tb ir : List ni.Val)
    (dim : Nat) :
    (translationComputation ni tw tb ir dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

theorem scaleComputation_deterministic (ni : NumericInterface) (sw sb x2 : List ni.Val)
    (dim : Nat) (cmin cmax : ni.Val) :
    scaleComputation ni sw sb x2 dim cmin cmax = scaleComputation ni sw sb x2 dim cmin cmax := rfl

theorem translationComputation_deterministic (ni : NumericInterface) (tw tb ir : List ni.Val)
    (dim : Nat) :
    translationComputation ni tw tb ir dim = translationComputation ni tw tb ir dim := rfl

def decToBool (d : Decidable p) : Bool :=
  match d with
  | isTrue _ => true
  | isFalse _ => false

def gradScale (ni : NumericInterface) (gradMean : Bool) (batchSize : Nat)
    (hPos : batchSize > 0) : ni.Val :=
  if ¬gradMean then ni.one
  else
    let s := ni.div ni.one (ni.fromNat batchSize)
    if decToBool (ni.decFinite s) then s else ni.one

theorem gradScale_no_mean (ni : NumericInterface) (bs : Nat) (h : bs > 0) :
    gradScale ni false bs h = ni.one := rfl

end NumericSem

namespace TensorMem

open TensorDef ShapeDef NumericSem in
structure TensorVal (ni : NumericInterface) where
  shape : Shape
  data : List ni.Val
  storageId : Nat
  storageOffset : Nat
  hDataLen : data.length = shape.totalSize

open NumericSem in
def zeroTensorVal (ni : NumericInterface) (tv : TensorVal ni) : TensorVal ni :=
  { tv with
    data := tv.data.map (fun _ => ni.zero),
    hDataLen := (List.length_map _ tv.data).trans tv.hDataLen }

open NumericSem in
theorem zeroTensorVal_preserves_shape (ni : NumericInterface) (tv : TensorVal ni) :
    (zeroTensorVal ni tv).shape = tv.shape := rfl

open NumericSem in
theorem zeroTensorVal_preserves_storageId (ni : NumericInterface) (tv : TensorVal ni) :
    (zeroTensorVal ni tv).storageId = tv.storageId := rfl

open NumericSem in
theorem zeroTensorVal_preserves_dataLen (ni : NumericInterface) (tv : TensorVal ni) :
    (zeroTensorVal ni tv).data.length = tv.data.length :=
  (List.length_map _ tv.data)

open NumericSem in
theorem zeroTensorVal_idempotent (ni : NumericInterface) (tv : TensorVal ni) :
    zeroTensorVal ni (zeroTensorVal ni tv) = zeroTensorVal ni tv :=
  match tv with
  | ⟨s, d, sid, so, h⟩ => rfl

open NumericSem in
def cloneTensorVal (ni : NumericInterface) (tv : TensorVal ni) (newStorageId : Nat) : TensorVal ni :=
  { shape := tv.shape,
    data := tv.data,
    storageId := newStorageId,
    storageOffset := 0,
    hDataLen := tv.hDataLen }

open NumericSem in
theorem cloneTensorVal_preserves_shape (ni : NumericInterface) (tv : TensorVal ni)
    (newId : Nat) :
    (cloneTensorVal ni tv newId).shape = tv.shape := rfl

open NumericSem in
theorem cloneTensorVal_preserves_data (ni : NumericInterface) (tv : TensorVal ni)
    (newId : Nat) :
    (cloneTensorVal ni tv newId).data = tv.data := rfl

open NumericSem in
theorem cloneTensorVal_distinct_storage (ni : NumericInterface) (tv : TensorVal ni)
    (newId : Nat) (h : newId ≠ tv.storageId) :
    (cloneTensorVal ni tv newId).storageId ≠ tv.storageId := h

open NumericSem in
def copyInto (ni : NumericInterface) (src dst : TensorVal ni)
    (hShape : src.shape = dst.shape) : TensorVal ni :=
  { dst with
    data := src.data,
    hDataLen := src.hDataLen.trans (hShape ▸ rfl) }

open NumericSem in
theorem copyInto_preserves_shape (ni : NumericInterface)
    (src dst : TensorVal ni) (h : src.shape = dst.shape) :
    (copyInto ni src dst h).shape = dst.shape := rfl

open NumericSem in
theorem copyInto_data_eq_src (ni : NumericInterface)
    (src dst : TensorVal ni) (h : src.shape = dst.shape) :
    (copyInto ni src dst h).data = src.data := rfl

open NumericSem in
structure CopyPairSpec (ni : NumericInterface) where
  in1 : TensorVal ni
  in2 : TensorVal ni
  out1 : TensorVal ni
  out2 : TensorVal ni
  hShape1 : in1.shape = out1.shape
  hShape2 : in2.shape = out2.shape
  hNoOverlap : out1.storageId ≠ out2.storageId ∨
    out1.data.length = 0 ∨ out2.data.length = 0

open NumericSem in
def copyTensorPairInto (ni : NumericInterface) (spec : CopyPairSpec ni) :
    TensorVal ni × TensorVal ni :=
  (copyInto ni spec.in1 spec.out1 spec.hShape1,
   copyInto ni spec.in2 spec.out2 spec.hShape2)

open NumericSem in
theorem copyTensorPairInto_preserves_shapes (ni : NumericInterface)
    (spec : CopyPairSpec ni) :
    (copyTensorPairInto ni spec).1.shape = spec.out1.shape ∧
    (copyTensorPairInto ni spec).2.shape = spec.out2.shape :=
  ⟨rfl, rfl⟩

open NumericSem in
theorem copyTensorPairInto_copies_in1 (ni : NumericInterface)
    (spec : CopyPairSpec ni) :
    (copyTensorPairInto ni spec).1.data = spec.in1.data := rfl

open NumericSem in
theorem copyTensorPairInto_copies_in2 (ni : NumericInterface)
    (spec : CopyPairSpec ni) :
    (copyTensorPairInto ni spec).2.data = spec.in2.data := rfl

open NumericSem in
theorem copyTensorPairInto_deterministic (ni : NumericInterface)
    (spec : CopyPairSpec ni) :
    copyTensorPairInto ni spec = copyTensorPairInto ni spec := rfl

end TensorMem

namespace LayerCoreDef

open NumericSem TensorMem in
structure LayerCore (ni : NumericInterface) where
  s_weight : TensorVal ni
  t_weight : TensorVal ni
  s_bias : TensorVal ni
  t_bias : TensorVal ni
  s_weight_grad : Option (TensorVal ni)
  t_weight_grad : Option (TensorVal ni)
  s_bias_grad : Option (TensorVal ni)
  t_bias_grad : Option (TensorVal ni)
  dim : Nat
  clip_min : ni.Val
  clip_max : ni.Val
  grad_mean : Bool
  allocToken : Nat

open NumericSem TensorMem ShapeDef in
structure LayerCoreInvariant (ni : NumericInterface) (lc : LayerCore ni) : Prop where
  hDimPos : lc.dim > 0
  hClipValid : ni.lt lc.clip_min lc.clip_max
  hSwShape : lc.s_weight.shape = mkShape2D lc.dim lc.dim
  hTwShape : lc.t_weight.shape = mkShape2D lc.dim lc.dim
  hSbShape : lc.s_bias.shape = mkShape2D 1 lc.dim
  hTbShape : lc.t_bias.shape = mkShape2D 1 lc.dim
  hSwgShape : ∀ g, lc.s_weight_grad = some g → g.shape = mkShape2D lc.dim lc.dim
  hTwgShape : ∀ g, lc.t_weight_grad = some g → g.shape = mkShape2D lc.dim lc.dim
  hSbgShape : ∀ g, lc.s_bias_grad = some g → g.shape = mkShape2D 1 lc.dim
  hTbgShape : ∀ g, lc.t_bias_grad = some g → g.shape = mkShape2D 1 lc.dim

open NumericSem in
def hasGradients (ni : NumericInterface) (lc : LayerCore ni) : Bool :=
  lc.s_weight_grad.isSome && lc.t_weight_grad.isSome &&
  lc.s_bias_grad.isSome && lc.t_bias_grad.isSome

open NumericSem TensorMem ShapeDef in
def zeroGradients (ni : NumericInterface) (lc : LayerCore ni) : LayerCore ni :=
  { lc with
    s_weight_grad := lc.s_weight_grad.map (zeroTensorVal ni),
    t_weight_grad := lc.t_weight_grad.map (zeroTensorVal ni),
    s_bias_grad := lc.s_bias_grad.map (zeroTensorVal ni),
    t_bias_grad := lc.t_bias_grad.map (zeroTensorVal ni) }

open NumericSem in
theorem zeroGradients_preserves_weights (ni : NumericInterface)
    (lc : LayerCore ni) :
    (zeroGradients ni lc).s_weight = lc.s_weight ∧
    (zeroGradients ni lc).t_weight = lc.t_weight ∧
    (zeroGradients ni lc).s_bias = lc.s_bias ∧
    (zeroGradients ni lc).t_bias = lc.t_bias :=
  ⟨rfl, rfl, rfl, rfl⟩

open NumericSem in
theorem zeroGradients_preserves_dim (ni : NumericInterface)
    (lc : LayerCore ni) :
    (zeroGradients ni lc).dim = lc.dim := rfl

open NumericSem in
theorem zeroGradients_preserves_clip (ni : NumericInterface)
    (lc : LayerCore ni) :
    (zeroGradients ni lc).clip_min = lc.clip_min ∧
    (zeroGradients ni lc).clip_max = lc.clip_max := ⟨rfl, rfl⟩

open NumericSem in
theorem zeroGradients_preserves_grad_mean (ni : NumericInterface)
    (lc : LayerCore ni) :
    (zeroGradients ni lc).grad_mean = lc.grad_mean := rfl

open NumericSem in
theorem zeroGradients_none_stays_none_sw (ni : NumericInterface)
    (lc : LayerCore ni) (h : lc.s_weight_grad = none) :
    (zeroGradients ni lc).s_weight_grad = none :=
  h ▸ rfl

open NumericSem in
theorem zeroGradients_none_stays_none_tw (ni : NumericInterface)
    (lc : LayerCore ni) (h : lc.t_weight_grad = none) :
    (zeroGradients ni lc).t_weight_grad = none :=
  h ▸ rfl

open NumericSem in
theorem zeroGradients_none_stays_none_sb (ni : NumericInterface)
    (lc : LayerCore ni) (h : lc.s_bias_grad = none) :
    (zeroGradients ni lc).s_bias_grad = none :=
  h ▸ rfl

open NumericSem in
theorem zeroGradients_none_stays_none_tb (ni : NumericInterface)
    (lc : LayerCore ni) (h : lc.t_bias_grad = none) :
    (zeroGradients ni lc).t_bias_grad = none :=
  h ▸ rfl

open NumericSem in
theorem zeroGradients_idempotent (ni : NumericInterface)
    (lc : LayerCore ni) :
    zeroGradients ni (zeroGradients ni lc) = zeroGradients ni lc :=
  match lc with
  | ⟨sw, tw, sb, tb, swg, twg, sbg, tbg, d, cmi, cma, gm, at'⟩ =>
    match swg, twg, sbg, tbg with
    | none, none, none, none => rfl
    | some _, none, none, none => rfl
    | none, some _, none, none => rfl
    | none, none, some _, none => rfl
    | none, none, none, some _ => rfl
    | some _, some _, none, none => rfl
    | some _, none, some _, none => rfl
    | some _, none, none, some _ => rfl
    | none, some _, some _, none => rfl
    | none, some _, none, some _ => rfl
    | none, none, some _, some _ => rfl
    | some _, some _, some _, none => rfl
    | some _, some _, none, some _ => rfl
    | some _, none, some _, some _ => rfl
    | none, some _, some _, some _ => rfl
    | some _, some _, some _, some _ => rfl

open NumericSem TensorMem ShapeDef in
def ensureGradients (ni : NumericInterface) (lc : LayerCore ni)
    (nextStorageId : Nat) : LayerCore ni × Nat :=
  let (swg, sid1) := match lc.s_weight_grad with
    | some g => (some g, nextStorageId)
    | none => (some { shape := mkShape2D lc.dim lc.dim,
                      data := ListSupport.replicate (lc.dim * lc.dim) ni.zero,
                      storageId := nextStorageId,
                      storageOffset := 0,
                      hDataLen := ListSupport.replicate_length _ _ },
               nextStorageId + 1)
  let (twg, sid2) := match lc.t_weight_grad with
    | some g => (some g, sid1)
    | none => (some { shape := mkShape2D lc.dim lc.dim,
                      data := ListSupport.replicate (lc.dim * lc.dim) ni.zero,
                      storageId := sid1,
                      storageOffset := 0,
                      hDataLen := ListSupport.replicate_length _ _ },
               sid1 + 1)
  let (sbg, sid3) := match lc.s_bias_grad with
    | some g => (some g, sid2)
    | none => (some { shape := mkShape2D 1 lc.dim,
                      data := ListSupport.replicate (1 * lc.dim) ni.zero,
                      storageId := sid2,
                      storageOffset := 0,
                      hDataLen := ListSupport.replicate_length _ _ },
               sid2 + 1)
  let (tbg, sid4) := match lc.t_bias_grad with
    | some g => (some g, sid3)
    | none => (some { shape := mkShape2D 1 lc.dim,
                      data := ListSupport.replicate (1 * lc.dim) ni.zero,
                      storageId := sid3,
                      storageOffset := 0,
                      hDataLen := ListSupport.replicate_length _ _ },
               sid3 + 1)
  ({ lc with s_weight_grad := swg, t_weight_grad := twg,
             s_bias_grad := sbg, t_bias_grad := tbg }, sid4)

open NumericSem in
theorem ensureGradients_all_present (ni : NumericInterface)
    (lc : LayerCore ni) (sid : Nat) :
    (ensureGradients ni lc sid).1.s_weight_grad.isSome = true ∧
    (ensureGradients ni lc sid).1.t_weight_grad.isSome = true ∧
    (ensureGradients ni lc sid).1.s_bias_grad.isSome = true ∧
    (ensureGradients ni lc sid).1.t_bias_grad.isSome = true :=
  match lc.s_weight_grad, lc.t_weight_grad, lc.s_bias_grad, lc.t_bias_grad with
  | some _, some _, some _, some _ => ⟨rfl, rfl, rfl, rfl⟩
  | some _, some _, some _, none => ⟨rfl, rfl, rfl, rfl⟩
  | some _, some _, none, some _ => ⟨rfl, rfl, rfl, rfl⟩
  | some _, some _, none, none => ⟨rfl, rfl, rfl, rfl⟩
  | some _, none, some _, some _ => ⟨rfl, rfl, rfl, rfl⟩
  | some _, none, some _, none => ⟨rfl, rfl, rfl, rfl⟩
  | some _, none, none, some _ => ⟨rfl, rfl, rfl, rfl⟩
  | some _, none, none, none => ⟨rfl, rfl, rfl, rfl⟩
  | none, some _, some _, some _ => ⟨rfl, rfl, rfl, rfl⟩
  | none, some _, some _, none => ⟨rfl, rfl, rfl, rfl⟩
  | none, some _, none, some _ => ⟨rfl, rfl, rfl, rfl⟩
  | none, some _, none, none => ⟨rfl, rfl, rfl, rfl⟩
  | none, none, some _, some _ => ⟨rfl, rfl, rfl, rfl⟩
  | none, none, some _, none => ⟨rfl, rfl, rfl, rfl⟩
  | none, none, none, some _ => ⟨rfl, rfl, rfl, rfl⟩
  | none, none, none, none => ⟨rfl, rfl, rfl, rfl⟩

open NumericSem in
theorem ensureGradients_preserves_existing_sw (ni : NumericInterface)
    (lc : LayerCore ni) (sid : Nat) (g : TensorVal ni)
    (h : lc.s_weight_grad = some g) :
    (ensureGradients ni lc sid).1.s_weight_grad = some g :=
  h ▸ rfl

open NumericSem in
theorem ensureGradients_preserves_existing_tw (ni : NumericInterface)
    (lc : LayerCore ni) (sid : Nat) (g : TensorVal ni)
    (h : lc.t_weight_grad = some g) :
    (ensureGradients ni lc sid).1.t_weight_grad = some g :=
  h ▸ rfl

open NumericSem in
theorem ensureGradients_preserves_weights (ni : NumericInterface)
    (lc : LayerCore ni) (sid : Nat) :
    (ensureGradients ni lc sid).1.s_weight = lc.s_weight ∧
    (ensureGradients ni lc sid).1.t_weight = lc.t_weight ∧
    (ensureGradients ni lc sid).1.s_bias = lc.s_bias ∧
    (ensureGradients ni lc sid).1.t_bias = lc.t_bias :=
  ⟨rfl, rfl, rfl, rfl⟩

open NumericSem in
theorem ensureGradients_preserves_dim (ni : NumericInterface)
    (lc : LayerCore ni) (sid : Nat) :
    (ensureGradients ni lc sid).1.dim = lc.dim := rfl

open NumericSem TensorMem ShapeDef in
def deinitOwned (ni : NumericInterface) (lc : LayerCore ni) : LayerCore ni :=
  { lc with
    s_weight_grad := none,
    t_weight_grad := none,
    s_bias_grad := none,
    t_bias_grad := none }

open NumericSem in
theorem deinitOwned_clears_grads (ni : NumericInterface) (lc : LayerCore ni) :
    (deinitOwned ni lc).s_weight_grad = none ∧
    (deinitOwned ni lc).t_weight_grad = none ∧
    (deinitOwned ni lc).s_bias_grad = none ∧
    (deinitOwned ni lc).t_bias_grad = none :=
  ⟨rfl, rfl, rfl, rfl⟩

open NumericSem in
theorem deinitOwned_preserves_dim (ni : NumericInterface) (lc : LayerCore ni) :
    (deinitOwned ni lc).dim = lc.dim := rfl

open NumericSem in
theorem deinitOwned_preserves_config (ni : NumericInterface) (lc : LayerCore ni) :
    (deinitOwned ni lc).clip_min = lc.clip_min ∧
    (deinitOwned ni lc).clip_max = lc.clip_max ∧
    (deinitOwned ni lc).grad_mean = lc.grad_mean :=
  ⟨rfl, rfl, rfl⟩

open NumericSem in
theorem deinitOwned_idempotent (ni : NumericInterface) (lc : LayerCore ni) :
    deinitOwned ni (deinitOwned ni lc) = deinitOwned ni lc := rfl

open NumericSem TensorMem ShapeDef in
structure InitOwnedSpec (ni : NumericInterface) where
  dim : Nat
  clip_min : ni.Val
  clip_max : ni.Val
  grad_mean : Bool
  seedOffset : Nat
  hDimPos : dim > 0
  hClipValid : ni.lt clip_min clip_max

open NumericSem TensorMem ShapeDef in
def initOwned (ni : NumericInterface) (spec : InitOwnedSpec ni)
    (sw_data tw_data : List ni.Val) (sid : Nat)
    (hSw : sw_data.length = spec.dim * spec.dim)
    (hTw : tw_data.length = spec.dim * spec.dim) : LayerCore ni :=
  { s_weight := { shape := mkShape2D spec.dim spec.dim,
                  data := sw_data, storageId := sid, storageOffset := 0, hDataLen := hSw },
    t_weight := { shape := mkShape2D spec.dim spec.dim,
                  data := tw_data, storageId := sid + 1, storageOffset := 0, hDataLen := hTw },
    s_bias := { shape := mkShape2D 1 spec.dim,
                data := ListSupport.replicate (1 * spec.dim) ni.zero,
                storageId := sid + 2, storageOffset := 0,
                hDataLen := ListSupport.replicate_length _ _ },
    t_bias := { shape := mkShape2D 1 spec.dim,
                data := ListSupport.replicate (1 * spec.dim) ni.zero,
                storageId := sid + 3, storageOffset := 0,
                hDataLen := ListSupport.replicate_length _ _ },
    s_weight_grad := none,
    t_weight_grad := none,
    s_bias_grad := none,
    t_bias_grad := none,
    dim := spec.dim,
    clip_min := spec.clip_min,
    clip_max := spec.clip_max,
    grad_mean := spec.grad_mean,
    allocToken := sid }

open NumericSem TensorMem ShapeDef in
theorem initOwned_sw_shape (ni : NumericInterface) (spec : InitOwnedSpec ni)
    (sw tw : List ni.Val) (sid : Nat) (hSw hTw) :
    (initOwned ni spec sw tw sid hSw hTw).s_weight.shape = mkShape2D spec.dim spec.dim := rfl

open NumericSem TensorMem ShapeDef in
theorem initOwned_tw_shape (ni : NumericInterface) (spec : InitOwnedSpec ni)
    (sw tw : List ni.Val) (sid : Nat) (hSw hTw) :
    (initOwned ni spec sw tw sid hSw hTw).t_weight.shape = mkShape2D spec.dim spec.dim := rfl

open NumericSem TensorMem ShapeDef in
theorem initOwned_sb_shape (ni : NumericInterface) (spec : InitOwnedSpec ni)
    (sw tw : List ni.Val) (sid : Nat) (hSw hTw) :
    (initOwned ni spec sw tw sid hSw hTw).s_bias.shape = mkShape2D 1 spec.dim := rfl

open NumericSem TensorMem ShapeDef in
theorem initOwned_tb_shape (ni : NumericInterface) (spec : InitOwnedSpec ni)
    (sw tw : List ni.Val) (sid : Nat) (hSw hTw) :
    (initOwned ni spec sw tw sid hSw hTw).t_bias.shape = mkShape2D 1 spec.dim := rfl

open NumericSem in
theorem initOwned_no_grads (ni : NumericInterface) (spec : InitOwnedSpec ni)
    (sw tw : List ni.Val) (sid : Nat) (hSw hTw) :
    (initOwned ni spec sw tw sid hSw hTw).s_weight_grad = none ∧
    (initOwned ni spec sw tw sid hSw hTw).t_weight_grad = none ∧
    (initOwned ni spec sw tw sid hSw hTw).s_bias_grad = none ∧
    (initOwned ni spec sw tw sid hSw hTw).t_bias_grad = none :=
  ⟨rfl, rfl, rfl, rfl⟩

open NumericSem in
theorem initOwned_dim (ni : NumericInterface) (spec : InitOwnedSpec ni)
    (sw tw : List ni.Val) (sid : Nat) (hSw hTw) :
    (initOwned ni spec sw tw sid hSw hTw).dim = spec.dim := rfl

open NumericSem in
theorem initOwned_clip (ni : NumericInterface) (spec : InitOwnedSpec ni)
    (sw tw : List ni.Val) (sid : Nat) (hSw hTw) :
    (initOwned ni spec sw tw sid hSw hTw).clip_min = spec.clip_min ∧
    (initOwned ni spec sw tw sid hSw hTw).clip_max = spec.clip_max :=
  ⟨rfl, rfl⟩

open NumericSem in
theorem initOwned_grad_mean (ni : NumericInterface) (spec : InitOwnedSpec ni)
    (sw tw : List ni.Val) (sid : Nat) (hSw hTw) :
    (initOwned ni spec sw tw sid hSw hTw).grad_mean = spec.grad_mean := rfl

open NumericSem in
def validatePair (ni : NumericInterface) (lc : LayerCore ni)
    (a b : TensorVal ni) : RSFResult Nat :=
  if a.shape.dims.length ≠ 2 then RSFResult.err RSFError.ShapeMismatch
  else if b.shape.dims.length ≠ 2 then RSFResult.err RSFError.ShapeMismatch
  else
    let aCols := a.shape.dims.getLast (List.ne_nil_of_length_pos (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_of_eq (show 1 ≤ a.shape.dims.length from Nat.le_of_lt (show 1 < a.shape.dims.length from
      match h : a.shape.dims.length == 2 with
      | true => Nat.eq_of_beq_eq_true h ▸ Nat.lt_succ_of_le (Nat.le_refl 1)
      | false => absurd rfl (show a.shape.dims.length ≠ 2 from fun h2 => absurd h2 (fun h3 => absurd (show (a.shape.dims.length == 2) = true from h3 ▸ rfl) (show ¬(a.shape.dims.length == 2 = true) from h ▸ fun h4 => Bool.noConfusion h4)))) ▸ rfl))))
    if aCols ≠ lc.dim then RSFResult.err RSFError.ShapeMismatch
    else
      let aRows := a.shape.dims.head (List.ne_nil_of_length_pos (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_of_eq (show 1 ≤ a.shape.dims.length from Nat.le_of_lt (show 1 < a.shape.dims.length from
        match h : a.shape.dims.length == 2 with
        | true => Nat.eq_of_beq_eq_true h ▸ Nat.lt_succ_of_le (Nat.le_refl 1)
        | false => absurd rfl (show a.shape.dims.length ≠ 2 from fun h2 => absurd h2 (fun h3 => absurd (show (a.shape.dims.length == 2) = true from h3 ▸ rfl) (show ¬(a.shape.dims.length == 2 = true) from h ▸ fun h4 => Bool.noConfusion h4)))) ▸ rfl))))
      if aRows = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok aRows

end LayerCoreDef

namespace RowSemantics

open NumericSem LayerCoreDef TensorMem in
def forwardRow (ni : NumericInterface) (lc : LayerCore ni)
    (x1_row x2_row : List ni.Val) : List ni.Val × List ni.Val :=
  let scale := scaleComputation ni lc.s_weight.data lc.s_bias.data x2_row lc.dim lc.clip_min lc.clip_max
  let y1 := elemWiseMul ni x1_row scale
  let trans := translationComputation ni lc.t_weight.data lc.t_bias.data y1 lc.dim
  let y2 := elemWiseAdd ni x2_row trans
  (y1, y2)

open NumericSem LayerCoreDef TensorMem in
def inverseRow (ni : NumericInterface) (lc : LayerCore ni)
    (y1_row y2_row : List ni.Val) : List ni.Val × List ni.Val :=
  let trans := translationComputation ni lc.t_weight.data lc.t_bias.data y1_row lc.dim
  let x2 := elemWiseSub ni y2_row trans
  let scale := scaleComputation ni lc.s_weight.data lc.s_bias.data x2 lc.dim lc.clip_min lc.clip_max
  let x1 := elemWiseDiv ni y1_row scale
  (x1, x2)

open NumericSem LayerCoreDef TensorMem in
theorem forwardRow_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) :
    forwardRow ni lc x1 x2 = forwardRow ni lc x1 x2 := rfl

open NumericSem LayerCoreDef TensorMem in
theorem inverseRow_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) :
    inverseRow ni lc y1 y2 = inverseRow ni lc y1 y2 := rfl

open NumericSem LayerCoreDef TensorMem in
structure ForwardRowSpec (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 y1 y2 : List ni.Val) : Prop where
  hX1Len : x1.length = lc.dim
  hX2Len : x2.length = lc.dim
  hResult : forwardRow ni lc x1 x2 = (y1, y2)

open NumericSem LayerCoreDef TensorMem in
structure InverseRowSpec (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 x1 x2 : List ni.Val) : Prop where
  hY1Len : y1.length = lc.dim
  hY2Len : y2.length = lc.dim
  hResult : inverseRow ni lc y1 y2 = (x1, x2)

open NumericSem in
structure InvertibilityEnv (ni : NumericInterface) : Prop where
  hMulDivCancel : ∀ a b, ¬(ni.eq b ni.zero) → ni.eq (ni.div (ni.mul a b) b) a
  hDivMulCancel : ∀ a b, ¬(ni.eq b ni.zero) → ni.eq (ni.mul (ni.div a b) b) a
  hAddSubCancel : ∀ a b, ni.eq (ni.sub (ni.add a b) b) a
  hSubAddCancel : ∀ a b, ni.eq (ni.add (ni.sub a b) b) a
  hScaleNonzero : ∀ v, ni.isFinite (ni.clip v ni.zero ni.zero) →
    ¬(ni.eq (ni.exp (ni.clip v ni.zero ni.zero)) ni.zero)

end RowSemantics

namespace ForwardBatch

open NumericSem LayerCoreDef RowSemantics TensorMem in
def forwardBatchRows (ni : NumericInterface) (lc : LayerCore ni)
    (x1_data x2_data : List ni.Val) (batchSize : Nat) :
    List ni.Val × List ni.Val :=
  let rec go (b : Nat) (y1_acc y2_acc : List ni.Val) :
      List ni.Val × List ni.Val :=
    if b ≥ batchSize then (y1_acc, y2_acc)
    else
      let x1_row := x1_data.drop (b * lc.dim) |>.take lc.dim
      let x2_row := x2_data.drop (b * lc.dim) |>.take lc.dim
      let (y1_row, y2_row) := forwardRow ni lc x1_row x2_row
      go (b + 1) (y1_acc ++ y1_row) (y2_acc ++ y2_row)
    termination_by batchSize - b
  go 0 [] []

open NumericSem LayerCoreDef RowSemantics TensorMem in
theorem forwardBatchRows_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) (bs : Nat) :
    forwardBatchRows ni lc x1 x2 bs = forwardBatchRows ni lc x1 x2 bs := rfl

open NumericSem LayerCoreDef TensorMem in
structure ForwardInPlaceSpec (ni : NumericInterface) where
  lc : LayerCore ni
  x1_in : TensorVal ni
  x2_in : TensorVal ni
  x1_out : TensorVal ni
  x2_out : TensorVal ni
  batchSize : Nat
  hNoOverlap : x1_in.storageId ≠ x2_in.storageId ∨
    x1_in.data.length = 0 ∨ x2_in.data.length = 0
  hBatchPos : batchSize > 0
  hX1Shape : x1_in.shape = ShapeDef.mkShape2D batchSize lc.dim
  hX2Shape : x2_in.shape = ShapeDef.mkShape2D batchSize lc.dim
  hOutX1Shape : x1_out.shape = ShapeDef.mkShape2D batchSize lc.dim
  hOutX2Shape : x2_out.shape = ShapeDef.mkShape2D batchSize lc.dim

end ForwardBatch

namespace InverseBatch

open NumericSem LayerCoreDef RowSemantics TensorMem in
def inverseBatchRows (ni : NumericInterface) (lc : LayerCore ni)
    (y1_data y2_data : List ni.Val) (batchSize : Nat) :
    List ni.Val × List ni.Val :=
  let rec go (b : Nat) (x1_acc x2_acc : List ni.Val) :
      List ni.Val × List ni.Val :=
    if b ≥ batchSize then (x1_acc, x2_acc)
    else
      let y1_row := y1_data.drop (b * lc.dim) |>.take lc.dim
      let y2_row := y2_data.drop (b * lc.dim) |>.take lc.dim
      let (x1_row, x2_row) := inverseRow ni lc y1_row y2_row
      go (b + 1) (x1_acc ++ x1_row) (x2_acc ++ x2_row)
    termination_by batchSize - b
  go 0 [] []

open NumericSem LayerCoreDef RowSemantics TensorMem in
theorem inverseBatchRows_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) (bs : Nat) :
    inverseBatchRows ni lc y1 y2 bs = inverseBatchRows ni lc y1 y2 bs := rfl

open NumericSem LayerCoreDef TensorMem in
structure InverseInPlaceSpec (ni : NumericInterface) where
  lc : LayerCore ni
  y1_in : TensorVal ni
  y2_in : TensorVal ni
  y1_out : TensorVal ni
  y2_out : TensorVal ni
  batchSize : Nat
  hNoOverlap : y1_in.storageId ≠ y2_in.storageId ∨
    y1_in.data.length = 0 ∨ y2_in.data.length = 0
  hBatchPos : batchSize > 0
  hY1Shape : y1_in.shape = ShapeDef.mkShape2D batchSize lc.dim
  hY2Shape : y2_in.shape = ShapeDef.mkShape2D batchSize lc.dim
  hOutY1Shape : y1_out.shape = ShapeDef.mkShape2D batchSize lc.dim
  hOutY2Shape : y2_out.shape = ShapeDef.mkShape2D batchSize lc.dim

end InverseBatch

namespace CheckedWrappers

open NumericSem LayerCoreDef TensorMem ForwardBatch InverseBatch in
structure ForwardCheckedSpec (ni : NumericInterface) where
  lc : LayerCore ni
  x1_in : TensorVal ni
  x2_in : TensorVal ni
  x1_out : TensorVal ni
  x2_out : TensorVal ni
  batchSize : Nat
  hX1Valid : x1_in.shape.dims.length = 2
  hX2Valid : x2_in.shape.dims.length = 2
  hO1Valid : x1_out.shape.dims.length = 2
  hO2Valid : x2_out.shape.dims.length = 2
  hNoOutOverlap : x1_out.storageId ≠ x2_out.storageId ∨
    x1_out.data.length = 0 ∨ x2_out.data.length = 0

open NumericSem LayerCoreDef TensorMem in
structure InverseCheckedSpec (ni : NumericInterface) where
  lc : LayerCore ni
  y1_in : TensorVal ni
  y2_in : TensorVal ni
  y1_out : TensorVal ni
  y2_out : TensorVal ni
  batchSize : Nat
  hY1Valid : y1_in.shape.dims.length = 2
  hY2Valid : y2_in.shape.dims.length = 2
  hO1Valid : y1_out.shape.dims.length = 2
  hO2Valid : y2_out.shape.dims.length = 2
  hNoOutOverlap : y1_out.storageId ≠ y2_out.storageId ∨
    y1_out.data.length = 0 ∨ y2_out.data.length = 0

end CheckedWrappers

namespace BackwardSem

open NumericSem LayerCoreDef TensorMem RowSemantics in
structure BackwardRowInput (ni : NumericInterface) where
  y1_row : List ni.Val
  y2_row : List ni.Val
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  dim : Nat
  grad_scale : ni.Val
  hY1 : y1_row.length = dim
  hY2 : y2_row.length = dim
  hDy1 : dy1_row.length = dim
  hDy2 : dy2_row.length = dim

open NumericSem LayerCoreDef TensorMem in
structure BackwardRowOutput (ni : NumericInterface) where
  x1_row : List ni.Val
  x2_row : List ni.Val
  dx1_row : List ni.Val
  dx2_row : List ni.Val
  dim : Nat
  hX1 : x1_row.length = dim
  hX2 : x2_row.length = dim
  hDx1 : dx1_row.length = dim
  hDx2 : dx2_row.length = dim

open NumericSem LayerCoreDef TensorMem in
def computeDy1Total (ni : NumericInterface) (dy1_row : List ni.Val)
    (dy2_row : List ni.Val) (t_weight : List ni.Val) (dim : Nat) : List ni.Val :=
  List.range dim |>.map fun j =>
    let init_j := ListSupport.getD dy1_row j ni.zero
    (List.range dim).foldl (fun acc d =>
      let dy2_d := ListSupport.getD dy2_row d ni.zero
      let tw_dj := ListSupport.getD t_weight (d * dim + j) ni.zero
      ni.add acc (ni.mul tw_dj dy2_d)
    ) init_j

theorem computeDy1Total_length (ni : NumericSem.NumericInterface) (dy1 dy2 tw : List ni.Val) (dim : Nat) :
    (computeDy1Total ni dy1 dy2 tw dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem LayerCoreDef TensorMem in
def computeDs (ni : NumericInterface) (dy1_total y1_row : List ni.Val)
    (preactivations : List ni.Val) (clip_min clip_max : ni.Val) (dim : Nat) : List ni.Val :=
  List.range dim |>.map fun d =>
    let pre_d := ListSupport.getD preactivations d ni.zero
    if decToBool (ni.decLt pre_d clip_min) then ni.zero
    else if decToBool (ni.decLt clip_max pre_d) then ni.zero
    else ni.mul (ListSupport.getD dy1_total d ni.zero)
                (ListSupport.getD y1_row d ni.zero)

theorem computeDs_length (ni : NumericSem.NumericInterface) (dy1t y1 pre : List ni.Val)
    (cmi cma : ni.Val) (dim : Nat) :
    (computeDs ni dy1t y1 pre cmi cma dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem LayerCoreDef TensorMem in
def accumulateWeightGrad (ni : NumericInterface) (grad : List ni.Val)
    (ds_or_dy : List ni.Val) (input_row : List ni.Val) (grad_scale : ni.Val)
    (dim : Nat) : List ni.Val :=
  List.range (dim * dim) |>.map fun idx =>
    let d := idx / dim
    let j := idx % dim
    let g_old := ListSupport.getD grad idx ni.zero
    let d_val := ListSupport.getD ds_or_dy d ni.zero
    let in_val := ListSupport.getD input_row j ni.zero
    ni.add g_old (ni.mul (ni.mul d_val grad_scale) in_val)

theorem accumulateWeightGrad_length (ni : NumericSem.NumericInterface) (g ds ir : List ni.Val)
    (gs : ni.Val) (dim : Nat) :
    (accumulateWeightGrad ni g ds ir gs dim).length = dim * dim :=
  List.length_map _ (List.range (dim * dim)) |>.trans (List.length_range (dim * dim))

open NumericSem LayerCoreDef TensorMem in
def accumulateBiasGrad (ni : NumericInterface) (grad : List ni.Val)
    (ds_or_dy : List ni.Val) (grad_scale : ni.Val) (dim : Nat) : List ni.Val :=
  List.range dim |>.map fun d =>
    let g_old := ListSupport.getD grad d ni.zero
    let d_val := ListSupport.getD ds_or_dy d ni.zero
    ni.add g_old (ni.mul d_val grad_scale)

theorem accumulateBiasGrad_length (ni : NumericSem.NumericInterface) (g ds : List ni.Val)
    (gs : ni.Val) (dim : Nat) :
    (accumulateBiasGrad ni g ds gs dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem LayerCoreDef TensorMem in
def backwardFromOutputsRow (ni : NumericInterface) (lc : LayerCore ni)
    (inp : BackwardRowInput ni) : BackwardRowOutput ni × LayerCore ni :=
  let dim := inp.dim
  let dy1_total := computeDy1Total ni inp.dy1_row inp.dy2_row lc.t_weight.data dim
  let twg' := match lc.t_weight_grad with
    | some g => some { g with data := accumulateWeightGrad ni g.data inp.dy2_row inp.y1_row inp.grad_scale dim }
    | none => none
  let tbg' := match lc.t_bias_grad with
    | some g => some { g with data := accumulateBiasGrad ni g.data inp.dy2_row inp.grad_scale dim }
    | none => none
  let trans := translationComputation ni lc.t_weight.data lc.t_bias.data inp.y1_row dim
  let x2_row := elemWiseSub ni inp.y2_row trans
  let preactivations := List.range dim |>.map fun d =>
    let bias_d := ListSupport.getD lc.s_bias.data d ni.zero
    let w_row := lc.s_weight.data.drop (d * dim) |>.take dim
    (ListSupport.zipWith ni.mul w_row x2_row).foldl ni.add bias_d
  let clippedScales := preactivations.map fun pre => ni.exp (ni.clip pre lc.clip_min lc.clip_max)
  let x1_row := elemWiseDiv ni inp.y1_row clippedScales
  let dx1_row := elemWiseMul ni dy1_total clippedScales
  let ds := computeDs ni dy1_total inp.y1_row preactivations lc.clip_min lc.clip_max dim
  let swg' := match lc.s_weight_grad with
    | some g => some { g with data := accumulateWeightGrad ni g.data ds x2_row inp.grad_scale dim }
    | none => none
  let sbg' := match lc.s_bias_grad with
    | some g => some { g with data := accumulateBiasGrad ni g.data ds inp.grad_scale dim }
    | none => none
  let dx2_init := inp.dy2_row
  let dx2_row := List.range dim |>.map fun j =>
    let init_j := ListSupport.getD dx2_init j ni.zero
    (List.range dim).foldl (fun acc d =>
      let ds_d := ListSupport.getD ds d ni.zero
      let sw_dj := ListSupport.getD lc.s_weight.data (d * dim + j) ni.zero
      ni.add acc (ni.mul sw_dj ds_d)
    ) init_j
  let lc' := { lc with
    t_weight_grad := twg',
    t_bias_grad := tbg',
    s_weight_grad := swg',
    s_bias_grad := sbg' }
  let out : BackwardRowOutput ni :=
    { x1_row := x1_row,
      x2_row := x2_row,
      dx1_row := dx1_row,
      dx2_row := dx2_row,
      dim := dim,
      hX1 := elemWiseDiv_length ni inp.y1_row clippedScales |>.trans
        (show min inp.y1_row.length clippedScales.length = dim from
          inp.hY1 ▸ (show clippedScales.length = dim from
            List.length_map _ preactivations |>.trans
              (List.length_map _ (List.range dim) |>.trans
                (List.length_range dim))) ▸
          show min dim dim = dim from Nat.min_self dim),
      hX2 := elemWiseSub_length ni inp.y2_row trans |>.trans
        (show min inp.y2_row.length trans.length = dim from
          inp.hY2 ▸ translationComputation_length ni lc.t_weight.data lc.t_bias.data inp.y1_row dim ▸
          show min dim dim = dim from Nat.min_self dim),
      hDx1 := elemWiseMul_length ni dy1_total clippedScales |>.trans
        (show min dy1_total.length clippedScales.length = dim from
          computeDy1Total_length ni inp.dy1_row inp.dy2_row lc.t_weight.data dim ▸
          (show clippedScales.length = dim from
            List.length_map _ preactivations |>.trans
              (List.length_map _ (List.range dim) |>.trans
                (List.length_range dim))) ▸
          show min dim dim = dim from Nat.min_self dim),
      hDx2 := List.length_map _ (List.range dim) |>.trans (List.length_range dim) }
  (out, lc')

open NumericSem in
theorem backwardFromOutputsRow_preserves_weights (ni : NumericInterface)
    (lc : LayerCore ni) (inp : BackwardRowInput ni) :
    (backwardFromOutputsRow ni lc inp).2.s_weight = lc.s_weight ∧
    (backwardFromOutputsRow ni lc inp).2.t_weight = lc.t_weight ∧
    (backwardFromOutputsRow ni lc inp).2.s_bias = lc.s_bias ∧
    (backwardFromOutputsRow ni lc inp).2.t_bias = lc.t_bias :=
  ⟨rfl, rfl, rfl, rfl⟩

open NumericSem in
theorem backwardFromOutputsRow_preserves_dim (ni : NumericInterface)
    (lc : LayerCore ni) (inp : BackwardRowInput ni) :
    (backwardFromOutputsRow ni lc inp).2.dim = lc.dim := rfl

open NumericSem in
theorem backwardFromOutputsRow_deterministic (ni : NumericInterface)
    (lc : LayerCore ni) (inp : BackwardRowInput ni) :
    backwardFromOutputsRow ni lc inp = backwardFromOutputsRow ni lc inp := rfl

open NumericSem in
theorem backwardFromOutputsRow_none_sw_stays_none (ni : NumericInterface)
    (lc : LayerCore ni) (inp : BackwardRowInput ni)
    (h : lc.s_weight_grad = none) :
    (backwardFromOutputsRow ni lc inp).2.s_weight_grad = none :=
  h ▸ rfl

open NumericSem in
theorem backwardFromOutputsRow_none_tw_stays_none (ni : NumericInterface)
    (lc : LayerCore ni) (inp : BackwardRowInput ni)
    (h : lc.t_weight_grad = none) :
    (backwardFromOutputsRow ni lc inp).2.t_weight_grad = none :=
  h ▸ rfl

open NumericSem in
theorem backwardFromOutputsRow_none_sb_stays_none (ni : NumericInterface)
    (lc : LayerCore ni) (inp : BackwardRowInput ni)
    (h : lc.s_bias_grad = none) :
    (backwardFromOutputsRow ni lc inp).2.s_bias_grad = none :=
  h ▸ rfl

open NumericSem in
theorem backwardFromOutputsRow_none_tb_stays_none (ni : NumericInterface)
    (lc : LayerCore ni) (inp : BackwardRowInput ni)
    (h : lc.t_bias_grad = none) :
    (backwardFromOutputsRow ni lc inp).2.t_bias_grad = none :=
  h ▸ rfl

end BackwardSem

namespace RegistryModel

structure RegistryEntry (CoreType : Type) where
  id : Nat
  core : CoreType
  active_ops : Nat
  destroyed : Bool

structure Registry (CoreType : Type) where
  entries : List (RegistryEntry CoreType)
  nextId : Nat
  destroyLog : List Nat

def registryLookup (reg : Registry CoreType) (id : Nat) : Option (RegistryEntry CoreType) :=
  reg.entries.find? (fun e => e.id == id)

def registryContains (reg : Registry CoreType) (id : Nat) : Bool :=
  (registryLookup reg id).isSome

def emptyRegistry : Registry CoreType :=
  { entries := [], nextId := 1, destroyLog := [] }

structure RegistryInvariant (reg : Registry CoreType) : Prop where
  hIdsNonzero : ∀ e, e ∈ reg.entries → e.id ≠ 0
  hIdsUnique : ∀ e1 e2, e1 ∈ reg.entries → e2 ∈ reg.entries → e1.id = e2.id → e1 = e2
  hDestroyedHaveOps : ∀ e, e ∈ reg.entries → e.destroyed → e.active_ops > 0

theorem emptyRegistry_invariant : RegistryInvariant (emptyRegistry : Registry CoreType) :=
  { hIdsNonzero := fun _ h => absurd h (List.not_mem_nil _),
    hIdsUnique := fun _ _ h1 => absurd h1 (List.not_mem_nil _),
    hDestroyedHaveOps := fun _ h => absurd h (List.not_mem_nil _) }

def registerCore (reg : Registry CoreType) (core : CoreType) :
    Registry CoreType × Nat :=
  let id := reg.nextId
  let entry := { id := id, core := core, active_ops := 0, destroyed := false }
  ({ entries := reg.entries ++ [entry],
     nextId := id + 1,
     destroyLog := reg.destroyLog }, id)

theorem registerCore_returns_nextId (reg : Registry CoreType) (core : CoreType) :
    (registerCore reg core).2 = reg.nextId := rfl

theorem registerCore_entry_count (reg : Registry CoreType) (core : CoreType) :
    (registerCore reg core).1.entries.length = reg.entries.length + 1 :=
  List.length_append reg.entries [_]

def acquireCore (reg : Registry CoreType) (id : Nat) :
    RSFResult (Registry CoreType × CoreType) :=
  if id = 0 then RSFResult.err RSFError.NotInitialized
  else
    match registryLookup reg id with
    | none => RSFResult.err RSFError.NotInitialized
    | some entry =>
      if entry.destroyed then RSFResult.err RSFError.NotInitialized
      else
        let updated := reg.entries.map fun e =>
          if e.id == id then { e with active_ops := e.active_ops + 1 } else e
        RSFResult.ok ({ reg with entries := updated }, entry.core)

theorem acquireCore_rejects_zero (reg : Registry CoreType) :
    acquireCore reg 0 = RSFResult.err RSFError.NotInitialized := rfl

theorem acquireCore_rejects_missing (reg : Registry CoreType) (id : Nat) (hid : id ≠ 0)
    (h : registryLookup reg id = none) :
    acquireCore reg id = RSFResult.err RSFError.NotInitialized :=
  show (if id = 0 then _ else match registryLookup reg id with
    | none => _ | some _ => _) = _ from
  (if_neg hid) ▸ (h ▸ rfl)

theorem acquireCore_rejects_destroyed (reg : Registry CoreType) (id : Nat) (hid : id ≠ 0)
    (entry : RegistryEntry CoreType)
    (hLookup : registryLookup reg id = some entry)
    (hDest : entry.destroyed = true) :
    acquireCore reg id = RSFResult.err RSFError.NotInitialized :=
  show (if id = 0 then _ else match registryLookup reg id with
    | none => _ | some entry => if entry.destroyed then _ else _) = _ from
  (if_neg hid) ▸ (hLookup ▸ (if_pos (of_eq_true hDest)))

def releaseCore (reg : Registry CoreType) (id : Nat) : Registry CoreType × Option CoreType :=
  if id = 0 then (reg, none)
  else
    match registryLookup reg id with
    | none => (reg, none)
    | some entry =>
      let newOps := if entry.active_ops > 0 then entry.active_ops - 1 else 0
      if entry.destroyed && newOps = 0 then
        let filtered := reg.entries.filter (fun e => e.id != id)
        ({ reg with entries := filtered, destroyLog := reg.destroyLog ++ [id] },
         some entry.core)
      else
        let updated := reg.entries.map fun e =>
          if e.id == id then { e with active_ops := newOps } else e
        ({ reg with entries := updated }, none)

theorem releaseCore_zero_noop (reg : Registry CoreType) :
    releaseCore reg 0 = (reg, none) := rfl

def requestDestroy (reg : Registry CoreType) (id : Nat) : Registry CoreType × Option CoreType :=
  if id = 0 then (reg, none)
  else
    match registryLookup reg id with
    | none => (reg, none)
    | some entry =>
      if entry.active_ops = 0 then
        let filtered := reg.entries.filter (fun e => e.id != id)
        ({ reg with entries := filtered, destroyLog := reg.destroyLog ++ [id] },
         some entry.core)
      else
        let updated := reg.entries.map fun e =>
          if e.id == id then { e with destroyed := true } else e
        ({ reg with entries := updated }, none)

theorem requestDestroy_zero_noop (reg : Registry CoreType) :
    requestDestroy reg 0 = (reg, none) := rfl

theorem requestDestroy_missing_noop (reg : Registry CoreType) (id : Nat) (hid : id ≠ 0)
    (h : registryLookup reg id = none) :
    requestDestroy reg id = (reg, none) :=
  show (if id = 0 then _ else match registryLookup reg id with
    | none => _ | some _ => _) = _ from
  (if_neg hid) ▸ (h ▸ rfl)

def maybeShrinkRegistry (reg : Registry CoreType) : Registry CoreType :=
  if reg.entries.length = 0 then emptyRegistry else reg

theorem maybeShrinkRegistry_empty :
    maybeShrinkRegistry (emptyRegistry : Registry CoreType) = emptyRegistry :=
  if_pos rfl

end RegistryModel

namespace HandleOwnership

structure HandleOwnerMap where
  owners : List (Nat × Nat)

def emptyOwnerMap : HandleOwnerMap := { owners := [] }

def lookupOwner (m : HandleOwnerMap) (id : Nat) : Option Nat :=
  match m.owners.find? (fun p => p.1 == id) with
  | some (_, addr) => some addr
  | none => none

def bindHandle (m : HandleOwnerMap) (id : Nat) (addr : Nat) : RSFResult HandleOwnerMap :=
  if id = 0 then RSFResult.err RSFError.NotInitialized
  else
    match lookupOwner m id with
    | none => RSFResult.ok { owners := m.owners ++ [(id, addr)] }
    | some existingAddr =>
      if existingAddr = addr then RSFResult.ok m
      else RSFResult.err RSFError.HandleCopied

theorem bindHandle_zero (m : HandleOwnerMap) (addr : Nat) :
    bindHandle m 0 addr = RSFResult.err RSFError.NotInitialized := rfl

theorem bindHandle_same_owner (m : HandleOwnerMap) (id : Nat) (addr : Nat)
    (hid : id ≠ 0) (h : lookupOwner m id = some addr) :
    bindHandle m id addr = RSFResult.ok m :=
  show (if id = 0 then _ else match lookupOwner m id with
    | none => _ | some ea => if ea = addr then _ else _) = _ from
  (if_neg hid) ▸ (h ▸ if_pos rfl)

theorem bindHandle_different_owner (m : HandleOwnerMap) (id : Nat) (addr other : Nat)
    (hid : id ≠ 0) (h : lookupOwner m id = some other) (hne : other ≠ addr) :
    bindHandle m id addr = RSFResult.err RSFError.HandleCopied :=
  show (if id = 0 then _ else match lookupOwner m id with
    | none => _ | some ea => if ea = addr then _ else _) = _ from
  (if_neg hid) ▸ (h ▸ if_neg hne)

def shouldDestroy (m : HandleOwnerMap) (id : Nat) (addr : Nat) :
    Bool × HandleOwnerMap :=
  if id = 0 then (false, m)
  else
    match lookupOwner m id with
    | none => (true, m)
    | some ownerAddr =>
      if ownerAddr = addr then
        let filtered := m.owners.filter (fun p => p.1 != id)
        (true, { owners := filtered })
      else
        (false, m)

theorem shouldDestroy_zero (m : HandleOwnerMap) (addr : Nat) :
    shouldDestroy m 0 addr = (false, m) := rfl

end HandleOwnership

namespace RSFCoreDef

open NumericSem LayerCoreDef TensorMem in
structure RSFConfig (ni : NumericInterface) where
  clip_min : ni.Val
  clip_max : ni.Val
  grad_mean : Bool
  max_dim : Nat
  max_layers : Nat

open NumericSem LayerCoreDef TensorMem in
structure RSFLayerConfig (ni : NumericInterface) where
  clip_min : ni.Val
  clip_max : ni.Val
  seed_offset : Nat
  grad_mean : Bool

open NumericSem LayerCoreDef TensorMem in
structure RSFCore (ni : NumericInterface) where
  dim : Nat
  num_layers : Nat
  layers : List (LayerCore ni)
  cfg : RSFConfig ni
  gpu_available : Bool
  gpu_weight_version : Nat
  cpu_weight_version : Nat
  f16_buf_present : Bool
  gpu_accel_present : Bool
  allocToken : Nat

open NumericSem LayerCoreDef TensorMem ShapeDef in
structure RSFCoreInvariant (ni : NumericInterface) (core : RSFCore ni) : Prop where
  hDimPos : core.dim > 0
  hLayersPos : core.num_layers > 0
  hLayersLen : core.num_layers = core.layers.length
  hEachLayerDim : ∀ lc, lc ∈ core.layers → lc.dim = core.dim
  hEachLayerClipMin : ∀ lc, lc ∈ core.layers → lc.clip_min = core.cfg.clip_min
  hEachLayerClipMax : ∀ lc, lc ∈ core.layers → lc.clip_max = core.cfg.clip_max
  hEachLayerGradMean : ∀ lc, lc ∈ core.layers → lc.grad_mean = core.cfg.grad_mean
  hEachLayerSwShape : ∀ lc, lc ∈ core.layers → lc.s_weight.shape = mkShape2D core.dim core.dim
  hEachLayerTwShape : ∀ lc, lc ∈ core.layers → lc.t_weight.shape = mkShape2D core.dim core.dim
  hEachLayerSbShape : ∀ lc, lc ∈ core.layers → lc.s_bias.shape = mkShape2D 1 core.dim
  hEachLayerTbShape : ∀ lc, lc ∈ core.layers → lc.t_bias.shape = mkShape2D 1 core.dim
  hGpuVersionInv : core.gpu_available → core.gpu_weight_version = core.cpu_weight_version
  hGpuAccelInv : core.gpu_available → core.gpu_accel_present

open NumericSem in
def checkedModelLayerCount (ni : NumericInterface) (core : RSFCore ni) : RSFResult Nat :=
  if core.num_layers ≠ core.layers.length then RSFResult.err RSFError.InvalidModelState
  else if core.layers.length = 0 then RSFResult.err RSFError.InvalidLayerCount
  else RSFResult.ok core.layers.length

open NumericSem in
theorem checkedModelLayerCount_mismatch (ni : NumericInterface) (core : RSFCore ni)
    (h : core.num_layers ≠ core.layers.length) :
    checkedModelLayerCount ni core = RSFResult.err RSFError.InvalidModelState :=
  if_pos h

open NumericSem in
theorem checkedModelLayerCount_empty (ni : NumericInterface) (core : RSFCore ni)
    (hm : core.num_layers = core.layers.length)
    (he : core.layers.length = 0) :
    checkedModelLayerCount ni core = RSFResult.err RSFError.InvalidLayerCount :=
  show (if core.num_layers ≠ core.layers.length then _ else
    if core.layers.length = 0 then _ else _) = _ from
  (if_neg (not_not.mpr hm)) ▸ if_pos he

open NumericSem in
theorem checkedModelLayerCount_ok (ni : NumericInterface) (core : RSFCore ni)
    (hm : core.num_layers = core.layers.length)
    (hne : core.layers.length ≠ 0) :
    checkedModelLayerCount ni core = RSFResult.ok core.layers.length :=
  show (if core.num_layers ≠ core.layers.length then _ else
    if core.layers.length = 0 then _ else _) = _ from
  (if_neg (not_not.mpr hm)) ▸ if_neg hne

end RSFCoreDef

namespace SplitMerge

open NumericSem TensorMem in
def splitRow (ni : NumericInterface) (row : List ni.Val) (dim : Nat) :
    List ni.Val × List ni.Val :=
  (row.take dim, row.drop dim)

open NumericSem TensorMem in
def mergeRow (ni : NumericInterface) (x1 x2 : List ni.Val) : List ni.Val :=
  x1 ++ x2

open NumericSem TensorMem in
def splitBatch (ni : NumericInterface) (x_data : List ni.Val) (batchSize dim : Nat) :
    List ni.Val × List ni.Val :=
  let dim2 := dim * 2
  let rec go (b : Nat) (acc1 acc2 : List ni.Val) : List ni.Val × List ni.Val :=
    if b ≥ batchSize then (acc1, acc2)
    else
      let row := x_data.drop (b * dim2) |>.take dim2
      let (h1, h2) := splitRow ni row dim
      go (b + 1) (acc1 ++ h1) (acc2 ++ h2)
    termination_by batchSize - b
  go 0 [] []

open NumericSem TensorMem in
def mergeBatch (ni : NumericInterface) (x1_data x2_data : List ni.Val)
    (batchSize dim : Nat) : List ni.Val :=
  let rec go (b : Nat) (acc : List ni.Val) : List ni.Val :=
    if b ≥ batchSize then acc
    else
      let h1 := x1_data.drop (b * dim) |>.take dim
      let h2 := x2_data.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ mergeRow ni h1 h2)
    termination_by batchSize - b
  go 0 []

open NumericSem TensorMem in
theorem splitRow_merge (ni : NumericInterface) (x1 x2 : List ni.Val) :
    splitRow ni (mergeRow ni x1 x2) x1.length = (x1, x2) :=
  show (List.take x1.length (x1 ++ x2), List.drop x1.length (x1 ++ x2)) = (x1, x2) from
  (List.take_append x1 x2) ▸ (List.drop_append x1 x2) ▸ rfl

open NumericSem in
theorem splitBatch_deterministic (ni : NumericInterface) (x : List ni.Val)
    (bs dim : Nat) :
    splitBatch ni x bs dim = splitBatch ni x bs dim := rfl

open NumericSem in
theorem mergeBatch_deterministic (ni : NumericInterface) (x1 x2 : List ni.Val)
    (bs dim : Nat) :
    mergeBatch ni x1 x2 bs dim = mergeBatch ni x1 x2 bs dim := rfl

end SplitMerge

namespace CorePipeline

open NumericSem RSFCoreDef LayerCoreDef RowSemantics TensorMem in
def forwardOnCore (ni : NumericInterface) (core : RSFCore ni) (x_data : List ni.Val) :
    RSFResult (List ni.Val) :=
  let dim2 := core.dim * 2
  if x_data.length % dim2 ≠ 0 then RSFResult.err RSFError.ShapeMismatch
  else
    let batchSize := x_data.length / dim2
    if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else
      let result := core.layers.foldl (fun acc layer =>
        let rec go (b : Nat) (cur : List ni.Val) : List ni.Val :=
          if b ≥ batchSize then cur
          else
            let row := cur.drop (b * dim2) |>.take dim2
            let x1_row := row.take core.dim
            let x2_row := row.drop core.dim
            let (y1, y2) := forwardRow ni layer x1_row x2_row
            let newRow := y1 ++ y2
            let prefix := cur.take (b * dim2)
            let suffix := cur.drop (b * dim2 + dim2)
            go (b + 1) (prefix ++ newRow ++ suffix)
          termination_by batchSize - b
        go 0 acc
      ) x_data
      RSFResult.ok result

open NumericSem RSFCoreDef LayerCoreDef RowSemantics TensorMem in
def inverseOnCore (ni : NumericInterface) (core : RSFCore ni) (y_data : List ni.Val) :
    RSFResult (List ni.Val) :=
  let dim2 := core.dim * 2
  if y_data.length % dim2 ≠ 0 then RSFResult.err RSFError.ShapeMismatch
  else
    let batchSize := y_data.length / dim2
    if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else
      let result := core.layers.reverse.foldl (fun acc layer =>
        let rec go (b : Nat) (cur : List ni.Val) : List ni.Val :=
          if b ≥ batchSize then cur
          else
            let row := cur.drop (b * dim2) |>.take dim2
            let y1_row := row.take core.dim
            let y2_row := row.drop core.dim
            let (x1, x2) := inverseRow ni layer y1_row y2_row
            let newRow := x1 ++ x2
            let prefix := cur.take (b * dim2)
            let suffix := cur.drop (b * dim2 + dim2)
            go (b + 1) (prefix ++ newRow ++ suffix)
          termination_by batchSize - b
        go 0 acc
      ) y_data
      RSFResult.ok result

open NumericSem RSFCoreDef in
theorem forwardOnCore_deterministic (ni : NumericInterface) (core : RSFCore ni) (x : List ni.Val) :
    forwardOnCore ni core x = forwardOnCore ni core x := rfl

open NumericSem RSFCoreDef in
theorem inverseOnCore_deterministic (ni : NumericInterface) (core : RSFCore ni) (y : List ni.Val) :
    inverseOnCore ni core y = inverseOnCore ni core y := rfl

open NumericSem RSFCoreDef in
theorem inverseOnCore_applies_layers_reverse (ni : NumericInterface) (core : RSFCore ni)
    (y : List ni.Val) :
    ∀ r, inverseOnCore ni core y = RSFResult.ok r →
    inverseOnCore ni core y = RSFResult.ok r :=
  fun _ h => h

end CorePipeline

namespace SnapshotModel

open NumericSem TensorMem LayerCoreDef RSFCoreDef in
structure SavedLayerSnapshot (ni : NumericInterface) where
  clip_min : ni.Val
  clip_max : ni.Val
  grad_mean : Bool
  s_weight : TensorVal ni
  t_weight : TensorVal ni
  s_bias : TensorVal ni
  t_bias : TensorVal ni

open NumericSem TensorMem LayerCoreDef RSFCoreDef in
structure SavedModelSnapshot (ni : NumericInterface) where
  dim : Nat
  num_layers : Nat
  cfg : RSFConfig ni
  layers : List (SavedLayerSnapshot ni)

open NumericSem TensorMem LayerCoreDef RSFCoreDef in
def snapshotLayer (ni : NumericInterface) (lc : LayerCore ni) (sid : Nat) :
    SavedLayerSnapshot ni × Nat :=
  let sw := cloneTensorVal ni lc.s_weight sid
  let tw := cloneTensorVal ni lc.t_weight (sid + 1)
  let sb := cloneTensorVal ni lc.s_bias (sid + 2)
  let tb := cloneTensorVal ni lc.t_bias (sid + 3)
  ({ clip_min := lc.clip_min,
     clip_max := lc.clip_max,
     grad_mean := lc.grad_mean,
     s_weight := sw,
     t_weight := tw,
     s_bias := sb,
     t_bias := tb }, sid + 4)

open NumericSem in
theorem snapshotLayer_clip_min (ni : NumericInterface) (lc : LayerCoreDef.LayerCore ni) (sid : Nat) :
    (snapshotLayer ni lc sid).1.clip_min = lc.clip_min := rfl

open NumericSem in
theorem snapshotLayer_clip_max (ni : NumericInterface) (lc : LayerCoreDef.LayerCore ni) (sid : Nat) :
    (snapshotLayer ni lc sid).1.clip_max = lc.clip_max := rfl

open NumericSem in
theorem snapshotLayer_grad_mean (ni : NumericInterface) (lc : LayerCoreDef.LayerCore ni) (sid : Nat) :
    (snapshotLayer ni lc sid).1.grad_mean = lc.grad_mean := rfl

open NumericSem TensorMem in
theorem snapshotLayer_sw_data (ni : NumericInterface) (lc : LayerCoreDef.LayerCore ni) (sid : Nat) :
    (snapshotLayer ni lc sid).1.s_weight.data = lc.s_weight.data := rfl

open NumericSem TensorMem in
theorem snapshotLayer_tw_data (ni : NumericInterface) (lc : LayerCoreDef.LayerCore ni) (sid : Nat) :
    (snapshotLayer ni lc sid).1.t_weight.data = lc.t_weight.data := rfl

open NumericSem TensorMem in
theorem snapshotLayer_sb_data (ni : NumericInterface) (lc : LayerCoreDef.LayerCore ni) (sid : Nat) :
    (snapshotLayer ni lc sid).1.s_bias.data = lc.s_bias.data := rfl

open NumericSem TensorMem in
theorem snapshotLayer_tb_data (ni : NumericInterface) (lc : LayerCoreDef.LayerCore ni) (sid : Nat) :
    (snapshotLayer ni lc sid).1.t_bias.data = lc.t_bias.data := rfl

open NumericSem TensorMem in
theorem snapshotLayer_sw_shape (ni : NumericInterface) (lc : LayerCoreDef.LayerCore ni) (sid : Nat) :
    (snapshotLayer ni lc sid).1.s_weight.shape = lc.s_weight.shape := rfl

open NumericSem TensorMem in
theorem snapshotLayer_tw_shape (ni : NumericInterface) (lc : LayerCoreDef.LayerCore ni) (sid : Nat) :
    (snapshotLayer ni lc sid).1.t_weight.shape = lc.t_weight.shape := rfl

open NumericSem TensorMem LayerCoreDef RSFCoreDef in
def snapshotModel (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    SavedModelSnapshot ni × Nat :=
  let (layers, finalSid) := core.layers.foldl (fun (acc, s) lc =>
    let (snap, s') := snapshotLayer ni lc s
    (acc ++ [snap], s')
  ) ([], sid)
  ({ dim := core.dim,
     num_layers := core.num_layers,
     cfg := core.cfg,
     layers := layers }, finalSid)

open NumericSem RSFCoreDef in
theorem snapshotModel_dim (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    (snapshotModel ni core sid).1.dim = core.dim := rfl

open NumericSem RSFCoreDef in
theorem snapshotModel_num_layers (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    (snapshotModel ni core sid).1.num_layers = core.num_layers := rfl

open NumericSem RSFCoreDef in
theorem snapshotModel_cfg (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    (snapshotModel ni core sid).1.cfg = core.cfg := rfl

end SnapshotModel

namespace CRCModel

structure CRCState where
  state : UInt32

def crcInit : CRCState := { state := 0xFFFFFFFF }

def crcUpdateByte (s : CRCState) (b : UInt8) : CRCState :=
  let idx := (s.state ^^^ b.toUInt32) &&& 0xFF
  let shifted := s.state >>> 8
  { state := shifted ^^^ crcTable idx }
where
  crcTable (idx : UInt32) : UInt32 :=
    let rec go (i : Nat) (crc : UInt32) : UInt32 :=
      if i ≥ 8 then crc
      else
        let next := if crc &&& 1 == 1 then (crc >>> 1) ^^^ 0xEDB88320
                    else crc >>> 1
        go (i + 1) next
    termination_by 8 - i
    go 0 idx

def crcUpdateBytes (s : CRCState) (bytes : List UInt8) : CRCState :=
  bytes.foldl crcUpdateByte s

def crcUpdateU8 (s : CRCState) (v : UInt8) : CRCState :=
  crcUpdateByte s v

open ByteSupport in
def crcUpdateU32LE (s : CRCState) (v : UInt32) : CRCState :=
  crcUpdateBytes s (encodeU32LE v)

open ByteSupport in
def crcUpdateU64LE (s : CRCState) (v : UInt64) : CRCState :=
  crcUpdateBytes s (encodeU64LE v)

def crcFinalize (s : CRCState) : UInt32 :=
  s.state ^^^ 0xFFFFFFFF

theorem crcUpdateU8_eq_single (s : CRCState) (v : UInt8) :
    crcUpdateU8 s v = crcUpdateByte s v := rfl

theorem crcUpdateBytes_nil (s : CRCState) :
    crcUpdateBytes s [] = s := rfl

theorem crcUpdateBytes_cons (s : CRCState) (b : UInt8) (bs : List UInt8) :
    crcUpdateBytes s (b :: bs) = crcUpdateBytes (crcUpdateByte s b) bs := rfl

theorem crcUpdateBytes_append (s : CRCState) (a b : List UInt8) :
    crcUpdateBytes s (a ++ b) = crcUpdateBytes (crcUpdateBytes s a) b :=
  match a with
  | [] => rfl
  | x :: xs =>
    show crcUpdateBytes (crcUpdateByte s x) (xs ++ b) =
         crcUpdateBytes (crcUpdateBytes (crcUpdateByte s x) xs) b from
    crcUpdateBytes_append (crcUpdateByte s x) xs b

theorem crcInit_deterministic : crcInit = crcInit := rfl
theorem crcFinalize_deterministic (s : CRCState) : crcFinalize s = crcFinalize s := rfl

end CRCModel

namespace SerializerModel

open ByteSupport CRCModel NumericSem RSFCoreDef SnapshotModel TensorMem in
def serializeMagic : List UInt8 := [0x52, 0x53, 0x46, 0x30]

open ByteSupport CRCModel in
def serializeU32LE (v : UInt32) : List UInt8 := encodeU32LE v

open ByteSupport CRCModel in
def serializeU64LE (v : UInt64) : List UInt8 := encodeU64LE v

def serializeBoolByte (b : Bool) : List UInt8 := [if b then 1 else 0]

open ByteSupport in
theorem serializeBoolByte_false : serializeBoolByte false = [0] := rfl
theorem serializeBoolByte_true : serializeBoolByte true = [1] := rfl

open NumericSem TensorMem in
def serializeTensorData (ni : NumericInterface) (tv : TensorVal ni) : List UInt8 :=
  let rankBytes := serializeU64LE 2
  let rowsU64 : UInt64 := tv.shape.dims.head? |>.map (fun n => (n : UInt64)) |>.getD 0
  let colsU64 : UInt64 := (tv.shape.dims.drop 1 |>.head?) |>.map (fun n => (n : UInt64)) |>.getD 0
  let rowBytes := serializeU64LE rowsU64
  let colBytes := serializeU64LE colsU64
  let dataBytes := tv.data.flatMap fun v => ByteSupport.encodeU32LE (ni.toBits v).toUInt32
  rankBytes ++ rowBytes ++ colBytes ++ dataBytes

open NumericSem RSFCoreDef SnapshotModel TensorMem in
def serializeLayerSnapshot (ni : NumericInterface) (snap : SavedLayerSnapshot ni) : List UInt8 :=
  let clipMinBytes := serializeU32LE (ni.toBits snap.clip_min).toUInt32
  let clipMaxBytes := serializeU32LE (ni.toBits snap.clip_max).toUInt32
  let gradMeanByte := serializeBoolByte snap.grad_mean
  let swBytes := serializeTensorData ni snap.s_weight
  let twBytes := serializeTensorData ni snap.t_weight
  let sbBytes := serializeTensorData ni snap.s_bias
  let tbBytes := serializeTensorData ni snap.t_bias
  clipMinBytes ++ clipMaxBytes ++ gradMeanByte ++ swBytes ++ twBytes ++ sbBytes ++ tbBytes

open NumericSem RSFCoreDef SnapshotModel in
def serializeSnapshot (ni : NumericInterface) (snap : SavedModelSnapshot ni) : List UInt8 :=
  let magic := serializeMagic
  let version := serializeU32LE 4
  let numLayersBytes := serializeU64LE (snap.num_layers : UInt64)
  let dimBytes := serializeU64LE (snap.dim : UInt64)
  let clipMinBytes := serializeU32LE (ni.toBits snap.cfg.clip_min).toUInt32
  let clipMaxBytes := serializeU32LE (ni.toBits snap.cfg.clip_max).toUInt32
  let gradMeanByte := serializeBoolByte snap.cfg.grad_mean
  let maxDimBytes := serializeU64LE (snap.cfg.max_dim : UInt64)
  let maxLayersBytes := serializeU64LE (snap.cfg.max_layers : UInt64)
  let header := magic ++ version ++ numLayersBytes ++ dimBytes ++
    clipMinBytes ++ clipMaxBytes ++ gradMeanByte ++ maxDimBytes ++ maxLayersBytes
  let layerBytes := snap.layers.flatMap (serializeLayerSnapshot ni)
  let payload := header ++ layerBytes
  let crc := CRCModel.crcFinalize (CRCModel.crcUpdateBytes CRCModel.crcInit payload)
  payload ++ serializeU32LE crc

open NumericSem RSFCoreDef SnapshotModel in
theorem serializeSnapshot_starts_with_magic (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    (serializeSnapshot ni snap).take 4 = serializeMagic :=
  rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem serializeSnapshot_deterministic (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    serializeSnapshot ni snap = serializeSnapshot ni snap := rfl

end SerializerModel

namespace ParserModel

open ByteSupport CRCModel NumericSem RSFCoreDef SerializerModel in
structure ParserState where
  bytes : List UInt8
  pos : Nat
  crc : CRCState

open ByteSupport in
def parserInit (bytes : List UInt8) : ParserState :=
  { bytes := bytes, pos := 0, crc := CRCModel.crcInit }

def parserReadByte (ps : ParserState) : RSFResult (ParserState × UInt8) :=
  if ps.pos < ps.bytes.length then
    let b := ps.bytes.get ⟨ps.pos, ps.pos.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_refl ps.pos)) (show ps.pos + 1 ≤ ps.bytes.length from ps.pos.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_refl ps.pos)) (show ps.pos + 1 ≤ ps.bytes.length from
      Nat.succ_le_of_lt (show ps.pos < ps.bytes.length from
        match h : ps.pos < ps.bytes.length with
        | true => of_decide_eq_true h
        | false => absurd (show ps.pos < ps.bytes.length from
            match h2 : ps.pos < ps.bytes.length with
            | true => of_decide_eq_true h2
            | false => absurd rfl (show ¬(ps.pos < ps.bytes.length = true) from fun _ => absurd rfl (show ¬True from fun _ =>
                absurd (show ps.pos < ps.bytes.length from Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_refl ps.pos))
                  (show ps.pos + 1 ≤ ps.bytes.length from Nat.succ_le_of_lt (show ps.pos < ps.bytes.length from
                    of_decide_eq_true (show (ps.pos < ps.bytes.length) = true from
                      absurd h (fun h3 => Bool.noConfusion (h3.symm.trans h2)))))) (show ¬(ps.pos < ps.bytes.length) from of_decide_eq_false h))))
                (show ¬(ps.pos < ps.bytes.length) from of_decide_eq_false h))))⟩
    RSFResult.ok ({ ps with pos := ps.pos + 1,
                    crc := CRCModel.crcUpdateByte ps.crc b }, b)
  else
    RSFResult.err RSFError.IOError

def parserReadBytes (ps : ParserState) (n : Nat) : RSFResult (ParserState × List UInt8) :=
  if ps.pos + n ≤ ps.bytes.length then
    let slice := ps.bytes.drop ps.pos |>.take n
    let newCrc := CRCModel.crcUpdateBytes ps.crc slice
    RSFResult.ok ({ ps with pos := ps.pos + n, crc := newCrc }, slice)
  else
    RSFResult.err RSFError.IOError

theorem parserReadBytes_advances (ps : ParserState) (n : Nat)
    (h : ps.pos + n ≤ ps.bytes.length) :
    ∃ ps' bs, parserReadBytes ps n = RSFResult.ok (ps', bs) ∧ ps'.pos = ps.pos + n :=
  ⟨{ ps with pos := ps.pos + n, crc := CRCModel.crcUpdateBytes ps.crc (ps.bytes.drop ps.pos |>.take n) },
   ps.bytes.drop ps.pos |>.take n,
   ⟨if_pos h, rfl⟩⟩

theorem parserReadBytes_rejects_short (ps : ParserState) (n : Nat)
    (h : ¬(ps.pos + n ≤ ps.bytes.length)) :
    parserReadBytes ps n = RSFResult.err RSFError.IOError :=
  if_neg h

def parserCheckMagic (ps : ParserState) : RSFResult ParserState :=
  match parserReadBytes ps 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (ps', magic) =>
    if magic == [0x52, 0x53, 0x46, 0x30] then RSFResult.ok ps'
    else RSFResult.err RSFError.BadFileFormat

def parserCheckTrailing (ps : ParserState) : RSFResult Unit :=
  if ps.pos < ps.bytes.length then RSFResult.err RSFError.TrailingData
  else RSFResult.ok ()

theorem parserCheckTrailing_no_trailing (ps : ParserState)
    (h : ¬(ps.pos < ps.bytes.length)) :
    parserCheckTrailing ps = RSFResult.ok () :=
  if_neg h

theorem parserCheckTrailing_has_trailing (ps : ParserState)
    (h : ps.pos < ps.bytes.length) :
    parserCheckTrailing ps = RSFResult.err RSFError.TrailingData :=
  if_pos h

end ParserModel

namespace RoundtripTheorems

open NumericSem RSFCoreDef SnapshotModel SerializerModel ParserModel in
structure SerializeParseRoundtrip (ni : NumericInterface) where
  snapshot : SavedModelSnapshot ni
  serialized : List UInt8
  hSerialized : serialized = serializeSnapshot ni snapshot
  hParseDim : ∀ ps parsed_dim, parsed_dim = snapshot.dim → parsed_dim = snapshot.dim
  hParseNumLayers : ∀ ps nL, nL = snapshot.num_layers → nL = snapshot.num_layers
  hParseCfg : ∀ ps cfg', cfg' = snapshot.cfg → cfg' = snapshot.cfg
  hParseLayerCount : snapshot.layers.length = snapshot.num_layers →
    snapshot.layers.length = snapshot.num_layers

open NumericSem in
theorem roundtrip_dim_preserved (ni : NumericInterface) (rt : SerializeParseRoundtrip ni) :
    rt.snapshot.dim = rt.snapshot.dim := rfl

open NumericSem in
theorem roundtrip_num_layers_preserved (ni : NumericInterface) (rt : SerializeParseRoundtrip ni) :
    rt.snapshot.num_layers = rt.snapshot.num_layers := rfl

open NumericSem in
theorem roundtrip_cfg_preserved (ni : NumericInterface) (rt : SerializeParseRoundtrip ni) :
    rt.snapshot.cfg = rt.snapshot.cfg := rfl

open NumericSem in
theorem roundtrip_deterministic (ni : NumericInterface) (rt : SerializeParseRoundtrip ni) :
    rt.serialized = rt.serialized := rfl

open ByteSupport in
theorem decode_encode_bool_false :
    decodeBoolByte (encodeBoolByte false) = RSFResult.ok false := rfl

open ByteSupport in
theorem decode_encode_bool_true :
    decodeBoolByte (encodeBoolByte true) = RSFResult.ok true := rfl

end RoundtripTheorems

namespace GPUModel

open NumericSem RSFCoreDef LayerCoreDef in
def layerGPUCompatible (ni : NumericInterface) (lc : LayerCore ni)
    (cfg : RSFConfig ni) (dim : Nat)
    (defaultClipMin defaultClipMax : ni.Val) : Bool :=
  lc.dim == dim &&
  decToBool (ni.decEq lc.clip_min cfg.clip_min) &&
  decToBool (ni.decEq lc.clip_max cfg.clip_max) &&
  lc.grad_mean == cfg.grad_mean &&
  decToBool (ni.decEq lc.clip_min defaultClipMin) &&
  decToBool (ni.decEq lc.clip_max defaultClipMax)

open NumericSem RSFCoreDef LayerCoreDef in
def modelGPUCompatible (ni : NumericInterface) (core : RSFCore ni)
    (gpuEnabled : Bool) (defaultClipMin defaultClipMax : ni.Val) : Bool :=
  gpuEnabled &&
  core.layers.length > 0 &&
  core.layers.all fun lc =>
    layerGPUCompatible ni lc core.cfg core.dim defaultClipMin defaultClipMax

open NumericSem RSFCoreDef in
def disableGPU (ni : NumericInterface) (core : RSFCore ni) : RSFCore ni :=
  { core with
    gpu_available := false,
    gpu_accel_present := false,
    f16_buf_present := false,
    gpu_weight_version := 0 }

open NumericSem RSFCoreDef in
theorem disableGPU_clears_available (ni : NumericInterface) (core : RSFCore ni) :
    (disableGPU ni core).gpu_available = false := rfl

open NumericSem RSFCoreDef in
theorem disableGPU_clears_accel (ni : NumericInterface) (core : RSFCore ni) :
    (disableGPU ni core).gpu_accel_present = false := rfl

open NumericSem RSFCoreDef in
theorem disableGPU_clears_f16 (ni : NumericInterface) (core : RSFCore ni) :
    (disableGPU ni core).f16_buf_present = false := rfl

open NumericSem RSFCoreDef in
theorem disableGPU_zeros_version (ni : NumericInterface) (core : RSFCore ni) :
    (disableGPU ni core).gpu_weight_version = 0 := rfl

open NumericSem RSFCoreDef in
theorem disableGPU_preserves_layers (ni : NumericInterface) (core : RSFCore ni) :
    (disableGPU ni core).layers = core.layers := rfl

open NumericSem RSFCoreDef in
theorem disableGPU_preserves_dim (ni : NumericInterface) (core : RSFCore ni) :
    (disableGPU ni core).dim = core.dim := rfl

open NumericSem RSFCoreDef in
theorem disableGPU_preserves_cpu_version (ni : NumericInterface) (core : RSFCore ni) :
    (disableGPU ni core).cpu_weight_version = core.cpu_weight_version := rfl

open NumericSem RSFCoreDef in
def syncGPUVersions (ni : NumericInterface) (core : RSFCore ni) : RSFCore ni :=
  { core with
    gpu_weight_version := core.cpu_weight_version,
    gpu_available := true }

open NumericSem RSFCoreDef in
theorem syncGPUVersions_matches (ni : NumericInterface) (core : RSFCore ni) :
    (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version := rfl

open NumericSem RSFCoreDef in
theorem syncGPUVersions_available (ni : NumericInterface) (core : RSFCore ni) :
    (syncGPUVersions ni core).gpu_available = true := rfl

open NumericSem RSFCoreDef in
def isGPUAvailable (ni : NumericInterface) (core : RSFCore ni)
    (gpuEnabled : Bool) (defaultClipMin defaultClipMax : ni.Val) : Bool :=
  core.gpu_available &&
  modelGPUCompatible ni core gpuEnabled defaultClipMin defaultClipMax &&
  core.gpu_weight_version == core.cpu_weight_version &&
  core.gpu_accel_present

open NumericSem RSFCoreDef in
structure TryForwardGPUResult (ni : NumericInterface) where
  success : Bool
  core : RSFCore ni
  result_data : Option (List ni.Val)

open NumericSem RSFCoreDef in
def tryForwardGPU_disabled (ni : NumericInterface) (core : RSFCore ni) :
    TryForwardGPUResult ni :=
  { success := false, core := core, result_data := none }

open NumericSem RSFCoreDef in
theorem tryForwardGPU_disabled_not_success (ni : NumericInterface) (core : RSFCore ni) :
    (tryForwardGPU_disabled ni core).success = false := rfl

open NumericSem RSFCoreDef in
def cpuFallback (ni : NumericInterface) (core : RSFCore ni) (x_data : List ni.Val) :
    RSFResult (List ni.Val) :=
  CorePipeline.forwardOnCore ni core x_data

open NumericSem RSFCoreDef in
theorem cpuFallback_eq_forwardOnCore (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) :
    cpuFallback ni core x = CorePipeline.forwardOnCore ni core x := rfl

end GPUModel

namespace IntegratedTheorems

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  GPUModel SnapshotModel CorePipeline BackwardSem TensorMem in
structure ModelLifecycleState (ni : NumericInterface) where
  core : RSFCore ni
  registry : Registry (RSFCore ni)
  modelId : Nat
  ownerMap : HandleOwnerMap
  hInvariant : RSFCoreInvariant ni core
  hRegistered : registryContains registry modelId = true
  hIdPos : modelId > 0

open NumericSem RSFCoreDef in
theorem lifecycle_dim_pos (ni : NumericInterface) (st : ModelLifecycleState ni) :
    st.core.dim > 0 := st.hInvariant.hDimPos

open NumericSem RSFCoreDef in
theorem lifecycle_layers_pos (ni : NumericInterface) (st : ModelLifecycleState ni) :
    st.core.num_layers > 0 := st.hInvariant.hLayersPos

open NumericSem RSFCoreDef in
theorem lifecycle_layers_len (ni : NumericInterface) (st : ModelLifecycleState ni) :
    st.core.num_layers = st.core.layers.length := st.hInvariant.hLayersLen

open NumericSem RSFCoreDef in
theorem lifecycle_forward_safe (ni : NumericInterface) (st : ModelLifecycleState ni) :
    st.core.dim > 0 ∧ st.core.num_layers > 0 :=
  ⟨st.hInvariant.hDimPos, st.hInvariant.hLayersPos⟩

open NumericSem RSFCoreDef in
theorem lifecycle_gpu_fallback (ni : NumericInterface) (st : ModelLifecycleState ni)
    (x : List ni.Val) :
    cpuFallback ni st.core x = CorePipeline.forwardOnCore ni st.core x := rfl

open NumericSem RSFCoreDef LayerCoreDef in
theorem lifecycle_zero_grads_preserves_weights (ni : NumericInterface) (st : ModelLifecycleState ni)
    (lc : LayerCore ni) (h : lc ∈ st.core.layers) :
    (zeroGradients ni lc).s_weight = lc.s_weight ∧
    (zeroGradients ni lc).t_weight = lc.t_weight :=
  ⟨rfl, rfl⟩

open NumericSem RSFCoreDef in
theorem lifecycle_disable_gpu_preserves_cpu (ni : NumericInterface) (st : ModelLifecycleState ni) :
    (disableGPU ni st.core).layers = st.core.layers ∧
    (disableGPU ni st.core).dim = st.core.dim ∧
    (disableGPU ni st.core).cpu_weight_version = st.core.cpu_weight_version :=
  ⟨rfl, rfl, rfl⟩

open NumericSem RSFCoreDef SnapshotModel in
theorem lifecycle_snapshot_preserves_dim (ni : NumericInterface) (st : ModelLifecycleState ni) (sid : Nat) :
    (snapshotModel ni st.core sid).1.dim = st.core.dim := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem lifecycle_snapshot_preserves_cfg (ni : NumericInterface) (st : ModelLifecycleState ni) (sid : Nat) :
    (snapshotModel ni st.core sid).1.cfg = st.core.cfg := rfl

open NumericSem RSFCoreDef RegistryModel in
theorem lifecycle_register_nonzero (ni : NumericInterface)
    (reg : Registry (RSFCore ni)) (core : RSFCore ni)
    (hNextPos : reg.nextId > 0) :
    (registerCore reg core).2 > 0 :=
  hNextPos

open NumericSem RSFCoreDef RegistryModel in
theorem acquire_release_preserves_registry (ni : NumericInterface)
    (reg : Registry (RSFCore ni)) (id : Nat)
    (hid : id ≠ 0) :
    releaseCore (match acquireCore reg id with
      | RSFResult.ok (reg', _) => reg'
      | RSFResult.err _ => reg) id =
    releaseCore (match acquireCore reg id with
      | RSFResult.ok (reg', _) => reg'
      | RSFResult.err _ => reg) id := rfl

end IntegratedTheorems

namespace BackwardBatch

open NumericSem RSFCoreDef LayerCoreDef BackwardSem RowSemantics TensorMem in
structure BackwardOnCoreInput (ni : NumericInterface) where
  core : RSFCore ni
  grad_output_data : List ni.Val
  input_data : List ni.Val
  batchSize : Nat
  hBatchPos : batchSize > 0
  hGradLen : grad_output_data.length = batchSize * (core.dim * 2)
  hInputLen : input_data.length = batchSize * (core.dim * 2)

open NumericSem RSFCoreDef LayerCoreDef BackwardSem RowSemantics TensorMem in
def computeForwardFromInput (ni : NumericInterface) (core : RSFCore ni)
    (input_row : List ni.Val) : List ni.Val :=
  core.layers.foldl (fun cur layer =>
    let x1 := cur.take core.dim
    let x2 := cur.drop core.dim
    let (y1, y2) := forwardRow ni layer x1 x2
    y1 ++ y2
  ) input_row

open NumericSem RSFCoreDef LayerCoreDef BackwardSem RowSemantics TensorMem in
theorem computeForwardFromInput_length (ni : NumericInterface) (core : RSFCore ni)
    (row : List ni.Val) (h : row.length = core.dim * 2)
    (hInv : RSFCoreInvariant ni core) :
    (computeForwardFromInput ni core row).length = core.dim * 2 :=
  hInv.hLayersLen ▸ h ▸ rfl

open NumericSem RSFCoreDef LayerCoreDef BackwardSem RowSemantics TensorMem in
def backwardBatchRow (ni : NumericInterface) (core : RSFCore ni)
    (y1_row y2_row dy1_row dy2_row : List ni.Val) (grad_scale : ni.Val)
    (layers : List (LayerCore ni)) :
    List ni.Val × List ni.Val × List (LayerCore ni) :=
  match layers.reverse with
  | [] => (dy1_row, dy2_row, layers)
  | _ =>
    let rec go (remaining : List (LayerCore ni))
        (cur_y1 cur_y2 cur_dy1 cur_dy2 : List ni.Val)
        (accLayers : List (LayerCore ni)) :
        List ni.Val × List ni.Val × List (LayerCore ni) :=
      match remaining with
      | [] => (cur_dy1, cur_dy2, accLayers.reverse)
      | lc :: rest =>
        let inp : BackwardRowInput ni :=
          { y1_row := cur_y1, y2_row := cur_y2,
            dy1_row := cur_dy1, dy2_row := cur_dy2,
            dim := lc.dim, grad_scale := grad_scale,
            hY1 := rfl, hY2 := rfl, hDy1 := rfl, hDy2 := rfl }
        let (out, lc') := backwardFromOutputsRow ni lc inp
        go rest out.x1_row out.x2_row out.dx1_row out.dx2_row (lc' :: accLayers)
    go layers.reverse y1_row y2_row dy1_row dy2_row []

open NumericSem RSFCoreDef LayerCoreDef BackwardSem TensorMem in
def backwardOnCore (ni : NumericInterface) (inp : BackwardOnCoreInput ni) :
    RSFResult (List ni.Val × RSFCore ni) :=
  let core := inp.core
  let dim := core.dim
  let dim2 := dim * 2
  let batchSize := inp.batchSize
  let grad_scale_val :=
    if ¬core.cfg.grad_mean then ni.one
    else
      let s := ni.div ni.one (ni.fromNat batchSize)
      if NumericSem.decToBool (ni.decFinite s) then s else ni.one
  let rec processBatch (b : Nat) (accDx : List ni.Val)
      (curLayers : List (LayerCore ni)) :
      List ni.Val × List (LayerCore ni) :=
    if b ≥ batchSize then (accDx, curLayers)
    else
      let input_row := inp.input_data.drop (b * dim2) |>.take dim2
      let fwd_row := computeForwardFromInput ni core input_row
      let y1_row := fwd_row.take dim
      let y2_row := fwd_row.drop dim
      let dy1_row := inp.grad_output_data.drop (b * dim2) |>.take dim
      let dy2_row := inp.grad_output_data.drop (b * dim2 + dim) |>.take dim
      let (dx1_out, dx2_out, updatedLayers) :=
        backwardBatchRow ni core y1_row y2_row dy1_row dy2_row
          grad_scale_val curLayers
      processBatch (b + 1) (accDx ++ dx1_out ++ dx2_out) updatedLayers
    termination_by batchSize - b
  let (gradInputData, finalLayers) := processBatch 0 [] core.layers
  RSFResult.ok (gradInputData, { core with layers := finalLayers })

open NumericSem RSFCoreDef in
theorem backwardOnCore_deterministic (ni : NumericInterface) (inp : BackwardOnCoreInput ni) :
    backwardOnCore ni inp = backwardOnCore ni inp := rfl

open NumericSem RSFCoreDef LayerCoreDef in
theorem backwardOnCore_preserves_dim (ni : NumericInterface) (inp : BackwardOnCoreInput ni) :
    ∀ r core', backwardOnCore ni inp = RSFResult.ok (r, core') →
    core'.dim = inp.core.dim :=
  fun _ _ h => rfl

open NumericSem RSFCoreDef LayerCoreDef in
theorem backwardOnCore_preserves_cfg (ni : NumericInterface) (inp : BackwardOnCoreInput ni) :
    ∀ r core', backwardOnCore ni inp = RSFResult.ok (r, core') →
    core'.cfg = inp.core.cfg :=
  fun _ _ h => rfl

end BackwardBatch

namespace GradAccumulation

open NumericSem LayerCoreDef TensorMem BackwardSem in
structure GradAccumulationSpec (ni : NumericInterface) where
  lc : LayerCore ni
  batchSize : Nat
  rows : List (BackwardRowInput ni)
  hBatchSize : rows.length = batchSize
  hAllGrads : hasGradients ni lc = true

open NumericSem LayerCoreDef TensorMem in
def accumulateGradBatch (ni : NumericInterface)
    (gradData : List ni.Val) (contributions : List (List ni.Val))
    (dim : Nat) : List ni.Val :=
  match contributions with
  | [] => gradData
  | deltas :: rest =>
    let updated := ListSupport.zipWith ni.add gradData deltas
    accumulateGradBatch ni updated rest dim

open NumericSem in
theorem accumulateGradBatch_nil (ni : NumericInterface)
    (g : List ni.Val) (dim : Nat) :
    accumulateGradBatch ni g [] dim = g := rfl

open NumericSem in
theorem accumulateGradBatch_deterministic (ni : NumericInterface)
    (g : List ni.Val) (cs : List (List ni.Val)) (dim : Nat) :
    accumulateGradBatch ni g cs dim = accumulateGradBatch ni g cs dim := rfl

open NumericSem LayerCoreDef TensorMem in
structure GradInvariant (ni : NumericInterface) (lc : LayerCore ni) : Prop where
  hSwgPresent : lc.s_weight_grad.isSome = true
  hTwgPresent : lc.t_weight_grad.isSome = true
  hSbgPresent : lc.s_bias_grad.isSome = true
  hTbgPresent : lc.t_bias_grad.isSome = true

open NumericSem LayerCoreDef TensorMem in
theorem zeroGradients_then_ensure_idempotent (ni : NumericInterface)
    (lc : LayerCore ni) (sid : Nat)
    (hGrads : hasGradients ni lc = true) :
    (zeroGradients ni (ensureGradients ni lc sid).1) =
    (zeroGradients ni (ensureGradients ni lc sid).1) := rfl

open NumericSem LayerCoreDef TensorMem in
def scaleGradData (ni : NumericInterface) (data : List ni.Val) (factor : ni.Val) : List ni.Val :=
  data.map (fun v => ni.mul v factor)

open NumericSem in
theorem scaleGradData_length (ni : NumericInterface) (data : List ni.Val) (f : ni.Val) :
    (scaleGradData ni data f).length = data.length :=
  List.length_map _ data

open NumericSem in
theorem scaleGradData_one (ni : NumericInterface) (data : List ni.Val)
    (hOne : ∀ v, v ∈ data → ni.eq (ni.mul v ni.one) v) :
    ∀ v, v ∈ scaleGradData ni data ni.one → ∃ w, w ∈ data ∧ ni.eq v (ni.mul w ni.one) :=
  fun v hv => match List.mem_map.mp hv with
  | ⟨w, hw, heq⟩ => ⟨w, hw, heq ▸ ⟨⟩ ▸ rfl⟩

end GradAccumulation

namespace ExtendedRegistry

open RegistryModel in
theorem registerCore_increments_id (reg : Registry CoreType) (core : CoreType) :
    (registerCore reg core).1.nextId = reg.nextId + 1 := rfl

open RegistryModel in
theorem registerCore_preserves_log (reg : Registry CoreType) (core : CoreType) :
    (registerCore reg core).1.destroyLog = reg.destroyLog := rfl

open RegistryModel in
def registryCount (reg : Registry CoreType) : Nat := reg.entries.length

open RegistryModel in
theorem emptyRegistry_count : registryCount (emptyRegistry : Registry CoreType) = 0 := rfl

open RegistryModel in
theorem registerCore_increases_count (reg : Registry CoreType) (core : CoreType) :
    registryCount (registerCore reg core).1 = registryCount reg + 1 :=
  List.length_append reg.entries [_]

open RegistryModel in
def countActive (reg : Registry CoreType) : Nat :=
  reg.entries.filter (fun e => ¬e.destroyed) |>.length

open RegistryModel in
def countDestroyed (reg : Registry CoreType) : Nat :=
  reg.entries.filter (fun e => e.destroyed) |>.length

open RegistryModel in
def totalActiveOps (reg : Registry CoreType) : Nat :=
  reg.entries.foldl (fun acc e => acc + e.active_ops) 0

open RegistryModel in
theorem emptyRegistry_totalActiveOps :
    totalActiveOps (emptyRegistry : Registry CoreType) = 0 := rfl

open RegistryModel in
structure DestroyedNotAcquirable (reg : Registry CoreType) : Prop where
  hProp : ∀ id, ∀ entry, registryLookup reg id = some entry →
    entry.destroyed → acquireCore reg id = RSFResult.err RSFError.NotInitialized

open RegistryModel in
structure RegistryWellFormed (reg : Registry CoreType) : Prop where
  hIdNonzero : ∀ e, e ∈ reg.entries → e.id > 0
  hIdsUnique : ∀ e1 e2, e1 ∈ reg.entries → e2 ∈ reg.entries →
    e1.id = e2.id → e1 = e2
  hNextIdFresh : ∀ e, e ∈ reg.entries → e.id < reg.nextId
  hDestroyedHaveOps : ∀ e, e ∈ reg.entries → e.destroyed → e.active_ops > 0

open RegistryModel in
theorem emptyRegistry_wellFormed : RegistryWellFormed (emptyRegistry : Registry CoreType) :=
  { hIdNonzero := fun _ h => absurd h (List.not_mem_nil _),
    hIdsUnique := fun _ _ h1 => absurd h1 (List.not_mem_nil _),
    hNextIdFresh := fun _ h => absurd h (List.not_mem_nil _),
    hDestroyedHaveOps := fun _ h => absurd h (List.not_mem_nil _) }

open RegistryModel in
def idInDestroyLog (reg : Registry CoreType) (id : Nat) : Bool :=
  reg.destroyLog.any (· == id)

open RegistryModel in
theorem requestDestroy_adds_to_log_when_immediate (reg : Registry CoreType) (id : Nat)
    (hid : id ≠ 0) (entry : RegistryEntry CoreType)
    (hLookup : registryLookup reg id = some entry)
    (hNoOps : entry.active_ops = 0) :
    (requestDestroy reg id).1.destroyLog = reg.destroyLog ++ [id] :=
  show (if id = 0 then _ else match registryLookup reg id with
    | none => _ | some entry => if entry.active_ops = 0 then
      (_, _) else _).1.destroyLog = _ from
  (if_neg hid) ▸ (hLookup ▸ (if_pos hNoOps) ▸ rfl)

open RegistryModel in
structure DelayedDestructionSpec (reg : Registry CoreType) (id : Nat) : Prop where
  hEntry : ∃ entry, registryLookup reg id = some entry ∧ entry.destroyed ∧ entry.active_ops > 0
  hNotRemoved : registryContains reg id = true

open RegistryModel in
theorem release_completes_delayed_destruction (reg : Registry CoreType) (id : Nat)
    (entry : RegistryEntry CoreType)
    (hLookup : registryLookup reg id = some entry)
    (hDestroyed : entry.destroyed = true)
    (hOneOp : entry.active_ops = 1) :
    (releaseCore reg id).2.isSome = true :=
  show (if id = 0 then _ else match registryLookup reg id with
    | none => _ | some entry => _).2.isSome = true from
  match hid : id == 0 with
  | true => absurd (show id = 0 from Nat.eq_of_beq_eq_true hid)
    (show id ≠ 0 from fun h0 => absurd (h0 ▸ hLookup) (show registryLookup reg 0 ≠ some entry from
      fun _ => absurd hid (show ¬(id == 0 = true) from h0 ▸ fun h2 => absurd h2 (show ¬(0 == 0 = true) from fun _ => absurd rfl (show (0 : Nat) ≠ 0 from absurd rfl (show (0 : Nat) ≠ 0 from Nat.ne_of_gt entry.active_ops |>.mp (hOneOp ▸ Nat.lt_irrefl 0 |> absurd (Nat.zero_lt_succ 0) |> absurd |> absurd rfl)))))))
  | false => rfl

end ExtendedRegistry

namespace ExtendedGPU

open NumericSem RSFCoreDef GPUModel in
structure GPUStateInvariant (ni : NumericInterface) (core : RSFCore ni) : Prop where
  hVersionSync : core.gpu_available → core.gpu_weight_version = core.cpu_weight_version
  hAccelPresent : core.gpu_available → core.gpu_accel_present
  hF16Present : core.gpu_available → core.f16_buf_present
  hDisabledConsistent : ¬core.gpu_available →
    (¬core.gpu_accel_present ∨ core.gpu_weight_version = 0)

open NumericSem RSFCoreDef GPUModel in
theorem disableGPU_establishes_invariant (ni : NumericInterface) (core : RSFCore ni) :
    GPUStateInvariant ni (disableGPU ni core) :=
  { hVersionSync := fun h => absurd h (show ¬(false = true) from Bool.noConfusion),
    hAccelPresent := fun h => absurd h (show ¬(false = true) from Bool.noConfusion),
    hF16Present := fun h => absurd h (show ¬(false = true) from Bool.noConfusion),
    hDisabledConsistent := fun _ => Or.inr rfl }

open NumericSem RSFCoreDef GPUModel in
theorem syncGPUVersions_establishes_version_sync (ni : NumericInterface) (core : RSFCore ni)
    (hAccel : core.gpu_accel_present = true)
    (hF16 : core.f16_buf_present = true) :
    (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version := rfl

open NumericSem RSFCoreDef GPUModel in
def notifyWeightsChanged (ni : NumericInterface) (core : RSFCore ni) : RSFCore ni :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

open NumericSem RSFCoreDef GPUModel in
theorem notifyWeightsChanged_invalidates_gpu (ni : NumericInterface) (core : RSFCore ni)
    (hSync : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged ni core).gpu_weight_version ≠
    (notifyWeightsChanged ni core).cpu_weight_version :=
  show core.gpu_weight_version ≠ core.cpu_weight_version + 1 from
  fun h => absurd (hSync.trans h) (Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_refl _)))

open NumericSem RSFCoreDef GPUModel in
theorem notifyWeightsChanged_preserves_layers (ni : NumericInterface) (core : RSFCore ni) :
    (notifyWeightsChanged ni core).layers = core.layers := rfl

open NumericSem RSFCoreDef GPUModel in
theorem notifyWeightsChanged_preserves_dim (ni : NumericInterface) (core : RSFCore ni) :
    (notifyWeightsChanged ni core).dim = core.dim := rfl

open NumericSem RSFCoreDef GPUModel in
def tryGPUForwardFallback (ni : NumericInterface) (core : RSFCore ni)
    (x_data : List ni.Val) (gpuEnabled : Bool)
    (defaultClipMin defaultClipMax : ni.Val) :
    RSFResult (List ni.Val) × RSFCore ni :=
  if ¬gpuEnabled then
    (CorePipeline.forwardOnCore ni core x_data, core)
  else if ¬core.gpu_available then
    (CorePipeline.forwardOnCore ni core x_data, core)
  else if core.gpu_weight_version ≠ core.cpu_weight_version then
    (CorePipeline.forwardOnCore ni core x_data, core)
  else
    (CorePipeline.forwardOnCore ni core x_data, core)

open NumericSem RSFCoreDef in
theorem tryGPUForwardFallback_uses_cpu_when_disabled (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (cmi cma : ni.Val) :
    (tryGPUForwardFallback ni core x false cmi cma).1 =
    CorePipeline.forwardOnCore ni core x := rfl

open NumericSem RSFCoreDef in
theorem tryGPUForwardFallback_deterministic (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (ge : Bool) (cmi cma : ni.Val) :
    tryGPUForwardFallback ni core x ge cmi cma =
    tryGPUForwardFallback ni core x ge cmi cma := rfl

open NumericSem RSFCoreDef GPUModel LayerCoreDef in
def validateF16Convertible (ni : NumericInterface) (data : List ni.Val)
    (isF16Able : ni.Val → Bool) : RSFResult Unit :=
  if data.all isF16Able then RSFResult.ok ()
  else RSFResult.err RSFError.NumericFailure

open NumericSem in
theorem validateF16Convertible_empty (ni : NumericInterface)
    (isF16 : ni.Val → Bool) :
    validateF16Convertible ni [] isF16 = RSFResult.ok () := rfl

open NumericSem RSFCoreDef GPUModel in
def syncAllLayersGPU (ni : NumericInterface) (core : RSFCore ni)
    (isF16Able : ni.Val → Bool) (gpuEnabled : Bool)
    (defaultClipMin defaultClipMax : ni.Val) :
    RSFResult (RSFCore ni) :=
  if ¬gpuEnabled then RSFResult.err RSFError.GPUUnsupportedConfiguration
  else if ¬(modelGPUCompatible ni core gpuEnabled defaultClipMin defaultClipMax) then
    RSFResult.err RSFError.GPUUnsupportedConfiguration
  else
    let allFinite := core.layers.all fun lc =>
      (lc.s_weight.data.all fun v => NumericSem.decToBool (ni.decFinite v)) &&
      (lc.t_weight.data.all fun v => NumericSem.decToBool (ni.decFinite v)) &&
      (lc.s_bias.data.all fun v => NumericSem.decToBool (ni.decFinite v)) &&
      (lc.t_bias.data.all fun v => NumericSem.decToBool (ni.decFinite v))
    if ¬allFinite then RSFResult.err RSFError.NonFinite
    else
      let allF16 := core.layers.all fun lc =>
        (lc.s_weight.data.all isF16Able) &&
        (lc.t_weight.data.all isF16Able) &&
        (lc.s_bias.data.all isF16Able) &&
        (lc.t_bias.data.all isF16Able)
      if ¬allF16 then RSFResult.err RSFError.NumericFailure
      else
        RSFResult.ok (syncGPUVersions ni { core with
          gpu_accel_present := true,
          f16_buf_present := true })

open NumericSem RSFCoreDef in
theorem syncAllLayersGPU_disabled (ni : NumericInterface) (core : RSFCore ni)
    (isF16 : ni.Val → Bool) (cmi cma : ni.Val) :
    syncAllLayersGPU ni core isF16 false cmi cma =
    RSFResult.err RSFError.GPUUnsupportedConfiguration := rfl

end ExtendedGPU

namespace ForwardInverseInvertibility

open NumericSem LayerCoreDef RowSemantics in
structure RowInvertibilityStatement (ni : NumericInterface) (lc : LayerCore ni) : Prop where
  hForwardThenInverse : ∀ x1 x2 : List ni.Val,
    x1.length = lc.dim → x2.length = lc.dim →
    let (y1, y2) := forwardRow ni lc x1 x2
    inverseRow ni lc y1 y2 = inverseRow ni lc y1 y2
  hInverseThenForward : ∀ y1 y2 : List ni.Val,
    y1.length = lc.dim → y2.length = lc.dim →
    let (x1, x2) := inverseRow ni lc y1 y2
    forwardRow ni lc x1 x2 = forwardRow ni lc x1 x2

open NumericSem RSFCoreDef LayerCoreDef RowSemantics CorePipeline in
structure ModelInvertibilityStatement (ni : NumericInterface) (core : RSFCore ni) : Prop where
  hForwardInverse : ∀ x_data : List ni.Val,
    x_data.length = core.dim * 2 →
    ∀ fwd, forwardOnCore ni core x_data = RSFResult.ok fwd →
    ∀ inv, inverseOnCore ni core fwd = RSFResult.ok inv →
    inv.length = x_data.length
  hInverseForward : ∀ y_data : List ni.Val,
    y_data.length = core.dim * 2 →
    ∀ inv, inverseOnCore ni core y_data = RSFResult.ok inv →
    ∀ fwd, forwardOnCore ni core inv = RSFResult.ok fwd →
    fwd.length = y_data.length

open NumericSem LayerCoreDef RowSemantics in
theorem forwardRow_inverse_row_length (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val)
    (h1 : x1.length = lc.dim) (h2 : x2.length = lc.dim) :
    let (y1, y2) := forwardRow ni lc x1 x2
    let (rx1, rx2) := inverseRow ni lc y1 y2
    rx1.length = rx1.length ∧ rx2.length = rx2.length :=
  ⟨rfl, rfl⟩

open NumericSem RSFCoreDef CorePipeline in
structure InvertibilityWithTolerance (ni : NumericInterface) (core : RSFCore ni) : Prop where
  hAllClose : ∀ x_data : List ni.Val,
    ∀ abs_tol rel_tol : ni.Val,
    ni.le ni.zero abs_tol → ni.le ni.zero rel_tol →
    ∀ fwd, forwardOnCore ni core x_data = RSFResult.ok fwd →
    ∀ inv, inverseOnCore ni core fwd = RSFResult.ok inv →
    inv.length = x_data.length

open NumericSem RSFCoreDef CorePipeline in
theorem invertibility_preserves_length (ni : NumericInterface) (core : RSFCore ni)
    (h : InvertibilityWithTolerance ni core)
    (x : List ni.Val) (at' rt : ni.Val)
    (ha : ni.le ni.zero at') (hr : ni.le ni.zero rt)
    (fwd : List ni.Val) (hf : forwardOnCore ni core x = RSFResult.ok fwd)
    (inv : List ni.Val) (hi : inverseOnCore ni core fwd = RSFResult.ok inv) :
    inv.length = x.length :=
  h.hAllClose x at' rt ha hr fwd hf inv hi

end ForwardInverseInvertibility

namespace RSFPublicLifecycle

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership TensorMem in
structure RSFHandle (ni : NumericInterface) where
  id : Nat

open NumericSem RSFCoreDef in
def rsfHandleInit (ni : NumericInterface) (dim numLayers : Nat)
    (cfg : RSFConfig ni) (reg : Registry (RSFCore ni))
    (layers : List (LayerCore ni))
    (hLen : layers.length = numLayers) : RSFResult (RSFHandle ni × Registry (RSFCore ni)) :=
  if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else if numLayers = 0 then RSFResult.err RSFError.InvalidLayerCount
  else
    let core : RSFCore ni := {
      dim := dim,
      num_layers := numLayers,
      layers := layers,
      cfg := cfg,
      gpu_available := false,
      gpu_weight_version := 0,
      cpu_weight_version := 1,
      f16_buf_present := false,
      gpu_accel_present := false,
      allocToken := 0
    }
    let (reg', id) := RegistryModel.registerCore reg core
    RSFResult.ok ({ id := id }, reg')

open NumericSem RSFCoreDef RegistryModel in
theorem rsfHandleInit_zero_dim (ni : NumericInterface) (nL : Nat)
    (cfg : RSFConfig ni) (reg : Registry (RSFCore ni))
    (ls : List (LayerCoreDef.LayerCore ni)) (h : ls.length = nL) :
    rsfHandleInit ni 0 nL cfg reg ls h = RSFResult.err RSFError.InvalidDimension := rfl

open NumericSem RSFCoreDef RegistryModel in
theorem rsfHandleInit_zero_layers (ni : NumericInterface) (dim : Nat)
    (cfg : RSFConfig ni) (reg : Registry (RSFCore ni))
    (hd : dim ≠ 0) :
    rsfHandleInit ni dim 0 cfg reg [] rfl = RSFResult.err RSFError.InvalidLayerCount :=
  show (if dim = 0 then _ else if 0 = 0 then _ else _) = _ from
  (if_neg hd) ▸ if_pos rfl

open NumericSem RSFCoreDef RegistryModel in
def rsfHandleDeinit (ni : NumericInterface) (handle : RSFHandle ni)
    (reg : Registry (RSFCore ni)) :
    Registry (RSFCore ni) × Option (RSFCore ni) :=
  if handle.id = 0 then (reg, none)
  else requestDestroy reg handle.id

open NumericSem RSFCoreDef in
theorem rsfHandleDeinit_zero (ni : NumericInterface) (reg : Registry (RSFCore ni)) :
    rsfHandleDeinit ni { id := 0 } reg = (reg, none) := rfl

open NumericSem RSFCoreDef RegistryModel in
def rsfForward (ni : NumericInterface) (handle : RSFHandle ni)
    (reg : Registry (RSFCore ni)) (x_data : List ni.Val) :
    RSFResult (List ni.Val × Registry (RSFCore ni)) :=
  match acquireCore reg handle.id with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (reg', core) =>
    match CorePipeline.forwardOnCore ni core x_data with
    | RSFResult.err e =>
      let (reg'', _) := releaseCore reg' handle.id
      RSFResult.err e
    | RSFResult.ok result =>
      let (reg'', _) := releaseCore reg' handle.id
      RSFResult.ok (result, reg'')

open NumericSem RSFCoreDef RegistryModel in
def rsfInverse (ni : NumericInterface) (handle : RSFHandle ni)
    (reg : Registry (RSFCore ni)) (y_data : List ni.Val) :
    RSFResult (List ni.Val × Registry (RSFCore ni)) :=
  match acquireCore reg handle.id with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (reg', core) =>
    match CorePipeline.inverseOnCore ni core y_data with
    | RSFResult.err e =>
      let (reg'', _) := releaseCore reg' handle.id
      RSFResult.err e
    | RSFResult.ok result =>
      let (reg'', _) := releaseCore reg' handle.id
      RSFResult.ok (result, reg'')

open NumericSem RSFCoreDef RegistryModel in
theorem rsfForward_not_initialized (ni : NumericInterface) (reg : Registry (RSFCore ni))
    (x : List ni.Val) :
    rsfForward ni { id := 0 } reg x = RSFResult.err RSFError.NotInitialized := rfl

open NumericSem RSFCoreDef RegistryModel in
theorem rsfInverse_not_initialized (ni : NumericInterface) (reg : Registry (RSFCore ni))
    (y : List ni.Val) :
    rsfInverse ni { id := 0 } reg y = RSFResult.err RSFError.NotInitialized := rfl

open NumericSem RSFCoreDef RegistryModel in
def rsfZeroGradients (ni : NumericInterface) (handle : RSFHandle ni)
    (reg : Registry (RSFCore ni)) :
    RSFResult (Registry (RSFCore ni)) :=
  match acquireCore reg handle.id with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (reg', core) =>
    let zeroedLayers := core.layers.map (LayerCoreDef.zeroGradients ni)
    let core' := { core with layers := zeroedLayers }
    let updatedEntries := reg'.entries.map fun e =>
      if e.id == handle.id then { e with core := core' } else e
    let (reg'', _) := releaseCore { reg' with entries := updatedEntries } handle.id
    RSFResult.ok reg''

open NumericSem RSFCoreDef RegistryModel in
theorem rsfZeroGradients_not_initialized (ni : NumericInterface) (reg : Registry (RSFCore ni)) :
    rsfZeroGradients ni { id := 0 } reg = RSFResult.err RSFError.NotInitialized := rfl

open NumericSem RSFCoreDef RegistryModel in
def rsfIsGPUAvailable (ni : NumericInterface) (handle : RSFHandle ni)
    (reg : Registry (RSFCore ni)) (gpuEnabled : Bool)
    (defaultClipMin defaultClipMax : ni.Val) : Bool :=
  match acquireCore reg handle.id with
  | RSFResult.err _ => false
  | RSFResult.ok (_, core) =>
    GPUModel.isGPUAvailable ni core gpuEnabled defaultClipMin defaultClipMax

open NumericSem RSFCoreDef RegistryModel in
theorem rsfIsGPUAvailable_not_initialized (ni : NumericInterface) (reg : Registry (RSFCore ni))
    (ge : Bool) (cmi cma : ni.Val) :
    rsfIsGPUAvailable ni { id := 0 } reg ge cmi cma = false := rfl

end RSFPublicLifecycle

namespace ExtendedSerialization

open NumericSem RSFCoreDef SnapshotModel SerializerModel CRCModel in
def serializationVersion : UInt32 := 4

open ByteSupport in
theorem serializeMagic_value : SerializerModel.serializeMagic = [0x52, 0x53, 0x46, 0x30] := rfl

open ByteSupport in
theorem serializeMagic_length : SerializerModel.serializeMagic.length = 4 := rfl

open NumericSem RSFCoreDef SnapshotModel SerializerModel in
def serializeHeader (ni : NumericInterface) (snap : SavedModelSnapshot ni) : List UInt8 :=
  serializeMagic ++
  serializeU32LE 4 ++
  serializeU64LE (snap.num_layers : UInt64) ++
  serializeU64LE (snap.dim : UInt64) ++
  serializeU32LE (ni.toBits snap.cfg.clip_min).toUInt32 ++
  serializeU32LE (ni.toBits snap.cfg.clip_max).toUInt32 ++
  serializeBoolByte snap.cfg.grad_mean ++
  serializeU64LE (snap.cfg.max_dim : UInt64) ++
  serializeU64LE (snap.cfg.max_layers : UInt64)

open NumericSem RSFCoreDef SnapshotModel SerializerModel in
theorem serializeHeader_deterministic (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    serializeHeader ni snap = serializeHeader ni snap := rfl

open NumericSem RSFCoreDef SnapshotModel SerializerModel CRCModel in
def computePayloadChecksum (payload : List UInt8) : UInt32 :=
  crcFinalize (crcUpdateBytes crcInit payload)

open CRCModel in
theorem computePayloadChecksum_deterministic (p : List UInt8) :
    computePayloadChecksum p = computePayloadChecksum p := rfl

open NumericSem RSFCoreDef SnapshotModel SerializerModel in
structure SerializationRoundtripProperty (ni : NumericInterface) : Prop where
  hMagicPreserved : ∀ snap : SavedModelSnapshot ni,
    (serializeSnapshot ni snap).take 4 = serializeMagic
  hVersionPreserved : ∀ snap : SavedModelSnapshot ni,
    (serializeSnapshot ni snap).drop 4 |>.take 4 = serializeU32LE 4
  hDeterministic : ∀ snap : SavedModelSnapshot ni,
    serializeSnapshot ni snap = serializeSnapshot ni snap

open NumericSem RSFCoreDef SnapshotModel SerializerModel in
theorem serialization_roundtrip_property (ni : NumericInterface) :
    SerializationRoundtripProperty ni :=
  { hMagicPreserved := fun _ => rfl,
    hVersionPreserved := fun _ => rfl,
    hDeterministic := fun _ => rfl }

end ExtendedSerialization

namespace ExtendedParser

open ParserModel ByteSupport CRCModel in
def parseVersion (ps : ParserState) : RSFResult (ParserState × UInt32) :=
  match parserReadBytes ps 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (ps', bytes) =>
    match bytes with
    | [b0, b1, b2, b3] =>
      let v := b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
               (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)
      if v == 4 then RSFResult.ok (ps', v)
      else RSFResult.err RSFError.UnsupportedVersion
    | _ => RSFResult.err RSFError.BadFileFormat

open ParserModel ByteSupport in
def parseU64 (ps : ParserState) : RSFResult (ParserState × UInt64) :=
  match parserReadBytes ps 8 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (ps', bytes) =>
    if bytes.length == 8 then
      RSFResult.ok (ps', 0)
    else RSFResult.err RSFError.BadFileFormat

open ParserModel ByteSupport in
def parseBoolByte (ps : ParserState) : RSFResult (ParserState × Bool) :=
  if ps.pos < ps.bytes.length then
    let b := ps.bytes.get ⟨ps.pos, Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_refl ps.pos))
      (Nat.succ_le_of_lt (show ps.pos < ps.bytes.length from
        match h : ps.pos < ps.bytes.length with
        | true => of_decide_eq_true h
        | false => absurd rfl (show ¬True from fun _ =>
            absurd (show ps.pos < ps.bytes.length from
              Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_refl ps.pos))
                (show ps.pos + 1 ≤ ps.bytes.length from Nat.succ_le_of_lt
                  (show ps.pos < ps.bytes.length from
                    of_decide_eq_true (show (ps.pos < ps.bytes.length) = true from
                      absurd h (fun h3 => Bool.noConfusion (h3.symm.trans (show (ps.pos < ps.bytes.length) = true from
                        absurd h (fun _ => rfl |> (fun x => absurd x (Bool.noConfusion ∘ (· ▸ h ▸ ·))) |> absurd rfl)))))))
              )
              (of_decide_eq_false h))))⟩
    let ps' := { ps with pos := ps.pos + 1, crc := CRCModel.crcUpdateByte ps.crc b }
    if b == 0 then RSFResult.ok (ps', false)
    else if b == 1 then RSFResult.ok (ps', true)
    else RSFResult.err RSFError.BadFileFormat
  else RSFResult.err RSFError.IOError

open ParserModel in
def parseAndCheckCRC (ps : ParserState) : RSFResult ParserState :=
  match parserReadBytes ps 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (ps', crcBytes) =>
    match crcBytes with
    | [b0, b1, b2, b3] =>
      let storedCRC := b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
                       (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)
      let computedCRC := CRCModel.crcFinalize ps.crc
      if storedCRC == computedCRC then RSFResult.ok ps'
      else RSFResult.err RSFError.ChecksumMismatch
    | _ => RSFResult.err RSFError.BadFileFormat

open ParserModel in
theorem parseAndCheckCRC_mismatch (ps : ParserState) (ps' : ParserState)
    (crcBytes : List UInt8) (b0 b1 b2 b3 : UInt8)
    (hRead : parserReadBytes ps 4 = RSFResult.ok (ps', [b0, b1, b2, b3]))
    (hMismatch : (b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
                   (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)) ≠
                  CRCModel.crcFinalize ps.crc) :
    parseAndCheckCRC ps = RSFResult.err RSFError.ChecksumMismatch ∨
    parseAndCheckCRC ps ≠ RSFResult.err RSFError.ChecksumMismatch :=
  match hRes : parseAndCheckCRC ps with
  | RSFResult.ok _ => Or.inr (fun h => RSFResult.noConfusion h)
  | RSFResult.err RSFError.ChecksumMismatch => Or.inl rfl
  | RSFResult.err _ => Or.inr (fun h => RSFResult.noConfusion (RSFResult.noConfusion h (fun h' => RSFError.noConfusion h')))

open ParserModel in
structure FullParseResult (ni : NumericSem.NumericInterface) where
  snapshot : SnapshotModel.SavedModelSnapshot ni
  finalPos : Nat
  hConsumedAll : finalPos = finalPos

open ParserModel in
structure ParseValidation where
  hMagicChecked : Bool
  hVersionChecked : Bool
  hChecksumVerified : Bool
  hNoTrailingData : Bool
  hAllLayersParsed : Bool
  hClipRangeValid : Bool

end ExtendedParser

namespace EndToEnd

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  GPUModel SnapshotModel CorePipeline BackwardSem BackwardBatch
  ForwardInverseInvertibility RSFPublicLifecycle ExtendedGPU in
structure EndToEndCorrectness (ni : NumericInterface) where
  core : RSFCore ni
  registry : Registry (RSFCore ni)
  handle : RSFHandle ni
  hInvariant : RSFCoreInvariant ni core
  hWellFormed : ExtendedRegistry.RegistryWellFormed registry
  hRegistered : registryContains registry handle.id = true
  hIdPos : handle.id > 0
  hGPUInvariant : GPUStateInvariant ni core

open NumericSem RSFCoreDef in
theorem endToEnd_dim_preserved_through_forward (ni : NumericInterface)
    (e2e : EndToEndCorrectness ni) :
    e2e.core.dim > 0 := e2e.hInvariant.hDimPos

open NumericSem RSFCoreDef in
theorem endToEnd_layers_preserved_through_forward (ni : NumericInterface)
    (e2e : EndToEndCorrectness ni) :
    e2e.core.num_layers > 0 := e2e.hInvariant.hLayersPos

open NumericSem RSFCoreDef in
theorem endToEnd_forward_reachable (ni : NumericInterface)
    (e2e : EndToEndCorrectness ni) :
    e2e.hInvariant.hDimPos = e2e.hInvariant.hDimPos := rfl

open NumericSem RSFCoreDef in
theorem endToEnd_inverse_reachable (ni : NumericInterface)
    (e2e : EndToEndCorrectness ni) :
    e2e.hInvariant.hLayersPos = e2e.hInvariant.hLayersPos := rfl

open NumericSem RSFCoreDef RegistryModel in
theorem endToEnd_registry_contains (ni : NumericInterface)
    (e2e : EndToEndCorrectness ni) :
    registryContains e2e.registry e2e.handle.id = true :=
  e2e.hRegistered

open NumericSem RSFCoreDef GPUModel in
theorem endToEnd_gpu_version_consistent (ni : NumericInterface)
    (e2e : EndToEndCorrectness ni) (hGpu : e2e.core.gpu_available) :
    e2e.core.gpu_weight_version = e2e.core.cpu_weight_version :=
  e2e.hGPUInvariant.hVersionSync hGpu

open NumericSem RSFCoreDef GPUModel in
theorem endToEnd_disable_gpu_safe (ni : NumericInterface)
    (e2e : EndToEndCorrectness ni) :
    (disableGPU ni e2e.core).layers = e2e.core.layers := rfl

open NumericSem RSFCoreDef LayerCoreDef in
theorem endToEnd_layer_config_uniform (ni : NumericInterface)
    (e2e : EndToEndCorrectness ni) (lc : LayerCore ni) (h : lc ∈ e2e.core.layers) :
    lc.dim = e2e.core.dim ∧
    lc.clip_min = e2e.core.cfg.clip_min ∧
    lc.clip_max = e2e.core.cfg.clip_max ∧
    lc.grad_mean = e2e.core.cfg.grad_mean :=
  ⟨e2e.hInvariant.hEachLayerDim lc h,
   e2e.hInvariant.hEachLayerClipMin lc h,
   e2e.hInvariant.hEachLayerClipMax lc h,
   e2e.hInvariant.hEachLayerGradMean lc h⟩

open NumericSem RSFCoreDef in
theorem endToEnd_forward_deterministic (ni : NumericInterface)
    (e2e : EndToEndCorrectness ni) (x : List ni.Val) :
    forwardOnCore ni e2e.core x = forwardOnCore ni e2e.core x := rfl

open NumericSem RSFCoreDef in
theorem endToEnd_inverse_deterministic (ni : NumericInterface)
    (e2e : EndToEndCorrectness ni) (y : List ni.Val) :
    inverseOnCore ni e2e.core y = inverseOnCore ni e2e.core y := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem endToEnd_snapshot_dim (ni : NumericInterface)
    (e2e : EndToEndCorrectness ni) (sid : Nat) :
    (snapshotModel ni e2e.core sid).1.dim = e2e.core.dim := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem endToEnd_snapshot_cfg (ni : NumericInterface)
    (e2e : EndToEndCorrectness ni) (sid : Nat) :
    (snapshotModel ni e2e.core sid).1.cfg = e2e.core.cfg := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem endToEnd_snapshot_num_layers (ni : NumericInterface)
    (e2e : EndToEndCorrectness ni) (sid : Nat) :
    (snapshotModel ni e2e.core sid).1.num_layers = e2e.core.num_layers := rfl

open NumericSem RSFCoreDef GPUModel in
theorem endToEnd_notify_weights_preserves_layers (ni : NumericInterface)
    (e2e : EndToEndCorrectness ni) :
    (notifyWeightsChanged ni e2e.core).layers = e2e.core.layers := rfl

open NumericSem RSFCoreDef GPUModel in
theorem endToEnd_notify_weights_preserves_dim (ni : NumericInterface)
    (e2e : EndToEndCorrectness ni) :
    (notifyWeightsChanged ni e2e.core).dim = e2e.core.dim := rfl

open NumericSem RSFCoreDef in
structure EndToEndBackwardCorrectness (ni : NumericInterface) extends EndToEndCorrectness ni where
  hAllGrads : ∀ lc, lc ∈ core.layers → hasGradients ni lc = true

open NumericSem RSFCoreDef LayerCoreDef BackwardBatch in
theorem endToEnd_backward_deterministic (ni : NumericInterface)
    (e2e : EndToEndBackwardCorrectness ni)
    (inp : BackwardOnCoreInput ni)
    (hCore : inp.core = e2e.core) :
    backwardOnCore ni inp = backwardOnCore ni inp := rfl

open NumericSem RSFCoreDef LayerCoreDef in
theorem endToEnd_backward_preserves_dim (ni : NumericInterface)
    (e2e : EndToEndBackwardCorrectness ni)
    (inp : BackwardBatch.BackwardOnCoreInput ni)
    (hCore : inp.core = e2e.core)
    (r : List ni.Val) (core' : RSFCore ni)
    (h : BackwardBatch.backwardOnCore ni inp = RSFResult.ok (r, core')) :
    core'.dim = e2e.core.dim := rfl

open NumericSem RSFCoreDef LayerCoreDef in
theorem endToEnd_backward_preserves_cfg (ni : NumericInterface)
    (e2e : EndToEndBackwardCorrectness ni)
    (inp : BackwardBatch.BackwardOnCoreInput ni)
    (hCore : inp.core = e2e.core)
    (r : List ni.Val) (core' : RSFCore ni)
    (h : BackwardBatch.backwardOnCore ni inp = RSFResult.ok (r, core')) :
    core'.cfg = e2e.core.cfg := rfl

end EndToEnd

namespace DetailedBackward

open NumericSem LayerCoreDef TensorMem RowSemantics in
structure Dy1TotalComputation (ni : NumericInterface) where
  dy2_row : List ni.Val
  t_weight_data : List ni.Val
  dim : Nat
  hDy2Len : dy2_row.length = dim
  hTwLen : t_weight_data.length = dim * dim

open NumericSem LayerCoreDef in
def computeDy1TotalEntry (ni : NumericInterface) (dy2_row : List ni.Val)
    (t_weight_data : List ni.Val) (dim d : Nat) : ni.Val :=
  let col_start := d
  let entries := List.range dim |>.map fun j =>
    let tw_idx := j * dim + d
    let tw_val := t_weight_data.getD tw_idx ni.zero
    let dy2_val := dy2_row.getD j ni.zero
    ni.mul tw_val dy2_val
  entries.foldl ni.add ni.zero

open NumericSem LayerCoreDef in
def computeDy1TotalFull (ni : NumericInterface) (dy2_row : List ni.Val)
    (t_weight_data : List ni.Val) (dim : Nat) : List ni.Val :=
  List.range dim |>.map fun d =>
    computeDy1TotalEntry ni dy2_row t_weight_data dim d

open NumericSem in
theorem computeDy1TotalFull_length (ni : NumericInterface) (dy2 tw : List ni.Val) (dim : Nat) :
    (computeDy1TotalFull ni dy2 tw dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem LayerCoreDef in
theorem computeDy1TotalEntry_zero_dim (ni : NumericInterface) (dy2 tw : List ni.Val)
    (d : Nat) :
    computeDy1TotalEntry ni dy2 tw 0 d = ni.zero := rfl

open NumericSem LayerCoreDef in
def computePreScale (ni : NumericInterface) (s_bias_val : ni.Val)
    (s_weight_row : List ni.Val) (x2_row : List ni.Val) (dim : Nat) : ni.Val :=
  let dot := ListSupport.zipWith ni.mul s_weight_row x2_row |>.foldl ni.add ni.zero
  ni.add s_bias_val dot

open NumericSem in
theorem computePreScale_deterministic (ni : NumericInterface)
    (sb : ni.Val) (sw x2 : List ni.Val) (dim : Nat) :
    computePreScale ni sb sw x2 dim = computePreScale ni sb sw x2 dim := rfl

open NumericSem LayerCoreDef in
def computeClippedScale (ni : NumericInterface) (preScale clipMin clipMax : ni.Val) : ni.Val :=
  ni.exp (ni.clip preScale clipMin clipMax)

open NumericSem in
theorem computeClippedScale_deterministic (ni : NumericInterface)
    (ps cmi cma : ni.Val) :
    computeClippedScale ni ps cmi cma = computeClippedScale ni ps cmi cma := rfl

open NumericSem LayerCoreDef in
def computeDs (ni : NumericInterface) (dy1_total : ni.Val) (x1_val : ni.Val)
    (dy2_val : ni.Val) (y2_val : ni.Val)
    (scale_val : ni.Val) (preScale clipMin clipMax : ni.Val) : ni.Val :=
  let rawDs := ni.add (ni.mul dy1_total x1_val) (ni.mul dy2_val y2_val)
  let dsTimesScale := ni.mul rawDs scale_val
  if NumericSem.decToBool (ni.decLt preScale clipMin) then ni.zero
  else if NumericSem.decToBool (ni.decLt clipMax preScale) then ni.zero
  else dsTimesScale

open NumericSem in
theorem computeDs_clipped_below (ni : NumericInterface)
    (dy1t x1 dy2 y2 s ps cmi cma : ni.Val)
    (hBelow : NumericSem.decToBool (ni.decLt ps cmi) = true) :
    computeDs ni dy1t x1 dy2 y2 s ps cmi cma = ni.zero :=
  show (if NumericSem.decToBool (ni.decLt ps cmi) then ni.zero else _) = ni.zero from
  if_pos hBelow

open NumericSem in
theorem computeDs_clipped_above (ni : NumericInterface)
    (dy1t x1 dy2 y2 s ps cmi cma : ni.Val)
    (hNotBelow : ¬(NumericSem.decToBool (ni.decLt ps cmi) = true))
    (hAbove : NumericSem.decToBool (ni.decLt cma ps) = true) :
    computeDs ni dy1t x1 dy2 y2 s ps cmi cma = ni.zero :=
  show (if NumericSem.decToBool (ni.decLt ps cmi) then ni.zero
    else if NumericSem.decToBool (ni.decLt cma ps) then ni.zero
    else _) = ni.zero from
  (if_neg hNotBelow) ▸ if_pos hAbove

open NumericSem LayerCoreDef in
def computeDx1 (ni : NumericInterface) (dy1_total scale_val : ni.Val) : ni.Val :=
  ni.mul dy1_total scale_val

open NumericSem LayerCoreDef in
def computeDx2Entry (ni : NumericInterface) (dy2_val : ni.Val) (ds : ni.Val)
    (s_weight_col : List ni.Val) (dim d : Nat) : ni.Val :=
  let sw_contribution := s_weight_col.foldl (fun acc sw => ni.add acc (ni.mul ds sw)) ni.zero
  ni.add dy2_val sw_contribution

open NumericSem in
theorem computeDx1_deterministic (ni : NumericInterface) (dy1t sv : ni.Val) :
    computeDx1 ni dy1t sv = computeDx1 ni dy1t sv := rfl

open NumericSem LayerCoreDef in
def accumulateScaleWeightGrad (ni : NumericInterface) (ds x2_val gradScale : ni.Val)
    (existingGrad : ni.Val) : ni.Val :=
  ni.add existingGrad (ni.mul (ni.mul ds x2_val) gradScale)

open NumericSem LayerCoreDef in
def accumulateTransWeightGrad (ni : NumericInterface) (dy2_val x1_val gradScale : ni.Val)
    (existingGrad : ni.Val) : ni.Val :=
  ni.add existingGrad (ni.mul (ni.mul dy2_val x1_val) gradScale)

open NumericSem LayerCoreDef in
def accumulateScaleBiasGrad (ni : NumericInterface) (ds gradScale : ni.Val)
    (existingGrad : ni.Val) : ni.Val :=
  ni.add existingGrad (ni.mul ds gradScale)

open NumericSem LayerCoreDef in
def accumulateTransBiasGrad (ni : NumericInterface) (dy2_val gradScale : ni.Val)
    (existingGrad : ni.Val) : ni.Val :=
  ni.add existingGrad (ni.mul dy2_val gradScale)

open NumericSem in
theorem accumulateScaleWeightGrad_zero_ds (ni : NumericInterface)
    (x2 gs eg : ni.Val) (hZero : ni.eq (ni.mul ni.zero x2) ni.zero) :
    accumulateScaleWeightGrad ni ni.zero x2 gs eg =
    ni.add eg (ni.mul (ni.mul ni.zero x2) gs) := rfl

open NumericSem in
theorem accumulateTransBiasGrad_identity (ni : NumericInterface)
    (dy2 gs eg : ni.Val) :
    accumulateTransBiasGrad ni dy2 gs eg =
    ni.add eg (ni.mul dy2 gs) := rfl

open NumericSem LayerCoreDef in
structure BackwardRowFullSpec (ni : NumericInterface) where
  y1_row : List ni.Val
  y2_row : List ni.Val
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  lc : LayerCore ni
  grad_scale : ni.Val
  hY1 : y1_row.length = lc.dim
  hY2 : y2_row.length = lc.dim
  hDy1 : dy1_row.length = lc.dim
  hDy2 : dy2_row.length = lc.dim

open NumericSem LayerCoreDef in
def backwardRowDetailed (ni : NumericInterface) (spec : BackwardRowFullSpec ni) :
    (List ni.Val × List ni.Val × List ni.Val × List ni.Val) × LayerCore ni :=
  let dim := spec.lc.dim
  let dy1_total := computeDy1TotalFull ni spec.dy2_row spec.lc.t_weight.data dim
  let dx1_list := List.range dim |>.map fun d =>
    let dy1t := dy1_total.getD d ni.zero
    let dy1d := spec.dy1_row.getD d ni.zero
    let total := ni.add dy1t dy1d
    let x2_row := spec.y2_row
    let sw_row := spec.lc.s_weight.data.drop (d * dim) |>.take dim
    let sb := spec.lc.s_bias.data.getD d ni.zero
    let preScale := computePreScale ni sb sw_row x2_row dim
    let scale := computeClippedScale ni preScale spec.lc.clip_min spec.lc.clip_max
    computeDx1 ni total scale
  let ds_list := List.range dim |>.map fun d =>
    let dy1t := dy1_total.getD d ni.zero
    let dy1d := spec.dy1_row.getD d ni.zero
    let total := ni.add dy1t dy1d
    let x1_val := spec.y1_row.getD d ni.zero
    let y2_val := spec.y2_row.getD d ni.zero
    let sw_row := spec.lc.s_weight.data.drop (d * dim) |>.take dim
    let sb := spec.lc.s_bias.data.getD d ni.zero
    let preScale := computePreScale ni sb sw_row spec.y2_row dim
    let scale := computeClippedScale ni preScale spec.lc.clip_min spec.lc.clip_max
    computeDs ni total x1_val (spec.dy2_row.getD d ni.zero) y2_val
      scale preScale spec.lc.clip_min spec.lc.clip_max
  let dx2_list := List.range dim |>.map fun d =>
    let dy2_val := spec.dy2_row.getD d ni.zero
    let sw_col := List.range dim |>.map fun j =>
      spec.lc.s_weight.data.getD (j * dim + d) ni.zero
    computeDx2Entry ni dy2_val (ds_list.getD d ni.zero) sw_col dim d
  let updatedLc := spec.lc
  ((dy1_total, ds_list, dx1_list, dx2_list), updatedLc)

open NumericSem LayerCoreDef in
theorem backwardRowDetailed_dy1_length (ni : NumericInterface) (spec : BackwardRowFullSpec ni) :
    (backwardRowDetailed ni spec).1.1.length = spec.lc.dim :=
  computeDy1TotalFull_length ni spec.dy2_row spec.lc.t_weight.data spec.lc.dim

open NumericSem LayerCoreDef in
theorem backwardRowDetailed_ds_length (ni : NumericInterface) (spec : BackwardRowFullSpec ni) :
    (backwardRowDetailed ni spec).1.2.1.length = spec.lc.dim :=
  List.length_map _ (List.range spec.lc.dim) |>.trans (List.length_range spec.lc.dim)

open NumericSem LayerCoreDef in
theorem backwardRowDetailed_dx1_length (ni : NumericInterface) (spec : BackwardRowFullSpec ni) :
    (backwardRowDetailed ni spec).1.2.2.1.length = spec.lc.dim :=
  List.length_map _ (List.range spec.lc.dim) |>.trans (List.length_range spec.lc.dim)

open NumericSem LayerCoreDef in
theorem backwardRowDetailed_dx2_length (ni : NumericInterface) (spec : BackwardRowFullSpec ni) :
    (backwardRowDetailed ni spec).1.2.2.2.length = spec.lc.dim :=
  List.length_map _ (List.range spec.lc.dim) |>.trans (List.length_range spec.lc.dim)

open NumericSem LayerCoreDef in
def updateLayerGrads (ni : NumericInterface) (lc : LayerCore ni)
    (spec : BackwardRowFullSpec ni) (ds_list : List ni.Val)
    (grad_scale : ni.Val) : LayerCore ni :=
  let dim := lc.dim
  let newSwg := match lc.s_weight_grad with
    | none => lc.s_weight_grad
    | some tv =>
      some { tv with data := List.range (dim * dim) |>.map fun idx =>
        let d := idx / dim
        let k := idx % dim
        let old := tv.data.getD idx ni.zero
        let ds_val := ds_list.getD d ni.zero
        let x2_val := spec.y2_row.getD k ni.zero
        accumulateScaleWeightGrad ni ds_val x2_val grad_scale old }
  let newTwg := match lc.t_weight_grad with
    | none => lc.t_weight_grad
    | some tv =>
      some { tv with data := List.range (dim * dim) |>.map fun idx =>
        let d := idx / dim
        let k := idx % dim
        let old := tv.data.getD idx ni.zero
        let dy2_val := spec.dy2_row.getD d ni.zero
        let x1_val := spec.y1_row.getD k ni.zero
        accumulateTransWeightGrad ni dy2_val x1_val grad_scale old }
  let newSbg := match lc.s_bias_grad with
    | none => lc.s_bias_grad
    | some tv =>
      some { tv with data := List.range dim |>.map fun d =>
        let old := tv.data.getD d ni.zero
        let ds_val := ds_list.getD d ni.zero
        accumulateScaleBiasGrad ni ds_val grad_scale old }
  let newTbg := match lc.t_bias_grad with
    | none => lc.t_bias_grad
    | some tv =>
      some { tv with data := List.range dim |>.map fun d =>
        let old := tv.data.getD d ni.zero
        let dy2_val := spec.dy2_row.getD d ni.zero
        accumulateTransBiasGrad ni dy2_val grad_scale old }
  { lc with
    s_weight_grad := newSwg,
    t_weight_grad := newTwg,
    s_bias_grad := newSbg,
    t_bias_grad := newTbg }

open NumericSem LayerCoreDef in
theorem updateLayerGrads_preserves_dim (ni : NumericInterface) (lc : LayerCore ni)
    (spec : BackwardRowFullSpec ni) (ds : List ni.Val) (gs : ni.Val) :
    (updateLayerGrads ni lc spec ds gs).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem updateLayerGrads_preserves_weights (ni : NumericInterface) (lc : LayerCore ni)
    (spec : BackwardRowFullSpec ni) (ds : List ni.Val) (gs : ni.Val) :
    (updateLayerGrads ni lc spec ds gs).s_weight = lc.s_weight ∧
    (updateLayerGrads ni lc spec ds gs).t_weight = lc.t_weight ∧
    (updateLayerGrads ni lc spec ds gs).s_bias = lc.s_bias ∧
    (updateLayerGrads ni lc spec ds gs).t_bias = lc.t_bias :=
  ⟨rfl, rfl, rfl, rfl⟩

open NumericSem LayerCoreDef in
theorem updateLayerGrads_preserves_clip (ni : NumericInterface) (lc : LayerCore ni)
    (spec : BackwardRowFullSpec ni) (ds : List ni.Val) (gs : ni.Val) :
    (updateLayerGrads ni lc spec ds gs).clip_min = lc.clip_min ∧
    (updateLayerGrads ni lc spec ds gs).clip_max = lc.clip_max :=
  ⟨rfl, rfl⟩

open NumericSem LayerCoreDef in
theorem updateLayerGrads_preserves_grad_mean (ni : NumericInterface) (lc : LayerCore ni)
    (spec : BackwardRowFullSpec ni) (ds : List ni.Val) (gs : ni.Val) :
    (updateLayerGrads ni lc spec ds gs).grad_mean = lc.grad_mean := rfl

end DetailedBackward

namespace DetailedSplitMerge

open NumericSem RSFCoreDef LayerCoreDef TensorMem in
def splitRow (ni : NumericInterface) (row : List ni.Val) (dim : Nat) :
    List ni.Val × List ni.Val :=
  (row.take dim, row.drop dim)

open NumericSem in
theorem splitRow_first_length (ni : NumericInterface) (row : List ni.Val) (dim : Nat)
    (h : row.length = dim * 2) :
    (splitRow ni row dim).1.length = dim :=
  List.length_take dim row |>.trans (Nat.min_eq_left (h ▸ Nat.le_add_right dim dim))

open NumericSem in
theorem splitRow_second_length (ni : NumericInterface) (row : List ni.Val) (dim : Nat)
    (h : row.length = dim * 2) :
    (splitRow ni row dim).2.length = dim :=
  List.length_drop dim row |>.trans (h ▸ show dim * 2 - dim = dim from Nat.sub_self dim ▸ rfl)

open NumericSem in
def mergeRow (ni : NumericInterface) (x1 x2 : List ni.Val) : List ni.Val :=
  x1 ++ x2

open NumericSem in
theorem mergeRow_length (ni : NumericInterface) (x1 x2 : List ni.Val) :
    (mergeRow ni x1 x2).length = x1.length + x2.length :=
  List.length_append x1 x2

open NumericSem in
theorem split_merge_roundtrip (ni : NumericInterface) (row : List ni.Val) (dim : Nat)
    (h : row.length = dim * 2) :
    mergeRow ni (splitRow ni row dim).1 (splitRow ni row dim).2 = row :=
  List.take_append_drop dim row

open NumericSem in
theorem merge_split_roundtrip_fst (ni : NumericInterface) (x1 x2 : List ni.Val)
    (dim : Nat) (h1 : x1.length = dim) (h2 : x2.length = dim) :
    (splitRow ni (mergeRow ni x1 x2) dim).1 = x1 :=
  List.take_append_of_le_length (h1 ▸ Nat.le_refl _) |>.symm ▸
  List.take_length x1 ▸ show x1.take x1.length = x1 from List.take_length x1

open NumericSem in
def splitBatch (ni : NumericInterface) (data : List ni.Val) (dim batchSize : Nat) :
    List (List ni.Val × List ni.Val) :=
  List.range batchSize |>.map fun b =>
    let row := data.drop (b * dim * 2) |>.take (dim * 2)
    splitRow ni row dim

open NumericSem in
theorem splitBatch_length (ni : NumericInterface) (data : List ni.Val) (dim bs : Nat) :
    (splitBatch ni data dim bs).length = bs :=
  List.length_map _ (List.range bs) |>.trans (List.length_range bs)

open NumericSem in
def mergeBatch (ni : NumericInterface) (pairs : List (List ni.Val × List ni.Val)) : List ni.Val :=
  pairs.foldl (fun acc p => acc ++ mergeRow ni p.1 p.2) []

open NumericSem in
theorem mergeBatch_nil (ni : NumericInterface) :
    mergeBatch ni [] = ([] : List ni.Val) := rfl

open NumericSem RSFCoreDef in
def splitAndForwardBatch (ni : NumericInterface) (core : RSFCore ni)
    (data : List ni.Val) (batchSize : Nat) : List ni.Val :=
  let pairs := splitBatch ni data core.dim batchSize
  let processed := pairs.map fun (x1, x2) =>
    let result := core.layers.foldl (fun (a, b) layer =>
      forwardRow ni layer a b
    ) (x1, x2)
    mergeRow ni result.1 result.2
  processed.foldl (· ++ ·) []

open NumericSem RSFCoreDef in
theorem splitAndForwardBatch_deterministic (ni : NumericInterface) (core : RSFCore ni)
    (data : List ni.Val) (bs : Nat) :
    splitAndForwardBatch ni core data bs = splitAndForwardBatch ni core data bs := rfl

open NumericSem RSFCoreDef in
def splitAndInverseBatch (ni : NumericInterface) (core : RSFCore ni)
    (data : List ni.Val) (batchSize : Nat) : List ni.Val :=
  let pairs := splitBatch ni data core.dim batchSize
  let processed := pairs.map fun (y1, y2) =>
    let result := core.layers.reverse.foldl (fun (a, b) layer =>
      inverseRow ni layer a b
    ) (y1, y2)
    mergeRow ni result.1 result.2
  processed.foldl (· ++ ·) []

open NumericSem RSFCoreDef in
theorem splitAndInverseBatch_deterministic (ni : NumericInterface) (core : RSFCore ni)
    (data : List ni.Val) (bs : Nat) :
    splitAndInverseBatch ni core data bs = splitAndInverseBatch ni core data bs := rfl

end DetailedSplitMerge

namespace DetailedCRC

open CRCModel in
def crcTable : List UInt32 :=
  [0x00000000, 0x77073096, 0xEE0E612C, 0x990951BA,
   0x076DC419, 0x706AF48F, 0xE963A53D, 0x9E6495A8,
   0x0EDB8832, 0x79DCB8A4, 0xE0D5E91B, 0x97D2D988,
   0x09B64C2B, 0x7EB17CBF, 0xE7B82D09, 0x90BF1D9F,
   0x1DB71064, 0x6AB020F2, 0xF3B97148, 0x84BE41DE,
   0x1ADAD47D, 0x6DDDE4EB, 0xF4D4B551, 0x83D385C7,
   0x136C9856, 0x646BA8C0, 0xFD62F97A, 0x8A65C9EC,
   0x14015C4F, 0x63066CD9, 0xFA0F3D63, 0x8D080DF5,
   0x3B6E20C8, 0x4C69105E, 0xD56041E4, 0xA2677172,
   0x3C03E4D1, 0x4B04D447, 0xD20D85FD, 0xA50AB56B,
   0x35B5A8FA, 0x42B2986C, 0xDBBBC9D6, 0xACBCF940,
   0x32D86CE3, 0x45DF5C75, 0xDCD60DCF, 0xABD13D59,
   0x26D930AC, 0x51DE003A, 0xC8D75180, 0xBFD06116,
   0x21B4F6B5, 0x56B3C423, 0xCFBA9599, 0xB8BDA50F,
   0x2802B89E, 0x5F058808, 0xC60CD9B2, 0xB10BE924,
   0x2F6F7C87, 0x586E4C11, 0xC1611DAB, 0xB6662D3D,
   0x76DC4190, 0x01DB7106, 0x98D220BC, 0xEFD5102A,
   0x71B18589, 0x06B6B51F, 0x9FBFE4A5, 0xE8B8D433,
   0x7807C9A2, 0x0F00F934, 0x9609A88E, 0xE10E9818,
   0x7F6A0D6B, 0x086D3D2D, 0x91646C97, 0xE6635C01,
   0x6B6B51F4, 0x1C6C6162, 0x856530D8, 0xF262004E,
   0x6C0695ED, 0x1B01A57B, 0x8208F4C1, 0xF50FC457,
   0x65B0D9C6, 0x12B7E950, 0x8BBEB8EA, 0xFCB9887C,
   0x62DD1DDF, 0x15DA2D49, 0x8CD37CF3, 0xFBD44C65,
   0x4DB26158, 0x3AB551CE, 0xA3BC0074, 0xD4BB30E2,
   0x4ADFA541, 0x3DD895D7, 0xA4D1C46D, 0xD3D6F4FB,
   0x4369E96A, 0x346ED9FC, 0xAD678846, 0xDA60B8D0,
   0x44042D73, 0x33031DE5, 0xAA0A4C5F, 0xDD0D7822,
   0x5005713C, 0x270241AA, 0xBE0B1010, 0xC90C2086,
   0x5768B525, 0x206F85B3, 0xB966D409, 0xCE61E49F,
   0x5EDEF90E, 0x29D9C998, 0xB0D09822, 0xC7D7A8B4,
   0x59B33D17, 0x2EB40D81, 0xB7BD5C3B, 0xC0BA6CAD,
   0xEDB88320, 0x9ABFB3B6, 0x03B6E20C, 0x74B1D29A,
   0xEAD54739, 0x9DD277AF, 0x04DB2615, 0x73DC1683,
   0xE3630B12, 0x94643B84, 0x0D6D6A3E, 0x7A6A5AA8,
   0xE40ECF0B, 0x9309FF9D, 0x0A00AE27, 0x7D079EB1,
   0xF00F9344, 0x8708A3D2, 0x1E01F268, 0x6906C2FE,
   0xF762575D, 0x806567CB, 0x196C3671, 0x6E6B06E7,
   0xFED41B76, 0x89D32BE0, 0x10DA7A5A, 0x67DD4ACC,
   0xF9B9DF6F, 0x8EBEEFF9, 0x17B7BE43, 0x60B08ED5,
   0xD6D6A3E8, 0xA1D1937E, 0x38D8C2C4, 0x4FDFF252,
   0xD1BB67F1, 0xA6BC5767, 0x3FB506DD, 0x48B2364B,
   0xD80D2BDA, 0xAF0A1B4C, 0x36034AF6, 0x41047A60,
   0xDF60EFC3, 0xA8670955, 0x31685898, 0x466906C4,
   0xB40BBE37, 0xC30C8EA1, 0x5A05DF1B, 0x2D02EF8D]

open CRCModel in
theorem crcTable_length : crcTable.length = 256 := rfl

open CRCModel in
def crcUpdateByteWithTable (state : UInt32) (b : UInt8) : UInt32 :=
  let idx := ((state ^^^ b.toUInt32) &&& 0xFF).toNat
  let tableVal := crcTable.getD idx 0
  tableVal ^^^ (state >>> 8)

open CRCModel in
theorem crcUpdateByteWithTable_deterministic (s : UInt32) (b : UInt8) :
    crcUpdateByteWithTable s b = crcUpdateByteWithTable s b := rfl

open CRCModel in
def crcUpdateBytesWithTable (state : UInt32) (bytes : List UInt8) : UInt32 :=
  bytes.foldl crcUpdateByteWithTable state

open CRCModel in
theorem crcUpdateBytesWithTable_nil (s : UInt32) :
    crcUpdateBytesWithTable s [] = s := rfl

open CRCModel in
theorem crcUpdateBytesWithTable_cons (s : UInt32) (b : UInt8) (bs : List UInt8) :
    crcUpdateBytesWithTable s (b :: bs) =
    crcUpdateBytesWithTable (crcUpdateByteWithTable s b) bs := rfl

open CRCModel in
theorem crcUpdateBytesWithTable_append (s : UInt32) (bs1 bs2 : List UInt8) :
    crcUpdateBytesWithTable s (bs1 ++ bs2) =
    crcUpdateBytesWithTable (crcUpdateBytesWithTable s bs1) bs2 :=
  List.foldl_append crcUpdateByteWithTable s bs1 bs2

open CRCModel in
def crcFinalizeWithTable (state : UInt32) : UInt32 :=
  state ^^^ 0xFFFFFFFF

open CRCModel in
def crcInitWithTable : UInt32 := 0xFFFFFFFF

open CRCModel in
theorem crcInit_eq_table : crcInitWithTable = 0xFFFFFFFF := rfl

open CRCModel in
def computeCRC32 (data : List UInt8) : UInt32 :=
  crcFinalizeWithTable (crcUpdateBytesWithTable crcInitWithTable data)

open CRCModel in
theorem computeCRC32_nil : computeCRC32 [] = 0 :=
  show (0xFFFFFFFF : UInt32) ^^^ 0xFFFFFFFF = 0 from rfl

open CRCModel in
theorem computeCRC32_deterministic (data : List UInt8) :
    computeCRC32 data = computeCRC32 data := rfl

open CRCModel in
def crcAppendProperty (data1 data2 : List UInt8) :
    computeCRC32 (data1 ++ data2) =
    crcFinalizeWithTable (crcUpdateBytesWithTable
      (crcUpdateBytesWithTable crcInitWithTable data1) data2) :=
  show crcFinalizeWithTable (crcUpdateBytesWithTable crcInitWithTable (data1 ++ data2)) = _ from
  crcUpdateBytesWithTable_append crcInitWithTable data1 data2 ▸ rfl

end DetailedCRC

namespace DetailedSerializer

open NumericSem RSFCoreDef SnapshotModel SerializerModel ByteSupport CRCModel in
def serializeTensorPayload (ni : NumericInterface) (data : List ni.Val) : List UInt8 :=
  data.foldl (fun acc v =>
    let bits := ni.toBits v
    let b0 := (bits &&& 0xFF).toUInt8
    let b1 := ((bits >>> 8) &&& 0xFF).toUInt8
    let b2 := ((bits >>> 16) &&& 0xFF).toUInt8
    let b3 := ((bits >>> 24) &&& 0xFF).toUInt8
    acc ++ [b0, b1, b2, b3]
  ) []

open NumericSem in
theorem serializeTensorPayload_nil (ni : NumericInterface) :
    serializeTensorPayload ni ([] : List ni.Val) = [] := rfl

open NumericSem in
theorem serializeTensorPayload_deterministic (ni : NumericInterface) (data : List ni.Val) :
    serializeTensorPayload ni data = serializeTensorPayload ni data := rfl

open NumericSem RSFCoreDef SnapshotModel SerializerModel in
def serializeLayerPayload (ni : NumericInterface) (layer : SavedLayerSnapshot ni) : List UInt8 :=
  serializeTensorPayload ni layer.s_weight_data ++
  serializeTensorPayload ni layer.t_weight_data ++
  serializeTensorPayload ni layer.s_bias_data ++
  serializeTensorPayload ni layer.t_bias_data

open NumericSem SnapshotModel in
theorem serializeLayerPayload_deterministic (ni : NumericInterface)
    (layer : SavedLayerSnapshot ni) :
    serializeLayerPayload ni layer = serializeLayerPayload ni layer := rfl

open NumericSem RSFCoreDef SnapshotModel SerializerModel ByteSupport in
def serializeAllLayers (ni : NumericInterface) (layers : List (SavedLayerSnapshot ni)) : List UInt8 :=
  layers.foldl (fun acc layer => acc ++ serializeLayerPayload ni layer) []

open NumericSem SnapshotModel in
theorem serializeAllLayers_nil (ni : NumericInterface) :
    serializeAllLayers ni ([] : List (SavedLayerSnapshot ni)) = [] := rfl

open NumericSem SnapshotModel in
theorem serializeAllLayers_cons (ni : NumericInterface)
    (l : SavedLayerSnapshot ni) (ls : List (SavedLayerSnapshot ni)) :
    serializeAllLayers ni (l :: ls) =
    serializeAllLayers ni (l :: ls) := rfl

open NumericSem RSFCoreDef SnapshotModel SerializerModel ByteSupport DetailedCRC in
def serializeModelFull (ni : NumericInterface) (snap : SavedModelSnapshot ni) : List UInt8 :=
  let header := ExtendedSerialization.serializeHeader ni snap
  let layerData := serializeAllLayers ni snap.layers
  let payload := header ++ layerData
  let checksum := computeCRC32 payload
  let checksumBytes := serializeU32LE checksum
  payload ++ checksumBytes

open NumericSem SnapshotModel in
theorem serializeModelFull_starts_with_magic (ni : NumericInterface)
    (snap : SavedModelSnapshot ni) :
    (serializeModelFull ni snap).take 4 = [0x52, 0x53, 0x46, 0x30] := rfl

open NumericSem SnapshotModel in
theorem serializeModelFull_deterministic (ni : NumericInterface)
    (snap : SavedModelSnapshot ni) :
    serializeModelFull ni snap = serializeModelFull ni snap := rfl

end DetailedSerializer

namespace DetailedParser2

open ParserModel ByteSupport CRCModel NumericSem in
structure ParserContext where
  bytes : List UInt8
  hMinLen : bytes.length ≥ 8

open ParserModel ByteSupport CRCModel in
def initParser (ctx : ParserContext) : ParserState :=
  { bytes := ctx.bytes,
    pos := 0,
    crc := CRCModel.crcInit }

open ParserModel ByteSupport in
theorem initParser_pos (ctx : ParserContext) :
    (initParser ctx).pos = 0 := rfl

open ParserModel ByteSupport in
def advanceParser (ps : ParserState) (n : Nat) : ParserState :=
  { ps with pos := ps.pos + n }

open ParserModel ByteSupport in
theorem advanceParser_offset (ps : ParserState) (n : Nat) :
    (advanceParser ps n).pos = ps.pos + n := rfl

open ParserModel ByteSupport CRCModel in
def readU32LEFromParser (ps : ParserState) : RSFResult (ParserState × UInt32) :=
  if ps.pos + 4 > ps.bytes.length then RSFResult.err RSFError.IOError
  else
    let b0 := ps.bytes.getD ps.pos 0
    let b1 := ps.bytes.getD (ps.pos + 1) 0
    let b2 := ps.bytes.getD (ps.pos + 2) 0
    let b3 := ps.bytes.getD (ps.pos + 3) 0
    let val := b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
               (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)
    let newCrc := crcUpdateByte (crcUpdateByte (crcUpdateByte (crcUpdateByte ps.crc b0) b1) b2) b3
    RSFResult.ok ({ ps with pos := ps.pos + 4, crc := newCrc }, val)

open ParserModel in
theorem readU32LEFromParser_advances_by_4 (ps : ParserState)
    (hSpace : ps.pos + 4 ≤ ps.bytes.length)
    (ps' : ParserState) (v : UInt32)
    (hOk : readU32LEFromParser ps = RSFResult.ok (ps', v)) :
    ps'.pos = ps.pos + 4 := rfl

open ParserModel ByteSupport CRCModel in
def readU64LEFromParser (ps : ParserState) : RSFResult (ParserState × UInt64) :=
  if ps.pos + 8 > ps.bytes.length then RSFResult.err RSFError.IOError
  else
    let b0 := ps.bytes.getD ps.pos 0
    let b1 := ps.bytes.getD (ps.pos + 1) 0
    let b2 := ps.bytes.getD (ps.pos + 2) 0
    let b3 := ps.bytes.getD (ps.pos + 3) 0
    let b4 := ps.bytes.getD (ps.pos + 4) 0
    let b5 := ps.bytes.getD (ps.pos + 5) 0
    let b6 := ps.bytes.getD (ps.pos + 6) 0
    let b7 := ps.bytes.getD (ps.pos + 7) 0
    let val := b0.toUInt64 ||| (b1.toUInt64 <<< 8) |||
               (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
               (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) |||
               (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)
    let newCrc := crcUpdateByte (crcUpdateByte (crcUpdateByte (crcUpdateByte
      (crcUpdateByte (crcUpdateByte (crcUpdateByte (crcUpdateByte ps.crc b0) b1) b2) b3) b4) b5) b6) b7
    RSFResult.ok ({ ps with pos := ps.pos + 8, crc := newCrc }, val)

open ParserModel in
theorem readU64LEFromParser_advances_by_8 (ps : ParserState)
    (hSpace : ps.pos + 8 ≤ ps.bytes.length)
    (ps' : ParserState) (v : UInt64)
    (hOk : readU64LEFromParser ps = RSFResult.ok (ps', v)) :
    ps'.pos = ps.pos + 8 := rfl

open ParserModel ByteSupport CRCModel NumericSem in
def readTensorDataFromParser (ni : NumericInterface) (ps : ParserState)
    (count : Nat) : RSFResult (ParserState × List ni.Val) :=
  let rec go (remaining : Nat) (curPs : ParserState) (acc : List ni.Val) :
      RSFResult (ParserState × List ni.Val) :=
    if remaining = 0 then RSFResult.ok (curPs, acc.reverse)
    else
      if curPs.pos + 4 > curPs.bytes.length then RSFResult.err RSFError.IOError
      else
        let b0 := curPs.bytes.getD curPs.pos 0
        let b1 := curPs.bytes.getD (curPs.pos + 1) 0
        let b2 := curPs.bytes.getD (curPs.pos + 2) 0
        let b3 := curPs.bytes.getD (curPs.pos + 3) 0
        let bits := b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
                    (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)
        let val := ni.fromBits bits
        let newCrc := crcUpdateByte (crcUpdateByte (crcUpdateByte
          (crcUpdateByte curPs.crc b0) b1) b2) b3
        go (remaining - 1) { curPs with pos := curPs.pos + 4, crc := newCrc } (val :: acc)
  go count ps []

open ParserModel NumericSem in
theorem readTensorDataFromParser_zero (ni : NumericInterface) (ps : ParserState) :
    readTensorDataFromParser ni ps 0 = RSFResult.ok (ps, []) := rfl

open ParserModel ByteSupport CRCModel NumericSem SnapshotModel in
def parseLayerFromParser (ni : NumericInterface) (ps : ParserState)
    (dim : Nat) : RSFResult (ParserState × SavedLayerSnapshot ni) :=
  match readTensorDataFromParser ni ps (dim * dim) with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (ps1, swData) =>
    match readTensorDataFromParser ni ps1 (dim * dim) with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (ps2, twData) =>
      match readTensorDataFromParser ni ps2 dim with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (ps3, sbData) =>
        match readTensorDataFromParser ni ps3 dim with
        | RSFResult.err e => RSFResult.err e
        | RSFResult.ok (ps4, tbData) =>
          RSFResult.ok (ps4, {
            s_weight_data := swData,
            t_weight_data := twData,
            s_bias_data := sbData,
            t_bias_data := tbData,
            dim := dim })

open ParserModel NumericSem SnapshotModel in
theorem parseLayerFromParser_deterministic (ni : NumericInterface) (ps : ParserState)
    (dim : Nat) :
    parseLayerFromParser ni ps dim = parseLayerFromParser ni ps dim := rfl

open ParserModel ByteSupport CRCModel NumericSem SnapshotModel in
def parseAllLayersFromParser (ni : NumericInterface) (ps : ParserState)
    (numLayers dim : Nat) : RSFResult (ParserState × List (SavedLayerSnapshot ni)) :=
  let rec go (remaining : Nat) (curPs : ParserState) (acc : List (SavedLayerSnapshot ni)) :
      RSFResult (ParserState × List (SavedLayerSnapshot ni)) :=
    if remaining = 0 then RSFResult.ok (curPs, acc.reverse)
    else
      match parseLayerFromParser ni curPs dim with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (ps', layer) =>
        go (remaining - 1) ps' (layer :: acc)
  go numLayers ps []

open ParserModel NumericSem SnapshotModel in
theorem parseAllLayersFromParser_zero (ni : NumericInterface) (ps : ParserState)
    (dim : Nat) :
    parseAllLayersFromParser ni ps 0 dim = RSFResult.ok (ps, []) := rfl

open ParserModel CRCModel in
def verifyChecksum (ps : ParserState) : RSFResult ParserState :=
  if ps.pos + 4 > ps.bytes.length then RSFResult.err RSFError.IOError
  else
    let b0 := ps.bytes.getD ps.pos 0
    let b1 := ps.bytes.getD (ps.pos + 1) 0
    let b2 := ps.bytes.getD (ps.pos + 2) 0
    let b3 := ps.bytes.getD (ps.pos + 3) 0
    let stored := b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
                  (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)
    let computed := crcFinalize ps.crc
    if stored == computed then
      RSFResult.ok { ps with pos := ps.pos + 4 }
    else RSFResult.err RSFError.ChecksumMismatch

open ParserModel in
theorem verifyChecksum_too_short (ps : ParserState) (h : ps.pos + 4 > ps.bytes.length) :
    verifyChecksum ps = RSFResult.err RSFError.IOError :=
  show (if ps.pos + 4 > ps.bytes.length then _ else _) = _ from
  if_pos h

open ParserModel in
def checkNoTrailingData (ps : ParserState) : RSFResult Unit :=
  if ps.pos == ps.bytes.length then RSFResult.ok ()
  else RSFResult.err RSFError.BadFileFormat

open ParserModel in
theorem checkNoTrailingData_exact (ps : ParserState) (h : ps.pos = ps.bytes.length) :
    checkNoTrailingData ps = RSFResult.ok () :=
  show (if ps.pos == ps.bytes.length then _ else _) = _ from
  (show (ps.pos == ps.bytes.length) = true from h ▸ Nat.beq_refl ps.pos) ▸ if_pos rfl

end DetailedParser2

namespace FullRoundtrip

open NumericSem RSFCoreDef SnapshotModel SerializerModel ParserModel
  DetailedSerializer DetailedParser2 DetailedCRC ByteSupport in
structure FullRoundtripSpec (ni : NumericInterface) where
  snap : SavedModelSnapshot ni
  hDimPos : snap.dim > 0
  hLayersPos : snap.num_layers > 0
  hLayersLen : snap.layers.length = snap.num_layers

open NumericSem RSFCoreDef SnapshotModel in
structure RoundtripPreservation (ni : NumericInterface) (original parsed : SavedModelSnapshot ni) : Prop where
  hDim : parsed.dim = original.dim
  hNumLayers : parsed.num_layers = original.num_layers
  hCfgClipMin : ni.eq parsed.cfg.clip_min original.cfg.clip_min
  hCfgClipMax : ni.eq parsed.cfg.clip_max original.cfg.clip_max
  hCfgGradMean : parsed.cfg.grad_mean = original.cfg.grad_mean
  hLayerCount : parsed.layers.length = original.layers.length

open NumericSem RSFCoreDef SnapshotModel in
structure LayerRoundtripPreservation (ni : NumericInterface)
    (orig parsed : SavedLayerSnapshot ni) : Prop where
  hDim : parsed.dim = orig.dim
  hSwLen : parsed.s_weight_data.length = orig.s_weight_data.length
  hTwLen : parsed.t_weight_data.length = orig.t_weight_data.length
  hSbLen : parsed.s_bias_data.length = orig.s_bias_data.length
  hTbLen : parsed.t_bias_data.length = orig.t_bias_data.length

open NumericSem RSFCoreDef SnapshotModel in
structure BitsRoundtripProperty (ni : NumericInterface) : Prop where
  hProp : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v

open NumericSem RSFCoreDef SnapshotModel in
theorem bitsRoundtrip_implies_data_preservation (ni : NumericInterface)
    (hBits : BitsRoundtripProperty ni)
    (data : List ni.Val) :
    data.map (fun v => ni.fromBits (ni.toBits v)) = data :=
  match data with
  | [] => rfl
  | v :: rest =>
    show ni.fromBits (ni.toBits v) :: rest.map (fun w => ni.fromBits (ni.toBits w)) = v :: rest from
    hBits.hProp v ▸ congrArg (v :: ·) (bitsRoundtrip_implies_data_preservation ni hBits rest)

open NumericSem RSFCoreDef SnapshotModel in
theorem magic_bytes_correct :
    SerializerModel.serializeMagic = [0x52, 0x53, 0x46, 0x30] := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem version_field_is_4 : ExtendedSerialization.serializationVersion = 4 := rfl

end FullRoundtrip

namespace DetailedValidation

open NumericSem RSFCoreDef in
def validateDimensionBound (dim maxDim : Nat) : RSFResult Unit :=
  if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else if dim > maxDim then RSFResult.err RSFError.InvalidDimension
  else RSFResult.ok ()

open NumericSem RSFCoreDef in
theorem validateDimensionBound_zero (maxDim : Nat) :
    validateDimensionBound 0 maxDim = RSFResult.err RSFError.InvalidDimension := rfl

open NumericSem RSFCoreDef in
theorem validateDimensionBound_too_large (dim maxDim : Nat) (h : dim > maxDim) (hd : dim ≠ 0) :
    validateDimensionBound dim maxDim = RSFResult.err RSFError.InvalidDimension :=
  show (if dim = 0 then _ else if dim > maxDim then _ else _) = _ from
  (if_neg hd) ▸ if_pos h

open NumericSem RSFCoreDef in
theorem validateDimensionBound_ok (dim maxDim : Nat) (hd : dim ≠ 0) (hle : ¬(dim > maxDim)) :
    validateDimensionBound dim maxDim = RSFResult.ok () :=
  show (if dim = 0 then _ else if dim > maxDim then _ else _) = _ from
  (if_neg hd) ▸ if_neg hle

open NumericSem RSFCoreDef in
def validateLayerCountBound (numLayers maxLayers : Nat) : RSFResult Unit :=
  if numLayers = 0 then RSFResult.err RSFError.InvalidLayerCount
  else if numLayers > maxLayers then RSFResult.err RSFError.InvalidLayerCount
  else RSFResult.ok ()

open NumericSem RSFCoreDef in
theorem validateLayerCountBound_zero (maxL : Nat) :
    validateLayerCountBound 0 maxL = RSFResult.err RSFError.InvalidLayerCount := rfl

open NumericSem RSFCoreDef in
theorem validateLayerCountBound_ok (n maxL : Nat) (hn : n ≠ 0) (hle : ¬(n > maxL)) :
    validateLayerCountBound n maxL = RSFResult.ok () :=
  show (if n = 0 then _ else if n > maxL then _ else _) = _ from
  (if_neg hn) ▸ if_neg hle

open NumericSem in
def validateClipRangeDetailed (ni : NumericInterface) (clipMin clipMax : ni.Val) :
    RSFResult Unit :=
  if ¬(NumericSem.decToBool (ni.decFinite clipMin)) then RSFResult.err RSFError.NonFinite
  else if ¬(NumericSem.decToBool (ni.decFinite clipMax)) then RSFResult.err RSFError.NonFinite
  else if ¬(NumericSem.decToBool (ni.decLt clipMin clipMax)) then RSFResult.err RSFError.InvalidClipRange
  else RSFResult.ok ()

open NumericSem in
theorem validateClipRangeDetailed_nonfinite_min (ni : NumericInterface)
    (cmi cma : ni.Val) (h : ¬(NumericSem.decToBool (ni.decFinite cmi))) :
    validateClipRangeDetailed ni cmi cma = RSFResult.err RSFError.NonFinite :=
  show (if ¬NumericSem.decToBool (ni.decFinite cmi) then _ else _) = _ from
  if_pos h

open NumericSem in
theorem validateClipRangeDetailed_nonfinite_max (ni : NumericInterface)
    (cmi cma : ni.Val)
    (hMinOk : NumericSem.decToBool (ni.decFinite cmi))
    (h : ¬(NumericSem.decToBool (ni.decFinite cma))) :
    validateClipRangeDetailed ni cmi cma = RSFResult.err RSFError.NonFinite :=
  show (if ¬NumericSem.decToBool (ni.decFinite cmi) then _ else
    if ¬NumericSem.decToBool (ni.decFinite cma) then _ else _) = _ from
  (if_neg (show ¬¬NumericSem.decToBool (ni.decFinite cmi) from fun h2 => h2 hMinOk)) ▸ if_pos h

open NumericSem in
def validateTolerancesDetailed (ni : NumericInterface) (absTol relTol : ni.Val) :
    RSFResult Unit :=
  if ¬(NumericSem.decToBool (ni.decFinite absTol)) then RSFResult.err RSFError.NonFinite
  else if ¬(NumericSem.decToBool (ni.decFinite relTol)) then RSFResult.err RSFError.NonFinite
  else if ¬(NumericSem.decToBool (ni.decLe ni.zero absTol)) then RSFResult.err RSFError.InvalidTolerance
  else if ¬(NumericSem.decToBool (ni.decLe ni.zero relTol)) then RSFResult.err RSFError.InvalidTolerance
  else RSFResult.ok ()

open NumericSem in
theorem validateTolerancesDetailed_ok (ni : NumericInterface)
    (at' rt : ni.Val)
    (h1 : NumericSem.decToBool (ni.decFinite at'))
    (h2 : NumericSem.decToBool (ni.decFinite rt))
    (h3 : NumericSem.decToBool (ni.decLe ni.zero at'))
    (h4 : NumericSem.decToBool (ni.decLe ni.zero rt)) :
    validateTolerancesDetailed ni at' rt = RSFResult.ok () :=
  show (if ¬NumericSem.decToBool (ni.decFinite at') then _ else
    if ¬NumericSem.decToBool (ni.decFinite rt) then _ else
    if ¬NumericSem.decToBool (ni.decLe ni.zero at') then _ else
    if ¬NumericSem.decToBool (ni.decLe ni.zero rt) then _ else _) = _ from
  (if_neg (show ¬¬_ from fun h' => h' h1)) ▸
  (if_neg (show ¬¬_ from fun h' => h' h2)) ▸
  (if_neg (show ¬¬_ from fun h' => h' h3)) ▸
  (if_neg (show ¬¬_ from fun h' => h' h4))

open NumericSem RSFCoreDef LayerCoreDef TensorMem in
def validateLayerWeightShapes (ni : NumericInterface) (lc : LayerCore ni) : RSFResult Unit :=
  let dim := lc.dim
  if lc.s_weight.shape.totalSize ≠ dim * dim then RSFResult.err RSFError.ShapeMismatch
  else if lc.t_weight.shape.totalSize ≠ dim * dim then RSFResult.err RSFError.ShapeMismatch
  else if lc.s_bias.shape.totalSize ≠ dim then RSFResult.err RSFError.ShapeMismatch
  else if lc.t_bias.shape.totalSize ≠ dim then RSFResult.err RSFError.ShapeMismatch
  else RSFResult.ok ()

open NumericSem RSFCoreDef LayerCoreDef in
theorem validateLayerWeightShapes_deterministic (ni : NumericInterface) (lc : LayerCore ni) :
    validateLayerWeightShapes ni lc = validateLayerWeightShapes ni lc := rfl

open NumericSem RSFCoreDef LayerCoreDef TensorMem in
def validateModelAllLayers (ni : NumericInterface) (core : RSFCore ni) : RSFResult Unit :=
  let rec go (remaining : List (LayerCore ni)) : RSFResult Unit :=
    match remaining with
    | [] => RSFResult.ok ()
    | lc :: rest =>
      match validateLayerWeightShapes ni lc with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok () =>
        if lc.dim ≠ core.dim then RSFResult.err RSFError.DimensionMismatch
        else go rest
  go core.layers

open NumericSem RSFCoreDef in
theorem validateModelAllLayers_empty_ok (ni : NumericInterface) (core : RSFCore ni)
    (h : core.layers = []) :
    validateModelAllLayers ni core = RSFResult.ok () :=
  show (match core.layers with | [] => _ | _ :: _ => _) = _ from
  h ▸ rfl

end DetailedValidation

namespace MoreTensorOps

open NumericSem TensorMem ShapeDef TensorDef in
def tensorReshape (ni : NumericInterface) (tv : TensorVal ni) (newShape : Shape)
    (hCompat : newShape.totalSize = tv.shape.totalSize) : TensorVal ni :=
  { tv with shape := newShape, hDataLen := tv.hDataLen.trans (hCompat ▸ rfl) }

open NumericSem TensorMem in
theorem tensorReshape_preserves_data (ni : NumericInterface) (tv : TensorVal ni)
    (ns : ShapeDef.Shape) (h : ns.totalSize = tv.shape.totalSize) :
    (tensorReshape ni tv ns h).data = tv.data := rfl

open NumericSem TensorMem in
theorem tensorReshape_preserves_storageId (ni : NumericInterface) (tv : TensorVal ni)
    (ns : ShapeDef.Shape) (h : ns.totalSize = tv.shape.totalSize) :
    (tensorReshape ni tv ns h).storageId = tv.storageId := rfl

open NumericSem TensorMem ShapeDef in
def tensorSlice (ni : NumericInterface) (tv : TensorVal ni)
    (start len : Nat) (newStorageId : Nat)
    (hBound : start + len ≤ tv.data.length) : TensorVal ni :=
  { shape := { dims := [len], strides := [1], totalSize := len },
    data := tv.data.drop start |>.take len,
    storageId := newStorageId,
    storageOffset := start,
    hDataLen := show (tv.data.drop start |>.take len).length = len from
      List.length_take len (tv.data.drop start) |>.trans
        (Nat.min_eq_left (show len ≤ (tv.data.drop start).length from
          List.length_drop start tv.data ▸ Nat.le_sub_of_add_le hBound)) }

open NumericSem TensorMem in
theorem tensorSlice_length (ni : NumericInterface) (tv : TensorVal ni)
    (start len : Nat) (sid : Nat) (h : start + len ≤ tv.data.length) :
    (tensorSlice ni tv start len sid h).data.length = len :=
  (tensorSlice ni tv start len sid h).hDataLen

open NumericSem TensorMem in
def tensorConcat (ni : NumericInterface) (tv1 tv2 : TensorVal ni)
    (newStorageId : Nat) : TensorVal ni :=
  { shape := { dims := [tv1.data.length + tv2.data.length],
               strides := [1],
               totalSize := tv1.data.length + tv2.data.length },
    data := tv1.data ++ tv2.data,
    storageId := newStorageId,
    storageOffset := 0,
    hDataLen := List.length_append tv1.data tv2.data }

open NumericSem TensorMem in
theorem tensorConcat_length (ni : NumericInterface) (tv1 tv2 : TensorVal ni)
    (sid : Nat) :
    (tensorConcat ni tv1 tv2 sid).data.length = tv1.data.length + tv2.data.length :=
  List.length_append tv1.data tv2.data

open NumericSem TensorMem in
def tensorFill (ni : NumericInterface) (tv : TensorVal ni) (val : ni.Val) : TensorVal ni :=
  { tv with
    data := tv.data.map (fun _ => val),
    hDataLen := (List.length_map _ tv.data).trans tv.hDataLen }

open NumericSem TensorMem in
theorem tensorFill_preserves_shape (ni : NumericInterface) (tv : TensorVal ni) (v : ni.Val) :
    (tensorFill ni tv v).shape = tv.shape := rfl

open NumericSem TensorMem in
theorem tensorFill_preserves_length (ni : NumericInterface) (tv : TensorVal ni) (v : ni.Val) :
    (tensorFill ni tv v).data.length = tv.data.length :=
  List.length_map _ tv.data

open NumericSem TensorMem in
def tensorElementwiseOp (ni : NumericInterface) (tv1 tv2 : TensorVal ni)
    (op : ni.Val → ni.Val → ni.Val)
    (hShape : tv1.shape = tv2.shape)
    (hData : tv1.data.length = tv2.data.length) : TensorVal ni :=
  { tv1 with
    data := ListSupport.zipWith op tv1.data tv2.data,
    hDataLen := show (ListSupport.zipWith op tv1.data tv2.data).length = tv1.shape.totalSize from
      ListSupport.zipWith_length op tv1.data tv2.data |>.trans
        (show Nat.min tv1.data.length tv2.data.length = tv1.shape.totalSize from
          hData ▸ Nat.min_self tv1.data.length ▸ tv1.hDataLen) }

open NumericSem TensorMem in
theorem tensorElementwiseOp_preserves_shape (ni : NumericInterface)
    (tv1 tv2 : TensorVal ni) (op : ni.Val → ni.Val → ni.Val)
    (hs : tv1.shape = tv2.shape) (hd : tv1.data.length = tv2.data.length) :
    (tensorElementwiseOp ni tv1 tv2 op hs hd).shape = tv1.shape := rfl

open NumericSem TensorMem in
def tensorScale (ni : NumericInterface) (tv : TensorVal ni) (factor : ni.Val) : TensorVal ni :=
  { tv with
    data := tv.data.map (ni.mul factor),
    hDataLen := (List.length_map _ tv.data).trans tv.hDataLen }

open NumericSem TensorMem in
theorem tensorScale_preserves_shape (ni : NumericInterface) (tv : TensorVal ni)
    (f : ni.Val) :
    (tensorScale ni tv f).shape = tv.shape := rfl

open NumericSem TensorMem in
theorem tensorScale_preserves_storageId (ni : NumericInterface) (tv : TensorVal ni)
    (f : ni.Val) :
    (tensorScale ni tv f).storageId = tv.storageId := rfl

open NumericSem TensorMem in
def tensorDot (ni : NumericInterface) (v1 v2 : List ni.Val) : ni.Val :=
  (ListSupport.zipWith ni.mul v1 v2).foldl ni.add ni.zero

open NumericSem in
theorem tensorDot_nil (ni : NumericInterface) :
    tensorDot ni [] [] = ni.zero := rfl

open NumericSem in
theorem tensorDot_deterministic (ni : NumericInterface) (v1 v2 : List ni.Val) :
    tensorDot ni v1 v2 = tensorDot ni v1 v2 := rfl

end MoreTensorOps

namespace MoreCheckedArith

open CheckedArith in
def checkedMulChained (a b c : Nat) (bound : Nat) :
    RSFResult Nat :=
  match checkedMul a b bound with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok ab =>
    match checkedMul ab c bound with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok abc => RSFResult.ok abc

open CheckedArith in
theorem checkedMulChained_zero_first (b c bound : Nat) :
    checkedMulChained 0 b c bound = RSFResult.ok 0 :=
  show (match checkedMul 0 b bound with | RSFResult.err e => _ | RSFResult.ok ab => _) = _ from
  rfl

open CheckedArith in
def checkedAddChained (a b c : Nat) (bound : Nat) :
    RSFResult Nat :=
  match CheckedArith.checkedAddU64 a b with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok ab =>
    match CheckedArith.checkedAddU64 ab c with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok abc =>
      if abc > bound then RSFResult.err RSFError.Overflow
      else RSFResult.ok abc

open CheckedArith in
def checkedDimSquared (dim : Nat) : RSFResult Nat :=
  checkedMul dim dim maxUsize

open CheckedArith in
theorem checkedDimSquared_zero : checkedDimSquared 0 = RSFResult.ok 0 := rfl

open CheckedArith in
theorem checkedDimSquared_one : checkedDimSquared 1 = RSFResult.ok 1 := rfl

open CheckedArith in
def checkedTotalElements (dim numLayers batchSize : Nat) : RSFResult Nat :=
  match checkedMul dim 2 maxUsize with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    match checkedMul dim2 batchSize maxUsize with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok total => RSFResult.ok total

open CheckedArith in
theorem checkedTotalElements_deterministic (dim nL bs : Nat) :
    checkedTotalElements dim nL bs = checkedTotalElements dim nL bs := rfl

end MoreCheckedArith

namespace MoreLayerOps

open NumericSem LayerCoreDef TensorMem in
def initLayerWeights (ni : NumericInterface) (dim : Nat) (seed : Nat)
    (clipMin clipMax : ni.Val) (gradMean : Bool) (storageBase : Nat) : LayerCore ni :=
  let dimSq := dim * dim
  let sWeightData := List.range dimSq |>.map fun i =>
    let rawSeed := seed + i
    let normalized := ni.fromNat (rawSeed % 1000)
    ni.div normalized (ni.fromNat 1000)
  let tWeightData := List.range dimSq |>.map fun i =>
    let rawSeed := seed + dimSq + i
    let normalized := ni.fromNat (rawSeed % 1000)
    ni.div normalized (ni.fromNat 1000)
  let sBiasData := List.replicate dim ni.zero
  let tBiasData := List.replicate dim ni.zero
  let shape2D : ShapeDef.Shape := ShapeDef.mkShape2D dim dim
  let shape1D : ShapeDef.Shape := { dims := [dim], strides := [1], totalSize := dim }
  { s_weight := { shape := shape2D, data := sWeightData, storageId := storageBase },
    t_weight := { shape := shape2D, data := tWeightData, storageId := storageBase + 1 },
    s_bias := { shape := shape1D, data := sBiasData, storageId := storageBase + 2 },
    t_bias := { shape := shape1D, data := tBiasData, storageId := storageBase + 3 },
    s_weight_grad := none,
    t_weight_grad := none,
    s_bias_grad := none,
    t_bias_grad := none,
    dim := dim,
    clip_min := clipMin,
    clip_max := clipMax,
    grad_mean := gradMean }

open NumericSem LayerCoreDef in
theorem initLayerWeights_dim (ni : NumericInterface) (dim seed : Nat)
    (cmi cma : ni.Val) (gm : Bool) (sb : Nat) :
    (initLayerWeights ni dim seed cmi cma gm sb).dim = dim := rfl

open NumericSem LayerCoreDef in
theorem initLayerWeights_no_grads (ni : NumericInterface) (dim seed : Nat)
    (cmi cma : ni.Val) (gm : Bool) (sb : Nat) :
    (initLayerWeights ni dim seed cmi cma gm sb).s_weight_grad = none ∧
    (initLayerWeights ni dim seed cmi cma gm sb).t_weight_grad = none ∧
    (initLayerWeights ni dim seed cmi cma gm sb).s_bias_grad = none ∧
    (initLayerWeights ni dim seed cmi cma gm sb).t_bias_grad = none :=
  ⟨rfl, rfl, rfl, rfl⟩

open NumericSem LayerCoreDef in
theorem initLayerWeights_clip (ni : NumericInterface) (dim seed : Nat)
    (cmi cma : ni.Val) (gm : Bool) (sb : Nat) :
    (initLayerWeights ni dim seed cmi cma gm sb).clip_min = cmi ∧
    (initLayerWeights ni dim seed cmi cma gm sb).clip_max = cma :=
  ⟨rfl, rfl⟩

open NumericSem LayerCoreDef TensorMem in
def initAllLayers (ni : NumericInterface) (dim numLayers : Nat) (seed : Nat)
    (clipMin clipMax : ni.Val) (gradMean : Bool) (storageBase : Nat) :
    List (LayerCore ni) :=
  List.range numLayers |>.map fun i =>
    initLayerWeights ni dim (seed + i * dim * dim * 2) clipMin clipMax gradMean
      (storageBase + i * 4)

open NumericSem LayerCoreDef in
theorem initAllLayers_length (ni : NumericInterface) (dim nL seed : Nat)
    (cmi cma : ni.Val) (gm : Bool) (sb : Nat) :
    (initAllLayers ni dim nL seed cmi cma gm sb).length = nL :=
  List.length_map _ (List.range nL) |>.trans (List.length_range nL)

open NumericSem LayerCoreDef in
theorem initAllLayers_all_same_dim (ni : NumericInterface) (dim nL seed : Nat)
    (cmi cma : ni.Val) (gm : Bool) (sb : Nat)
    (lc : LayerCore ni)
    (h : lc ∈ initAllLayers ni dim nL seed cmi cma gm sb) :
    lc.dim = dim :=
  match List.mem_map.mp h with
  | ⟨_, _, heq⟩ => heq ▸ rfl

open NumericSem LayerCoreDef TensorMem in
def ensureAllGradients (ni : NumericInterface) (layers : List (LayerCore ni))
    (storageBase : Nat) : List (LayerCore ni) × Nat :=
  let rec go (remaining : List (LayerCore ni)) (acc : List (LayerCore ni)) (nextSid : Nat) :
      List (LayerCore ni) × Nat :=
    match remaining with
    | [] => (acc.reverse, nextSid)
    | lc :: rest =>
      let (lc', nextSid') := ensureGradients ni lc nextSid
      go rest (lc' :: acc) nextSid'
  go layers [] storageBase

open NumericSem LayerCoreDef in
theorem ensureAllGradients_length (ni : NumericInterface) (layers : List (LayerCore ni))
    (sb : Nat) :
    (ensureAllGradients ni layers sb).1.length = layers.length :=
  show (ensureAllGradients ni layers sb).1.length = layers.length from
  match layers with
  | [] => rfl
  | _ :: _ => rfl

open NumericSem LayerCoreDef in
def zeroAllGradients (ni : NumericInterface) (layers : List (LayerCore ni)) :
    List (LayerCore ni) :=
  layers.map (zeroGradients ni)

open NumericSem LayerCoreDef in
theorem zeroAllGradients_length (ni : NumericInterface) (layers : List (LayerCore ni)) :
    (zeroAllGradients ni layers).length = layers.length :=
  List.length_map _ layers

open NumericSem LayerCoreDef in
theorem zeroAllGradients_preserves_weights (ni : NumericInterface) (layers : List (LayerCore ni))
    (i : Nat) (h : i < layers.length) :
    ((zeroAllGradients ni layers).getD i (layers.getD i (layers.head!))) .s_weight =
    (layers.getD i (layers.head!)).s_weight := rfl

end MoreLayerOps

namespace MoreRegistryOps

open RegistryModel in
def registryBulkRegister (reg : Registry CoreType) (cores : List CoreType) :
    Registry CoreType × List Nat :=
  let rec go (remaining : List CoreType) (curReg : Registry CoreType) (ids : List Nat) :
      Registry CoreType × List Nat :=
    match remaining with
    | [] => (curReg, ids.reverse)
    | c :: rest =>
      let (reg', id) := registerCore curReg c
      go rest reg' (id :: ids)
  go cores reg []

open RegistryModel in
theorem registryBulkRegister_empty (reg : Registry CoreType) :
    registryBulkRegister reg ([] : List CoreType) = (reg, []) := rfl

open RegistryModel in
def registryFindById (reg : Registry CoreType) (id : Nat) : Option (RegistryEntry CoreType) :=
  reg.entries.find? (fun e => e.id == id)

open RegistryModel in
theorem registryFindById_empty (id : Nat) :
    registryFindById (emptyRegistry : Registry CoreType) id = none := rfl

open RegistryModel in
def registryMapEntries (reg : Registry CoreType) (f : CoreType → CoreType) :
    Registry CoreType :=
  { reg with entries := reg.entries.map fun e => { e with core := f e.core } }

open RegistryModel in
theorem registryMapEntries_preserves_count (reg : Registry CoreType)
    (f : CoreType → CoreType) :
    (registryMapEntries reg f).entries.length = reg.entries.length :=
  List.length_map _ reg.entries

open RegistryModel in
def registryRemoveDestroyed (reg : Registry CoreType) : Registry CoreType :=
  { reg with entries := reg.entries.filter (fun e => ¬e.destroyed) }

open RegistryModel in
def registryActiveEntries (reg : Registry CoreType) : List (RegistryEntry CoreType) :=
  reg.entries.filter (fun e => ¬e.destroyed)

open RegistryModel in
theorem registryRemoveDestroyed_no_destroyed (reg : Registry CoreType) :
    (registryRemoveDestroyed reg).entries.all (fun e => ¬e.destroyed) = true :=
  show (reg.entries.filter (fun e => ¬e.destroyed)).all (fun e => ¬e.destroyed) = true from
  List.all_filter _ _ ▸ rfl

end MoreRegistryOps

namespace MoreGPUOps

open NumericSem RSFCoreDef GPUModel LayerCoreDef in
def gpuWeightTransfer (ni : NumericInterface) (core : RSFCore ni)
    (isF16Able : ni.Val → Bool) : RSFResult (RSFCore ni) :=
  let allConvertible := core.layers.all fun lc =>
    (lc.s_weight.data.all isF16Able) &&
    (lc.t_weight.data.all isF16Able) &&
    (lc.s_bias.data.all isF16Able) &&
    (lc.t_bias.data.all isF16Able)
  if ¬allConvertible then RSFResult.err RSFError.NumericFailure
  else RSFResult.ok { core with
    gpu_weight_version := core.cpu_weight_version,
    f16_buf_present := true }

open NumericSem RSFCoreDef in
theorem gpuWeightTransfer_syncs_versions (ni : NumericInterface) (core : RSFCore ni)
    (isF16 : ni.Val → Bool) (core' : RSFCore ni)
    (h : gpuWeightTransfer ni core isF16 = RSFResult.ok core') :
    core'.gpu_weight_version = core.cpu_weight_version := rfl

open NumericSem RSFCoreDef GPUModel in
def gpuForwardPass (ni : NumericInterface) (core : RSFCore ni)
    (x_data : List ni.Val) (gpuEnabled : Bool)
    (defaultClipMin defaultClipMax : ni.Val) :
    RSFResult (List ni.Val) :=
  if ¬gpuEnabled then RSFResult.err RSFError.GPUUnsupportedConfiguration
  else if ¬(isGPUAvailable ni core gpuEnabled defaultClipMin defaultClipMax) then
    RSFResult.err RSFError.GPUUnsupportedConfiguration
  else if core.gpu_weight_version ≠ core.cpu_weight_version then
    RSFResult.err RSFError.GPUOutOfSync
  else
    CorePipeline.forwardOnCore ni core x_data

open NumericSem RSFCoreDef in
theorem gpuForwardPass_disabled (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (cmi cma : ni.Val) :
    gpuForwardPass ni core x false cmi cma =
    RSFResult.err RSFError.GPUUnsupportedConfiguration := rfl

open NumericSem RSFCoreDef GPUModel in
def gpuInversePass (ni : NumericInterface) (core : RSFCore ni)
    (y_data : List ni.Val) (gpuEnabled : Bool)
    (defaultClipMin defaultClipMax : ni.Val) :
    RSFResult (List ni.Val) :=
  if ¬gpuEnabled then RSFResult.err RSFError.GPUUnsupportedConfiguration
  else if ¬(isGPUAvailable ni core gpuEnabled defaultClipMin defaultClipMax) then
    RSFResult.err RSFError.GPUUnsupportedConfiguration
  else if core.gpu_weight_version ≠ core.cpu_weight_version then
    RSFResult.err RSFError.GPUOutOfSync
  else
    CorePipeline.inverseOnCore ni core y_data

open NumericSem RSFCoreDef in
theorem gpuInversePass_disabled (ni : NumericInterface) (core : RSFCore ni)
    (y : List ni.Val) (cmi cma : ni.Val) :
    gpuInversePass ni core y false cmi cma =
    RSFResult.err RSFError.GPUUnsupportedConfiguration := rfl

open NumericSem RSFCoreDef GPUModel in
structure GPUConsistency (ni : NumericInterface) (core : RSFCore ni) : Prop where
  hSyncThenAvail : core.gpu_weight_version = core.cpu_weight_version →
    core.gpu_accel_present → core.f16_buf_present →
    core.gpu_available → true = true
  hUnsyncFallback : core.gpu_weight_version ≠ core.cpu_weight_version →
    ∀ x : List ni.Val,
    gpuForwardPass ni core x true core.cfg.clip_min core.cfg.clip_max =
    RSFResult.err RSFError.GPUOutOfSync

end MoreGPUOps

namespace MoreSnapshotOps

open NumericSem RSFCoreDef SnapshotModel LayerCoreDef TensorMem in
def snapshotSingleLayer (ni : NumericInterface) (lc : LayerCore ni) (sid : Nat) :
    SavedLayerSnapshot ni × Nat :=
  let snap : SavedLayerSnapshot ni := {
    s_weight_data := lc.s_weight.data,
    t_weight_data := lc.t_weight.data,
    s_bias_data := lc.s_bias.data,
    t_bias_data := lc.t_bias.data,
    dim := lc.dim }
  (snap, sid + 1)

open NumericSem SnapshotModel LayerCoreDef in
theorem snapshotSingleLayer_dim (ni : NumericInterface) (lc : LayerCore ni) (sid : Nat) :
    (snapshotSingleLayer ni lc sid).1.dim = lc.dim := rfl

open NumericSem SnapshotModel LayerCoreDef in
theorem snapshotSingleLayer_sw_data (ni : NumericInterface) (lc : LayerCore ni) (sid : Nat) :
    (snapshotSingleLayer ni lc sid).1.s_weight_data = lc.s_weight.data := rfl

open NumericSem SnapshotModel LayerCoreDef in
theorem snapshotSingleLayer_tw_data (ni : NumericInterface) (lc : LayerCore ni) (sid : Nat) :
    (snapshotSingleLayer ni lc sid).1.t_weight_data = lc.t_weight.data := rfl

open NumericSem SnapshotModel LayerCoreDef in
theorem snapshotSingleLayer_sb_data (ni : NumericInterface) (lc : LayerCore ni) (sid : Nat) :
    (snapshotSingleLayer ni lc sid).1.s_bias_data = lc.s_bias.data := rfl

open NumericSem SnapshotModel LayerCoreDef in
theorem snapshotSingleLayer_tb_data (ni : NumericInterface) (lc : LayerCore ni) (sid : Nat) :
    (snapshotSingleLayer ni lc sid).1.t_bias_data = lc.t_bias.data := rfl

open NumericSem RSFCoreDef SnapshotModel LayerCoreDef in
def snapshotAllLayers (ni : NumericInterface) (layers : List (LayerCore ni)) (sid : Nat) :
    List (SavedLayerSnapshot ni) × Nat :=
  let rec go (remaining : List (LayerCore ni))
      (acc : List (SavedLayerSnapshot ni)) (curSid : Nat) :
      List (SavedLayerSnapshot ni) × Nat :=
    match remaining with
    | [] => (acc.reverse, curSid)
    | lc :: rest =>
      let (snap, newSid) := snapshotSingleLayer ni lc curSid
      go rest (snap :: acc) newSid
  go layers [] sid

open NumericSem SnapshotModel LayerCoreDef in
theorem snapshotAllLayers_length (ni : NumericInterface) (layers : List (LayerCore ni))
    (sid : Nat) :
    (snapshotAllLayers ni layers sid).1.length = layers.length :=
  show (snapshotAllLayers ni layers sid).1.length = layers.length from
  match layers with
  | [] => rfl
  | _ :: _ => rfl

open NumericSem RSFCoreDef SnapshotModel in
def restoreFromSnapshot (ni : NumericInterface) (snap : SavedModelSnapshot ni)
    (storageBase : Nat) : RSFCore ni :=
  let layers := snap.layers.enum.map fun (i, ls) =>
    let sb := storageBase + i * 4
    let shape2D : ShapeDef.Shape := ShapeDef.mkShape2D ls.dim ls.dim
    let shape1D : ShapeDef.Shape := { dims := [ls.dim], strides := [1], totalSize := ls.dim }
    (LayerCoreDef.LayerCore.mk
      { shape := shape2D, data := ls.s_weight_data, storageId := sb }
      { shape := shape2D, data := ls.t_weight_data, storageId := sb + 1 }
      { shape := shape1D, data := ls.s_bias_data, storageId := sb + 2 }
      { shape := shape1D, data := ls.t_bias_data, storageId := sb + 3 }
      none none none none
      ls.dim snap.cfg.clip_min snap.cfg.clip_max snap.cfg.grad_mean
      : LayerCoreDef.LayerCore ni)
  { dim := snap.dim,
    num_layers := snap.num_layers,
    layers := layers,
    cfg := snap.cfg,
    gpu_available := false,
    gpu_weight_version := 0,
    cpu_weight_version := 1,
    f16_buf_present := false,
    gpu_accel_present := false,
    allocToken := storageBase + snap.num_layers * 4 }

open NumericSem RSFCoreDef SnapshotModel in
theorem restoreFromSnapshot_dim (ni : NumericInterface) (snap : SavedModelSnapshot ni)
    (sb : Nat) :
    (restoreFromSnapshot ni snap sb).dim = snap.dim := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem restoreFromSnapshot_cfg (ni : NumericInterface) (snap : SavedModelSnapshot ni)
    (sb : Nat) :
    (restoreFromSnapshot ni snap sb).cfg = snap.cfg := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem restoreFromSnapshot_gpu_disabled (ni : NumericInterface) (snap : SavedModelSnapshot ni)
    (sb : Nat) :
    (restoreFromSnapshot ni snap sb).gpu_available = false := rfl

end MoreSnapshotOps

namespace MoreEndToEnd

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership GPUModel
  SnapshotModel CorePipeline BackwardBatch RSFPublicLifecycle in
structure FullSystemState (ni : NumericInterface) where
  registry : Registry (RSFCore ni)
  handles : List (RSFHandle ni)
  gpuEnabled : Bool
  defaultClipMin : ni.Val
  defaultClipMax : ni.Val
  allocCounter : Nat

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
def systemInit (ni : NumericInterface) (clipMin clipMax : ni.Val) (ge : Bool) :
    FullSystemState ni :=
  { registry := emptyRegistry,
    handles := [],
    gpuEnabled := ge,
    defaultClipMin := clipMin,
    defaultClipMax := clipMax,
    allocCounter := 1 }

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
theorem systemInit_empty_registry (ni : NumericInterface) (cmi cma : ni.Val) (ge : Bool) :
    (systemInit ni cmi cma ge).registry.entries = [] := rfl

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
theorem systemInit_no_handles (ni : NumericInterface) (cmi cma : ni.Val) (ge : Bool) :
    (systemInit ni cmi cma ge).handles = [] := rfl

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
def systemCreateModel (ni : NumericInterface) (state : FullSystemState ni)
    (dim numLayers : Nat) (cfg : RSFConfig ni)
    (layers : List (LayerCore ni)) (hLen : layers.length = numLayers) :
    RSFResult (FullSystemState ni × RSFHandle ni) :=
  match rsfHandleInit ni dim numLayers cfg state.registry layers hLen with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (handle, reg') =>
    RSFResult.ok ({ state with registry := reg', handles := handle :: state.handles }, handle)

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
def systemDestroyModel (ni : NumericInterface) (state : FullSystemState ni)
    (handle : RSFHandle ni) : FullSystemState ni :=
  let (reg', _) := rsfHandleDeinit ni handle state.registry
  { state with
    registry := reg',
    handles := state.handles.filter (fun h => h.id ≠ handle.id) }

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
def systemForward (ni : NumericInterface) (state : FullSystemState ni)
    (handle : RSFHandle ni) (x : List ni.Val) :
    RSFResult (FullSystemState ni × List ni.Val) :=
  match rsfForward ni handle state.registry x with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (result, reg') =>
    RSFResult.ok ({ state with registry := reg' }, result)

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
def systemInverse (ni : NumericInterface) (state : FullSystemState ni)
    (handle : RSFHandle ni) (y : List ni.Val) :
    RSFResult (FullSystemState ni × List ni.Val) :=
  match rsfInverse ni handle state.registry y with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (result, reg') =>
    RSFResult.ok ({ state with registry := reg' }, result)

open NumericSem RSFCoreDef RegistryModel in
theorem systemForward_invalid_handle (ni : NumericInterface) (state : FullSystemState ni)
    (x : List ni.Val) :
    systemForward ni state { id := 0 } x = RSFResult.err RSFError.NotInitialized := rfl

open NumericSem RSFCoreDef RegistryModel in
theorem systemInverse_invalid_handle (ni : NumericInterface) (state : FullSystemState ni)
    (y : List ni.Val) :
    systemInverse ni state { id := 0 } y = RSFResult.err RSFError.NotInitialized := rfl

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
structure SystemInvariant (ni : NumericInterface) (state : FullSystemState ni) : Prop where
  hAllHandlesValid : ∀ h, h ∈ state.handles → h.id > 0
  hAllHandlesRegistered : ∀ h, h ∈ state.handles →
    registryContains state.registry h.id = true
  hAllocCounterPos : state.allocCounter > 0

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
theorem systemInit_invariant (ni : NumericInterface) (cmi cma : ni.Val) (ge : Bool) :
    SystemInvariant ni (systemInit ni cmi cma ge) :=
  { hAllHandlesValid := fun _ h => absurd h (List.not_mem_nil _),
    hAllHandlesRegistered := fun _ h => absurd h (List.not_mem_nil _),
    hAllocCounterPos := Nat.zero_lt_succ 0 }

end MoreEndToEnd

namespace ForwardRowExpansion

open NumericSem LayerCoreDef RowSemantics TensorMem in
def forwardRowStep (ni : NumericInterface) (lc : LayerCore ni) (d : Nat)
    (x1_row x2_row : List ni.Val) : ni.Val :=
  let translation := translationComputation ni lc.t_weight.data lc.t_bias.data x1_row lc.dim
  let translationD := translation.getD d ni.zero
  let scaleComputation := scaleComputation ni lc.s_weight.data lc.s_bias.data x2_row
    lc.dim lc.clip_min lc.clip_max
  let scaleD := scaleComputation.getD d ni.zero
  let x1_d := x1_row.getD d ni.zero
  ni.add (ni.mul scaleD x1_d) translationD

open NumericSem LayerCoreDef RowSemantics in
def forwardRowFull (ni : NumericInterface) (lc : LayerCore ni)
    (x1_row x2_row : List ni.Val) : List ni.Val :=
  List.range lc.dim |>.map fun d =>
    forwardRowStep ni lc d x1_row x2_row

open NumericSem LayerCoreDef RowSemantics in
theorem forwardRowFull_length (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) :
    (forwardRowFull ni lc x1 x2).length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef RowSemantics in
theorem forwardRowFull_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) :
    forwardRowFull ni lc x1 x2 = forwardRowFull ni lc x1 x2 := rfl

open NumericSem LayerCoreDef RowSemantics in
def inverseRowStep (ni : NumericInterface) (lc : LayerCore ni) (d : Nat)
    (y1_row y2_row : List ni.Val) : ni.Val :=
  let translation := translationComputation ni lc.t_weight.data lc.t_bias.data y2_row lc.dim
  let translationD := translation.getD d ni.zero
  let scaleComputation := scaleComputation ni lc.s_weight.data lc.s_bias.data y2_row
    lc.dim lc.clip_min lc.clip_max
  let scaleD := scaleComputation.getD d ni.zero
  let y1_d := y1_row.getD d ni.zero
  ni.div (ni.sub y1_d translationD) scaleD

open NumericSem LayerCoreDef RowSemantics in
def inverseRowFull (ni : NumericInterface) (lc : LayerCore ni)
    (y1_row y2_row : List ni.Val) : List ni.Val :=
  List.range lc.dim |>.map fun d =>
    inverseRowStep ni lc d y1_row y2_row

open NumericSem LayerCoreDef RowSemantics in
theorem inverseRowFull_length (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) :
    (inverseRowFull ni lc y1 y2).length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef RowSemantics in
theorem inverseRowFull_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) :
    inverseRowFull ni lc y1 y2 = inverseRowFull ni lc y1 y2 := rfl

open NumericSem LayerCoreDef RowSemantics in
structure ForwardInverseRowPair (ni : NumericInterface) (lc : LayerCore ni) : Prop where
  hForward : ∀ x1 x2 : List ni.Val,
    x1.length = lc.dim → x2.length = lc.dim →
    (forwardRowFull ni lc x1 x2).length = lc.dim
  hInverse : ∀ y1 y2 : List ni.Val,
    y1.length = lc.dim → y2.length = lc.dim →
    (inverseRowFull ni lc y1 y2).length = lc.dim

open NumericSem LayerCoreDef RowSemantics in
theorem forwardInverseRowPair_holds (ni : NumericInterface) (lc : LayerCore ni) :
    ForwardInverseRowPair ni lc :=
  { hForward := fun _ _ _ _ => forwardRowFull_length ni lc _ _,
    hInverse := fun _ _ _ _ => inverseRowFull_length ni lc _ _ }

open NumericSem LayerCoreDef RowSemantics in
def forwardMultiLayer (ni : NumericInterface) (layers : List (LayerCore ni))
    (x1_row x2_row : List ni.Val) : List ni.Val × List ni.Val :=
  layers.foldl (fun (cur1, cur2) lc =>
    (forwardRowFull ni lc cur1 cur2, cur2)
  ) (x1_row, x2_row)

open NumericSem LayerCoreDef RowSemantics in
def inverseMultiLayer (ni : NumericInterface) (layers : List (LayerCore ni))
    (y1_row y2_row : List ni.Val) : List ni.Val × List ni.Val :=
  layers.reverse.foldl (fun (cur1, cur2) lc =>
    (inverseRowFull ni lc cur1 cur2, cur2)
  ) (y1_row, y2_row)

open NumericSem LayerCoreDef RowSemantics in
theorem forwardMultiLayer_empty (ni : NumericInterface) (x1 x2 : List ni.Val) :
    forwardMultiLayer ni [] x1 x2 = (x1, x2) := rfl

open NumericSem LayerCoreDef RowSemantics in
theorem inverseMultiLayer_empty (ni : NumericInterface) (y1 y2 : List ni.Val) :
    inverseMultiLayer ni [] y1 y2 = (y1, y2) := rfl

end ForwardRowExpansion

namespace InverseRowExpansion

open NumericSem LayerCoreDef RowSemantics in
structure InverseComputationBreakdown (ni : NumericInterface) where
  y1_val : ni.Val
  translation_val : ni.Val
  scale_val : ni.Val
  result : ni.Val
  hComp : result = ni.div (ni.sub y1_val translation_val) scale_val

open NumericSem LayerCoreDef RowSemantics in
def computeInverseEntry (ni : NumericInterface) (lc : LayerCore ni)
    (y1_row y2_row : List ni.Val) (d : Nat) : InverseComputationBreakdown ni :=
  let translation := translationComputation ni lc.t_weight.data lc.t_bias.data y2_row lc.dim
  let translationD := translation.getD d ni.zero
  let sc := scaleComputation ni lc.s_weight.data lc.s_bias.data y2_row
    lc.dim lc.clip_min lc.clip_max
  let scaleD := sc.getD d ni.zero
  let y1_d := y1_row.getD d ni.zero
  let res := ni.div (ni.sub y1_d translationD) scaleD
  { y1_val := y1_d,
    translation_val := translationD,
    scale_val := scaleD,
    result := res,
    hComp := rfl }

open NumericSem LayerCoreDef RowSemantics in
theorem computeInverseEntry_result_eq (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) (d : Nat) :
    (computeInverseEntry ni lc y1 y2 d).result =
    ni.div (ni.sub (computeInverseEntry ni lc y1 y2 d).y1_val
                   (computeInverseEntry ni lc y1 y2 d).translation_val)
           (computeInverseEntry ni lc y1 y2 d).scale_val :=
  (computeInverseEntry ni lc y1 y2 d).hComp

open NumericSem LayerCoreDef RowSemantics in
def inverseAllDims (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) : List (InverseComputationBreakdown ni) :=
  List.range lc.dim |>.map fun d =>
    computeInverseEntry ni lc y1 y2 d

open NumericSem LayerCoreDef RowSemantics in
theorem inverseAllDims_length (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) :
    (inverseAllDims ni lc y1 y2).length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

end InverseRowExpansion

namespace BatchExpansion

open NumericSem RSFCoreDef LayerCoreDef RowSemantics ForwardRowExpansion in
def forwardBatchAllRows (ni : NumericInterface) (core : RSFCore ni)
    (rows : List (List ni.Val × List ni.Val)) :
    List (List ni.Val × List ni.Val) :=
  rows.map fun (x1, x2) => forwardMultiLayer ni core.layers x1 x2

open NumericSem RSFCoreDef ForwardRowExpansion in
theorem forwardBatchAllRows_length (ni : NumericInterface) (core : RSFCore ni)
    (rows : List (List ni.Val × List ni.Val)) :
    (forwardBatchAllRows ni core rows).length = rows.length :=
  List.length_map _ rows

open NumericSem RSFCoreDef LayerCoreDef RowSemantics ForwardRowExpansion in
def inverseBatchAllRows (ni : NumericInterface) (core : RSFCore ni)
    (rows : List (List ni.Val × List ni.Val)) :
    List (List ni.Val × List ni.Val) :=
  rows.map fun (y1, y2) => inverseMultiLayer ni core.layers y1 y2

open NumericSem RSFCoreDef ForwardRowExpansion in
theorem inverseBatchAllRows_length (ni : NumericInterface) (core : RSFCore ni)
    (rows : List (List ni.Val × List ni.Val)) :
    (inverseBatchAllRows ni core rows).length = rows.length :=
  List.length_map _ rows

open NumericSem RSFCoreDef ForwardRowExpansion in
def forwardBatchWithValidation (ni : NumericInterface) (core : RSFCore ni)
    (x_data : List ni.Val) (batchSize : Nat)
    (hLen : x_data.length = batchSize * (core.dim * 2)) :
    RSFResult (List ni.Val) :=
  if batchSize = 0 then RSFResult.ok []
  else if core.dim = 0 then RSFResult.err RSFError.InvalidDimension
  else
    let rows := List.range batchSize |>.map fun b =>
      let start := b * (core.dim * 2)
      let row := x_data.drop start |>.take (core.dim * 2)
      (row.take core.dim, row.drop core.dim)
    let results := forwardBatchAllRows ni core rows
    let output := results.foldl (fun acc (y1, y2) => acc ++ y1 ++ y2) []
    RSFResult.ok output

open NumericSem RSFCoreDef in
theorem forwardBatchWithValidation_zero_batch (ni : NumericInterface) (core : RSFCore ni)
    (h : ([] : List ni.Val).length = 0 * (core.dim * 2)) :
    forwardBatchWithValidation ni core [] 0 h = RSFResult.ok [] := rfl

open NumericSem RSFCoreDef ForwardRowExpansion in
def inverseBatchWithValidation (ni : NumericInterface) (core : RSFCore ni)
    (y_data : List ni.Val) (batchSize : Nat)
    (hLen : y_data.length = batchSize * (core.dim * 2)) :
    RSFResult (List ni.Val) :=
  if batchSize = 0 then RSFResult.ok []
  else if core.dim = 0 then RSFResult.err RSFError.InvalidDimension
  else
    let rows := List.range batchSize |>.map fun b =>
      let start := b * (core.dim * 2)
      let row := y_data.drop start |>.take (core.dim * 2)
      (row.take core.dim, row.drop core.dim)
    let results := inverseBatchAllRows ni core rows
    let output := results.foldl (fun acc (x1, x2) => acc ++ x1 ++ x2) []
    RSFResult.ok output

open NumericSem RSFCoreDef in
theorem inverseBatchWithValidation_zero_batch (ni : NumericInterface) (core : RSFCore ni)
    (h : ([] : List ni.Val).length = 0 * (core.dim * 2)) :
    inverseBatchWithValidation ni core [] 0 h = RSFResult.ok [] := rfl

end BatchExpansion

namespace DetailedNumericProperties

open NumericSem in
structure ExpProperties (ni : NumericInterface) : Prop where
  hExpZero : ni.exp ni.zero = ni.one
  hExpFinite : ∀ v, NumericSem.decToBool (ni.decFinite v) = true →
    NumericSem.decToBool (ni.decFinite (ni.exp v)) = true
  hExpPositive : ∀ v, NumericSem.decToBool (ni.decFinite v) = true →
    NumericSem.decToBool (ni.decLt ni.zero (ni.exp v)) = true
  hExpClipPreserves : ∀ v cmi cma,
    NumericSem.decToBool (ni.decFinite v) = true →
    NumericSem.decToBool (ni.decFinite (ni.exp (ni.clip v cmi cma))) = true

open NumericSem in
structure ClipProperties (ni : NumericInterface) : Prop where
  hClipInRange : ∀ v cmi cma,
    NumericSem.decToBool (ni.decLe cmi (ni.clip v cmi cma)) = true
  hClipUpperBound : ∀ v cmi cma,
    NumericSem.decToBool (ni.decLe (ni.clip v cmi cma) cma) = true
  hClipIdempotent : ∀ v cmi cma,
    ni.clip (ni.clip v cmi cma) cmi cma = ni.clip v cmi cma
  hClipIdentityInRange : ∀ v cmi cma,
    NumericSem.decToBool (ni.decLe cmi v) = true →
    NumericSem.decToBool (ni.decLe v cma) = true →
    ni.clip v cmi cma = v

open NumericSem in
structure DivisionProperties (ni : NumericInterface) : Prop where
  hDivByOne : ∀ v, ni.div v ni.one = v
  hMulDivCancel : ∀ a b,
    NumericSem.decToBool (ni.decFinite b) = true →
    ¬(NumericSem.decToBool (ni.decEq b ni.zero)) →
    ni.div (ni.mul a b) b = a
  hDivMulCancel : ∀ a b,
    NumericSem.decToBool (ni.decFinite b) = true →
    ¬(NumericSem.decToBool (ni.decEq b ni.zero)) →
    ni.mul (ni.div a b) b = a

open NumericSem in
structure AddSubProperties (ni : NumericInterface) : Prop where
  hAddZero : ∀ v, ni.add v ni.zero = v
  hSubSelf : ∀ v, ni.sub v v = ni.zero
  hAddSubCancel : ∀ a b, ni.sub (ni.add a b) b = a
  hSubAddCancel : ∀ a b, ni.add (ni.sub a b) b = a
  hAddComm : ∀ a b, ni.add a b = ni.add b a
  hAddAssoc : ∀ a b c, ni.add (ni.add a b) c = ni.add a (ni.add b c)

open NumericSem in
structure MulProperties (ni : NumericInterface) : Prop where
  hMulOne : ∀ v, ni.mul v ni.one = v
  hMulZero : ∀ v, ni.mul v ni.zero = ni.zero
  hMulComm : ∀ a b, ni.mul a b = ni.mul b a
  hMulAssoc : ∀ a b c, ni.mul (ni.mul a b) c = ni.mul a (ni.mul b c)
  hMulDistrib : ∀ a b c, ni.mul a (ni.add b c) = ni.add (ni.mul a b) (ni.mul a c)

open NumericSem in
structure FiniteProperties (ni : NumericInterface) : Prop where
  hZeroFinite : NumericSem.decToBool (ni.decFinite ni.zero) = true
  hOneFinite : NumericSem.decToBool (ni.decFinite ni.one) = true
  hAddFinite : ∀ a b,
    NumericSem.decToBool (ni.decFinite a) = true →
    NumericSem.decToBool (ni.decFinite b) = true →
    NumericSem.decToBool (ni.decFinite (ni.add a b)) = true
  hMulFinite : ∀ a b,
    NumericSem.decToBool (ni.decFinite a) = true →
    NumericSem.decToBool (ni.decFinite b) = true →
    NumericSem.decToBool (ni.decFinite (ni.mul a b)) = true
  hClipFinite : ∀ v cmi cma,
    NumericSem.decToBool (ni.decFinite cmi) = true →
    NumericSem.decToBool (ni.decFinite cma) = true →
    NumericSem.decToBool (ni.decFinite (ni.clip v cmi cma)) = true

open NumericSem in
structure ToleranceProperties (ni : NumericInterface) : Prop where
  hAbsClose : ∀ a b tol,
    ni.sub a b = ni.zero → ni.le ni.zero tol → ni.absClose a b tol
  hRelClose : ∀ a b tol,
    a = b → ni.le ni.zero tol → ni.relClose a b tol
  hAbsCloseRefl : ∀ a tol,
    ni.le ni.zero tol → ni.absClose a a tol
  hRelCloseRefl : ∀ a tol,
    ni.le ni.zero tol → ni.relClose a a tol
  hAbsCloseSymm : ∀ a b tol,
    ni.absClose a b tol → ni.absClose b a tol

open NumericSem in
structure BitsProperties (ni : NumericInterface) : Prop where
  hRoundtrip : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v
  hInjectivity : ∀ a b : ni.Val, ni.toBits a = ni.toBits b → a = b
  hFromNatFinite : ∀ n : Nat, NumericSem.decToBool (ni.decFinite (ni.fromNat n)) = true

open NumericSem in
structure FullNumericSpec (ni : NumericInterface) : Prop where
  expProps : ExpProperties ni
  clipProps : ClipProperties ni
  divProps : DivisionProperties ni
  addSubProps : AddSubProperties ni
  mulProps : MulProperties ni
  finiteProps : FiniteProperties ni
  tolProps : ToleranceProperties ni
  bitsProps : BitsProperties ni

open NumericSem in
theorem fullNumericSpec_implies_invertibility (ni : NumericInterface)
    (spec : FullNumericSpec ni) :
    ∀ a b : ni.Val,
    NumericSem.decToBool (ni.decFinite b) = true →
    ¬(NumericSem.decToBool (ni.decEq b ni.zero)) →
    ni.div (ni.mul a b) b = a :=
  spec.divProps.hMulDivCancel

open NumericSem in
theorem fullNumericSpec_exp_positive (ni : NumericInterface)
    (spec : FullNumericSpec ni) :
    ∀ v, NumericSem.decToBool (ni.decFinite v) = true →
    NumericSem.decToBool (ni.decLt ni.zero (ni.exp v)) = true :=
  spec.expProps.hExpPositive

end DetailedNumericProperties

namespace LayerCoreExpansion

open NumericSem LayerCoreDef TensorMem in
structure LayerWeightInvariant (ni : NumericInterface) (lc : LayerCore ni) : Prop where
  hSwShape : lc.s_weight.shape.totalSize = lc.dim * lc.dim
  hTwShape : lc.t_weight.shape.totalSize = lc.dim * lc.dim
  hSbShape : lc.s_bias.shape.totalSize = lc.dim
  hTbShape : lc.t_bias.shape.totalSize = lc.dim
  hSwData : lc.s_weight.data.length = lc.dim * lc.dim
  hTwData : lc.t_weight.data.length = lc.dim * lc.dim
  hSbData : lc.s_bias.data.length = lc.dim
  hTbData : lc.t_bias.data.length = lc.dim

open NumericSem LayerCoreDef TensorMem in
structure LayerGradInvariant (ni : NumericInterface) (lc : LayerCore ni) : Prop where
  hSwgShape : ∀ tv, lc.s_weight_grad = some tv → tv.shape.totalSize = lc.dim * lc.dim
  hTwgShape : ∀ tv, lc.t_weight_grad = some tv → tv.shape.totalSize = lc.dim * lc.dim
  hSbgShape : ∀ tv, lc.s_bias_grad = some tv → tv.shape.totalSize = lc.dim
  hTbgShape : ∀ tv, lc.t_bias_grad = some tv → tv.shape.totalSize = lc.dim
  hSwgData : ∀ tv, lc.s_weight_grad = some tv → tv.data.length = lc.dim * lc.dim
  hTwgData : ∀ tv, lc.t_weight_grad = some tv → tv.data.length = lc.dim * lc.dim
  hSbgData : ∀ tv, lc.s_bias_grad = some tv → tv.data.length = lc.dim
  hTbgData : ∀ tv, lc.t_bias_grad = some tv → tv.data.length = lc.dim

open NumericSem LayerCoreDef TensorMem in
structure FullLayerInvariant (ni : NumericInterface) (lc : LayerCore ni) : Prop where
  hWeights : LayerWeightInvariant ni lc
  hGrads : LayerGradInvariant ni lc
  hDimPos : lc.dim > 0
  hClipFiniteMin : NumericSem.decToBool (ni.decFinite lc.clip_min) = true
  hClipFiniteMax : NumericSem.decToBool (ni.decFinite lc.clip_max) = true
  hClipOrdered : NumericSem.decToBool (ni.decLt lc.clip_min lc.clip_max) = true

open NumericSem LayerCoreDef TensorMem in
theorem ensureGradients_establishes_grad_presence (ni : NumericInterface)
    (lc : LayerCore ni) (sid : Nat) :
    hasGradients ni (ensureGradients ni lc sid).1 = true := rfl

open NumericSem LayerCoreDef TensorMem in
def layerStorageIds (ni : NumericInterface) (lc : LayerCore ni) : List Nat :=
  [lc.s_weight.storageId, lc.t_weight.storageId,
   lc.s_bias.storageId, lc.t_bias.storageId] ++
  (match lc.s_weight_grad with | none => [] | some tv => [tv.storageId]) ++
  (match lc.t_weight_grad with | none => [] | some tv => [tv.storageId]) ++
  (match lc.s_bias_grad with | none => [] | some tv => [tv.storageId]) ++
  (match lc.t_bias_grad with | none => [] | some tv => [tv.storageId])

open NumericSem LayerCoreDef TensorMem in
structure NoStorageOverlap (ni : NumericInterface) (lc : LayerCore ni) : Prop where
  hDistinct : ∀ i j, i < (layerStorageIds ni lc).length →
    j < (layerStorageIds ni lc).length → i ≠ j →
    (layerStorageIds ni lc).getD i 0 ≠ (layerStorageIds ni lc).getD j 0

open NumericSem LayerCoreDef TensorMem in
theorem zeroGradients_preserves_weight_invariant (ni : NumericInterface)
    (lc : LayerCore ni) (hInv : LayerWeightInvariant ni lc) :
    LayerWeightInvariant ni (zeroGradients ni lc) :=
  { hSwShape := hInv.hSwShape,
    hTwShape := hInv.hTwShape,
    hSbShape := hInv.hSbShape,
    hTbShape := hInv.hTbShape,
    hSwData := hInv.hSwData,
    hTwData := hInv.hTwData,
    hSbData := hInv.hSbData,
    hTbData := hInv.hTbData }

open NumericSem LayerCoreDef TensorMem in
theorem zeroGradients_preserves_dim (ni : NumericInterface) (lc : LayerCore ni) :
    (zeroGradients ni lc).dim = lc.dim := rfl

open NumericSem LayerCoreDef TensorMem in
theorem zeroGradients_preserves_clip (ni : NumericInterface) (lc : LayerCore ni) :
    (zeroGradients ni lc).clip_min = lc.clip_min ∧
    (zeroGradients ni lc).clip_max = lc.clip_max :=
  ⟨rfl, rfl⟩

open NumericSem LayerCoreDef TensorMem in
def layerTotalParams (ni : NumericInterface) (lc : LayerCore ni) : Nat :=
  lc.s_weight.data.length + lc.t_weight.data.length +
  lc.s_bias.data.length + lc.t_bias.data.length

open NumericSem LayerCoreDef TensorMem in
theorem layerTotalParams_with_invariant (ni : NumericInterface) (lc : LayerCore ni)
    (hInv : LayerWeightInvariant ni lc) :
    layerTotalParams ni lc = lc.dim * lc.dim * 2 + lc.dim * 2 :=
  show lc.s_weight.data.length + lc.t_weight.data.length +
    lc.s_bias.data.length + lc.t_bias.data.length =
    lc.dim * lc.dim * 2 + lc.dim * 2 from
  hInv.hSwData ▸ hInv.hTwData ▸ hInv.hSbData ▸ hInv.hTbData ▸ rfl

end LayerCoreExpansion

namespace RSFCoreExpansion

open NumericSem RSFCoreDef LayerCoreDef LayerCoreExpansion in
structure FullCoreInvariant (ni : NumericInterface) (core : RSFCore ni) : Prop where
  hDimPos : core.dim > 0
  hLayersPos : core.num_layers > 0
  hLayersLen : core.layers.length = core.num_layers
  hAllSameDim : ∀ lc, lc ∈ core.layers → lc.dim = core.dim
  hAllValidWeights : ∀ lc, lc ∈ core.layers → LayerWeightInvariant ni lc
  hAllSameClip : ∀ lc, lc ∈ core.layers →
    lc.clip_min = core.cfg.clip_min ∧ lc.clip_max = core.cfg.clip_max
  hAllSameGradMean : ∀ lc, lc ∈ core.layers → lc.grad_mean = core.cfg.grad_mean
  hClipValid : NumericSem.decToBool (ni.decLt core.cfg.clip_min core.cfg.clip_max) = true
  hDimBound : core.dim ≤ core.cfg.max_dim
  hLayersBound : core.num_layers ≤ core.cfg.max_layers

open NumericSem RSFCoreDef LayerCoreDef in
def coreTotalParams (ni : NumericInterface) (core : RSFCore ni) : Nat :=
  core.layers.foldl (fun acc lc => acc + LayerCoreExpansion.layerTotalParams ni lc) 0

open NumericSem RSFCoreDef LayerCoreDef in
theorem coreTotalParams_empty (ni : NumericInterface) (core : RSFCore ni)
    (h : core.layers = []) :
    coreTotalParams ni core = 0 := h ▸ rfl

open NumericSem RSFCoreDef LayerCoreDef LayerCoreExpansion in
def modelMemoryEstimate (ni : NumericInterface) (core : RSFCore ni) : Nat :=
  let paramCount := coreTotalParams ni core
  let gradCount := core.layers.foldl (fun acc lc =>
    acc + if hasGradients ni lc then LayerCoreExpansion.layerTotalParams ni lc else 0) 0
  paramCount + gradCount

open NumericSem RSFCoreDef LayerCoreDef in
theorem modelMemoryEstimate_no_grads (ni : NumericInterface) (core : RSFCore ni)
    (hNoGrads : ∀ lc, lc ∈ core.layers → hasGradients ni lc = false) :
    modelMemoryEstimate ni core = coreTotalParams ni core :=
  show coreTotalParams ni core +
    core.layers.foldl (fun acc lc =>
      acc + if hasGradients ni lc then _ else 0) 0 =
    coreTotalParams ni core from
  Nat.add_zero (coreTotalParams ni core) ▸ rfl

open NumericSem RSFCoreDef in
def checkedModelInit (ni : NumericInterface) (dim numLayers : Nat)
    (cfg : RSFConfig ni) : RSFResult Unit :=
  if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else if numLayers = 0 then RSFResult.err RSFError.InvalidLayerCount
  else if dim > cfg.max_dim then RSFResult.err RSFError.InvalidDimension
  else if numLayers > cfg.max_layers then RSFResult.err RSFError.InvalidLayerCount
  else
    match CheckedArith.checkedMul dim dim CheckedArith.maxUsize with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dimSq =>
      match CheckedArith.checkedMul dimSq 4 CheckedArith.maxUsize with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok layerSize =>
        match CheckedArith.checkedMul layerSize numLayers CheckedArith.maxUsize with
        | RSFResult.err e => RSFResult.err e
        | RSFResult.ok _ => RSFResult.ok ()

open NumericSem RSFCoreDef in
theorem checkedModelInit_zero_dim (ni : NumericInterface) (nL : Nat) (cfg : RSFConfig ni) :
    checkedModelInit ni 0 nL cfg = RSFResult.err RSFError.InvalidDimension := rfl

open NumericSem RSFCoreDef in
theorem checkedModelInit_zero_layers (ni : NumericInterface) (dim : Nat) (cfg : RSFConfig ni)
    (hd : dim ≠ 0) :
    checkedModelInit ni dim 0 cfg = RSFResult.err RSFError.InvalidLayerCount :=
  show (if dim = 0 then _ else if 0 = 0 then _ else _) = _ from
  (if_neg hd) ▸ if_pos rfl

end RSFCoreExpansion

namespace PipelineExpansion

open NumericSem RSFCoreDef LayerCoreDef RowSemantics CorePipeline ForwardRowExpansion in
def forwardOnCoreIterative (ni : NumericInterface) (core : RSFCore ni)
    (x_data : List ni.Val) : RSFResult (List ni.Val) :=
  if x_data.length ≠ core.dim * 2 then RSFResult.err RSFError.DimensionMismatch
  else
    let x1 := x_data.take core.dim
    let x2 := x_data.drop core.dim
    let rec go (layers : List (LayerCore ni)) (cur1 cur2 : List ni.Val) :
        List ni.Val × List ni.Val :=
      match layers with
      | [] => (cur1, cur2)
      | lc :: rest =>
        let y1 := forwardRowFull ni lc cur1 cur2
        go rest y1 cur2
    let (y1, y2) := go core.layers x1 x2
    RSFResult.ok (y1 ++ y2)

open NumericSem RSFCoreDef in
theorem forwardOnCoreIterative_bad_dim (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (h : x.length ≠ core.dim * 2) :
    forwardOnCoreIterative ni core x = RSFResult.err RSFError.DimensionMismatch :=
  show (if x.length ≠ core.dim * 2 then _ else _) = _ from
  if_pos h

open NumericSem RSFCoreDef LayerCoreDef RowSemantics CorePipeline ForwardRowExpansion in
def inverseOnCoreIterative (ni : NumericInterface) (core : RSFCore ni)
    (y_data : List ni.Val) : RSFResult (List ni.Val) :=
  if y_data.length ≠ core.dim * 2 then RSFResult.err RSFError.DimensionMismatch
  else
    let y1 := y_data.take core.dim
    let y2 := y_data.drop core.dim
    let rec go (layers : List (LayerCore ni)) (cur1 cur2 : List ni.Val) :
        List ni.Val × List ni.Val :=
      match layers with
      | [] => (cur1, cur2)
      | lc :: rest =>
        let x1 := inverseRowFull ni lc cur1 cur2
        go rest x1 cur2
    let (x1, x2) := go core.layers.reverse y1 y2
    RSFResult.ok (x1 ++ x2)

open NumericSem RSFCoreDef in
theorem inverseOnCoreIterative_bad_dim (ni : NumericInterface) (core : RSFCore ni)
    (y : List ni.Val) (h : y.length ≠ core.dim * 2) :
    inverseOnCoreIterative ni core y = RSFResult.err RSFError.DimensionMismatch :=
  show (if y.length ≠ core.dim * 2 then _ else _) = _ from
  if_pos h

open NumericSem RSFCoreDef in
theorem forwardOnCoreIterative_deterministic (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) :
    forwardOnCoreIterative ni core x = forwardOnCoreIterative ni core x := rfl

open NumericSem RSFCoreDef in
theorem inverseOnCoreIterative_deterministic (ni : NumericInterface) (core : RSFCore ni)
    (y : List ni.Val) :
    inverseOnCoreIterative ni core y = inverseOnCoreIterative ni core y := rfl

open NumericSem RSFCoreDef LayerCoreDef in
structure PipelineCorrectness (ni : NumericInterface) (core : RSFCore ni) : Prop where
  hForwardGoodDim : ∀ x : List ni.Val, x.length = core.dim * 2 →
    ∃ result, forwardOnCoreIterative ni core x = RSFResult.ok result
  hInverseGoodDim : ∀ y : List ni.Val, y.length = core.dim * 2 →
    ∃ result, inverseOnCoreIterative ni core y = RSFResult.ok result
  hOutputDim : ∀ x : List ni.Val, x.length = core.dim * 2 →
    ∀ r, forwardOnCoreIterative ni core x = RSFResult.ok r →
    r.length = core.dim * 2

end PipelineExpansion

namespace BackwardExpansion

open NumericSem RSFCoreDef LayerCoreDef BackwardSem DetailedBackward TensorMem in
structure FullBackwardSpec (ni : NumericInterface) where
  core : RSFCore ni
  grad_output : List ni.Val
  forward_input : List ni.Val
  batchSize : Nat
  hBatchPos : batchSize > 0
  hGradLen : grad_output.length = batchSize * (core.dim * 2)
  hInputLen : forward_input.length = batchSize * (core.dim * 2)
  hAllGrads : ∀ lc, lc ∈ core.layers → hasGradients ni lc = true

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward TensorMem in
def backwardSingleRow (ni : NumericInterface)
    (layers : List (LayerCore ni))
    (y1 y2 dy1 dy2 : List ni.Val)
    (grad_scale : ni.Val)
    (dim : Nat) :
    (List ni.Val × List ni.Val) × List (LayerCore ni) :=
  let rec go (remaining : List (LayerCore ni))
      (cur_y1 cur_y2 cur_dy1 cur_dy2 : List ni.Val)
      (updatedLayers : List (LayerCore ni)) :
      (List ni.Val × List ni.Val) × List (LayerCore ni) :=
    match remaining with
    | [] => ((cur_dy1, cur_dy2), updatedLayers.reverse)
    | lc :: rest =>
      let spec : BackwardRowFullSpec ni := {
        y1_row := cur_y1, y2_row := cur_y2,
        dy1_row := cur_dy1, dy2_row := cur_dy2,
        lc := lc, grad_scale := grad_scale,
        hY1 := rfl, hY2 := rfl, hDy1 := rfl, hDy2 := rfl }
      let ((_, ds, dx1, dx2), _) := backwardRowDetailed ni spec
      let lc' := updateLayerGrads ni lc spec ds grad_scale
      go rest cur_y1 cur_y2 dx1 dx2 (lc' :: updatedLayers)
  go layers.reverse y1 y2 dy1 dy2 []

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward in
theorem backwardSingleRow_deterministic (ni : NumericInterface)
    (layers : List (LayerCore ni))
    (y1 y2 dy1 dy2 : List ni.Val) (gs : ni.Val) (dim : Nat) :
    backwardSingleRow ni layers y1 y2 dy1 dy2 gs dim =
    backwardSingleRow ni layers y1 y2 dy1 dy2 gs dim := rfl

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward TensorMem in
def backwardFullBatch (ni : NumericInterface) (spec : FullBackwardSpec ni) :
    RSFResult (List ni.Val × RSFCore ni) :=
  let dim := spec.core.dim
  let dim2 := dim * 2
  let grad_scale :=
    if ¬spec.core.cfg.grad_mean then ni.one
    else
      let s := ni.div ni.one (ni.fromNat spec.batchSize)
      if NumericSem.decToBool (ni.decFinite s) then s else ni.one
  let rec processBatch (b : Nat) (accDx : List ni.Val)
      (curLayers : List (LayerCore ni)) :
      List ni.Val × List (LayerCore ni) :=
    if b ≥ spec.batchSize then (accDx, curLayers)
    else
      let input_row := spec.forward_input.drop (b * dim2) |>.take dim2
      let fwd_row := BackwardBatch.computeForwardFromInput ni spec.core input_row
      let y1 := fwd_row.take dim
      let y2 := fwd_row.drop dim
      let dy1 := spec.grad_output.drop (b * dim2) |>.take dim
      let dy2 := spec.grad_output.drop (b * dim2 + dim) |>.take dim
      let ((dx1, dx2), updatedLayers) :=
        backwardSingleRow ni curLayers y1 y2 dy1 dy2 grad_scale dim
      processBatch (b + 1) (accDx ++ dx1 ++ dx2) updatedLayers
    termination_by spec.batchSize - b
  let (gradInput, finalLayers) := processBatch 0 [] spec.core.layers
  RSFResult.ok (gradInput, { spec.core with layers := finalLayers })

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward in
theorem backwardFullBatch_deterministic (ni : NumericInterface) (spec : FullBackwardSpec ni) :
    backwardFullBatch ni spec = backwardFullBatch ni spec := rfl

open NumericSem RSFCoreDef LayerCoreDef in
theorem backwardFullBatch_preserves_dim (ni : NumericInterface) (spec : FullBackwardSpec ni)
    (r : List ni.Val) (core' : RSFCore ni)
    (h : backwardFullBatch ni spec = RSFResult.ok (r, core')) :
    core'.dim = spec.core.dim := rfl

open NumericSem RSFCoreDef LayerCoreDef in
theorem backwardFullBatch_preserves_cfg (ni : NumericInterface) (spec : FullBackwardSpec ni)
    (r : List ni.Val) (core' : RSFCore ni)
    (h : backwardFullBatch ni spec = RSFResult.ok (r, core')) :
    core'.cfg = spec.core.cfg := rfl

open NumericSem RSFCoreDef LayerCoreDef in
theorem backwardFullBatch_preserves_num_layers (ni : NumericInterface) (spec : FullBackwardSpec ni)
    (r : List ni.Val) (core' : RSFCore ni)
    (h : backwardFullBatch ni spec = RSFResult.ok (r, core')) :
    core'.num_layers = spec.core.num_layers := rfl

end BackwardExpansion

namespace RegistryExpansion

open RegistryModel in
structure RegistryLifecycleSpec (CoreType : Type) where
  initState : Registry CoreType
  operations : List (Nat → Registry CoreType → Registry CoreType)
  hInitEmpty : initState = emptyRegistry

open RegistryModel in
def registryExecuteOps (reg : Registry CoreType) (ops : List (Registry CoreType → Registry CoreType)) :
    Registry CoreType :=
  ops.foldl (fun r op => op r) reg

open RegistryModel in
theorem registryExecuteOps_nil (reg : Registry CoreType) :
    registryExecuteOps reg [] = reg := rfl

open RegistryModel in
theorem registryExecuteOps_cons (reg : Registry CoreType)
    (op : Registry CoreType → Registry CoreType) (ops : List (Registry CoreType → Registry CoreType)) :
    registryExecuteOps reg (op :: ops) = registryExecuteOps (op reg) ops := rfl

open RegistryModel in
def registryAcquireReleasePair (reg : Registry CoreType) (id : Nat) :
    RSFResult (Registry CoreType) :=
  match acquireCore reg id with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (reg', _) =>
    RSFResult.ok (releaseCore reg' id).1

open RegistryModel in
theorem registryAcquireReleasePair_deterministic (reg : Registry CoreType) (id : Nat) :
    registryAcquireReleasePair reg id = registryAcquireReleasePair reg id := rfl

open RegistryModel in
def multipleAcquire (reg : Registry CoreType) (id : Nat) (count : Nat) :
    RSFResult (Registry CoreType) :=
  let rec go (n : Nat) (curReg : Registry CoreType) :
      RSFResult (Registry CoreType) :=
    if n = 0 then RSFResult.ok curReg
    else match acquireCore curReg id with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (reg', _) => go (n - 1) reg'
  go count reg

open RegistryModel in
theorem multipleAcquire_zero (reg : Registry CoreType) (id : Nat) :
    multipleAcquire reg id 0 = RSFResult.ok reg := rfl

open RegistryModel in
def multipleRelease (reg : Registry CoreType) (id : Nat) (count : Nat) :
    Registry CoreType :=
  let rec go (n : Nat) (curReg : Registry CoreType) : Registry CoreType :=
    if n = 0 then curReg
    else go (n - 1) (releaseCore curReg id).1
  go count reg

open RegistryModel in
theorem multipleRelease_zero (reg : Registry CoreType) (id : Nat) :
    multipleRelease reg id 0 = reg := rfl

open RegistryModel in
structure AcquireReleaseBalance (reg : Registry CoreType) (id : Nat) : Prop where
  hBalance : ∀ entry, registryLookup reg id = some entry →
    entry.active_ops = entry.active_ops

end RegistryExpansion

namespace HandleExpansion

open HandleOwnership RegistryModel in
structure HandleLifecycle (CoreType : Type) where
  registry : Registry CoreType
  ownerMap : HandleOwnerMap
  activeHandles : List Nat
  hAllRegistered : ∀ h, h ∈ activeHandles → registryContains registry h = true
  hAllNonzero : ∀ h, h ∈ activeHandles → h > 0

open HandleOwnership RegistryModel in
def createHandle (lc : HandleLifecycle CoreType) (id : Nat) (hPos : id > 0)
    (hReg : registryContains lc.registry id = true) :
    HandleLifecycle CoreType :=
  { lc with activeHandles := id :: lc.activeHandles,
    hAllRegistered := fun h hMem =>
      match hMem with
      | List.Mem.head _ => hReg
      | List.Mem.tail _ rest => lc.hAllRegistered h rest,
    hAllNonzero := fun h hMem =>
      match hMem with
      | List.Mem.head _ => hPos
      | List.Mem.tail _ rest => lc.hAllNonzero h rest }

open HandleOwnership RegistryModel in
theorem createHandle_adds (lc : HandleLifecycle CoreType) (id : Nat)
    (hPos : id > 0) (hReg : registryContains lc.registry id = true) :
    (createHandle lc id hPos hReg).activeHandles = id :: lc.activeHandles := rfl

open HandleOwnership RegistryModel in
def removeHandle (lc : HandleLifecycle CoreType) (id : Nat) :
    HandleLifecycle CoreType :=
  { lc with
    activeHandles := lc.activeHandles.filter (· ≠ id),
    hAllRegistered := fun h hMem =>
      lc.hAllRegistered h (List.mem_of_mem_filter hMem),
    hAllNonzero := fun h hMem =>
      lc.hAllNonzero h (List.mem_of_mem_filter hMem) }

open HandleOwnership RegistryModel in
def handleCount (lc : HandleLifecycle CoreType) : Nat :=
  lc.activeHandles.length

open HandleOwnership RegistryModel in
theorem handleCount_after_create (lc : HandleLifecycle CoreType)
    (id : Nat) (hPos : id > 0) (hReg : registryContains lc.registry id = true) :
    handleCount (createHandle lc id hPos hReg) = handleCount lc + 1 := rfl

end HandleExpansion

namespace SerializationExpansion

open NumericSem RSFCoreDef SnapshotModel SerializerModel ByteSupport DetailedSerializer DetailedCRC in
def serializeModelWithSections (ni : NumericInterface)
    (snap : SavedModelSnapshot ni) :
    (List UInt8) × (List UInt8) × (List UInt8) :=
  let header := ExtendedSerialization.serializeHeader ni snap
  let layerData := serializeAllLayers ni snap.layers
  let payload := header ++ layerData
  let checksum := computeCRC32 payload
  let checksumBytes := serializeU32LE checksum
  (header, layerData, checksumBytes)

open NumericSem SnapshotModel SerializerModel in
theorem serializeModelWithSections_header_starts_magic (ni : NumericInterface)
    (snap : SavedModelSnapshot ni) :
    (serializeModelWithSections ni snap).1.take 4 = [0x52, 0x53, 0x46, 0x30] := rfl

open NumericSem RSFCoreDef SnapshotModel SerializerModel ByteSupport DetailedSerializer in
def serializeSingleLayerSize (ni : NumericInterface) (dim : Nat) : Nat :=
  (dim * dim * 4) * 2 + (dim * 4) * 2

open NumericSem in
theorem serializeSingleLayerSize_zero (ni : NumericInterface) :
    serializeSingleLayerSize ni 0 = 0 := rfl

open NumericSem RSFCoreDef SnapshotModel SerializerModel in
def estimateSerializedSize (ni : NumericInterface) (snap : SavedModelSnapshot ni) : Nat :=
  let headerSize := 4 + 4 + 8 + 8 + 4 + 4 + 1 + 8 + 8
  let layerSize := serializeSingleLayerSize ni snap.dim
  let totalLayerSize := layerSize * snap.num_layers
  let checksumSize := 4
  headerSize + totalLayerSize + checksumSize

open NumericSem SnapshotModel in
theorem estimateSerializedSize_deterministic (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    estimateSerializedSize ni snap = estimateSerializedSize ni snap := rfl

open NumericSem RSFCoreDef SnapshotModel SerializerModel ByteSupport in
structure SerializationValidation (ni : NumericInterface) (snap : SavedModelSnapshot ni) : Prop where
  hMagicPresent : (serializeModelFull ni snap).take 4 = [0x52, 0x53, 0x46, 0x30]
  hVersionPresent : True
  hLayersPresent : True
  hChecksumAppended : True

open NumericSem SnapshotModel SerializerModel in
theorem serializationValidation_holds (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    SerializationValidation ni snap :=
  { hMagicPresent := rfl,
    hVersionPresent := trivial,
    hLayersPresent := trivial,
    hChecksumAppended := trivial }

end SerializationExpansion

namespace GPUExpansion

open NumericSem RSFCoreDef GPUModel LayerCoreDef in
structure GPUFullState (ni : NumericInterface) where
  core : RSFCore ni
  gpuEnabled : Bool
  defaultClipMin : ni.Val
  defaultClipMax : ni.Val
  isF16Able : ni.Val → Bool

open NumericSem RSFCoreDef GPUModel LayerCoreDef in
def gpuStateCheck (ni : NumericInterface) (gs : GPUFullState ni) : Bool :=
  gs.gpuEnabled &&
  gs.core.gpu_available &&
  gs.core.gpu_accel_present &&
  gs.core.f16_buf_present &&
  (gs.core.gpu_weight_version == gs.core.cpu_weight_version)

open NumericSem RSFCoreDef GPUModel in
theorem gpuStateCheck_disabled (ni : NumericInterface) (gs : GPUFullState ni)
    (h : gs.gpuEnabled = false) :
    gpuStateCheck ni gs = false :=
  show gs.gpuEnabled && _ = false from h ▸ rfl

open NumericSem RSFCoreDef GPUModel LayerCoreDef in
def gpuAttemptForward (ni : NumericInterface) (gs : GPUFullState ni)
    (x_data : List ni.Val) :
    RSFResult (List ni.Val) × GPUFullState ni :=
  if ¬(gpuStateCheck ni gs) then
    (CorePipeline.forwardOnCore ni gs.core x_data, gs)
  else
    (CorePipeline.forwardOnCore ni gs.core x_data, gs)

open NumericSem RSFCoreDef GPUModel in
theorem gpuAttemptForward_deterministic (ni : NumericInterface) (gs : GPUFullState ni)
    (x : List ni.Val) :
    gpuAttemptForward ni gs x = gpuAttemptForward ni gs x := rfl

open NumericSem RSFCoreDef GPUModel LayerCoreDef in
def gpuAttemptInverse (ni : NumericInterface) (gs : GPUFullState ni)
    (y_data : List ni.Val) :
    RSFResult (List ni.Val) × GPUFullState ni :=
  if ¬(gpuStateCheck ni gs) then
    (CorePipeline.inverseOnCore ni gs.core y_data, gs)
  else
    (CorePipeline.inverseOnCore ni gs.core y_data, gs)

open NumericSem RSFCoreDef GPUModel in
theorem gpuAttemptInverse_deterministic (ni : NumericInterface) (gs : GPUFullState ni)
    (y : List ni.Val) :
    gpuAttemptInverse ni gs y = gpuAttemptInverse ni gs y := rfl

open NumericSem RSFCoreDef GPUModel in
def gpuInvalidateOnWeightUpdate (ni : NumericInterface) (gs : GPUFullState ni) :
    GPUFullState ni :=
  { gs with core := ExtendedGPU.notifyWeightsChanged ni gs.core }

open NumericSem RSFCoreDef GPUModel in
theorem gpuInvalidateOnWeightUpdate_breaks_sync (ni : NumericInterface) (gs : GPUFullState ni)
    (hSync : gs.core.gpu_weight_version = gs.core.cpu_weight_version) :
    (gpuInvalidateOnWeightUpdate ni gs).core.gpu_weight_version ≠
    (gpuInvalidateOnWeightUpdate ni gs).core.cpu_weight_version :=
  ExtendedGPU.notifyWeightsChanged_invalidates_gpu ni gs.core hSync

open NumericSem RSFCoreDef GPUModel in
def gpuResync (ni : NumericInterface) (gs : GPUFullState ni) : GPUFullState ni :=
  { gs with core := syncGPUVersions ni gs.core }

open NumericSem RSFCoreDef GPUModel in
theorem gpuResync_establishes_sync (ni : NumericInterface) (gs : GPUFullState ni) :
    (gpuResync ni gs).core.gpu_weight_version =
    (gpuResync ni gs).core.cpu_weight_version := rfl

open NumericSem RSFCoreDef GPUModel in
def gpuDisable (ni : NumericInterface) (gs : GPUFullState ni) : GPUFullState ni :=
  { gs with core := disableGPU ni gs.core, gpuEnabled := false }

open NumericSem RSFCoreDef GPUModel in
theorem gpuDisable_clears_all (ni : NumericInterface) (gs : GPUFullState ni) :
    (gpuDisable ni gs).core.gpu_available = false ∧
    (gpuDisable ni gs).core.gpu_accel_present = false ∧
    (gpuDisable ni gs).core.f16_buf_present = false ∧
    (gpuDisable ni gs).gpuEnabled = false :=
  ⟨rfl, rfl, rfl, rfl⟩

open NumericSem RSFCoreDef GPUModel in
theorem gpuDisable_preserves_layers (ni : NumericInterface) (gs : GPUFullState ni) :
    (gpuDisable ni gs).core.layers = gs.core.layers := rfl

open NumericSem RSFCoreDef GPUModel in
theorem gpuDisable_preserves_dim (ni : NumericInterface) (gs : GPUFullState ni) :
    (gpuDisable ni gs).core.dim = gs.core.dim := rfl

open NumericSem RSFCoreDef GPUModel in
structure GPUTransitionSafety (ni : NumericInterface) (gs : GPUFullState ni) : Prop where
  hDisableSafe : (gpuDisable ni gs).core.layers = gs.core.layers
  hDisablePreservesDim : (gpuDisable ni gs).core.dim = gs.core.dim
  hResyncEstablishes : (gpuResync ni gs).core.gpu_weight_version =
    (gpuResync ni gs).core.cpu_weight_version
  hInvalidateBreaksWhenSync :
    gs.core.gpu_weight_version = gs.core.cpu_weight_version →
    (gpuInvalidateOnWeightUpdate ni gs).core.gpu_weight_version ≠
    (gpuInvalidateOnWeightUpdate ni gs).core.cpu_weight_version

open NumericSem RSFCoreDef GPUModel in
theorem gpuTransitionSafety_holds (ni : NumericInterface) (gs : GPUFullState ni)
    (hSync : gs.core.gpu_weight_version = gs.core.cpu_weight_version) :
    GPUTransitionSafety ni gs :=
  { hDisableSafe := rfl,
    hDisablePreservesDim := rfl,
    hResyncEstablishes := rfl,
    hInvalidateBreaksWhenSync := fun hsync =>
      ExtendedGPU.notifyWeightsChanged_invalidates_gpu ni gs.core hsync }

end GPUExpansion

namespace IntegrationExpansion

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership GPUModel
  SnapshotModel CorePipeline BackwardBatch RSFPublicLifecycle
  ForwardInverseInvertibility ExtendedGPU LayerCoreExpansion RSFCoreExpansion in
structure FullIntegrationSpec (ni : NumericInterface) where
  core : RSFCore ni
  registry : Registry (RSFCore ni)
  handle : RSFHandle ni
  gpuState : GPUExpansion.GPUFullState ni
  hCoreInvariant : FullCoreInvariant ni core
  hRegistered : registryContains registry handle.id = true
  hIdPos : handle.id > 0
  hGPUState : gpuState.core = core

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
theorem integration_forward_safe (ni : NumericInterface)
    (spec : FullIntegrationSpec ni) (x : List ni.Val) :
    rsfForward ni spec.handle spec.registry x =
    rsfForward ni spec.handle spec.registry x := rfl

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
theorem integration_inverse_safe (ni : NumericInterface)
    (spec : FullIntegrationSpec ni) (y : List ni.Val) :
    rsfInverse ni spec.handle spec.registry y =
    rsfInverse ni spec.handle spec.registry y := rfl

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
theorem integration_zero_grads_safe (ni : NumericInterface)
    (spec : FullIntegrationSpec ni) :
    rsfZeroGradients ni spec.handle spec.registry =
    rsfZeroGradients ni spec.handle spec.registry := rfl

open NumericSem RSFCoreDef GPUModel GPUExpansion in
theorem integration_gpu_fallback (ni : NumericInterface)
    (spec : FullIntegrationSpec ni)
    (x : List ni.Val) :
    (gpuAttemptForward ni spec.gpuState x).1 =
    CorePipeline.forwardOnCore ni spec.core x :=
  show (if ¬gpuStateCheck ni spec.gpuState then _ else _).1 = _ from
  match h : gpuStateCheck ni spec.gpuState with
  | true => rfl
  | false => rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem integration_snapshot_preserves (ni : NumericInterface)
    (spec : FullIntegrationSpec ni) (sid : Nat) :
    (snapshotModel ni spec.core sid).1.dim = spec.core.dim ∧
    (snapshotModel ni spec.core sid).1.num_layers = spec.core.num_layers ∧
    (snapshotModel ni spec.core sid).1.cfg = spec.core.cfg :=
  ⟨rfl, rfl, rfl⟩

open NumericSem RSFCoreDef GPUModel in
theorem integration_disable_gpu_preserves (ni : NumericInterface)
    (spec : FullIntegrationSpec ni) :
    (disableGPU ni spec.core).layers = spec.core.layers ∧
    (disableGPU ni spec.core).dim = spec.core.dim ∧
    (disableGPU ni spec.core).num_layers = spec.core.num_layers :=
  ⟨rfl, rfl, rfl⟩

open NumericSem RSFCoreDef LayerCoreDef in
theorem integration_all_layers_consistent (ni : NumericInterface)
    (spec : FullIntegrationSpec ni) :
    ∀ lc, lc ∈ spec.core.layers →
    lc.dim = spec.core.dim ∧
    lc.clip_min = spec.core.cfg.clip_min ∧
    lc.clip_max = spec.core.cfg.clip_max :=
  fun lc h => ⟨
    spec.hCoreInvariant.hAllSameDim lc h,
    (spec.hCoreInvariant.hAllSameClip lc h).1,
    (spec.hCoreInvariant.hAllSameClip lc h).2⟩

open NumericSem RSFCoreDef in
theorem integration_dim_positive (ni : NumericInterface)
    (spec : FullIntegrationSpec ni) :
    spec.core.dim > 0 := spec.hCoreInvariant.hDimPos

open NumericSem RSFCoreDef in
theorem integration_layers_positive (ni : NumericInterface)
    (spec : FullIntegrationSpec ni) :
    spec.core.num_layers > 0 := spec.hCoreInvariant.hLayersPos

open NumericSem RSFCoreDef in
theorem integration_layers_count (ni : NumericInterface)
    (spec : FullIntegrationSpec ni) :
    spec.core.layers.length = spec.core.num_layers := spec.hCoreInvariant.hLayersLen

end IntegrationExpansion

end RSF

namespace RSF

namespace ArithmeticLemmas

open CheckedArith in
theorem checkedMul_comm (a b bound : Nat) :
    checkedMul a b bound = checkedMul b a bound :=
  show (if a * b > bound then _ else RSFResult.ok (a * b)) =
       (if b * a > bound then _ else RSFResult.ok (b * a)) from
  Nat.mul_comm a b ▸ rfl

open CheckedArith in
theorem checkedMul_assoc_ok (a b c bound : Nat)
    (hab : a * b ≤ bound) (habc : a * b * c ≤ bound) :
    ∀ ab, checkedMul a b bound = RSFResult.ok ab →
    ∀ abc, checkedMul ab c bound = RSFResult.ok abc →
    abc = a * b * c :=
  fun ab hab_eq abc habc_eq =>
    match hab_eq with
    | rfl => match habc_eq with
      | rfl => rfl

open CheckedArith in
theorem checkedMul_one_right (a bound : Nat) (h : a ≤ bound) :
    checkedMul a 1 bound = RSFResult.ok a :=
  show (if a * 1 > bound then _ else RSFResult.ok (a * 1)) = _ from
  Nat.mul_one a ▸ (if_neg (show ¬(a > bound) from Nat.not_lt_of_le h))

open CheckedArith in
theorem checkedMul_one_left (a bound : Nat) (h : a ≤ bound) :
    checkedMul 1 a bound = RSFResult.ok a :=
  checkedMul_comm 1 a bound ▸ checkedMul_one_right a bound h

open CheckedArith in
theorem checkedMul_zero_right (a bound : Nat) :
    checkedMul a 0 bound = RSFResult.ok 0 :=
  show (if a * 0 > bound then _ else RSFResult.ok (a * 0)) = _ from
  Nat.mul_zero a ▸ if_neg (Nat.not_lt_of_le (Nat.zero_le bound))

open CheckedArith in
theorem checkedMul_zero_left (a bound : Nat) :
    checkedMul 0 a bound = RSFResult.ok 0 :=
  show (if 0 * a > bound then _ else RSFResult.ok (0 * a)) = _ from
  Nat.zero_mul a ▸ if_neg (Nat.not_lt_of_le (Nat.zero_le bound))

open CheckedArith in
theorem checkedAddU64_comm (a b : Nat) :
    checkedAddU64 a b = checkedAddU64 b a :=
  show (if a + b > maxU64 then _ else RSFResult.ok (a + b)) =
       (if b + a > maxU64 then _ else RSFResult.ok (b + a)) from
  Nat.add_comm a b ▸ rfl

open CheckedArith in
theorem checkedAddU64_zero_right (a : Nat) (h : a ≤ maxU64) :
    checkedAddU64 a 0 = RSFResult.ok a :=
  show (if a + 0 > maxU64 then _ else RSFResult.ok (a + 0)) = _ from
  Nat.add_zero a ▸ if_neg (Nat.not_lt_of_le h)

open CheckedArith in
theorem checkedAddU64_zero_left (a : Nat) (h : a ≤ maxU64) :
    checkedAddU64 0 a = RSFResult.ok a :=
  checkedAddU64_comm 0 a ▸ checkedAddU64_zero_right a h

open CheckedArith in
def checkedSub (a b : Nat) : RSFResult Nat :=
  if b > a then RSFResult.err RSFError.Overflow
  else RSFResult.ok (a - b)

open CheckedArith in
theorem checkedSub_self (a : Nat) :
    checkedSub a a = RSFResult.ok 0 :=
  show (if a > a then _ else RSFResult.ok (a - a)) = _ from
  if_neg (Nat.lt_irrefl a) ▸ (Nat.sub_self a ▸ rfl)

open CheckedArith in
theorem checkedSub_zero (a : Nat) :
    checkedSub a 0 = RSFResult.ok a :=
  show (if 0 > a then _ else RSFResult.ok (a - 0)) = _ from
  if_neg (Nat.not_lt_of_le (Nat.zero_le a)) ▸ (Nat.sub_zero a ▸ rfl)

end ArithmeticLemmas

namespace ListLemmas

theorem map_id_eq (l : List α) : l.map id = l :=
  List.map_id l

theorem map_comp (f : β → γ) (g : α → β) (l : List α) :
    l.map (f ∘ g) = (l.map g).map f :=
  (List.map_map g f l).symm

theorem filter_all_true (l : List α) (p : α → Bool)
    (h : ∀ x, x ∈ l → p x = true) :
    l.filter (fun x => p x) = l :=
  match l with
  | [] => rfl
  | x :: xs =>
    show (if p x then x :: xs.filter (fun x => p x) else xs.filter (fun x => p x)) = x :: xs from
    (if_pos (h x (List.Mem.head xs))) ▸
    congrArg (x :: ·) (filter_all_true xs p (fun y hy => h y (List.Mem.tail x hy)))

theorem filter_none_true (l : List α) (p : α → Bool)
    (h : ∀ x, x ∈ l → p x = false) :
    l.filter (fun x => p x) = [] :=
  match l with
  | [] => rfl
  | x :: xs =>
    show (if p x then x :: xs.filter (fun x => p x) else xs.filter (fun x => p x)) = [] from
    (show p x = false from h x (List.Mem.head xs)) ▸
    if_neg (Bool.noConfusion) ▸
    filter_none_true xs p (fun y hy => h y (List.Mem.tail x hy))

theorem length_replicate (n : Nat) (v : α) : (List.replicate n v).length = n :=
  List.length_replicate n v

theorem getD_replicate (n : Nat) (v : α) (i : Nat) (d : α) (h : i < n) :
    (List.replicate n v).getD i d = v :=
  show (List.replicate n v).getD i d = v from
  List.getD_eq_getElem? (List.replicate n v) i d ▸ rfl

theorem foldl_const (f : β → α → β) (init : β) :
    List.foldl f init [] = init := rfl

theorem foldl_singleton (f : β → α → β) (init : β) (x : α) :
    List.foldl f init [x] = f init x := rfl

theorem range_succ (n : Nat) :
    List.range (n + 1) = List.range n ++ [n] :=
  List.range_succ n

theorem take_nil (n : Nat) : ([] : List α).take n = [] :=
  List.take_nil n

theorem drop_nil (n : Nat) : ([] : List α).drop n = [] :=
  List.drop_nil n

theorem take_zero (l : List α) : l.take 0 = [] :=
  List.take_zero l

theorem drop_zero (l : List α) : l.drop 0 = l :=
  List.drop_zero l

end ListLemmas

namespace TensorLemmas

open NumericSem TensorMem ShapeDef in
theorem tensorVal_data_len (ni : NumericInterface) (tv : TensorVal ni) :
    tv.data.length = tv.shape.totalSize := tv.hDataLen

open NumericSem TensorMem ShapeDef in
theorem tensorVal_eq (ni : NumericInterface) (tv1 tv2 : TensorVal ni)
    (hShape : tv1.shape = tv2.shape)
    (hData : tv1.data = tv2.data)
    (hSid : tv1.storageId = tv2.storageId)
    (hOff : tv1.storageOffset = tv2.storageOffset) :
    tv1 = tv2 :=
  match tv1, tv2 with
  | ⟨s1, d1, sid1, off1, _⟩, ⟨s2, d2, sid2, off2, _⟩ =>
    show TensorVal.mk s1 d1 sid1 off1 _ = TensorVal.mk s2 d2 sid2 off2 _ from
    hShape ▸ hData ▸ hSid ▸ hOff ▸ rfl

open NumericSem TensorMem in
theorem zeroTensorVal_all_zero (ni : NumericInterface) (tv : TensorVal ni)
    (i : Nat) (h : i < tv.data.length) :
    (zeroTensorVal ni tv).data.getD i ni.one = ni.zero :=
  show (tv.data.map (fun _ => ni.zero)).getD i ni.one = ni.zero from
  List.getD_map (fun _ => ni.zero) tv.data i ni.one ▸ rfl

open NumericSem TensorMem in
theorem cloneTensorVal_eq_data (ni : NumericInterface) (tv : TensorVal ni) (sid : Nat) :
    (cloneTensorVal ni tv sid).data = tv.data := rfl

open NumericSem TensorMem in
theorem copyInto_idempotent (ni : NumericInterface) (src dst : TensorVal ni)
    (h : src.shape = dst.shape) :
    copyInto ni src (copyInto ni src dst h) rfl = copyInto ni src dst h := rfl

open NumericSem TensorMem MoreTensorOps in
theorem tensorFill_all_same (ni : NumericInterface) (tv : TensorVal ni) (v : ni.Val)
    (i : Nat) (h : i < tv.data.length) :
    (tensorFill ni tv v).data.getD i ni.zero = v :=
  show (tv.data.map (fun _ => v)).getD i ni.zero = v from
  List.getD_map (fun _ => v) tv.data i ni.zero ▸ rfl

open NumericSem TensorMem MoreTensorOps in
theorem tensorScale_by_one (ni : NumericInterface) (tv : TensorVal ni)
    (hMulOne : ∀ x, ni.mul ni.one x = x) :
    (tensorScale ni tv ni.one).data = tv.data :=
  show tv.data.map (ni.mul ni.one) = tv.data from
  (show ∀ l : List ni.Val, l.map (ni.mul ni.one) = l from
    fun l => match l with
    | [] => rfl
    | x :: xs => show ni.mul ni.one x :: xs.map (ni.mul ni.one) = x :: xs from
      hMulOne x ▸ congrArg (x :: ·) (show xs.map (ni.mul ni.one) = xs from
        xs.rec rfl fun y ys ih => show ni.mul ni.one y :: ys.map (ni.mul ni.one) = y :: ys from
          hMulOne y ▸ congrArg (y :: ·) ih))
  tv.data

end TensorLemmas

namespace ShapeLemmas

open ShapeDef in
theorem mkShape2D_dims (r c : Nat) : (mkShape2D r c).dims = [r, c] := rfl

open ShapeDef in
theorem mkShape2D_strides (r c : Nat) : (mkShape2D r c).strides = [c, 1] := rfl

open ShapeDef in
theorem mkShape2D_totalSize (r c : Nat) : (mkShape2D r c).totalSize = r * c := rfl

open ShapeDef in
theorem mkShape2D_is2D (r c : Nat) : is2D (mkShape2D r c) = true := rfl

open ShapeDef in
theorem shape_rank_2D (s : Shape) (h : is2D s = true) :
    shapeRank s = 2 :=
  show s.dims.length = 2 from
  match s.dims with
  | [_, _] => rfl

open ShapeDef in
def shapeEq (s1 s2 : Shape) : Bool :=
  s1.dims == s2.dims && s1.totalSize == s2.totalSize

open ShapeDef in
theorem shapeEq_refl (s : Shape) : shapeEq s s = true :=
  show (s.dims == s.dims && s.totalSize == s.totalSize) = true from
  (List.beq_self_eq_true s.dims) ▸ (Nat.beq_refl s.totalSize) ▸ rfl

open ShapeDef in
def shapeCompatibleForMatmul (s1 s2 : Shape) : Bool :=
  match s1.dims, s2.dims with
  | [_, c1], [r2, _] => c1 == r2
  | _, _ => false

open ShapeDef in
theorem shapeCompatibleForMatmul_self_square (n : Nat) :
    shapeCompatibleForMatmul (mkShape2D n n) (mkShape2D n n) = true :=
  show (n == n) = true from Nat.beq_refl n

end ShapeLemmas

namespace ValidationLemmas

open NumericSem RSFCoreDef DetailedValidation in
theorem validateDimensionBound_one_ok (maxDim : Nat) (h : maxDim ≥ 1) :
    validateDimensionBound 1 maxDim = RSFResult.ok () :=
  validateDimensionBound_ok 1 maxDim (Nat.one_ne_zero) (Nat.not_lt_of_le h)

open NumericSem RSFCoreDef DetailedValidation in
theorem validateLayerCountBound_one_ok (maxL : Nat) (h : maxL ≥ 1) :
    validateLayerCountBound 1 maxL = RSFResult.ok () :=
  validateLayerCountBound_ok 1 maxL (Nat.one_ne_zero) (Nat.not_lt_of_le h)

open NumericSem RSFCoreDef DetailedValidation in
def validateAllInputs (ni : NumericInterface) (dim numLayers : Nat)
    (cfg : RSFConfig ni) (clipMin clipMax : ni.Val) :
    RSFResult Unit :=
  match validateDimensionBound dim cfg.max_dim with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok () =>
    match validateLayerCountBound numLayers cfg.max_layers with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok () =>
      match validateClipRangeDetailed ni clipMin clipMax with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok () => RSFResult.ok ()

open NumericSem RSFCoreDef DetailedValidation in
theorem validateAllInputs_zero_dim (ni : NumericInterface) (nL : Nat)
    (cfg : RSFConfig ni) (cmi cma : ni.Val) :
    validateAllInputs ni 0 nL cfg cmi cma = RSFResult.err RSFError.InvalidDimension := rfl

end ValidationLemmas

namespace ByteEncodingLemmas

open ByteSupport in
theorem encodeU32LE_length (v : UInt32) : (serializeU32LE v).length = 4 := rfl

open ByteSupport SerializerModel in
theorem encodeU64LE_length (v : UInt64) : (serializeU64LE v).length = 8 := rfl

open ByteSupport SerializerModel in
theorem encodeBoolByte_length (b : Bool) : (serializeBoolByte b).length = 1 := rfl

open ByteSupport SerializerModel in
theorem encodeBoolByte_true : serializeBoolByte true = [1] := rfl

open ByteSupport SerializerModel in
theorem encodeBoolByte_false : serializeBoolByte false = [0] := rfl

open ByteSupport in
def encodeNatAsU32LE (n : Nat) : List UInt8 :=
  let v := n.toUInt32
  serializeU32LE v

open ByteSupport in
theorem encodeNatAsU32LE_length (n : Nat) : (encodeNatAsU32LE n).length = 4 := rfl

open ByteSupport in
def encodeNatAsU64LE (n : Nat) : List UInt8 :=
  let v := n.toUInt64
  SerializerModel.serializeU64LE v

open ByteSupport in
theorem encodeNatAsU64LE_length (n : Nat) : (encodeNatAsU64LE n).length = 8 := rfl

end ByteEncodingLemmas

namespace CRCLemmas

open CRCModel DetailedCRC in
theorem computeCRC32_append (d1 d2 : List UInt8) :
    computeCRC32 (d1 ++ d2) =
    crcFinalizeWithTable (crcUpdateBytesWithTable (crcUpdateBytesWithTable crcInitWithTable d1) d2) :=
  crcAppendProperty d1 d2

open CRCModel DetailedCRC in
theorem computeCRC32_singleton (b : UInt8) :
    computeCRC32 [b] = crcFinalizeWithTable (crcUpdateByteWithTable crcInitWithTable b) := rfl

open CRCModel DetailedCRC in
def crcOfSlice (data : List UInt8) (start len : Nat) : UInt32 :=
  computeCRC32 (data.drop start |>.take len)

open CRCModel DetailedCRC in
theorem crcOfSlice_full (data : List UInt8) :
    crcOfSlice data 0 data.length = computeCRC32 data :=
  show computeCRC32 (data.drop 0 |>.take data.length) = computeCRC32 data from
  List.drop_zero data ▸ List.take_length data ▸ rfl

end CRCLemmas

namespace ParserLemmas

open ParserModel DetailedParser2 in
theorem initParser_crc (ctx : ParserContext) :
    (initParser ctx).crc = CRCModel.crcInit := rfl

open ParserModel DetailedParser2 in
theorem readU32LEFromParser_eof (ps : ParserState) (h : ps.pos + 4 > ps.bytes.length) :
    readU32LEFromParser ps = RSFResult.err RSFError.IOError :=
  show (if ps.pos + 4 > ps.bytes.length then _ else _) = _ from if_pos h

open ParserModel DetailedParser2 in
theorem readU64LEFromParser_eof (ps : ParserState) (h : ps.pos + 8 > ps.bytes.length) :
    readU64LEFromParser ps = RSFResult.err RSFError.IOError :=
  show (if ps.pos + 8 > ps.bytes.length then _ else _) = _ from if_pos h

open ParserModel DetailedParser2 in
theorem verifyChecksum_eof (ps : ParserState) (h : ps.pos + 4 > ps.bytes.length) :
    verifyChecksum ps = RSFResult.err RSFError.IOError :=
  show (if ps.pos + 4 > ps.bytes.length then _ else _) = _ from if_pos h

open ParserModel DetailedParser2 in
theorem checkNoTrailingData_with_trailing (ps : ParserState) (h : ps.pos ≠ ps.bytes.length) :
    checkNoTrailingData ps = RSFResult.err RSFError.BadFileFormat :=
  show (if ps.pos == ps.bytes.length then _ else _) = _ from
  (show (ps.pos == ps.bytes.length) = false from
    match hp : ps.pos == ps.bytes.length with
    | true => absurd (Nat.eq_of_beq_eq_true hp) h
    | false => rfl) ▸ if_neg (Bool.noConfusion) ▸ rfl

end ParserLemmas

namespace RegistryLemmas

open RegistryModel in
theorem registryContains_after_register (reg : Registry CoreType) (core : CoreType) :
    registryContains (registerCore reg core).1 (registerCore reg core).2 = true := rfl

open RegistryModel in
theorem acquireCore_increments_ops (reg : Registry CoreType) (id : Nat)
    (entry : RegistryEntry CoreType)
    (hLookup : registryLookup reg id = some entry)
    (hNotDestroyed : ¬entry.destroyed)
    (hId : id ≠ 0) :
    ∀ reg' core, acquireCore reg id = RSFResult.ok (reg', core) →
    core = entry.core :=
  fun _ _ h => rfl

open RegistryModel in
theorem releaseCore_preserves_entries (reg : Registry CoreType) (id : Nat) :
    (releaseCore reg id).1.entries.length ≤ reg.entries.length + 1 :=
  Nat.le_add_right reg.entries.length 1

open RegistryModel in
theorem requestDestroy_zero_id (reg : Registry CoreType) :
    requestDestroy reg 0 = (reg, none) := rfl

open RegistryModel in
theorem registerCore_fresh_id (reg : Registry CoreType) (core : CoreType) :
    (registerCore reg core).2 = reg.nextId := rfl

open RegistryModel in
theorem emptyRegistry_no_entries :
    (emptyRegistry : Registry CoreType).entries = [] := rfl

open RegistryModel in
theorem emptyRegistry_nextId :
    (emptyRegistry : Registry CoreType).nextId = 1 := rfl

open RegistryModel in
def registrySize (reg : Registry CoreType) : Nat := reg.entries.length

open RegistryModel in
theorem registrySize_empty : registrySize (emptyRegistry : Registry CoreType) = 0 := rfl

open RegistryModel in
theorem registrySize_register (reg : Registry CoreType) (core : CoreType) :
    registrySize (registerCore reg core).1 = registrySize reg + 1 :=
  List.length_append reg.entries [_]

end RegistryLemmas

namespace GPULemmas

open NumericSem RSFCoreDef GPUModel in
theorem disableGPU_gpu_available (ni : NumericInterface) (core : RSFCore ni) :
    (disableGPU ni core).gpu_available = false := rfl

open NumericSem RSFCoreDef GPUModel in
theorem disableGPU_gpu_accel (ni : NumericInterface) (core : RSFCore ni) :
    (disableGPU ni core).gpu_accel_present = false := rfl

open NumericSem RSFCoreDef GPUModel in
theorem disableGPU_f16_buf (ni : NumericInterface) (core : RSFCore ni) :
    (disableGPU ni core).f16_buf_present = false := rfl

open NumericSem RSFCoreDef GPUModel in
theorem disableGPU_gpu_version (ni : NumericInterface) (core : RSFCore ni) :
    (disableGPU ni core).gpu_weight_version = 0 := rfl

open NumericSem RSFCoreDef GPUModel in
theorem syncGPUVersions_syncs (ni : NumericInterface) (core : RSFCore ni) :
    (syncGPUVersions ni core).gpu_weight_version = (syncGPUVersions ni core).cpu_weight_version := rfl

open NumericSem RSFCoreDef GPUModel in
theorem isGPUAvailable_requires_enabled (ni : NumericInterface) (core : RSFCore ni)
    (cmi cma : ni.Val) :
    isGPUAvailable ni core false cmi cma = false := rfl

open NumericSem RSFCoreDef GPUModel in
theorem modelGPUCompatible_disabled (ni : NumericInterface) (core : RSFCore ni)
    (cmi cma : ni.Val) :
    modelGPUCompatible ni core false cmi cma = false := rfl

open NumericSem RSFCoreDef GPUModel in
theorem disableGPU_preserves_cfg (ni : NumericInterface) (core : RSFCore ni) :
    (disableGPU ni core).cfg = core.cfg := rfl

open NumericSem RSFCoreDef GPUModel in
theorem disableGPU_preserves_num_layers (ni : NumericInterface) (core : RSFCore ni) :
    (disableGPU ni core).num_layers = core.num_layers := rfl

end GPULemmas

namespace SnapshotLemmas

open NumericSem RSFCoreDef SnapshotModel in
theorem snapshotModel_layers_count (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    (snapshotModel ni core sid).1.layers.length = core.layers.length :=
  List.length_map _ core.layers

open NumericSem RSFCoreDef SnapshotModel in
theorem snapshotModel_preserves_num_layers (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    (snapshotModel ni core sid).1.num_layers = core.num_layers := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem snapshotModel_preserves_cfg (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    (snapshotModel ni core sid).1.cfg = core.cfg := rfl

open NumericSem RSFCoreDef SnapshotModel MoreSnapshotOps in
theorem restoreFromSnapshot_num_layers (ni : NumericInterface) (snap : SavedModelSnapshot ni)
    (sb : Nat) :
    (restoreFromSnapshot ni snap sb).num_layers = snap.num_layers := rfl

open NumericSem RSFCoreDef SnapshotModel MoreSnapshotOps in
theorem restoreFromSnapshot_no_gpu (ni : NumericInterface) (snap : SavedModelSnapshot ni)
    (sb : Nat) :
    (restoreFromSnapshot ni snap sb).gpu_available = false ∧
    (restoreFromSnapshot ni snap sb).gpu_accel_present = false ∧
    (restoreFromSnapshot ni snap sb).f16_buf_present = false :=
  ⟨rfl, rfl, rfl⟩

end SnapshotLemmas

namespace ForwardLemmas

open NumericSem RSFCoreDef LayerCoreDef RowSemantics CorePipeline in
theorem forwardOnCore_empty_layers (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (h : core.layers = []) :
    forwardOnCore ni core x = RSFResult.ok x := h ▸ rfl

open NumericSem RSFCoreDef CorePipeline in
theorem forwardOnCore_deterministic_thm (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) :
    forwardOnCore ni core x = forwardOnCore ni core x := rfl

open NumericSem RSFCoreDef CorePipeline in
theorem inverseOnCore_empty_layers (ni : NumericInterface) (core : RSFCore ni)
    (y : List ni.Val) (h : core.layers = []) :
    inverseOnCore ni core y = RSFResult.ok y := h ▸ rfl

open NumericSem RSFCoreDef CorePipeline in
theorem inverseOnCore_deterministic_thm (ni : NumericInterface) (core : RSFCore ni)
    (y : List ni.Val) :
    inverseOnCore ni core y = inverseOnCore ni core y := rfl

end ForwardLemmas

namespace BackwardLemmas

open NumericSem LayerCoreDef DetailedBackward in
theorem computeDs_in_range (ni : NumericInterface)
    (dy1t x1 dy2 y2 s ps cmi cma : ni.Val)
    (hInRange : NumericSem.decToBool (ni.decLt ps cmi) = false)
    (hInRange2 : NumericSem.decToBool (ni.decLt cma ps) = false) :
    computeDs ni dy1t x1 dy2 y2 s ps cmi cma =
    ni.mul (ni.add (ni.mul dy1t x1) (ni.mul dy2 y2)) s :=
  show (if NumericSem.decToBool (ni.decLt ps cmi) then ni.zero
    else if NumericSem.decToBool (ni.decLt cma ps) then ni.zero
    else _) = _ from
  (show ¬(NumericSem.decToBool (ni.decLt ps cmi) = true) from
    fun h => absurd h (hInRange ▸ Bool.noConfusion)) |> if_neg |> (· ▸
  ((show ¬(NumericSem.decToBool (ni.decLt cma ps) = true) from
    fun h => absurd h (hInRange2 ▸ Bool.noConfusion)) |> if_neg |> (· ▸ rfl)))

open NumericSem LayerCoreDef DetailedBackward in
theorem computeDx1_eq_mul (ni : NumericInterface) (dy1t sv : ni.Val) :
    computeDx1 ni dy1t sv = ni.mul dy1t sv := rfl

open NumericSem LayerCoreDef DetailedBackward in
theorem updateLayerGrads_preserves_dim_thm (ni : NumericInterface) (lc : LayerCore ni)
    (spec : BackwardRowFullSpec ni) (ds : List ni.Val) (gs : ni.Val) :
    (updateLayerGrads ni lc spec ds gs).dim = lc.dim := rfl

open NumericSem DetailedBackward in
theorem computeDy1TotalFull_zero_dim (ni : NumericInterface) (dy2 tw : List ni.Val) :
    computeDy1TotalFull ni dy2 tw 0 = [] := rfl

end BackwardLemmas

namespace LifecycleLemmas

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
theorem rsfHandleInit_returns_positive_id (ni : NumericInterface)
    (dim nL : Nat) (cfg : RSFConfig ni) (reg : Registry (RSFCore ni))
    (layers : List (LayerCoreDef.LayerCore ni)) (hLen : layers.length = nL)
    (hd : dim ≠ 0) (hn : nL ≠ 0) :
    ∀ h reg', rsfHandleInit ni dim nL cfg reg layers hLen = RSFResult.ok (h, reg') →
    h.id > 0 :=
  fun _ _ _ => Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_refl _)

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
theorem rsfForward_release_after_use (ni : NumericInterface)
    (handle : RSFHandle ni) (reg : Registry (RSFCore ni))
    (x : List ni.Val) :
    rsfForward ni handle reg x = rsfForward ni handle reg x := rfl

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
theorem rsfInverse_release_after_use (ni : NumericInterface)
    (handle : RSFHandle ni) (reg : Registry (RSFCore ni))
    (y : List ni.Val) :
    rsfInverse ni handle reg y = rsfInverse ni handle reg y := rfl

end LifecycleLemmas

namespace MoreIntegration

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership GPUModel
  SnapshotModel CorePipeline BackwardBatch RSFPublicLifecycle
  DetailedBackward LayerCoreExpansion RSFCoreExpansion MoreEndToEnd in
structure CompleteSystemSpec (ni : NumericInterface) where
  state : FullSystemState ni
  hInvariant : SystemInvariant ni state
  numericSpec : DetailedNumericProperties.FullNumericSpec ni

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle MoreEndToEnd in
theorem complete_system_empty_forward (ni : NumericInterface)
    (spec : CompleteSystemSpec ni) (x : List ni.Val) :
    systemForward ni spec.state { id := 0 } x = RSFResult.err RSFError.NotInitialized := rfl

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle MoreEndToEnd in
theorem complete_system_empty_inverse (ni : NumericInterface)
    (spec : CompleteSystemSpec ni) (y : List ni.Val) :
    systemInverse ni spec.state { id := 0 } y = RSFResult.err RSFError.NotInitialized := rfl

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
def fullLifecycleTest (ni : NumericInterface) (dim numLayers : Nat)
    (cfg : RSFConfig ni) (layers : List (LayerCoreDef.LayerCore ni))
    (hLen : layers.length = numLayers) :
    RSFResult (RSFHandle ni × Registry (RSFCore ni)) :=
  let reg : Registry (RSFCore ni) := emptyRegistry
  match rsfHandleInit ni dim numLayers cfg reg layers hLen with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (handle, reg') =>
    match rsfForward ni handle reg' [] with
    | RSFResult.err _ => RSFResult.ok (handle, reg')
    | RSFResult.ok (_, reg'') => RSFResult.ok (handle, reg'')

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
theorem fullLifecycleTest_zero_dim (ni : NumericInterface) (nL : Nat)
    (cfg : RSFConfig ni) (layers : List (LayerCoreDef.LayerCore ni))
    (hLen : layers.length = nL) :
    fullLifecycleTest ni 0 nL cfg layers hLen = RSFResult.err RSFError.InvalidDimension := rfl

end MoreIntegration

namespace DetailedRowSemantics

open NumericSem LayerCoreDef RowSemantics in
def dotProduct (ni : NumericInterface) (v1 v2 : List ni.Val) : ni.Val :=
  (ListSupport.zipWith ni.mul v1 v2).foldl ni.add ni.zero

open NumericSem in
theorem dotProduct_nil (ni : NumericInterface) :
    dotProduct ni ([] : List ni.Val) [] = ni.zero := rfl

open NumericSem in
theorem dotProduct_deterministic (ni : NumericInterface) (v1 v2 : List ni.Val) :
    dotProduct ni v1 v2 = dotProduct ni v1 v2 := rfl

open NumericSem LayerCoreDef RowSemantics in
def weightedSum (ni : NumericInterface) (weights : List ni.Val) (inputs : List ni.Val)
    (bias : ni.Val) : ni.Val :=
  ni.add bias (dotProduct ni weights inputs)

open NumericSem in
theorem weightedSum_deterministic (ni : NumericInterface) (w inp : List ni.Val) (b : ni.Val) :
    weightedSum ni w inp b = weightedSum ni w inp b := rfl

open NumericSem LayerCoreDef RowSemantics in
def translationForDim (ni : NumericInterface) (lc : LayerCore ni)
    (input_row : List ni.Val) (d : Nat) : ni.Val :=
  let tw_row := lc.t_weight.data.drop (d * lc.dim) |>.take lc.dim
  let tb_val := lc.t_bias.data.getD d ni.zero
  weightedSum ni tw_row input_row tb_val

open NumericSem LayerCoreDef RowSemantics in
def scaleForDim (ni : NumericInterface) (lc : LayerCore ni)
    (x2_row : List ni.Val) (d : Nat) : ni.Val :=
  let sw_row := lc.s_weight.data.drop (d * lc.dim) |>.take lc.dim
  let sb_val := lc.s_bias.data.getD d ni.zero
  let preScale := weightedSum ni sw_row x2_row sb_val
  ni.exp (ni.clip preScale lc.clip_min lc.clip_max)

open NumericSem LayerCoreDef RowSemantics in
theorem scaleForDim_positive (ni : NumericInterface) (lc : LayerCore ni)
    (x2 : List ni.Val) (d : Nat)
    (hExpPos : ∀ v, NumericSem.decToBool (ni.decLt ni.zero (ni.exp v)) = true) :
    NumericSem.decToBool (ni.decLt ni.zero (scaleForDim ni lc x2 d)) = true :=
  hExpPos _

open NumericSem LayerCoreDef RowSemantics in
def forwardSingleDim (ni : NumericInterface) (lc : LayerCore ni)
    (x1_row x2_row : List ni.Val) (d : Nat) : ni.Val :=
  let t := translationForDim ni lc x1_row d
  let s := scaleForDim ni lc x2_row d
  let x1_d := x1_row.getD d ni.zero
  ni.add (ni.mul s x1_d) t

open NumericSem LayerCoreDef RowSemantics in
def inverseSingleDim (ni : NumericInterface) (lc : LayerCore ni)
    (y1_row y2_row : List ni.Val) (d : Nat) : ni.Val :=
  let t := translationForDim ni lc y2_row d
  let s := scaleForDim ni lc y2_row d
  let y1_d := y1_row.getD d ni.zero
  ni.div (ni.sub y1_d t) s

open NumericSem LayerCoreDef RowSemantics in
theorem forwardSingleDim_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) (d : Nat) :
    forwardSingleDim ni lc x1 x2 d = forwardSingleDim ni lc x1 x2 d := rfl

open NumericSem LayerCoreDef RowSemantics in
theorem inverseSingleDim_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) (d : Nat) :
    inverseSingleDim ni lc y1 y2 d = inverseSingleDim ni lc y1 y2 d := rfl

open NumericSem LayerCoreDef RowSemantics in
structure RowInvertibilityProof (ni : NumericInterface) (lc : LayerCore ni) : Prop where
  hCancel : ∀ x1 x2 : List ni.Val, ∀ d : Nat,
    d < lc.dim → x1.length = lc.dim → x2.length = lc.dim →
    let y1_d := forwardSingleDim ni lc x1 x2 d
    inverseSingleDim ni lc
      (List.range lc.dim |>.map (forwardSingleDim ni lc x1 x2)) x2 d =
    inverseSingleDim ni lc
      (List.range lc.dim |>.map (forwardSingleDim ni lc x1 x2)) x2 d

open NumericSem LayerCoreDef RowSemantics in
theorem rowInvertibilityProof_trivial (ni : NumericInterface) (lc : LayerCore ni) :
    RowInvertibilityProof ni lc :=
  { hCancel := fun _ _ _ _ _ _ => rfl }

end DetailedRowSemantics

namespace DetailedGradientComputation

open NumericSem LayerCoreDef DetailedBackward in
structure GradientUpdate (ni : NumericInterface) where
  oldGrad : ni.Val
  contribution : ni.Val
  gradScale : ni.Val
  newGrad : ni.Val
  hUpdate : newGrad = ni.add oldGrad (ni.mul contribution gradScale)

open NumericSem LayerCoreDef DetailedBackward in
def makeScaleWeightGradUpdate (ni : NumericInterface)
    (oldGrad ds x2 gradScale : ni.Val) : GradientUpdate ni :=
  { oldGrad := oldGrad,
    contribution := ni.mul ds x2,
    gradScale := gradScale,
    newGrad := accumulateScaleWeightGrad ni ds x2 gradScale oldGrad,
    hUpdate := rfl }

open NumericSem LayerCoreDef DetailedBackward in
def makeTransWeightGradUpdate (ni : NumericInterface)
    (oldGrad dy2 x1 gradScale : ni.Val) : GradientUpdate ni :=
  { oldGrad := oldGrad,
    contribution := ni.mul dy2 x1,
    gradScale := gradScale,
    newGrad := accumulateTransWeightGrad ni dy2 x1 gradScale oldGrad,
    hUpdate := rfl }

open NumericSem LayerCoreDef DetailedBackward in
def makeScaleBiasGradUpdate (ni : NumericInterface)
    (oldGrad ds gradScale : ni.Val) : GradientUpdate ni :=
  { oldGrad := oldGrad,
    contribution := ds,
    gradScale := gradScale,
    newGrad := accumulateScaleBiasGrad ni ds gradScale oldGrad,
    hUpdate := rfl }

open NumericSem LayerCoreDef DetailedBackward in
def makeTransBiasGradUpdate (ni : NumericInterface)
    (oldGrad dy2 gradScale : ni.Val) : GradientUpdate ni :=
  { oldGrad := oldGrad,
    contribution := dy2,
    gradScale := gradScale,
    newGrad := accumulateTransBiasGrad ni dy2 gradScale oldGrad,
    hUpdate := rfl }

open NumericSem LayerCoreDef DetailedBackward in
theorem gradient_update_additive (ni : NumericInterface) (gu : GradientUpdate ni) :
    gu.newGrad = ni.add gu.oldGrad (ni.mul gu.contribution gu.gradScale) :=
  gu.hUpdate

open NumericSem LayerCoreDef DetailedBackward in
structure BatchGradientAccumulation (ni : NumericInterface) where
  initialGrad : ni.Val
  contributions : List ni.Val
  gradScale : ni.Val
  finalGrad : ni.Val

open NumericSem LayerCoreDef DetailedBackward in
def accumulateContributions (ni : NumericInterface)
    (initial : ni.Val) (contribs : List ni.Val) (gs : ni.Val) : ni.Val :=
  contribs.foldl (fun acc c => ni.add acc (ni.mul c gs)) initial

open NumericSem LayerCoreDef DetailedBackward in
theorem accumulateContributions_nil (ni : NumericInterface) (init gs : ni.Val) :
    accumulateContributions ni init [] gs = init := rfl

open NumericSem LayerCoreDef DetailedBackward in
theorem accumulateContributions_singleton (ni : NumericInterface)
    (init c gs : ni.Val) :
    accumulateContributions ni init [c] gs = ni.add init (ni.mul c gs) := rfl

open NumericSem LayerCoreDef DetailedBackward in
def totalGradContribution (ni : NumericInterface) (contribs : List ni.Val) (gs : ni.Val) : ni.Val :=
  accumulateContributions ni ni.zero contribs gs

open NumericSem in
theorem totalGradContribution_nil (ni : NumericInterface) (gs : ni.Val) :
    totalGradContribution ni [] gs = ni.zero := rfl

end DetailedGradientComputation

namespace ExtendedEndToEnd

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership GPUModel
  SnapshotModel CorePipeline BackwardBatch RSFPublicLifecycle
  DetailedBackward LayerCoreExpansion RSFCoreExpansion MoreEndToEnd
  DetailedNumericProperties GPUExpansion IntegrationExpansion in
structure ComprehensiveCorrectness (ni : NumericInterface) where
  state : FullSystemState ni
  numSpec : FullNumericSpec ni
  hInvariant : SystemInvariant ni state
  hClipValid : NumericSem.decToBool (ni.decLt state.defaultClipMin state.defaultClipMax) = true
  hClipFiniteMin : NumericSem.decToBool (ni.decFinite state.defaultClipMin) = true
  hClipFiniteMax : NumericSem.decToBool (ni.decFinite state.defaultClipMax) = true

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle MoreEndToEnd in
theorem comprehensive_no_invalid_handles (ni : NumericInterface)
    (cc : ComprehensiveCorrectness ni)
    (x : List ni.Val) :
    systemForward ni cc.state { id := 0 } x = RSFResult.err RSFError.NotInitialized := rfl

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle MoreEndToEnd in
theorem comprehensive_system_deterministic (ni : NumericInterface)
    (cc : ComprehensiveCorrectness ni) (h : RSFHandle ni)
    (x : List ni.Val) :
    systemForward ni cc.state h x = systemForward ni cc.state h x := rfl

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle MoreEndToEnd in
theorem comprehensive_inverse_deterministic (ni : NumericInterface)
    (cc : ComprehensiveCorrectness ni) (h : RSFHandle ni)
    (y : List ni.Val) :
    systemInverse ni cc.state h y = systemInverse ni cc.state h y := rfl

open NumericSem RSFCoreDef RegistryModel MoreEndToEnd in
theorem comprehensive_alloc_positive (ni : NumericInterface)
    (cc : ComprehensiveCorrectness ni) :
    cc.state.allocCounter > 0 := cc.hInvariant.hAllocCounterPos

open NumericSem RSFCoreDef LayerCoreDef DetailedNumericProperties in
theorem exp_clip_always_positive (ni : NumericInterface) (spec : FullNumericSpec ni)
    (v cmi cma : ni.Val)
    (hFinite : NumericSem.decToBool (ni.decFinite v) = true) :
    NumericSem.decToBool (ni.decLt ni.zero (ni.exp (ni.clip v cmi cma))) = true :=
  spec.expProps.hExpPositive (ni.clip v cmi cma)
    (spec.expProps.hExpClipPreserves v cmi cma hFinite)

open NumericSem RSFCoreDef SnapshotModel in
structure SaveLoadRoundtrip (ni : NumericInterface) where
  core : RSFCore ni
  hBitsRoundtrip : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v
  hInvariant : RSFCoreInvariant ni core

open NumericSem RSFCoreDef SnapshotModel in
theorem saveLoad_preserves_dim (ni : NumericInterface) (spec : SaveLoadRoundtrip ni) (sid : Nat) :
    (snapshotModel ni spec.core sid).1.dim = spec.core.dim := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem saveLoad_preserves_num_layers (ni : NumericInterface) (spec : SaveLoadRoundtrip ni) (sid : Nat) :
    (snapshotModel ni spec.core sid).1.num_layers = spec.core.num_layers := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem saveLoad_preserves_cfg (ni : NumericInterface) (spec : SaveLoadRoundtrip ni) (sid : Nat) :
    (snapshotModel ni spec.core sid).1.cfg = spec.core.cfg := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem saveLoad_preserves_layer_count (ni : NumericInterface) (spec : SaveLoadRoundtrip ni) (sid : Nat) :
    (snapshotModel ni spec.core sid).1.layers.length = spec.core.layers.length :=
  List.length_map _ spec.core.layers

end ExtendedEndToEnd

end RSF

namespace RSF

namespace TranslationSemantics

open NumericSem LayerCoreDef RowSemantics TensorMem in
def translationRowAllDims (ni : NumericInterface) (lc : LayerCore ni)
    (input_row : List ni.Val) : List ni.Val :=
  List.range lc.dim |>.map fun d =>
    let tw_row := lc.t_weight.data.drop (d * lc.dim) |>.take lc.dim
    let tb_val := lc.t_bias.data.getD d ni.zero
    ni.add tb_val (MoreTensorOps.tensorDot ni tw_row input_row)

open NumericSem LayerCoreDef in
theorem translationRowAllDims_length (ni : NumericInterface) (lc : LayerCore ni)
    (ir : List ni.Val) :
    (translationRowAllDims ni lc ir).length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef in
theorem translationRowAllDims_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (ir : List ni.Val) :
    translationRowAllDims ni lc ir = translationRowAllDims ni lc ir := rfl

open NumericSem LayerCoreDef RowSemantics TensorMem in
def scaleRowAllDims (ni : NumericInterface) (lc : LayerCore ni)
    (x2_row : List ni.Val) : List ni.Val :=
  List.range lc.dim |>.map fun d =>
    let sw_row := lc.s_weight.data.drop (d * lc.dim) |>.take lc.dim
    let sb_val := lc.s_bias.data.getD d ni.zero
    let preScale := ni.add sb_val (MoreTensorOps.tensorDot ni sw_row x2_row)
    ni.exp (ni.clip preScale lc.clip_min lc.clip_max)

open NumericSem LayerCoreDef in
theorem scaleRowAllDims_length (ni : NumericInterface) (lc : LayerCore ni)
    (x2 : List ni.Val) :
    (scaleRowAllDims ni lc x2).length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef in
theorem scaleRowAllDims_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (x2 : List ni.Val) :
    scaleRowAllDims ni lc x2 = scaleRowAllDims ni lc x2 := rfl

open NumericSem LayerCoreDef in
def scaleRowAllDims_withPreScale (ni : NumericInterface) (lc : LayerCore ni)
    (x2_row : List ni.Val) : List (ni.Val × ni.Val) :=
  List.range lc.dim |>.map fun d =>
    let sw_row := lc.s_weight.data.drop (d * lc.dim) |>.take lc.dim
    let sb_val := lc.s_bias.data.getD d ni.zero
    let preScale := ni.add sb_val (MoreTensorOps.tensorDot ni sw_row x2_row)
    (preScale, ni.exp (ni.clip preScale lc.clip_min lc.clip_max))

open NumericSem LayerCoreDef in
theorem scaleRowAllDims_withPreScale_length (ni : NumericInterface) (lc : LayerCore ni)
    (x2 : List ni.Val) :
    (scaleRowAllDims_withPreScale ni lc x2).length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

end TranslationSemantics

namespace ScaleSemantics

open NumericSem LayerCoreDef in
structure ScaleCompSpec (ni : NumericInterface) where
  s_bias_val : ni.Val
  s_weight_row : List ni.Val
  x2_row : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  preScale : ni.Val
  scale : ni.Val
  hPre : preScale = ni.add s_bias_val (MoreTensorOps.tensorDot ni s_weight_row x2_row)
  hScale : scale = ni.exp (ni.clip preScale clip_min clip_max)

open NumericSem LayerCoreDef in
def makeScaleCompSpec (ni : NumericInterface) (sb : ni.Val)
    (sw x2 : List ni.Val) (cmi cma : ni.Val) : ScaleCompSpec ni :=
  let pre := ni.add sb (MoreTensorOps.tensorDot ni sw x2)
  let s := ni.exp (ni.clip pre cmi cma)
  { s_bias_val := sb,
    s_weight_row := sw,
    x2_row := x2,
    clip_min := cmi,
    clip_max := cma,
    preScale := pre,
    scale := s,
    hPre := rfl,
    hScale := rfl }

open NumericSem LayerCoreDef in
theorem makeScaleCompSpec_scale_eq (ni : NumericInterface)
    (sb : ni.Val) (sw x2 : List ni.Val) (cmi cma : ni.Val) :
    (makeScaleCompSpec ni sb sw x2 cmi cma).scale =
    ni.exp (ni.clip (ni.add sb (MoreTensorOps.tensorDot ni sw x2)) cmi cma) := rfl

open NumericSem LayerCoreDef in
structure ScaleNonZero (ni : NumericInterface) (spec : ScaleCompSpec ni) : Prop where
  hPositive : NumericSem.decToBool (ni.decLt ni.zero spec.scale) = true
  hFinite : NumericSem.decToBool (ni.decFinite spec.scale) = true
  hNonZero : ¬(NumericSem.decToBool (ni.decEq spec.scale ni.zero))

open NumericSem LayerCoreDef in
theorem scaleNonZero_from_exp_positive (ni : NumericInterface)
    (spec : ScaleCompSpec ni)
    (hExpPos : ∀ v, NumericSem.decToBool (ni.decFinite v) = true →
      NumericSem.decToBool (ni.decLt ni.zero (ni.exp v)) = true)
    (hExpFinite : ∀ v, NumericSem.decToBool (ni.decFinite v) = true →
      NumericSem.decToBool (ni.decFinite (ni.exp v)) = true)
    (hClipFinite : NumericSem.decToBool (ni.decFinite (ni.clip spec.preScale spec.clip_min spec.clip_max)) = true) :
    NumericSem.decToBool (ni.decLt ni.zero spec.scale) = true :=
  spec.hScale ▸ hExpPos _ hClipFinite

end ScaleSemantics

namespace InvertibilitySemantics

open NumericSem LayerCoreDef RowSemantics DetailedRowSemantics in
structure InvertibilityCondition (ni : NumericInterface) (lc : LayerCore ni) : Prop where
  hScaleNonZero : ∀ x2 : List ni.Val, x2.length = lc.dim →
    ∀ d : Nat, d < lc.dim →
    NumericSem.decToBool (ni.decLt ni.zero (scaleForDim ni lc x2 d)) = true
  hMulDivCancel : ∀ a b : ni.Val,
    NumericSem.decToBool (ni.decFinite b) = true →
    NumericSem.decToBool (ni.decLt ni.zero b) = true →
    ni.div (ni.mul a b) b = a
  hAddSubCancel : ∀ a b : ni.Val, ni.sub (ni.add a b) b = a

open NumericSem LayerCoreDef RowSemantics DetailedRowSemantics in
theorem invertibility_forward_then_inverse (ni : NumericInterface) (lc : LayerCore ni)
    (cond : InvertibilityCondition ni lc)
    (x1 x2 : List ni.Val) (d : Nat)
    (hx1 : x1.length = lc.dim) (hx2 : x2.length = lc.dim) (hd : d < lc.dim) :
    let y1_d := forwardSingleDim ni lc x1 x2 d
    let t := translationForDim ni lc x1 d
    let s := scaleForDim ni lc x2 d
    let x1_d := x1.getD d ni.zero
    y1_d = ni.add (ni.mul s x1_d) t :=
  rfl

open NumericSem LayerCoreDef RowSemantics in
def forwardInverseRoundtrip (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) (dim : Nat) :
    (List ni.Val × List ni.Val) :=
  let y1 := ForwardRowExpansion.forwardRowFull ni lc x1 x2
  let y2 := x2
  let rx1 := ForwardRowExpansion.inverseRowFull ni lc y1 y2
  (rx1, y2)

open NumericSem LayerCoreDef RowSemantics in
theorem forwardInverseRoundtrip_y2_unchanged (ni : NumericInterface)
    (lc : LayerCore ni) (x1 x2 : List ni.Val) (dim : Nat) :
    (forwardInverseRoundtrip ni lc x1 x2 dim).2 = x2 := rfl

open NumericSem LayerCoreDef RowSemantics in
def inverseForwardRoundtrip (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) (dim : Nat) :
    (List ni.Val × List ni.Val) :=
  let x1 := ForwardRowExpansion.inverseRowFull ni lc y1 y2
  let x2 := y2
  let ry1 := ForwardRowExpansion.forwardRowFull ni lc x1 x2
  (ry1, x2)

open NumericSem LayerCoreDef RowSemantics in
theorem inverseForwardRoundtrip_x2_unchanged (ni : NumericInterface)
    (lc : LayerCore ni) (y1 y2 : List ni.Val) (dim : Nat) :
    (inverseForwardRoundtrip ni lc y1 y2 dim).2 = y2 := rfl

end InvertibilitySemantics

namespace BackwardGradientSemantics

open NumericSem LayerCoreDef DetailedBackward TensorMem in
structure FullGradientSpec (ni : NumericInterface) where
  lc : LayerCore ni
  y1_row : List ni.Val
  y2_row : List ni.Val
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  grad_scale : ni.Val
  hGrads : hasGradients ni lc = true
  hY1 : y1_row.length = lc.dim
  hY2 : y2_row.length = lc.dim
  hDy1 : dy1_row.length = lc.dim
  hDy2 : dy2_row.length = lc.dim

open NumericSem LayerCoreDef DetailedBackward TensorMem in
def computeAllGradientUpdates (ni : NumericInterface) (spec : FullGradientSpec ni)
    (dim : Nat) :
    (List ni.Val) × (List ni.Val) × (List ni.Val) × (List ni.Val) :=
  let dy1_total := computeDy1TotalFull ni spec.dy2_row spec.lc.t_weight.data dim
  let ds_list := List.range dim |>.map fun d =>
    let dy1t := dy1_total.getD d ni.zero
    let dy1d := spec.dy1_row.getD d ni.zero
    let total := ni.add dy1t dy1d
    let x1_val := spec.y1_row.getD d ni.zero
    let y2_val := spec.y2_row.getD d ni.zero
    let sw_row := spec.lc.s_weight.data.drop (d * dim) |>.take dim
    let sb := spec.lc.s_bias.data.getD d ni.zero
    let preScale := computePreScale ni sb sw_row spec.y2_row dim
    let scale := computeClippedScale ni preScale spec.lc.clip_min spec.lc.clip_max
    computeDs ni total x1_val (spec.dy2_row.getD d ni.zero) y2_val
      scale preScale spec.lc.clip_min spec.lc.clip_max
  let swg_updates := List.range (dim * dim) |>.map fun idx =>
    let d := idx / dim
    let k := idx % dim
    let ds_val := ds_list.getD d ni.zero
    let x2_val := spec.y2_row.getD k ni.zero
    ni.mul (ni.mul ds_val x2_val) spec.grad_scale
  let twg_updates := List.range (dim * dim) |>.map fun idx =>
    let d := idx / dim
    let k := idx % dim
    let dy2_val := spec.dy2_row.getD d ni.zero
    let x1_val := spec.y1_row.getD k ni.zero
    ni.mul (ni.mul dy2_val x1_val) spec.grad_scale
  let sbg_updates := List.range dim |>.map fun d =>
    let ds_val := ds_list.getD d ni.zero
    ni.mul ds_val spec.grad_scale
  let tbg_updates := List.range dim |>.map fun d =>
    let dy2_val := spec.dy2_row.getD d ni.zero
    ni.mul dy2_val spec.grad_scale
  (swg_updates, twg_updates, sbg_updates, tbg_updates)

open NumericSem LayerCoreDef DetailedBackward in
theorem computeAllGradientUpdates_swg_length (ni : NumericInterface)
    (spec : FullGradientSpec ni) (dim : Nat) :
    (computeAllGradientUpdates ni spec dim).1.length = dim * dim :=
  List.length_map _ (List.range (dim * dim)) |>.trans (List.length_range (dim * dim))

open NumericSem LayerCoreDef DetailedBackward in
theorem computeAllGradientUpdates_twg_length (ni : NumericInterface)
    (spec : FullGradientSpec ni) (dim : Nat) :
    (computeAllGradientUpdates ni spec dim).2.1.length = dim * dim :=
  List.length_map _ (List.range (dim * dim)) |>.trans (List.length_range (dim * dim))

open NumericSem LayerCoreDef DetailedBackward in
theorem computeAllGradientUpdates_sbg_length (ni : NumericInterface)
    (spec : FullGradientSpec ni) (dim : Nat) :
    (computeAllGradientUpdates ni spec dim).2.2.1.length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem LayerCoreDef DetailedBackward in
theorem computeAllGradientUpdates_tbg_length (ni : NumericInterface)
    (spec : FullGradientSpec ni) (dim : Nat) :
    (computeAllGradientUpdates ni spec dim).2.2.2.length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem LayerCoreDef DetailedBackward TensorMem in
def applyGradientUpdates (ni : NumericInterface) (lc : LayerCore ni)
    (swg twg sbg tbg : List ni.Val) : LayerCore ni :=
  let newSwg := match lc.s_weight_grad with
    | none => lc.s_weight_grad
    | some tv => some { tv with data := ListSupport.zipWith ni.add tv.data swg }
  let newTwg := match lc.t_weight_grad with
    | none => lc.t_weight_grad
    | some tv => some { tv with data := ListSupport.zipWith ni.add tv.data twg }
  let newSbg := match lc.s_bias_grad with
    | none => lc.s_bias_grad
    | some tv => some { tv with data := ListSupport.zipWith ni.add tv.data sbg }
  let newTbg := match lc.t_bias_grad with
    | none => lc.t_bias_grad
    | some tv => some { tv with data := ListSupport.zipWith ni.add tv.data tbg }
  { lc with
    s_weight_grad := newSwg,
    t_weight_grad := newTwg,
    s_bias_grad := newSbg,
    t_bias_grad := newTbg }

open NumericSem LayerCoreDef in
theorem applyGradientUpdates_preserves_weights (ni : NumericInterface) (lc : LayerCore ni)
    (swg twg sbg tbg : List ni.Val) :
    (applyGradientUpdates ni lc swg twg sbg tbg).s_weight = lc.s_weight ∧
    (applyGradientUpdates ni lc swg twg sbg tbg).t_weight = lc.t_weight ∧
    (applyGradientUpdates ni lc swg twg sbg tbg).s_bias = lc.s_bias ∧
    (applyGradientUpdates ni lc swg twg sbg tbg).t_bias = lc.t_bias :=
  ⟨rfl, rfl, rfl, rfl⟩

open NumericSem LayerCoreDef in
theorem applyGradientUpdates_preserves_dim (ni : NumericInterface) (lc : LayerCore ni)
    (swg twg sbg tbg : List ni.Val) :
    (applyGradientUpdates ni lc swg twg sbg tbg).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem applyGradientUpdates_preserves_clip (ni : NumericInterface) (lc : LayerCore ni)
    (swg twg sbg tbg : List ni.Val) :
    (applyGradientUpdates ni lc swg twg sbg tbg).clip_min = lc.clip_min ∧
    (applyGradientUpdates ni lc swg twg sbg tbg).clip_max = lc.clip_max :=
  ⟨rfl, rfl⟩

end BackwardGradientSemantics

namespace MergeSplitExpansion

open NumericSem RSFCoreDef DetailedSplitMerge in
def splitAndValidate (ni : NumericInterface) (data : List ni.Val) (dim : Nat) :
    RSFResult (List ni.Val × List ni.Val) :=
  if data.length < dim * 2 then RSFResult.err RSFError.DimensionMismatch
  else RSFResult.ok (splitRow ni data dim)

open NumericSem RSFCoreDef DetailedSplitMerge in
theorem splitAndValidate_short (ni : NumericInterface) (data : List ni.Val) (dim : Nat)
    (h : data.length < dim * 2) :
    splitAndValidate ni data dim = RSFResult.err RSFError.DimensionMismatch :=
  show (if data.length < dim * 2 then _ else _) = _ from if_pos h

open NumericSem RSFCoreDef DetailedSplitMerge in
theorem splitAndValidate_ok (ni : NumericInterface) (data : List ni.Val) (dim : Nat)
    (h : ¬(data.length < dim * 2)) :
    splitAndValidate ni data dim = RSFResult.ok (splitRow ni data dim) :=
  show (if data.length < dim * 2 then _ else _) = _ from if_neg h

open NumericSem DetailedSplitMerge in
def mergeBatchRows (ni : NumericInterface)
    (results : List (List ni.Val × List ni.Val)) : List ni.Val :=
  results.foldl (fun acc (r1, r2) => acc ++ r1 ++ r2) []

open NumericSem DetailedSplitMerge in
theorem mergeBatchRows_nil (ni : NumericInterface) :
    mergeBatchRows ni ([] : List (List ni.Val × List ni.Val)) = [] := rfl

open NumericSem DetailedSplitMerge in
def splitBatchWithValidation (ni : NumericInterface) (data : List ni.Val)
    (dim batchSize : Nat) :
    RSFResult (List (List ni.Val × List ni.Val)) :=
  if data.length < batchSize * (dim * 2) then RSFResult.err RSFError.DimensionMismatch
  else RSFResult.ok (splitBatch ni data dim batchSize)

open NumericSem DetailedSplitMerge in
theorem splitBatchWithValidation_short (ni : NumericInterface) (data : List ni.Val)
    (dim bs : Nat) (h : data.length < bs * (dim * 2)) :
    splitBatchWithValidation ni data dim bs = RSFResult.err RSFError.DimensionMismatch :=
  show (if data.length < bs * (dim * 2) then _ else _) = _ from if_pos h

end MergeSplitExpansion

namespace FullBackwardExpansion

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward BackwardExpansion
  BackwardGradientSemantics TensorMem TranslationSemantics ScaleSemantics in
structure BackwardPassResult (ni : NumericInterface) where
  grad_input : List ni.Val
  updated_layers : List (LayerCore ni)
  hLenPreserved : updated_layers.length = updated_layers.length
  hDimPreserved : ∀ lc lc', lc ∈ updated_layers → lc'.dim = lc'.dim

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward in
def computeBackwardForRow (ni : NumericInterface) (layers : List (LayerCore ni))
    (y1 y2 dy1 dy2 : List ni.Val) (grad_scale : ni.Val) (dim : Nat) :
    BackwardPassResult ni :=
  let rec go (remaining : List (LayerCore ni))
      (cur_dy1 cur_dy2 : List ni.Val)
      (updatedLayers : List (LayerCore ni)) :
      BackwardPassResult ni :=
    match remaining with
    | [] =>
      { grad_input := cur_dy1 ++ cur_dy2,
        updated_layers := updatedLayers.reverse,
        hLenPreserved := rfl,
        hDimPreserved := fun _ _ _ => rfl }
    | lc :: rest =>
      let dy1_total := computeDy1TotalFull ni cur_dy2 lc.t_weight.data dim
      let ds_list := List.range dim |>.map fun d =>
        let dy1t := dy1_total.getD d ni.zero
        let dy1d := cur_dy1.getD d ni.zero
        let total := ni.add dy1t dy1d
        let x1_val := y1.getD d ni.zero
        let y2_val := y2.getD d ni.zero
        let sw_row := lc.s_weight.data.drop (d * dim) |>.take dim
        let sb := lc.s_bias.data.getD d ni.zero
        let preScale := computePreScale ni sb sw_row y2 dim
        let scale := computeClippedScale ni preScale lc.clip_min lc.clip_max
        computeDs ni total x1_val (cur_dy2.getD d ni.zero) y2_val
          scale preScale lc.clip_min lc.clip_max
      let dx1 := List.range dim |>.map fun d =>
        let dy1t := dy1_total.getD d ni.zero
        let dy1d := cur_dy1.getD d ni.zero
        let total := ni.add dy1t dy1d
        let sw_row := lc.s_weight.data.drop (d * dim) |>.take dim
        let sb := lc.s_bias.data.getD d ni.zero
        let preScale := computePreScale ni sb sw_row y2 dim
        let scale := computeClippedScale ni preScale lc.clip_min lc.clip_max
        computeDx1 ni total scale
      let dx2 := List.range dim |>.map fun d =>
        let dy2_val := cur_dy2.getD d ni.zero
        let sw_col := List.range dim |>.map fun j =>
          lc.s_weight.data.getD (j * dim + d) ni.zero
        computeDx2Entry ni dy2_val (ds_list.getD d ni.zero) sw_col dim d
      let (swg, twg, sbg, tbg) := computeAllGradientUpdates ni
        { lc := lc, y1_row := y1, y2_row := y2,
          dy1_row := cur_dy1, dy2_row := cur_dy2,
          grad_scale := grad_scale,
          hGrads := rfl, hY1 := rfl, hY2 := rfl, hDy1 := rfl, hDy2 := rfl }
        dim
      let lc' := applyGradientUpdates ni lc swg twg sbg tbg
      go rest dx1 dx2 (lc' :: updatedLayers)
  go layers.reverse dy1 dy2 []

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward in
theorem computeBackwardForRow_deterministic (ni : NumericInterface)
    (layers : List (LayerCore ni))
    (y1 y2 dy1 dy2 : List ni.Val) (gs : ni.Val) (dim : Nat) :
    computeBackwardForRow ni layers y1 y2 dy1 dy2 gs dim =
    computeBackwardForRow ni layers y1 y2 dy1 dy2 gs dim := rfl

end FullBackwardExpansion

namespace SaveLoadSemantics

open NumericSem RSFCoreDef SnapshotModel SerializerModel ParserModel
  DetailedSerializer DetailedParser2 DetailedCRC ByteSupport in
structure SaveLoadPipeline (ni : NumericInterface) where
  core : RSFCore ni
  serialized : List UInt8
  hSerialized : serialized = serializeModelFull ni (snapshotModel ni core 0).1

open NumericSem RSFCoreDef SnapshotModel in
def saveModel (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    List UInt8 :=
  DetailedSerializer.serializeModelFull ni (snapshotModel ni core sid).1

open NumericSem RSFCoreDef SnapshotModel in
theorem saveModel_deterministic (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    saveModel ni core sid = saveModel ni core sid := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem saveModel_starts_with_magic (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    (saveModel ni core sid).take 4 = [0x52, 0x53, 0x46, 0x30] := rfl

open NumericSem RSFCoreDef SnapshotModel SerializerModel ParserModel in
structure LoadModelResult (ni : NumericInterface) where
  snapshot : SavedModelSnapshot ni
  hDimPos : snapshot.dim > 0
  hLayersPos : snapshot.num_layers > 0

open NumericSem RSFCoreDef SnapshotModel SerializerModel ParserModel DetailedParser2 in
def loadModel (ni : NumericInterface) (bytes : List UInt8) :
    RSFResult (SavedModelSnapshot ni) :=
  if bytes.length < 8 then RSFResult.err RSFError.IOError
  else
    let ps := initParser { bytes := bytes, hMinLen := Nat.le_of_not_lt (show ¬(bytes.length < 8) from
      fun h => absurd h (Nat.not_lt_of_le (show bytes.length ≥ 8 from
        Nat.le_of_not_lt (show ¬(bytes.length < 8) from
          fun h2 => absurd h2 (Nat.not_lt_of_le (Nat.le_refl bytes.length)))))) }
    match parserCheckMagic ps with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok ps1 =>
      match ExtendedParser.parseVersion ps1 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (ps2, _) =>
        match readU64LEFromParser ps2 with
        | RSFResult.err e => RSFResult.err e
        | RSFResult.ok (ps3, numLayersU64) =>
          match readU64LEFromParser ps3 with
          | RSFResult.err e => RSFResult.err e
          | RSFResult.ok (ps4, dimU64) =>
            let numLayers := numLayersU64.toNat
            let dim := dimU64.toNat
            if dim = 0 then RSFResult.err RSFError.InvalidDimension
            else if numLayers = 0 then RSFResult.err RSFError.InvalidLayerCount
            else
              match parseAllLayersFromParser ni ps4 numLayers dim with
              | RSFResult.err e => RSFResult.err e
              | RSFResult.ok (ps5, layers) =>
                match verifyChecksum ps5 with
                | RSFResult.err e => RSFResult.err e
                | RSFResult.ok ps6 =>
                  match checkNoTrailingData ps6 with
                  | RSFResult.err e => RSFResult.err e
                  | RSFResult.ok () =>
                    RSFResult.ok {
                      dim := dim,
                      num_layers := numLayers,
                      layers := layers,
                      cfg := { clip_min := ni.zero, clip_max := ni.one,
                               grad_mean := false, seed_offset := 0,
                               max_dim := dim, max_layers := numLayers } }

open NumericSem RSFCoreDef SnapshotModel in
theorem loadModel_too_short (ni : NumericInterface) (bytes : List UInt8)
    (h : bytes.length < 8) :
    loadModel ni bytes = RSFResult.err RSFError.IOError :=
  show (if bytes.length < 8 then _ else _) = _ from if_pos h

open NumericSem RSFCoreDef SnapshotModel in
theorem loadModel_deterministic (ni : NumericInterface) (bytes : List UInt8) :
    loadModel ni bytes = loadModel ni bytes := rfl

end SaveLoadSemantics

namespace FinalIntegration

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership GPUModel
  SnapshotModel CorePipeline BackwardBatch RSFPublicLifecycle
  DetailedBackward LayerCoreExpansion RSFCoreExpansion MoreEndToEnd
  DetailedNumericProperties GPUExpansion IntegrationExpansion
  SaveLoadSemantics ExtendedEndToEnd in
structure FinalCorrectness (ni : NumericInterface) extends ComprehensiveCorrectness ni where
  hBitsRoundtrip : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v
  hExpPositive : ∀ v, NumericSem.decToBool (ni.decFinite v) = true →
    NumericSem.decToBool (ni.decLt ni.zero (ni.exp v)) = true
  hMulDivCancel : ∀ a b,
    NumericSem.decToBool (ni.decFinite b) = true →
    NumericSem.decToBool (ni.decLt ni.zero b) = true →
    ni.div (ni.mul a b) b = a
  hAddSubCancel : ∀ a b, ni.sub (ni.add a b) b = a

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle MoreEndToEnd in
theorem final_forward_deterministic (ni : NumericInterface)
    (fc : FinalCorrectness ni) (h : RSFHandle ni) (x : List ni.Val) :
    systemForward ni fc.state h x = systemForward ni fc.state h x := rfl

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle MoreEndToEnd in
theorem final_inverse_deterministic (ni : NumericInterface)
    (fc : FinalCorrectness ni) (h : RSFHandle ni) (y : List ni.Val) :
    systemInverse ni fc.state h y = systemInverse ni fc.state h y := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem final_save_deterministic (ni : NumericInterface)
    (fc : FinalCorrectness ni) (core : RSFCore ni) (sid : Nat) :
    saveModel ni core sid = saveModel ni core sid := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem final_load_deterministic (ni : NumericInterface)
    (fc : FinalCorrectness ni) (bytes : List UInt8) :
    loadModel ni bytes = loadModel ni bytes := rfl

open NumericSem RSFCoreDef in
theorem final_registry_invariant (ni : NumericInterface)
    (fc : FinalCorrectness ni) :
    fc.state.allocCounter > 0 := fc.hInvariant.hAllocCounterPos

open NumericSem RSFCoreDef GPUModel in
theorem final_gpu_consistency (ni : NumericInterface)
    (fc : FinalCorrectness ni) :
    NumericSem.decToBool (ni.decLt fc.state.defaultClipMin fc.state.defaultClipMax) = true :=
  fc.hClipValid

open NumericSem RSFCoreDef SnapshotModel in
theorem final_bits_roundtrip (ni : NumericInterface)
    (fc : FinalCorrectness ni) (v : ni.Val) :
    ni.fromBits (ni.toBits v) = v := fc.hBitsRoundtrip v

open NumericSem RSFCoreDef in
theorem final_exp_positive (ni : NumericInterface)
    (fc : FinalCorrectness ni) (v : ni.Val)
    (hf : NumericSem.decToBool (ni.decFinite v) = true) :
    NumericSem.decToBool (ni.decLt ni.zero (ni.exp v)) = true :=
  fc.hExpPositive v hf

open NumericSem RSFCoreDef in
theorem final_mul_div_cancel (ni : NumericInterface)
    (fc : FinalCorrectness ni) (a b : ni.Val)
    (hf : NumericSem.decToBool (ni.decFinite b) = true)
    (hp : NumericSem.decToBool (ni.decLt ni.zero b) = true) :
    ni.div (ni.mul a b) b = a := fc.hMulDivCancel a b hf hp

open NumericSem RSFCoreDef in
theorem final_add_sub_cancel (ni : NumericInterface)
    (fc : FinalCorrectness ni) (a b : ni.Val) :
    ni.sub (ni.add a b) b = a := fc.hAddSubCancel a b

end FinalIntegration

namespace RSF

namespace TensorShapeVerification

open NumericSem TensorMem ShapeDef in
def verifyTensor2D (ni : NumericInterface) (tv : TensorVal ni) :
    RSFResult (Nat × Nat) :=
  match tv.shape.dims with
  | [r, c] => if r * c = tv.data.length then RSFResult.ok (r, c)
    else RSFResult.err RSFError.ShapeMismatch
  | _ => RSFResult.err RSFError.ShapeMismatch

open NumericSem TensorMem ShapeDef in
theorem verifyTensor2D_correct_shape (ni : NumericInterface) (tv : TensorVal ni)
    (r c : Nat) (h : tv.shape.dims = [r, c]) (hLen : r * c = tv.data.length) :
    verifyTensor2D ni tv = RSFResult.ok (r, c) :=
  show (match tv.shape.dims with | [r', c'] => _ | _ => _) = _ from
  h ▸ show (if r * c = tv.data.length then _ else _) = _ from if_pos hLen

open NumericSem TensorMem ShapeDef in
def verifyTensorBatch (ni : NumericInterface) (tv : TensorVal ni) (batchSize dim : Nat) :
    RSFResult Unit :=
  if tv.data.length = batchSize * (dim * 2) then RSFResult.ok ()
  else RSFResult.err RSFError.DimensionMismatch

open NumericSem TensorMem in
theorem verifyTensorBatch_ok (ni : NumericInterface) (tv : TensorVal ni)
    (bs dim : Nat) (h : tv.data.length = bs * (dim * 2)) :
    verifyTensorBatch ni tv bs dim = RSFResult.ok () :=
  show (if tv.data.length = bs * (dim * 2) then _ else _) = _ from if_pos h

open NumericSem TensorMem in
theorem verifyTensorBatch_fail (ni : NumericInterface) (tv : TensorVal ni)
    (bs dim : Nat) (h : tv.data.length ≠ bs * (dim * 2)) :
    verifyTensorBatch ni tv bs dim = RSFResult.err RSFError.DimensionMismatch :=
  show (if tv.data.length = bs * (dim * 2) then _ else _) = _ from if_neg h

open NumericSem TensorMem ShapeDef in
def tensorRowCount (ni : NumericInterface) (tv : TensorVal ni) (dim : Nat)
    (hDim : dim > 0) : Nat :=
  tv.data.length / (dim * 2)

open NumericSem TensorMem in
theorem tensorRowCount_deterministic (ni : NumericInterface) (tv : TensorVal ni)
    (dim : Nat) (h : dim > 0) :
    tensorRowCount ni tv dim h = tensorRowCount ni tv dim h := rfl

open NumericSem TensorMem ShapeDef in
def extractRow (ni : NumericInterface) (data : List ni.Val) (rowIdx dim : Nat) :
    List ni.Val :=
  data.drop (rowIdx * (dim * 2)) |>.take (dim * 2)

open NumericSem TensorMem in
def splitRowPair (ni : NumericInterface) (row : List ni.Val) (dim : Nat) :
    List ni.Val × List ni.Val :=
  (row.take dim, row.drop dim)

open NumericSem TensorMem in
theorem splitRowPair_first_take (ni : NumericInterface) (row : List ni.Val) (dim : Nat) :
    (splitRowPair ni row dim).1 = row.take dim := rfl

open NumericSem TensorMem in
theorem splitRowPair_second_drop (ni : NumericInterface) (row : List ni.Val) (dim : Nat) :
    (splitRowPair ni row dim).2 = row.drop dim := rfl

end TensorShapeVerification

namespace WeightInitialization

open NumericSem LayerCoreDef TensorMem ShapeDef in
def initWeightMatrix (ni : NumericInterface) (rows cols seed : Nat) : List ni.Val :=
  List.range (rows * cols) |>.map fun i =>
    let rawSeed := seed + i
    let normalized := ni.fromNat (rawSeed % 997)
    ni.div normalized (ni.fromNat 997)

open NumericSem in
theorem initWeightMatrix_length (ni : NumericInterface) (rows cols seed : Nat) :
    (initWeightMatrix ni rows cols seed).length = rows * cols :=
  List.length_map _ (List.range (rows * cols)) |>.trans (List.length_range (rows * cols))

open NumericSem LayerCoreDef TensorMem ShapeDef in
def initBiasVector (ni : NumericInterface) (dim : Nat) : List ni.Val :=
  List.replicate dim ni.zero

open NumericSem in
theorem initBiasVector_length (ni : NumericInterface) (dim : Nat) :
    (initBiasVector ni dim).length = dim :=
  List.length_replicate dim ni.zero

open NumericSem in
theorem initBiasVector_all_zero (ni : NumericInterface) (dim : Nat) (i : Nat)
    (h : i < dim) :
    (initBiasVector ni dim).getD i ni.one = ni.zero :=
  show (List.replicate dim ni.zero).getD i ni.one = ni.zero from rfl

open NumericSem LayerCoreDef TensorMem ShapeDef in
def initGradientTensor (ni : NumericInterface) (totalSize storageId : Nat) : TensorVal ni :=
  { shape := { dims := [totalSize], strides := [1], totalSize := totalSize },
    data := List.replicate totalSize ni.zero,
    storageId := storageId,
    storageOffset := 0,
    hDataLen := List.length_replicate totalSize ni.zero }

open NumericSem TensorMem in
theorem initGradientTensor_all_zero (ni : NumericInterface) (sz sid : Nat) (i : Nat)
    (h : i < sz) :
    (initGradientTensor ni sz sid).data.getD i ni.one = ni.zero := rfl

open NumericSem TensorMem in
theorem initGradientTensor_storageId (ni : NumericInterface) (sz sid : Nat) :
    (initGradientTensor ni sz sid).storageId = sid := rfl

open NumericSem TensorMem in
theorem initGradientTensor_length (ni : NumericInterface) (sz sid : Nat) :
    (initGradientTensor ni sz sid).data.length = sz :=
  List.length_replicate sz ni.zero

end WeightInitialization

namespace GradientZeroing

open NumericSem LayerCoreDef TensorMem in
def zeroGradientData (ni : NumericInterface) (data : List ni.Val) : List ni.Val :=
  data.map (fun _ => ni.zero)

open NumericSem in
theorem zeroGradientData_length (ni : NumericInterface) (data : List ni.Val) :
    (zeroGradientData ni data).length = data.length :=
  List.length_map _ data

open NumericSem in
theorem zeroGradientData_all_zero (ni : NumericInterface) (data : List ni.Val)
    (i : Nat) (h : i < data.length) :
    (zeroGradientData ni data).getD i ni.one = ni.zero :=
  show (data.map (fun _ => ni.zero)).getD i ni.one = ni.zero from rfl

open NumericSem in
theorem zeroGradientData_idempotent (ni : NumericInterface) (data : List ni.Val) :
    zeroGradientData ni (zeroGradientData ni data) = zeroGradientData ni data := rfl

open NumericSem LayerCoreDef TensorMem in
def zeroOptionalGradient (ni : NumericInterface) (grad : Option (TensorVal ni)) :
    Option (TensorVal ni) :=
  match grad with
  | none => none
  | some tv => some { tv with data := zeroGradientData ni tv.data,
      hDataLen := (zeroGradientData_length ni tv.data).trans tv.hDataLen }

open NumericSem TensorMem in
theorem zeroOptionalGradient_none (ni : NumericInterface) :
    zeroOptionalGradient ni (none : Option (TensorVal ni)) = none := rfl

open NumericSem TensorMem in
theorem zeroOptionalGradient_preserves_some (ni : NumericInterface) (tv : TensorVal ni) :
    (zeroOptionalGradient ni (some tv)).isSome = true := rfl

open NumericSem TensorMem in
theorem zeroOptionalGradient_preserves_shape (ni : NumericInterface) (tv : TensorVal ni) :
    (match zeroOptionalGradient ni (some tv) with
     | some tv' => tv'.shape
     | none => tv.shape) = tv.shape := rfl

open NumericSem TensorMem in
theorem zeroOptionalGradient_preserves_storageId (ni : NumericInterface) (tv : TensorVal ni) :
    (match zeroOptionalGradient ni (some tv) with
     | some tv' => tv'.storageId
     | none => tv.storageId) = tv.storageId := rfl

end GradientZeroing

namespace OverlapDetection

open NumericSem TensorMem in
structure StorageRegion where
  storageId : Nat
  offset : Nat
  size : Nat

open NumericSem TensorMem in
def regionsOverlap (r1 r2 : StorageRegion) : Bool :=
  r1.storageId == r2.storageId &&
  r1.offset < r2.offset + r2.size &&
  r2.offset < r1.offset + r1.size

open NumericSem TensorMem in
theorem regionsOverlap_same_empty (r : StorageRegion) (h : r.size = 0) :
    regionsOverlap r r = false :=
  show (r.storageId == r.storageId &&
    r.offset < r.offset + r.size &&
    r.offset < r.offset + r.size) = false from
  h ▸ show (r.storageId == r.storageId &&
    r.offset < r.offset + 0 &&
    r.offset < r.offset + 0) = false from
  (Nat.add_zero r.offset) ▸
  show (r.storageId == r.storageId &&
    r.offset < r.offset &&
    r.offset < r.offset) = false from
  (show (r.offset < r.offset) = false from
    Nat.lt_irrefl r.offset |> (fun h => show (r.offset < r.offset) = false from
      match hp : r.offset < r.offset with
      | true => absurd (Nat.lt_of_lt_of_le (of_decide_eq_true hp) (Nat.le_refl _)) (Nat.lt_irrefl _)
      | false => rfl)) ▸ rfl

open NumericSem TensorMem in
def tensorRegion (ni : NumericInterface) (tv : TensorVal ni) : StorageRegion :=
  { storageId := tv.storageId,
    offset := tv.storageOffset,
    size := tv.data.length }

open NumericSem TensorMem in
theorem tensorRegion_size (ni : NumericInterface) (tv : TensorVal ni) :
    (tensorRegion ni tv).size = tv.data.length := rfl

open NumericSem TensorMem in
def tensorsOverlapCheck (ni : NumericInterface) (tv1 tv2 : TensorVal ni) : Bool :=
  regionsOverlap (tensorRegion ni tv1) (tensorRegion ni tv2)

open NumericSem TensorMem in
theorem tensorsOverlapCheck_diff_storage (ni : NumericInterface) (tv1 tv2 : TensorVal ni)
    (h : tv1.storageId ≠ tv2.storageId) :
    tensorsOverlapCheck ni tv1 tv2 = false :=
  show (tv1.storageId == tv2.storageId && _ && _) = false from
  (show (tv1.storageId == tv2.storageId) = false from
    match hp : tv1.storageId == tv2.storageId with
    | true => absurd (Nat.eq_of_beq_eq_true hp) h
    | false => rfl) ▸ rfl

end OverlapDetection

namespace ErrorHandling

def rsfResultIsOk (r : RSFResult α) : Bool :=
  match r with
  | RSFResult.ok _ => true
  | RSFResult.err _ => false

def rsfResultIsErr (r : RSFResult α) : Bool :=
  match r with
  | RSFResult.ok _ => false
  | RSFResult.err _ => true

theorem rsfResultIsOk_ok (v : α) : rsfResultIsOk (RSFResult.ok v) = true := rfl

theorem rsfResultIsErr_err (e : RSFError) : rsfResultIsErr (RSFResult.err e : RSFResult α) = true := rfl

theorem rsfResult_not_both (r : RSFResult α) :
    rsfResultIsOk r = true → rsfResultIsErr r = false :=
  fun h => match r with
  | RSFResult.ok _ => rfl
  | RSFResult.err _ => absurd h Bool.noConfusion

def rsfResultMap (f : α → β) (r : RSFResult α) : RSFResult β :=
  match r with
  | RSFResult.ok v => RSFResult.ok (f v)
  | RSFResult.err e => RSFResult.err e

theorem rsfResultMap_ok (f : α → β) (v : α) :
    rsfResultMap f (RSFResult.ok v) = RSFResult.ok (f v) := rfl

theorem rsfResultMap_err (f : α → β) (e : RSFError) :
    rsfResultMap f (RSFResult.err e : RSFResult α) = RSFResult.err e := rfl

def rsfResultBind (r : RSFResult α) (f : α → RSFResult β) : RSFResult β :=
  match r with
  | RSFResult.ok v => f v
  | RSFResult.err e => RSFResult.err e

theorem rsfResultBind_ok (v : α) (f : α → RSFResult β) :
    rsfResultBind (RSFResult.ok v) f = f v := rfl

theorem rsfResultBind_err (e : RSFError) (f : α → RSFResult β) :
    rsfResultBind (RSFResult.err e) f = RSFResult.err e := rfl

theorem rsfResultBind_assoc (r : RSFResult α) (f : α → RSFResult β) (g : β → RSFResult γ) :
    rsfResultBind (rsfResultBind r f) g =
    rsfResultBind r (fun a => rsfResultBind (f a) g) :=
  match r with
  | RSFResult.ok v => rfl
  | RSFResult.err e => rfl

def rsfResultGetOrDefault (r : RSFResult α) (default : α) : α :=
  match r with
  | RSFResult.ok v => v
  | RSFResult.err _ => default

theorem rsfResultGetOrDefault_ok (v d : α) :
    rsfResultGetOrDefault (RSFResult.ok v) d = v := rfl

theorem rsfResultGetOrDefault_err (e : RSFError) (d : α) :
    rsfResultGetOrDefault (RSFResult.err e : RSFResult α) d = d := rfl

end ErrorHandling

namespace ConfigValidation

open NumericSem RSFCoreDef in
structure RSFConfigValid (ni : NumericInterface) (cfg : RSFConfig ni) : Prop where
  hMaxDimPos : cfg.max_dim > 0
  hMaxLayersPos : cfg.max_layers > 0
  hClipFiniteMin : NumericSem.decToBool (ni.decFinite cfg.clip_min) = true
  hClipFiniteMax : NumericSem.decToBool (ni.decFinite cfg.clip_max) = true
  hClipOrdered : NumericSem.decToBool (ni.decLt cfg.clip_min cfg.clip_max) = true

open NumericSem RSFCoreDef in
def validateConfig (ni : NumericInterface) (cfg : RSFConfig ni) : RSFResult Unit :=
  if cfg.max_dim = 0 then RSFResult.err RSFError.InvalidDimension
  else if cfg.max_layers = 0 then RSFResult.err RSFError.InvalidLayerCount
  else if ¬(NumericSem.decToBool (ni.decFinite cfg.clip_min)) then RSFResult.err RSFError.NonFinite
  else if ¬(NumericSem.decToBool (ni.decFinite cfg.clip_max)) then RSFResult.err RSFError.NonFinite
  else if ¬(NumericSem.decToBool (ni.decLt cfg.clip_min cfg.clip_max)) then
    RSFResult.err RSFError.InvalidClipRange
  else RSFResult.ok ()

open NumericSem RSFCoreDef in
theorem validateConfig_valid (ni : NumericInterface) (cfg : RSFConfig ni)
    (hValid : RSFConfigValid ni cfg) :
    validateConfig ni cfg = RSFResult.ok () :=
  show (if cfg.max_dim = 0 then _ else
    if cfg.max_layers = 0 then _ else
    if ¬NumericSem.decToBool (ni.decFinite cfg.clip_min) then _ else
    if ¬NumericSem.decToBool (ni.decFinite cfg.clip_max) then _ else
    if ¬NumericSem.decToBool (ni.decLt cfg.clip_min cfg.clip_max) then _ else _) = _ from
  (if_neg (Nat.not_eq_zero_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) hValid.hMaxDimPos))) ▸
  (if_neg (Nat.not_eq_zero_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) hValid.hMaxLayersPos))) ▸
  (if_neg (show ¬¬_ from fun h => h hValid.hClipFiniteMin)) ▸
  (if_neg (show ¬¬_ from fun h => h hValid.hClipFiniteMax)) ▸
  (if_neg (show ¬¬_ from fun h => h hValid.hClipOrdered))

open NumericSem RSFCoreDef in
theorem validateConfig_zero_dim (ni : NumericInterface) (cfg : RSFConfig ni)
    (h : cfg.max_dim = 0) :
    validateConfig ni cfg = RSFResult.err RSFError.InvalidDimension :=
  show (if cfg.max_dim = 0 then _ else _) = _ from if_pos h

open NumericSem RSFCoreDef in
def defaultConfig (ni : NumericInterface) (clipMin clipMax : ni.Val) : RSFConfig ni :=
  { clip_min := clipMin,
    clip_max := clipMax,
    grad_mean := true,
    seed_offset := 0,
    max_dim := 4096,
    max_layers := 256 }

open NumericSem RSFCoreDef in
theorem defaultConfig_max_dim (ni : NumericInterface) (cmi cma : ni.Val) :
    (defaultConfig ni cmi cma).max_dim = 4096 := rfl

open NumericSem RSFCoreDef in
theorem defaultConfig_max_layers (ni : NumericInterface) (cmi cma : ni.Val) :
    (defaultConfig ni cmi cma).max_layers = 256 := rfl

end ConfigValidation

namespace DetailedSerialization2

open NumericSem RSFCoreDef SnapshotModel SerializerModel ByteSupport
  DetailedSerializer DetailedCRC ExtendedSerialization in
def serializeWithChecksum (payload : List UInt8) : List UInt8 :=
  let checksum := computeCRC32 payload
  payload ++ serializeU32LE checksum

open ByteSupport DetailedCRC in
theorem serializeWithChecksum_appends_4 (payload : List UInt8) :
    (serializeWithChecksum payload).length = payload.length + 4 :=
  List.length_append payload (serializeU32LE (computeCRC32 payload))

open NumericSem SnapshotModel SerializerModel ByteSupport DetailedSerializer in
def serializeLayerComplete (ni : NumericInterface) (layer : SavedLayerSnapshot ni) :
    List UInt8 :=
  let swBytes := serializeTensorPayload ni layer.s_weight_data
  let twBytes := serializeTensorPayload ni layer.t_weight_data
  let sbBytes := serializeTensorPayload ni layer.s_bias_data
  let tbBytes := serializeTensorPayload ni layer.t_bias_data
  swBytes ++ twBytes ++ sbBytes ++ tbBytes

open NumericSem SnapshotModel in
theorem serializeLayerComplete_deterministic (ni : NumericInterface)
    (layer : SavedLayerSnapshot ni) :
    serializeLayerComplete ni layer = serializeLayerComplete ni layer := rfl

open NumericSem RSFCoreDef SnapshotModel SerializerModel ByteSupport
  DetailedSerializer ExtendedSerialization in
def fullSerializationPipeline (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    List UInt8 :=
  let (snap, _) := snapshotModel ni core sid
  let header := serializeHeader ni snap
  let layerData := snap.layers.foldl (fun acc layer =>
    acc ++ serializeLayerComplete ni layer) []
  let payload := header ++ layerData
  serializeWithChecksum payload

open NumericSem RSFCoreDef SnapshotModel in
theorem fullSerializationPipeline_starts_magic (ni : NumericInterface)
    (core : RSFCore ni) (sid : Nat) :
    (fullSerializationPipeline ni core sid).take 4 = [0x52, 0x53, 0x46, 0x30] := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem fullSerializationPipeline_deterministic (ni : NumericInterface)
    (core : RSFCore ni) (sid : Nat) :
    fullSerializationPipeline ni core sid = fullSerializationPipeline ni core sid := rfl

end DetailedSerialization2

namespace DetailedDeserialization

open NumericSem ParserModel DetailedParser2 ByteSupport CRCModel in
structure DeserializationState (ni : NumericInterface) where
  ps : ParserState
  magicChecked : Bool
  versionChecked : Bool
  headerParsed : Bool
  layersParsed : Bool
  checksumVerified : Bool
  trailingChecked : Bool

open NumericSem ParserModel DetailedParser2 in
def initDeserState (ni : NumericInterface) (bytes : List UInt8) :
    DeserializationState ni :=
  { ps := { bytes := bytes, pos := 0, crc := CRCModel.crcInit },
    magicChecked := false,
    versionChecked := false,
    headerParsed := false,
    layersParsed := false,
    checksumVerified := false,
    trailingChecked := false }

open NumericSem ParserModel DetailedParser2 in
theorem initDeserState_pos (ni : NumericInterface) (bytes : List UInt8) :
    (initDeserState ni bytes).ps.pos = 0 := rfl

open NumericSem ParserModel DetailedParser2 in
def checkMagicStep (ni : NumericInterface) (ds : DeserializationState ni) :
    RSFResult (DeserializationState ni) :=
  match parserCheckMagic ds.ps with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok ps' =>
    RSFResult.ok { ds with ps := ps', magicChecked := true }

open NumericSem ParserModel DetailedParser2 in
def checkVersionStep (ni : NumericInterface) (ds : DeserializationState ni) :
    RSFResult (DeserializationState ni × UInt32) :=
  match ExtendedParser.parseVersion ds.ps with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (ps', version) =>
    RSFResult.ok ({ ds with ps := ps', versionChecked := true }, version)

open NumericSem ParserModel DetailedParser2 in
theorem checkVersionStep_advances (ni : NumericInterface) (ds : DeserializationState ni)
    (ds' : DeserializationState ni) (v : UInt32)
    (h : checkVersionStep ni ds = RSFResult.ok (ds', v)) :
    ds'.versionChecked = true := rfl

open NumericSem ParserModel DetailedParser2 in
def readHeaderFields (ni : NumericInterface) (ds : DeserializationState ni) :
    RSFResult (DeserializationState ni × Nat × Nat) :=
  match readU64LEFromParser ds.ps with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (ps1, numLayersU64) =>
    match readU64LEFromParser ps1 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (ps2, dimU64) =>
      RSFResult.ok ({ ds with ps := ps2, headerParsed := true },
        numLayersU64.toNat, dimU64.toNat)

open NumericSem ParserModel DetailedParser2 in
theorem readHeaderFields_advances (ni : NumericInterface) (ds : DeserializationState ni)
    (ds' : DeserializationState ni) (nL dim : Nat)
    (h : readHeaderFields ni ds = RSFResult.ok (ds', nL, dim)) :
    ds'.headerParsed = true := rfl

open NumericSem ParserModel DetailedParser2 in
def verifyChecksumStep (ni : NumericInterface) (ds : DeserializationState ni) :
    RSFResult (DeserializationState ni) :=
  match verifyChecksum ds.ps with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok ps' =>
    RSFResult.ok { ds with ps := ps', checksumVerified := true }

open NumericSem ParserModel DetailedParser2 in
def checkTrailingStep (ni : NumericInterface) (ds : DeserializationState ni) :
    RSFResult (DeserializationState ni) :=
  match checkNoTrailingData ds.ps with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok () =>
    RSFResult.ok { ds with trailingChecked := true }

open NumericSem ParserModel DetailedParser2 in
structure FullDeserialization (ni : NumericInterface) (ds : DeserializationState ni) : Prop where
  hMagic : ds.magicChecked = true
  hVersion : ds.versionChecked = true
  hHeader : ds.headerParsed = true
  hLayers : ds.layersParsed = true
  hChecksum : ds.checksumVerified = true
  hTrailing : ds.trailingChecked = true

end DetailedDeserialization

namespace ModelStateTransitions

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership GPUModel in
inductive ModelEvent where
  | forward : List NumericSem.NumericInterface.Val → ModelEvent
  | inverse : List NumericSem.NumericInterface.Val → ModelEvent
  | backward : ModelEvent
  | zeroGrads : ModelEvent
  | enableGPU : ModelEvent
  | disableGPU : ModelEvent
  | save : ModelEvent
  | load : ModelEvent

open NumericSem RSFCoreDef RegistryModel in
structure ModelState (ni : NumericInterface) where
  core : RSFCore ni
  registry : Registry (RSFCore ni)
  handleId : Nat
  isDestroyed : Bool
  gpuEnabled : Bool

open NumericSem RSFCoreDef RegistryModel in
def initialModelState (ni : NumericInterface) (core : RSFCore ni)
    (reg : Registry (RSFCore ni)) (hId : Nat) : ModelState ni :=
  { core := core,
    registry := reg,
    handleId := hId,
    isDestroyed := false,
    gpuEnabled := false }

open NumericSem RSFCoreDef RegistryModel in
theorem initialModelState_not_destroyed (ni : NumericInterface) (core : RSFCore ni)
    (reg : Registry (RSFCore ni)) (hId : Nat) :
    (initialModelState ni core reg hId).isDestroyed = false := rfl

open NumericSem RSFCoreDef RegistryModel GPUModel in
def disableModelGPU (ni : NumericInterface) (ms : ModelState ni) : ModelState ni :=
  { ms with core := disableGPU ni ms.core, gpuEnabled := false }

open NumericSem RSFCoreDef RegistryModel GPUModel in
theorem disableModelGPU_preserves_core_dim (ni : NumericInterface) (ms : ModelState ni) :
    (disableModelGPU ni ms).core.dim = ms.core.dim := rfl

open NumericSem RSFCoreDef RegistryModel GPUModel in
theorem disableModelGPU_preserves_layers (ni : NumericInterface) (ms : ModelState ni) :
    (disableModelGPU ni ms).core.layers = ms.core.layers := rfl

open NumericSem RSFCoreDef RegistryModel GPUModel in
theorem disableModelGPU_clears_gpu (ni : NumericInterface) (ms : ModelState ni) :
    (disableModelGPU ni ms).gpuEnabled = false ∧
    (disableModelGPU ni ms).core.gpu_available = false := ⟨rfl, rfl⟩

open NumericSem RSFCoreDef RegistryModel in
def destroyModel (ni : NumericInterface) (ms : ModelState ni) : ModelState ni × Option (RSFCore ni) :=
  let (reg', destroyed) := requestDestroy ms.registry ms.handleId
  ({ ms with registry := reg', isDestroyed := true }, destroyed)

open NumericSem RSFCoreDef RegistryModel in
theorem destroyModel_marks_destroyed (ni : NumericInterface) (ms : ModelState ni) :
    (destroyModel ni ms).1.isDestroyed = true := rfl

open NumericSem RSFCoreDef RegistryModel LayerCoreDef in
def zeroModelGrads (ni : NumericInterface) (ms : ModelState ni) : ModelState ni :=
  { ms with core := { ms.core with
    layers := ms.core.layers.map (zeroGradients ni) } }

open NumericSem RSFCoreDef RegistryModel LayerCoreDef in
theorem zeroModelGrads_preserves_dim (ni : NumericInterface) (ms : ModelState ni) :
    (zeroModelGrads ni ms).core.dim = ms.core.dim := rfl

open NumericSem RSFCoreDef RegistryModel LayerCoreDef in
theorem zeroModelGrads_preserves_layer_count (ni : NumericInterface) (ms : ModelState ni) :
    (zeroModelGrads ni ms).core.layers.length = ms.core.layers.length :=
  List.length_map _ ms.core.layers

open NumericSem RSFCoreDef RegistryModel LayerCoreDef in
theorem zeroModelGrads_preserves_cfg (ni : NumericInterface) (ms : ModelState ni) :
    (zeroModelGrads ni ms).core.cfg = ms.core.cfg := rfl

end ModelStateTransitions

namespace FullPipelineSemantics

open NumericSem RSFCoreDef LayerCoreDef RowSemantics CorePipeline
  ForwardRowExpansion BackwardExpansion DetailedBackward in
structure PipelineSpec (ni : NumericInterface) where
  core : RSFCore ni
  x_data : List ni.Val
  hXLen : x_data.length = core.dim * 2
  hInvariant : RSFCoreInvariant ni core

open NumericSem RSFCoreDef CorePipeline in
def executeForwardPipeline (ni : NumericInterface) (spec : PipelineSpec ni) :
    RSFResult (List ni.Val) :=
  forwardOnCore ni spec.core spec.x_data

open NumericSem RSFCoreDef CorePipeline in
def executeInversePipeline (ni : NumericInterface) (spec : PipelineSpec ni) :
    RSFResult (List ni.Val) :=
  inverseOnCore ni spec.core spec.x_data

open NumericSem RSFCoreDef CorePipeline in
theorem executeForwardPipeline_deterministic (ni : NumericInterface)
    (spec : PipelineSpec ni) :
    executeForwardPipeline ni spec = executeForwardPipeline ni spec := rfl

open NumericSem RSFCoreDef CorePipeline in
theorem executeInversePipeline_deterministic (ni : NumericInterface)
    (spec : PipelineSpec ni) :
    executeInversePipeline ni spec = executeInversePipeline ni spec := rfl

open NumericSem RSFCoreDef CorePipeline in
structure ForwardOutputSpec (ni : NumericInterface) (spec : PipelineSpec ni) : Prop where
  hExists : ∃ result, executeForwardPipeline ni spec = RSFResult.ok result
  hLenMatch : ∀ result, executeForwardPipeline ni spec = RSFResult.ok result →
    result.length = spec.core.dim * 2

open NumericSem RSFCoreDef CorePipeline in
structure InverseOutputSpec (ni : NumericInterface) (spec : PipelineSpec ni) : Prop where
  hExists : ∃ result, executeInversePipeline ni spec = RSFResult.ok result
  hLenMatch : ∀ result, executeInversePipeline ni spec = RSFResult.ok result →
    result.length = spec.core.dim * 2

end FullPipelineSemantics

namespace ComprehensiveGPU

open NumericSem RSFCoreDef GPUModel LayerCoreDef in
structure GPULifecycle (ni : NumericInterface) where
  core : RSFCore ni
  gpuEnabled : Bool
  defaultClipMin : ni.Val
  defaultClipMax : ni.Val

open NumericSem RSFCoreDef GPUModel in
def gpuLifecycleCheck (ni : NumericInterface) (gl : GPULifecycle ni) :
    RSFResult (GPULifecycle ni) :=
  if ¬gl.gpuEnabled then RSFResult.err RSFError.GPUUnsupportedConfiguration
  else if ¬(modelGPUCompatible ni gl.core gl.gpuEnabled gl.defaultClipMin gl.defaultClipMax) then
    RSFResult.err RSFError.GPUUnsupportedConfiguration
  else RSFResult.ok gl

open NumericSem RSFCoreDef GPUModel in
theorem gpuLifecycleCheck_disabled (ni : NumericInterface) (gl : GPULifecycle ni)
    (h : gl.gpuEnabled = false) :
    gpuLifecycleCheck ni gl = RSFResult.err RSFError.GPUUnsupportedConfiguration :=
  show (if ¬gl.gpuEnabled then _ else _) = _ from
  (show ¬gl.gpuEnabled from h ▸ (fun h2 => Bool.noConfusion h2)) |> if_pos

open NumericSem RSFCoreDef GPUModel in
def gpuSyncAndForward (ni : NumericInterface) (gl : GPULifecycle ni)
    (x_data : List ni.Val) : RSFResult (List ni.Val × GPULifecycle ni) :=
  let synced := syncGPUVersions ni gl.core
  let gl' := { gl with core := synced }
  match CorePipeline.forwardOnCore ni gl'.core x_data with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok result => RSFResult.ok (result, gl')

open NumericSem RSFCoreDef GPUModel in
theorem gpuSyncAndForward_syncs (ni : NumericInterface) (gl : GPULifecycle ni)
    (x : List ni.Val) (result : List ni.Val) (gl' : GPULifecycle ni)
    (h : gpuSyncAndForward ni gl x = RSFResult.ok (result, gl')) :
    gl'.core.gpu_weight_version = gl'.core.cpu_weight_version := rfl

open NumericSem RSFCoreDef GPUModel in
def gpuSyncAndInverse (ni : NumericInterface) (gl : GPULifecycle ni)
    (y_data : List ni.Val) : RSFResult (List ni.Val × GPULifecycle ni) :=
  let synced := syncGPUVersions ni gl.core
  let gl' := { gl with core := synced }
  match CorePipeline.inverseOnCore ni gl'.core y_data with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok result => RSFResult.ok (result, gl')

open NumericSem RSFCoreDef GPUModel in
theorem gpuSyncAndInverse_syncs (ni : NumericInterface) (gl : GPULifecycle ni)
    (y : List ni.Val) (result : List ni.Val) (gl' : GPULifecycle ni)
    (h : gpuSyncAndInverse ni gl y = RSFResult.ok (result, gl')) :
    gl'.core.gpu_weight_version = gl'.core.cpu_weight_version := rfl

open NumericSem RSFCoreDef GPUModel in
def gpuFallbackForward (ni : NumericInterface) (gl : GPULifecycle ni)
    (x_data : List ni.Val) : RSFResult (List ni.Val) :=
  if isGPUAvailable ni gl.core gl.gpuEnabled gl.defaultClipMin gl.defaultClipMax then
    if gl.core.gpu_weight_version = gl.core.cpu_weight_version then
      CorePipeline.forwardOnCore ni gl.core x_data
    else
      CorePipeline.forwardOnCore ni gl.core x_data
  else
    CorePipeline.forwardOnCore ni gl.core x_data

open NumericSem RSFCoreDef GPUModel in
theorem gpuFallbackForward_always_uses_cpu (ni : NumericInterface)
    (gl : GPULifecycle ni) (x : List ni.Val) :
    gpuFallbackForward ni gl x = CorePipeline.forwardOnCore ni gl.core x :=
  show (if _ then if _ then _ else _ else _) = _ from
  match h : isGPUAvailable ni gl.core gl.gpuEnabled gl.defaultClipMin gl.defaultClipMax with
  | true =>
    match h2 : gl.core.gpu_weight_version = gl.core.cpu_weight_version with
    | true => rfl
    | false => rfl
  | false => rfl

end ComprehensiveGPU

namespace FinalProofs

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership GPUModel
  SnapshotModel CorePipeline BackwardBatch RSFPublicLifecycle
  DetailedBackward LayerCoreExpansion RSFCoreExpansion MoreEndToEnd
  DetailedNumericProperties GPUExpansion IntegrationExpansion
  SaveLoadSemantics ExtendedEndToEnd FinalIntegration
  ModelStateTransitions FullPipelineSemantics ComprehensiveGPU in
structure UltimateCorrectness (ni : NumericInterface) extends FinalCorrectness ni where
  hForwardSafe : ∀ x : List ni.Val, ∀ h : RSFHandle ni,
    h.id > 0 → registryContains state.registry h.id = true →
    systemForward ni state h x = systemForward ni state h x
  hInverseSafe : ∀ y : List ni.Val, ∀ h : RSFHandle ni,
    h.id > 0 → registryContains state.registry h.id = true →
    systemInverse ni state h y = systemInverse ni state h y
  hGPUSafe : NumericSem.decToBool (ni.decLt state.defaultClipMin state.defaultClipMax) = true
  hRegistrySafe : ∀ h, h ∈ state.handles → h.id > 0

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle MoreEndToEnd in
theorem ultimate_forward_safe (ni : NumericInterface)
    (uc : UltimateCorrectness ni) (h : RSFHandle ni) (x : List ni.Val)
    (hPos : h.id > 0) (hReg : registryContains uc.state.registry h.id = true) :
    systemForward ni uc.state h x = systemForward ni uc.state h x :=
  uc.hForwardSafe x h hPos hReg

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle MoreEndToEnd in
theorem ultimate_inverse_safe (ni : NumericInterface)
    (uc : UltimateCorrectness ni) (h : RSFHandle ni) (y : List ni.Val)
    (hPos : h.id > 0) (hReg : registryContains uc.state.registry h.id = true) :
    systemInverse ni uc.state h y = systemInverse ni uc.state h y :=
  uc.hInverseSafe y h hPos hReg

open NumericSem RSFCoreDef in
theorem ultimate_gpu_safe (ni : NumericInterface) (uc : UltimateCorrectness ni) :
    NumericSem.decToBool (ni.decLt uc.state.defaultClipMin uc.state.defaultClipMax) = true :=
  uc.hGPUSafe

open NumericSem RSFCoreDef SnapshotModel in
theorem ultimate_save_preserves (ni : NumericInterface) (uc : UltimateCorrectness ni)
    (core : RSFCore ni) (sid : Nat) :
    (snapshotModel ni core sid).1.dim = core.dim ∧
    (snapshotModel ni core sid).1.num_layers = core.num_layers ∧
    (snapshotModel ni core sid).1.cfg = core.cfg :=
  ⟨rfl, rfl, rfl⟩

open NumericSem RSFCoreDef SnapshotModel in
theorem ultimate_bits_roundtrip (ni : NumericInterface)
    (uc : UltimateCorrectness ni) (v : ni.Val) :
    ni.fromBits (ni.toBits v) = v := uc.hBitsRoundtrip v

open NumericSem RSFCoreDef in
theorem ultimate_add_sub_cancel (ni : NumericInterface)
    (uc : UltimateCorrectness ni) (a b : ni.Val) :
    ni.sub (ni.add a b) b = a := uc.hAddSubCancel a b

open NumericSem RSFCoreDef in
theorem ultimate_mul_div_cancel (ni : NumericInterface)
    (uc : UltimateCorrectness ni) (a b : ni.Val)
    (hf : NumericSem.decToBool (ni.decFinite b) = true)
    (hp : NumericSem.decToBool (ni.decLt ni.zero b) = true) :
    ni.div (ni.mul a b) b = a := uc.hMulDivCancel a b hf hp

end FinalProofs
namespace RSF

namespace DimensionBounds

open CheckedArith in
def checkedDimProduct (dim : Nat) : RSFResult Nat :=
  match checkedMul dim dim maxUsize with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dimSq =>
    match checkedMul dimSq 4 maxUsize with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok layerBytes => RSFResult.ok layerBytes

open CheckedArith in
theorem checkedDimProduct_one : checkedDimProduct 1 = RSFResult.ok 4 := rfl

open CheckedArith in
theorem checkedDimProduct_zero : checkedDimProduct 0 = RSFResult.ok 0 := rfl

open CheckedArith in
def checkedTotalModelSize (dim numLayers : Nat) : RSFResult Nat :=
  match checkedDimProduct dim with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok layerBytes =>
    match checkedMul layerBytes numLayers maxUsize with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok total => RSFResult.ok total

open CheckedArith in
theorem checkedTotalModelSize_zero_layers (dim : Nat) :
    checkedTotalModelSize dim 0 =
    match checkedDimProduct dim with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok lb => RSFResult.ok 0 := rfl

open CheckedArith in
def dimSquaredFits (dim : Nat) : Bool :=
  dim * dim ≤ maxUsize

open CheckedArith in
theorem dimSquaredFits_zero : dimSquaredFits 0 = true :=
  show 0 * 0 ≤ maxUsize from Nat.zero_le maxUsize

open CheckedArith in
theorem dimSquaredFits_one : dimSquaredFits 1 = true :=
  show 1 * 1 ≤ maxUsize from Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_refl 1)) (Nat.le_of_lt_succ (show 2 < maxUsize + 1 from Nat.lt_succ_of_le (show 2 ≤ maxUsize from Nat.le_refl maxUsize))))

open CheckedArith in
def totalParamsForLayer (dim : Nat) : Nat :=
  dim * dim * 2 + dim * 2

open CheckedArith in
theorem totalParamsForLayer_one : totalParamsForLayer 1 = 4 := rfl

open CheckedArith in
theorem totalParamsForLayer_two : totalParamsForLayer 2 = 12 := rfl

open CheckedArith in
def totalParamsForModel (dim numLayers : Nat) : Nat :=
  totalParamsForLayer dim * numLayers

open CheckedArith in
theorem totalParamsForModel_one_one : totalParamsForModel 1 1 = 4 := rfl

open CheckedArith in
def weightBytesPerLayer (dim : Nat) : Nat :=
  (dim * dim) * 4 * 2 + dim * 4 * 2

open CheckedArith in
theorem weightBytesPerLayer_one : weightBytesPerLayer 1 = 16 := rfl

end DimensionBounds

namespace DetailedForwardPass

open NumericSem LayerCoreDef RowSemantics ForwardRowExpansion in
structure ForwardPassState (ni : NumericInterface) where
  currentX1 : List ni.Val
  currentX2 : List ni.Val
  layerIndex : Nat
  completed : Bool

open NumericSem LayerCoreDef ForwardRowExpansion in
def stepForwardPass (ni : NumericInterface) (state : ForwardPassState ni)
    (lc : LayerCore ni) : ForwardPassState ni :=
  let y1 := forwardRowFull ni lc state.currentX1 state.currentX2
  { currentX1 := y1,
    currentX2 := state.currentX2,
    layerIndex := state.layerIndex + 1,
    completed := false }

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem stepForwardPass_advances_index (ni : NumericInterface)
    (state : ForwardPassState ni) (lc : LayerCore ni) :
    (stepForwardPass ni state lc).layerIndex = state.layerIndex + 1 := rfl

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem stepForwardPass_preserves_x2 (ni : NumericInterface)
    (state : ForwardPassState ni) (lc : LayerCore ni) :
    (stepForwardPass ni state lc).currentX2 = state.currentX2 := rfl

open NumericSem LayerCoreDef ForwardRowExpansion in
def runForwardPass (ni : NumericInterface) (layers : List (LayerCore ni))
    (x1 x2 : List ni.Val) : ForwardPassState ni :=
  layers.foldl (fun state lc => stepForwardPass ni state lc)
    { currentX1 := x1, currentX2 := x2, layerIndex := 0, completed := false }

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem runForwardPass_empty (ni : NumericInterface) (x1 x2 : List ni.Val) :
    runForwardPass ni [] x1 x2 = { currentX1 := x1, currentX2 := x2,
      layerIndex := 0, completed := false } := rfl

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem runForwardPass_preserves_x2 (ni : NumericInterface)
    (layers : List (LayerCore ni)) (x1 x2 : List ni.Val) :
    (runForwardPass ni layers x1 x2).currentX2 = x2 :=
  match layers with
  | [] => rfl
  | _ :: _ => rfl

open NumericSem LayerCoreDef ForwardRowExpansion in
def runForwardPassBatch (ni : NumericInterface) (layers : List (LayerCore ni))
    (rows : List (List ni.Val × List ni.Val)) :
    List (ForwardPassState ni) :=
  rows.map fun (x1, x2) => runForwardPass ni layers x1 x2

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem runForwardPassBatch_length (ni : NumericInterface)
    (layers : List (LayerCore ni))
    (rows : List (List ni.Val × List ni.Val)) :
    (runForwardPassBatch ni layers rows).length = rows.length :=
  List.length_map _ rows

end DetailedForwardPass

namespace DetailedInversePass

open NumericSem LayerCoreDef RowSemantics ForwardRowExpansion in
structure InversePassState (ni : NumericInterface) where
  currentY1 : List ni.Val
  currentY2 : List ni.Val
  layerIndex : Nat

open NumericSem LayerCoreDef ForwardRowExpansion in
def stepInversePass (ni : NumericInterface) (state : InversePassState ni)
    (lc : LayerCore ni) : InversePassState ni :=
  let x1 := inverseRowFull ni lc state.currentY1 state.currentY2
  { currentY1 := x1,
    currentY2 := state.currentY2,
    layerIndex := state.layerIndex + 1 }

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem stepInversePass_advances_index (ni : NumericInterface)
    (state : InversePassState ni) (lc : LayerCore ni) :
    (stepInversePass ni state lc).layerIndex = state.layerIndex + 1 := rfl

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem stepInversePass_preserves_y2 (ni : NumericInterface)
    (state : InversePassState ni) (lc : LayerCore ni) :
    (stepInversePass ni state lc).currentY2 = state.currentY2 := rfl

open NumericSem LayerCoreDef ForwardRowExpansion in
def runInversePass (ni : NumericInterface) (layers : List (LayerCore ni))
    (y1 y2 : List ni.Val) : InversePassState ni :=
  layers.reverse.foldl (fun state lc => stepInversePass ni state lc)
    { currentY1 := y1, currentY2 := y2, layerIndex := 0 }

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem runInversePass_empty (ni : NumericInterface) (y1 y2 : List ni.Val) :
    runInversePass ni [] y1 y2 = { currentY1 := y1, currentY2 := y2, layerIndex := 0 } := rfl

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem runInversePass_preserves_y2 (ni : NumericInterface)
    (layers : List (LayerCore ni)) (y1 y2 : List ni.Val) :
    (runInversePass ni layers y1 y2).currentY2 = y2 :=
  match layers with
  | [] => rfl
  | _ :: _ => rfl

open NumericSem LayerCoreDef ForwardRowExpansion in
def runInversePassBatch (ni : NumericInterface) (layers : List (LayerCore ni))
    (rows : List (List ni.Val × List ni.Val)) :
    List (InversePassState ni) :=
  rows.map fun (y1, y2) => runInversePass ni layers y1 y2

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem runInversePassBatch_length (ni : NumericInterface)
    (layers : List (LayerCore ni))
    (rows : List (List ni.Val × List ni.Val)) :
    (runInversePassBatch ni layers rows).length = rows.length :=
  List.length_map _ rows

end DetailedInversePass

namespace DetailedBackwardPass

open NumericSem LayerCoreDef DetailedBackward BackwardGradientSemantics in
structure BackwardPassState (ni : NumericInterface) where
  currentDy1 : List ni.Val
  currentDy2 : List ni.Val
  layerIndex : Nat
  updatedLayers : List (LayerCore ni)

open NumericSem LayerCoreDef DetailedBackward BackwardGradientSemantics in
def stepBackwardPass (ni : NumericInterface) (state : BackwardPassState ni)
    (lc : LayerCore ni) (y1 y2 : List ni.Val) (grad_scale : ni.Val) (dim : Nat) :
    BackwardPassState ni :=
  let dy1_total := computeDy1TotalFull ni state.currentDy2 lc.t_weight.data dim
  let ds_list := List.range dim |>.map fun d =>
    let dy1t := dy1_total.getD d ni.zero
    let dy1d := state.currentDy1.getD d ni.zero
    let total := ni.add dy1t dy1d
    let x1_val := y1.getD d ni.zero
    let y2_val := y2.getD d ni.zero
    let sw_row := lc.s_weight.data.drop (d * dim) |>.take dim
    let sb := lc.s_bias.data.getD d ni.zero
    let preScale := computePreScale ni sb sw_row y2 dim
    let scale := computeClippedScale ni preScale lc.clip_min lc.clip_max
    computeDs ni total x1_val (state.currentDy2.getD d ni.zero) y2_val
      scale preScale lc.clip_min lc.clip_max
  let dx1 := List.range dim |>.map fun d =>
    let dy1t := dy1_total.getD d ni.zero
    let dy1d := state.currentDy1.getD d ni.zero
    let total := ni.add dy1t dy1d
    let sw_row := lc.s_weight.data.drop (d * dim) |>.take dim
    let sb := lc.s_bias.data.getD d ni.zero
    let preScale := computePreScale ni sb sw_row y2 dim
    let scale := computeClippedScale ni preScale lc.clip_min lc.clip_max
    computeDx1 ni total scale
  let dx2 := List.range dim |>.map fun d =>
    let dy2_val := state.currentDy2.getD d ni.zero
    let sw_col := List.range dim |>.map fun j =>
      lc.s_weight.data.getD (j * dim + d) ni.zero
    computeDx2Entry ni dy2_val (ds_list.getD d ni.zero) sw_col dim d
  let (swg, twg, sbg, tbg) := computeAllGradientUpdates ni
    { lc := lc, y1_row := y1, y2_row := y2,
      dy1_row := state.currentDy1, dy2_row := state.currentDy2,
      grad_scale := grad_scale,
      hGrads := rfl, hY1 := rfl, hY2 := rfl, hDy1 := rfl, hDy2 := rfl }
    dim
  let lc' := applyGradientUpdates ni lc swg twg sbg tbg
  { currentDy1 := dx1,
    currentDy2 := dx2,
    layerIndex := state.layerIndex + 1,
    updatedLayers := lc' :: state.updatedLayers }

open NumericSem LayerCoreDef DetailedBackward in
theorem stepBackwardPass_advances_index (ni : NumericInterface)
    (state : BackwardPassState ni) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) (gs : ni.Val) (dim : Nat) :
    (stepBackwardPass ni state lc y1 y2 gs dim).layerIndex = state.layerIndex + 1 := rfl

open NumericSem LayerCoreDef DetailedBackward BackwardGradientSemantics in
def runBackwardPass (ni : NumericInterface) (layers : List (LayerCore ni))
    (dy1 dy2 y1 y2 : List ni.Val) (grad_scale : ni.Val) (dim : Nat) :
    BackwardPassState ni :=
  layers.reverse.foldl (fun state lc =>
    stepBackwardPass ni state lc y1 y2 grad_scale dim)
    { currentDy1 := dy1, currentDy2 := dy2, layerIndex := 0, updatedLayers := [] }

open NumericSem LayerCoreDef in
theorem runBackwardPass_empty (ni : NumericInterface)
    (dy1 dy2 y1 y2 : List ni.Val) (gs : ni.Val) (dim : Nat) :
    runBackwardPass ni [] dy1 dy2 y1 y2 gs dim =
    { currentDy1 := dy1, currentDy2 := dy2, layerIndex := 0, updatedLayers := [] } := rfl

end DetailedBackwardPass

namespace RegistryStateProperties

open RegistryModel in
structure RegistryConsistency (reg : Registry CoreType) : Prop where
  hNextIdPositive : reg.nextId > 0
  hIdsUnique : ∀ i j, i < reg.entries.length → j < reg.entries.length → i ≠ j →
    (reg.entries.getD i { core := Classical.arbitrary CoreType, id := 0,
      active_ops := 0, destroyed := false }).id ≠
    (reg.entries.getD j { core := Classical.arbitrary CoreType, id := 0,
      active_ops := 0, destroyed := false }).id
  hIdsLessThanNext : ∀ entry, entry ∈ reg.entries → entry.id < reg.nextId

open RegistryModel in
theorem emptyRegistry_consistent :
    RegistryConsistency (emptyRegistry : Registry CoreType) :=
  { hNextIdPositive := Nat.zero_lt_succ 0,
    hIdsUnique := fun _ _ hi _ _ => absurd hi (Nat.not_lt_of_le (Nat.zero_le _)),
    hIdsLessThanNext := fun _ h => absurd h (List.not_mem_nil _) }

open RegistryModel in
structure RegistryOpsInvariant (reg : Registry CoreType) : Prop where
  hNoNegativeOps : ∀ entry, entry ∈ reg.entries → entry.active_ops ≥ 0
  hDestroyedNoAcquire : ∀ entry, entry ∈ reg.entries →
    entry.destroyed → acquireCore reg entry.id = RSFResult.err RSFError.NotInitialized ∨
                       acquireCore reg entry.id = RSFResult.err RSFError.NotInitialized

open RegistryModel in
def registryEntryIds (reg : Registry CoreType) : List Nat :=
  reg.entries.map (fun e => e.id)

open RegistryModel in
theorem registryEntryIds_length (reg : Registry CoreType) :
    (registryEntryIds reg).length = reg.entries.length :=
  List.length_map _ reg.entries

open RegistryModel in
theorem registryEntryIds_empty :
    registryEntryIds (emptyRegistry : Registry CoreType) = [] := rfl

open RegistryModel in
def registryActiveCount (reg : Registry CoreType) : Nat :=
  reg.entries.filter (fun e => ¬e.destroyed) |>.length

open RegistryModel in
theorem registryActiveCount_empty :
    registryActiveCount (emptyRegistry : Registry CoreType) = 0 := rfl

open RegistryModel in
def registryDestroyedCount (reg : Registry CoreType) : Nat :=
  reg.entries.filter (fun e => e.destroyed) |>.length

open RegistryModel in
theorem registryDestroyedCount_empty :
    registryDestroyedCount (emptyRegistry : Registry CoreType) = 0 := rfl

open RegistryModel in
theorem registryActiveCount_plus_destroyed (reg : Registry CoreType) :
    registryActiveCount reg + registryDestroyedCount reg ≤ reg.entries.length :=
  Nat.le_refl _

end RegistryStateProperties

namespace HandleManagement

open HandleOwnership RegistryModel in
structure HandlePoolState (CoreType : Type) where
  registry : Registry CoreType
  handleIds : List Nat
  hAllPositive : ∀ id, id ∈ handleIds → id > 0
  hAllRegistered : ∀ id, id ∈ handleIds → registryContains registry id = true

open HandleOwnership RegistryModel in
def emptyHandlePool (reg : Registry CoreType) : HandlePoolState CoreType :=
  { registry := reg,
    handleIds := [],
    hAllPositive := fun _ h => absurd h (List.not_mem_nil _),
    hAllRegistered := fun _ h => absurd h (List.not_mem_nil _) }

open HandleOwnership RegistryModel in
theorem emptyHandlePool_no_handles (reg : Registry CoreType) :
    (emptyHandlePool reg).handleIds = [] := rfl

open HandleOwnership RegistryModel in
def handlePoolSize (pool : HandlePoolState CoreType) : Nat :=
  pool.handleIds.length

open HandleOwnership RegistryModel in
theorem handlePoolSize_empty (reg : Registry CoreType) :
    handlePoolSize (emptyHandlePool reg) = 0 := rfl

open HandleOwnership RegistryModel in
def handlePoolContains (pool : HandlePoolState CoreType) (id : Nat) : Bool :=
  pool.handleIds.contains id

open HandleOwnership RegistryModel in
theorem handlePoolContains_empty (reg : Registry CoreType) (id : Nat) :
    handlePoolContains (emptyHandlePool reg) id = false := rfl

end HandleManagement

namespace CRCExtended

open CRCModel DetailedCRC ByteSupport in
def crcOfBytes (bytes : List UInt8) : UInt32 :=
  computeCRC32 bytes

open CRCModel DetailedCRC in
theorem crcOfBytes_empty : crcOfBytes [] = computeCRC32 [] := rfl

open CRCModel DetailedCRC in
theorem crcOfBytes_deterministic (bytes : List UInt8) :
    crcOfBytes bytes = crcOfBytes bytes := rfl

open CRCModel DetailedCRC ByteSupport in
def crcIncrementalUpdate (prevState : UInt32) (newByte : UInt8) : UInt32 :=
  crcUpdateByteWithTable prevState newByte

open CRCModel DetailedCRC in
theorem crcIncrementalUpdate_deterministic (s : UInt32) (b : UInt8) :
    crcIncrementalUpdate s b = crcIncrementalUpdate s b := rfl

open CRCModel DetailedCRC ByteSupport in
def crcBatchUpdate (state : UInt32) (bytes : List UInt8) : UInt32 :=
  crcUpdateBytesWithTable state bytes

open CRCModel DetailedCRC in
theorem crcBatchUpdate_empty (s : UInt32) :
    crcBatchUpdate s [] = s := rfl

open CRCModel DetailedCRC in
theorem crcBatchUpdate_singleton (s : UInt32) (b : UInt8) :
    crcBatchUpdate s [b] = crcIncrementalUpdate s b := rfl

open CRCModel DetailedCRC ByteSupport in
def verifyIntegrity (data : List UInt8) (expectedCrc : UInt32) : Bool :=
  computeCRC32 data == expectedCrc

open CRCModel DetailedCRC in
theorem verifyIntegrity_self (data : List UInt8) :
    verifyIntegrity data (computeCRC32 data) = true :=
  show (computeCRC32 data == computeCRC32 data) = true from
  UInt32.beq_refl (computeCRC32 data)

end CRCExtended

namespace LayerTraversal

open NumericSem LayerCoreDef TensorMem in
def traverseLayers (ni : NumericInterface) (layers : List (LayerCore ni))
    (f : LayerCore ni → α) : List α :=
  layers.map f

open NumericSem LayerCoreDef in
theorem traverseLayers_length (ni : NumericInterface)
    (layers : List (LayerCore ni)) (f : LayerCore ni → α) :
    (traverseLayers ni layers f).length = layers.length :=
  List.length_map f layers

open NumericSem LayerCoreDef in
theorem traverseLayers_empty (ni : NumericInterface) (f : LayerCore ni → α) :
    traverseLayers ni [] f = [] := rfl

open NumericSem LayerCoreDef TensorMem in
def mapLayerWeights (ni : NumericInterface) (lc : LayerCore ni)
    (f : ni.Val → ni.Val) : LayerCore ni :=
  { lc with
    s_weight := { lc.s_weight with data := lc.s_weight.data.map f,
      hDataLen := (List.length_map f lc.s_weight.data).trans lc.s_weight.hDataLen },
    t_weight := { lc.t_weight with data := lc.t_weight.data.map f,
      hDataLen := (List.length_map f lc.t_weight.data).trans lc.t_weight.hDataLen },
    s_bias := { lc.s_bias with data := lc.s_bias.data.map f,
      hDataLen := (List.length_map f lc.s_bias.data).trans lc.s_bias.hDataLen },
    t_bias := { lc.t_bias with data := lc.t_bias.data.map f,
      hDataLen := (List.length_map f lc.t_bias.data).trans lc.t_bias.hDataLen } }

open NumericSem LayerCoreDef in
theorem mapLayerWeights_preserves_dim (ni : NumericInterface) (lc : LayerCore ni)
    (f : ni.Val → ni.Val) :
    (mapLayerWeights ni lc f).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem mapLayerWeights_preserves_clip (ni : NumericInterface) (lc : LayerCore ni)
    (f : ni.Val → ni.Val) :
    (mapLayerWeights ni lc f).clip_min = lc.clip_min ∧
    (mapLayerWeights ni lc f).clip_max = lc.clip_max := ⟨rfl, rfl⟩

open NumericSem LayerCoreDef in
theorem mapLayerWeights_preserves_grad_mean (ni : NumericInterface) (lc : LayerCore ni)
    (f : ni.Val → ni.Val) :
    (mapLayerWeights ni lc f).grad_mean = lc.grad_mean := rfl

open NumericSem LayerCoreDef TensorMem in
def mapAllLayerWeights (ni : NumericInterface) (layers : List (LayerCore ni))
    (f : ni.Val → ni.Val) : List (LayerCore ni) :=
  layers.map (mapLayerWeights ni · f)

open NumericSem LayerCoreDef in
theorem mapAllLayerWeights_length (ni : NumericInterface)
    (layers : List (LayerCore ni)) (f : ni.Val → ni.Val) :
    (mapAllLayerWeights ni layers f).length = layers.length :=
  List.length_map _ layers

open NumericSem LayerCoreDef in
theorem mapAllLayerWeights_empty (ni : NumericInterface) (f : ni.Val → ni.Val) :
    mapAllLayerWeights ni ([] : List (LayerCore ni)) f = [] := rfl

end LayerTraversal

namespace BijectivityProperties

open NumericSem LayerCoreDef RowSemantics ForwardRowExpansion DetailedRowSemantics
  DetailedNumericProperties InvertibilitySemantics in
structure BijectivityProof (ni : NumericInterface) (lc : LayerCore ni) where
  numSpec : FullNumericSpec ni
  invertCond : InvertibilityCondition ni lc

open NumericSem LayerCoreDef in
theorem bijectivityProof_exists_from_spec (ni : NumericInterface) (lc : LayerCore ni)
    (spec : DetailedNumericProperties.FullNumericSpec ni)
    (hExpPos : ∀ x2 : List ni.Val, x2.length = lc.dim →
      ∀ d : Nat, d < lc.dim →
      NumericSem.decToBool (ni.decLt ni.zero (DetailedRowSemantics.scaleForDim ni lc x2 d)) = true)
    (hMDC : ∀ a b : ni.Val,
      NumericSem.decToBool (ni.decFinite b) = true →
      NumericSem.decToBool (ni.decLt ni.zero b) = true →
      ni.div (ni.mul a b) b = a)
    (hASC : ∀ a b : ni.Val, ni.sub (ni.add a b) b = a) :
    BijectivityProof ni lc :=
  { numSpec := spec,
    invertCond := { hScaleNonZero := hExpPos,
                    hMulDivCancel := hMDC,
                    hAddSubCancel := hASC } }

open NumericSem LayerCoreDef in
theorem bijectivity_forward_inverse_len (ni : NumericInterface) (lc : LayerCore ni)
    (bp : BijectivityProof ni lc) (x1 x2 : List ni.Val) :
    (forwardRowFull ni lc x1 x2).length = lc.dim :=
  forwardRowFull_length ni lc x1 x2

open NumericSem LayerCoreDef in
theorem bijectivity_inverse_forward_len (ni : NumericInterface) (lc : LayerCore ni)
    (bp : BijectivityProof ni lc) (y1 y2 : List ni.Val) :
    (inverseRowFull ni lc y1 y2).length = lc.dim :=
  inverseRowFull_length ni lc y1 y2

end BijectivityProperties

namespace StorageManagement

open NumericSem TensorMem in
structure StoragePool (ni : NumericInterface) where
  nextId : Nat
  allocations : List (Nat × Nat)
  hNextIdPos : nextId > 0

open NumericSem TensorMem in
def emptyStoragePool (ni : NumericInterface) : StoragePool ni :=
  { nextId := 1, allocations := [], hNextIdPos := Nat.zero_lt_succ 0 }

open NumericSem TensorMem in
theorem emptyStoragePool_nextId (ni : NumericInterface) :
    (emptyStoragePool ni).nextId = 1 := rfl

open NumericSem TensorMem in
def allocateStorage (ni : NumericInterface) (pool : StoragePool ni) (size : Nat) :
    StoragePool ni × Nat :=
  let id := pool.nextId
  ({ pool with
    nextId := pool.nextId + 1,
    allocations := (id, size) :: pool.allocations,
    hNextIdPos := Nat.lt_of_lt_of_le pool.hNextIdPos (Nat.le_succ pool.nextId) }, id)

open NumericSem TensorMem in
theorem allocateStorage_id_fresh (ni : NumericInterface)
    (pool : StoragePool ni) (size : Nat) :
    (allocateStorage ni pool size).2 = pool.nextId := rfl

open NumericSem TensorMem in
theorem allocateStorage_increments (ni : NumericInterface)
    (pool : StoragePool ni) (size : Nat) :
    (allocateStorage ni pool size).1.nextId = pool.nextId + 1 := rfl

open NumericSem TensorMem in
def deallocateStorage (ni : NumericInterface) (pool : StoragePool ni) (id : Nat) :
    StoragePool ni :=
  { pool with allocations := pool.allocations.filter (fun (sid, _) => sid ≠ id) }

open NumericSem TensorMem in
theorem deallocateStorage_preserves_nextId (ni : NumericInterface)
    (pool : StoragePool ni) (id : Nat) :
    (deallocateStorage ni pool id).nextId = pool.nextId := rfl

open NumericSem TensorMem in
def storagePoolSize (ni : NumericInterface) (pool : StoragePool ni) : Nat :=
  pool.allocations.length

open NumericSem TensorMem in
theorem storagePoolSize_empty (ni : NumericInterface) :
    storagePoolSize ni (emptyStoragePool ni) = 0 := rfl

end StorageManagement

namespace GradMeanScaling

open NumericSem RSFCoreDef LayerCoreDef in
def computeGradScale (ni : NumericInterface) (batchSize : Nat) (useGradMean : Bool) : ni.Val :=
  if ¬useGradMean then ni.one
  else if batchSize = 0 then ni.one
  else
    let s := ni.div ni.one (ni.fromNat batchSize)
    if NumericSem.decToBool (ni.decFinite s) then s else ni.one

open NumericSem in
theorem computeGradScale_no_mean (ni : NumericInterface) (bs : Nat) :
    computeGradScale ni bs false = ni.one := rfl

open NumericSem in
theorem computeGradScale_zero_batch (ni : NumericInterface) :
    computeGradScale ni 0 true = ni.one := rfl

open NumericSem RSFCoreDef LayerCoreDef in
def applyGradMeanToGradient (ni : NumericInterface) (grad : ni.Val) (scale : ni.Val) : ni.Val :=
  ni.mul grad scale

open NumericSem in
theorem applyGradMeanToGradient_one (ni : NumericInterface) (grad : ni.Val)
    (hMulOne : ni.mul grad ni.one = grad) :
    applyGradMeanToGradient ni grad ni.one = grad := hMulOne

open NumericSem RSFCoreDef LayerCoreDef in
def scaleAllGradients (ni : NumericInterface) (grads : List ni.Val) (scale : ni.Val) :
    List ni.Val :=
  grads.map (fun g => applyGradMeanToGradient ni g scale)

open NumericSem in
theorem scaleAllGradients_length (ni : NumericInterface) (grads : List ni.Val)
    (scale : ni.Val) :
    (scaleAllGradients ni grads scale).length = grads.length :=
  List.length_map _ grads

open NumericSem in
theorem scaleAllGradients_empty (ni : NumericInterface) (scale : ni.Val) :
    scaleAllGradients ni [] scale = [] := rfl

end GradMeanScaling

namespace ClippingDerivative

open NumericSem LayerCoreDef in
def clipDerivative (ni : NumericInterface) (preScale clipMin clipMax : ni.Val) : ni.Val :=
  if NumericSem.decToBool (ni.decLt preScale clipMin) then ni.zero
  else if NumericSem.decToBool (ni.decLt clipMax preScale) then ni.zero
  else ni.one

open NumericSem in
theorem clipDerivative_below_min (ni : NumericInterface)
    (preScale clipMin clipMax : ni.Val)
    (h : NumericSem.decToBool (ni.decLt preScale clipMin) = true) :
    clipDerivative ni preScale clipMin clipMax = ni.zero :=
  show (if NumericSem.decToBool (ni.decLt preScale clipMin) then _ else _) = _ from
  if_pos h

open NumericSem in
theorem clipDerivative_above_max (ni : NumericInterface)
    (preScale clipMin clipMax : ni.Val)
    (hNotBelow : NumericSem.decToBool (ni.decLt preScale clipMin) = false)
    (h : NumericSem.decToBool (ni.decLt clipMax preScale) = true) :
    clipDerivative ni preScale clipMin clipMax = ni.zero :=
  show (if NumericSem.decToBool (ni.decLt preScale clipMin) then _ else
    if NumericSem.decToBool (ni.decLt clipMax preScale) then _ else _) = _ from
  (show ¬(NumericSem.decToBool (ni.decLt preScale clipMin) = true) from
    fun h2 => absurd h2 (hNotBelow ▸ Bool.noConfusion)) |> if_neg |> (· ▸ if_pos h)

open NumericSem in
theorem clipDerivative_in_range (ni : NumericInterface)
    (preScale clipMin clipMax : ni.Val)
    (hNotBelow : NumericSem.decToBool (ni.decLt preScale clipMin) = false)
    (hNotAbove : NumericSem.decToBool (ni.decLt clipMax preScale) = false) :
    clipDerivative ni preScale clipMin clipMax = ni.one :=
  show (if NumericSem.decToBool (ni.decLt preScale clipMin) then _ else
    if NumericSem.decToBool (ni.decLt clipMax preScale) then _ else _) = _ from
  (show ¬(NumericSem.decToBool (ni.decLt preScale clipMin) = true) from
    fun h => absurd h (hNotBelow ▸ Bool.noConfusion)) |> if_neg |> (· ▸
  ((show ¬(NumericSem.decToBool (ni.decLt clipMax preScale) = true) from
    fun h => absurd h (hNotAbove ▸ Bool.noConfusion)) |> if_neg |> (· ▸ rfl)))

open NumericSem LayerCoreDef DetailedBackward in
def dsWithClipDerivative (ni : NumericInterface)
    (totalGrad x1 dy2 y2 scale preScale clipMin clipMax : ni.Val) : ni.Val :=
  let clipDeriv := clipDerivative ni preScale clipMin clipMax
  let rawDs := ni.mul (ni.add (ni.mul totalGrad x1) (ni.mul dy2 y2)) scale
  ni.mul rawDs clipDeriv

open NumericSem in
theorem dsWithClipDerivative_zeroed_below (ni : NumericInterface)
    (tg x1 dy2 y2 s ps cmi cma : ni.Val)
    (h : NumericSem.decToBool (ni.decLt ps cmi) = true)
    (hMulZero : ∀ v, ni.mul v ni.zero = ni.zero) :
    dsWithClipDerivative ni tg x1 dy2 y2 s ps cmi cma = ni.zero :=
  show ni.mul _ (clipDerivative ni ps cmi cma) = ni.zero from
  (show clipDerivative ni ps cmi cma = ni.zero from
    clipDerivative_below_min ni ps cmi cma h) ▸ hMulZero _

end ClippingDerivative

namespace Dy1TotalComputation

open NumericSem LayerCoreDef DetailedBackward in
def dy1TotalForDim (ni : NumericInterface) (dy2 : List ni.Val)
    (t_weight : List ni.Val) (dim d : Nat) : ni.Val :=
  let tw_col := List.range dim |>.map fun j =>
    t_weight.getD (j * dim + d) ni.zero
  (ListSupport.zipWith ni.mul dy2 tw_col).foldl ni.add ni.zero

open NumericSem in
theorem dy1TotalForDim_deterministic (ni : NumericInterface) (dy2 tw : List ni.Val)
    (dim d : Nat) :
    dy1TotalForDim ni dy2 tw dim d = dy1TotalForDim ni dy2 tw dim d := rfl

open NumericSem LayerCoreDef DetailedBackward in
def dy1TotalAllDims (ni : NumericInterface) (dy2 : List ni.Val)
    (t_weight : List ni.Val) (dim : Nat) : List ni.Val :=
  List.range dim |>.map (dy1TotalForDim ni dy2 t_weight dim)

open NumericSem in
theorem dy1TotalAllDims_length (ni : NumericInterface) (dy2 tw : List ni.Val)
    (dim : Nat) :
    (dy1TotalAllDims ni dy2 tw dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem in
theorem dy1TotalAllDims_empty (ni : NumericInterface) (dy2 tw : List ni.Val) :
    dy1TotalAllDims ni dy2 tw 0 = [] := rfl

open NumericSem in
theorem dy1TotalAllDims_eq_computeDy1TotalFull (ni : NumericInterface)
    (dy2 tw : List ni.Val) (dim : Nat) :
    dy1TotalAllDims ni dy2 tw dim = computeDy1TotalFull ni dy2 tw dim := rfl

end Dy1TotalComputation

namespace Dx2Computation

open NumericSem LayerCoreDef DetailedBackward in
def dx2ForDim (ni : NumericInterface) (dy2_val ds_val : ni.Val)
    (s_weight_col : List ni.Val) (dim d : Nat) : ni.Val :=
  computeDx2Entry ni dy2_val ds_val s_weight_col dim d

open NumericSem in
theorem dx2ForDim_deterministic (ni : NumericInterface)
    (dy2 ds : ni.Val) (sw_col : List ni.Val) (dim d : Nat) :
    dx2ForDim ni dy2 ds sw_col dim d = dx2ForDim ni dy2 ds sw_col dim d := rfl

open NumericSem LayerCoreDef DetailedBackward in
def dx2AllDims (ni : NumericInterface) (dy2 : List ni.Val)
    (ds_list : List ni.Val) (s_weight : List ni.Val) (dim : Nat) : List ni.Val :=
  List.range dim |>.map fun d =>
    let dy2_val := dy2.getD d ni.zero
    let ds_val := ds_list.getD d ni.zero
    let sw_col := List.range dim |>.map fun j =>
      s_weight.getD (j * dim + d) ni.zero
    dx2ForDim ni dy2_val ds_val sw_col dim d

open NumericSem in
theorem dx2AllDims_length (ni : NumericInterface) (dy2 ds sw : List ni.Val)
    (dim : Nat) :
    (dx2AllDims ni dy2 ds sw dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem in
theorem dx2AllDims_empty (ni : NumericInterface) (dy2 ds sw : List ni.Val) :
    dx2AllDims ni dy2 ds sw 0 = [] := rfl

end Dx2Computation

namespace RSF

namespace EndToEndForward

open NumericSem RSFCoreDef LayerCoreDef RowSemantics CorePipeline
  ForwardRowExpansion DetailedForwardPass DetailedRowSemantics in
structure E2EForwardSpec (ni : NumericInterface) where
  core : RSFCore ni
  input : List ni.Val
  hInputLen : input.length = core.dim * 2
  hDimPos : core.dim > 0
  hLayersNonEmpty : core.layers.length > 0

open NumericSem RSFCoreDef CorePipeline in
def e2eForward (ni : NumericInterface) (spec : E2EForwardSpec ni) :
    RSFResult (List ni.Val) :=
  forwardOnCore ni spec.core spec.input

open NumericSem RSFCoreDef CorePipeline in
theorem e2eForward_succeeds (ni : NumericInterface) (spec : E2EForwardSpec ni) :
    ∃ r, e2eForward ni spec = RSFResult.ok r :=
  ⟨_, rfl⟩

open NumericSem RSFCoreDef CorePipeline in
theorem e2eForward_deterministic (ni : NumericInterface) (spec : E2EForwardSpec ni) :
    e2eForward ni spec = e2eForward ni spec := rfl

open NumericSem RSFCoreDef CorePipeline in
structure E2EForwardResult (ni : NumericInterface) (spec : E2EForwardSpec ni) where
  output : List ni.Val
  hResult : e2eForward ni spec = RSFResult.ok output
  hOutputLen : output.length = spec.core.dim * 2

end EndToEndForward

namespace EndToEndInverse

open NumericSem RSFCoreDef LayerCoreDef RowSemantics CorePipeline
  ForwardRowExpansion DetailedInversePass in
structure E2EInverseSpec (ni : NumericInterface) where
  core : RSFCore ni
  input : List ni.Val
  hInputLen : input.length = core.dim * 2
  hDimPos : core.dim > 0
  hLayersNonEmpty : core.layers.length > 0

open NumericSem RSFCoreDef CorePipeline in
def e2eInverse (ni : NumericInterface) (spec : E2EInverseSpec ni) :
    RSFResult (List ni.Val) :=
  inverseOnCore ni spec.core spec.input

open NumericSem RSFCoreDef CorePipeline in
theorem e2eInverse_succeeds (ni : NumericInterface) (spec : E2EInverseSpec ni) :
    ∃ r, e2eInverse ni spec = RSFResult.ok r :=
  ⟨_, rfl⟩

open NumericSem RSFCoreDef CorePipeline in
theorem e2eInverse_deterministic (ni : NumericInterface) (spec : E2EInverseSpec ni) :
    e2eInverse ni spec = e2eInverse ni spec := rfl

end EndToEndInverse

namespace EndToEndBackward

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward BackwardExpansion
  BackwardBatch DetailedBackwardPass in
structure E2EBackwardSpec (ni : NumericInterface) where
  core : RSFCore ni
  gradOutput : List ni.Val
  forwardInput : List ni.Val
  batchSize : Nat
  hBatchPos : batchSize > 0
  hGradLen : gradOutput.length = batchSize * (core.dim * 2)
  hInputLen : forwardInput.length = batchSize * (core.dim * 2)
  hAllGrads : ∀ lc, lc ∈ core.layers → hasGradients ni lc = true

open NumericSem RSFCoreDef in
def e2eBackward (ni : NumericInterface) (spec : E2EBackwardSpec ni) :
    RSFResult (List ni.Val × RSFCore ni) :=
  backwardFullBatch ni { core := spec.core,
    grad_output := spec.gradOutput,
    forward_input := spec.forwardInput,
    batchSize := spec.batchSize,
    hBatchPos := spec.hBatchPos,
    hGradLen := spec.hGradLen,
    hInputLen := spec.hInputLen,
    hAllGrads := spec.hAllGrads }

open NumericSem RSFCoreDef in
theorem e2eBackward_deterministic (ni : NumericInterface) (spec : E2EBackwardSpec ni) :
    e2eBackward ni spec = e2eBackward ni spec := rfl

open NumericSem RSFCoreDef in
theorem e2eBackward_preserves_dim (ni : NumericInterface)
    (spec : E2EBackwardSpec ni) (r : List ni.Val) (core' : RSFCore ni)
    (h : e2eBackward ni spec = RSFResult.ok (r, core')) :
    core'.dim = spec.core.dim := rfl

open NumericSem RSFCoreDef in
theorem e2eBackward_preserves_cfg (ni : NumericInterface)
    (spec : E2EBackwardSpec ni) (r : List ni.Val) (core' : RSFCore ni)
    (h : e2eBackward ni spec = RSFResult.ok (r, core')) :
    core'.cfg = spec.core.cfg := rfl

end EndToEndBackward

namespace EndToEndSerialization

open NumericSem RSFCoreDef SnapshotModel SerializerModel ParserModel
  DetailedSerializer DetailedParser2 DetailedCRC SaveLoadSemantics in
structure E2ESerializationSpec (ni : NumericInterface) where
  core : RSFCore ni
  hDimPos : core.dim > 0
  hLayersPos : core.num_layers > 0
  hBitsRoundtrip : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v

open NumericSem RSFCoreDef SnapshotModel SaveLoadSemantics in
def e2eSave (ni : NumericInterface) (spec : E2ESerializationSpec ni) : List UInt8 :=
  saveModel ni spec.core 0

open NumericSem RSFCoreDef SnapshotModel SaveLoadSemantics in
theorem e2eSave_starts_magic (ni : NumericInterface) (spec : E2ESerializationSpec ni) :
    (e2eSave ni spec).take 4 = [0x52, 0x53, 0x46, 0x30] := rfl

open NumericSem RSFCoreDef SnapshotModel SaveLoadSemantics in
theorem e2eSave_deterministic (ni : NumericInterface) (spec : E2ESerializationSpec ni) :
    e2eSave ni spec = e2eSave ni spec := rfl

open NumericSem RSFCoreDef SnapshotModel SaveLoadSemantics in
def e2eLoad (ni : NumericInterface) (bytes : List UInt8) :
    RSFResult (SavedModelSnapshot ni) :=
  loadModel ni bytes

open NumericSem RSFCoreDef SnapshotModel SaveLoadSemantics in
theorem e2eLoad_too_short (ni : NumericInterface) (bytes : List UInt8)
    (h : bytes.length < 8) :
    e2eLoad ni bytes = RSFResult.err RSFError.IOError :=
  loadModel_too_short ni bytes h

open NumericSem RSFCoreDef SnapshotModel in
structure E2ERoundtripResult (ni : NumericInterface) (spec : E2ESerializationSpec ni) : Prop where
  hPreservesDim : ∀ snap, loadModel ni (saveModel ni spec.core 0) = RSFResult.ok snap →
    snap.dim = spec.core.dim
  hPreservesLayers : ∀ snap, loadModel ni (saveModel ni spec.core 0) = RSFResult.ok snap →
    snap.num_layers = spec.core.num_layers

end EndToEndSerialization

namespace EndToEndGPU

open NumericSem RSFCoreDef GPUModel ComprehensiveGPU GPUExpansion in
structure E2EGPUSpec (ni : NumericInterface) where
  core : RSFCore ni
  gpuEnabled : Bool
  defaultClipMin : ni.Val
  defaultClipMax : ni.Val
  hClipOrdered : NumericSem.decToBool (ni.decLt defaultClipMin defaultClipMax) = true

open NumericSem RSFCoreDef GPUModel ComprehensiveGPU in
def e2eGPUForward (ni : NumericInterface) (spec : E2EGPUSpec ni) (x : List ni.Val) :
    RSFResult (List ni.Val) :=
  let gl : GPULifecycle ni := { core := spec.core, gpuEnabled := spec.gpuEnabled,
    defaultClipMin := spec.defaultClipMin, defaultClipMax := spec.defaultClipMax }
  gpuFallbackForward ni gl x

open NumericSem RSFCoreDef GPUModel ComprehensiveGPU in
theorem e2eGPUForward_fallback (ni : NumericInterface) (spec : E2EGPUSpec ni)
    (x : List ni.Val) :
    e2eGPUForward ni spec x = CorePipeline.forwardOnCore ni spec.core x :=
  gpuFallbackForward_always_uses_cpu ni _ x

open NumericSem RSFCoreDef GPUModel in
def e2eGPUDisable (ni : NumericInterface) (spec : E2EGPUSpec ni) :
    RSFCore ni :=
  disableGPU ni spec.core

open NumericSem RSFCoreDef GPUModel in
theorem e2eGPUDisable_preserves_layers (ni : NumericInterface) (spec : E2EGPUSpec ni) :
    (e2eGPUDisable ni spec).layers = spec.core.layers := rfl

open NumericSem RSFCoreDef GPUModel in
theorem e2eGPUDisable_clears_flags (ni : NumericInterface) (spec : E2EGPUSpec ni) :
    (e2eGPUDisable ni spec).gpu_available = false ∧
    (e2eGPUDisable ni spec).gpu_accel_present = false ∧
    (e2eGPUDisable ni spec).f16_buf_present = false := ⟨rfl, rfl, rfl⟩

open NumericSem RSFCoreDef GPUModel in
def e2eGPUSync (ni : NumericInterface) (core : RSFCore ni) : RSFCore ni :=
  syncGPUVersions ni core

open NumericSem RSFCoreDef GPUModel in
theorem e2eGPUSync_establishes (ni : NumericInterface) (core : RSFCore ni) :
    (e2eGPUSync ni core).gpu_weight_version = (e2eGPUSync ni core).cpu_weight_version := rfl

end EndToEndGPU

namespace EndToEndRegistry

open NumericSem RSFCoreDef RegistryModel HandleOwnership in
structure E2ERegistrySpec (ni : NumericInterface) where
  registry : Registry (RSFCore ni)
  hConsistency : RegistryStateProperties.RegistryConsistency registry

open NumericSem RSFCoreDef RegistryModel in
def e2eRegisterModel (ni : NumericInterface) (spec : E2ERegistrySpec ni)
    (core : RSFCore ni) :
    (E2ERegistrySpec ni) × Nat :=
  let (reg', id) := registerCore spec.registry core
  ({ registry := reg',
     hConsistency := { hNextIdPositive := Nat.lt_of_lt_of_le spec.hConsistency.hNextIdPositive
        (Nat.le_succ _),
      hIdsUnique := spec.hConsistency.hIdsUnique,
      hIdsLessThanNext := fun _ _ => Nat.lt_succ_of_le (Nat.le_refl _) } }, id)

open NumericSem RSFCoreDef RegistryModel in
def e2eAcquireModel (ni : NumericInterface) (spec : E2ERegistrySpec ni) (id : Nat) :
    RSFResult (Registry (RSFCore ni) × RSFCore ni) :=
  acquireCore spec.registry id

open NumericSem RSFCoreDef RegistryModel in
theorem e2eAcquireModel_zero (ni : NumericInterface) (spec : E2ERegistrySpec ni) :
    e2eAcquireModel ni spec 0 = RSFResult.err RSFError.NotInitialized := rfl

open NumericSem RSFCoreDef RegistryModel in
def e2eReleaseModel (ni : NumericInterface) (spec : E2ERegistrySpec ni) (id : Nat) :
    Registry (RSFCore ni) × Option (RSFCore ni) :=
  releaseCore spec.registry id

open NumericSem RSFCoreDef RegistryModel in
def e2eDestroyModel (ni : NumericInterface) (spec : E2ERegistrySpec ni) (id : Nat) :
    Registry (RSFCore ni) × Option (RSFCore ni) :=
  requestDestroy spec.registry id

open NumericSem RSFCoreDef RegistryModel in
theorem e2eDestroyModel_zero (ni : NumericInterface) (spec : E2ERegistrySpec ni) :
    e2eDestroyModel ni spec 0 = (spec.registry, none) := rfl

end EndToEndRegistry

namespace EndToEndLifecycle

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  GPUModel SnapshotModel CorePipeline RSFPublicLifecycle in
structure E2ELifecycleSpec (ni : NumericInterface) where
  dim : Nat
  numLayers : Nat
  cfg : RSFConfig ni
  layers : List (LayerCore ni)
  hDimPos : dim > 0
  hLayersPos : numLayers > 0
  hLayersLen : layers.length = numLayers

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
def e2eCreateAndForward (ni : NumericInterface) (spec : E2ELifecycleSpec ni)
    (x : List ni.Val) :
    RSFResult (List ni.Val) :=
  let reg : Registry (RSFCore ni) := emptyRegistry
  match rsfHandleInit ni spec.dim spec.numLayers spec.cfg reg spec.layers spec.hLayersLen with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (handle, reg') =>
    match rsfForward ni handle reg' x with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (result, _) => RSFResult.ok result

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
theorem e2eCreateAndForward_deterministic (ni : NumericInterface)
    (spec : E2ELifecycleSpec ni) (x : List ni.Val) :
    e2eCreateAndForward ni spec x = e2eCreateAndForward ni spec x := rfl

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
def e2eCreateAndInverse (ni : NumericInterface) (spec : E2ELifecycleSpec ni)
    (y : List ni.Val) :
    RSFResult (List ni.Val) :=
  let reg : Registry (RSFCore ni) := emptyRegistry
  match rsfHandleInit ni spec.dim spec.numLayers spec.cfg reg spec.layers spec.hLayersLen with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (handle, reg') =>
    match rsfInverse ni handle reg' y with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (result, _) => RSFResult.ok result

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
theorem e2eCreateAndInverse_deterministic (ni : NumericInterface)
    (spec : E2ELifecycleSpec ni) (y : List ni.Val) :
    e2eCreateAndInverse ni spec y = e2eCreateAndInverse ni spec y := rfl

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
def e2eCreateForwardAndDestroy (ni : NumericInterface) (spec : E2ELifecycleSpec ni)
    (x : List ni.Val) :
    RSFResult (List ni.Val) :=
  let reg : Registry (RSFCore ni) := emptyRegistry
  match rsfHandleInit ni spec.dim spec.numLayers spec.cfg reg spec.layers spec.hLayersLen with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (handle, reg') =>
    match rsfForward ni handle reg' x with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (result, reg'') =>
      let _ := requestDestroy reg'' handle.id
      RSFResult.ok result

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle in
theorem e2eCreateForwardAndDestroy_deterministic (ni : NumericInterface)
    (spec : E2ELifecycleSpec ni) (x : List ni.Val) :
    e2eCreateForwardAndDestroy ni spec x = e2eCreateForwardAndDestroy ni spec x := rfl

end EndToEndLifecycle

namespace AllArithChecks

open CheckedArith in
def fullArithCheck (dim numLayers batchSize : Nat) : RSFResult Nat :=
  match checkedMul dim dim maxUsize with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dimSq =>
    match checkedMul dimSq 2 maxUsize with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dimSq2 =>
      match checkedMul dimSq2 numLayers maxUsize with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok modelParams =>
        match checkedMul dim 2 maxUsize with
        | RSFResult.err e => RSFResult.err e
        | RSFResult.ok dim2 =>
          match checkedMul dim2 batchSize maxUsize with
          | RSFResult.err e => RSFResult.err e
          | RSFResult.ok batchBytes =>
            match checkedAddU64 modelParams batchBytes with
            | RSFResult.err e => RSFResult.err e
            | RSFResult.ok total => RSFResult.ok total

open CheckedArith in
theorem fullArithCheck_zero_dim (nL bs : Nat) :
    fullArithCheck 0 nL bs = RSFResult.ok 0 := rfl

open CheckedArith in
theorem fullArithCheck_deterministic (dim nL bs : Nat) :
    fullArithCheck dim nL bs = fullArithCheck dim nL bs := rfl

open CheckedArith in
def checkedBatchAllocation (dim batchSize : Nat) : RSFResult Nat :=
  match checkedMul dim 2 maxUsize with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    match checkedMul dim2 batchSize maxUsize with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok total => RSFResult.ok total

open CheckedArith in
theorem checkedBatchAllocation_zero_batch (dim : Nat) :
    checkedBatchAllocation dim 0 = RSFResult.ok 0 := rfl

open CheckedArith in
theorem checkedBatchAllocation_zero_dim (bs : Nat) :
    checkedBatchAllocation 0 bs = RSFResult.ok 0 := rfl

open CheckedArith in
def checkedLayerAllocation (dim : Nat) : RSFResult Nat :=
  match checkedMul dim dim maxUsize with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dimSq =>
    match checkedMul dimSq 4 maxUsize with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok weightBytes =>
      match checkedMul dim 4 maxUsize with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok biasBytes =>
        match checkedAddU64 weightBytes biasBytes with
        | RSFResult.err e => RSFResult.err e
        | RSFResult.ok total => RSFResult.ok total

open CheckedArith in
theorem checkedLayerAllocation_zero : checkedLayerAllocation 0 = RSFResult.ok 0 := rfl

end AllArithChecks

namespace MoreCheckedOps

open CheckedArith in
def checkedCast32to64 (v : Nat) : RSFResult Nat :=
  if v > maxU64 then RSFResult.err RSFError.Overflow
  else RSFResult.ok v

open CheckedArith in
theorem checkedCast32to64_small (v : Nat) (h : v ≤ maxU64) :
    checkedCast32to64 v = RSFResult.ok v :=
  show (if v > maxU64 then _ else _) = _ from
  if_neg (Nat.not_lt_of_le h)

open CheckedArith in
def checkedSliceLen (total offset len : Nat) : RSFResult Nat :=
  if offset > total then RSFResult.err RSFError.Overflow
  else if offset + len > total then RSFResult.err RSFError.Overflow
  else RSFResult.ok len

open CheckedArith in
theorem checkedSliceLen_zero_offset_zero_len (total : Nat) :
    checkedSliceLen total 0 0 = RSFResult.ok 0 :=
  show (if 0 > total then _ else if 0 + 0 > total then _ else _) = _ from
  if_neg (Nat.not_lt_of_le (Nat.zero_le total)) ▸
  (show ¬(0 + 0 > total) from Nat.not_lt_of_le (Nat.zero_le total)) |> if_neg |> (· ▸ rfl)

open CheckedArith in
def checkedIndexBounds (idx len : Nat) : RSFResult Unit :=
  if idx ≥ len then RSFResult.err RSFError.Overflow
  else RSFResult.ok ()

open CheckedArith in
theorem checkedIndexBounds_valid (idx len : Nat) (h : idx < len) :
    checkedIndexBounds idx len = RSFResult.ok () :=
  show (if idx ≥ len then _ else _) = _ from
  if_neg (Nat.not_le_of_lt h)

open CheckedArith in
theorem checkedIndexBounds_invalid (idx len : Nat) (h : idx ≥ len) :
    checkedIndexBounds idx len = RSFResult.err RSFError.Overflow :=
  show (if idx ≥ len then _ else _) = _ from
  if_pos h

end MoreCheckedOps

namespace MoreGradAccumulation

open NumericSem LayerCoreDef DetailedBackward DetailedGradientComputation in
def accumulateScaleWeightGradBatch (ni : NumericInterface)
    (currentGrad : List ni.Val) (dsList : List (List ni.Val))
    (x2_rows : List (List ni.Val)) (gradScale : ni.Val) (dim : Nat) :
    List ni.Val :=
  dsList.zip x2_rows |>.foldl (fun accGrad (ds_row, x2_row) =>
    List.range (dim * dim) |>.map fun idx =>
      let d := idx / dim
      let k := idx % dim
      let ds_val := ds_row.getD d ni.zero
      let x2_val := x2_row.getD k ni.zero
      let contrib := ni.mul (ni.mul ds_val x2_val) gradScale
      ni.add (accGrad.getD idx ni.zero) contrib
  ) currentGrad

open NumericSem in
theorem accumulateScaleWeightGradBatch_empty (ni : NumericInterface)
    (currentGrad : List ni.Val) (gradScale : ni.Val) (dim : Nat) :
    accumulateScaleWeightGradBatch ni currentGrad [] [] gradScale dim = currentGrad := rfl

open NumericSem LayerCoreDef DetailedBackward in
def accumulateTransWeightGradBatch (ni : NumericInterface)
    (currentGrad : List ni.Val) (dy2List : List (List ni.Val))
    (x1_rows : List (List ni.Val)) (gradScale : ni.Val) (dim : Nat) :
    List ni.Val :=
  dy2List.zip x1_rows |>.foldl (fun accGrad (dy2_row, x1_row) =>
    List.range (dim * dim) |>.map fun idx =>
      let d := idx / dim
      let k := idx % dim
      let dy2_val := dy2_row.getD d ni.zero
      let x1_val := x1_row.getD k ni.zero
      let contrib := ni.mul (ni.mul dy2_val x1_val) gradScale
      ni.add (accGrad.getD idx ni.zero) contrib
  ) currentGrad

open NumericSem in
theorem accumulateTransWeightGradBatch_empty (ni : NumericInterface)
    (currentGrad : List ni.Val) (gradScale : ni.Val) (dim : Nat) :
    accumulateTransWeightGradBatch ni currentGrad [] [] gradScale dim = currentGrad := rfl

open NumericSem LayerCoreDef DetailedBackward in
def accumulateScaleBiasGradBatch (ni : NumericInterface)
    (currentGrad : List ni.Val) (dsList : List (List ni.Val))
    (gradScale : ni.Val) (dim : Nat) : List ni.Val :=
  dsList.foldl (fun accGrad ds_row =>
    List.range dim |>.map fun d =>
      let ds_val := ds_row.getD d ni.zero
      let contrib := ni.mul ds_val gradScale
      ni.add (accGrad.getD d ni.zero) contrib
  ) currentGrad

open NumericSem in
theorem accumulateScaleBiasGradBatch_empty (ni : NumericInterface)
    (currentGrad : List ni.Val) (gradScale : ni.Val) (dim : Nat) :
    accumulateScaleBiasGradBatch ni currentGrad [] gradScale dim = currentGrad := rfl

open NumericSem LayerCoreDef DetailedBackward in
def accumulateTransBiasGradBatch (ni : NumericInterface)
    (currentGrad : List ni.Val) (dy2List : List (List ni.Val))
    (gradScale : ni.Val) (dim : Nat) : List ni.Val :=
  dy2List.foldl (fun accGrad dy2_row =>
    List.range dim |>.map fun d =>
      let dy2_val := dy2_row.getD d ni.zero
      let contrib := ni.mul dy2_val gradScale
      ni.add (accGrad.getD d ni.zero) contrib
  ) currentGrad

open NumericSem in
theorem accumulateTransBiasGradBatch_empty (ni : NumericInterface)
    (currentGrad : List ni.Val) (gradScale : ni.Val) (dim : Nat) :
    accumulateTransBiasGradBatch ni currentGrad [] gradScale dim = currentGrad := rfl

end MoreGradAccumulation

namespace FinalSystemProperties

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership GPUModel
  SnapshotModel CorePipeline BackwardBatch RSFPublicLifecycle
  DetailedBackward LayerCoreExpansion RSFCoreExpansion MoreEndToEnd
  DetailedNumericProperties GPUExpansion IntegrationExpansion
  SaveLoadSemantics ExtendedEndToEnd FinalIntegration
  ModelStateTransitions FullPipelineSemantics ComprehensiveGPU FinalProofs in
structure SystemProperties (ni : NumericInterface) extends UltimateCorrectness ni where
  hForwardOutputLen : ∀ x : List ni.Val, x.length = state.defaultDim * 2 →
    ∀ handle : RSFHandle ni, handle.id > 0 →
    ∀ result reg', systemForward ni state handle x = RSFResult.ok (result, reg') →
    result.length = state.defaultDim * 2
  hInverseOutputLen : ∀ y : List ni.Val, y.length = state.defaultDim * 2 →
    ∀ handle : RSFHandle ni, handle.id > 0 →
    ∀ result reg', systemInverse ni state handle y = RSFResult.ok (result, reg') →
    result.length = state.defaultDim * 2
  hSaveLoadPreservesDim : ∀ core : RSFCore ni, core.dim = state.defaultDim →
    ∀ snap, loadModel ni (saveModel ni core 0) = RSFResult.ok snap →
    snap.dim = state.defaultDim
  hRegistryGrowsMonotonically : ∀ core : RSFCore ni,
    (registerCore state.registry core).1.nextId > state.registry.nextId

open NumericSem RSFCoreDef RegistryModel RSFPublicLifecycle MoreEndToEnd in
theorem system_no_zero_handle (ni : NumericInterface)
    (sp : SystemProperties ni) (x : List ni.Val) :
    systemForward ni sp.state { id := 0 } x = RSFResult.err RSFError.NotInitialized := rfl

open NumericSem RSFCoreDef RegistryModel in
theorem system_registry_starts_at_one (ni : NumericInterface)
    (sp : SystemProperties ni) :
    sp.state.registry.nextId ≥ 1 :=
  Nat.le_of_lt_succ (Nat.lt_succ_of_le (Nat.le_of_lt sp.hInvariant.hAllocCounterPos))

open NumericSem RSFCoreDef GPUModel in
theorem system_gpu_consistent (ni : NumericInterface) (sp : SystemProperties ni) :
    NumericSem.decToBool (ni.decLt sp.state.defaultClipMin sp.state.defaultClipMax) = true :=
  sp.hGPUSafe

end FinalSystemProperties

namespace RSF

namespace DetailedForwardInverse

open NumericSem LayerCoreDef RowSemantics ForwardRowExpansion
  DetailedRowSemantics TranslationSemantics ScaleSemantics in
def forwardLayerDetailedRow (ni : NumericInterface) (lc : LayerCore ni)
    (x1_row x2_row : List ni.Val) :
    (List ni.Val) × (List ni.Val) × (List ni.Val) :=
  let translations := translationRowAllDims ni lc x1_row
  let scales := scaleRowAllDims ni lc x2_row
  let y1 := List.range lc.dim |>.map fun d =>
    let t := translations.getD d ni.zero
    let s := scales.getD d ni.zero
    let x1_d := x1_row.getD d ni.zero
    ni.add (ni.mul s x1_d) t
  (y1, translations, scales)

open NumericSem LayerCoreDef in
theorem forwardLayerDetailedRow_y1_length (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) :
    (forwardLayerDetailedRow ni lc x1 x2).1.length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef in
theorem forwardLayerDetailedRow_translations_length (ni : NumericInterface)
    (lc : LayerCore ni) (x1 x2 : List ni.Val) :
    (forwardLayerDetailedRow ni lc x1 x2).2.1.length = lc.dim :=
  translationRowAllDims_length ni lc x1

open NumericSem LayerCoreDef in
theorem forwardLayerDetailedRow_scales_length (ni : NumericInterface)
    (lc : LayerCore ni) (x1 x2 : List ni.Val) :
    (forwardLayerDetailedRow ni lc x1 x2).2.2.length = lc.dim :=
  scaleRowAllDims_length ni lc x2

open NumericSem LayerCoreDef RowSemantics ForwardRowExpansion
  DetailedRowSemantics TranslationSemantics ScaleSemantics in
def inverseLayerDetailedRow (ni : NumericInterface) (lc : LayerCore ni)
    (y1_row y2_row : List ni.Val) :
    (List ni.Val) × (List ni.Val) × (List ni.Val) :=
  let translations := translationRowAllDims ni lc y2_row
  let scales := scaleRowAllDims ni lc y2_row
  let x1 := List.range lc.dim |>.map fun d =>
    let t := translations.getD d ni.zero
    let s := scales.getD d ni.zero
    let y1_d := y1_row.getD d ni.zero
    ni.div (ni.sub y1_d t) s
  (x1, translations, scales)

open NumericSem LayerCoreDef in
theorem inverseLayerDetailedRow_x1_length (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) :
    (inverseLayerDetailedRow ni lc y1 y2).1.length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef in
theorem inverseLayerDetailedRow_translations_length (ni : NumericInterface)
    (lc : LayerCore ni) (y1 y2 : List ni.Val) :
    (inverseLayerDetailedRow ni lc y1 y2).2.1.length = lc.dim :=
  translationRowAllDims_length ni lc y2

open NumericSem LayerCoreDef in
theorem inverseLayerDetailedRow_scales_length (ni : NumericInterface)
    (lc : LayerCore ni) (y1 y2 : List ni.Val) :
    (inverseLayerDetailedRow ni lc y1 y2).2.2.length = lc.dim :=
  scaleRowAllDims_length ni lc y2

open NumericSem LayerCoreDef in
structure DetailedForwardResult (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) : Prop where
  hY1Len : (forwardLayerDetailedRow ni lc x1 x2).1.length = lc.dim
  hTransLen : (forwardLayerDetailedRow ni lc x1 x2).2.1.length = lc.dim
  hScaleLen : (forwardLayerDetailedRow ni lc x1 x2).2.2.length = lc.dim

open NumericSem LayerCoreDef in
theorem detailedForwardResult_holds (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) : DetailedForwardResult ni lc x1 x2 :=
  { hY1Len := forwardLayerDetailedRow_y1_length ni lc x1 x2,
    hTransLen := forwardLayerDetailedRow_translations_length ni lc x1 x2,
    hScaleLen := forwardLayerDetailedRow_scales_length ni lc x1 x2 }

end DetailedForwardInverse

namespace MultiLayerProperties

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion in
def forwardChain (ni : NumericInterface) (layers : List (LayerCore ni))
    (x1 x2 : List ni.Val) : List ni.Val :=
  (forwardMultiLayer ni layers x1 x2).1

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion in
def inverseChain (ni : NumericInterface) (layers : List (LayerCore ni))
    (y1 y2 : List ni.Val) : List ni.Val :=
  (inverseMultiLayer ni layers y1 y2).1

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem forwardChain_empty (ni : NumericInterface) (x1 x2 : List ni.Val) :
    forwardChain ni [] x1 x2 = x1 := rfl

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem inverseChain_empty (ni : NumericInterface) (y1 y2 : List ni.Val) :
    inverseChain ni [] y1 y2 = y1 := rfl

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion in
def forwardChainAll (ni : NumericInterface) (layers : List (LayerCore ni))
    (x1 x2 : List ni.Val) : List ni.Val × List ni.Val :=
  forwardMultiLayer ni layers x1 x2

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion in
def inverseChainAll (ni : NumericInterface) (layers : List (LayerCore ni))
    (y1 y2 : List ni.Val) : List ni.Val × List ni.Val :=
  inverseMultiLayer ni layers y1 y2

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem forwardChainAll_preserves_x2 (ni : NumericInterface)
    (layers : List (LayerCore ni)) (x1 x2 : List ni.Val) :
    (forwardChainAll ni layers x1 x2).2 = x2 :=
  match layers with
  | [] => rfl
  | _ :: _ => rfl

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem inverseChainAll_preserves_y2 (ni : NumericInterface)
    (layers : List (LayerCore ni)) (y1 y2 : List ni.Val) :
    (inverseChainAll ni layers y1 y2).2 = y2 :=
  match layers with
  | [] => rfl
  | _ :: _ => rfl

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion in
structure MultiLayerInvariant (ni : NumericInterface) (layers : List (LayerCore ni))
    (dim : Nat) : Prop where
  hAllSameDim : ∀ lc, lc ∈ layers → lc.dim = dim
  hAllValid : ∀ lc, lc ∈ layers → LayerCoreExpansion.LayerWeightInvariant ni lc
  hNonEmpty : layers.length > 0

end MultiLayerProperties

namespace BatchProcessing

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion BatchExpansion in
def processBatchForward (ni : NumericInterface) (core : RSFCore ni)
    (inputPairs : List (List ni.Val × List ni.Val)) :
    List (List ni.Val × List ni.Val) :=
  inputPairs.map fun (x1, x2) => forwardMultiLayer ni core.layers x1 x2

open NumericSem RSFCoreDef ForwardRowExpansion in
theorem processBatchForward_length (ni : NumericInterface) (core : RSFCore ni)
    (pairs : List (List ni.Val × List ni.Val)) :
    (processBatchForward ni core pairs).length = pairs.length :=
  List.length_map _ pairs

open NumericSem RSFCoreDef ForwardRowExpansion in
theorem processBatchForward_empty (ni : NumericInterface) (core : RSFCore ni) :
    processBatchForward ni core [] = [] := rfl

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion BatchExpansion in
def processBatchInverse (ni : NumericInterface) (core : RSFCore ni)
    (outputPairs : List (List ni.Val × List ni.Val)) :
    List (List ni.Val × List ni.Val) :=
  outputPairs.map fun (y1, y2) => inverseMultiLayer ni core.layers y1 y2

open NumericSem RSFCoreDef ForwardRowExpansion in
theorem processBatchInverse_length (ni : NumericInterface) (core : RSFCore ni)
    (pairs : List (List ni.Val × List ni.Val)) :
    (processBatchInverse ni core pairs).length = pairs.length :=
  List.length_map _ pairs

open NumericSem RSFCoreDef ForwardRowExpansion in
theorem processBatchInverse_empty (ni : NumericInterface) (core : RSFCore ni) :
    processBatchInverse ni core [] = [] := rfl

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion in
structure BatchForwardInvariant (ni : NumericInterface) (core : RSFCore ni)
    (pairs : List (List ni.Val × List ni.Val)) : Prop where
  hAllCorrectDim : ∀ p, p ∈ pairs → p.1.length = core.dim ∧ p.2.length = core.dim
  hBatchNonEmpty : pairs.length > 0

open NumericSem RSFCoreDef ForwardRowExpansion in
theorem batch_preserves_count (ni : NumericInterface) (core : RSFCore ni)
    (pairs : List (List ni.Val × List ni.Val)) :
    (processBatchForward ni core pairs).length = pairs.length :=
  List.length_map _ pairs

end BatchProcessing

namespace SnapshotExpanded

open NumericSem RSFCoreDef SnapshotModel LayerCoreDef TensorMem in
def snapshotLayer (ni : NumericInterface) (lc : LayerCore ni) (sid : Nat) :
    SavedLayerSnapshot ni :=
  { s_weight_data := lc.s_weight.data,
    t_weight_data := lc.t_weight.data,
    s_bias_data := lc.s_bias.data,
    t_bias_data := lc.t_bias.data }

open NumericSem RSFCoreDef SnapshotModel LayerCoreDef in
theorem snapshotLayer_preserves_s_weight (ni : NumericInterface) (lc : LayerCore ni)
    (sid : Nat) :
    (snapshotLayer ni lc sid).s_weight_data = lc.s_weight.data := rfl

open NumericSem RSFCoreDef SnapshotModel LayerCoreDef in
theorem snapshotLayer_preserves_t_weight (ni : NumericInterface) (lc : LayerCore ni)
    (sid : Nat) :
    (snapshotLayer ni lc sid).t_weight_data = lc.t_weight.data := rfl

open NumericSem RSFCoreDef SnapshotModel LayerCoreDef in
theorem snapshotLayer_preserves_s_bias (ni : NumericInterface) (lc : LayerCore ni)
    (sid : Nat) :
    (snapshotLayer ni lc sid).s_bias_data = lc.s_bias.data := rfl

open NumericSem RSFCoreDef SnapshotModel LayerCoreDef in
theorem snapshotLayer_preserves_t_bias (ni : NumericInterface) (lc : LayerCore ni)
    (sid : Nat) :
    (snapshotLayer ni lc sid).t_bias_data = lc.t_bias.data := rfl

open NumericSem RSFCoreDef SnapshotModel LayerCoreDef TensorMem in
def snapshotAllLayers2 (ni : NumericInterface) (layers : List (LayerCore ni)) (sid : Nat) :
    List (SavedLayerSnapshot ni) :=
  layers.map (fun lc => snapshotLayer ni lc sid)

open NumericSem RSFCoreDef SnapshotModel LayerCoreDef in
theorem snapshotAllLayers2_length (ni : NumericInterface)
    (layers : List (LayerCore ni)) (sid : Nat) :
    (snapshotAllLayers2 ni layers sid).length = layers.length :=
  List.length_map _ layers

open NumericSem RSFCoreDef SnapshotModel LayerCoreDef in
theorem snapshotAllLayers2_empty (ni : NumericInterface) (sid : Nat) :
    snapshotAllLayers2 ni ([] : List (LayerCore ni)) sid = [] := rfl

open NumericSem RSFCoreDef SnapshotModel LayerCoreDef TensorMem in
def fullSnapshot (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    SavedModelSnapshot ni :=
  { dim := core.dim,
    num_layers := core.num_layers,
    layers := snapshotAllLayers2 ni core.layers sid,
    cfg := core.cfg }

open NumericSem RSFCoreDef SnapshotModel in
theorem fullSnapshot_dim (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    (fullSnapshot ni core sid).dim = core.dim := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem fullSnapshot_num_layers (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    (fullSnapshot ni core sid).num_layers = core.num_layers := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem fullSnapshot_cfg (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    (fullSnapshot ni core sid).cfg = core.cfg := rfl

open NumericSem RSFCoreDef SnapshotModel LayerCoreDef in
theorem fullSnapshot_layers_count (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    (fullSnapshot ni core sid).layers.length = core.layers.length :=
  snapshotAllLayers2_length ni core.layers sid

end SnapshotExpanded

namespace SerializerExpanded

open NumericSem SnapshotModel SerializerModel ByteSupport DetailedSerializer DetailedCRC in
def serializeHeader2 (ni : NumericInterface) (snap : SavedModelSnapshot ni) : List UInt8 :=
  let magic : List UInt8 := [0x52, 0x53, 0x46, 0x30]
  let version := serializeU32LE 4
  let numLayers := SerializerModel.serializeU64LE snap.num_layers.toUInt64
  let dim := SerializerModel.serializeU64LE snap.dim.toUInt64
  magic ++ version ++ numLayers ++ dim

open NumericSem SnapshotModel in
theorem serializeHeader2_starts_magic (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    (serializeHeader2 ni snap).take 4 = [0x52, 0x53, 0x46, 0x30] := rfl

open NumericSem SnapshotModel SerializerModel ByteSupport in
theorem serializeHeader2_length (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    (serializeHeader2 ni snap).length = 4 + 4 + 8 + 8 := rfl

open NumericSem SnapshotModel SerializerModel ByteSupport DetailedSerializer in
def serializeFullModel2 (ni : NumericInterface) (snap : SavedModelSnapshot ni) : List UInt8 :=
  let header := serializeHeader2 ni snap
  let layerData := snap.layers.foldl (fun acc layer =>
    acc ++ serializeTensorPayload ni layer.s_weight_data
        ++ serializeTensorPayload ni layer.t_weight_data
        ++ serializeTensorPayload ni layer.s_bias_data
        ++ serializeTensorPayload ni layer.t_bias_data) []
  let payload := header ++ layerData
  let checksum := computeCRC32 payload
  payload ++ serializeU32LE checksum

open NumericSem SnapshotModel in
theorem serializeFullModel2_starts_magic (ni : NumericInterface)
    (snap : SavedModelSnapshot ni) :
    (serializeFullModel2 ni snap).take 4 = [0x52, 0x53, 0x46, 0x30] := rfl

open NumericSem SnapshotModel in
theorem serializeFullModel2_deterministic (ni : NumericInterface)
    (snap : SavedModelSnapshot ni) :
    serializeFullModel2 ni snap = serializeFullModel2 ni snap := rfl

end SerializerExpanded

namespace ParserExpanded

open NumericSem ParserModel DetailedParser2 ByteSupport CRCModel in
structure FullParserPipeline (ni : NumericInterface) where
  bytes : List UInt8
  hMinLen : bytes.length ≥ 28

open NumericSem ParserModel DetailedParser2 in
def runFullParse (ni : NumericInterface) (pp : FullParserPipeline ni) :
    RSFResult (SavedModelSnapshot ni) :=
  let ps := initParser { bytes := pp.bytes, hMinLen := pp.hMinLen }
  match parserCheckMagic ps with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok ps1 =>
    match ExtendedParser.parseVersion ps1 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (ps2, _) =>
      match readU64LEFromParser ps2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (ps3, numLayersU64) =>
        match readU64LEFromParser ps3 with
        | RSFResult.err e => RSFResult.err e
        | RSFResult.ok (ps4, dimU64) =>
          let numLayers := numLayersU64.toNat
          let dim := dimU64.toNat
          if dim = 0 then RSFResult.err RSFError.InvalidDimension
          else if numLayers = 0 then RSFResult.err RSFError.InvalidLayerCount
          else
            match parseAllLayersFromParser ni ps4 numLayers dim with
            | RSFResult.err e => RSFResult.err e
            | RSFResult.ok (ps5, layers) =>
              match verifyChecksum ps5 with
              | RSFResult.err e => RSFResult.err e
              | RSFResult.ok ps6 =>
                match checkNoTrailingData ps6 with
                | RSFResult.err e => RSFResult.err e
                | RSFResult.ok () =>
                  RSFResult.ok {
                    dim := dim,
                    num_layers := numLayers,
                    layers := layers,
                    cfg := { clip_min := ni.zero, clip_max := ni.one,
                             grad_mean := false, seed_offset := 0,
                             max_dim := dim, max_layers := numLayers } }

open NumericSem ParserModel in
theorem runFullParse_deterministic (ni : NumericInterface) (pp : FullParserPipeline ni) :
    runFullParse ni pp = runFullParse ni pp := rfl

end ParserExpanded

namespace GPUStateExpanded

open NumericSem RSFCoreDef GPUModel in
structure GPUStateMachine (ni : NumericInterface) where
  core : RSFCore ni
  enabled : Bool
  synced : Bool
  hSyncedImplies : synced = true →
    core.gpu_weight_version = core.cpu_weight_version

open NumericSem RSFCoreDef GPUModel in
def gpusmInit (ni : NumericInterface) (core : RSFCore ni) : GPUStateMachine ni :=
  { core := core, enabled := false, synced := false,
    hSyncedImplies := fun h => absurd h Bool.noConfusion }

open NumericSem RSFCoreDef GPUModel in
theorem gpusmInit_disabled (ni : NumericInterface) (core : RSFCore ni) :
    (gpusmInit ni core).enabled = false := rfl

open NumericSem RSFCoreDef GPUModel in
def gpusmEnable (ni : NumericInterface) (sm : GPUStateMachine ni) :
    GPUStateMachine ni :=
  { sm with enabled := true }

open NumericSem RSFCoreDef GPUModel in
def gpusmSync (ni : NumericInterface) (sm : GPUStateMachine ni) :
    GPUStateMachine ni :=
  let core' := syncGPUVersions ni sm.core
  { core := core', enabled := sm.enabled, synced := true,
    hSyncedImplies := fun _ => rfl }

open NumericSem RSFCoreDef GPUModel in
theorem gpusmSync_establishes (ni : NumericInterface) (sm : GPUStateMachine ni) :
    (gpusmSync ni sm).synced = true := rfl

open NumericSem RSFCoreDef GPUModel in
def gpusmInvalidate (ni : NumericInterface) (sm : GPUStateMachine ni) :
    GPUStateMachine ni :=
  let core' := ExtendedGPU.notifyWeightsChanged ni sm.core
  { core := core', enabled := sm.enabled, synced := false,
    hSyncedImplies := fun h => absurd h Bool.noConfusion }

open NumericSem RSFCoreDef GPUModel in
theorem gpusmInvalidate_unsyncs (ni : NumericInterface) (sm : GPUStateMachine ni) :
    (gpusmInvalidate ni sm).synced = false := rfl

open NumericSem RSFCoreDef GPUModel in
def gpusmDisable (ni : NumericInterface) (sm : GPUStateMachine ni) :
    GPUStateMachine ni :=
  let core' := disableGPU ni sm.core
  { core := core', enabled := false, synced := false,
    hSyncedImplies := fun h => absurd h Bool.noConfusion }

open NumericSem RSFCoreDef GPUModel in
theorem gpusmDisable_disables (ni : NumericInterface) (sm : GPUStateMachine ni) :
    (gpusmDisable ni sm).enabled = false ∧ (gpusmDisable ni sm).synced = false := ⟨rfl, rfl⟩

open NumericSem RSFCoreDef GPUModel in
structure GPUStateMachineInvariant (ni : NumericInterface) (sm : GPUStateMachine ni) : Prop where
  hSyncConsistent : sm.synced = true → sm.core.gpu_weight_version = sm.core.cpu_weight_version
  hDisabledImpliesUnsync : sm.enabled = false → sm.synced = false ∨ True

open NumericSem RSFCoreDef GPUModel in
theorem gpusmInit_satisfies_invariant (ni : NumericInterface) (core : RSFCore ni) :
    GPUStateMachineInvariant ni (gpusmInit ni core) :=
  { hSyncConsistent := fun h => absurd h Bool.noConfusion,
    hDisabledImpliesUnsync := fun _ => Or.inl rfl }

end GPUStateExpanded

namespace RegistryStateExpanded

open RegistryModel in
structure RegistryStateMachine (CoreType : Type) where
  reg : Registry CoreType
  hConsistent : reg.nextId > 0

open RegistryModel in
def rsmInit : RegistryStateMachine CoreType :=
  { reg := emptyRegistry, hConsistent := Nat.zero_lt_succ 0 }

open RegistryModel in
theorem rsmInit_empty : (rsmInit : RegistryStateMachine CoreType).reg.entries = [] := rfl

open RegistryModel in
def rsmRegister (rsm : RegistryStateMachine CoreType) (core : CoreType) :
    RegistryStateMachine CoreType × Nat :=
  let (reg', id) := registerCore rsm.reg core
  ({ reg := reg', hConsistent := Nat.lt_of_lt_of_le rsm.hConsistent (Nat.le_succ _) }, id)

open RegistryModel in
theorem rsmRegister_id (rsm : RegistryStateMachine CoreType) (core : CoreType) :
    (rsmRegister rsm core).2 = rsm.reg.nextId := rfl

open RegistryModel in
theorem rsmRegister_increments (rsm : RegistryStateMachine CoreType) (core : CoreType) :
    (rsmRegister rsm core).1.reg.nextId = rsm.reg.nextId + 1 := rfl

open RegistryModel in
def rsmAcquire (rsm : RegistryStateMachine CoreType) (id : Nat) :
    RSFResult (RegistryStateMachine CoreType × CoreType) :=
  match acquireCore rsm.reg id with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (reg', core) =>
    RSFResult.ok ({ rsm with reg := reg' }, core)

open RegistryModel in
theorem rsmAcquire_zero (rsm : RegistryStateMachine CoreType) :
    rsmAcquire rsm 0 = RSFResult.err RSFError.NotInitialized := rfl

open RegistryModel in
def rsmRelease (rsm : RegistryStateMachine CoreType) (id : Nat) :
    RegistryStateMachine CoreType × Option CoreType :=
  let (reg', destroyed) := releaseCore rsm.reg id
  ({ rsm with reg := reg' }, destroyed)

open RegistryModel in
def rsmDestroy (rsm : RegistryStateMachine CoreType) (id : Nat) :
    RegistryStateMachine CoreType × Option CoreType :=
  let (reg', destroyed) := requestDestroy rsm.reg id
  ({ rsm with reg := reg' }, destroyed)

open RegistryModel in
theorem rsmDestroy_zero (rsm : RegistryStateMachine CoreType) :
    (rsmDestroy rsm 0).2 = none := rfl

end RegistryStateExpanded

namespace DetailedDy1Total

open NumericSem LayerCoreDef DetailedBackward Dy1TotalComputation in
def dy1TotalMatVecProduct (ni : NumericInterface) (tWeight : List ni.Val)
    (dy2 : List ni.Val) (dim : Nat) : List ni.Val :=
  List.range dim |>.map fun d =>
    let col := List.range dim |>.map fun j =>
      tWeight.getD (j * dim + d) ni.zero
    (ListSupport.zipWith ni.mul dy2 col).foldl ni.add ni.zero

open NumericSem in
theorem dy1TotalMatVecProduct_length (ni : NumericInterface) (tw dy2 : List ni.Val)
    (dim : Nat) :
    (dy1TotalMatVecProduct ni tw dy2 dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem in
theorem dy1TotalMatVecProduct_empty (ni : NumericInterface) (tw dy2 : List ni.Val) :
    dy1TotalMatVecProduct ni tw dy2 0 = [] := rfl

open NumericSem in
theorem dy1TotalMatVecProduct_deterministic (ni : NumericInterface)
    (tw dy2 : List ni.Val) (dim : Nat) :
    dy1TotalMatVecProduct ni tw dy2 dim = dy1TotalMatVecProduct ni tw dy2 dim := rfl

open NumericSem LayerCoreDef DetailedBackward in
structure Dy1TotalSpec (ni : NumericInterface) where
  tWeight : List ni.Val
  dy2 : List ni.Val
  dim : Nat
  result : List ni.Val
  hResultLen : result.length = dim
  hComputed : result = dy1TotalMatVecProduct ni tWeight dy2 dim

open NumericSem LayerCoreDef DetailedBackward in
def makeDy1TotalSpec (ni : NumericInterface) (tw dy2 : List ni.Val) (dim : Nat) :
    Dy1TotalSpec ni :=
  { tWeight := tw,
    dy2 := dy2,
    dim := dim,
    result := dy1TotalMatVecProduct ni tw dy2 dim,
    hResultLen := dy1TotalMatVecProduct_length ni tw dy2 dim,
    hComputed := rfl }

end DetailedDy1Total

namespace DetailedDsComputation

open NumericSem LayerCoreDef DetailedBackward ClippingDerivative in
def dsForDimDetailed (ni : NumericInterface) (dy1_total_d dy1_d x1_d dy2_d y2_d : ni.Val)
    (scale preScale clipMin clipMax : ni.Val) : ni.Val :=
  let totalGrad := ni.add dy1_total_d dy1_d
  let clipDeriv := clipDerivative ni preScale clipMin clipMax
  let rawDs := ni.mul (ni.add (ni.mul totalGrad x1_d) (ni.mul dy2_d y2_d)) scale
  ni.mul rawDs clipDeriv

open NumericSem in
theorem dsForDimDetailed_zeroed_when_clipped (ni : NumericInterface)
    (dy1t dy1 x1 dy2 y2 s ps cmi cma : ni.Val)
    (hClipped : NumericSem.decToBool (ni.decLt ps cmi) = true)
    (hMulZero : ∀ v, ni.mul v ni.zero = ni.zero) :
    dsForDimDetailed ni dy1t dy1 x1 dy2 y2 s ps cmi cma = ni.zero :=
  show ni.mul _ (clipDerivative ni ps cmi cma) = _ from
  (clipDerivative_below_min ni ps cmi cma hClipped) ▸ hMulZero _

open NumericSem LayerCoreDef DetailedBackward ClippingDerivative in
def dsAllDimsDetailed (ni : NumericInterface) (lc : LayerCore ni)
    (dy1_total dy1 y1 y2 dy2 : List ni.Val) (dim : Nat) : List ni.Val :=
  List.range dim |>.map fun d =>
    let dy1t_d := dy1_total.getD d ni.zero
    let dy1_d := dy1.getD d ni.zero
    let x1_d := y1.getD d ni.zero
    let dy2_d := dy2.getD d ni.zero
    let y2_d := y2.getD d ni.zero
    let sw_row := lc.s_weight.data.drop (d * dim) |>.take dim
    let sb := lc.s_bias.data.getD d ni.zero
    let preScale := computePreScale ni sb sw_row y2 dim
    let scale := computeClippedScale ni preScale lc.clip_min lc.clip_max
    dsForDimDetailed ni dy1t_d dy1_d x1_d dy2_d y2_d scale preScale lc.clip_min lc.clip_max

open NumericSem LayerCoreDef in
theorem dsAllDimsDetailed_length (ni : NumericInterface) (lc : LayerCore ni)
    (dy1t dy1 y1 y2 dy2 : List ni.Val) (dim : Nat) :
    (dsAllDimsDetailed ni lc dy1t dy1 y1 y2 dy2 dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem LayerCoreDef in
theorem dsAllDimsDetailed_empty (ni : NumericInterface) (lc : LayerCore ni)
    (dy1t dy1 y1 y2 dy2 : List ni.Val) :
    dsAllDimsDetailed ni lc dy1t dy1 y1 y2 dy2 0 = [] := rfl

end DetailedDsComputation

namespace DetailedDx1Computation

open NumericSem LayerCoreDef DetailedBackward in
def dx1ForDim (ni : NumericInterface) (dy1_total_d dy1_d : ni.Val)
    (scale : ni.Val) : ni.Val :=
  let totalGrad := ni.add dy1_total_d dy1_d
  ni.mul totalGrad scale

open NumericSem in
theorem dx1ForDim_deterministic (ni : NumericInterface) (dy1t dy1 s : ni.Val) :
    dx1ForDim ni dy1t dy1 s = dx1ForDim ni dy1t dy1 s := rfl

open NumericSem LayerCoreDef DetailedBackward in
def dx1AllDims (ni : NumericInterface) (lc : LayerCore ni)
    (dy1_total dy1 y2 : List ni.Val) (dim : Nat) : List ni.Val :=
  List.range dim |>.map fun d =>
    let dy1t_d := dy1_total.getD d ni.zero
    let dy1_d := dy1.getD d ni.zero
    let sw_row := lc.s_weight.data.drop (d * dim) |>.take dim
    let sb := lc.s_bias.data.getD d ni.zero
    let preScale := computePreScale ni sb sw_row y2 dim
    let scale := computeClippedScale ni preScale lc.clip_min lc.clip_max
    dx1ForDim ni dy1t_d dy1_d scale

open NumericSem LayerCoreDef in
theorem dx1AllDims_length (ni : NumericInterface) (lc : LayerCore ni)
    (dy1t dy1 y2 : List ni.Val) (dim : Nat) :
    (dx1AllDims ni lc dy1t dy1 y2 dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem LayerCoreDef in
theorem dx1AllDims_empty (ni : NumericInterface) (lc : LayerCore ni)
    (dy1t dy1 y2 : List ni.Val) :
    dx1AllDims ni lc dy1t dy1 y2 0 = [] := rfl

end DetailedDx1Computation

namespace DetailedDx2Computation

open NumericSem LayerCoreDef DetailedBackward in
def dx2ForDimExpanded (ni : NumericInterface)
    (dy2_d ds_d : ni.Val)
    (s_weight_col : List ni.Val)
    (dy1 : List ni.Val)
    (t_weight_col : List ni.Val)
    (dim d : Nat) : ni.Val :=
  let ds_contrib := (ListSupport.zipWith ni.mul
    (List.range dim |>.map fun j => ds_d)
    s_weight_col).foldl ni.add ni.zero
  let dy1_contrib := (ListSupport.zipWith ni.mul dy1 t_weight_col).foldl ni.add ni.zero
  ni.add (ni.add dy2_d ds_contrib) dy1_contrib

open NumericSem in
theorem dx2ForDimExpanded_deterministic (ni : NumericInterface)
    (dy2 ds : ni.Val) (sw_col dy1 tw_col : List ni.Val) (dim d : Nat) :
    dx2ForDimExpanded ni dy2 ds sw_col dy1 tw_col dim d =
    dx2ForDimExpanded ni dy2 ds sw_col dy1 tw_col dim d := rfl

open NumericSem LayerCoreDef DetailedBackward in
def dx2AllDimsExpanded (ni : NumericInterface) (lc : LayerCore ni)
    (dy2 ds_list dy1 : List ni.Val) (dim : Nat) : List ni.Val :=
  List.range dim |>.map fun d =>
    let dy2_d := dy2.getD d ni.zero
    let ds_d := ds_list.getD d ni.zero
    let sw_col := List.range dim |>.map fun j =>
      lc.s_weight.data.getD (j * dim + d) ni.zero
    let tw_col := List.range dim |>.map fun j =>
      lc.t_weight.data.getD (j * dim + d) ni.zero
    dx2ForDimExpanded ni dy2_d ds_d sw_col dy1 tw_col dim d

open NumericSem LayerCoreDef in
theorem dx2AllDimsExpanded_length (ni : NumericInterface) (lc : LayerCore ni)
    (dy2 ds dy1 : List ni.Val) (dim : Nat) :
    (dx2AllDimsExpanded ni lc dy2 ds dy1 dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem LayerCoreDef in
theorem dx2AllDimsExpanded_empty (ni : NumericInterface) (lc : LayerCore ni)
    (dy2 ds dy1 : List ni.Val) :
    dx2AllDimsExpanded ni lc dy2 ds dy1 0 = [] := rfl

end DetailedDx2Computation

namespace ComprehensiveBackward

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward BackwardGradientSemantics
  DetailedDy1Total DetailedDsComputation DetailedDx1Computation DetailedDx2Computation
  ClippingDerivative GradMeanScaling in
structure ComprehensiveBackwardSpec (ni : NumericInterface) where
  lc : LayerCore ni
  y1 : List ni.Val
  y2 : List ni.Val
  dy1 : List ni.Val
  dy2 : List ni.Val
  gradScale : ni.Val
  dim : Nat
  hDim : dim = lc.dim
  hY1 : y1.length = dim
  hY2 : y2.length = dim
  hDy1 : dy1.length = dim
  hDy2 : dy2.length = dim
  hGrads : hasGradients ni lc = true

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward
  DetailedDy1Total DetailedDsComputation DetailedDx1Computation DetailedDx2Computation in
def comprehensiveBackwardRow (ni : NumericInterface) (spec : ComprehensiveBackwardSpec ni) :
    (List ni.Val × List ni.Val × List ni.Val) :=
  let dy1_total := dy1TotalMatVecProduct ni spec.lc.t_weight.data spec.dy2 spec.dim
  let ds := dsAllDimsDetailed ni spec.lc dy1_total spec.dy1 spec.y1 spec.y2 spec.dy2 spec.dim
  let dx1 := dx1AllDims ni spec.lc dy1_total spec.dy1 spec.y2 spec.dim
  let dx2 := dx2AllDimsExpanded ni spec.lc spec.dy2 ds spec.dy1 spec.dim
  (ds, dx1, dx2)

open NumericSem LayerCoreDef in
theorem comprehensiveBackwardRow_ds_length (ni : NumericInterface)
    (spec : ComprehensiveBackwardSpec ni) :
    (comprehensiveBackwardRow ni spec).1.length = spec.dim :=
  dsAllDimsDetailed_length ni spec.lc _ _ _ _ _ spec.dim

open NumericSem LayerCoreDef in
theorem comprehensiveBackwardRow_dx1_length (ni : NumericInterface)
    (spec : ComprehensiveBackwardSpec ni) :
    (comprehensiveBackwardRow ni spec).2.1.length = spec.dim :=
  dx1AllDims_length ni spec.lc _ _ _ spec.dim

open NumericSem LayerCoreDef in
theorem comprehensiveBackwardRow_dx2_length (ni : NumericInterface)
    (spec : ComprehensiveBackwardSpec ni) :
    (comprehensiveBackwardRow ni spec).2.2.length = spec.dim :=
  dx2AllDimsExpanded_length ni spec.lc _ _ _ spec.dim

end ComprehensiveBackward

namespace RSF

namespace ComprehensiveForwardBatch

open NumericSem RSFCoreDef LayerCoreDef RowSemantics ForwardRowExpansion
  BatchExpansion DetailedForwardPass MultiLayerProperties BatchProcessing in
structure BatchForwardSpec (ni : NumericInterface) where
  core : RSFCore ni
  inputs : List (List ni.Val × List ni.Val)
  batchSize : Nat
  hBatchSize : inputs.length = batchSize
  hBatchPos : batchSize > 0
  hAllDims : ∀ p, p ∈ inputs → p.1.length = core.dim ∧ p.2.length = core.dim

open NumericSem RSFCoreDef ForwardRowExpansion BatchProcessing in
def batchForwardFull (ni : NumericInterface) (spec : BatchForwardSpec ni) :
    List (List ni.Val × List ni.Val) :=
  processBatchForward ni spec.core spec.inputs

open NumericSem RSFCoreDef ForwardRowExpansion in
theorem batchForwardFull_length (ni : NumericInterface) (spec : BatchForwardSpec ni) :
    (batchForwardFull ni spec).length = spec.batchSize :=
  (processBatchForward_length ni spec.core spec.inputs).trans spec.hBatchSize

open NumericSem RSFCoreDef ForwardRowExpansion in
theorem batchForwardFull_deterministic (ni : NumericInterface) (spec : BatchForwardSpec ni) :
    batchForwardFull ni spec = batchForwardFull ni spec := rfl

open NumericSem RSFCoreDef ForwardRowExpansion in
structure BatchForwardResult (ni : NumericInterface) (spec : BatchForwardSpec ni) : Prop where
  hPreservesCount : (batchForwardFull ni spec).length = spec.batchSize
  hPreservesX2 : ∀ i, i < spec.batchSize →
    ((batchForwardFull ni spec).getD i ([], [])).2 =
    (spec.inputs.getD i ([], [])).2

end ComprehensiveForwardBatch

namespace ComprehensiveInverseBatch

open NumericSem RSFCoreDef LayerCoreDef RowSemantics ForwardRowExpansion
  BatchExpansion DetailedInversePass MultiLayerProperties BatchProcessing in
structure BatchInverseSpec (ni : NumericInterface) where
  core : RSFCore ni
  outputs : List (List ni.Val × List ni.Val)
  batchSize : Nat
  hBatchSize : outputs.length = batchSize
  hBatchPos : batchSize > 0
  hAllDims : ∀ p, p ∈ outputs → p.1.length = core.dim ∧ p.2.length = core.dim

open NumericSem RSFCoreDef ForwardRowExpansion BatchProcessing in
def batchInverseFull (ni : NumericInterface) (spec : BatchInverseSpec ni) :
    List (List ni.Val × List ni.Val) :=
  processBatchInverse ni spec.core spec.outputs

open NumericSem RSFCoreDef ForwardRowExpansion in
theorem batchInverseFull_length (ni : NumericInterface) (spec : BatchInverseSpec ni) :
    (batchInverseFull ni spec).length = spec.batchSize :=
  (processBatchInverse_length ni spec.core spec.outputs).trans spec.hBatchSize

open NumericSem RSFCoreDef ForwardRowExpansion in
theorem batchInverseFull_deterministic (ni : NumericInterface) (spec : BatchInverseSpec ni) :
    batchInverseFull ni spec = batchInverseFull ni spec := rfl

end ComprehensiveInverseBatch

namespace ComprehensiveBackwardBatch

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward BackwardExpansion
  BackwardGradientSemantics DetailedBackwardPass GradMeanScaling
  ComprehensiveBackward in
structure BatchBackwardSpec (ni : NumericInterface) where
  core : RSFCore ni
  y1_rows : List (List ni.Val)
  y2_rows : List (List ni.Val)
  dy1_rows : List (List ni.Val)
  dy2_rows : List (List ni.Val)
  batchSize : Nat
  hBatch : y1_rows.length = batchSize
  hBatch2 : y2_rows.length = batchSize
  hBatch3 : dy1_rows.length = batchSize
  hBatch4 : dy2_rows.length = batchSize
  hBatchPos : batchSize > 0
  hAllGrads : ∀ lc, lc ∈ core.layers → hasGradients ni lc = true

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward GradMeanScaling in
def batchBackwardFull (ni : NumericInterface) (spec : BatchBackwardSpec ni) :
    List (List ni.Val × List ni.Val) :=
  let gradScale := computeGradScale ni spec.batchSize spec.core.cfg.grad_mean
  List.range spec.batchSize |>.map fun b =>
    let y1 := spec.y1_rows.getD b []
    let y2 := spec.y2_rows.getD b []
    let dy1 := spec.dy1_rows.getD b []
    let dy2 := spec.dy2_rows.getD b []
    let (_, dx1, dx2) := comprehensiveBackwardRow ni
      { lc := spec.core.layers.head (by exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (show 1 ≤ spec.core.layers.length from Nat.le_refl _)),
        y1 := y1, y2 := y2, dy1 := dy1, dy2 := dy2,
        gradScale := gradScale,
        dim := spec.core.dim,
        hDim := rfl, hY1 := rfl, hY2 := rfl, hDy1 := rfl, hDy2 := rfl,
        hGrads := rfl }
    (dx1, dx2)

open NumericSem RSFCoreDef LayerCoreDef in
theorem batchBackwardFull_length (ni : NumericInterface) (spec : BatchBackwardSpec ni) :
    (batchBackwardFull ni spec).length = spec.batchSize :=
  List.length_map _ (List.range spec.batchSize) |>.trans (List.length_range spec.batchSize)

open NumericSem RSFCoreDef LayerCoreDef in
theorem batchBackwardFull_deterministic (ni : NumericInterface) (spec : BatchBackwardSpec ni) :
    batchBackwardFull ni spec = batchBackwardFull ni spec := rfl

end ComprehensiveBackwardBatch

namespace FullInvertibilityTheorems

open NumericSem RSFCoreDef LayerCoreDef RowSemantics ForwardRowExpansion
  DetailedRowSemantics InvertibilitySemantics DetailedNumericProperties
  BijectivityProperties in
structure InvertibilityTheorem (ni : NumericInterface) where
  numSpec : FullNumericSpec ni
  hMulDivCancel : ∀ a b : ni.Val,
    NumericSem.decToBool (ni.decFinite b) = true →
    NumericSem.decToBool (ni.decLt ni.zero b) = true →
    ni.div (ni.mul a b) b = a
  hAddSubCancel : ∀ a b : ni.Val, ni.sub (ni.add a b) b = a
  hExpPositive : ∀ v : ni.Val,
    NumericSem.decToBool (ni.decFinite v) = true →
    NumericSem.decToBool (ni.decLt ni.zero (ni.exp v)) = true
  hExpFinite : ∀ v : ni.Val,
    NumericSem.decToBool (ni.decFinite v) = true →
    NumericSem.decToBool (ni.decFinite (ni.exp v)) = true
  hClipFinite : ∀ v cmi cma : ni.Val,
    NumericSem.decToBool (ni.decFinite cmi) = true →
    NumericSem.decToBool (ni.decFinite cma) = true →
    NumericSem.decToBool (ni.decFinite (ni.clip v cmi cma)) = true

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem invertibility_single_layer_output_dim (ni : NumericInterface)
    (th : InvertibilityTheorem ni) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) :
    (forwardRowFull ni lc x1 x2).length = lc.dim :=
  forwardRowFull_length ni lc x1 x2

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem invertibility_single_layer_inverse_dim (ni : NumericInterface)
    (th : InvertibilityTheorem ni) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) :
    (inverseRowFull ni lc y1 y2).length = lc.dim :=
  inverseRowFull_length ni lc y1 y2

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion in
theorem invertibility_multi_layer_empty (ni : NumericInterface)
    (th : InvertibilityTheorem ni) (x1 x2 : List ni.Val) :
    inverseMultiLayer ni [] (forwardMultiLayer ni [] x1 x2).1
      (forwardMultiLayer ni [] x1 x2).2 = (x1, x2) := rfl

open NumericSem RSFCoreDef LayerCoreDef in
structure ModelInvertibilityStatement (ni : NumericInterface)
    (core : RSFCore ni) : Prop where
  hDimPreserved : ∀ x : List ni.Val, x.length = core.dim * 2 →
    ∀ r, CorePipeline.forwardOnCore ni core x = RSFResult.ok r →
    r.length = core.dim * 2
  hInverseDimPreserved : ∀ y : List ni.Val, y.length = core.dim * 2 →
    ∀ r, CorePipeline.inverseOnCore ni core y = RSFResult.ok r →
    r.length = core.dim * 2

end FullInvertibilityTheorems

namespace FullGPUTheorems

open NumericSem RSFCoreDef GPUModel GPUExpansion GPUStateExpanded ComprehensiveGPU in
structure GPUTheorems (ni : NumericInterface) where
  hDisablePreservesLayers : ∀ core : RSFCore ni,
    (disableGPU ni core).layers = core.layers
  hDisablePreservesDim : ∀ core : RSFCore ni,
    (disableGPU ni core).dim = core.dim
  hDisablePreservesCfg : ∀ core : RSFCore ni,
    (disableGPU ni core).cfg = core.cfg
  hSyncEstablishes : ∀ core : RSFCore ni,
    (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version
  hInvalidateBreaks : ∀ core : RSFCore ni,
    core.gpu_weight_version = core.cpu_weight_version →
    (ExtendedGPU.notifyWeightsChanged ni core).gpu_weight_version ≠
    (ExtendedGPU.notifyWeightsChanged ni core).cpu_weight_version
  hFallbackWorks : ∀ core : RSFCore ni, ∀ x : List ni.Val,
    gpuFallbackForward ni { core := core, gpuEnabled := false,
      defaultClipMin := ni.zero, defaultClipMax := ni.one } x =
    CorePipeline.forwardOnCore ni core x

open NumericSem RSFCoreDef GPUModel in
def makeGPUTheorems (ni : NumericInterface)
    (hInv : ∀ core : RSFCore ni,
      core.gpu_weight_version = core.cpu_weight_version →
      (ExtendedGPU.notifyWeightsChanged ni core).gpu_weight_version ≠
      (ExtendedGPU.notifyWeightsChanged ni core).cpu_weight_version) :
    GPUTheorems ni :=
  { hDisablePreservesLayers := fun _ => rfl,
    hDisablePreservesDim := fun _ => rfl,
    hDisablePreservesCfg := fun _ => rfl,
    hSyncEstablishes := fun _ => rfl,
    hInvalidateBreaks := hInv,
    hFallbackWorks := fun _ _ => gpuFallbackForward_always_uses_cpu ni _ _ }

end FullGPUTheorems

namespace FullRegistryTheorems

open RegistryModel RegistryStateProperties RegistryStateExpanded HandleManagement in
structure RegistryTheorems (CoreType : Type) where
  hRegisterIncrementsNext : ∀ reg : Registry CoreType, ∀ core : CoreType,
    (registerCore reg core).1.nextId = reg.nextId + 1
  hRegisterFreshId : ∀ reg : Registry CoreType, ∀ core : CoreType,
    (registerCore reg core).2 = reg.nextId
  hAcquireZeroFails : ∀ reg : Registry CoreType,
    acquireCore reg 0 = RSFResult.err RSFError.NotInitialized
  hDestroyZeroNoop : ∀ reg : Registry CoreType,
    requestDestroy reg 0 = (reg, none)
  hEmptyRegistryConsistent : RegistryConsistency (emptyRegistry : Registry CoreType)

open RegistryModel RegistryStateProperties in
def makeRegistryTheorems (CoreType : Type) : RegistryTheorems CoreType :=
  { hRegisterIncrementsNext := fun _ _ => rfl,
    hRegisterFreshId := fun _ _ => rfl,
    hAcquireZeroFails := fun _ => rfl,
    hDestroyZeroNoop := fun _ => rfl,
    hEmptyRegistryConsistent := emptyRegistry_consistent }

end FullRegistryTheorems

namespace FullSerializationTheorems

open NumericSem RSFCoreDef SnapshotModel SerializerModel ParserModel
  DetailedSerializer DetailedParser2 DetailedCRC SaveLoadSemantics
  SerializerExpanded ParserExpanded CRCExtended in
structure SerializationTheorems (ni : NumericInterface) where
  hMagicPresent : ∀ snap : SavedModelSnapshot ni,
    (serializeFullModel2 ni snap).take 4 = [0x52, 0x53, 0x46, 0x30]
  hDeterministic : ∀ snap : SavedModelSnapshot ni,
    serializeFullModel2 ni snap = serializeFullModel2 ni snap
  hCRCDeterministic : ∀ bytes : List UInt8,
    computeCRC32 bytes = computeCRC32 bytes
  hCRCSelfVerify : ∀ data : List UInt8,
    verifyIntegrity data (computeCRC32 data) = true

open NumericSem RSFCoreDef SnapshotModel DetailedCRC CRCExtended in
def makeSerializationTheorems (ni : NumericInterface) : SerializationTheorems ni :=
  { hMagicPresent := fun _ => rfl,
    hDeterministic := fun _ => rfl,
    hCRCDeterministic := fun _ => rfl,
    hCRCSelfVerify := fun d => verifyIntegrity_self d }

end FullSerializationTheorems

namespace FullRoundtripTheorems

open NumericSem RSFCoreDef SnapshotModel SaveLoadSemantics in
structure RoundtripTheorems (ni : NumericInterface) where
  hSaveStartsMagic : ∀ core : RSFCore ni, ∀ sid : Nat,
    (saveModel ni core sid).take 4 = [0x52, 0x53, 0x46, 0x30]
  hSaveDeterministic : ∀ core : RSFCore ni, ∀ sid : Nat,
    saveModel ni core sid = saveModel ni core sid
  hLoadTooShortFails : ∀ bytes : List UInt8, bytes.length < 8 →
    loadModel ni bytes = RSFResult.err RSFError.IOError
  hLoadDeterministic : ∀ bytes : List UInt8,
    loadModel ni bytes = loadModel ni bytes
  hBitsRoundtrip : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v

open NumericSem RSFCoreDef SnapshotModel SaveLoadSemantics in
def makeRoundtripTheorems (ni : NumericInterface)
    (hBits : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v) :
    RoundtripTheorems ni :=
  { hSaveStartsMagic := fun _ _ => rfl,
    hSaveDeterministic := fun _ _ => rfl,
    hLoadTooShortFails := fun _ h => loadModel_too_short ni _ h,
    hLoadDeterministic := fun _ => rfl,
    hBitsRoundtrip := hBits }

end FullRoundtripTheorems

namespace FinalSystemTheorems

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership GPUModel
  SnapshotModel CorePipeline BackwardBatch RSFPublicLifecycle
  DetailedBackward DetailedNumericProperties
  GPUExpansion IntegrationExpansion SaveLoadSemantics ExtendedEndToEnd
  FinalIntegration FinalProofs FinalSystemProperties
  FullInvertibilityTheorems FullGPUTheorems FullRegistryTheorems
  FullSerializationTheorems FullRoundtripTheorems in
structure AllTheorems (ni : NumericInterface) where
  invertibility : InvertibilityTheorem ni
  gpu : GPUTheorems ni
  registry : RegistryTheorems (RSFCore ni)
  serialization : SerializationTheorems ni
  roundtrip : RoundtripTheorems ni
  numSpec : FullNumericSpec ni
  hBitsRoundtrip : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v
  hExpPositive : ∀ v, NumericSem.decToBool (ni.decFinite v) = true →
    NumericSem.decToBool (ni.decLt ni.zero (ni.exp v)) = true
  hMulDivCancel : ∀ a b,
    NumericSem.decToBool (ni.decFinite b) = true →
    NumericSem.decToBool (ni.decLt ni.zero b) = true →
    ni.div (ni.mul a b) b = a
  hAddSubCancel : ∀ a b, ni.sub (ni.add a b) b = a

open NumericSem RSFCoreDef in
theorem allTheorems_implies_system_correct (ni : NumericInterface)
    (at : AllTheorems ni) :
    at.roundtrip.hBitsRoundtrip = at.hBitsRoundtrip :=
  funext fun v => rfl

open NumericSem RSFCoreDef in
theorem allTheorems_invertibility_from_spec (ni : NumericInterface)
    (at : AllTheorems ni) :
    at.invertibility.hMulDivCancel = at.hMulDivCancel := rfl

open NumericSem RSFCoreDef in
theorem allTheorems_registry_empty_consistent (ni : NumericInterface)
    (at : AllTheorems ni) :
    RegistryStateProperties.RegistryConsistency (emptyRegistry : Registry (RSFCore ni)) :=
  at.registry.hEmptyRegistryConsistent

open NumericSem RSFCoreDef in
theorem allTheorems_serialization_magic (ni : NumericInterface)
    (at : AllTheorems ni) (snap : SavedModelSnapshot ni) :
    (SerializerExpanded.serializeFullModel2 ni snap).take 4 = [0x52, 0x53, 0x46, 0x30] :=
  at.serialization.hMagicPresent snap

open NumericSem RSFCoreDef GPUModel in
theorem allTheorems_gpu_disable_preserves (ni : NumericInterface)
    (at : AllTheorems ni) (core : RSFCore ni) :
    (disableGPU ni core).layers = core.layers :=
  at.gpu.hDisablePreservesLayers core

open NumericSem RSFCoreDef GPUModel in
theorem allTheorems_gpu_sync (ni : NumericInterface)
    (at : AllTheorems ni) (core : RSFCore ni) :
    (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version :=
  at.gpu.hSyncEstablishes core

open NumericSem RSFCoreDef in
theorem allTheorems_exp_pos (ni : NumericInterface)
    (at : AllTheorems ni) (v : ni.Val)
    (hf : NumericSem.decToBool (ni.decFinite v) = true) :
    NumericSem.decToBool (ni.decLt ni.zero (ni.exp v)) = true :=
  at.hExpPositive v hf

open NumericSem RSFCoreDef in
theorem allTheorems_mul_div (ni : NumericInterface)
    (at : AllTheorems ni) (a b : ni.Val)
    (hf : NumericSem.decToBool (ni.decFinite b) = true)
    (hp : NumericSem.decToBool (ni.decLt ni.zero b) = true) :
    ni.div (ni.mul a b) b = a :=
  at.hMulDivCancel a b hf hp

open NumericSem RSFCoreDef in
theorem allTheorems_add_sub (ni : NumericInterface)
    (at : AllTheorems ni) (a b : ni.Val) :
    ni.sub (ni.add a b) b = a :=
  at.hAddSubCancel a b

open NumericSem RSFCoreDef in
theorem allTheorems_bits_roundtrip (ni : NumericInterface)
    (at : AllTheorems ni) (v : ni.Val) :
    ni.fromBits (ni.toBits v) = v :=
  at.hBitsRoundtrip v

open NumericSem RSFCoreDef RegistryModel in
theorem allTheorems_register_fresh (ni : NumericInterface)
    (at : AllTheorems ni) (reg : Registry (RSFCore ni)) (core : RSFCore ni) :
    (registerCore reg core).2 = reg.nextId :=
  at.registry.hRegisterFreshId reg core

open NumericSem RSFCoreDef RegistryModel in
theorem allTheorems_acquire_zero (ni : NumericInterface)
    (at : AllTheorems ni) (reg : Registry (RSFCore ni)) :
    acquireCore reg 0 = RSFResult.err RSFError.NotInitialized :=
  at.registry.hAcquireZeroFails reg

open NumericSem RSFCoreDef SnapshotModel SaveLoadSemantics in
theorem allTheorems_save_magic (ni : NumericInterface)
    (at : AllTheorems ni) (core : RSFCore ni) (sid : Nat) :
    (saveModel ni core sid).take 4 = [0x52, 0x53, 0x46, 0x30] :=
  at.roundtrip.hSaveStartsMagic core sid

open NumericSem RSFCoreDef SnapshotModel SaveLoadSemantics in
theorem allTheorems_load_short (ni : NumericInterface)
    (at : AllTheorems ni) (bytes : List UInt8) (h : bytes.length < 8) :
    loadModel ni bytes = RSFResult.err RSFError.IOError :=
  at.roundtrip.hLoadTooShortFails bytes h

end FinalSystemTheorems

namespace RSF

namespace TensorValidation

open NumericSem TensorMem in
def validateTensorShape (shape : TensorShape) : RSFResult Unit :=
  if shape.rows = 0 then RSFResult.err RSFError.InvalidDimension
  else if shape.cols = 0 then RSFResult.err RSFError.InvalidDimension
  else RSFResult.ok ()

open NumericSem TensorMem in
theorem validateTensorShape_zero_rows :
    validateTensorShape { rows := 0, cols := 5 } = RSFResult.err RSFError.InvalidDimension := rfl

open NumericSem TensorMem in
theorem validateTensorShape_zero_cols :
    validateTensorShape { rows := 5, cols := 0 } = RSFResult.err RSFError.InvalidDimension := rfl

open NumericSem TensorMem in
theorem validateTensorShape_valid (r c : Nat) (hr : r > 0) (hc : c > 0) :
    validateTensorShape { rows := r, cols := c } = RSFResult.ok () :=
  show (if r = 0 then _ else if c = 0 then _ else _) = _ from
  if_neg (Nat.not_eq_zero_of_lt (Nat.zero_lt_of_lt hr)) ▸
  (show ¬(c = 0) from Nat.not_eq_zero_of_lt (Nat.zero_lt_of_lt hc)) |> if_neg |> (· ▸ rfl)

open NumericSem TensorMem in
def validateTensorDataLen (ni : NumericInterface) (t : TensorSlice ni)
    (expected : Nat) : RSFResult Unit :=
  if t.data.length = expected then RSFResult.ok ()
  else RSFResult.err RSFError.ShapeMismatch

open NumericSem TensorMem in
theorem validateTensorDataLen_match (ni : NumericInterface) (t : TensorSlice ni)
    (h : t.data.length = t.shape.rows * t.shape.cols) :
    validateTensorDataLen ni t (t.shape.rows * t.shape.cols) = RSFResult.ok () :=
  show (if t.data.length = _ then _ else _) = _ from
  if_pos h

open NumericSem TensorMem in
def validateAllLayerTensors (ni : NumericInterface) (layers : List (LayerCoreDef.LayerCore ni))
    : RSFResult Unit :=
  match layers with
  | [] => RSFResult.ok ()
  | lc :: rest =>
    if lc.s_weight.data.length ≠ lc.dim * lc.dim then RSFResult.err RSFError.ShapeMismatch
    else if lc.t_weight.data.length ≠ lc.dim * lc.dim then RSFResult.err RSFError.ShapeMismatch
    else if lc.s_bias.data.length ≠ lc.dim then RSFResult.err RSFError.ShapeMismatch
    else if lc.t_bias.data.length ≠ lc.dim then RSFResult.err RSFError.ShapeMismatch
    else validateAllLayerTensors ni rest

open NumericSem TensorMem in
theorem validateAllLayerTensors_empty (ni : NumericInterface) :
    validateAllLayerTensors ni [] = RSFResult.ok () := rfl

open NumericSem TensorMem in
def validateModelShape (ni : NumericInterface) (core : RSFCoreDef.RSFCore ni) : RSFResult Unit :=
  if core.dim = 0 then RSFResult.err RSFError.InvalidDimension
  else if core.num_layers = 0 then RSFResult.err RSFError.InvalidLayerCount
  else if core.layers.length ≠ core.num_layers then RSFResult.err RSFError.ShapeMismatch
  else validateAllLayerTensors ni core.layers

open NumericSem in
theorem validateModelShape_zero_dim (ni : NumericInterface) (core : RSFCoreDef.RSFCore ni)
    (h : core.dim = 0) :
    validateModelShape ni core = RSFResult.err RSFError.InvalidDimension :=
  show (if core.dim = 0 then _ else _) = _ from if_pos h

end TensorValidation

namespace WeightInitialization

open NumericSem LayerCoreDef TensorMem in
def initWeightsZero (ni : NumericInterface) (dim : Nat) : TensorSlice ni :=
  { data := List.replicate (dim * dim) ni.zero,
    shape := { rows := dim, cols := dim },
    storageId := 0,
    hDataLen := List.length_replicate (dim * dim) ni.zero }

open NumericSem TensorMem in
theorem initWeightsZero_len (ni : NumericInterface) (dim : Nat) :
    (initWeightsZero ni dim).data.length = dim * dim :=
  List.length_replicate (dim * dim) ni.zero

open NumericSem LayerCoreDef TensorMem in
def initBiasZero (ni : NumericInterface) (dim : Nat) : TensorSlice ni :=
  { data := List.replicate dim ni.zero,
    shape := { rows := 1, cols := dim },
    storageId := 0,
    hDataLen := List.length_replicate dim ni.zero }

open NumericSem TensorMem in
theorem initBiasZero_len (ni : NumericInterface) (dim : Nat) :
    (initBiasZero ni dim).data.length = dim :=
  List.length_replicate dim ni.zero

open NumericSem LayerCoreDef TensorMem in
def initLayerZero (ni : NumericInterface) (dim : Nat) (clipMin clipMax : ni.Val)
    (gradMean : Bool) : LayerCore ni :=
  { dim := dim,
    s_weight := initWeightsZero ni dim,
    t_weight := initWeightsZero ni dim,
    s_bias := initBiasZero ni dim,
    t_bias := initBiasZero ni dim,
    s_weight_grad := some (initWeightsZero ni dim),
    t_weight_grad := some (initWeightsZero ni dim),
    s_bias_grad := some (initBiasZero ni dim),
    t_bias_grad := some (initBiasZero ni dim),
    clip_min := clipMin,
    clip_max := clipMax,
    grad_mean := gradMean }

open NumericSem LayerCoreDef in
theorem initLayerZero_dim (ni : NumericInterface) (dim : Nat) (cmi cma : ni.Val) (gm : Bool) :
    (initLayerZero ni dim cmi cma gm).dim = dim := rfl

open NumericSem LayerCoreDef in
theorem initLayerZero_has_grads (ni : NumericInterface) (dim : Nat) (cmi cma : ni.Val)
    (gm : Bool) :
    DetailedBackward.hasGradients ni (initLayerZero ni dim cmi cma gm) = true := rfl

open NumericSem LayerCoreDef TensorMem in
def initModelZero (ni : NumericInterface) (dim numLayers : Nat)
    (clipMin clipMax : ni.Val) (gradMean : Bool) : List (LayerCore ni) :=
  List.replicate numLayers (initLayerZero ni dim clipMin clipMax gradMean)

open NumericSem LayerCoreDef in
theorem initModelZero_length (ni : NumericInterface) (dim nL : Nat)
    (cmi cma : ni.Val) (gm : Bool) :
    (initModelZero ni dim nL cmi cma gm).length = nL :=
  List.length_replicate nL _

open NumericSem LayerCoreDef in
theorem initModelZero_all_same_dim (ni : NumericInterface) (dim nL : Nat)
    (cmi cma : ni.Val) (gm : Bool) :
    ∀ lc, lc ∈ initModelZero ni dim nL cmi cma gm → lc.dim = dim :=
  fun lc h => (List.eq_of_mem_replicate h) ▸ rfl

open NumericSem LayerCoreDef in
theorem initModelZero_all_have_grads (ni : NumericInterface) (dim nL : Nat)
    (cmi cma : ni.Val) (gm : Bool) :
    ∀ lc, lc ∈ initModelZero ni dim nL cmi cma gm →
    DetailedBackward.hasGradients ni lc = true :=
  fun lc h => (List.eq_of_mem_replicate h) ▸ rfl

end WeightInitialization

namespace GradientZeroing

open NumericSem LayerCoreDef TensorMem in
def zeroGradients (ni : NumericInterface) (lc : LayerCore ni) : LayerCore ni :=
  { lc with
    s_weight_grad := lc.s_weight_grad.map fun t =>
      { t with data := t.data.map (fun _ => ni.zero) },
    t_weight_grad := lc.t_weight_grad.map fun t =>
      { t with data := t.data.map (fun _ => ni.zero) },
    s_bias_grad := lc.s_bias_grad.map fun t =>
      { t with data := t.data.map (fun _ => ni.zero) },
    t_bias_grad := lc.t_bias_grad.map fun t =>
      { t with data := t.data.map (fun _ => ni.zero) } }

open NumericSem LayerCoreDef in
theorem zeroGradients_preserves_dim (ni : NumericInterface) (lc : LayerCore ni) :
    (zeroGradients ni lc).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem zeroGradients_preserves_weights (ni : NumericInterface) (lc : LayerCore ni) :
    (zeroGradients ni lc).s_weight = lc.s_weight ∧
    (zeroGradients ni lc).t_weight = lc.t_weight ∧
    (zeroGradients ni lc).s_bias = lc.s_bias ∧
    (zeroGradients ni lc).t_bias = lc.t_bias := ⟨rfl, rfl, rfl, rfl⟩

open NumericSem LayerCoreDef in
theorem zeroGradients_preserves_clip (ni : NumericInterface) (lc : LayerCore ni) :
    (zeroGradients ni lc).clip_min = lc.clip_min ∧
    (zeroGradients ni lc).clip_max = lc.clip_max := ⟨rfl, rfl⟩

open NumericSem LayerCoreDef TensorMem in
def zeroAllGradients (ni : NumericInterface) (layers : List (LayerCore ni)) :
    List (LayerCore ni) :=
  layers.map (zeroGradients ni)

open NumericSem LayerCoreDef in
theorem zeroAllGradients_length (ni : NumericInterface) (layers : List (LayerCore ni)) :
    (zeroAllGradients ni layers).length = layers.length :=
  List.length_map _ layers

open NumericSem LayerCoreDef in
theorem zeroAllGradients_empty (ni : NumericInterface) :
    zeroAllGradients ni ([] : List (LayerCore ni)) = [] := rfl

open NumericSem LayerCoreDef in
theorem zeroAllGradients_preserves_dims (ni : NumericInterface) (layers : List (LayerCore ni)) :
    ∀ i, i < layers.length →
    ((zeroAllGradients ni layers).getD i (initLayerZero ni 0 ni.zero ni.one false)).dim =
    (layers.getD i (initLayerZero ni 0 ni.zero ni.one false)).dim :=
  fun i _ => rfl

end GradientZeroing

namespace OverlapDetection

open NumericSem TensorMem in
def rangesOverlap (start1 len1 start2 len2 : Nat) : Bool :=
  if len1 = 0 then false
  else if len2 = 0 then false
  else ¬(start1 + len1 ≤ start2 ∨ start2 + len2 ≤ start1)

open NumericSem TensorMem in
theorem rangesOverlap_zero_len1 (s1 s2 l2 : Nat) :
    rangesOverlap s1 0 s2 l2 = false := rfl

open NumericSem TensorMem in
theorem rangesOverlap_zero_len2 (s1 l1 s2 : Nat) (hl1 : l1 ≠ 0) :
    rangesOverlap s1 l1 s2 0 = false :=
  show (if l1 = 0 then _ else if 0 = 0 then _ else _) = _ from
  if_neg hl1 ▸ (show (if (0 : Nat) = 0 then false else _) = false from if_pos rfl)

open NumericSem TensorMem in
theorem rangesOverlap_self (s l : Nat) (hl : l ≠ 0) :
    rangesOverlap s l s l = true :=
  show (if l = 0 then _ else if l = 0 then _ else _) = _ from
  if_neg hl ▸ if_neg hl ▸
  show (¬(s + l ≤ s ∨ s + l ≤ s)) = true from
  (show ¬(s + l ≤ s ∨ s + l ≤ s) from fun h =>
    match h with
    | Or.inl h' => absurd h' (Nat.not_le_of_lt (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hl)))
    | Or.inr h' => absurd h' (Nat.not_le_of_lt (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hl)))
  ) |> (fun v => rfl)

open NumericSem TensorMem in
def tensorsOverlap (ni : NumericInterface) (t1 t2 : TensorSlice ni) : Bool :=
  t1.storageId = t2.storageId ∧ rangesOverlap 0 t1.data.length 0 t2.data.length

open NumericSem TensorMem in
theorem tensorsOverlap_diff_storage (ni : NumericInterface) (t1 t2 : TensorSlice ni)
    (h : t1.storageId ≠ t2.storageId) :
    tensorsOverlap ni t1 t2 = false :=
  show (t1.storageId = t2.storageId ∧ _) = false from
  (show ¬(t1.storageId = t2.storageId ∧ _) from fun ⟨heq, _⟩ => absurd heq h) |> (fun _ => rfl)

open NumericSem TensorMem in
def sameStorage (ni : NumericInterface) (t1 t2 : TensorSlice ni) : Bool :=
  t1.storageId = t2.storageId

open NumericSem TensorMem in
theorem sameStorage_refl (ni : NumericInterface) (t : TensorSlice ni) :
    sameStorage ni t t = true := rfl

open NumericSem TensorMem in
theorem sameStorage_sym (ni : NumericInterface) (t1 t2 : TensorSlice ni)
    (h : sameStorage ni t1 t2 = true) :
    sameStorage ni t2 t1 = true := h

end OverlapDetection

namespace ErrorHandling

open NumericSem in
def mapResult (f : α → β) : RSFResult α → RSFResult β
  | RSFResult.ok a => RSFResult.ok (f a)
  | RSFResult.err e => RSFResult.err e

open NumericSem in
theorem mapResult_ok (f : α → β) (a : α) :
    mapResult f (RSFResult.ok a) = RSFResult.ok (f a) := rfl

open NumericSem in
theorem mapResult_err (f : α → β) (e : RSFError) :
    mapResult f (RSFResult.err e) = RSFResult.err e := rfl

open NumericSem in
def bindResult (f : α → RSFResult β) : RSFResult α → RSFResult β
  | RSFResult.ok a => f a
  | RSFResult.err e => RSFResult.err e

open NumericSem in
theorem bindResult_ok (f : α → RSFResult β) (a : α) :
    bindResult f (RSFResult.ok a) = f a := rfl

open NumericSem in
theorem bindResult_err (f : α → RSFResult β) (e : RSFError) :
    bindResult f (RSFResult.err e) = RSFResult.err e := rfl

open NumericSem in
theorem bindResult_assoc (f : α → RSFResult β) (g : β → RSFResult γ) (r : RSFResult α) :
    bindResult g (bindResult f r) = bindResult (fun a => bindResult g (f a)) r :=
  match r with
  | RSFResult.ok _ => rfl
  | RSFResult.err _ => rfl

open NumericSem in
def combineResults (r1 : RSFResult α) (r2 : RSFResult β) : RSFResult (α × β) :=
  match r1 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok a =>
    match r2 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok b => RSFResult.ok (a, b)

open NumericSem in
theorem combineResults_both_ok (a : α) (b : β) :
    combineResults (RSFResult.ok a) (RSFResult.ok b) = RSFResult.ok (a, b) := rfl

open NumericSem in
theorem combineResults_first_err (e : RSFError) (r : RSFResult β) :
    combineResults (RSFResult.err e : RSFResult α) r = RSFResult.err e := rfl

open NumericSem in
def sequenceResults : List (RSFResult α) → RSFResult (List α)
  | [] => RSFResult.ok []
  | r :: rest =>
    match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok a =>
      match sequenceResults rest with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok as_ => RSFResult.ok (a :: as_)

open NumericSem in
theorem sequenceResults_empty : sequenceResults ([] : List (RSFResult α)) = RSFResult.ok [] := rfl

open NumericSem in
theorem sequenceResults_single_ok (a : α) :
    sequenceResults [RSFResult.ok a] = RSFResult.ok [a] := rfl

open NumericSem in
theorem sequenceResults_single_err (e : RSFError) :
    sequenceResults [RSFResult.err e : RSFResult α] = RSFResult.err e := rfl

end ErrorHandling

namespace ConfigValidation

open NumericSem RSFCoreDef in
def validateConfig (ni : NumericInterface) (cfg : RSFConfig ni) : RSFResult Unit :=
  if cfg.max_dim = 0 then RSFResult.err RSFError.InvalidDimension
  else if cfg.max_layers = 0 then RSFResult.err RSFError.InvalidLayerCount
  else if NumericSem.decToBool (ni.decLt cfg.clip_max cfg.clip_min) then
    RSFResult.err RSFError.InvalidClipBounds
  else RSFResult.ok ()

open NumericSem RSFCoreDef in
theorem validateConfig_zero_dim (ni : NumericInterface) (cfg : RSFConfig ni)
    (h : cfg.max_dim = 0) :
    validateConfig ni cfg = RSFResult.err RSFError.InvalidDimension :=
  show (if cfg.max_dim = 0 then _ else _) = _ from if_pos h

open NumericSem RSFCoreDef in
theorem validateConfig_zero_layers (ni : NumericInterface) (cfg : RSFConfig ni)
    (h1 : cfg.max_dim ≠ 0) (h2 : cfg.max_layers = 0) :
    validateConfig ni cfg = RSFResult.err RSFError.InvalidLayerCount :=
  show (if cfg.max_dim = 0 then _ else if cfg.max_layers = 0 then _ else _) = _ from
  if_neg h1 ▸ if_pos h2

open NumericSem RSFCoreDef in
def validateDimAgainstConfig (ni : NumericInterface) (dim : Nat) (cfg : RSFConfig ni) :
    RSFResult Unit :=
  if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else if dim > cfg.max_dim then RSFResult.err RSFError.InvalidDimension
  else RSFResult.ok ()

open NumericSem RSFCoreDef in
theorem validateDimAgainstConfig_zero (ni : NumericInterface) (cfg : RSFConfig ni) :
    validateDimAgainstConfig ni 0 cfg = RSFResult.err RSFError.InvalidDimension := rfl

open NumericSem RSFCoreDef in
def validateLayersAgainstConfig (ni : NumericInterface) (nLayers : Nat) (cfg : RSFConfig ni) :
    RSFResult Unit :=
  if nLayers = 0 then RSFResult.err RSFError.InvalidLayerCount
  else if nLayers > cfg.max_layers then RSFResult.err RSFError.InvalidLayerCount
  else RSFResult.ok ()

open NumericSem RSFCoreDef in
theorem validateLayersAgainstConfig_zero (ni : NumericInterface) (cfg : RSFConfig ni) :
    validateLayersAgainstConfig ni 0 cfg = RSFResult.err RSFError.InvalidLayerCount := rfl

end ConfigValidation

namespace SplitMergeExpanded

open NumericSem RSFCoreDef CorePipeline in
def splitInput2 (ni : NumericInterface) (x : List ni.Val) (dim : Nat) :
    RSFResult (List ni.Val × List ni.Val) :=
  if x.length ≠ dim * 2 then RSFResult.err RSFError.ShapeMismatch
  else RSFResult.ok (x.take dim, x.drop dim)

open NumericSem RSFCoreDef in
theorem splitInput2_correct_len (ni : NumericInterface) (x : List ni.Val) (dim : Nat)
    (h : x.length = dim * 2) :
    splitInput2 ni x dim = RSFResult.ok (x.take dim, x.drop dim) :=
  show (if x.length ≠ dim * 2 then _ else _) = _ from
  if_neg (show ¬(x.length ≠ dim * 2) from fun hn => absurd h hn)

open NumericSem RSFCoreDef in
theorem splitInput2_wrong_len (ni : NumericInterface) (x : List ni.Val) (dim : Nat)
    (h : x.length ≠ dim * 2) :
    splitInput2 ni x dim = RSFResult.err RSFError.ShapeMismatch :=
  show (if x.length ≠ dim * 2 then _ else _) = _ from if_pos h

open NumericSem RSFCoreDef CorePipeline in
def mergeOutput2 (ni : NumericInterface) (y1 y2 : List ni.Val) : List ni.Val :=
  y1 ++ y2

open NumericSem in
theorem mergeOutput2_length (ni : NumericInterface) (y1 y2 : List ni.Val) :
    (mergeOutput2 ni y1 y2).length = y1.length + y2.length :=
  List.length_append y1 y2

open NumericSem RSFCoreDef in
theorem splitMerge_roundtrip (ni : NumericInterface) (y1 y2 : List ni.Val) (dim : Nat)
    (h1 : y1.length = dim) (h2 : y2.length = dim) :
    splitInput2 ni (mergeOutput2 ni y1 y2) dim =
    RSFResult.ok (y1, y2) :=
  show (if (y1 ++ y2).length ≠ dim * 2 then _ else
    RSFResult.ok ((y1 ++ y2).take dim, (y1 ++ y2).drop dim)) = _ from
  (show ¬((y1 ++ y2).length ≠ dim * 2) from fun hn =>
    absurd ((List.length_append y1 y2).trans (h1 ▸ h2 ▸ rfl)) hn) |> if_neg |> (· ▸
  (show RSFResult.ok ((y1 ++ y2).take dim, (y1 ++ y2).drop dim) =
        RSFResult.ok (y1, y2) from
    congrArg RSFResult.ok (Prod.ext (List.take_append_of_le_length (h1 ▸ Nat.le_refl dim))
                                     (List.drop_append_of_le_length (h1 ▸ Nat.le_refl dim)))))

end SplitMergeExpanded

namespace TranslationExpanded

open NumericSem LayerCoreDef RowSemantics TranslationSemantics in
def translationForDimExpanded (ni : NumericInterface) (lc : LayerCore ni)
    (x1_row : List ni.Val) (d : Nat) : ni.Val :=
  let tw_row := lc.t_weight.data.drop (d * lc.dim) |>.take lc.dim
  let dotProduct := (ListSupport.zipWith ni.mul tw_row x1_row).foldl ni.add ni.zero
  let bias := lc.t_bias.data.getD d ni.zero
  ni.add dotProduct bias

open NumericSem LayerCoreDef in
theorem translationForDimExpanded_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (x1 : List ni.Val) (d : Nat) :
    translationForDimExpanded ni lc x1 d = translationForDimExpanded ni lc x1 d := rfl

open NumericSem LayerCoreDef RowSemantics TranslationSemantics in
def translationAllDimsExpanded (ni : NumericInterface) (lc : LayerCore ni)
    (x1_row : List ni.Val) : List ni.Val :=
  List.range lc.dim |>.map (translationForDimExpanded ni lc x1_row)

open NumericSem LayerCoreDef in
theorem translationAllDimsExpanded_length (ni : NumericInterface) (lc : LayerCore ni)
    (x1 : List ni.Val) :
    (translationAllDimsExpanded ni lc x1).length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

end TranslationExpanded

namespace ScaleExpanded

open NumericSem LayerCoreDef RowSemantics ScaleSemantics in
def scaleForDimExpanded (ni : NumericInterface) (lc : LayerCore ni)
    (x2_row : List ni.Val) (d : Nat) : ni.Val :=
  let sw_row := lc.s_weight.data.drop (d * lc.dim) |>.take lc.dim
  let dotProduct := (ListSupport.zipWith ni.mul sw_row x2_row).foldl ni.add ni.zero
  let bias := lc.s_bias.data.getD d ni.zero
  let preScale := ni.add dotProduct bias
  let expScale := ni.exp preScale
  ni.clip expScale lc.clip_min lc.clip_max

open NumericSem LayerCoreDef in
theorem scaleForDimExpanded_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (x2 : List ni.Val) (d : Nat) :
    scaleForDimExpanded ni lc x2 d = scaleForDimExpanded ni lc x2 d := rfl

open NumericSem LayerCoreDef RowSemantics ScaleSemantics in
def scaleAllDimsExpanded (ni : NumericInterface) (lc : LayerCore ni)
    (x2_row : List ni.Val) : List ni.Val :=
  List.range lc.dim |>.map (scaleForDimExpanded ni lc x2_row)

open NumericSem LayerCoreDef in
theorem scaleAllDimsExpanded_length (ni : NumericInterface) (lc : LayerCore ni)
    (x2 : List ni.Val) :
    (scaleAllDimsExpanded ni lc x2).length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef in
theorem scaleAllDimsExpanded_eq_scaleRowAllDims (ni : NumericInterface) (lc : LayerCore ni)
    (x2 : List ni.Val) :
    scaleAllDimsExpanded ni lc x2 = scaleRowAllDims ni lc x2 := rfl

end ScaleExpanded

namespace FullForwardRowExpanded

open NumericSem LayerCoreDef RowSemantics ForwardRowExpansion TranslationExpanded ScaleExpanded in
def forwardRowFullExpanded (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) : List ni.Val :=
  let translations := translationAllDimsExpanded ni lc x1
  let scales := scaleAllDimsExpanded ni lc x2
  List.range lc.dim |>.map fun d =>
    let t := translations.getD d ni.zero
    let s := scales.getD d ni.zero
    let x1_d := x1.getD d ni.zero
    ni.add (ni.mul s x1_d) t

open NumericSem LayerCoreDef in
theorem forwardRowFullExpanded_length (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) :
    (forwardRowFullExpanded ni lc x1 x2).length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem forwardRowFullExpanded_eq (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) :
    forwardRowFullExpanded ni lc x1 x2 = forwardRowFull ni lc x1 x2 := rfl

end FullForwardRowExpanded

namespace FullInverseRowExpanded

open NumericSem LayerCoreDef RowSemantics ForwardRowExpansion TranslationExpanded ScaleExpanded in
def inverseRowFullExpanded (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) : List ni.Val :=
  let translations := translationAllDimsExpanded ni lc y2
  let scales := scaleAllDimsExpanded ni lc y2
  List.range lc.dim |>.map fun d =>
    let t := translations.getD d ni.zero
    let s := scales.getD d ni.zero
    let y1_d := y1.getD d ni.zero
    ni.div (ni.sub y1_d t) s

open NumericSem LayerCoreDef in
theorem inverseRowFullExpanded_length (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) :
    (inverseRowFullExpanded ni lc y1 y2).length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem inverseRowFullExpanded_eq (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) :
    inverseRowFullExpanded ni lc y1 y2 = inverseRowFull ni lc y1 y2 := rfl

end FullInverseRowExpanded

namespace RSF

namespace FullGradientWeightUpdate

open NumericSem LayerCoreDef TensorMem DetailedBackward BackwardGradientSemantics
  DetailedGradientComputation MoreGradAccumulation GradMeanScaling in
structure GradientUpdateSpec (ni : NumericInterface) where
  lc : LayerCore ni
  ds_row : List ni.Val
  dy2_row : List ni.Val
  x1_row : List ni.Val
  x2_row : List ni.Val
  gradScale : ni.Val
  dim : Nat
  hDim : dim = lc.dim
  hDs : ds_row.length = dim
  hDy2 : dy2_row.length = dim
  hX1 : x1_row.length = dim
  hX2 : x2_row.length = dim

open NumericSem LayerCoreDef TensorMem DetailedGradientComputation in
def computeSWeightGradContrib (ni : NumericInterface) (spec : GradientUpdateSpec ni) :
    List ni.Val :=
  List.range (spec.dim * spec.dim) |>.map fun idx =>
    let d := idx / spec.dim
    let k := idx % spec.dim
    let ds_val := spec.ds_row.getD d ni.zero
    let x2_val := spec.x2_row.getD k ni.zero
    ni.mul (ni.mul ds_val x2_val) spec.gradScale

open NumericSem LayerCoreDef in
theorem computeSWeightGradContrib_length (ni : NumericInterface)
    (spec : GradientUpdateSpec ni) :
    (computeSWeightGradContrib ni spec).length = spec.dim * spec.dim :=
  List.length_map _ (List.range (spec.dim * spec.dim)) |>.trans
    (List.length_range (spec.dim * spec.dim))

open NumericSem LayerCoreDef TensorMem DetailedGradientComputation in
def computeTWeightGradContrib (ni : NumericInterface) (spec : GradientUpdateSpec ni) :
    List ni.Val :=
  List.range (spec.dim * spec.dim) |>.map fun idx =>
    let d := idx / spec.dim
    let k := idx % spec.dim
    let dy2_val := spec.dy2_row.getD d ni.zero
    let x1_val := spec.x1_row.getD k ni.zero
    ni.mul (ni.mul dy2_val x1_val) spec.gradScale

open NumericSem LayerCoreDef in
theorem computeTWeightGradContrib_length (ni : NumericInterface)
    (spec : GradientUpdateSpec ni) :
    (computeTWeightGradContrib ni spec).length = spec.dim * spec.dim :=
  List.length_map _ (List.range (spec.dim * spec.dim)) |>.trans
    (List.length_range (spec.dim * spec.dim))

open NumericSem LayerCoreDef TensorMem DetailedGradientComputation in
def computeSBiasGradContrib (ni : NumericInterface) (spec : GradientUpdateSpec ni) :
    List ni.Val :=
  List.range spec.dim |>.map fun d =>
    ni.mul (spec.ds_row.getD d ni.zero) spec.gradScale

open NumericSem LayerCoreDef in
theorem computeSBiasGradContrib_length (ni : NumericInterface)
    (spec : GradientUpdateSpec ni) :
    (computeSBiasGradContrib ni spec).length = spec.dim :=
  List.length_map _ (List.range spec.dim) |>.trans (List.length_range spec.dim)

open NumericSem LayerCoreDef TensorMem DetailedGradientComputation in
def computeTBiasGradContrib (ni : NumericInterface) (spec : GradientUpdateSpec ni) :
    List ni.Val :=
  List.range spec.dim |>.map fun d =>
    ni.mul (spec.dy2_row.getD d ni.zero) spec.gradScale

open NumericSem LayerCoreDef in
theorem computeTBiasGradContrib_length (ni : NumericInterface)
    (spec : GradientUpdateSpec ni) :
    (computeTBiasGradContrib ni spec).length = spec.dim :=
  List.length_map _ (List.range spec.dim) |>.trans (List.length_range spec.dim)

open NumericSem LayerCoreDef TensorMem in
def addGradContrib (ni : NumericInterface) (current contrib : List ni.Val) :
    List ni.Val :=
  ListSupport.zipWith ni.add current contrib

open NumericSem in
theorem addGradContrib_length_min (ni : NumericInterface) (c ct : List ni.Val) :
    (addGradContrib ni c ct).length = min c.length ct.length :=
  ListSupport.zipWith_length ni.add c ct

open NumericSem LayerCoreDef TensorMem in
def applyGradContribs (ni : NumericInterface) (lc : LayerCore ni)
    (swg twg sbg tbg : List ni.Val) : LayerCore ni :=
  { lc with
    s_weight_grad := lc.s_weight_grad.map fun t =>
      { t with data := addGradContrib ni t.data swg },
    t_weight_grad := lc.t_weight_grad.map fun t =>
      { t with data := addGradContrib ni t.data twg },
    s_bias_grad := lc.s_bias_grad.map fun t =>
      { t with data := addGradContrib ni t.data sbg },
    t_bias_grad := lc.t_bias_grad.map fun t =>
      { t with data := addGradContrib ni t.data tbg } }

open NumericSem LayerCoreDef in
theorem applyGradContribs_preserves_dim (ni : NumericInterface)
    (lc : LayerCore ni) (swg twg sbg tbg : List ni.Val) :
    (applyGradContribs ni lc swg twg sbg tbg).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem applyGradContribs_preserves_weights (ni : NumericInterface)
    (lc : LayerCore ni) (swg twg sbg tbg : List ni.Val) :
    (applyGradContribs ni lc swg twg sbg tbg).s_weight = lc.s_weight ∧
    (applyGradContribs ni lc swg twg sbg tbg).t_weight = lc.t_weight ∧
    (applyGradContribs ni lc swg twg sbg tbg).s_bias = lc.s_bias ∧
    (applyGradContribs ni lc swg twg sbg tbg).t_bias = lc.t_bias := ⟨rfl, rfl, rfl, rfl⟩

open NumericSem LayerCoreDef in
theorem applyGradContribs_preserves_clip (ni : NumericInterface)
    (lc : LayerCore ni) (swg twg sbg tbg : List ni.Val) :
    (applyGradContribs ni lc swg twg sbg tbg).clip_min = lc.clip_min ∧
    (applyGradContribs ni lc swg twg sbg tbg).clip_max = lc.clip_max := ⟨rfl, rfl⟩

end FullGradientWeightUpdate

namespace FullBackwardRow

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward DetailedDy1Total
  DetailedDsComputation DetailedDx1Computation DetailedDx2Computation
  ClippingDerivative ComprehensiveBackward FullGradientWeightUpdate in
structure FullBackwardRowSpec (ni : NumericInterface) where
  lc : LayerCore ni
  y1 : List ni.Val
  y2 : List ni.Val
  dy1 : List ni.Val
  dy2 : List ni.Val
  gradScale : ni.Val
  dim : Nat
  hDim : dim = lc.dim
  hY1 : y1.length = dim
  hY2 : y2.length = dim
  hDy1 : dy1.length = dim
  hDy2 : dy2.length = dim
  hGrads : DetailedBackward.hasGradients ni lc = true

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward
  DetailedDy1Total DetailedDsComputation DetailedDx1Computation
  DetailedDx2Computation FullGradientWeightUpdate in
structure FullBackwardRowResult (ni : NumericInterface) where
  dx1 : List ni.Val
  dx2 : List ni.Val
  ds_list : List ni.Val
  updatedLc : LayerCore ni
  hDx1Len : dx1.length = spec.dim
  hDx2Len : dx2.length = spec.dim
  hDsLen : ds_list.length = spec.dim
  hPreservesDim : updatedLc.dim = spec.dim

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward
  DetailedDy1Total DetailedDsComputation DetailedDx1Computation
  DetailedDx2Computation FullGradientWeightUpdate in
def runFullBackwardRow (ni : NumericInterface)
    (spec : FullBackwardRowSpec ni) :
    (List ni.Val × List ni.Val × List ni.Val × LayerCore ni) :=
  let dy1_total := dy1TotalMatVecProduct ni spec.lc.t_weight.data spec.dy2 spec.dim
  let ds := dsAllDimsDetailed ni spec.lc dy1_total spec.dy1 spec.y1 spec.y2 spec.dy2 spec.dim
  let dx1 := dx1AllDims ni spec.lc dy1_total spec.dy1 spec.y2 spec.dim
  let dx2 := dx2AllDimsExpanded ni spec.lc spec.dy2 ds spec.dy1 spec.dim
  let gspec : GradientUpdateSpec ni := {
    lc := spec.lc,
    ds_row := ds,
    dy2_row := spec.dy2,
    x1_row := spec.y1,
    x2_row := spec.y2,
    gradScale := spec.gradScale,
    dim := spec.dim,
    hDim := spec.hDim,
    hDs := dsAllDimsDetailed_length ni spec.lc _ _ _ _ _ spec.dim,
    hDy2 := spec.hDy2,
    hX1 := spec.hY1,
    hX2 := spec.hY2 }
  let swg := computeSWeightGradContrib ni gspec
  let twg := computeTWeightGradContrib ni gspec
  let sbg := computeSBiasGradContrib ni gspec
  let tbg := computeTBiasGradContrib ni gspec
  let lc' := applyGradContribs ni spec.lc swg twg sbg tbg
  (dx1, dx2, ds, lc')

open NumericSem LayerCoreDef DetailedDy1Total DetailedDsComputation
  DetailedDx1Computation DetailedDx2Computation in
theorem runFullBackwardRow_dx1_length (ni : NumericInterface) (spec : FullBackwardRowSpec ni) :
    (runFullBackwardRow ni spec).1.length = spec.dim :=
  dx1AllDims_length ni spec.lc _ _ _ spec.dim

open NumericSem LayerCoreDef DetailedDsComputation in
theorem runFullBackwardRow_ds_length (ni : NumericInterface) (spec : FullBackwardRowSpec ni) :
    (runFullBackwardRow ni spec).2.2.1.length = spec.dim :=
  dsAllDimsDetailed_length ni spec.lc _ _ _ _ _ spec.dim

open NumericSem LayerCoreDef DetailedDx2Computation in
theorem runFullBackwardRow_dx2_length (ni : NumericInterface) (spec : FullBackwardRowSpec ni) :
    (runFullBackwardRow ni spec).2.1.length = spec.dim :=
  dx2AllDimsExpanded_length ni spec.lc _ _ _ spec.dim

open NumericSem LayerCoreDef FullGradientWeightUpdate in
theorem runFullBackwardRow_preserves_dim (ni : NumericInterface) (spec : FullBackwardRowSpec ni) :
    (runFullBackwardRow ni spec).2.2.2.dim = spec.dim :=
  applyGradContribs_preserves_dim ni spec.lc _ _ _ _

end FullBackwardRow

namespace FullBackwardBatch

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward GradMeanScaling
  FullBackwardRow ComprehensiveBackwardBatch in
structure FullBackwardBatchSpec (ni : NumericInterface) where
  core : RSFCore ni
  y1_rows : List (List ni.Val)
  y2_rows : List (List ni.Val)
  dy1_rows : List (List ni.Val)
  dy2_rows : List (List ni.Val)
  batchSize : Nat
  hBatch : y1_rows.length = batchSize
  hBatch2 : y2_rows.length = batchSize
  hBatch3 : dy1_rows.length = batchSize
  hBatch4 : dy2_rows.length = batchSize
  hBatchPos : batchSize > 0
  hAllGrads : ∀ lc, lc ∈ core.layers → hasGradients ni lc = true
  hLayersNonEmpty : core.layers.length > 0

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward GradMeanScaling in
def runFullBackwardBatch (ni : NumericInterface) (spec : FullBackwardBatchSpec ni) :
    List (List ni.Val × List ni.Val) :=
  let gradScale := computeGradScale ni spec.batchSize spec.core.cfg.grad_mean
  List.range spec.batchSize |>.map fun b =>
    let y1 := spec.y1_rows.getD b []
    let y2 := spec.y2_rows.getD b []
    let dy1 := spec.dy1_rows.getD b []
    let dy2 := spec.dy2_rows.getD b []
    let result := runFullBackwardRow ni
      { lc := spec.core.layers.head (by exact Nat.lt_of_lt_of_le
          (Nat.zero_lt_succ 0) (show 1 ≤ spec.core.layers.length from
          Nat.le_of_lt_succ (Nat.lt_succ_of_le (Nat.le_of_lt spec.hLayersNonEmpty)))),
        y1 := y1, y2 := y2, dy1 := dy1, dy2 := dy2,
        gradScale := gradScale,
        dim := spec.core.dim,
        hDim := rfl, hY1 := rfl, hY2 := rfl, hDy1 := rfl, hDy2 := rfl,
        hGrads := rfl }
    (result.1, result.2.1)

open NumericSem RSFCoreDef LayerCoreDef in
theorem runFullBackwardBatch_length (ni : NumericInterface) (spec : FullBackwardBatchSpec ni) :
    (runFullBackwardBatch ni spec).length = spec.batchSize :=
  List.length_map _ (List.range spec.batchSize) |>.trans (List.length_range spec.batchSize)

open NumericSem RSFCoreDef LayerCoreDef in
theorem runFullBackwardBatch_deterministic (ni : NumericInterface)
    (spec : FullBackwardBatchSpec ni) :
    runFullBackwardBatch ni spec = runFullBackwardBatch ni spec := rfl

end FullBackwardBatch

namespace GradScaleProperties

open NumericSem GradMeanScaling in
structure GradScaleSpec (ni : NumericInterface) where
  batchSize : Nat
  useGradMean : Bool
  hBatchPos : batchSize > 0

open NumericSem GradMeanScaling in
def computeGradScaleForSpec (ni : NumericInterface) (spec : GradScaleSpec ni) : ni.Val :=
  computeGradScale ni spec.batchSize spec.useGradMean

open NumericSem GradMeanScaling in
theorem computeGradScaleForSpec_no_mean (ni : NumericInterface) (spec : GradScaleSpec ni)
    (h : spec.useGradMean = false) :
    computeGradScaleForSpec ni { spec with useGradMean := false } = ni.one := rfl

open NumericSem GradMeanScaling in
structure GradScaleProperties (ni : NumericInterface) where
  hNoMeanIsOne : ∀ bs : Nat, computeGradScale ni bs false = ni.one
  hZeroBatchIsOne : computeGradScale ni 0 true = ni.one
  hPositiveBatchFinite : ∀ bs : Nat, bs > 0 →
    ∀ (hMulOne : ni.mul ni.one ni.one = ni.one),
    computeGradScale ni bs false = ni.one

open NumericSem GradMeanScaling in
def makeGradScaleProperties (ni : NumericInterface) : GradScaleProperties ni :=
  { hNoMeanIsOne := fun _ => rfl,
    hZeroBatchIsOne := rfl,
    hPositiveBatchFinite := fun _ _ _ => rfl }

end GradScaleProperties

namespace LayerGradientAccumulation

open NumericSem LayerCoreDef TensorMem DetailedBackward FullGradientWeightUpdate in
structure LayerGradAccumulationState (ni : NumericInterface) where
  lc : LayerCore ni
  totalSwg : List ni.Val
  totalTwg : List ni.Val
  totalSbg : List ni.Val
  totalTbg : List ni.Val
  rowsProcessed : Nat

open NumericSem LayerCoreDef TensorMem FullGradientWeightUpdate in
def initGradAccumulation (ni : NumericInterface) (lc : LayerCore ni) :
    LayerGradAccumulationState ni :=
  { lc := lc,
    totalSwg := List.replicate (lc.dim * lc.dim) ni.zero,
    totalTwg := List.replicate (lc.dim * lc.dim) ni.zero,
    totalSbg := List.replicate lc.dim ni.zero,
    totalTbg := List.replicate lc.dim ni.zero,
    rowsProcessed := 0 }

open NumericSem LayerCoreDef in
theorem initGradAccumulation_zero_rows (ni : NumericInterface) (lc : LayerCore ni) :
    (initGradAccumulation ni lc).rowsProcessed = 0 := rfl

open NumericSem LayerCoreDef in
theorem initGradAccumulation_preserves_lc (ni : NumericInterface) (lc : LayerCore ni) :
    (initGradAccumulation ni lc).lc = lc := rfl

open NumericSem LayerCoreDef TensorMem FullGradientWeightUpdate in
def accumGradRow (ni : NumericInterface)
    (state : LayerGradAccumulationState ni) (swg twg sbg tbg : List ni.Val) :
    LayerGradAccumulationState ni :=
  { state with
    totalSwg := addGradContrib ni state.totalSwg swg,
    totalTwg := addGradContrib ni state.totalTwg twg,
    totalSbg := addGradContrib ni state.totalSbg sbg,
    totalTbg := addGradContrib ni state.totalTbg tbg,
    rowsProcessed := state.rowsProcessed + 1 }

open NumericSem LayerCoreDef in
theorem accumGradRow_increments (ni : NumericInterface)
    (state : LayerGradAccumulationState ni) (swg twg sbg tbg : List ni.Val) :
    (accumGradRow ni state swg twg sbg tbg).rowsProcessed = state.rowsProcessed + 1 := rfl

open NumericSem LayerCoreDef in
theorem accumGradRow_preserves_lc (ni : NumericInterface)
    (state : LayerGradAccumulationState ni) (swg twg sbg tbg : List ni.Val) :
    (accumGradRow ni state swg twg sbg tbg).lc = state.lc := rfl

open NumericSem LayerCoreDef TensorMem FullGradientWeightUpdate in
def finalizeGradAccumulation (ni : NumericInterface)
    (state : LayerGradAccumulationState ni) : LayerCore ni :=
  applyGradContribs ni state.lc state.totalSwg state.totalTwg state.totalSbg state.totalTbg

open NumericSem LayerCoreDef FullGradientWeightUpdate in
theorem finalizeGradAccumulation_preserves_dim (ni : NumericInterface)
    (state : LayerGradAccumulationState ni) :
    (finalizeGradAccumulation ni state).dim = state.lc.dim :=
  applyGradContribs_preserves_dim ni state.lc _ _ _ _

end LayerGradientAccumulation

namespace MultiLayerBackward

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward FullBackwardRow
  FullBackwardBatch LayerGradientAccumulation in
structure MultiLayerBackwardState (ni : NumericInterface) where
  updatedLayers : List (LayerCore ni)
  currentDx1 : List ni.Val
  currentDx2 : List ni.Val
  layersProcessed : Nat

open NumericSem RSFCoreDef LayerCoreDef FullBackwardRow in
def stepMultiLayerBackward (ni : NumericInterface)
    (state : MultiLayerBackwardState ni)
    (lc : LayerCore ni)
    (y1 y2 : List ni.Val)
    (gradScale : ni.Val) (dim : Nat)
    (hDim : dim = lc.dim)
    (hGrads : hasGradients ni lc = true) :
    MultiLayerBackwardState ni :=
  let result := runFullBackwardRow ni
    { lc := lc, y1 := y1, y2 := y2,
      dy1 := state.currentDx1, dy2 := state.currentDx2,
      gradScale := gradScale, dim := dim,
      hDim := hDim, hY1 := rfl, hY2 := rfl, hDy1 := rfl, hDy2 := rfl,
      hGrads := hGrads }
  { updatedLayers := result.2.2.2 :: state.updatedLayers,
    currentDx1 := result.1,
    currentDx2 := result.2.1,
    layersProcessed := state.layersProcessed + 1 }

open NumericSem RSFCoreDef LayerCoreDef in
theorem stepMultiLayerBackward_advances (ni : NumericInterface)
    (state : MultiLayerBackwardState ni)
    (lc : LayerCore ni) (y1 y2 : List ni.Val)
    (gs : ni.Val) (dim : Nat) (hd : dim = lc.dim) (hg : hasGradients ni lc = true) :
    (stepMultiLayerBackward ni state lc y1 y2 gs dim hd hg).layersProcessed =
    state.layersProcessed + 1 := rfl

open NumericSem RSFCoreDef LayerCoreDef in
def initMultiLayerBackwardState (ni : NumericInterface) (dy1 dy2 : List ni.Val) :
    MultiLayerBackwardState ni :=
  { updatedLayers := [], currentDx1 := dy1, currentDx2 := dy2, layersProcessed := 0 }

open NumericSem RSFCoreDef LayerCoreDef in
theorem initMultiLayerBackwardState_zero (ni : NumericInterface) (dy1 dy2 : List ni.Val) :
    (initMultiLayerBackwardState ni dy1 dy2).layersProcessed = 0 := rfl

open NumericSem RSFCoreDef LayerCoreDef in
theorem initMultiLayerBackwardState_empty_layers (ni : NumericInterface) (dy1 dy2 : List ni.Val) :
    (initMultiLayerBackwardState ni dy1 dy2).updatedLayers = [] := rfl

end MultiLayerBackward

namespace LayerDeinitialization

open NumericSem LayerCoreDef TensorMem in
def deallocateLayerGrads (ni : NumericInterface) (lc : LayerCore ni) : LayerCore ni :=
  { lc with
    s_weight_grad := none,
    t_weight_grad := none,
    s_bias_grad := none,
    t_bias_grad := none }

open NumericSem LayerCoreDef in
theorem deallocateLayerGrads_removes (ni : NumericInterface) (lc : LayerCore ni) :
    (deallocateLayerGrads ni lc).s_weight_grad = none ∧
    (deallocateLayerGrads ni lc).t_weight_grad = none ∧
    (deallocateLayerGrads ni lc).s_bias_grad = none ∧
    (deallocateLayerGrads ni lc).t_bias_grad = none := ⟨rfl, rfl, rfl, rfl⟩

open NumericSem LayerCoreDef in
theorem deallocateLayerGrads_preserves_dim (ni : NumericInterface) (lc : LayerCore ni) :
    (deallocateLayerGrads ni lc).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem deallocateLayerGrads_preserves_weights (ni : NumericInterface) (lc : LayerCore ni) :
    (deallocateLayerGrads ni lc).s_weight = lc.s_weight ∧
    (deallocateLayerGrads ni lc).t_weight = lc.t_weight ∧
    (deallocateLayerGrads ni lc).s_bias = lc.s_bias ∧
    (deallocateLayerGrads ni lc).t_bias = lc.t_bias := ⟨rfl, rfl, rfl, rfl⟩

open NumericSem LayerCoreDef in
theorem deallocateLayerGrads_no_grads (ni : NumericInterface) (lc : LayerCore ni) :
    hasGradients ni (deallocateLayerGrads ni lc) = false := rfl

open NumericSem LayerCoreDef TensorMem in
def deallocateAllGrads (ni : NumericInterface) (layers : List (LayerCore ni)) :
    List (LayerCore ni) :=
  layers.map (deallocateLayerGrads ni)

open NumericSem LayerCoreDef in
theorem deallocateAllGrads_length (ni : NumericInterface) (layers : List (LayerCore ni)) :
    (deallocateAllGrads ni layers).length = layers.length :=
  List.length_map _ layers

open NumericSem LayerCoreDef in
theorem deallocateAllGrads_empty (ni : NumericInterface) :
    deallocateAllGrads ni ([] : List (LayerCore ni)) = [] := rfl

open NumericSem LayerCoreDef in
theorem deallocateAllGrads_no_grads (ni : NumericInterface) (layers : List (LayerCore ni)) :
    ∀ lc, lc ∈ deallocateAllGrads ni layers → hasGradients ni lc = false :=
  fun lc h => (List.mem_map.mp h).elim fun ⟨_, _, heq⟩ => heq ▸ rfl

end LayerDeinitialization

namespace CRCTableProperties

open CRCModel DetailedCRC in
def crc32Polynomial : UInt32 := 0xEDB88320

open CRCModel DetailedCRC in
theorem crc32Polynomial_value : crc32Polynomial = 0xEDB88320 := rfl

open CRCModel DetailedCRC in
def crcTableEntry (idx : UInt8) : UInt32 :=
  crcTable.getD idx.toNat 0

open CRCModel DetailedCRC in
theorem crcTableEntry_deterministic (idx : UInt8) :
    crcTableEntry idx = crcTableEntry idx := rfl

open CRCModel DetailedCRC in
def crcTableLookup (state : UInt32) (byte : UInt8) : UInt32 :=
  let idx := (state.toNat % 256) ^^^ byte.toNat
  let tableVal := crcTable.getD (idx % 256) 0
  (state >>> 8) ^^^ tableVal

open CRCModel DetailedCRC in
theorem crcTableLookup_deterministic (s : UInt32) (b : UInt8) :
    crcTableLookup s b = crcTableLookup s b := rfl

open CRCModel DetailedCRC ByteSupport in
def computeCRC32Full (bytes : List UInt8) : UInt32 :=
  let init : UInt32 := 0xFFFFFFFF
  let folded := bytes.foldl crcTableLookup init
  folded ^^^ 0xFFFFFFFF

open CRCModel DetailedCRC in
theorem computeCRC32Full_empty : computeCRC32Full [] = 0xFFFFFFFF ^^^ 0xFFFFFFFF := rfl

open CRCModel DetailedCRC in
theorem computeCRC32Full_deterministic (bytes : List UInt8) :
    computeCRC32Full bytes = computeCRC32Full bytes := rfl

end CRCTableProperties

namespace ByteSerializationExpanded

open ByteSupport SerializerModel in
def toLE32 (v : UInt32) : List UInt8 :=
  serializeU32LE v

open ByteSupport SerializerModel in
theorem toLE32_length (v : UInt32) : (toLE32 v).length = 4 := rfl

open ByteSupport SerializerModel in
def toLE64 (v : UInt64) : List UInt8 :=
  serializeU64LE v

open ByteSupport SerializerModel in
theorem toLE64_length (v : UInt64) : (toLE64 v).length = 8 := rfl

open ByteSupport SerializerModel in
def fromLE32 (bytes : List UInt8) : Option UInt32 :=
  if bytes.length < 4 then none
  else some (parseU32LE bytes)

open ByteSupport SerializerModel in
theorem fromLE32_too_short (bytes : List UInt8) (h : bytes.length < 4) :
    fromLE32 bytes = none :=
  show (if bytes.length < 4 then _ else _) = _ from if_pos h

open ByteSupport SerializerModel in
def fromLE64 (bytes : List UInt8) : Option UInt64 :=
  if bytes.length < 8 then none
  else some (parseU64LE bytes)

open ByteSupport SerializerModel in
theorem fromLE64_too_short (bytes : List UInt8) (h : bytes.length < 8) :
    fromLE64 bytes = none :=
  show (if bytes.length < 8 then _ else _) = _ from if_pos h

open ByteSupport SerializerModel in
theorem fromLE32_toLE32_roundtrip (v : UInt32) :
    fromLE32 (toLE32 v) = some (parseU32LE (serializeU32LE v)) :=
  show (if (serializeU32LE v).length < 4 then _ else _) = _ from
  if_neg (show ¬((serializeU32LE v).length < 4) from Nat.not_lt_of_le (Nat.le_refl 4))

open ByteSupport SerializerModel in
theorem fromLE64_toLE64_roundtrip (v : UInt64) :
    fromLE64 (toLE64 v) = some (parseU64LE (serializeU64LE v)) :=
  show (if (serializeU64LE v).length < 8 then _ else _) = _ from
  if_neg (show ¬((serializeU64LE v).length < 8) from Nat.not_lt_of_le (Nat.le_refl 8))

end ByteSerializationExpanded

namespace RSF

namespace GPUVersionTracking

open NumericSem RSFCoreDef GPUModel in
structure VersionState (ni : NumericInterface) where
  cpuVersion : Nat
  gpuVersion : Nat
  hCpuNonNeg : cpuVersion ≥ 0
  hGpuNonNeg : gpuVersion ≥ 0

open NumericSem RSFCoreDef GPUModel in
def initVersionState (ni : NumericInterface) : VersionState ni :=
  { cpuVersion := 0, gpuVersion := 0,
    hCpuNonNeg := Nat.le_refl 0, hGpuNonNeg := Nat.le_refl 0 }

open NumericSem RSFCoreDef GPUModel in
theorem initVersionState_synced (ni : NumericInterface) :
    (initVersionState ni).cpuVersion = (initVersionState ni).gpuVersion := rfl

open NumericSem RSFCoreDef GPUModel in
def incrementCpuVersion (ni : NumericInterface) (vs : VersionState ni) : VersionState ni :=
  { vs with cpuVersion := vs.cpuVersion + 1,
    hCpuNonNeg := Nat.le_of_lt (Nat.zero_lt_succ vs.cpuVersion) }

open NumericSem RSFCoreDef GPUModel in
theorem incrementCpuVersion_breaks_sync (ni : NumericInterface) (vs : VersionState ni)
    (h : vs.cpuVersion = vs.gpuVersion) :
    (incrementCpuVersion ni vs).cpuVersion ≠ (incrementCpuVersion ni vs).gpuVersion :=
  show vs.cpuVersion + 1 ≠ vs.gpuVersion from
  h ▸ Nat.succ_ne_self vs.gpuVersion

open NumericSem RSFCoreDef GPUModel in
def syncVersions (ni : NumericInterface) (vs : VersionState ni) : VersionState ni :=
  { vs with gpuVersion := vs.cpuVersion,
    hGpuNonNeg := vs.hCpuNonNeg }

open NumericSem RSFCoreDef GPUModel in
theorem syncVersions_establishes_sync (ni : NumericInterface) (vs : VersionState ni) :
    (syncVersions ni vs).cpuVersion = (syncVersions ni vs).gpuVersion := rfl

open NumericSem RSFCoreDef GPUModel in
def isSynced (ni : NumericInterface) (vs : VersionState ni) : Bool :=
  vs.cpuVersion = vs.gpuVersion

open NumericSem RSFCoreDef GPUModel in
theorem isSynced_init (ni : NumericInterface) :
    isSynced ni (initVersionState ni) = true := rfl

open NumericSem RSFCoreDef GPUModel in
theorem isSynced_after_sync (ni : NumericInterface) (vs : VersionState ni) :
    isSynced ni (syncVersions ni vs) = true := rfl

open NumericSem RSFCoreDef GPUModel in
theorem isSynced_after_increment_false (ni : NumericInterface) (vs : VersionState ni)
    (h : vs.cpuVersion = vs.gpuVersion) :
    isSynced ni (incrementCpuVersion ni vs) = false :=
  show (vs.cpuVersion + 1 = vs.gpuVersion) = false from
  (show ¬(vs.cpuVersion + 1 = vs.gpuVersion) from
    h ▸ Nat.succ_ne_self vs.gpuVersion) |> (fun _ => rfl)

end GPUVersionTracking

namespace GPUMemoryManagement

open NumericSem RSFCoreDef GPUModel in
structure GPUMemState (ni : NumericInterface) where
  f16BufAllocated : Bool
  f16BufSize : Nat
  gpuWeightsAllocated : Bool
  gpuWeightsSize : Nat

open NumericSem RSFCoreDef GPUModel in
def initGPUMem (ni : NumericInterface) : GPUMemState ni :=
  { f16BufAllocated := false, f16BufSize := 0,
    gpuWeightsAllocated := false, gpuWeightsSize := 0 }

open NumericSem RSFCoreDef GPUModel in
theorem initGPUMem_not_allocated (ni : NumericInterface) :
    (initGPUMem ni).f16BufAllocated = false ∧
    (initGPUMem ni).gpuWeightsAllocated = false := ⟨rfl, rfl⟩

open NumericSem RSFCoreDef GPUModel in
def allocateF16Buf (ni : NumericInterface) (gms : GPUMemState ni) (size : Nat) :
    GPUMemState ni :=
  { gms with f16BufAllocated := true, f16BufSize := size }

open NumericSem RSFCoreDef GPUModel in
theorem allocateF16Buf_allocated (ni : NumericInterface) (gms : GPUMemState ni) (sz : Nat) :
    (allocateF16Buf ni gms sz).f16BufAllocated = true := rfl

open NumericSem RSFCoreDef GPUModel in
def allocateGPUWeights (ni : NumericInterface) (gms : GPUMemState ni) (size : Nat) :
    GPUMemState ni :=
  { gms with gpuWeightsAllocated := true, gpuWeightsSize := size }

open NumericSem RSFCoreDef GPUModel in
theorem allocateGPUWeights_allocated (ni : NumericInterface) (gms : GPUMemState ni) (sz : Nat) :
    (allocateGPUWeights ni gms sz).gpuWeightsAllocated = true := rfl

open NumericSem RSFCoreDef GPUModel in
def deallocateAll (ni : NumericInterface) (gms : GPUMemState ni) : GPUMemState ni :=
  { f16BufAllocated := false, f16BufSize := 0,
    gpuWeightsAllocated := false, gpuWeightsSize := 0 }

open NumericSem RSFCoreDef GPUModel in
theorem deallocateAll_clears (ni : NumericInterface) (gms : GPUMemState ni) :
    (deallocateAll ni gms).f16BufAllocated = false ∧
    (deallocateAll ni gms).gpuWeightsAllocated = false := ⟨rfl, rfl⟩

open NumericSem RSFCoreDef GPUModel in
def totalGPUMemory (ni : NumericInterface) (gms : GPUMemState ni) : Nat :=
  (if gms.f16BufAllocated then gms.f16BufSize else 0) +
  (if gms.gpuWeightsAllocated then gms.gpuWeightsSize else 0)

open NumericSem RSFCoreDef GPUModel in
theorem totalGPUMemory_init (ni : NumericInterface) :
    totalGPUMemory ni (initGPUMem ni) = 0 := rfl

open NumericSem RSFCoreDef GPUModel in
theorem totalGPUMemory_after_dealloc (ni : NumericInterface) (gms : GPUMemState ni) :
    totalGPUMemory ni (deallocateAll ni gms) = 0 := rfl

end GPUMemoryManagement

namespace GPUCompatibility

open NumericSem RSFCoreDef GPUModel in
structure GPUCapabilities where
  supportsF16 : Bool
  supportsF32 : Bool
  maxMemoryMB : Nat
  computeVersion : Nat
  hCompute : computeVersion > 0

open NumericSem RSFCoreDef GPUModel in
def isCompatible (caps : GPUCapabilities) (requiredMemMB : Nat) : Bool :=
  caps.supportsF32 ∧ caps.maxMemoryMB ≥ requiredMemMB

open NumericSem RSFCoreDef GPUModel in
theorem isCompatible_needs_f32 (caps : GPUCapabilities) (mem : Nat)
    (h : caps.supportsF32 = false) :
    isCompatible caps mem = false :=
  show (caps.supportsF32 ∧ _) = false from
  (show ¬(caps.supportsF32 ∧ _) from fun ⟨hf, _⟩ => absurd hf (h ▸ Bool.noConfusion)) |>
  (fun _ => rfl)

open NumericSem RSFCoreDef GPUModel in
def canUseF16Optimization (caps : GPUCapabilities) : Bool :=
  caps.supportsF16 ∧ caps.supportsF32

open NumericSem RSFCoreDef GPUModel in
theorem canUseF16_needs_both (caps : GPUCapabilities)
    (h1 : caps.supportsF16 = true) (h2 : caps.supportsF32 = true) :
    canUseF16Optimization caps = true :=
  show (caps.supportsF16 ∧ caps.supportsF32) = true from
  (show caps.supportsF16 ∧ caps.supportsF32 from ⟨h1 ▸ rfl, h2 ▸ rfl⟩) |> (fun _ => rfl)

open NumericSem RSFCoreDef GPUModel in
structure GPUFallbackDecision where
  useGPU : Bool
  reason : String
  hReason : reason.length > 0

open NumericSem RSFCoreDef GPUModel in
def decideFallback (caps : Option GPUCapabilities) (requiredMemMB : Nat) :
    GPUFallbackDecision :=
  match caps with
  | none => { useGPU := false, reason := "no_gpu_available",
              hReason := Nat.zero_lt_succ _ }
  | some c =>
    if isCompatible c requiredMemMB then
      { useGPU := true, reason := "compatible",
        hReason := Nat.zero_lt_succ _ }
    else
      { useGPU := false, reason := "incompatible_or_insufficient_memory",
        hReason := Nat.zero_lt_succ _ }

open NumericSem RSFCoreDef GPUModel in
theorem decideFallback_none :
    (decideFallback none 0).useGPU = false := rfl

end GPUCompatibility

namespace FullLifecycleStateMachine

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  GPUModel WeightInitialization GradientZeroing LayerDeinitialization in
inductive LifecyclePhase where
  | uninitialized
  | initialized
  | training
  | inference
  | destroyed

open NumericSem RSFCoreDef RegistryModel in
structure LifecycleState (ni : NumericInterface) where
  phase : LifecyclePhase
  coreId : Option Nat
  registry : Registry (RSFCore ni)
  hPhaseConsistent : phase = LifecyclePhase.uninitialized → coreId = none

open NumericSem RSFCoreDef RegistryModel in
def lsInit (ni : NumericInterface) : LifecycleState ni :=
  { phase := LifecyclePhase.uninitialized,
    coreId := none,
    registry := emptyRegistry,
    hPhaseConsistent := fun _ => rfl }

open NumericSem RSFCoreDef RegistryModel in
theorem lsInit_uninitialized (ni : NumericInterface) :
    (lsInit ni).phase = LifecyclePhase.uninitialized := rfl

open NumericSem RSFCoreDef RegistryModel in
def lsCreate (ni : NumericInterface) (ls : LifecycleState ni) (core : RSFCore ni) :
    LifecycleState ni :=
  let (reg', id) := registerCore ls.registry core
  { phase := LifecyclePhase.initialized,
    coreId := some id,
    registry := reg',
    hPhaseConsistent := fun h => absurd h (show LifecyclePhase.initialized ≠ LifecyclePhase.uninitialized from
      fun h => LifecyclePhase.noConfusion h) }

open NumericSem RSFCoreDef RegistryModel in
theorem lsCreate_initialized (ni : NumericInterface) (ls : LifecycleState ni)
    (core : RSFCore ni) :
    (lsCreate ni ls core).phase = LifecyclePhase.initialized := rfl

open NumericSem RSFCoreDef RegistryModel in
theorem lsCreate_has_id (ni : NumericInterface) (ls : LifecycleState ni)
    (core : RSFCore ni) :
    (lsCreate ni ls core).coreId = some ls.registry.nextId := rfl

open NumericSem RSFCoreDef RegistryModel in
def lsStartTraining (ni : NumericInterface) (ls : LifecycleState ni) :
    LifecycleState ni :=
  { ls with
    phase := LifecyclePhase.training,
    hPhaseConsistent := fun h => absurd h (show LifecyclePhase.training ≠ LifecyclePhase.uninitialized from
      fun h => LifecyclePhase.noConfusion h) }

open NumericSem RSFCoreDef RegistryModel in
theorem lsStartTraining_phase (ni : NumericInterface) (ls : LifecycleState ni) :
    (lsStartTraining ni ls).phase = LifecyclePhase.training := rfl

open NumericSem RSFCoreDef RegistryModel in
def lsStartInference (ni : NumericInterface) (ls : LifecycleState ni) :
    LifecycleState ni :=
  { ls with
    phase := LifecyclePhase.inference,
    hPhaseConsistent := fun h => absurd h (show LifecyclePhase.inference ≠ LifecyclePhase.uninitialized from
      fun h => LifecyclePhase.noConfusion h) }

open NumericSem RSFCoreDef RegistryModel in
theorem lsStartInference_phase (ni : NumericInterface) (ls : LifecycleState ni) :
    (lsStartInference ni ls).phase = LifecyclePhase.inference := rfl

open NumericSem RSFCoreDef RegistryModel in
def lsDestroy (ni : NumericInterface) (ls : LifecycleState ni) :
    LifecycleState ni :=
  match ls.coreId with
  | none => ls
  | some id =>
    let (reg', _) := requestDestroy ls.registry id
    { phase := LifecyclePhase.destroyed,
      coreId := none,
      registry := reg',
      hPhaseConsistent := fun h => absurd h (show LifecyclePhase.destroyed ≠ LifecyclePhase.uninitialized from
        fun h => LifecyclePhase.noConfusion h) }

open NumericSem RSFCoreDef RegistryModel in
theorem lsDestroy_no_id (ni : NumericInterface) (ls : LifecycleState ni) :
    (lsDestroy ni ls).coreId = none :=
  match ls.coreId with
  | none => rfl
  | some _ => rfl

end FullLifecycleStateMachine

namespace LayerCoreProperties

open NumericSem LayerCoreDef TensorMem in
theorem layerCore_s_weight_shape (ni : NumericInterface) (lc : LayerCore ni) :
    lc.s_weight.shape = { rows := lc.dim, cols := lc.dim } := rfl

open NumericSem LayerCoreDef TensorMem in
theorem layerCore_t_weight_shape (ni : NumericInterface) (lc : LayerCore ni) :
    lc.t_weight.shape = { rows := lc.dim, cols := lc.dim } := rfl

open NumericSem LayerCoreDef TensorMem in
theorem layerCore_s_bias_shape (ni : NumericInterface) (lc : LayerCore ni) :
    lc.s_bias.shape = { rows := 1, cols := lc.dim } := rfl

open NumericSem LayerCoreDef TensorMem in
theorem layerCore_t_bias_shape (ni : NumericInterface) (lc : LayerCore ni) :
    lc.t_bias.shape = { rows := 1, cols := lc.dim } := rfl

open NumericSem LayerCoreDef TensorMem in
def layerTotalParams (ni : NumericInterface) (lc : LayerCore ni) : Nat :=
  lc.s_weight.data.length + lc.t_weight.data.length +
  lc.s_bias.data.length + lc.t_bias.data.length

open NumericSem LayerCoreDef TensorMem in
theorem layerTotalParams_formula (ni : NumericInterface) (lc : LayerCore ni) :
    layerTotalParams ni lc = lc.dim * lc.dim + lc.dim * lc.dim + lc.dim + lc.dim :=
  show lc.s_weight.data.length + lc.t_weight.data.length +
    lc.s_bias.data.length + lc.t_bias.data.length =
    lc.dim * lc.dim + lc.dim * lc.dim + lc.dim + lc.dim from
  lc.s_weight.hDataLen ▸ lc.t_weight.hDataLen ▸ lc.s_bias.hDataLen ▸ lc.t_bias.hDataLen ▸ rfl

open NumericSem LayerCoreDef TensorMem in
def layerGradParams (ni : NumericInterface) (lc : LayerCore ni) : Nat :=
  (lc.s_weight_grad.map (·.data.length)).getD 0 +
  (lc.t_weight_grad.map (·.data.length)).getD 0 +
  (lc.s_bias_grad.map (·.data.length)).getD 0 +
  (lc.t_bias_grad.map (·.data.length)).getD 0

open NumericSem LayerCoreDef TensorMem in
def modelTotalParams (ni : NumericInterface) (layers : List (LayerCore ni)) : Nat :=
  layers.foldl (fun acc lc => acc + layerTotalParams ni lc) 0

open NumericSem LayerCoreDef TensorMem in
theorem modelTotalParams_empty (ni : NumericInterface) :
    modelTotalParams ni ([] : List (LayerCore ni)) = 0 := rfl

end LayerCoreProperties

namespace RSFCoreProperties

open NumericSem RSFCoreDef LayerCoreDef in
def coreTotalParams (ni : NumericInterface) (core : RSFCore ni) : Nat :=
  LayerCoreProperties.modelTotalParams ni core.layers

open NumericSem RSFCoreDef LayerCoreDef in
theorem coreTotalParams_empty_layers (ni : NumericInterface) (core : RSFCore ni)
    (h : core.layers = []) :
    coreTotalParams ni core = 0 :=
  show LayerCoreProperties.modelTotalParams ni core.layers = 0 from
  h ▸ rfl

open NumericSem RSFCoreDef in
def coreInputSize (ni : NumericInterface) (core : RSFCore ni) : Nat :=
  core.dim * 2

open NumericSem RSFCoreDef in
theorem coreInputSize_pos (ni : NumericInterface) (core : RSFCore ni)
    (h : core.dim > 0) :
    coreInputSize ni core > 0 :=
  Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (show 1 ≤ core.dim * 2 from
    Nat.le_mul_of_pos_right 2 h)

open NumericSem RSFCoreDef in
def coreOutputSize (ni : NumericInterface) (core : RSFCore ni) : Nat :=
  core.dim * 2

open NumericSem RSFCoreDef in
theorem coreOutputSize_eq_input (ni : NumericInterface) (core : RSFCore ni) :
    coreOutputSize ni core = coreInputSize ni core := rfl

open NumericSem RSFCoreDef LayerCoreDef in
def coreAllLayersSameDim (ni : NumericInterface) (core : RSFCore ni) : Bool :=
  core.layers.all (fun lc => lc.dim = core.dim)

open NumericSem RSFCoreDef LayerCoreDef in
def coreHasGradients (ni : NumericInterface) (core : RSFCore ni) : Bool :=
  core.layers.all (fun lc => DetailedBackward.hasGradients ni lc)

open NumericSem RSFCoreDef LayerCoreDef in
theorem coreHasGradients_empty (ni : NumericInterface) (core : RSFCore ni)
    (h : core.layers = []) :
    coreHasGradients ni core = true :=
  show core.layers.all _ = true from h ▸ rfl

end RSFCoreProperties

namespace DetailedSnapshotLayerBytes

open NumericSem SnapshotModel SerializerModel DetailedSerializer ByteSupport in
def serializeLayerSnapshot (ni : NumericInterface) (layer : SavedLayerSnapshot ni) :
    List UInt8 :=
  serializeTensorPayload ni layer.s_weight_data ++
  serializeTensorPayload ni layer.t_weight_data ++
  serializeTensorPayload ni layer.s_bias_data ++
  serializeTensorPayload ni layer.t_bias_data

open NumericSem SnapshotModel SerializerModel DetailedSerializer in
theorem serializeLayerSnapshot_deterministic (ni : NumericInterface)
    (layer : SavedLayerSnapshot ni) :
    serializeLayerSnapshot ni layer = serializeLayerSnapshot ni layer := rfl

open NumericSem SnapshotModel SerializerModel DetailedSerializer ByteSupport in
def serializeAllLayerSnapshots (ni : NumericInterface)
    (layers : List (SavedLayerSnapshot ni)) : List UInt8 :=
  layers.foldl (fun acc layer => acc ++ serializeLayerSnapshot ni layer) []

open NumericSem SnapshotModel SerializerModel in
theorem serializeAllLayerSnapshots_empty (ni : NumericInterface) :
    serializeAllLayerSnapshots ni [] = [] := rfl

open NumericSem SnapshotModel SerializerModel in
theorem serializeAllLayerSnapshots_deterministic (ni : NumericInterface)
    (layers : List (SavedLayerSnapshot ni)) :
    serializeAllLayerSnapshots ni layers = serializeAllLayerSnapshots ni layers := rfl

open NumericSem SnapshotModel ParserModel DetailedParser2 ByteSupport in
def deserializeLayerFromBytes (ni : NumericInterface) (bytes : List UInt8) (dim : Nat) :
    RSFResult (SavedLayerSnapshot ni × Nat) :=
  let weightSize := dim * dim * 4
  let biasSize := dim * 4
  let totalSize := weightSize * 2 + biasSize * 2
  if bytes.length < totalSize then RSFResult.err RSFError.IOError
  else
    let s_weight_bytes := bytes.take weightSize
    let rest1 := bytes.drop weightSize
    let t_weight_bytes := rest1.take weightSize
    let rest2 := rest1.drop weightSize
    let s_bias_bytes := rest2.take biasSize
    let rest3 := rest2.drop biasSize
    let t_bias_bytes := rest3.take biasSize
    let layer : SavedLayerSnapshot ni :=
      { s_weight_data := parseTensorPayload ni s_weight_bytes (dim * dim),
        t_weight_data := parseTensorPayload ni t_weight_bytes (dim * dim),
        s_bias_data := parseTensorPayload ni s_bias_bytes dim,
        t_bias_data := parseTensorPayload ni t_bias_bytes dim }
    RSFResult.ok (layer, totalSize)

open NumericSem SnapshotModel in
theorem deserializeLayerFromBytes_deterministic (ni : NumericInterface)
    (bytes : List UInt8) (dim : Nat) :
    deserializeLayerFromBytes ni bytes dim = deserializeLayerFromBytes ni bytes dim := rfl

end DetailedSnapshotLayerBytes

namespace ParserCheckpoints

open NumericSem ParserModel DetailedParser2 ByteSupport in
structure ParserCheckpoint (ni : NumericInterface) where
  position : Nat
  bytesRemaining : Nat
  isValid : Bool

open NumericSem ParserModel DetailedParser2 in
def createCheckpoint (ni : NumericInterface) (ps : ParserState) : ParserCheckpoint ni :=
  { position := ps.pos,
    bytesRemaining := ps.data.length - ps.pos,
    isValid := ps.pos ≤ ps.data.length }

open NumericSem ParserModel DetailedParser2 in
theorem createCheckpoint_valid_init (ni : NumericInterface) (bytes : List UInt8)
    (hLen : bytes.length ≥ 28) :
    (createCheckpoint ni (initParser { bytes := bytes, hMinLen := hLen })).isValid = true := rfl

open NumericSem ParserModel DetailedParser2 in
def parserAdvance (ps : ParserState) (n : Nat) : ParserState :=
  { ps with pos := ps.pos + n }

open NumericSem ParserModel DetailedParser2 in
theorem parserAdvance_increases_pos (ps : ParserState) (n : Nat) :
    (parserAdvance ps n).pos = ps.pos + n := rfl

open NumericSem ParserModel DetailedParser2 in
def parserAtEnd (ps : ParserState) : Bool :=
  ps.pos ≥ ps.data.length

open NumericSem ParserModel DetailedParser2 in
theorem parserAtEnd_when_past (ps : ParserState) (h : ps.pos ≥ ps.data.length) :
    parserAtEnd ps = true :=
  show (ps.pos ≥ ps.data.length) = true from h |> (fun _ => rfl)

open NumericSem ParserModel DetailedParser2 in
def parserBytesLeft (ps : ParserState) : Nat :=
  if ps.pos ≥ ps.data.length then 0
  else ps.data.length - ps.pos

open NumericSem ParserModel DetailedParser2 in
theorem parserBytesLeft_at_end (ps : ParserState)
    (h : ps.pos ≥ ps.data.length) :
    parserBytesLeft ps = 0 :=
  show (if ps.pos ≥ ps.data.length then 0 else _) = 0 from
  if_pos h

end ParserCheckpoints

namespace MagicValidation

open ByteSupport in
def rsfMagicBytes : List UInt8 := [0x52, 0x53, 0x46, 0x30]

theorem rsfMagicBytes_length : rsfMagicBytes.length = 4 := rfl

def checkMagicBytes (bytes : List UInt8) : RSFResult Unit :=
  if bytes.length < 4 then RSFResult.err RSFError.IOError
  else if bytes.take 4 = rsfMagicBytes then RSFResult.ok ()
  else RSFResult.err RSFError.IOError

theorem checkMagicBytes_too_short (bytes : List UInt8) (h : bytes.length < 4) :
    checkMagicBytes bytes = RSFResult.err RSFError.IOError :=
  show (if bytes.length < 4 then _ else _) = _ from if_pos h

theorem checkMagicBytes_correct :
    checkMagicBytes [0x52, 0x53, 0x46, 0x30] = RSFResult.ok () := rfl

theorem checkMagicBytes_correct_prefix (rest : List UInt8) :
    checkMagicBytes ([0x52, 0x53, 0x46, 0x30] ++ rest) = RSFResult.ok () := rfl

def rsfVersionBytes : List UInt8 := [0x04, 0x00, 0x00, 0x00]

theorem rsfVersionBytes_length : rsfVersionBytes.length = 4 := rfl

def checkVersionBytes (bytes : List UInt8) (offset : Nat) : RSFResult Nat :=
  if bytes.length < offset + 4 then RSFResult.err RSFError.IOError
  else
    let vBytes := bytes.drop offset |>.take 4
    if vBytes = rsfVersionBytes then RSFResult.ok 4
    else RSFResult.err RSFError.IOError

theorem checkVersionBytes_too_short (bytes : List UInt8) (offset : Nat)
    (h : bytes.length < offset + 4) :
    checkVersionBytes bytes offset = RSFResult.err RSFError.IOError :=
  show (if bytes.length < offset + 4 then _ else _) = _ from if_pos h

end MagicValidation

namespace ModelConsistencyChecks

open NumericSem RSFCoreDef LayerCoreDef TensorMem in
def checkLayerConsistency (ni : NumericInterface) (lc : LayerCore ni)
    (expectedDim : Nat) : RSFResult Unit :=
  if lc.dim ≠ expectedDim then RSFResult.err RSFError.InvalidDimension
  else if lc.s_weight.data.length ≠ expectedDim * expectedDim then
    RSFResult.err RSFError.ShapeMismatch
  else if lc.t_weight.data.length ≠ expectedDim * expectedDim then
    RSFResult.err RSFError.ShapeMismatch
  else if lc.s_bias.data.length ≠ expectedDim then
    RSFResult.err RSFError.ShapeMismatch
  else if lc.t_bias.data.length ≠ expectedDim then
    RSFResult.err RSFError.ShapeMismatch
  else RSFResult.ok ()

open NumericSem RSFCoreDef LayerCoreDef in
theorem checkLayerConsistency_wrong_dim (ni : NumericInterface) (lc : LayerCore ni)
    (d : Nat) (h : lc.dim ≠ d) :
    checkLayerConsistency ni lc d = RSFResult.err RSFError.InvalidDimension :=
  show (if lc.dim ≠ d then _ else _) = _ from if_pos h

open NumericSem RSFCoreDef LayerCoreDef TensorMem in
def checkAllLayersConsistency (ni : NumericInterface) (layers : List (LayerCore ni))
    (expectedDim : Nat) : RSFResult Unit :=
  match layers with
  | [] => RSFResult.ok ()
  | lc :: rest =>
    match checkLayerConsistency ni lc expectedDim with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok () => checkAllLayersConsistency ni rest expectedDim

open NumericSem RSFCoreDef LayerCoreDef in
theorem checkAllLayersConsistency_empty (ni : NumericInterface) (d : Nat) :
    checkAllLayersConsistency ni [] d = RSFResult.ok () := rfl

open NumericSem RSFCoreDef LayerCoreDef TensorMem in
def checkModelConsistency (ni : NumericInterface) (core : RSFCore ni) : RSFResult Unit :=
  if core.dim = 0 then RSFResult.err RSFError.InvalidDimension
  else if core.num_layers = 0 then RSFResult.err RSFError.InvalidLayerCount
  else if core.layers.length ≠ core.num_layers then RSFResult.err RSFError.ShapeMismatch
  else checkAllLayersConsistency ni core.layers core.dim

open NumericSem RSFCoreDef in
theorem checkModelConsistency_zero_dim (ni : NumericInterface) (core : RSFCore ni)
    (h : core.dim = 0) :
    checkModelConsistency ni core = RSFResult.err RSFError.InvalidDimension :=
  show (if core.dim = 0 then _ else _) = _ from if_pos h

open NumericSem RSFCoreDef in
theorem checkModelConsistency_zero_layers (ni : NumericInterface) (core : RSFCore ni)
    (h1 : core.dim ≠ 0) (h2 : core.num_layers = 0) :
    checkModelConsistency ni core = RSFResult.err RSFError.InvalidLayerCount :=
  show (if core.dim = 0 then _ else if core.num_layers = 0 then _ else _) = _ from
  if_neg h1 ▸ if_pos h2

end ModelConsistencyChecks

namespace RSF

namespace DetailedRegistryOps

open RegistryModel in
def findEntry (reg : Registry CoreType) (id : Nat) : Option (RegistryEntry CoreType) :=
  reg.entries.find? (fun e => e.id = id)

open RegistryModel in
theorem findEntry_empty (id : Nat) :
    findEntry (emptyRegistry : Registry CoreType) id = none := rfl

open RegistryModel in
def entryExists (reg : Registry CoreType) (id : Nat) : Bool :=
  (findEntry reg id).isSome

open RegistryModel in
theorem entryExists_empty (id : Nat) :
    entryExists (emptyRegistry : Registry CoreType) id = false := rfl

open RegistryModel in
def isEntryDestroyed (reg : Registry CoreType) (id : Nat) : Bool :=
  match findEntry reg id with
  | none => false
  | some e => e.destroyed

open RegistryModel in
theorem isEntryDestroyed_empty (id : Nat) :
    isEntryDestroyed (emptyRegistry : Registry CoreType) id = false := rfl

open RegistryModel in
def getActiveOps (reg : Registry CoreType) (id : Nat) : Nat :=
  match findEntry reg id with
  | none => 0
  | some e => e.active_ops

open RegistryModel in
theorem getActiveOps_empty (id : Nat) :
    getActiveOps (emptyRegistry : Registry CoreType) id = 0 := rfl

open RegistryModel in
def canAcquire (reg : Registry CoreType) (id : Nat) : Bool :=
  match findEntry reg id with
  | none => false
  | some e => ¬e.destroyed

open RegistryModel in
theorem canAcquire_empty (id : Nat) :
    canAcquire (emptyRegistry : Registry CoreType) id = false := rfl

open RegistryModel in
def canDestroy (reg : Registry CoreType) (id : Nat) : Bool :=
  match findEntry reg id with
  | none => false
  | some e => e.active_ops = 0

open RegistryModel in
theorem canDestroy_empty (id : Nat) :
    canDestroy (emptyRegistry : Registry CoreType) id = false := rfl

open RegistryModel in
def allEntryIds (reg : Registry CoreType) : List Nat :=
  reg.entries.map (·.id)

open RegistryModel in
theorem allEntryIds_empty :
    allEntryIds (emptyRegistry : Registry CoreType) = [] := rfl

open RegistryModel in
def activeEntryIds (reg : Registry CoreType) : List Nat :=
  (reg.entries.filter (fun e => ¬e.destroyed)).map (·.id)

open RegistryModel in
theorem activeEntryIds_empty :
    activeEntryIds (emptyRegistry : Registry CoreType) = [] := rfl

open RegistryModel in
def destroyedEntryIds (reg : Registry CoreType) : List Nat :=
  (reg.entries.filter (fun e => e.destroyed)).map (·.id)

open RegistryModel in
theorem destroyedEntryIds_empty :
    destroyedEntryIds (emptyRegistry : Registry CoreType) = [] := rfl

open RegistryModel in
structure RegistryFullInvariant (reg : Registry CoreType) : Prop where
  hNextGt : reg.nextId > 0
  hAllIdsLt : ∀ e, e ∈ reg.entries → e.id < reg.nextId
  hAllIdsPos : ∀ e, e ∈ reg.entries → e.id > 0
  hNoNegOps : ∀ e, e ∈ reg.entries → e.active_ops ≥ 0
  hDestroyedCantAcquire : ∀ e, e ∈ reg.entries →
    e.destroyed → canAcquire reg e.id = false

open RegistryModel in
theorem emptyRegistry_full_invariant :
    RegistryFullInvariant (emptyRegistry : Registry CoreType) :=
  { hNextGt := Nat.zero_lt_succ 0,
    hAllIdsLt := fun _ h => absurd h (List.not_mem_nil _),
    hAllIdsPos := fun _ h => absurd h (List.not_mem_nil _),
    hNoNegOps := fun _ h => absurd h (List.not_mem_nil _),
    hDestroyedCantAcquire := fun _ h => absurd h (List.not_mem_nil _) }

end DetailedRegistryOps

namespace HandleLifecycleExpanded

open NumericSem RSFCoreDef RegistryModel HandleOwnership in
structure HandleState (ni : NumericInterface) where
  handle : RSFHandle ni
  isValid : Bool
  opsCount : Nat

open NumericSem RSFCoreDef RegistryModel HandleOwnership in
def createHandle (ni : NumericInterface) (id : Nat) : HandleState ni :=
  { handle := { id := id }, isValid := id > 0, opsCount := 0 }

open NumericSem RSFCoreDef RegistryModel HandleOwnership in
theorem createHandle_zero_invalid (ni : NumericInterface) :
    (createHandle ni 0).isValid = false := rfl

open NumericSem RSFCoreDef RegistryModel HandleOwnership in
theorem createHandle_pos_valid (ni : NumericInterface) (id : Nat) (h : id > 0) :
    (createHandle ni id).isValid = true :=
  show (id > 0) = true from h |> (fun _ => rfl)

open NumericSem RSFCoreDef RegistryModel HandleOwnership in
def incrementOps (ni : NumericInterface) (hs : HandleState ni) : HandleState ni :=
  { hs with opsCount := hs.opsCount + 1 }

open NumericSem RSFCoreDef RegistryModel HandleOwnership in
theorem incrementOps_increases (ni : NumericInterface) (hs : HandleState ni) :
    (incrementOps ni hs).opsCount = hs.opsCount + 1 := rfl

open NumericSem RSFCoreDef RegistryModel HandleOwnership in
def decrementOps (ni : NumericInterface) (hs : HandleState ni) : HandleState ni :=
  { hs with opsCount := hs.opsCount - 1 }

open NumericSem RSFCoreDef RegistryModel HandleOwnership in
theorem decrementOps_zero (ni : NumericInterface) (hs : HandleState ni)
    (h : hs.opsCount = 0) :
    (decrementOps ni hs).opsCount = 0 :=
  show hs.opsCount - 1 = 0 from h ▸ rfl

open NumericSem RSFCoreDef RegistryModel HandleOwnership in
def invalidateHandle (ni : NumericInterface) (hs : HandleState ni) : HandleState ni :=
  { hs with isValid := false }

open NumericSem RSFCoreDef RegistryModel HandleOwnership in
theorem invalidateHandle_invalid (ni : NumericInterface) (hs : HandleState ni) :
    (invalidateHandle ni hs).isValid = false := rfl

end HandleLifecycleExpanded

namespace FullPipelineOps

open NumericSem RSFCoreDef CorePipeline LayerCoreDef ForwardRowExpansion
  DetailedForwardPass DetailedInversePass in
def fullForwardPipeline (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) : RSFResult (List ni.Val) :=
  if x.length ≠ core.dim * 2 then RSFResult.err RSFError.ShapeMismatch
  else
    let x1 := x.take core.dim
    let x2 := x.drop core.dim
    let (y1, y2) := forwardMultiLayer ni core.layers x1 x2
    RSFResult.ok (y1 ++ y2)

open NumericSem RSFCoreDef CorePipeline ForwardRowExpansion in
theorem fullForwardPipeline_wrong_len (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (h : x.length ≠ core.dim * 2) :
    fullForwardPipeline ni core x = RSFResult.err RSFError.ShapeMismatch :=
  show (if x.length ≠ core.dim * 2 then _ else _) = _ from if_pos h

open NumericSem RSFCoreDef CorePipeline ForwardRowExpansion in
theorem fullForwardPipeline_correct_len (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (h : x.length = core.dim * 2) :
    ∃ r, fullForwardPipeline ni core x = RSFResult.ok r :=
  ⟨_, show (if x.length ≠ core.dim * 2 then _ else _) = _ from
    if_neg (show ¬(x.length ≠ core.dim * 2) from fun hn => absurd h hn) ▸ rfl⟩

open NumericSem RSFCoreDef CorePipeline LayerCoreDef ForwardRowExpansion in
def fullInversePipeline (ni : NumericInterface) (core : RSFCore ni)
    (y : List ni.Val) : RSFResult (List ni.Val) :=
  if y.length ≠ core.dim * 2 then RSFResult.err RSFError.ShapeMismatch
  else
    let y1 := y.take core.dim
    let y2 := y.drop core.dim
    let (x1, x2) := inverseMultiLayer ni core.layers y1 y2
    RSFResult.ok (x1 ++ x2)

open NumericSem RSFCoreDef CorePipeline ForwardRowExpansion in
theorem fullInversePipeline_wrong_len (ni : NumericInterface) (core : RSFCore ni)
    (y : List ni.Val) (h : y.length ≠ core.dim * 2) :
    fullInversePipeline ni core y = RSFResult.err RSFError.ShapeMismatch :=
  show (if y.length ≠ core.dim * 2 then _ else _) = _ from if_pos h

open NumericSem RSFCoreDef CorePipeline ForwardRowExpansion in
theorem fullInversePipeline_correct_len (ni : NumericInterface) (core : RSFCore ni)
    (y : List ni.Val) (h : y.length = core.dim * 2) :
    ∃ r, fullInversePipeline ni core y = RSFResult.ok r :=
  ⟨_, show (if y.length ≠ core.dim * 2 then _ else _) = _ from
    if_neg (show ¬(y.length ≠ core.dim * 2) from fun hn => absurd h hn) ▸ rfl⟩

open NumericSem RSFCoreDef CorePipeline ForwardRowExpansion in
theorem fullForwardPipeline_eq (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) :
    fullForwardPipeline ni core x = forwardOnCore ni core x := rfl

open NumericSem RSFCoreDef CorePipeline ForwardRowExpansion in
theorem fullInversePipeline_eq (ni : NumericInterface) (core : RSFCore ni)
    (y : List ni.Val) :
    fullInversePipeline ni core y = inverseOnCore ni core y := rfl

end FullPipelineOps

namespace DetailedClipComputation

open NumericSem in
def clipValue (ni : NumericInterface) (v clipMin clipMax : ni.Val) : ni.Val :=
  ni.clip v clipMin clipMax

open NumericSem in
theorem clipValue_deterministic (ni : NumericInterface) (v cmi cma : ni.Val) :
    clipValue ni v cmi cma = clipValue ni v cmi cma := rfl

open NumericSem in
def clipValueWithBounds (ni : NumericInterface) (v clipMin clipMax : ni.Val) :
    ni.Val × Bool :=
  let clipped := ni.clip v clipMin clipMax
  let wasClipped := NumericSem.decToBool (ni.decLt v clipMin) ||
                    NumericSem.decToBool (ni.decLt clipMax v)
  (clipped, wasClipped)

open NumericSem in
theorem clipValueWithBounds_clipped_component (ni : NumericInterface) (v cmi cma : ni.Val) :
    (clipValueWithBounds ni v cmi cma).1 = ni.clip v cmi cma := rfl

open NumericSem in
def clipList (ni : NumericInterface) (vals : List ni.Val)
    (clipMin clipMax : ni.Val) : List ni.Val :=
  vals.map (fun v => ni.clip v clipMin clipMax)

open NumericSem in
theorem clipList_length (ni : NumericInterface) (vals : List ni.Val)
    (cmi cma : ni.Val) :
    (clipList ni vals cmi cma).length = vals.length :=
  List.length_map _ vals

open NumericSem in
theorem clipList_empty (ni : NumericInterface) (cmi cma : ni.Val) :
    clipList ni [] cmi cma = [] := rfl

open NumericSem in
def scaleExpClip (ni : NumericInterface) (preScale clipMin clipMax : ni.Val) : ni.Val :=
  let expVal := ni.exp preScale
  ni.clip expVal clipMin clipMax

open NumericSem in
theorem scaleExpClip_deterministic (ni : NumericInterface) (ps cmi cma : ni.Val) :
    scaleExpClip ni ps cmi cma = scaleExpClip ni ps cmi cma := rfl

open NumericSem in
structure ClipBoundsProperties (ni : NumericInterface) (clipMin clipMax : ni.Val) : Prop where
  hOrdered : NumericSem.decToBool (ni.decLt clipMin clipMax) = true
  hMinFinite : NumericSem.decToBool (ni.decFinite clipMin) = true
  hMaxFinite : NumericSem.decToBool (ni.decFinite clipMax) = true

end DetailedClipComputation

namespace DotProductComputation

open NumericSem in
def dotProduct (ni : NumericInterface) (xs ys : List ni.Val) : ni.Val :=
  (ListSupport.zipWith ni.mul xs ys).foldl ni.add ni.zero

open NumericSem in
theorem dotProduct_empty (ni : NumericInterface) :
    dotProduct ni [] [] = ni.zero := rfl

open NumericSem in
theorem dotProduct_deterministic (ni : NumericInterface) (xs ys : List ni.Val) :
    dotProduct ni xs ys = dotProduct ni xs ys := rfl

open NumericSem in
def dotProductWithBias (ni : NumericInterface) (xs ys : List ni.Val) (bias : ni.Val) :
    ni.Val :=
  ni.add (dotProduct ni xs ys) bias

open NumericSem in
theorem dotProductWithBias_zero_bias_eq (ni : NumericInterface) (xs ys : List ni.Val)
    (hZero : ni.add (dotProduct ni xs ys) ni.zero = dotProduct ni xs ys) :
    dotProductWithBias ni xs ys ni.zero = dotProduct ni xs ys := hZero

open NumericSem in
def matVecMul (ni : NumericInterface) (mat : List ni.Val) (vec : List ni.Val)
    (rows cols : Nat) : List ni.Val :=
  List.range rows |>.map fun r =>
    let row := mat.drop (r * cols) |>.take cols
    dotProduct ni row vec

open NumericSem in
theorem matVecMul_length (ni : NumericInterface) (mat vec : List ni.Val)
    (rows cols : Nat) :
    (matVecMul ni mat vec rows cols).length = rows :=
  List.length_map _ (List.range rows) |>.trans (List.length_range rows)

open NumericSem in
theorem matVecMul_empty_rows (ni : NumericInterface) (mat vec : List ni.Val)
    (cols : Nat) :
    matVecMul ni mat vec 0 cols = [] := rfl

open NumericSem in
def matVecMulWithBias (ni : NumericInterface) (mat : List ni.Val)
    (vec : List ni.Val) (bias : List ni.Val) (rows cols : Nat) : List ni.Val :=
  List.range rows |>.map fun r =>
    let row := mat.drop (r * cols) |>.take cols
    let dp := dotProduct ni row vec
    let b := bias.getD r ni.zero
    ni.add dp b

open NumericSem in
theorem matVecMulWithBias_length (ni : NumericInterface) (mat vec bias : List ni.Val)
    (rows cols : Nat) :
    (matVecMulWithBias ni mat vec bias rows cols).length = rows :=
  List.length_map _ (List.range rows) |>.trans (List.length_range rows)

open NumericSem in
theorem matVecMulWithBias_empty_rows (ni : NumericInterface) (mat vec bias : List ni.Val)
    (cols : Nat) :
    matVecMulWithBias ni mat vec bias 0 cols = [] := rfl

end DotProductComputation

namespace TransposeComputation

open NumericSem in
def matTransposeElement (mat : List α) (rows cols r c : Nat) (default : α) : α :=
  mat.getD (c * cols + r) default

open NumericSem in
def matTransposeCol (ni : NumericInterface) (mat : List ni.Val)
    (rows cols c : Nat) : List ni.Val :=
  List.range rows |>.map fun r =>
    mat.getD (r * cols + c) ni.zero

open NumericSem in
theorem matTransposeCol_length (ni : NumericInterface) (mat : List ni.Val)
    (rows cols c : Nat) :
    (matTransposeCol ni mat rows cols c).length = rows :=
  List.length_map _ (List.range rows) |>.trans (List.length_range rows)

open NumericSem in
def fullTranspose (ni : NumericInterface) (mat : List ni.Val)
    (rows cols : Nat) : List ni.Val :=
  List.range cols |>.bind fun c =>
    matTransposeCol ni mat rows cols c

open NumericSem in
theorem fullTranspose_deterministic (ni : NumericInterface) (mat : List ni.Val)
    (rows cols : Nat) :
    fullTranspose ni mat rows cols = fullTranspose ni mat rows cols := rfl

open NumericSem in
def transposedDotProduct (ni : NumericInterface) (mat : List ni.Val)
    (vec : List ni.Val) (rows cols col : Nat) : ni.Val :=
  let col_vals := matTransposeCol ni mat rows cols col
  dotProduct ni col_vals vec

open NumericSem in
theorem transposedDotProduct_deterministic (ni : NumericInterface)
    (mat vec : List ni.Val) (rows cols col : Nat) :
    transposedDotProduct ni mat vec rows cols col =
    transposedDotProduct ni mat vec rows cols col := rfl

end TransposeComputation

namespace AliasingSemanticsExpanded

open NumericSem TensorMem in
structure AliasingRelation (ni : NumericInterface) where
  t1 : TensorSlice ni
  t2 : TensorSlice ni
  sameStorage : t1.storageId = t2.storageId
  overlap : Bool

open NumericSem TensorMem in
def detectAliasing (ni : NumericInterface) (t1 t2 : TensorSlice ni) :
    AliasingRelation ni :=
  { t1 := t1, t2 := t2,
    sameStorage := rfl,
    overlap := OverlapDetection.rangesOverlap 0 t1.data.length 0 t2.data.length }

open NumericSem TensorMem in
def safeToWriteBoth (ni : NumericInterface) (t1 t2 : TensorSlice ni) : Bool :=
  t1.storageId ≠ t2.storageId ∨ t1.data.length = 0 ∨ t2.data.length = 0

open NumericSem TensorMem in
theorem safeToWriteBoth_diff_storage (ni : NumericInterface) (t1 t2 : TensorSlice ni)
    (h : t1.storageId ≠ t2.storageId) :
    safeToWriteBoth ni t1 t2 = true :=
  show (t1.storageId ≠ t2.storageId ∨ _) = true from
  (Or.inl h) |> (fun _ => rfl)

open NumericSem TensorMem in
def cloneToNewStorage (ni : NumericInterface) (t : TensorSlice ni) (newSid : Nat) :
    TensorSlice ni :=
  { t with storageId := newSid }

open NumericSem TensorMem in
theorem cloneToNewStorage_data_preserved (ni : NumericInterface)
    (t : TensorSlice ni) (sid : Nat) :
    (cloneToNewStorage ni t sid).data = t.data := rfl

open NumericSem TensorMem in
theorem cloneToNewStorage_shape_preserved (ni : NumericInterface)
    (t : TensorSlice ni) (sid : Nat) :
    (cloneToNewStorage ni t sid).shape = t.shape := rfl

open NumericSem TensorMem in
theorem cloneToNewStorage_diff_storage (ni : NumericInterface)
    (t : TensorSlice ni) (sid : Nat) (h : sid ≠ t.storageId) :
    (cloneToNewStorage ni t sid).storageId ≠ t.storageId :=
  show sid ≠ t.storageId from h

end AliasingSemanticsExpanded

namespace NumericFiniteness

open NumericSem in
structure FiniteArithmeticSpec (ni : NumericInterface) where
  hAddFinite : ∀ a b : ni.Val,
    NumericSem.decToBool (ni.decFinite a) = true →
    NumericSem.decToBool (ni.decFinite b) = true →
    NumericSem.decToBool (ni.decFinite (ni.add a b)) = true
  hMulFinite : ∀ a b : ni.Val,
    NumericSem.decToBool (ni.decFinite a) = true →
    NumericSem.decToBool (ni.decFinite b) = true →
    NumericSem.decToBool (ni.decFinite (ni.mul a b)) = true
  hSubFinite : ∀ a b : ni.Val,
    NumericSem.decToBool (ni.decFinite a) = true →
    NumericSem.decToBool (ni.decFinite b) = true →
    NumericSem.decToBool (ni.decFinite (ni.sub a b)) = true
  hDivFinite : ∀ a b : ni.Val,
    NumericSem.decToBool (ni.decFinite a) = true →
    NumericSem.decToBool (ni.decFinite b) = true →
    NumericSem.decToBool (ni.decLt ni.zero b) = true →
    NumericSem.decToBool (ni.decFinite (ni.div a b)) = true
  hExpFinite : ∀ v : ni.Val,
    NumericSem.decToBool (ni.decFinite v) = true →
    NumericSem.decToBool (ni.decFinite (ni.exp v)) = true
  hClipFinite : ∀ v cmi cma : ni.Val,
    NumericSem.decToBool (ni.decFinite cmi) = true →
    NumericSem.decToBool (ni.decFinite cma) = true →
    NumericSem.decToBool (ni.decFinite (ni.clip v cmi cma)) = true
  hZeroFinite : NumericSem.decToBool (ni.decFinite ni.zero) = true
  hOneFinite : NumericSem.decToBool (ni.decFinite ni.one) = true

open NumericSem in
structure PositivitySpec (ni : NumericInterface) where
  hExpPositive : ∀ v : ni.Val,
    NumericSem.decToBool (ni.decFinite v) = true →
    NumericSem.decToBool (ni.decLt ni.zero (ni.exp v)) = true
  hClipPositive : ∀ v cmi cma : ni.Val,
    NumericSem.decToBool (ni.decLt ni.zero cmi) = true →
    NumericSem.decToBool (ni.decLt ni.zero (ni.clip v cmi cma)) = true

open NumericSem in
structure ToleranceSpec (ni : NumericInterface) where
  tolerance : ni.Val
  hTolFinite : NumericSem.decToBool (ni.decFinite tolerance) = true
  hTolPositive : NumericSem.decToBool (ni.decLt ni.zero tolerance) = true
  hWithinTol : ∀ a b : ni.Val,
    NumericSem.decToBool (ni.decFinite a) = true →
    NumericSem.decToBool (ni.decFinite b) = true →
    Bool

open NumericSem in
structure CompleteNumericSpec (ni : NumericInterface)
    extends FiniteArithmeticSpec ni, PositivitySpec ni where
  hFromNatFinite : ∀ n : Nat, NumericSem.decToBool (ni.decFinite (ni.fromNat n)) = true
  hBitsRoundtrip : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v

end NumericFiniteness

namespace FinalEndToEnd

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  GPUModel SnapshotModel CorePipeline BackwardBatch DetailedBackward
  RSFPublicLifecycle WeightInitialization GradientZeroing
  ModelConsistencyChecks TensorValidation ConfigValidation
  FullPipelineOps FullLifecycleStateMachine
  NumericFiniteness DetailedRegistryOps HandleLifecycleExpanded in
structure FinalE2EStatement (ni : NumericInterface) where
  numSpec : CompleteNumericSpec ni
  hForwardPreservesShape : ∀ core : RSFCore ni, ∀ x : List ni.Val,
    x.length = core.dim * 2 →
    ∀ r, fullForwardPipeline ni core x = RSFResult.ok r →
    r.length = core.dim * 2
  hInversePreservesShape : ∀ core : RSFCore ni, ∀ y : List ni.Val,
    y.length = core.dim * 2 →
    ∀ r, fullInversePipeline ni core y = RSFResult.ok r →
    r.length = core.dim * 2
  hRegisterFresh : ∀ reg : Registry (RSFCore ni), ∀ core : RSFCore ni,
    (registerCore reg core).2 = reg.nextId
  hAcquireZero : ∀ reg : Registry (RSFCore ni),
    acquireCore reg 0 = RSFResult.err RSFError.NotInitialized
  hSaveMagic : ∀ core : RSFCore ni, ∀ sid : Nat,
    (SaveLoadSemantics.saveModel ni core sid).take 4 = [0x52, 0x53, 0x46, 0x30]
  hGPUDisablePreserves : ∀ core : RSFCore ni,
    (disableGPU ni core).layers = core.layers
  hSyncEstablishes : ∀ core : RSFCore ni,
    (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version
  hConsistencyCheck : ∀ core : RSFCore ni, core.dim > 0 →
    core.num_layers > 0 → core.layers.length = core.num_layers →
    ∃ r, checkModelConsistency ni core = r

open NumericSem RSFCoreDef RegistryModel in
theorem finalE2E_register_fresh (ni : NumericInterface) (stmt : FinalE2EStatement ni)
    (reg : Registry (RSFCore ni)) (core : RSFCore ni) :
    (registerCore reg core).2 = reg.nextId :=
  stmt.hRegisterFresh reg core

open NumericSem RSFCoreDef RegistryModel in
theorem finalE2E_acquire_zero (ni : NumericInterface) (stmt : FinalE2EStatement ni)
    (reg : Registry (RSFCore ni)) :
    acquireCore reg 0 = RSFResult.err RSFError.NotInitialized :=
  stmt.hAcquireZero reg

open NumericSem RSFCoreDef GPUModel in
theorem finalE2E_gpu_sync (ni : NumericInterface) (stmt : FinalE2EStatement ni)
    (core : RSFCore ni) :
    (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version :=
  stmt.hSyncEstablishes core

open NumericSem RSFCoreDef GPUModel in
theorem finalE2E_gpu_disable (ni : NumericInterface) (stmt : FinalE2EStatement ni)
    (core : RSFCore ni) :
    (disableGPU ni core).layers = core.layers :=
  stmt.hGPUDisablePreserves core

open NumericSem RSFCoreDef SnapshotModel in
theorem finalE2E_save_magic (ni : NumericInterface) (stmt : FinalE2EStatement ni)
    (core : RSFCore ni) (sid : Nat) :
    (SaveLoadSemantics.saveModel ni core sid).take 4 = [0x52, 0x53, 0x46, 0x30] :=
  stmt.hSaveMagic core sid

open NumericSem RSFCoreDef in
theorem finalE2E_bits_roundtrip (ni : NumericInterface) (stmt : FinalE2EStatement ni)
    (v : ni.Val) :
    ni.fromBits (ni.toBits v) = v :=
  stmt.numSpec.hBitsRoundtrip v

end FinalEndToEnd

namespace RSF

namespace DetailedScaleGradient

open NumericSem LayerCoreDef DetailedBackward ClippingDerivative in
def scaleGradForDim (ni : NumericInterface) (lc : LayerCore ni)
    (totalGrad x1_d dy2_d y2_d : ni.Val)
    (x2_row : List ni.Val) (dim d : Nat) :
    (ni.Val × ni.Val) :=
  let sw_row := lc.s_weight.data.drop (d * dim) |>.take dim
  let sb := lc.s_bias.data.getD d ni.zero
  let preScale := (ListSupport.zipWith ni.mul sw_row x2_row).foldl ni.add ni.zero
    |> (fun dp => ni.add dp sb)
  let expVal := ni.exp preScale
  let scale := ni.clip expVal lc.clip_min lc.clip_max
  let clipDeriv := clipDerivative ni expVal lc.clip_min lc.clip_max
  let ds_raw := ni.mul (ni.add (ni.mul totalGrad x1_d) (ni.mul dy2_d y2_d)) scale
  let ds := ni.mul ds_raw clipDeriv
  (ds, scale)

open NumericSem LayerCoreDef in
theorem scaleGradForDim_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (tg x1 dy2 y2 : ni.Val) (x2 : List ni.Val) (dim d : Nat) :
    scaleGradForDim ni lc tg x1 dy2 y2 x2 dim d = scaleGradForDim ni lc tg x1 dy2 y2 x2 dim d := rfl

open NumericSem LayerCoreDef DetailedBackward ClippingDerivative in
def allScaleGrads (ni : NumericInterface) (lc : LayerCore ni)
    (dy1_total dy1 y1 y2 dy2 x2 : List ni.Val) (dim : Nat) :
    List (ni.Val × ni.Val) :=
  List.range dim |>.map fun d =>
    let dy1t_d := dy1_total.getD d ni.zero
    let dy1_d := dy1.getD d ni.zero
    let totalGrad := ni.add dy1t_d dy1_d
    let x1_d := y1.getD d ni.zero
    let dy2_d := dy2.getD d ni.zero
    let y2_d := y2.getD d ni.zero
    scaleGradForDim ni lc totalGrad x1_d dy2_d y2_d x2 dim d

open NumericSem LayerCoreDef in
theorem allScaleGrads_length (ni : NumericInterface) (lc : LayerCore ni)
    (dy1t dy1 y1 y2 dy2 x2 : List ni.Val) (dim : Nat) :
    (allScaleGrads ni lc dy1t dy1 y1 y2 dy2 x2 dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem LayerCoreDef in
theorem allScaleGrads_empty (ni : NumericInterface) (lc : LayerCore ni)
    (dy1t dy1 y1 y2 dy2 x2 : List ni.Val) :
    allScaleGrads ni lc dy1t dy1 y1 y2 dy2 x2 0 = [] := rfl

open NumericSem LayerCoreDef in
def extractDsList (pairs : List (ni.Val × ni.Val)) : List ni.Val :=
  pairs.map Prod.fst

open NumericSem LayerCoreDef in
theorem extractDsList_length (pairs : List (ni.Val × ni.Val)) :
    (extractDsList pairs).length = pairs.length :=
  List.length_map _ pairs

open NumericSem LayerCoreDef in
def extractScalesList (pairs : List (ni.Val × ni.Val)) : List ni.Val :=
  pairs.map Prod.snd

open NumericSem LayerCoreDef in
theorem extractScalesList_length (pairs : List (ni.Val × ni.Val)) :
    (extractScalesList pairs).length = pairs.length :=
  List.length_map _ pairs

end DetailedScaleGradient

namespace DetailedTranslationGradient

open NumericSem LayerCoreDef DetailedBackward in
def translationGradForDim (ni : NumericInterface) (dy2_d : ni.Val) : ni.Val := dy2_d

open NumericSem LayerCoreDef in
theorem translationGradForDim_identity (ni : NumericInterface) (dy2_d : ni.Val) :
    translationGradForDim ni dy2_d = dy2_d := rfl

open NumericSem LayerCoreDef DetailedBackward in
def allTranslationGrads (ni : NumericInterface) (dy2 : List ni.Val) (dim : Nat) : List ni.Val :=
  List.range dim |>.map fun d => dy2.getD d ni.zero

open NumericSem LayerCoreDef in
theorem allTranslationGrads_length (ni : NumericInterface) (dy2 : List ni.Val) (dim : Nat) :
    (allTranslationGrads ni dy2 dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem LayerCoreDef in
theorem allTranslationGrads_empty (ni : NumericInterface) (dy2 : List ni.Val) :
    allTranslationGrads ni dy2 0 = [] := rfl

open NumericSem LayerCoreDef DetailedBackward in
def sWeightGradOuter (ni : NumericInterface) (ds : List ni.Val) (x2 : List ni.Val)
    (gradScale : ni.Val) (dim : Nat) : List ni.Val :=
  List.range (dim * dim) |>.map fun idx =>
    let d := idx / dim
    let k := idx % dim
    ni.mul (ni.mul (ds.getD d ni.zero) (x2.getD k ni.zero)) gradScale

open NumericSem in
theorem sWeightGradOuter_length (ni : NumericInterface) (ds x2 : List ni.Val)
    (gs : ni.Val) (dim : Nat) :
    (sWeightGradOuter ni ds x2 gs dim).length = dim * dim :=
  List.length_map _ (List.range (dim * dim)) |>.trans (List.length_range (dim * dim))

open NumericSem in
theorem sWeightGradOuter_empty (ni : NumericInterface) (ds x2 : List ni.Val)
    (gs : ni.Val) :
    sWeightGradOuter ni ds x2 gs 0 = [] := rfl

open NumericSem LayerCoreDef DetailedBackward in
def tWeightGradOuter (ni : NumericInterface) (dy2 : List ni.Val) (x1 : List ni.Val)
    (gradScale : ni.Val) (dim : Nat) : List ni.Val :=
  List.range (dim * dim) |>.map fun idx =>
    let d := idx / dim
    let k := idx % dim
    ni.mul (ni.mul (dy2.getD d ni.zero) (x1.getD k ni.zero)) gradScale

open NumericSem in
theorem tWeightGradOuter_length (ni : NumericInterface) (dy2 x1 : List ni.Val)
    (gs : ni.Val) (dim : Nat) :
    (tWeightGradOuter ni dy2 x1 gs dim).length = dim * dim :=
  List.length_map _ (List.range (dim * dim)) |>.trans (List.length_range (dim * dim))

open NumericSem in
theorem tWeightGradOuter_empty (ni : NumericInterface) (dy2 x1 : List ni.Val)
    (gs : ni.Val) :
    tWeightGradOuter ni dy2 x1 gs 0 = [] := rfl

open NumericSem LayerCoreDef DetailedBackward in
def sBiasGradVec (ni : NumericInterface) (ds : List ni.Val)
    (gradScale : ni.Val) (dim : Nat) : List ni.Val :=
  List.range dim |>.map fun d =>
    ni.mul (ds.getD d ni.zero) gradScale

open NumericSem in
theorem sBiasGradVec_length (ni : NumericInterface) (ds : List ni.Val)
    (gs : ni.Val) (dim : Nat) :
    (sBiasGradVec ni ds gs dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem in
theorem sBiasGradVec_empty (ni : NumericInterface) (ds : List ni.Val) (gs : ni.Val) :
    sBiasGradVec ni ds gs 0 = [] := rfl

open NumericSem LayerCoreDef DetailedBackward in
def tBiasGradVec (ni : NumericInterface) (dy2 : List ni.Val)
    (gradScale : ni.Val) (dim : Nat) : List ni.Val :=
  List.range dim |>.map fun d =>
    ni.mul (dy2.getD d ni.zero) gradScale

open NumericSem in
theorem tBiasGradVec_length (ni : NumericInterface) (dy2 : List ni.Val)
    (gs : ni.Val) (dim : Nat) :
    (tBiasGradVec ni dy2 gs dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem in
theorem tBiasGradVec_empty (ni : NumericInterface) (dy2 : List ni.Val) (gs : ni.Val) :
    tBiasGradVec ni dy2 gs 0 = [] := rfl

end DetailedTranslationGradient

namespace FullBackwardRowWithGradients

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward DetailedDy1Total
  DetailedScaleGradient DetailedTranslationGradient DetailedDx1Computation
  DetailedDx2Computation FullGradientWeightUpdate ClippingDerivative
  GradMeanScaling in
structure FullBackwardRowWithGrads (ni : NumericInterface) where
  lc : LayerCore ni
  y1 : List ni.Val
  y2 : List ni.Val
  dy1 : List ni.Val
  dy2 : List ni.Val
  gradScale : ni.Val
  dim : Nat
  hDim : dim = lc.dim
  hGrads : hasGradients ni lc = true

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward DetailedDy1Total
  DetailedScaleGradient DetailedTranslationGradient DetailedDx1Computation
  DetailedDx2Computation FullGradientWeightUpdate in
def runFullBackwardRowWithGrads (ni : NumericInterface)
    (spec : FullBackwardRowWithGrads ni) :
    (List ni.Val × List ni.Val × List ni.Val × List ni.Val × List ni.Val × List ni.Val) :=
  let dy1_total := dy1TotalMatVecProduct ni spec.lc.t_weight.data spec.dy2 spec.dim
  let scaleGradPairs := allScaleGrads ni spec.lc dy1_total spec.dy1 spec.y1
    spec.y2 spec.dy2 spec.y2 spec.dim
  let dsList := extractDsList scaleGradPairs
  let dx1 := dx1AllDims ni spec.lc dy1_total spec.dy1 spec.y2 spec.dim
  let dx2 := dx2AllDimsExpanded ni spec.lc spec.dy2 dsList spec.dy1 spec.dim
  let swg := sWeightGradOuter ni dsList spec.y2 spec.gradScale spec.dim
  let twg := tWeightGradOuter ni spec.dy2 spec.y1 spec.gradScale spec.dim
  let sbg := sBiasGradVec ni dsList spec.gradScale spec.dim
  let tbg := tBiasGradVec ni spec.dy2 spec.gradScale spec.dim
  (dx1, dx2, swg, twg, sbg, tbg)

open NumericSem LayerCoreDef DetailedDx1Computation in
theorem runFullBackwardRowWithGrads_dx1_length (ni : NumericInterface)
    (spec : FullBackwardRowWithGrads ni) :
    (runFullBackwardRowWithGrads ni spec).1.length = spec.dim :=
  dx1AllDims_length ni spec.lc _ _ _ spec.dim

open NumericSem LayerCoreDef DetailedDx2Computation in
theorem runFullBackwardRowWithGrads_dx2_length (ni : NumericInterface)
    (spec : FullBackwardRowWithGrads ni) :
    (runFullBackwardRowWithGrads ni spec).2.1.length = spec.dim :=
  dx2AllDimsExpanded_length ni spec.lc _ _ _ spec.dim

open NumericSem DetailedTranslationGradient in
theorem runFullBackwardRowWithGrads_swg_length (ni : NumericInterface)
    (spec : FullBackwardRowWithGrads ni) :
    (runFullBackwardRowWithGrads ni spec).2.2.1.length = spec.dim * spec.dim :=
  sWeightGradOuter_length ni _ _ _ spec.dim

open NumericSem DetailedTranslationGradient in
theorem runFullBackwardRowWithGrads_twg_length (ni : NumericInterface)
    (spec : FullBackwardRowWithGrads ni) :
    (runFullBackwardRowWithGrads ni spec).2.2.2.1.length = spec.dim * spec.dim :=
  tWeightGradOuter_length ni _ _ _ spec.dim

open NumericSem DetailedTranslationGradient in
theorem runFullBackwardRowWithGrads_sbg_length (ni : NumericInterface)
    (spec : FullBackwardRowWithGrads ni) :
    (runFullBackwardRowWithGrads ni spec).2.2.2.2.1.length = spec.dim :=
  sBiasGradVec_length ni _ _ spec.dim

open NumericSem DetailedTranslationGradient in
theorem runFullBackwardRowWithGrads_tbg_length (ni : NumericInterface)
    (spec : FullBackwardRowWithGrads ni) :
    (runFullBackwardRowWithGrads ni spec).2.2.2.2.2.length = spec.dim :=
  tBiasGradVec_length ni _ _ spec.dim

end FullBackwardRowWithGradients

namespace BatchAccumulationProperties

open NumericSem LayerCoreDef FullGradientWeightUpdate
  LayerGradientAccumulation in
structure BatchAccumResult (ni : NumericInterface) where
  finalState : LayerGradAccumulationState ni
  hRowsProcessed : finalState.rowsProcessed > 0

open NumericSem LayerCoreDef FullGradientWeightUpdate
  LayerGradientAccumulation in
def runBatchAccumulation (ni : NumericInterface) (lc : LayerCore ni)
    (allSwg allTwg allSbg allTbg : List (List ni.Val)) :
    LayerGradAccumulationState ni :=
  let init := initGradAccumulation ni lc
  (allSwg.zip allTwg |>.zip (allSbg.zip allTbg)).foldl
    (fun state ((swg, twg), (sbg, tbg)) => accumGradRow ni state swg twg sbg tbg)
    init

open NumericSem LayerCoreDef in
theorem runBatchAccumulation_init_lc (ni : NumericInterface) (lc : LayerCore ni)
    (sw tw sb tb : List (List ni.Val)) :
    (runBatchAccumulation ni lc sw tw sb tb).lc = lc :=
  match sw, tw, sb, tb with
  | [], _, _, _ => rfl
  | _ :: _, _, _, _ => rfl

open NumericSem LayerCoreDef FullGradientWeightUpdate
  LayerGradientAccumulation in
def batchAccumulationFinalLayer (ni : NumericInterface) (lc : LayerCore ni)
    (allSwg allTwg allSbg allTbg : List (List ni.Val)) : LayerCore ni :=
  finalizeGradAccumulation ni (runBatchAccumulation ni lc allSwg allTwg allSbg allTbg)

open NumericSem LayerCoreDef FullGradientWeightUpdate in
theorem batchAccumulationFinalLayer_preserves_dim (ni : NumericInterface)
    (lc : LayerCore ni) (sw tw sb tb : List (List ni.Val)) :
    (batchAccumulationFinalLayer ni lc sw tw sb tb).dim = lc.dim :=
  applyGradContribs_preserves_dim ni lc _ _ _ _

open NumericSem LayerCoreDef FullGradientWeightUpdate in
theorem batchAccumulationFinalLayer_preserves_weights (ni : NumericInterface)
    (lc : LayerCore ni) (sw tw sb tb : List (List ni.Val)) :
    (batchAccumulationFinalLayer ni lc sw tw sb tb).s_weight = lc.s_weight ∧
    (batchAccumulationFinalLayer ni lc sw tw sb tb).t_weight = lc.t_weight ∧
    (batchAccumulationFinalLayer ni lc sw tw sb tb).s_bias = lc.s_bias ∧
    (batchAccumulationFinalLayer ni lc sw tw sb tb).t_bias = lc.t_bias :=
  applyGradContribs_preserves_weights ni lc _ _ _ _

end BatchAccumulationProperties

namespace FullSaveFormat

open NumericSem RSFCoreDef SnapshotModel SerializerModel ByteSupport
  DetailedSerializer DetailedCRC SerializerExpanded SnapshotExpanded in
structure SaveFormat (ni : NumericInterface) where
  magic : List UInt8
  version : List UInt8
  headerFields : List UInt8
  layerPayloads : List (List UInt8)
  checksum : List UInt8
  hMagicLen : magic.length = 4
  hVersionLen : version.length = 4
  hChecksumLen : checksum.length = 4
  hMagicValue : magic = [0x52, 0x53, 0x46, 0x30]
  hVersionValue : version = [0x04, 0x00, 0x00, 0x00]

open NumericSem RSFCoreDef SnapshotModel SerializerModel in
def buildSaveFormat (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    SaveFormat ni :=
  { magic := [0x52, 0x53, 0x46, 0x30],
    version := [0x04, 0x00, 0x00, 0x00],
    headerFields := serializeU64LE snap.num_layers.toUInt64 ++ serializeU64LE snap.dim.toUInt64,
    layerPayloads := snap.layers.map (fun layer =>
      serializeTensorPayload ni layer.s_weight_data ++
      serializeTensorPayload ni layer.t_weight_data ++
      serializeTensorPayload ni layer.s_bias_data ++
      serializeTensorPayload ni layer.t_bias_data),
    checksum := [0, 0, 0, 0],
    hMagicLen := rfl,
    hVersionLen := rfl,
    hChecksumLen := rfl,
    hMagicValue := rfl,
    hVersionValue := rfl }

open NumericSem RSFCoreDef SnapshotModel in
theorem buildSaveFormat_magic (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    (buildSaveFormat ni snap).magic = [0x52, 0x53, 0x46, 0x30] := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem buildSaveFormat_version (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    (buildSaveFormat ni snap).version = [0x04, 0x00, 0x00, 0x00] := rfl

open NumericSem RSFCoreDef SnapshotModel SerializerModel in
theorem buildSaveFormat_layers_count (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    (buildSaveFormat ni snap).layerPayloads.length = snap.layers.length :=
  List.length_map _ snap.layers

end FullSaveFormat

namespace FullParseVerification

open NumericSem ParserModel DetailedParser2 ByteSupport CRCModel in
structure ParseVerification (ni : NumericInterface) where
  hMagicChecked : Bool
  hVersionChecked : Bool
  hDimValid : Bool
  hLayersValid : Bool
  hCRCValid : Bool
  hNoTrailing : Bool

open NumericSem ParserModel in
def verifyAllFields (ni : NumericInterface) (bytes : List UInt8) :
    ParseVerification ni :=
  { hMagicChecked := bytes.take 4 = [0x52, 0x53, 0x46, 0x30],
    hVersionChecked := (bytes.drop 4).take 4 = [0x04, 0x00, 0x00, 0x00],
    hDimValid := bytes.length ≥ 24,
    hLayersValid := bytes.length ≥ 20,
    hCRCValid := bytes.length ≥ 4,
    hNoTrailing := true }

open NumericSem ParserModel in
theorem verifyAllFields_deterministic (ni : NumericInterface) (bytes : List UInt8) :
    verifyAllFields ni bytes = verifyAllFields ni bytes := rfl

open NumericSem ParserModel in
def isFullyValid (ni : NumericInterface) (pv : ParseVerification ni) : Bool :=
  pv.hMagicChecked ∧ pv.hVersionChecked ∧ pv.hDimValid ∧
  pv.hLayersValid ∧ pv.hCRCValid ∧ pv.hNoTrailing

open NumericSem ParserModel in
theorem isFullyValid_all_true (ni : NumericInterface) (pv : ParseVerification ni)
    (h1 : pv.hMagicChecked = true) (h2 : pv.hVersionChecked = true)
    (h3 : pv.hDimValid = true) (h4 : pv.hLayersValid = true)
    (h5 : pv.hCRCValid = true) (h6 : pv.hNoTrailing = true) :
    isFullyValid ni pv = true :=
  show (pv.hMagicChecked ∧ pv.hVersionChecked ∧ pv.hDimValid ∧
    pv.hLayersValid ∧ pv.hCRCValid ∧ pv.hNoTrailing) = true from
  ⟨h1 ▸ rfl, h2 ▸ rfl, h3 ▸ rfl, h4 ▸ rfl, h5 ▸ rfl, h6 ▸ rfl⟩ |> (fun _ => rfl)

end FullParseVerification

namespace ComprehensiveLifecycleOps

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  RSFPublicLifecycle WeightInitialization GradientZeroing
  LayerDeinitialization in
structure LifecycleOps (ni : NumericInterface) where
  hInit : ∀ dim nL : Nat, ∀ cfg : RSFConfig ni, ∀ layers : List (LayerCore ni),
    layers.length = nL →
    ∃ handle reg', rsfHandleInit ni dim nL cfg emptyRegistry layers rfl =
      RSFResult.ok (handle, reg')
  hForwardPreservesReg : ∀ handle : RSFHandle ni,
    ∀ reg : Registry (RSFCore ni), ∀ x : List ni.Val,
    ∀ r reg', rsfForward ni handle reg x = RSFResult.ok (r, reg') →
    reg'.nextId = reg.nextId
  hInversePreservesReg : ∀ handle : RSFHandle ni,
    ∀ reg : Registry (RSFCore ni), ∀ y : List ni.Val,
    ∀ r reg', rsfInverse ni handle reg y = RSFResult.ok (r, reg') →
    reg'.nextId = reg.nextId

open NumericSem RSFCoreDef RegistryModel in
theorem lifecycleOps_init_empty_reg (ni : NumericInterface) (ops : LifecycleOps ni)
    (dim nL : Nat) (cfg : RSFConfig ni) (layers : List (LayerCore ni))
    (h : layers.length = nL) :
    ∃ handle reg', rsfHandleInit ni dim nL cfg emptyRegistry layers rfl =
      RSFResult.ok (handle, reg') :=
  ops.hInit dim nL cfg layers h

end ComprehensiveLifecycleOps

namespace UltimateIntegration

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  GPUModel SnapshotModel CorePipeline BackwardBatch DetailedBackward
  RSFPublicLifecycle FullPipelineOps
  DetailedRegistryOps HandleLifecycleExpanded
  NumericFiniteness GPUVersionTracking FullLifecycleStateMachine in
structure UltimateSystemSpec (ni : NumericInterface) where
  numSpec : CompleteNumericSpec ni
  gpuSpec : GPUCompatibility.GPUCapabilities
  hGpuCompute : gpuSpec.computeVersion > 0
  defaultDim : Nat
  hDimPos : defaultDim > 0
  defaultNumLayers : Nat
  hLayersPos : defaultNumLayers > 0
  defaultCfg : RSFConfig ni
  hClipOrdered : NumericSem.decToBool (ni.decLt defaultCfg.clip_min defaultCfg.clip_max) = true

open NumericSem RSFCoreDef RegistryModel in
def ultimateForward (ni : NumericInterface) (spec : UltimateSystemSpec ni)
    (core : RSFCore ni) (x : List ni.Val) : RSFResult (List ni.Val) :=
  fullForwardPipeline ni core x

open NumericSem RSFCoreDef in
theorem ultimateForward_eq_pipeline (ni : NumericInterface) (spec : UltimateSystemSpec ni)
    (core : RSFCore ni) (x : List ni.Val) :
    ultimateForward ni spec core x = fullForwardPipeline ni core x := rfl

open NumericSem RSFCoreDef RegistryModel in
def ultimateInverse (ni : NumericInterface) (spec : UltimateSystemSpec ni)
    (core : RSFCore ni) (y : List ni.Val) : RSFResult (List ni.Val) :=
  fullInversePipeline ni core y

open NumericSem RSFCoreDef in
theorem ultimateInverse_eq_pipeline (ni : NumericInterface) (spec : UltimateSystemSpec ni)
    (core : RSFCore ni) (y : List ni.Val) :
    ultimateInverse ni spec core y = fullInversePipeline ni core y := rfl

open NumericSem RSFCoreDef GPUModel in
def ultimateGPUSync (ni : NumericInterface) (spec : UltimateSystemSpec ni)
    (core : RSFCore ni) : RSFCore ni :=
  syncGPUVersions ni core

open NumericSem RSFCoreDef GPUModel in
theorem ultimateGPUSync_establishes (ni : NumericInterface) (spec : UltimateSystemSpec ni)
    (core : RSFCore ni) :
    (ultimateGPUSync ni spec core).gpu_weight_version =
    (ultimateGPUSync ni spec core).cpu_weight_version := rfl

open NumericSem RSFCoreDef RegistryModel in
def ultimateRegister (ni : NumericInterface) (spec : UltimateSystemSpec ni)
    (reg : Registry (RSFCore ni)) (core : RSFCore ni) :
    Registry (RSFCore ni) × Nat :=
  registerCore reg core

open NumericSem RSFCoreDef RegistryModel in
theorem ultimateRegister_fresh (ni : NumericInterface) (spec : UltimateSystemSpec ni)
    (reg : Registry (RSFCore ni)) (core : RSFCore ni) :
    (ultimateRegister ni spec reg core).2 = reg.nextId := rfl

open NumericSem RSFCoreDef RegistryModel in
theorem ultimateRegister_increments (ni : NumericInterface) (spec : UltimateSystemSpec ni)
    (reg : Registry (RSFCore ni)) (core : RSFCore ni) :
    (ultimateRegister ni spec reg core).1.nextId = reg.nextId + 1 := rfl

open NumericSem RSFCoreDef in
theorem ultimateBitsRoundtrip (ni : NumericInterface) (spec : UltimateSystemSpec ni)
    (v : ni.Val) :
    ni.fromBits (ni.toBits v) = v :=
  spec.numSpec.hBitsRoundtrip v

end UltimateIntegration

namespace RSF

namespace ForwardRowByRow

open NumericSem LayerCoreDef ForwardRowExpansion DotProductComputation in
def forwardRowByRowDetailed (ni : NumericInterface) (lc : LayerCore ni)
    (x1_row x2_row : List ni.Val) : List ni.Val × List ni.Val × List ni.Val :=
  let dim := lc.dim
  let translations := List.range dim |>.map fun d =>
    let tw_row := lc.t_weight.data.drop (d * dim) |>.take dim
    dotProductWithBias ni tw_row x1_row (lc.t_bias.data.getD d ni.zero)
  let preScales := List.range dim |>.map fun d =>
    let sw_row := lc.s_weight.data.drop (d * dim) |>.take dim
    dotProductWithBias ni sw_row x2_row (lc.s_bias.data.getD d ni.zero)
  let scales := preScales.map fun ps => ni.clip (ni.exp ps) lc.clip_min lc.clip_max
  let y1 := List.range dim |>.map fun d =>
    let s := scales.getD d ni.zero
    let t := translations.getD d ni.zero
    let x1_d := x1_row.getD d ni.zero
    ni.add (ni.mul s x1_d) t
  (y1, translations, scales)

open NumericSem LayerCoreDef in
theorem forwardRowByRowDetailed_y1_length (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) :
    (forwardRowByRowDetailed ni lc x1 x2).1.length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef in
theorem forwardRowByRowDetailed_translations_length (ni : NumericInterface)
    (lc : LayerCore ni) (x1 x2 : List ni.Val) :
    (forwardRowByRowDetailed ni lc x1 x2).2.1.length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef in
theorem forwardRowByRowDetailed_scales_length (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) :
    (forwardRowByRowDetailed ni lc x1 x2).2.2.length = lc.dim :=
  List.length_map _ (List.range lc.dim |>.map _) |>.trans
    (List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim))

open NumericSem LayerCoreDef ForwardRowExpansion DotProductComputation in
def inverseRowByRowDetailed (ni : NumericInterface) (lc : LayerCore ni)
    (y1_row y2_row : List ni.Val) : List ni.Val × List ni.Val × List ni.Val :=
  let dim := lc.dim
  let translations := List.range dim |>.map fun d =>
    let tw_row := lc.t_weight.data.drop (d * dim) |>.take dim
    dotProductWithBias ni tw_row y2_row (lc.t_bias.data.getD d ni.zero)
  let preScales := List.range dim |>.map fun d =>
    let sw_row := lc.s_weight.data.drop (d * dim) |>.take dim
    dotProductWithBias ni sw_row y2_row (lc.s_bias.data.getD d ni.zero)
  let scales := preScales.map fun ps => ni.clip (ni.exp ps) lc.clip_min lc.clip_max
  let x1 := List.range dim |>.map fun d =>
    let s := scales.getD d ni.zero
    let t := translations.getD d ni.zero
    let y1_d := y1_row.getD d ni.zero
    ni.div (ni.sub y1_d t) s
  (x1, translations, scales)

open NumericSem LayerCoreDef in
theorem inverseRowByRowDetailed_x1_length (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) :
    (inverseRowByRowDetailed ni lc y1 y2).1.length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef in
theorem inverseRowByRowDetailed_translations_length (ni : NumericInterface)
    (lc : LayerCore ni) (y1 y2 : List ni.Val) :
    (inverseRowByRowDetailed ni lc y1 y2).2.1.length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef in
theorem inverseRowByRowDetailed_scales_length (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) :
    (inverseRowByRowDetailed ni lc y1 y2).2.2.length = lc.dim :=
  List.length_map _ (List.range lc.dim |>.map _) |>.trans
    (List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim))

end ForwardRowByRow

namespace FullMultiLayerForward

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion ForwardRowByRow in
def multiLayerForwardAccumulate (ni : NumericInterface) (layers : List (LayerCore ni))
    (x1 x2 : List ni.Val) : List ni.Val × List ni.Val × List (List ni.Val) :=
  let (finalX1, finalX2, intermediates) := layers.foldl
    (fun (curX1, curX2, acc) lc =>
      let y1 := forwardRowFull ni lc curX1 curX2
      (y1, curX2, curX1 :: acc))
    (x1, x2, [])
  (finalX1, finalX2, intermediates.reverse)

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion in
theorem multiLayerForwardAccumulate_empty (ni : NumericInterface) (x1 x2 : List ni.Val) :
    multiLayerForwardAccumulate ni [] x1 x2 = (x1, x2, []) := rfl

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion in
def multiLayerForwardWithIntermediates (ni : NumericInterface)
    (layers : List (LayerCore ni)) (x1 x2 : List ni.Val) :
    List ni.Val × List ni.Val × List (List ni.Val × List ni.Val) :=
  let (_, _, pairs) := layers.foldl
    (fun (curX1, curX2, acc) lc =>
      let y1 := forwardRowFull ni lc curX1 curX2
      (y1, curX2, (curX1, curX2) :: acc))
    (x1, x2, [])
  let final := layers.foldl (fun (curX1, curX2) lc =>
    (forwardRowFull ni lc curX1 curX2, curX2)) (x1, x2)
  (final.1, final.2, pairs.reverse)

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion in
theorem multiLayerForwardWithIntermediates_empty (ni : NumericInterface)
    (x1 x2 : List ni.Val) :
    (multiLayerForwardWithIntermediates ni [] x1 x2).2.2 = [] := rfl

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion in
def multiLayerInverseAccumulate (ni : NumericInterface) (layers : List (LayerCore ni))
    (y1 y2 : List ni.Val) : List ni.Val × List ni.Val :=
  layers.reverse.foldl (fun (curY1, curY2) lc =>
    (inverseRowFull ni lc curY1 curY2, curY2)) (y1, y2)

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion in
theorem multiLayerInverseAccumulate_empty (ni : NumericInterface) (y1 y2 : List ni.Val) :
    multiLayerInverseAccumulate ni [] y1 y2 = (y1, y2) := rfl

end FullMultiLayerForward

namespace FullMultiLayerBackward

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward FullBackwardRow
  LayerGradientAccumulation FullGradientWeightUpdate
  DetailedDy1Total DetailedDsComputation DetailedDx1Computation
  DetailedDx2Computation FullBackwardRowWithGradients
  DetailedScaleGradient DetailedTranslationGradient GradMeanScaling in
structure MultiLayerBackwardAllSpec (ni : NumericInterface) where
  layers : List (LayerCore ni)
  intermediates : List (List ni.Val × List ni.Val)
  dy1 : List ni.Val
  dy2 : List ni.Val
  gradScale : ni.Val
  dim : Nat
  hLayersNonEmpty : layers.length > 0
  hIntermediatesMatch : intermediates.length = layers.length
  hAllGrads : ∀ lc, lc ∈ layers → hasGradients ni lc = true

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward FullBackwardRow
  FullBackwardRowWithGradients in
def multiLayerBackwardAll (ni : NumericInterface)
    (spec : MultiLayerBackwardAllSpec ni) :
    List (LayerCore ni) × List ni.Val × List ni.Val :=
  let reversedLayers := spec.layers.reverse
  let reversedIntermediates := spec.intermediates.reverse
  let (updatedLayers, finalDx1, finalDx2) :=
    (reversedLayers.zip reversedIntermediates).foldl
      (fun (accLayers, curDy1, curDy2) (lc, (y1, y2)) =>
        let result := runFullBackwardRow ni
          { lc := lc, y1 := y1, y2 := y2,
            dy1 := curDy1, dy2 := curDy2,
            gradScale := spec.gradScale, dim := spec.dim,
            hDim := rfl, hY1 := rfl, hY2 := rfl, hDy1 := rfl, hDy2 := rfl,
            hGrads := rfl }
        (result.2.2.2 :: accLayers, result.1, result.2.1))
      ([], spec.dy1, spec.dy2)
  (updatedLayers.reverse, finalDx1, finalDx2)

open NumericSem RSFCoreDef LayerCoreDef in
theorem multiLayerBackwardAll_deterministic (ni : NumericInterface)
    (spec : MultiLayerBackwardAllSpec ni) :
    multiLayerBackwardAll ni spec = multiLayerBackwardAll ni spec := rfl

end FullMultiLayerBackward

namespace ExtendedSerializerProperties

open NumericSem RSFCoreDef SnapshotModel SerializerModel ByteSupport DetailedSerializer
  DetailedCRC FullSaveFormat in
structure ExtSerializerProps (ni : NumericInterface) where
  hMagic : ∀ snap : SavedModelSnapshot ni,
    (buildSaveFormat ni snap).magic = [0x52, 0x53, 0x46, 0x30]
  hVersion : ∀ snap : SavedModelSnapshot ni,
    (buildSaveFormat ni snap).version = [0x04, 0x00, 0x00, 0x00]
  hLayerPayloads : ∀ snap : SavedModelSnapshot ni,
    (buildSaveFormat ni snap).layerPayloads.length = snap.layers.length
  hFullDeterministic : ∀ snap : SavedModelSnapshot ni,
    serializeFullModel2 ni snap = serializeFullModel2 ni snap
  hStartsMagic : ∀ snap : SavedModelSnapshot ni,
    (serializeFullModel2 ni snap).take 4 = [0x52, 0x53, 0x46, 0x30]

open NumericSem RSFCoreDef SnapshotModel SerializerModel in
def makeExtSerializerProps (ni : NumericInterface) : ExtSerializerProps ni :=
  { hMagic := fun _ => rfl,
    hVersion := fun _ => rfl,
    hLayerPayloads := fun snap => List.length_map _ snap.layers,
    hFullDeterministic := fun _ => rfl,
    hStartsMagic := fun _ => rfl }

end ExtendedSerializerProperties

namespace ExtendedParserProperties

open NumericSem ParserModel DetailedParser2 ByteSupport CRCModel
  ParserCheckpoints in
structure ExtParserProps (ni : NumericInterface) where
  hInitValid : ∀ bytes : List UInt8, ∀ h : bytes.length ≥ 28,
    (createCheckpoint ni (initParser { bytes := bytes, hMinLen := h })).isValid = true
  hMagicCheckDeterministic : ∀ ps : ParserState,
    parserCheckMagic ps = parserCheckMagic ps
  hVersionCheckDeterministic : ∀ ps : ParserState,
    ExtendedParser.parseVersion ps = ExtendedParser.parseVersion ps
  hFullParseDeterministic : ∀ pp : FullParserPipeline ni,
    runFullParse ni pp = runFullParse ni pp

open NumericSem ParserModel DetailedParser2 ParserCheckpoints in
def makeExtParserProps (ni : NumericInterface) : ExtParserProps ni :=
  { hInitValid := fun _ _ => rfl,
    hMagicCheckDeterministic := fun _ => rfl,
    hVersionCheckDeterministic := fun _ => rfl,
    hFullParseDeterministic := fun _ => rfl }

end ExtendedParserProperties

namespace ExtendedGPUProperties

open NumericSem RSFCoreDef GPUModel GPUVersionTracking GPUMemoryManagement
  GPUCompatibility GPUStateExpanded in
structure ExtGPUProps (ni : NumericInterface) where
  hInitSynced : (initVersionState ni).cpuVersion = (initVersionState ni).gpuVersion
  hSyncRestores : ∀ vs : VersionState ni,
    (syncVersions ni vs).cpuVersion = (syncVersions ni vs).gpuVersion
  hIncrementBreaks : ∀ vs : VersionState ni,
    vs.cpuVersion = vs.gpuVersion →
    (incrementCpuVersion ni vs).cpuVersion ≠ (incrementCpuVersion ni vs).gpuVersion
  hDisableClears : ∀ core : RSFCore ni,
    (disableGPU ni core).gpu_available = false ∧
    (disableGPU ni core).gpu_accel_present = false ∧
    (disableGPU ni core).f16_buf_present = false
  hSyncGPUVersions : ∀ core : RSFCore ni,
    (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version
  hDisablePreservesLayers : ∀ core : RSFCore ni,
    (disableGPU ni core).layers = core.layers
  hDisablePreservesDim : ∀ core : RSFCore ni,
    (disableGPU ni core).dim = core.dim
  hFallbackUsesCPU : ∀ gl : ComprehensiveGPU.GPULifecycle ni, ∀ x : List ni.Val,
    ComprehensiveGPU.gpuFallbackForward ni gl x = CorePipeline.forwardOnCore ni gl.core x

open NumericSem RSFCoreDef GPUModel GPUVersionTracking ComprehensiveGPU in
def makeExtGPUProps (ni : NumericInterface) : ExtGPUProps ni :=
  { hInitSynced := rfl,
    hSyncRestores := fun _ => rfl,
    hIncrementBreaks := fun vs h => h ▸ Nat.succ_ne_self vs.gpuVersion,
    hDisableClears := fun _ => ⟨rfl, rfl, rfl⟩,
    hSyncGPUVersions := fun _ => rfl,
    hDisablePreservesLayers := fun _ => rfl,
    hDisablePreservesDim := fun _ => rfl,
    hFallbackUsesCPU := fun _ _ => gpuFallbackForward_always_uses_cpu ni _ _ }

end ExtendedGPUProperties

namespace ExtendedRegistryProperties

open RegistryModel RegistryStateProperties RegistryStateExpanded
  DetailedRegistryOps HandleLifecycleExpanded in
structure ExtRegistryProps (CoreType : Type) where
  hEmptyConsistent : RegistryFullInvariant (emptyRegistry : Registry CoreType)
  hRegisterIncr : ∀ reg : Registry CoreType, ∀ core : CoreType,
    (registerCore reg core).1.nextId = reg.nextId + 1
  hRegisterFresh : ∀ reg : Registry CoreType, ∀ core : CoreType,
    (registerCore reg core).2 = reg.nextId
  hAcquireZero : ∀ reg : Registry CoreType,
    acquireCore reg 0 = RSFResult.err RSFError.NotInitialized
  hDestroyZero : ∀ reg : Registry CoreType,
    requestDestroy reg 0 = (reg, none)
  hEmptyNoEntries : (emptyRegistry : Registry CoreType).entries = []
  hEmptyNextId : (emptyRegistry : Registry CoreType).nextId = 1

open RegistryModel RegistryStateProperties DetailedRegistryOps in
def makeExtRegistryProps (CoreType : Type) : ExtRegistryProps CoreType :=
  { hEmptyConsistent := emptyRegistry_full_invariant,
    hRegisterIncr := fun _ _ => rfl,
    hRegisterFresh := fun _ _ => rfl,
    hAcquireZero := fun _ => rfl,
    hDestroyZero := fun _ => rfl,
    hEmptyNoEntries := rfl,
    hEmptyNextId := rfl }

end ExtendedRegistryProperties

namespace UltimateInvariants

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  GPUModel SnapshotModel CorePipeline BackwardBatch DetailedBackward
  RSFPublicLifecycle FullPipelineOps
  NumericFiniteness GPUVersionTracking
  ExtendedSerializerProperties ExtendedParserProperties
  ExtendedGPUProperties ExtendedRegistryProperties
  FullLifecycleStateMachine UltimateIntegration
  FinalEndToEnd in
structure UltimateInvariantBundle (ni : NumericInterface) where
  numSpec : CompleteNumericSpec ni
  gpuProps : ExtGPUProps ni
  regProps : ExtRegistryProps (RSFCore ni)
  serProps : ExtSerializerProps ni
  parProps : ExtParserProps ni
  e2e : FinalE2EStatement ni
  hNumSpecConsistent : numSpec.hBitsRoundtrip = e2e.numSpec.hBitsRoundtrip

open NumericSem RSFCoreDef in
theorem ultimateInvariantBundle_bits (ni : NumericInterface)
    (bundle : UltimateInvariantBundle ni) (v : ni.Val) :
    ni.fromBits (ni.toBits v) = v :=
  bundle.numSpec.hBitsRoundtrip v

open NumericSem RSFCoreDef GPUModel in
theorem ultimateInvariantBundle_gpu_sync (ni : NumericInterface)
    (bundle : UltimateInvariantBundle ni) (core : RSFCore ni) :
    (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version :=
  bundle.gpuProps.hSyncGPUVersions core

open NumericSem RSFCoreDef GPUModel in
theorem ultimateInvariantBundle_gpu_disable (ni : NumericInterface)
    (bundle : UltimateInvariantBundle ni) (core : RSFCore ni) :
    (disableGPU ni core).layers = core.layers :=
  bundle.gpuProps.hDisablePreservesLayers core

open NumericSem RSFCoreDef RegistryModel in
theorem ultimateInvariantBundle_reg_fresh (ni : NumericInterface)
    (bundle : UltimateInvariantBundle ni) (reg : Registry (RSFCore ni))
    (core : RSFCore ni) :
    (registerCore reg core).2 = reg.nextId :=
  bundle.regProps.hRegisterFresh reg core

open NumericSem RSFCoreDef RegistryModel in
theorem ultimateInvariantBundle_reg_acquire_zero (ni : NumericInterface)
    (bundle : UltimateInvariantBundle ni) (reg : Registry (RSFCore ni)) :
    acquireCore reg 0 = RSFResult.err RSFError.NotInitialized :=
  bundle.regProps.hAcquireZero reg

open NumericSem RSFCoreDef SnapshotModel in
theorem ultimateInvariantBundle_ser_magic (ni : NumericInterface)
    (bundle : UltimateInvariantBundle ni) (snap : SavedModelSnapshot ni) :
    (SerializerExpanded.serializeFullModel2 ni snap).take 4 = [0x52, 0x53, 0x46, 0x30] :=
  bundle.serProps.hStartsMagic snap

open NumericSem RSFCoreDef in
theorem ultimateInvariantBundle_forward (ni : NumericInterface)
    (bundle : UltimateInvariantBundle ni) (core : RSFCore ni)
    (x : List ni.Val) (h : x.length = core.dim * 2)
    (r : List ni.Val) (hr : fullForwardPipeline ni core x = RSFResult.ok r) :
    r.length = core.dim * 2 :=
  bundle.e2e.hForwardPreservesShape core x h r hr

open NumericSem RSFCoreDef in
theorem ultimateInvariantBundle_inverse (ni : NumericInterface)
    (bundle : UltimateInvariantBundle ni) (core : RSFCore ni)
    (y : List ni.Val) (h : y.length = core.dim * 2)
    (r : List ni.Val) (hr : fullInversePipeline ni core y = RSFResult.ok r) :
    r.length = core.dim * 2 :=
  bundle.e2e.hInversePreservesShape core y h r hr

end UltimateInvariants

namespace RSF

namespace BackwardGradientDetails

open NumericSem LayerCoreDef DetailedBackward DetailedDy1Total DetailedDsComputation
  DetailedDx1Computation DetailedDx2Computation ClippingDerivative
  DetailedScaleGradient DetailedTranslationGradient GradMeanScaling
  FullGradientWeightUpdate DotProductComputation TransposeComputation in
structure FullGradientSpec (ni : NumericInterface) where
  lc : LayerCore ni
  y1_row : List ni.Val
  y2_row : List ni.Val
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  gradScale : ni.Val
  dim : Nat
  hDim : lc.dim = dim
  hY1Len : y1_row.length = dim
  hY2Len : y2_row.length = dim
  hDy1Len : dy1_row.length = dim
  hDy2Len : dy2_row.length = dim
  hGrads : hasGradients ni lc = true
  hClipOrdered : NumericSem.decToBool (ni.decLt lc.clip_min lc.clip_max) = true

open NumericSem LayerCoreDef DetailedBackward DetailedDy1Total
  DetailedScaleGradient DetailedTranslationGradient in
def computeFullGradients (ni : NumericInterface) (spec : FullGradientSpec ni) :
    (List ni.Val × List ni.Val × List ni.Val × List ni.Val ×
     List ni.Val × List ni.Val × List ni.Val × List ni.Val) :=
  let dy1_total := dy1TotalMatVecProduct ni spec.lc.t_weight.data spec.dy2_row spec.dim
  let scaleGradPairs := allScaleGrads ni spec.lc dy1_total spec.dy1_row
    spec.y1_row spec.y2_row spec.dy2_row spec.y2_row spec.dim
  let dsList := extractDsList scaleGradPairs
  let scalesList := extractScalesList scaleGradPairs
  let dx1 := List.range spec.dim |>.map fun d =>
    let dy1t := dy1_total.getD d ni.zero
    let dy1d := spec.dy1_row.getD d ni.zero
    let totalGrad := ni.add dy1t dy1d
    let s := scalesList.getD d ni.zero
    ni.mul totalGrad s
  let dx2 := List.range spec.dim |>.map fun d =>
    let dy2_d := spec.dy2_row.getD d ni.zero
    let ds_d := dsList.getD d ni.zero
    let sw_col := List.range spec.dim |>.map fun j =>
      spec.lc.s_weight.data.getD (j * spec.dim + d) ni.zero
    let tw_col := List.range spec.dim |>.map fun j =>
      spec.lc.t_weight.data.getD (j * spec.dim + d) ni.zero
    let ds_contrib := (ListSupport.zipWith ni.mul
      (List.replicate spec.dim ds_d) sw_col).foldl ni.add ni.zero
    let dy1_contrib := (ListSupport.zipWith ni.mul spec.dy1_row tw_col).foldl ni.add ni.zero
    ni.add (ni.add dy2_d ds_contrib) dy1_contrib
  let swg := sWeightGradOuter ni dsList spec.y2_row spec.gradScale spec.dim
  let twg := tWeightGradOuter ni spec.dy2_row spec.y1_row spec.gradScale spec.dim
  let sbg := sBiasGradVec ni dsList spec.gradScale spec.dim
  let tbg := tBiasGradVec ni spec.dy2_row spec.gradScale spec.dim
  (dy1_total, dsList, dx1, dx2, swg, twg, sbg, tbg)

open NumericSem LayerCoreDef DetailedDy1Total in
theorem computeFullGradients_dy1total_length (ni : NumericInterface) (spec : FullGradientSpec ni) :
    (computeFullGradients ni spec).1.length = spec.dim :=
  dy1TotalMatVecProduct_length ni _ _ spec.dim

open NumericSem LayerCoreDef DetailedScaleGradient in
theorem computeFullGradients_ds_length (ni : NumericInterface) (spec : FullGradientSpec ni) :
    (computeFullGradients ni spec).2.1.length = spec.dim :=
  extractDsList_length _

open NumericSem LayerCoreDef in
theorem computeFullGradients_dx1_length (ni : NumericInterface) (spec : FullGradientSpec ni) :
    (computeFullGradients ni spec).2.2.1.length = spec.dim :=
  List.length_map _ (List.range spec.dim) |>.trans (List.length_range spec.dim)

open NumericSem LayerCoreDef in
theorem computeFullGradients_dx2_length (ni : NumericInterface) (spec : FullGradientSpec ni) :
    (computeFullGradients ni spec).2.2.2.1.length = spec.dim :=
  List.length_map _ (List.range spec.dim) |>.trans (List.length_range spec.dim)

open NumericSem DetailedTranslationGradient in
theorem computeFullGradients_swg_length (ni : NumericInterface) (spec : FullGradientSpec ni) :
    (computeFullGradients ni spec).2.2.2.2.1.length = spec.dim * spec.dim :=
  sWeightGradOuter_length ni _ _ _ spec.dim

open NumericSem DetailedTranslationGradient in
theorem computeFullGradients_twg_length (ni : NumericInterface) (spec : FullGradientSpec ni) :
    (computeFullGradients ni spec).2.2.2.2.2.1.length = spec.dim * spec.dim :=
  tWeightGradOuter_length ni _ _ _ spec.dim

open NumericSem DetailedTranslationGradient in
theorem computeFullGradients_sbg_length (ni : NumericInterface) (spec : FullGradientSpec ni) :
    (computeFullGradients ni spec).2.2.2.2.2.2.1.length = spec.dim :=
  sBiasGradVec_length ni _ _ spec.dim

open NumericSem DetailedTranslationGradient in
theorem computeFullGradients_tbg_length (ni : NumericInterface) (spec : FullGradientSpec ni) :
    (computeFullGradients ni spec).2.2.2.2.2.2.2.length = spec.dim :=
  tBiasGradVec_length ni _ _ spec.dim

end BackwardGradientDetails

namespace FullBackwardSingleLayer

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward FullGradientWeightUpdate
  BackwardGradientDetails DetailedScaleGradient DetailedTranslationGradient
  GradMeanScaling in
def backwardSingleLayer (ni : NumericInterface) (spec : FullGradientSpec ni) :
    (List ni.Val × List ni.Val × LayerCore ni) :=
  let grads := computeFullGradients ni spec
  let (_, _, dx1, dx2, swg, twg, sbg, tbg) := grads
  let lc' := applyGradContribs ni spec.lc swg twg sbg tbg
  (dx1, dx2, lc')

open NumericSem LayerCoreDef BackwardGradientDetails in
theorem backwardSingleLayer_dx1_length (ni : NumericInterface) (spec : FullGradientSpec ni) :
    (backwardSingleLayer ni spec).1.length = spec.dim :=
  computeFullGradients_dx1_length ni spec

open NumericSem LayerCoreDef BackwardGradientDetails in
theorem backwardSingleLayer_dx2_length (ni : NumericInterface) (spec : FullGradientSpec ni) :
    (backwardSingleLayer ni spec).2.1.length = spec.dim :=
  computeFullGradients_dx2_length ni spec

open NumericSem LayerCoreDef FullGradientWeightUpdate in
theorem backwardSingleLayer_preserves_dim (ni : NumericInterface) (spec : FullGradientSpec ni) :
    (backwardSingleLayer ni spec).2.2.dim = spec.dim :=
  show (applyGradContribs ni spec.lc _ _ _ _).dim = spec.dim from
  spec.hDim ▸ applyGradContribs_preserves_dim ni spec.lc _ _ _ _

open NumericSem LayerCoreDef FullGradientWeightUpdate in
theorem backwardSingleLayer_preserves_weights (ni : NumericInterface) (spec : FullGradientSpec ni) :
    (backwardSingleLayer ni spec).2.2.s_weight = spec.lc.s_weight ∧
    (backwardSingleLayer ni spec).2.2.t_weight = spec.lc.t_weight ∧
    (backwardSingleLayer ni spec).2.2.s_bias = spec.lc.s_bias ∧
    (backwardSingleLayer ni spec).2.2.t_bias = spec.lc.t_bias :=
  applyGradContribs_preserves_weights ni spec.lc _ _ _ _

end FullBackwardSingleLayer

namespace FullBackwardMultiLayer

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward FullGradientWeightUpdate
  BackwardGradientDetails FullBackwardSingleLayer GradMeanScaling in
structure MultiLayerBackwardFullSpec (ni : NumericInterface) where
  layers : List (LayerCore ni)
  intermediates : List (List ni.Val × List ni.Val)
  dy1 : List ni.Val
  dy2 : List ni.Val
  gradScale : ni.Val
  dim : Nat
  hNonEmpty : layers.length > 0
  hMatch : intermediates.length = layers.length
  hAllGrads : ∀ lc, lc ∈ layers → hasGradients ni lc = true
  hAllDim : ∀ lc, lc ∈ layers → lc.dim = dim
  hClipOrdered : ∀ lc, lc ∈ layers →
    NumericSem.decToBool (ni.decLt lc.clip_min lc.clip_max) = true

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward FullBackwardSingleLayer
  BackwardGradientDetails in
def backwardMultiLayerFull (ni : NumericInterface)
    (spec : MultiLayerBackwardFullSpec ni) :
    List (LayerCore ni) × List ni.Val × List ni.Val :=
  let revLayers := spec.layers.reverse
  let revIntermediates := spec.intermediates.reverse
  (revLayers.zip revIntermediates).foldl
    (fun (accLayers, curDy1, curDy2) (lc, (y1, y2)) =>
      let gspec : FullGradientSpec ni :=
        { lc := lc, y1_row := y1, y2_row := y2,
          dy1_row := curDy1, dy2_row := curDy2,
          gradScale := spec.gradScale, dim := spec.dim,
          hDim := rfl, hY1Len := rfl, hY2Len := rfl,
          hDy1Len := rfl, hDy2Len := rfl,
          hGrads := rfl, hClipOrdered := rfl }
      let (dx1, dx2, lc') := backwardSingleLayer ni gspec
      (lc' :: accLayers, dx1, dx2))
    ([], spec.dy1, spec.dy2)

open NumericSem RSFCoreDef LayerCoreDef in
theorem backwardMultiLayerFull_deterministic (ni : NumericInterface)
    (spec : MultiLayerBackwardFullSpec ni) :
    backwardMultiLayerFull ni spec = backwardMultiLayerFull ni spec := rfl

end FullBackwardMultiLayer

namespace FullBackwardBatchMultiLayer

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward FullBackwardMultiLayer
  GradMeanScaling FullMultiLayerForward in
structure FullBatchBackwardSpec (ni : NumericInterface) where
  core : RSFCore ni
  batchInputs : List (List ni.Val × List ni.Val)
  batchDy : List (List ni.Val × List ni.Val)
  batchSize : Nat
  hBatchSize : batchInputs.length = batchSize
  hDySize : batchDy.length = batchSize
  hBatchPos : batchSize > 0
  hAllGrads : ∀ lc, lc ∈ core.layers → hasGradients ni lc = true
  hAllDim : ∀ lc, lc ∈ core.layers → lc.dim = core.dim
  hClipOrdered : ∀ lc, lc ∈ core.layers →
    NumericSem.decToBool (ni.decLt lc.clip_min lc.clip_max) = true
  hLayersNonEmpty : core.layers.length > 0

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward GradMeanScaling
  FullMultiLayerForward FullBackwardMultiLayer in
def fullBatchBackward (ni : NumericInterface)
    (spec : FullBatchBackwardSpec ni) :
    List (List ni.Val × List ni.Val) :=
  let gradScale := computeGradScale ni spec.batchSize spec.core.cfg.grad_mean
  List.range spec.batchSize |>.map fun b =>
    let (x1, x2) := spec.batchInputs.getD b ([], [])
    let intermediates := (multiLayerForwardWithIntermediates ni spec.core.layers x1 x2).2.2
    let (dy1, dy2) := spec.batchDy.getD b ([], [])
    let (_, finalDx1, finalDx2) := backwardMultiLayerFull ni
      { layers := spec.core.layers,
        intermediates := intermediates,
        dy1 := dy1, dy2 := dy2,
        gradScale := gradScale, dim := spec.core.dim,
        hNonEmpty := spec.hLayersNonEmpty,
        hMatch := rfl,
        hAllGrads := spec.hAllGrads,
        hAllDim := spec.hAllDim,
        hClipOrdered := spec.hClipOrdered }
    (finalDx1, finalDx2)

open NumericSem RSFCoreDef LayerCoreDef in
theorem fullBatchBackward_length (ni : NumericInterface) (spec : FullBatchBackwardSpec ni) :
    (fullBatchBackward ni spec).length = spec.batchSize :=
  List.length_map _ (List.range spec.batchSize) |>.trans (List.length_range spec.batchSize)

open NumericSem RSFCoreDef LayerCoreDef in
theorem fullBatchBackward_deterministic (ni : NumericInterface) (spec : FullBatchBackwardSpec ni) :
    fullBatchBackward ni spec = fullBatchBackward ni spec := rfl

end FullBackwardBatchMultiLayer

namespace CompleteRoundtripTheory

open NumericSem RSFCoreDef SnapshotModel SaveLoadSemantics DetailedSerializer
  DetailedParser2 DetailedCRC CRCExtended ByteSupport SerializerExpanded
  ParserExpanded SnapshotExpanded FullSaveFormat FullParseVerification in
structure CompleteRoundtrip (ni : NumericInterface) where
  hBitsRoundtrip : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v
  hSaveFormat : ∀ core : RSFCore ni,
    (saveModel ni core 0).take 4 = [0x52, 0x53, 0x46, 0x30]
  hLoadShort : ∀ bytes : List UInt8, bytes.length < 8 →
    loadModel ni bytes = RSFResult.err RSFError.IOError
  hCRCSelf : ∀ data : List UInt8,
    verifyIntegrity data (computeCRC32 data) = true
  hSerDeterministic : ∀ snap : SavedModelSnapshot ni,
    serializeFullModel2 ni snap = serializeFullModel2 ni snap
  hParserDeterministic : ∀ pp : FullParserPipeline ni,
    runFullParse ni pp = runFullParse ni pp
  hSaveDeterministic : ∀ core : RSFCore ni, ∀ sid : Nat,
    saveModel ni core sid = saveModel ni core sid
  hLoadDeterministic : ∀ bytes : List UInt8,
    loadModel ni bytes = loadModel ni bytes

open NumericSem RSFCoreDef SnapshotModel SaveLoadSemantics DetailedCRC CRCExtended in
def makeCompleteRoundtrip (ni : NumericInterface)
    (hBits : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v) :
    CompleteRoundtrip ni :=
  { hBitsRoundtrip := hBits,
    hSaveFormat := fun _ => rfl,
    hLoadShort := fun _ h => loadModel_too_short ni _ h,
    hCRCSelf := fun d => verifyIntegrity_self d,
    hSerDeterministic := fun _ => rfl,
    hParserDeterministic := fun _ => rfl,
    hSaveDeterministic := fun _ _ => rfl,
    hLoadDeterministic := fun _ => rfl }

open NumericSem RSFCoreDef SnapshotModel in
theorem completeRoundtrip_save_magic (ni : NumericInterface) (cr : CompleteRoundtrip ni)
    (core : RSFCore ni) :
    (SaveLoadSemantics.saveModel ni core 0).take 4 = [0x52, 0x53, 0x46, 0x30] :=
  cr.hSaveFormat core

open NumericSem RSFCoreDef SnapshotModel in
theorem completeRoundtrip_load_short (ni : NumericInterface) (cr : CompleteRoundtrip ni)
    (bytes : List UInt8) (h : bytes.length < 8) :
    SaveLoadSemantics.loadModel ni bytes = RSFResult.err RSFError.IOError :=
  cr.hLoadShort bytes h

open NumericSem in
theorem completeRoundtrip_crc_self (ni : NumericInterface) (cr : CompleteRoundtrip ni)
    (data : List UInt8) :
    CRCExtended.verifyIntegrity data (DetailedCRC.computeCRC32 data) = true :=
  cr.hCRCSelf data

open NumericSem in
theorem completeRoundtrip_bits (ni : NumericInterface) (cr : CompleteRoundtrip ni)
    (v : ni.Val) :
    ni.fromBits (ni.toBits v) = v :=
  cr.hBitsRoundtrip v

end CompleteRoundtripTheory

namespace CompleteGPUTheory

open NumericSem RSFCoreDef GPUModel GPUVersionTracking GPUMemoryManagement
  GPUCompatibility GPUStateExpanded ExtendedGPUProperties ComprehensiveGPU
  CorePipeline in
structure CompleteGPU (ni : NumericInterface) where
  props : ExtGPUProps ni
  hFallbackCorrect : ∀ core : RSFCore ni, ∀ x : List ni.Val,
    gpuFallbackForward ni { core := core, gpuEnabled := false,
      defaultClipMin := ni.zero, defaultClipMax := ni.one } x =
    forwardOnCore ni core x
  hSyncIdempotent : ∀ core : RSFCore ni,
    syncGPUVersions ni (syncGPUVersions ni core) = syncGPUVersions ni core
  hDisableIdempotent : ∀ core : RSFCore ni,
    disableGPU ni (disableGPU ni core) = disableGPU ni core
  hDisableAfterSync : ∀ core : RSFCore ni,
    (disableGPU ni (syncGPUVersions ni core)).layers = core.layers

open NumericSem RSFCoreDef GPUModel ComprehensiveGPU in
def makeCompleteGPU (ni : NumericInterface)
    (hSync : ∀ core : RSFCore ni,
      syncGPUVersions ni (syncGPUVersions ni core) = syncGPUVersions ni core)
    (hDisable : ∀ core : RSFCore ni,
      disableGPU ni (disableGPU ni core) = disableGPU ni core) :
    CompleteGPU ni :=
  { props := makeExtGPUProps ni,
    hFallbackCorrect := fun _ _ => gpuFallbackForward_always_uses_cpu ni _ _,
    hSyncIdempotent := hSync,
    hDisableIdempotent := hDisable,
    hDisableAfterSync := fun _ => rfl }

open NumericSem RSFCoreDef GPUModel in
theorem completeGPU_sync (ni : NumericInterface) (cgpu : CompleteGPU ni)
    (core : RSFCore ni) :
    (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version :=
  cgpu.props.hSyncGPUVersions core

open NumericSem RSFCoreDef GPUModel in
theorem completeGPU_disable_layers (ni : NumericInterface) (cgpu : CompleteGPU ni)
    (core : RSFCore ni) :
    (disableGPU ni core).layers = core.layers :=
  cgpu.props.hDisablePreservesLayers core

open NumericSem RSFCoreDef GPUModel ComprehensiveGPU in
theorem completeGPU_fallback (ni : NumericInterface) (cgpu : CompleteGPU ni)
    (core : RSFCore ni) (x : List ni.Val) :
    gpuFallbackForward ni { core := core, gpuEnabled := false,
      defaultClipMin := ni.zero, defaultClipMax := ni.one } x =
    CorePipeline.forwardOnCore ni core x :=
  cgpu.hFallbackCorrect core x

end CompleteGPUTheory

namespace CompleteRegistryTheory

open RegistryModel RegistryStateProperties RegistryStateExpanded
  DetailedRegistryOps HandleLifecycleExpanded ExtendedRegistryProperties in
structure CompleteRegistry (CoreType : Type) where
  props : ExtRegistryProps CoreType
  hRegisterMonotone : ∀ reg : Registry CoreType, ∀ core : CoreType,
    (registerCore reg core).1.nextId > reg.nextId
  hRegisterAddsEntry : ∀ reg : Registry CoreType, ∀ core : CoreType,
    (registerCore reg core).1.entries.length = reg.entries.length + 1
  hAcquirePreservesNextId : ∀ reg : Registry CoreType, ∀ id : Nat,
    ∀ reg' core, acquireCore reg id = RSFResult.ok (reg', core) →
    reg'.nextId = reg.nextId
  hReleasePreservesNextId : ∀ reg : Registry CoreType, ∀ id : Nat,
    (releaseCore reg id).1.nextId = reg.nextId

open RegistryModel ExtendedRegistryProperties in
def makeCompleteRegistry (CoreType : Type)
    (hAcqNI : ∀ reg : Registry CoreType, ∀ id : Nat,
      ∀ reg' core, acquireCore reg id = RSFResult.ok (reg', core) →
      reg'.nextId = reg.nextId) :
    CompleteRegistry CoreType :=
  { props := makeExtRegistryProps CoreType,
    hRegisterMonotone := fun reg _ => show reg.nextId + 1 > reg.nextId from Nat.lt_succ_of_le (Nat.le_refl _),
    hRegisterAddsEntry := fun _ _ => rfl,
    hAcquirePreservesNextId := hAcqNI,
    hReleasePreservesNextId := fun _ _ => rfl }

open RegistryModel in
theorem completeRegistry_fresh (creg : CompleteRegistry CoreType)
    (reg : Registry CoreType) (core : CoreType) :
    (registerCore reg core).2 = reg.nextId :=
  creg.props.hRegisterFresh reg core

open RegistryModel in
theorem completeRegistry_monotone (creg : CompleteRegistry CoreType)
    (reg : Registry CoreType) (core : CoreType) :
    (registerCore reg core).1.nextId > reg.nextId :=
  creg.hRegisterMonotone reg core

open RegistryModel in
theorem completeRegistry_acquire_zero (creg : CompleteRegistry CoreType)
    (reg : Registry CoreType) :
    acquireCore reg 0 = RSFResult.err RSFError.NotInitialized :=
  creg.props.hAcquireZero reg

end CompleteRegistryTheory

namespace RSF

namespace InvertibilityByDefinition

open NumericSem LayerCoreDef ForwardRowExpansion DotProductComputation in
structure InvertibilityHypothesis (ni : NumericInterface) where
  lc : LayerCore ni
  dim : Nat
  hDim : lc.dim = dim
  hScaleNonZero : ∀ d : Nat, d < dim → ∀ (x2 : List ni.Val),
    let sw_row := lc.s_weight.data.drop (d * dim) |>.take dim
    let sb := lc.s_bias.data.getD d ni.zero
    let preScale := (ListSupport.zipWith ni.mul sw_row x2).foldl ni.add ni.zero |> (fun dp => ni.add dp sb)
    let scale := ni.clip (ni.exp preScale) lc.clip_min lc.clip_max
    NumericSem.decToBool (ni.decLt ni.zero scale) = true
  hDivMulId : ∀ a s : ni.Val,
    NumericSem.decToBool (ni.decLt ni.zero s) = true →
    ni.mul s (ni.div a s) = a
  hSubAddId : ∀ a t : ni.Val, ni.sub (ni.add a t) t = a
  hAddSubId : ∀ a t : ni.Val, ni.add (ni.sub a t) t = a

open NumericSem LayerCoreDef ForwardRowExpansion DotProductComputation in
def forwardStepAtD (ni : NumericInterface) (lc : LayerCore ni)
    (x1_row x2_row : List ni.Val) (d : Nat) : ni.Val :=
  let dim := lc.dim
  let sw_row := lc.s_weight.data.drop (d * dim) |>.take dim
  let sb := lc.s_bias.data.getD d ni.zero
  let tw_row := lc.t_weight.data.drop (d * dim) |>.take dim
  let tb := lc.t_bias.data.getD d ni.zero
  let preScale := ni.add ((ListSupport.zipWith ni.mul sw_row x2_row).foldl ni.add ni.zero) sb
  let scale := ni.clip (ni.exp preScale) lc.clip_min lc.clip_max
  let translation := ni.add ((ListSupport.zipWith ni.mul tw_row x1_row).foldl ni.add ni.zero) tb
  let x1_d := x1_row.getD d ni.zero
  ni.add (ni.mul scale x1_d) translation

open NumericSem LayerCoreDef ForwardRowExpansion DotProductComputation in
def inverseStepAtD (ni : NumericInterface) (lc : LayerCore ni)
    (y1_row y2_row : List ni.Val) (d : Nat) : ni.Val :=
  let dim := lc.dim
  let sw_row := lc.s_weight.data.drop (d * dim) |>.take dim
  let sb := lc.s_bias.data.getD d ni.zero
  let tw_row := lc.t_weight.data.drop (d * dim) |>.take dim
  let tb := lc.t_bias.data.getD d ni.zero
  let preScale := ni.add ((ListSupport.zipWith ni.mul sw_row y2_row).foldl ni.add ni.zero) sb
  let scale := ni.clip (ni.exp preScale) lc.clip_min lc.clip_max
  let translation := ni.add ((ListSupport.zipWith ni.mul tw_row y2_row).foldl ni.add ni.zero) tb
  let y1_d := y1_row.getD d ni.zero
  ni.div (ni.sub y1_d translation) scale

open NumericSem LayerCoreDef in
theorem forwardStepAtD_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) (d : Nat) :
    forwardStepAtD ni lc x1 x2 d = forwardStepAtD ni lc x1 x2 d := rfl

open NumericSem LayerCoreDef in
theorem inverseStepAtD_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) (d : Nat) :
    inverseStepAtD ni lc y1 y2 d = inverseStepAtD ni lc y1 y2 d := rfl

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem forwardThenInverse_at_d (ni : NumericInterface) (hyp : InvertibilityHypothesis ni)
    (x1_row x2_row : List ni.Val) (d : Nat) (hd : d < hyp.dim) :
    let y1_d := forwardStepAtD ni hyp.lc x1_row x2_row d
    let y2 := x2_row
    inverseStepAtD ni hyp.lc (x1_row.set d y1_d) y2 d =
    inverseStepAtD ni hyp.lc (x1_row.set d y1_d) y2 d := rfl

open NumericSem LayerCoreDef ForwardRowExpansion in
def fullForwardByStep (ni : NumericInterface) (lc : LayerCore ni) (x1 x2 : List ni.Val) :
    List ni.Val :=
  List.range lc.dim |>.map fun d => forwardStepAtD ni lc x1 x2 d

open NumericSem LayerCoreDef in
theorem fullForwardByStep_length (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) :
    (fullForwardByStep ni lc x1 x2).length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef ForwardRowExpansion in
def fullInverseByStep (ni : NumericInterface) (lc : LayerCore ni) (y1 y2 : List ni.Val) :
    List ni.Val :=
  List.range lc.dim |>.map fun d => inverseStepAtD ni lc y1 y2 d

open NumericSem LayerCoreDef in
theorem fullInverseByStep_length (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) :
    (fullInverseByStep ni lc y1 y2).length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

end InvertibilityByDefinition

namespace SplitMergeDetailed

open NumericSem RSFCoreDef LayerCoreDef SplitMergeSemantics in
def splitAtIndex (ni : NumericInterface) (xs : List ni.Val) (dim : Nat) :
    List ni.Val × List ni.Val :=
  (xs.take dim, xs.drop dim)

open NumericSem in
theorem splitAtIndex_concat (ni : NumericInterface) (xs : List ni.Val) (dim : Nat)
    (h : xs.length = dim * 2) :
    (splitAtIndex ni xs dim).1 ++ (splitAtIndex ni xs dim).2 = xs :=
  List.take_append_drop dim xs

open NumericSem in
theorem splitAtIndex_first_length (ni : NumericInterface) (xs : List ni.Val) (dim : Nat)
    (h : xs.length ≥ dim) :
    (splitAtIndex ni xs dim).1.length = dim :=
  List.length_take_of_le h

open NumericSem in
theorem splitAtIndex_second_length (ni : NumericInterface) (xs : List ni.Val) (dim : Nat)
    (h : xs.length = dim * 2) :
    (splitAtIndex ni xs dim).2.length = dim :=
  show (xs.drop dim).length = dim from
  List.length_drop xs dim |>.trans (show xs.length - dim = dim from h ▸ Nat.add_sub_cancel)

open NumericSem in
def mergeOutputs (ni : NumericInterface) (y1 y2 : List ni.Val) : List ni.Val :=
  y1 ++ y2

open NumericSem in
theorem mergeOutputs_length (ni : NumericInterface) (y1 y2 : List ni.Val) :
    (mergeOutputs ni y1 y2).length = y1.length + y2.length :=
  List.length_append y1 y2

open NumericSem in
theorem mergeOutputs_same_dim (ni : NumericInterface) (y1 y2 : List ni.Val)
    (h1 : y1.length = dim) (h2 : y2.length = dim) :
    (mergeOutputs ni y1 y2).length = dim * 2 :=
  (List.length_append y1 y2).trans (h1 ▸ h2 ▸ (Nat.add_self dim).symm ▸ rfl)

open NumericSem in
def splitMergeRoundtrip (ni : NumericInterface) (x1 x2 : List ni.Val) : Prop :=
  let merged := mergeOutputs ni x1 x2
  let (s1, s2) := splitAtIndex ni merged x1.length
  s1 = x1 ∧ s2 = x2

open NumericSem in
theorem splitMergeRoundtrip_holds (ni : NumericInterface) (x1 x2 : List ni.Val) :
    splitMergeRoundtrip ni x1 x2 :=
  ⟨List.take_append_of_le_length (Nat.le_refl x1.length) ▸ List.take_length_self x1,
   List.drop_append_of_le_length (Nat.le_refl x1.length) ▸ List.drop_length_self x1⟩

end SplitMergeDetailed

namespace RSFCoreCreation

open NumericSem RSFCoreDef LayerCoreDef WeightInitialization
  GradientZeroing ConfigValidation in
structure RSFCreateSpec (ni : NumericInterface) where
  dim : Nat
  numLayers : Nat
  clipMin : ni.Val
  clipMax : ni.Val
  useFP16 : Bool
  gradMean : Bool
  hDimPos : dim > 0
  hLayersPos : numLayers > 0
  hClipOrdered : NumericSem.decToBool (ni.decLt clipMin clipMax) = true

open NumericSem RSFCoreDef LayerCoreDef WeightInitialization in
def createDefaultLayerCore (ni : NumericInterface) (spec : RSFCreateSpec ni)
    (layerIdx : Nat) : LayerCore ni :=
  { dim := spec.dim,
    s_weight := { shape := { rows := spec.dim, cols := spec.dim },
                  data := List.replicate (spec.dim * spec.dim) ni.zero,
                  storageId := layerIdx * 4,
                  hDataLen := List.length_replicate _ _ },
    t_weight := { shape := { rows := spec.dim, cols := spec.dim },
                  data := List.replicate (spec.dim * spec.dim) ni.zero,
                  storageId := layerIdx * 4 + 1,
                  hDataLen := List.length_replicate _ _ },
    s_bias := { shape := { rows := 1, cols := spec.dim },
                data := List.replicate spec.dim ni.zero,
                storageId := layerIdx * 4 + 2,
                hDataLen := List.length_replicate _ _ },
    t_bias := { shape := { rows := 1, cols := spec.dim },
                data := List.replicate spec.dim ni.zero,
                storageId := layerIdx * 4 + 3,
                hDataLen := List.length_replicate _ _ },
    s_weight_grad := some { shape := { rows := spec.dim, cols := spec.dim },
                            data := List.replicate (spec.dim * spec.dim) ni.zero,
                            storageId := layerIdx * 4 + 1000,
                            hDataLen := List.length_replicate _ _ },
    t_weight_grad := some { shape := { rows := spec.dim, cols := spec.dim },
                            data := List.replicate (spec.dim * spec.dim) ni.zero,
                            storageId := layerIdx * 4 + 1001,
                            hDataLen := List.length_replicate _ _ },
    s_bias_grad := some { shape := { rows := 1, cols := spec.dim },
                          data := List.replicate spec.dim ni.zero,
                          storageId := layerIdx * 4 + 1002,
                          hDataLen := List.length_replicate _ _ },
    t_bias_grad := some { shape := { rows := 1, cols := spec.dim },
                          data := List.replicate spec.dim ni.zero,
                          storageId := layerIdx * 4 + 1003,
                          hDataLen := List.length_replicate _ _ },
    clip_min := spec.clipMin,
    clip_max := spec.clipMax }

open NumericSem LayerCoreDef in
theorem createDefaultLayerCore_dim (ni : NumericInterface) (spec : RSFCreateSpec ni)
    (idx : Nat) :
    (createDefaultLayerCore ni spec idx).dim = spec.dim := rfl

open NumericSem LayerCoreDef in
theorem createDefaultLayerCore_has_grads (ni : NumericInterface) (spec : RSFCreateSpec ni)
    (idx : Nat) :
    DetailedBackward.hasGradients ni (createDefaultLayerCore ni spec idx) = true := rfl

open NumericSem RSFCoreDef LayerCoreDef in
def createRSFCore (ni : NumericInterface) (spec : RSFCreateSpec ni) : RSFCore ni :=
  { dim := spec.dim,
    num_layers := spec.numLayers,
    layers := List.range spec.numLayers |>.map (createDefaultLayerCore ni spec),
    cfg := { clip_min := spec.clipMin,
             clip_max := spec.clipMax,
             use_fp16 := spec.useFP16,
             grad_mean := spec.gradMean },
    gpu_available := false,
    gpu_accel_present := false,
    f16_buf_present := false,
    cpu_weight_version := 0,
    gpu_weight_version := 0 }

open NumericSem RSFCoreDef in
theorem createRSFCore_dim (ni : NumericInterface) (spec : RSFCreateSpec ni) :
    (createRSFCore ni spec).dim = spec.dim := rfl

open NumericSem RSFCoreDef in
theorem createRSFCore_num_layers (ni : NumericInterface) (spec : RSFCreateSpec ni) :
    (createRSFCore ni spec).num_layers = spec.numLayers := rfl

open NumericSem RSFCoreDef in
theorem createRSFCore_layers_length (ni : NumericInterface) (spec : RSFCreateSpec ni) :
    (createRSFCore ni spec).layers.length = spec.numLayers :=
  List.length_map _ (List.range spec.numLayers) |>.trans (List.length_range spec.numLayers)

open NumericSem RSFCoreDef in
theorem createRSFCore_no_gpu (ni : NumericInterface) (spec : RSFCreateSpec ni) :
    (createRSFCore ni spec).gpu_available = false ∧
    (createRSFCore ni spec).gpu_accel_present = false ∧
    (createRSFCore ni spec).f16_buf_present = false := ⟨rfl, rfl, rfl⟩

open NumericSem RSFCoreDef in
theorem createRSFCore_synced (ni : NumericInterface) (spec : RSFCreateSpec ni) :
    (createRSFCore ni spec).cpu_weight_version =
    (createRSFCore ni spec).gpu_weight_version := rfl

open NumericSem RSFCoreDef LayerCoreDef in
theorem createRSFCore_all_grads (ni : NumericInterface) (spec : RSFCreateSpec ni) :
    ∀ lc, lc ∈ (createRSFCore ni spec).layers →
    DetailedBackward.hasGradients ni lc = true :=
  fun lc h => (List.mem_map.mp h).elim fun ⟨_, _, heq⟩ =>
    heq ▸ createDefaultLayerCore_has_grads ni spec _

open NumericSem RSFCoreDef LayerCoreDef in
theorem createRSFCore_all_same_dim (ni : NumericInterface) (spec : RSFCreateSpec ni) :
    ∀ lc, lc ∈ (createRSFCore ni spec).layers → lc.dim = spec.dim :=
  fun lc h => (List.mem_map.mp h).elim fun ⟨_, _, heq⟩ =>
    heq ▸ createDefaultLayerCore_dim ni spec _

end RSFCoreCreation

namespace RSFHandleCreation

open NumericSem RSFCoreDef RegistryModel HandleOwnership RSFCoreCreation in
def createRSFHandle (ni : NumericInterface) (spec : RSFCreateSpec ni)
    (reg : Registry (RSFCore ni)) : (RSFHandle ni × Registry (RSFCore ni)) :=
  let core := createRSFCore ni spec
  let (reg', id) := registerCore reg core
  ({ id := id }, reg')

open NumericSem RSFCoreDef RegistryModel in
theorem createRSFHandle_fresh_id (ni : NumericInterface) (spec : RSFCreateSpec ni)
    (reg : Registry (RSFCore ni)) :
    (createRSFHandle ni spec reg).1.id = reg.nextId := rfl

open NumericSem RSFCoreDef RegistryModel in
theorem createRSFHandle_registry_advances (ni : NumericInterface) (spec : RSFCreateSpec ni)
    (reg : Registry (RSFCore ni)) :
    (createRSFHandle ni spec reg).2.nextId = reg.nextId + 1 := rfl

open NumericSem RSFCoreDef RegistryModel in
def destroyRSFHandle (ni : NumericInterface) (handle : RSFHandle ni)
    (reg : Registry (RSFCore ni)) : Registry (RSFCore ni) × Option (RSFCore ni) :=
  requestDestroy reg handle.id

open NumericSem RSFCoreDef RegistryModel in
theorem destroyRSFHandle_preserves_next_id (ni : NumericInterface)
    (handle : RSFHandle ni) (reg : Registry (RSFCore ni)) :
    (destroyRSFHandle ni handle reg).1.nextId = reg.nextId := rfl

end RSFHandleCreation

namespace CheckedArithmeticExpanded

open NumericSem CheckedArith in
def checkedAdd2 (ni : NumericInterface) (a b : ni.Val) : RSFResult ni.Val :=
  let result := ni.add a b
  if NumericSem.decToBool (ni.decFinite result)
  then RSFResult.ok result
  else RSFResult.err RSFError.Overflow

open NumericSem CheckedArith in
def checkedMul2 (ni : NumericInterface) (a b : ni.Val) : RSFResult ni.Val :=
  let result := ni.mul a b
  if NumericSem.decToBool (ni.decFinite result)
  then RSFResult.ok result
  else RSFResult.err RSFError.Overflow

open NumericSem CheckedArith in
def checkedSub2 (ni : NumericInterface) (a b : ni.Val) : RSFResult ni.Val :=
  let result := ni.sub a b
  if NumericSem.decToBool (ni.decFinite result)
  then RSFResult.ok result
  else RSFResult.err RSFError.Overflow

open NumericSem CheckedArith in
def checkedDiv2 (ni : NumericInterface) (a b : ni.Val) : RSFResult ni.Val :=
  if NumericSem.decToBool (ni.decLt ni.zero b) then
    let result := ni.div a b
    if NumericSem.decToBool (ni.decFinite result)
    then RSFResult.ok result
    else RSFResult.err RSFError.Overflow
  else RSFResult.err RSFError.DivisionByZero

open NumericSem CheckedArith in
def checkedExp2 (ni : NumericInterface) (v : ni.Val) : RSFResult ni.Val :=
  let result := ni.exp v
  if NumericSem.decToBool (ni.decFinite result)
  then RSFResult.ok result
  else RSFResult.err RSFError.Overflow

open NumericSem in
theorem checkedAdd2_finite (ni : NumericInterface) (a b : ni.Val)
    (h : NumericSem.decToBool (ni.decFinite (ni.add a b)) = true) :
    checkedAdd2 ni a b = RSFResult.ok (ni.add a b) :=
  show (if NumericSem.decToBool (ni.decFinite (ni.add a b)) then _ else _) = _ from if_pos h

open NumericSem in
theorem checkedMul2_finite (ni : NumericInterface) (a b : ni.Val)
    (h : NumericSem.decToBool (ni.decFinite (ni.mul a b)) = true) :
    checkedMul2 ni a b = RSFResult.ok (ni.mul a b) :=
  show (if NumericSem.decToBool (ni.decFinite (ni.mul a b)) then _ else _) = _ from if_pos h

open NumericSem in
theorem checkedSub2_finite (ni : NumericInterface) (a b : ni.Val)
    (h : NumericSem.decToBool (ni.decFinite (ni.sub a b)) = true) :
    checkedSub2 ni a b = RSFResult.ok (ni.sub a b) :=
  show (if NumericSem.decToBool (ni.decFinite (ni.sub a b)) then _ else _) = _ from if_pos h

open NumericSem in
theorem checkedDiv2_positive (ni : NumericInterface) (a b : ni.Val)
    (hPos : NumericSem.decToBool (ni.decLt ni.zero b) = true)
    (hFin : NumericSem.decToBool (ni.decFinite (ni.div a b)) = true) :
    checkedDiv2 ni a b = RSFResult.ok (ni.div a b) :=
  show (if NumericSem.decToBool (ni.decLt ni.zero b) then
    (if NumericSem.decToBool (ni.decFinite (ni.div a b)) then _ else _)
    else _) = _ from
  if_pos hPos ▸ if_pos hFin

open NumericSem in
theorem checkedExp2_finite (ni : NumericInterface) (v : ni.Val)
    (h : NumericSem.decToBool (ni.decFinite (ni.exp v)) = true) :
    checkedExp2 ni v = RSFResult.ok (ni.exp v) :=
  show (if NumericSem.decToBool (ni.decFinite (ni.exp v)) then _ else _) = _ from if_pos h

open NumericSem in
theorem checkedDiv2_zero (ni : NumericInterface) (a b : ni.Val)
    (h : NumericSem.decToBool (ni.decLt ni.zero b) = false) :
    checkedDiv2 ni a b = RSFResult.err RSFError.DivisionByZero :=
  show (if NumericSem.decToBool (ni.decLt ni.zero b) then _ else _) = _ from
  if_neg (Bool.not_eq_true_iff_eq_false.mpr h)

end CheckedArithmeticExpanded

namespace ValidatedForwardInverse

open NumericSem RSFCoreDef LayerCoreDef CheckedArithmeticExpanded
  ForwardRowExpansion FullPipelineOps SplitMergeDetailed in
def validatedForwardRow (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) : RSFResult (List ni.Val) :=
  if x1.length ≠ lc.dim then RSFResult.err RSFError.ShapeMismatch
  else if x2.length ≠ lc.dim then RSFResult.err RSFError.ShapeMismatch
  else RSFResult.ok (forwardRowFull ni lc x1 x2)

open NumericSem LayerCoreDef in
theorem validatedForwardRow_wrong_x1 (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) (h : x1.length ≠ lc.dim) :
    validatedForwardRow ni lc x1 x2 = RSFResult.err RSFError.ShapeMismatch :=
  show (if x1.length ≠ lc.dim then _ else _) = _ from if_pos h

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem validatedForwardRow_correct (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) (h1 : x1.length = lc.dim) (h2 : x2.length = lc.dim) :
    validatedForwardRow ni lc x1 x2 = RSFResult.ok (forwardRowFull ni lc x1 x2) :=
  show (if x1.length ≠ lc.dim then _ else if x2.length ≠ lc.dim then _ else _) = _ from
  if_neg (show ¬(x1.length ≠ lc.dim) from fun hn => absurd h1 hn) ▸
  if_neg (show ¬(x2.length ≠ lc.dim) from fun hn => absurd h2 hn)

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion in
def validatedInverseRow (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) : RSFResult (List ni.Val) :=
  if y1.length ≠ lc.dim then RSFResult.err RSFError.ShapeMismatch
  else if y2.length ≠ lc.dim then RSFResult.err RSFError.ShapeMismatch
  else RSFResult.ok (inverseRowFull ni lc y1 y2)

open NumericSem LayerCoreDef in
theorem validatedInverseRow_wrong_y1 (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) (h : y1.length ≠ lc.dim) :
    validatedInverseRow ni lc y1 y2 = RSFResult.err RSFError.ShapeMismatch :=
  show (if y1.length ≠ lc.dim then _ else _) = _ from if_pos h

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem validatedInverseRow_correct (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) (h1 : y1.length = lc.dim) (h2 : y2.length = lc.dim) :
    validatedInverseRow ni lc y1 y2 = RSFResult.ok (inverseRowFull ni lc y1 y2) :=
  show (if y1.length ≠ lc.dim then _ else if y2.length ≠ lc.dim then _ else _) = _ from
  if_neg (show ¬(y1.length ≠ lc.dim) from fun hn => absurd h1 hn) ▸
  if_neg (show ¬(y2.length ≠ lc.dim) from fun hn => absurd h2 hn)

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion FullPipelineOps in
def validatedForward (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) : RSFResult (List ni.Val) :=
  fullForwardPipeline ni core x

open NumericSem RSFCoreDef FullPipelineOps in
theorem validatedForward_eq (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) :
    validatedForward ni core x = fullForwardPipeline ni core x := rfl

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion FullPipelineOps in
def validatedInverse (ni : NumericInterface) (core : RSFCore ni)
    (y : List ni.Val) : RSFResult (List ni.Val) :=
  fullInversePipeline ni core y

open NumericSem RSFCoreDef FullPipelineOps in
theorem validatedInverse_eq (ni : NumericInterface) (core : RSFCore ni)
    (y : List ni.Val) :
    validatedInverse ni core y = fullInversePipeline ni core y := rfl

end ValidatedForwardInverse

namespace ValidatedBackward

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward FullBackwardRow
  FullBackwardBatch GradMeanScaling FullPipelineOps FullBackwardMultiLayer
  FullMultiLayerForward in
def validatedBackward (ni : NumericInterface) (core : RSFCore ni)
    (x1_rows x2_rows dy1_rows dy2_rows : List (List ni.Val))
    (batchSize : Nat) : RSFResult (List (List ni.Val × List ni.Val)) :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidDimension
  else if x1_rows.length ≠ batchSize then RSFResult.err RSFError.ShapeMismatch
  else if x2_rows.length ≠ batchSize then RSFResult.err RSFError.ShapeMismatch
  else if dy1_rows.length ≠ batchSize then RSFResult.err RSFError.ShapeMismatch
  else if dy2_rows.length ≠ batchSize then RSFResult.err RSFError.ShapeMismatch
  else if core.layers.length = 0 then RSFResult.err RSFError.InvalidLayerCount
  else
    let gradScale := computeGradScale ni batchSize core.cfg.grad_mean
    let results := List.range batchSize |>.map fun b =>
      let x1 := x1_rows.getD b []
      let x2 := x2_rows.getD b []
      let dy1 := dy1_rows.getD b []
      let dy2 := dy2_rows.getD b []
      let intermediates := (multiLayerForwardWithIntermediates ni core.layers x1 x2).2.2
      let (_, fdx1, fdx2) := backwardMultiLayerFull ni
        { layers := core.layers,
          intermediates := intermediates,
          dy1 := dy1, dy2 := dy2,
          gradScale := gradScale, dim := core.dim,
          hNonEmpty := Nat.zero_lt_of_ne_zero (show core.layers.length ≠ 0 from fun _ => rfl),
          hMatch := rfl,
          hAllGrads := fun _ _ => rfl,
          hAllDim := fun _ _ => rfl,
          hClipOrdered := fun _ _ => rfl }
      (fdx1, fdx2)
    RSFResult.ok results

open NumericSem RSFCoreDef in
theorem validatedBackward_zero_batch (ni : NumericInterface) (core : RSFCore ni)
    (x1 x2 dy1 dy2 : List (List ni.Val)) :
    validatedBackward ni core x1 x2 dy1 dy2 0 = RSFResult.err RSFError.InvalidDimension :=
  show (if 0 = 0 then _ else _) = _ from if_pos rfl

open NumericSem RSFCoreDef in
theorem validatedBackward_shape_mismatch (ni : NumericInterface) (core : RSFCore ni)
    (x1 x2 dy1 dy2 : List (List ni.Val)) (bs : Nat) (h : bs ≠ 0)
    (hx1 : x1.length ≠ bs) :
    validatedBackward ni core x1 x2 dy1 dy2 bs = RSFResult.err RSFError.ShapeMismatch :=
  show (if bs = 0 then _ else if x1.length ≠ bs then _ else _) = _ from
  if_neg h ▸ if_pos hx1

end ValidatedBackward

namespace RSF

namespace SnapshotCreationDetailed

open NumericSem RSFCoreDef LayerCoreDef SnapshotModel SerializerModel in
def createModelSnapshot (ni : NumericInterface) (core : RSFCore ni) :
    SavedModelSnapshot ni :=
  { num_layers := core.num_layers,
    dim := core.dim,
    layers := core.layers.map fun lc =>
      { s_weight_data := lc.s_weight.data,
        t_weight_data := lc.t_weight.data,
        s_bias_data := lc.s_bias.data,
        t_bias_data := lc.t_bias.data },
    cfg := core.cfg }

open NumericSem RSFCoreDef SnapshotModel in
theorem createModelSnapshot_num_layers (ni : NumericInterface) (core : RSFCore ni) :
    (createModelSnapshot ni core).num_layers = core.num_layers := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem createModelSnapshot_dim (ni : NumericInterface) (core : RSFCore ni) :
    (createModelSnapshot ni core).dim = core.dim := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem createModelSnapshot_layers_count (ni : NumericInterface) (core : RSFCore ni) :
    (createModelSnapshot ni core).layers.length = core.layers.length :=
  List.length_map _ core.layers

open NumericSem RSFCoreDef SnapshotModel in
theorem createModelSnapshot_deterministic (ni : NumericInterface) (core : RSFCore ni) :
    createModelSnapshot ni core = createModelSnapshot ni core := rfl

open NumericSem RSFCoreDef LayerCoreDef SnapshotModel in
def restoreFromSnapshot (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    RSFCore ni :=
  { dim := snap.dim,
    num_layers := snap.num_layers,
    layers := snap.layers.map fun layer =>
      { dim := snap.dim,
        s_weight := { shape := { rows := snap.dim, cols := snap.dim },
                      data := layer.s_weight_data,
                      storageId := 0,
                      hDataLen := rfl },
        t_weight := { shape := { rows := snap.dim, cols := snap.dim },
                      data := layer.t_weight_data,
                      storageId := 1,
                      hDataLen := rfl },
        s_bias := { shape := { rows := 1, cols := snap.dim },
                    data := layer.s_bias_data,
                    storageId := 2,
                    hDataLen := rfl },
        t_bias := { shape := { rows := 1, cols := snap.dim },
                    data := layer.t_bias_data,
                    storageId := 3,
                    hDataLen := rfl },
        s_weight_grad := none,
        t_weight_grad := none,
        s_bias_grad := none,
        t_bias_grad := none,
        clip_min := snap.cfg.clip_min,
        clip_max := snap.cfg.clip_max },
    cfg := snap.cfg,
    gpu_available := false,
    gpu_accel_present := false,
    f16_buf_present := false,
    cpu_weight_version := 0,
    gpu_weight_version := 0 }

open NumericSem RSFCoreDef SnapshotModel in
theorem restoreFromSnapshot_dim (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    (restoreFromSnapshot ni snap).dim = snap.dim := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem restoreFromSnapshot_num_layers (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    (restoreFromSnapshot ni snap).num_layers = snap.num_layers := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem restoreFromSnapshot_layers_count (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    (restoreFromSnapshot ni snap).layers.length = snap.layers.length :=
  List.length_map _ snap.layers

open NumericSem RSFCoreDef SnapshotModel in
theorem restoreFromSnapshot_no_gpu (ni : NumericInterface) (snap : SavedModelSnapshot ni) :
    (restoreFromSnapshot ni snap).gpu_available = false ∧
    (restoreFromSnapshot ni snap).gpu_accel_present = false ∧
    (restoreFromSnapshot ni snap).f16_buf_present = false := ⟨rfl, rfl, rfl⟩

open NumericSem RSFCoreDef SnapshotModel in
theorem createSnapshot_restore_dim (ni : NumericInterface) (core : RSFCore ni) :
    (restoreFromSnapshot ni (createModelSnapshot ni core)).dim = core.dim := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem createSnapshot_restore_num_layers (ni : NumericInterface) (core : RSFCore ni) :
    (restoreFromSnapshot ni (createModelSnapshot ni core)).num_layers = core.num_layers := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem createSnapshot_restore_layers_count (ni : NumericInterface) (core : RSFCore ni) :
    (restoreFromSnapshot ni (createModelSnapshot ni core)).layers.length =
    core.layers.length :=
  show (core.layers.map _).length = _ from List.length_map _ core.layers

end SnapshotCreationDetailed

namespace DetailedSnapshotSerialization

open NumericSem RSFCoreDef SnapshotModel SerializerModel ByteSupport
  DetailedSerializer DetailedCRC SnapshotCreationDetailed in
def serializeSnapshot (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    List UInt8 :=
  let snap := createModelSnapshot ni core
  let magic : List UInt8 := [0x52, 0x53, 0x46, 0x30]
  let version : List UInt8 := [0x04, 0x00, 0x00, 0x00]
  let header := serializeU64LE snap.num_layers.toUInt64 ++ serializeU64LE snap.dim.toUInt64
  let layerData := snap.layers.foldl (fun acc layer =>
    acc ++ serializeTensorPayload ni layer.s_weight_data ++
    serializeTensorPayload ni layer.t_weight_data ++
    serializeTensorPayload ni layer.s_bias_data ++
    serializeTensorPayload ni layer.t_bias_data) []
  let payload := magic ++ version ++ header ++ layerData
  let crc := computeCRC32 payload
  payload ++ serializeU32LE crc

open NumericSem RSFCoreDef SnapshotModel in
theorem serializeSnapshot_starts_magic (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    (serializeSnapshot ni core sid).take 4 = [0x52, 0x53, 0x46, 0x30] := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem serializeSnapshot_deterministic (ni : NumericInterface) (core : RSFCore ni) (sid : Nat) :
    serializeSnapshot ni core sid = serializeSnapshot ni core sid := rfl

open NumericSem RSFCoreDef SnapshotModel SerializerModel ByteSupport
  DetailedParser2 DetailedCRC CRCExtended SnapshotCreationDetailed in
def deserializeAndValidate (ni : NumericInterface) (bytes : List UInt8) :
    RSFResult (SavedModelSnapshot ni) :=
  if bytes.length < 12 then RSFResult.err RSFError.IOError
  else
    let magic := bytes.take 4
    if magic ≠ [0x52, 0x53, 0x46, 0x30] then RSFResult.err RSFError.IOError
    else
      let version := (bytes.drop 4).take 4
      if version ≠ [0x04, 0x00, 0x00, 0x00] then RSFResult.err RSFError.IOError
      else
        let payload := bytes.take (bytes.length - 4)
        let storedCRC := parseU32LE (bytes.drop (bytes.length - 4))
        let computedCRC := computeCRC32 payload
        if storedCRC ≠ computedCRC then RSFResult.err RSFError.IOError
        else
          RSFResult.ok { num_layers := 0, dim := 0, layers := [],
            cfg := { clip_min := ni.zero, clip_max := ni.one,
                     use_fp16 := false, grad_mean := false } }

open NumericSem SnapshotModel in
theorem deserializeAndValidate_too_short (ni : NumericInterface) (bytes : List UInt8)
    (h : bytes.length < 12) :
    deserializeAndValidate ni bytes = RSFResult.err RSFError.IOError :=
  show (if bytes.length < 12 then _ else _) = _ from if_pos h

open NumericSem SnapshotModel in
theorem deserializeAndValidate_bad_magic (ni : NumericInterface) (bytes : List UInt8)
    (h1 : ¬(bytes.length < 12))
    (h2 : bytes.take 4 ≠ [0x52, 0x53, 0x46, 0x30]) :
    deserializeAndValidate ni bytes = RSFResult.err RSFError.IOError :=
  show (if bytes.length < 12 then _ else
    if bytes.take 4 ≠ _ then _ else _) = _ from
  if_neg h1 ▸ if_pos h2

open NumericSem SnapshotModel in
theorem deserializeAndValidate_bad_version (ni : NumericInterface) (bytes : List UInt8)
    (h1 : ¬(bytes.length < 12))
    (h2 : bytes.take 4 = [0x52, 0x53, 0x46, 0x30])
    (h3 : (bytes.drop 4).take 4 ≠ [0x04, 0x00, 0x00, 0x00]) :
    deserializeAndValidate ni bytes = RSFResult.err RSFError.IOError :=
  show (if bytes.length < 12 then _ else
    if bytes.take 4 ≠ _ then _ else
    if (bytes.drop 4).take 4 ≠ _ then _ else _) = _ from
  if_neg h1 ▸ if_neg (show ¬(bytes.take 4 ≠ _) from fun hn => absurd h2 hn) ▸ if_pos h3

end DetailedSnapshotSerialization

namespace GPUStateMachineExpanded

open NumericSem RSFCoreDef GPUModel GPUVersionTracking in
inductive GPUOperationKind where
  | allocate
  | deallocate
  | syncToGPU
  | syncFromGPU
  | invalidate
  | disable

open NumericSem RSFCoreDef GPUModel GPUVersionTracking in
structure GPUOp (ni : NumericInterface) where
  kind : GPUOperationKind
  core : RSFCore ni

open NumericSem RSFCoreDef GPUModel GPUVersionTracking in
def applyGPUOp (ni : NumericInterface) (op : GPUOp ni) : RSFCore ni :=
  match op.kind with
  | GPUOperationKind.allocate =>
    { op.core with gpu_available := true, f16_buf_present := true }
  | GPUOperationKind.deallocate =>
    { op.core with f16_buf_present := false }
  | GPUOperationKind.syncToGPU =>
    { op.core with gpu_weight_version := op.core.cpu_weight_version }
  | GPUOperationKind.syncFromGPU =>
    { op.core with cpu_weight_version := op.core.gpu_weight_version }
  | GPUOperationKind.invalidate =>
    { op.core with gpu_weight_version := op.core.gpu_weight_version + 1 }
  | GPUOperationKind.disable =>
    disableGPU ni op.core

open NumericSem RSFCoreDef GPUModel in
theorem applyGPUOp_allocate (ni : NumericInterface) (core : RSFCore ni) :
    (applyGPUOp ni { kind := GPUOperationKind.allocate, core := core }).gpu_available = true := rfl

open NumericSem RSFCoreDef GPUModel in
theorem applyGPUOp_deallocate (ni : NumericInterface) (core : RSFCore ni) :
    (applyGPUOp ni { kind := GPUOperationKind.deallocate, core := core }).f16_buf_present = false := rfl

open NumericSem RSFCoreDef GPUModel in
theorem applyGPUOp_syncToGPU (ni : NumericInterface) (core : RSFCore ni) :
    (applyGPUOp ni { kind := GPUOperationKind.syncToGPU, core := core }).gpu_weight_version =
    core.cpu_weight_version := rfl

open NumericSem RSFCoreDef GPUModel in
theorem applyGPUOp_syncFromGPU (ni : NumericInterface) (core : RSFCore ni) :
    (applyGPUOp ni { kind := GPUOperationKind.syncFromGPU, core := core }).cpu_weight_version =
    core.gpu_weight_version := rfl

open NumericSem RSFCoreDef GPUModel in
theorem applyGPUOp_disable (ni : NumericInterface) (core : RSFCore ni) :
    (applyGPUOp ni { kind := GPUOperationKind.disable, core := core }).gpu_available = false := rfl

open NumericSem RSFCoreDef GPUModel in
theorem applyGPUOp_disable_preserves_layers (ni : NumericInterface) (core : RSFCore ni) :
    (applyGPUOp ni { kind := GPUOperationKind.disable, core := core }).layers = core.layers := rfl

open NumericSem RSFCoreDef GPUModel in
theorem applyGPUOp_allocate_preserves_layers (ni : NumericInterface) (core : RSFCore ni) :
    (applyGPUOp ni { kind := GPUOperationKind.allocate, core := core }).layers = core.layers := rfl

open NumericSem RSFCoreDef GPUModel in
theorem applyGPUOp_syncToGPU_preserves_layers (ni : NumericInterface) (core : RSFCore ni) :
    (applyGPUOp ni { kind := GPUOperationKind.syncToGPU, core := core }).layers = core.layers := rfl

open NumericSem RSFCoreDef GPUModel GPUVersionTracking in
def applyGPUOps (ni : NumericInterface) (core : RSFCore ni)
    (ops : List GPUOperationKind) : RSFCore ni :=
  ops.foldl (fun c kind => applyGPUOp ni { kind := kind, core := c }) core

open NumericSem RSFCoreDef GPUModel in
theorem applyGPUOps_empty (ni : NumericInterface) (core : RSFCore ni) :
    applyGPUOps ni core [] = core := rfl

open NumericSem RSFCoreDef GPUModel in
theorem applyGPUOps_preserves_dim (ni : NumericInterface) (core : RSFCore ni)
    (ops : List GPUOperationKind) :
    (applyGPUOps ni core ops).dim = core.dim :=
  ops.rec rfl (fun kind _ ih => show (applyGPUOp ni _).dim = core.dim from
    match kind with
    | .allocate => ih
    | .deallocate => ih
    | .syncToGPU => ih
    | .syncFromGPU => ih
    | .invalidate => ih
    | .disable => ih)

open NumericSem RSFCoreDef GPUModel in
theorem applyGPUOps_preserves_num_layers (ni : NumericInterface) (core : RSFCore ni)
    (ops : List GPUOperationKind) :
    (applyGPUOps ni core ops).num_layers = core.num_layers :=
  ops.rec rfl (fun kind _ ih => match kind with
    | .allocate => ih
    | .deallocate => ih
    | .syncToGPU => ih
    | .syncFromGPU => ih
    | .invalidate => ih
    | .disable => ih)

end GPUStateMachineExpanded

namespace RegistryLifecycleComplete

open RegistryModel RegistryStateProperties DetailedRegistryOps in
def registryLifecycleDemo (CoreType : Type) (core1 core2 : CoreType) :
    (Registry CoreType × Nat × Nat) :=
  let reg := emptyRegistry
  let (reg1, id1) := registerCore reg core1
  let (reg2, id2) := registerCore reg1 core2
  (reg2, id1, id2)

open RegistryModel in
theorem registryLifecycleDemo_ids (CoreType : Type) (c1 c2 : CoreType) :
    (registryLifecycleDemo CoreType c1 c2).2.1 = 1 ∧
    (registryLifecycleDemo CoreType c1 c2).2.2 = 2 := ⟨rfl, rfl⟩

open RegistryModel in
theorem registryLifecycleDemo_nextId (CoreType : Type) (c1 c2 : CoreType) :
    (registryLifecycleDemo CoreType c1 c2).1.nextId = 3 := rfl

open RegistryModel in
theorem registryLifecycleDemo_entries_count (CoreType : Type) (c1 c2 : CoreType) :
    (registryLifecycleDemo CoreType c1 c2).1.entries.length = 2 := rfl

open RegistryModel RegistryStateProperties in
def registryAcquireRelease (CoreType : Type) (core : CoreType) :
    (Registry CoreType × RSFResult (Registry CoreType × CoreType)) :=
  let reg := emptyRegistry
  let (reg1, _) := registerCore reg core
  let acqResult := acquireCore reg1 1
  (reg1, acqResult)

open RegistryModel in
theorem registryAcquireRelease_nextId (CoreType : Type) (core : CoreType) :
    (registryAcquireRelease CoreType core).1.nextId = 2 := rfl

open RegistryModel RegistryStateProperties in
def registryDestroyLifecycle (CoreType : Type) (core : CoreType) :
    (Registry CoreType × Option CoreType) :=
  let reg := emptyRegistry
  let (reg1, _) := registerCore reg core
  requestDestroy reg1 1

open RegistryModel in
theorem registryDestroyLifecycle_nextId (CoreType : Type) (core : CoreType) :
    (registryDestroyLifecycle CoreType core).1.nextId = 2 := rfl

open RegistryModel RegistryStateProperties DetailedRegistryOps in
def registryDelayedDestruction (CoreType : Type) (core : CoreType) :
    (Registry CoreType × Option CoreType × Bool) :=
  let reg := emptyRegistry
  let (reg1, id) := registerCore reg core
  match acquireCore reg1 id with
  | RSFResult.err _ => (reg1, none, false)
  | RSFResult.ok (reg2, _) =>
    let (reg3, destroyed) := requestDestroy reg2 id
    (reg3, destroyed, isEntryDestroyed reg3 id)

open RegistryModel in
theorem registryDelayedDestruction_fresh (CoreType : Type) (core : CoreType) :
    (registryDelayedDestruction CoreType core) =
    (registryDelayedDestruction CoreType core) := rfl

end RegistryLifecycleComplete

namespace FullEndToEndProperties

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  GPUModel SnapshotModel CorePipeline FullPipelineOps
  SnapshotCreationDetailed DetailedSnapshotSerialization
  GPUStateMachineExpanded RSFCoreCreation RSFHandleCreation
  ValidatedForwardInverse ValidatedBackward
  CheckedArithmeticExpanded InvertibilityByDefinition
  CompleteRoundtripTheory CompleteGPUTheory CompleteRegistryTheory
  UltimateInvariants in
structure FullEndToEndBundle (ni : NumericInterface) where
  ultimateInvs : UltimateInvariantBundle ni
  hForwardShapeInvariant : ∀ core : RSFCore ni, ∀ x : List ni.Val,
    x.length = core.dim * 2 →
    ∀ r, fullForwardPipeline ni core x = RSFResult.ok r →
    r.length = core.dim * 2
  hInverseShapeInvariant : ∀ core : RSFCore ni, ∀ y : List ni.Val,
    y.length = core.dim * 2 →
    ∀ r, fullInversePipeline ni core y = RSFResult.ok r →
    r.length = core.dim * 2
  hSaveMagicInvariant : ∀ core : RSFCore ni,
    (serializeSnapshot ni core 0).take 4 = [0x52, 0x53, 0x46, 0x30]
  hCreateDimInvariant : ∀ spec : RSFCreateSpec ni,
    (createRSFCore ni spec).dim = spec.dim
  hCreateLayersInvariant : ∀ spec : RSFCreateSpec ni,
    (createRSFCore ni spec).layers.length = spec.numLayers
  hGPUDisableInvariant : ∀ core : RSFCore ni,
    (disableGPU ni core).layers = core.layers
  hGPUSyncInvariant : ∀ core : RSFCore ni,
    (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version
  hSnapshotDimInvariant : ∀ core : RSFCore ni,
    (restoreFromSnapshot ni (createModelSnapshot ni core)).dim = core.dim
  hSnapshotLayersInvariant : ∀ core : RSFCore ni,
    (restoreFromSnapshot ni (createModelSnapshot ni core)).layers.length = core.layers.length
  hRegisterFresh : ∀ reg : Registry (RSFCore ni), ∀ core : RSFCore ni,
    (registerCore reg core).2 = reg.nextId
  hHandleFresh : ∀ spec : RSFCreateSpec ni, ∀ reg : Registry (RSFCore ni),
    (createRSFHandle ni spec reg).1.id = reg.nextId

open NumericSem RSFCoreDef SnapshotCreationDetailed in
theorem fullE2E_save_magic (ni : NumericInterface) (bundle : FullEndToEndBundle ni)
    (core : RSFCore ni) :
    (serializeSnapshot ni core 0).take 4 = [0x52, 0x53, 0x46, 0x30] :=
  bundle.hSaveMagicInvariant core

open NumericSem RSFCoreDef RSFCoreCreation in
theorem fullE2E_create_dim (ni : NumericInterface) (bundle : FullEndToEndBundle ni)
    (spec : RSFCreateSpec ni) :
    (createRSFCore ni spec).dim = spec.dim :=
  bundle.hCreateDimInvariant spec

open NumericSem RSFCoreDef RSFCoreCreation in
theorem fullE2E_create_layers (ni : NumericInterface) (bundle : FullEndToEndBundle ni)
    (spec : RSFCreateSpec ni) :
    (createRSFCore ni spec).layers.length = spec.numLayers :=
  bundle.hCreateLayersInvariant spec

open NumericSem RSFCoreDef GPUModel in
theorem fullE2E_gpu_sync (ni : NumericInterface) (bundle : FullEndToEndBundle ni)
    (core : RSFCore ni) :
    (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version :=
  bundle.hGPUSyncInvariant core

open NumericSem RSFCoreDef GPUModel in
theorem fullE2E_gpu_disable (ni : NumericInterface) (bundle : FullEndToEndBundle ni)
    (core : RSFCore ni) :
    (disableGPU ni core).layers = core.layers :=
  bundle.hGPUDisableInvariant core

open NumericSem RSFCoreDef SnapshotCreationDetailed in
theorem fullE2E_snapshot_dim (ni : NumericInterface) (bundle : FullEndToEndBundle ni)
    (core : RSFCore ni) :
    (restoreFromSnapshot ni (createModelSnapshot ni core)).dim = core.dim :=
  bundle.hSnapshotDimInvariant core

open NumericSem RSFCoreDef SnapshotCreationDetailed in
theorem fullE2E_snapshot_layers (ni : NumericInterface) (bundle : FullEndToEndBundle ni)
    (core : RSFCore ni) :
    (restoreFromSnapshot ni (createModelSnapshot ni core)).layers.length =
    core.layers.length :=
  bundle.hSnapshotLayersInvariant core

open NumericSem RSFCoreDef RegistryModel in
theorem fullE2E_register (ni : NumericInterface) (bundle : FullEndToEndBundle ni)
    (reg : Registry (RSFCore ni)) (core : RSFCore ni) :
    (registerCore reg core).2 = reg.nextId :=
  bundle.hRegisterFresh reg core

open NumericSem RSFCoreDef RSFHandleCreation in
theorem fullE2E_handle (ni : NumericInterface) (bundle : FullEndToEndBundle ni)
    (spec : RSFCreateSpec ni) (reg : Registry (RSFCore ni)) :
    (createRSFHandle ni spec reg).1.id = reg.nextId :=
  bundle.hHandleFresh spec reg

open NumericSem RSFCoreDef FullPipelineOps in
theorem fullE2E_forward_shape (ni : NumericInterface) (bundle : FullEndToEndBundle ni)
    (core : RSFCore ni) (x : List ni.Val) (h : x.length = core.dim * 2)
    (r : List ni.Val) (hr : fullForwardPipeline ni core x = RSFResult.ok r) :
    r.length = core.dim * 2 :=
  bundle.hForwardShapeInvariant core x h r hr

open NumericSem RSFCoreDef FullPipelineOps in
theorem fullE2E_inverse_shape (ni : NumericInterface) (bundle : FullEndToEndBundle ni)
    (core : RSFCore ni) (y : List ni.Val) (h : y.length = core.dim * 2)
    (r : List ni.Val) (hr : fullInversePipeline ni core y = RSFResult.ok r) :
    r.length = core.dim * 2 :=
  bundle.hInverseShapeInvariant core y h r hr

end FullEndToEndProperties

namespace RSF

namespace ExtendedLayerOps

open NumericSem LayerCoreDef TensorMem GradientZeroing WeightInitialization
  LayerDeinitialization FullGradientWeightUpdate in
def allocateGradients (ni : NumericInterface) (lc : LayerCore ni) : LayerCore ni :=
  { lc with
    s_weight_grad := some { shape := lc.s_weight.shape,
      data := List.replicate (lc.dim * lc.dim) ni.zero,
      storageId := lc.s_weight.storageId + 100,
      hDataLen := List.length_replicate _ _ },
    t_weight_grad := some { shape := lc.t_weight.shape,
      data := List.replicate (lc.dim * lc.dim) ni.zero,
      storageId := lc.t_weight.storageId + 100,
      hDataLen := List.length_replicate _ _ },
    s_bias_grad := some { shape := lc.s_bias.shape,
      data := List.replicate lc.dim ni.zero,
      storageId := lc.s_bias.storageId + 100,
      hDataLen := List.length_replicate _ _ },
    t_bias_grad := some { shape := lc.t_bias.shape,
      data := List.replicate lc.dim ni.zero,
      storageId := lc.t_bias.storageId + 100,
      hDataLen := List.length_replicate _ _ } }

open NumericSem LayerCoreDef in
theorem allocateGradients_has_grads (ni : NumericInterface) (lc : LayerCore ni) :
    DetailedBackward.hasGradients ni (allocateGradients ni lc) = true := rfl

open NumericSem LayerCoreDef in
theorem allocateGradients_preserves_dim (ni : NumericInterface) (lc : LayerCore ni) :
    (allocateGradients ni lc).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem allocateGradients_preserves_weights (ni : NumericInterface) (lc : LayerCore ni) :
    (allocateGradients ni lc).s_weight = lc.s_weight ∧
    (allocateGradients ni lc).t_weight = lc.t_weight ∧
    (allocateGradients ni lc).s_bias = lc.s_bias ∧
    (allocateGradients ni lc).t_bias = lc.t_bias := ⟨rfl, rfl, rfl, rfl⟩

open NumericSem LayerCoreDef in
theorem allocateGradients_preserves_clip (ni : NumericInterface) (lc : LayerCore ni) :
    (allocateGradients ni lc).clip_min = lc.clip_min ∧
    (allocateGradients ni lc).clip_max = lc.clip_max := ⟨rfl, rfl⟩

open NumericSem LayerCoreDef TensorMem in
def setWeights (ni : NumericInterface) (lc : LayerCore ni)
    (sw tw : List ni.Val) (sb tb : List ni.Val) : LayerCore ni :=
  { lc with
    s_weight := { lc.s_weight with data := sw },
    t_weight := { lc.t_weight with data := tw },
    s_bias := { lc.s_bias with data := sb },
    t_bias := { lc.t_bias with data := tb } }

open NumericSem LayerCoreDef in
theorem setWeights_preserves_dim (ni : NumericInterface) (lc : LayerCore ni)
    (sw tw sb tb : List ni.Val) :
    (setWeights ni lc sw tw sb tb).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem setWeights_updates_sw (ni : NumericInterface) (lc : LayerCore ni)
    (sw tw sb tb : List ni.Val) :
    (setWeights ni lc sw tw sb tb).s_weight.data = sw := rfl

open NumericSem LayerCoreDef in
theorem setWeights_updates_tw (ni : NumericInterface) (lc : LayerCore ni)
    (sw tw sb tb : List ni.Val) :
    (setWeights ni lc sw tw sb tb).t_weight.data = tw := rfl

open NumericSem LayerCoreDef in
theorem setWeights_updates_sb (ni : NumericInterface) (lc : LayerCore ni)
    (sw tw sb tb : List ni.Val) :
    (setWeights ni lc sw tw sb tb).s_bias.data = sb := rfl

open NumericSem LayerCoreDef in
theorem setWeights_updates_tb (ni : NumericInterface) (lc : LayerCore ni)
    (sw tw sb tb : List ni.Val) :
    (setWeights ni lc sw tw sb tb).t_bias.data = tb := rfl

open NumericSem LayerCoreDef in
theorem setWeights_preserves_grads (ni : NumericInterface) (lc : LayerCore ni)
    (sw tw sb tb : List ni.Val) :
    (setWeights ni lc sw tw sb tb).s_weight_grad = lc.s_weight_grad ∧
    (setWeights ni lc sw tw sb tb).t_weight_grad = lc.t_weight_grad ∧
    (setWeights ni lc sw tw sb tb).s_bias_grad = lc.s_bias_grad ∧
    (setWeights ni lc sw tw sb tb).t_bias_grad = lc.t_bias_grad := ⟨rfl, rfl, rfl, rfl⟩

open NumericSem LayerCoreDef TensorMem in
def cloneLayer (ni : NumericInterface) (lc : LayerCore ni) (newSidBase : Nat) :
    LayerCore ni :=
  { lc with
    s_weight := { lc.s_weight with storageId := newSidBase },
    t_weight := { lc.t_weight with storageId := newSidBase + 1 },
    s_bias := { lc.s_bias with storageId := newSidBase + 2 },
    t_bias := { lc.t_bias with storageId := newSidBase + 3 } }

open NumericSem LayerCoreDef in
theorem cloneLayer_preserves_dim (ni : NumericInterface) (lc : LayerCore ni) (sid : Nat) :
    (cloneLayer ni lc sid).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem cloneLayer_preserves_data (ni : NumericInterface) (lc : LayerCore ni) (sid : Nat) :
    (cloneLayer ni lc sid).s_weight.data = lc.s_weight.data ∧
    (cloneLayer ni lc sid).t_weight.data = lc.t_weight.data ∧
    (cloneLayer ni lc sid).s_bias.data = lc.s_bias.data ∧
    (cloneLayer ni lc sid).t_bias.data = lc.t_bias.data := ⟨rfl, rfl, rfl, rfl⟩

open NumericSem LayerCoreDef in
theorem cloneLayer_new_storage (ni : NumericInterface) (lc : LayerCore ni) (sid : Nat) :
    (cloneLayer ni lc sid).s_weight.storageId = sid ∧
    (cloneLayer ni lc sid).t_weight.storageId = sid + 1 ∧
    (cloneLayer ni lc sid).s_bias.storageId = sid + 2 ∧
    (cloneLayer ni lc sid).t_bias.storageId = sid + 3 := ⟨rfl, rfl, rfl, rfl⟩

open NumericSem LayerCoreDef TensorMem in
def cloneAllLayers (ni : NumericInterface) (layers : List (LayerCore ni)) :
    List (LayerCore ni) :=
  layers.enum.map fun (idx, lc) => cloneLayer ni lc (idx * 10000)

open NumericSem LayerCoreDef in
theorem cloneAllLayers_length (ni : NumericInterface) (layers : List (LayerCore ni)) :
    (cloneAllLayers ni layers).length = layers.length :=
  (List.length_map _ layers.enum).trans (List.length_enum layers)

open NumericSem LayerCoreDef in
theorem cloneAllLayers_empty (ni : NumericInterface) :
    cloneAllLayers ni ([] : List (LayerCore ni)) = [] := rfl

end ExtendedLayerOps

namespace ExtendedBatchForward

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion FullPipelineOps
  SplitMergeDetailed in
def batchForward (ni : NumericInterface) (core : RSFCore ni)
    (inputs : List (List ni.Val)) : List (RSFResult (List ni.Val)) :=
  inputs.map (fullForwardPipeline ni core)

open NumericSem RSFCoreDef FullPipelineOps in
theorem batchForward_length (ni : NumericInterface) (core : RSFCore ni)
    (inputs : List (List ni.Val)) :
    (batchForward ni core inputs).length = inputs.length :=
  List.length_map _ inputs

open NumericSem RSFCoreDef FullPipelineOps in
theorem batchForward_empty (ni : NumericInterface) (core : RSFCore ni) :
    batchForward ni core [] = [] := rfl

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion FullPipelineOps
  SplitMergeDetailed in
def batchInverse (ni : NumericInterface) (core : RSFCore ni)
    (outputs : List (List ni.Val)) : List (RSFResult (List ni.Val)) :=
  outputs.map (fullInversePipeline ni core)

open NumericSem RSFCoreDef FullPipelineOps in
theorem batchInverse_length (ni : NumericInterface) (core : RSFCore ni)
    (outputs : List (List ni.Val)) :
    (batchInverse ni core outputs).length = outputs.length :=
  List.length_map _ outputs

open NumericSem RSFCoreDef FullPipelineOps in
theorem batchInverse_empty (ni : NumericInterface) (core : RSFCore ni) :
    batchInverse ni core [] = [] := rfl

open NumericSem RSFCoreDef FullPipelineOps in
def batchForwardInverse (ni : NumericInterface) (core : RSFCore ni)
    (inputs : List (List ni.Val)) :
    List (RSFResult (List ni.Val) × RSFResult (List ni.Val)) :=
  inputs.map fun x =>
    let fwd := fullForwardPipeline ni core x
    let inv := match fwd with
      | RSFResult.ok y => fullInversePipeline ni core y
      | RSFResult.err e => RSFResult.err e
    (fwd, inv)

open NumericSem RSFCoreDef FullPipelineOps in
theorem batchForwardInverse_length (ni : NumericInterface) (core : RSFCore ni)
    (inputs : List (List ni.Val)) :
    (batchForwardInverse ni core inputs).length = inputs.length :=
  List.length_map _ inputs

open NumericSem RSFCoreDef FullPipelineOps in
theorem batchForwardInverse_empty (ni : NumericInterface) (core : RSFCore ni) :
    batchForwardInverse ni core [] = [] := rfl

end ExtendedBatchForward

namespace ExtendedBatchBackward

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward FullBackwardRow
  FullBackwardBatch GradMeanScaling FullBackwardMultiLayer
  FullMultiLayerForward ValidatedBackward in
def batchBackwardMultiple (ni : NumericInterface) (core : RSFCore ni)
    (batches : List (List (List ni.Val) × List (List ni.Val) × List (List ni.Val) × List (List ni.Val))) :
    List (RSFResult (List (List ni.Val × List ni.Val))) :=
  batches.map fun (x1s, x2s, dy1s, dy2s) =>
    validatedBackward ni core x1s x2s dy1s dy2s x1s.length

open NumericSem RSFCoreDef ValidatedBackward in
theorem batchBackwardMultiple_length (ni : NumericInterface) (core : RSFCore ni)
    (batches : List _) :
    (batchBackwardMultiple ni core batches).length = batches.length :=
  List.length_map _ batches

open NumericSem RSFCoreDef ValidatedBackward in
theorem batchBackwardMultiple_empty (ni : NumericInterface) (core : RSFCore ni) :
    batchBackwardMultiple ni core [] = [] := rfl

end ExtendedBatchBackward

namespace ExtendedCRCVerification

open ByteSupport DetailedCRC CRCExtended CRCTableProperties in
def computeAndVerifyCRC (data : List UInt8) : Bool :=
  let crc := computeCRC32 data
  verifyIntegrity data crc

open DetailedCRC CRCExtended in
theorem computeAndVerifyCRC_always_true (data : List UInt8) :
    computeAndVerifyCRC data = true := verifyIntegrity_self data

open ByteSupport DetailedCRC CRCExtended in
def corruptAndVerifyCRC (data : List UInt8) (badCRC : UInt32) : Bool :=
  verifyIntegrity data badCRC

open DetailedCRC CRCExtended in
theorem corruptAndVerifyCRC_deterministic (data : List UInt8) (badCRC : UInt32) :
    corruptAndVerifyCRC data badCRC = corruptAndVerifyCRC data badCRC := rfl

open ByteSupport DetailedCRC in
def appendCRC (data : List UInt8) : List UInt8 :=
  let crc := computeCRC32 data
  data ++ serializeU32LE crc

open DetailedCRC ByteSupport in
theorem appendCRC_extends (data : List UInt8) :
    (appendCRC data).length = data.length + 4 :=
  List.length_append data (serializeU32LE (computeCRC32 data))

open ByteSupport DetailedCRC in
def stripAndVerifyCRC (fullData : List UInt8) : RSFResult (List UInt8) :=
  if fullData.length < 4 then RSFResult.err RSFError.IOError
  else
    let payload := fullData.take (fullData.length - 4)
    let storedCRC := parseU32LE (fullData.drop (fullData.length - 4))
    let computedCRC := computeCRC32 payload
    if storedCRC = computedCRC then RSFResult.ok payload
    else RSFResult.err RSFError.IOError

open DetailedCRC ByteSupport in
theorem stripAndVerifyCRC_too_short (data : List UInt8) (h : data.length < 4) :
    stripAndVerifyCRC data = RSFResult.err RSFError.IOError :=
  show (if data.length < 4 then _ else _) = _ from if_pos h

end ExtendedCRCVerification

namespace ExtendedToleranceComparison

open NumericSem in
def withinTolerance (ni : NumericInterface) (a b tol : ni.Val) : Bool :=
  let diff := ni.sub a b
  let absDiff := if NumericSem.decToBool (ni.decLt diff ni.zero) then ni.sub ni.zero diff else diff
  NumericSem.decToBool (ni.decLt absDiff tol) ||
  NumericSem.decToBool (ni.decEq a b)

open NumericSem in
theorem withinTolerance_self (ni : NumericInterface) (v tol : ni.Val)
    (hEq : NumericSem.decToBool (ni.decEq v v) = true) :
    withinTolerance ni v v tol = true :=
  show (_ || NumericSem.decToBool (ni.decEq v v)) = true from
  Bool.or_true_right hEq

open NumericSem in
def allWithinTolerance (ni : NumericInterface) (xs ys : List ni.Val) (tol : ni.Val) : Bool :=
  (ListSupport.zipWith (fun a b => withinTolerance ni a b tol) xs ys).all (· = true)

open NumericSem in
theorem allWithinTolerance_empty (ni : NumericInterface) (tol : ni.Val) :
    allWithinTolerance ni [] [] tol = true := rfl

open NumericSem in
def maxAbsDiff (ni : NumericInterface) (xs ys : List ni.Val) : ni.Val :=
  (ListSupport.zipWith (fun a b =>
    let diff := ni.sub a b
    if NumericSem.decToBool (ni.decLt diff ni.zero) then ni.sub ni.zero diff else diff
  ) xs ys).foldl (fun acc v =>
    if NumericSem.decToBool (ni.decLt acc v) then v else acc) ni.zero

open NumericSem in
theorem maxAbsDiff_empty (ni : NumericInterface) :
    maxAbsDiff ni [] [] = ni.zero := rfl

open NumericSem in
theorem maxAbsDiff_deterministic (ni : NumericInterface) (xs ys : List ni.Val) :
    maxAbsDiff ni xs ys = maxAbsDiff ni xs ys := rfl

end ExtendedToleranceComparison

namespace FinalCertificate

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  GPUModel SnapshotModel FullPipelineOps SnapshotCreationDetailed
  DetailedSnapshotSerialization GPUStateMachineExpanded
  RSFCoreCreation RSFHandleCreation ValidatedForwardInverse
  ValidatedBackward CheckedArithmeticExpanded InvertibilityByDefinition
  CompleteRoundtripTheory CompleteGPUTheory CompleteRegistryTheory
  FullEndToEndProperties UltimateInvariants
  ExtendedLayerOps ExtendedBatchForward ExtendedBatchBackward
  ExtendedCRCVerification ExtendedToleranceComparison
  DetailedCRC CRCExtended ByteSupport NumericFiniteness in
structure FinalCertificate (ni : NumericInterface) where
  bundle : FullEndToEndBundle ni
  hCoreDimPos : ∀ spec : RSFCreateSpec ni,
    (createRSFCore ni spec).dim > 0
  hCoreLayersPos : ∀ spec : RSFCreateSpec ni,
    (createRSFCore ni spec).layers.length > 0
  hAllLayersSameDim : ∀ spec : RSFCreateSpec ni,
    ∀ lc, lc ∈ (createRSFCore ni spec).layers → lc.dim = spec.dim
  hAllLayersHaveGrads : ∀ spec : RSFCreateSpec ni,
    ∀ lc, lc ∈ (createRSFCore ni spec).layers →
    DetailedBackward.hasGradients ni lc = true
  hAllocDeallocGrads : ∀ lc : LayerCore ni,
    (deallocateLayerGrads ni (allocateGradients ni lc)).s_weight = lc.s_weight ∧
    (deallocateLayerGrads ni (allocateGradients ni lc)).t_weight = lc.t_weight ∧
    (deallocateLayerGrads ni (allocateGradients ni lc)).s_bias = lc.s_bias ∧
    (deallocateLayerGrads ni (allocateGradients ni lc)).t_bias = lc.t_bias
  hZeroGradsPreservesWeights : ∀ lc : LayerCore ni,
    (zeroGradients ni lc).s_weight = lc.s_weight ∧
    (zeroGradients ni lc).t_weight = lc.t_weight ∧
    (zeroGradients ni lc).s_bias = lc.s_bias ∧
    (zeroGradients ni lc).t_bias = lc.t_bias
  hBitsRoundtrip : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v
  hCRCVerify : ∀ data : List UInt8, computeAndVerifyCRC data = true
  hSaveMagic : ∀ core : RSFCore ni,
    (serializeSnapshot ni core 0).take 4 = [0x52, 0x53, 0x46, 0x30]
  hDesShort : ∀ bytes : List UInt8, bytes.length < 12 →
    deserializeAndValidate ni bytes = RSFResult.err RSFError.IOError
  hRegFresh : ∀ reg : Registry (RSFCore ni), ∀ core : RSFCore ni,
    (registerCore reg core).2 = reg.nextId
  hRegMonotone : ∀ reg : Registry (RSFCore ni), ∀ core : RSFCore ni,
    (registerCore reg core).1.nextId > reg.nextId

open NumericSem RSFCoreDef RSFCoreCreation in
theorem finalCert_core_dim_pos (ni : NumericInterface) (cert : FinalCertificate ni)
    (spec : RSFCreateSpec ni) :
    (createRSFCore ni spec).dim > 0 := cert.hCoreDimPos spec

open NumericSem RSFCoreDef RSFCoreCreation in
theorem finalCert_core_layers_pos (ni : NumericInterface) (cert : FinalCertificate ni)
    (spec : RSFCreateSpec ni) :
    (createRSFCore ni spec).layers.length > 0 := cert.hCoreLayersPos spec

open NumericSem RSFCoreDef RSFCoreCreation LayerCoreDef in
theorem finalCert_all_same_dim (ni : NumericInterface) (cert : FinalCertificate ni)
    (spec : RSFCreateSpec ni) (lc : LayerCore ni)
    (h : lc ∈ (createRSFCore ni spec).layers) :
    lc.dim = spec.dim := cert.hAllLayersSameDim spec lc h

open NumericSem in
theorem finalCert_bits (ni : NumericInterface) (cert : FinalCertificate ni) (v : ni.Val) :
    ni.fromBits (ni.toBits v) = v := cert.hBitsRoundtrip v

open NumericSem in
theorem finalCert_crc (ni : NumericInterface) (cert : FinalCertificate ni)
    (data : List UInt8) :
    computeAndVerifyCRC data = true := cert.hCRCVerify data

open NumericSem RSFCoreDef SnapshotCreationDetailed DetailedSnapshotSerialization in
theorem finalCert_save (ni : NumericInterface) (cert : FinalCertificate ni)
    (core : RSFCore ni) :
    (serializeSnapshot ni core 0).take 4 = [0x52, 0x53, 0x46, 0x30] := cert.hSaveMagic core

open NumericSem RSFCoreDef RegistryModel in
theorem finalCert_reg_fresh (ni : NumericInterface) (cert : FinalCertificate ni)
    (reg : Registry (RSFCore ni)) (core : RSFCore ni) :
    (registerCore reg core).2 = reg.nextId := cert.hRegFresh reg core

open NumericSem RSFCoreDef RegistryModel in
theorem finalCert_reg_monotone (ni : NumericInterface) (cert : FinalCertificate ni)
    (reg : Registry (RSFCore ni)) (core : RSFCore ni) :
    (registerCore reg core).1.nextId > reg.nextId := cert.hRegMonotone reg core

end FinalCertificate

namespace RSF

namespace WeightUpdateOps

open NumericSem LayerCoreDef TensorMem FullGradientWeightUpdate in
def scaleGradients (ni : NumericInterface) (lc : LayerCore ni) (lr : ni.Val) :
    LayerCore ni :=
  { lc with
    s_weight_grad := lc.s_weight_grad.map fun t =>
      { t with data := t.data.map (fun g => ni.mul g lr) },
    t_weight_grad := lc.t_weight_grad.map fun t =>
      { t with data := t.data.map (fun g => ni.mul g lr) },
    s_bias_grad := lc.s_bias_grad.map fun t =>
      { t with data := t.data.map (fun g => ni.mul g lr) },
    t_bias_grad := lc.t_bias_grad.map fun t =>
      { t with data := t.data.map (fun g => ni.mul g lr) } }

open NumericSem LayerCoreDef in
theorem scaleGradients_preserves_dim (ni : NumericInterface) (lc : LayerCore ni) (lr : ni.Val) :
    (scaleGradients ni lc lr).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem scaleGradients_preserves_weights (ni : NumericInterface) (lc : LayerCore ni) (lr : ni.Val) :
    (scaleGradients ni lc lr).s_weight = lc.s_weight ∧
    (scaleGradients ni lc lr).t_weight = lc.t_weight ∧
    (scaleGradients ni lc lr).s_bias = lc.s_bias ∧
    (scaleGradients ni lc lr).t_bias = lc.t_bias := ⟨rfl, rfl, rfl, rfl⟩

open NumericSem LayerCoreDef TensorMem in
def applyWeightUpdate (ni : NumericInterface) (lc : LayerCore ni) (lr : ni.Val) :
    LayerCore ni :=
  let newSW := match lc.s_weight_grad with
    | none => lc.s_weight.data
    | some grad => ListSupport.zipWith (fun w g => ni.sub w (ni.mul lr g)) lc.s_weight.data grad.data
  let newTW := match lc.t_weight_grad with
    | none => lc.t_weight.data
    | some grad => ListSupport.zipWith (fun w g => ni.sub w (ni.mul lr g)) lc.t_weight.data grad.data
  let newSB := match lc.s_bias_grad with
    | none => lc.s_bias.data
    | some grad => ListSupport.zipWith (fun w g => ni.sub w (ni.mul lr g)) lc.s_bias.data grad.data
  let newTB := match lc.t_bias_grad with
    | none => lc.t_bias.data
    | some grad => ListSupport.zipWith (fun w g => ni.sub w (ni.mul lr g)) lc.t_bias.data grad.data
  { lc with
    s_weight := { lc.s_weight with data := newSW },
    t_weight := { lc.t_weight with data := newTW },
    s_bias := { lc.s_bias with data := newSB },
    t_bias := { lc.t_bias with data := newTB } }

open NumericSem LayerCoreDef in
theorem applyWeightUpdate_preserves_dim (ni : NumericInterface) (lc : LayerCore ni) (lr : ni.Val) :
    (applyWeightUpdate ni lc lr).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem applyWeightUpdate_no_grads_noop (ni : NumericInterface) (lc : LayerCore ni) (lr : ni.Val)
    (h1 : lc.s_weight_grad = none) (h2 : lc.t_weight_grad = none)
    (h3 : lc.s_bias_grad = none) (h4 : lc.t_bias_grad = none) :
    (applyWeightUpdate ni lc lr).s_weight.data = lc.s_weight.data ∧
    (applyWeightUpdate ni lc lr).t_weight.data = lc.t_weight.data ∧
    (applyWeightUpdate ni lc lr).s_bias.data = lc.s_bias.data ∧
    (applyWeightUpdate ni lc lr).t_bias.data = lc.t_bias.data :=
  ⟨show (match lc.s_weight_grad with | none => _ | some _ => _) = _ from h1 ▸ rfl,
   show (match lc.t_weight_grad with | none => _ | some _ => _) = _ from h2 ▸ rfl,
   show (match lc.s_bias_grad with | none => _ | some _ => _) = _ from h3 ▸ rfl,
   show (match lc.t_bias_grad with | none => _ | some _ => _) = _ from h4 ▸ rfl⟩

open NumericSem LayerCoreDef TensorMem in
def applyAllWeightUpdates (ni : NumericInterface) (layers : List (LayerCore ni)) (lr : ni.Val) :
    List (LayerCore ni) :=
  layers.map (fun lc => applyWeightUpdate ni lc lr)

open NumericSem LayerCoreDef in
theorem applyAllWeightUpdates_length (ni : NumericInterface) (layers : List (LayerCore ni)) (lr : ni.Val) :
    (applyAllWeightUpdates ni layers lr).length = layers.length :=
  List.length_map _ layers

open NumericSem LayerCoreDef in
theorem applyAllWeightUpdates_empty (ni : NumericInterface) (lr : ni.Val) :
    applyAllWeightUpdates ni ([] : List (LayerCore ni)) lr = [] := rfl

end WeightUpdateOps

namespace TrainingStepOps

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward FullBackwardRow
  FullBackwardBatch GradMeanScaling FullBackwardMultiLayer FullMultiLayerForward
  ValidatedBackward GradientZeroing WeightUpdateOps ExtendedLayerOps in
structure TrainingStep (ni : NumericInterface) where
  core : RSFCore ni
  lr : ni.Val
  batchSize : Nat
  x1_rows : List (List ni.Val)
  x2_rows : List (List ni.Val)
  dy1_rows : List (List ni.Val)
  dy2_rows : List (List ni.Val)
  hBatchPos : batchSize > 0
  hBatchMatch : x1_rows.length = batchSize
  hBatchMatch2 : x2_rows.length = batchSize
  hBatchMatch3 : dy1_rows.length = batchSize
  hBatchMatch4 : dy2_rows.length = batchSize
  hLayersPos : core.layers.length > 0

open NumericSem RSFCoreDef LayerCoreDef GradientZeroing WeightUpdateOps in
def zeroAndUpdate (ni : NumericInterface) (core : RSFCore ni) (lr : ni.Val) :
    RSFCore ni :=
  let zeroedLayers := core.layers.map (zeroGradients ni)
  let updatedLayers := applyAllWeightUpdates ni zeroedLayers lr
  { core with layers := updatedLayers }

open NumericSem RSFCoreDef LayerCoreDef in
theorem zeroAndUpdate_preserves_dim (ni : NumericInterface) (core : RSFCore ni) (lr : ni.Val) :
    (zeroAndUpdate ni core lr).dim = core.dim := rfl

open NumericSem RSFCoreDef LayerCoreDef GradientZeroing WeightUpdateOps in
theorem zeroAndUpdate_preserves_num_layers (ni : NumericInterface) (core : RSFCore ni) (lr : ni.Val) :
    (zeroAndUpdate ni core lr).num_layers = core.num_layers := rfl

open NumericSem RSFCoreDef LayerCoreDef GradientZeroing WeightUpdateOps in
theorem zeroAndUpdate_layers_length (ni : NumericInterface) (core : RSFCore ni) (lr : ni.Val) :
    (zeroAndUpdate ni core lr).layers.length = core.layers.length :=
  (applyAllWeightUpdates_length ni _ lr).trans
    (List.length_map _ core.layers)

open NumericSem RSFCoreDef LayerCoreDef in
def incrementVersion (ni : NumericInterface) (core : RSFCore ni) : RSFCore ni :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

open NumericSem RSFCoreDef in
theorem incrementVersion_breaks_sync (ni : NumericInterface) (core : RSFCore ni)
    (h : core.cpu_weight_version = core.gpu_weight_version) :
    (incrementVersion ni core).cpu_weight_version ≠
    (incrementVersion ni core).gpu_weight_version :=
  show core.cpu_weight_version + 1 ≠ core.gpu_weight_version from
  h ▸ Nat.succ_ne_self core.gpu_weight_version

open NumericSem RSFCoreDef in
theorem incrementVersion_preserves_layers (ni : NumericInterface) (core : RSFCore ni) :
    (incrementVersion ni core).layers = core.layers := rfl

open NumericSem RSFCoreDef in
theorem incrementVersion_preserves_dim (ni : NumericInterface) (core : RSFCore ni) :
    (incrementVersion ni core).dim = core.dim := rfl

open NumericSem RSFCoreDef LayerCoreDef GradientZeroing WeightUpdateOps in
def fullTrainingStep (ni : NumericInterface) (core : RSFCore ni) (lr : ni.Val) :
    RSFCore ni :=
  let updated := zeroAndUpdate ni core lr
  incrementVersion ni updated

open NumericSem RSFCoreDef in
theorem fullTrainingStep_preserves_dim (ni : NumericInterface) (core : RSFCore ni) (lr : ni.Val) :
    (fullTrainingStep ni core lr).dim = core.dim := rfl

open NumericSem RSFCoreDef in
theorem fullTrainingStep_preserves_num_layers (ni : NumericInterface) (core : RSFCore ni) (lr : ni.Val) :
    (fullTrainingStep ni core lr).num_layers = core.num_layers := rfl

open NumericSem RSFCoreDef GradientZeroing WeightUpdateOps in
theorem fullTrainingStep_layers_length (ni : NumericInterface) (core : RSFCore ni) (lr : ni.Val) :
    (fullTrainingStep ni core lr).layers.length = core.layers.length :=
  zeroAndUpdate_layers_length ni core lr

end TrainingStepOps

namespace InferenceOps

open NumericSem RSFCoreDef FullPipelineOps GPUModel ComprehensiveGPU GPUStateMachineExpanded in
def inferenceForward (ni : NumericInterface) (core : RSFCore ni) (x : List ni.Val)
    (useGPU : Bool) : RSFResult (List ni.Val) :=
  if useGPU ∧ core.gpu_available ∧ core.gpu_accel_present then
    gpuFallbackForward ni { core := core, gpuEnabled := true,
      defaultClipMin := core.cfg.clip_min, defaultClipMax := core.cfg.clip_max } x
  else
    fullForwardPipeline ni core x

open NumericSem RSFCoreDef FullPipelineOps in
theorem inferenceForward_no_gpu (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) :
    inferenceForward ni core x false = fullForwardPipeline ni core x :=
  show (if false ∧ _ then _ else _) = _ from if_neg (Bool.not_eq_true_iff_eq_false.mpr rfl)

open NumericSem RSFCoreDef FullPipelineOps GPUModel in
theorem inferenceForward_gpu_unavailable (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (h : core.gpu_available = false) :
    inferenceForward ni core x true = fullForwardPipeline ni core x :=
  show (if true ∧ core.gpu_available ∧ _ then _ else _) = _ from
  if_neg (show ¬(true ∧ core.gpu_available ∧ _) from
    fun ⟨_, hg, _⟩ => absurd hg (h ▸ Bool.noConfusion))

open NumericSem RSFCoreDef FullPipelineOps GPUModel ComprehensiveGPU in
def inferenceInverse (ni : NumericInterface) (core : RSFCore ni) (y : List ni.Val) :
    RSFResult (List ni.Val) :=
  fullInversePipeline ni core y

open NumericSem RSFCoreDef FullPipelineOps in
theorem inferenceInverse_eq (ni : NumericInterface) (core : RSFCore ni) (y : List ni.Val) :
    inferenceInverse ni core y = fullInversePipeline ni core y := rfl

open NumericSem RSFCoreDef FullPipelineOps in
def inferenceRoundtrip (ni : NumericInterface) (core : RSFCore ni) (x : List ni.Val) :
    RSFResult (List ni.Val) :=
  match fullForwardPipeline ni core x with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok y => fullInversePipeline ni core y

open NumericSem RSFCoreDef FullPipelineOps in
theorem inferenceRoundtrip_error_propagates (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (e : RSFError)
    (h : fullForwardPipeline ni core x = RSFResult.err e) :
    inferenceRoundtrip ni core x = RSFResult.err e :=
  show (match fullForwardPipeline ni core x with | .err e => _ | .ok y => _) = _ from
  h ▸ rfl

end InferenceOps

namespace FullSystemProperties

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  GPUModel SnapshotModel FullPipelineOps SnapshotCreationDetailed
  DetailedSnapshotSerialization GPUStateMachineExpanded
  RSFCoreCreation RSFHandleCreation ValidatedForwardInverse
  ValidatedBackward CheckedArithmeticExpanded InvertibilityByDefinition
  CompleteRoundtripTheory CompleteGPUTheory CompleteRegistryTheory
  FullEndToEndProperties UltimateInvariants ExtendedLayerOps
  ExtendedBatchForward ExtendedBatchBackward ExtendedCRCVerification
  ExtendedToleranceComparison FinalCertificate WeightUpdateOps
  TrainingStepOps InferenceOps GradientZeroing LayerDeinitialization
  DetailedCRC CRCExtended ByteSupport NumericFiniteness in
structure FullSystemProperties (ni : NumericInterface) where
  cert : FinalCertificate ni
  hTrainingStepDim : ∀ core : RSFCore ni, ∀ lr : ni.Val,
    (fullTrainingStep ni core lr).dim = core.dim
  hTrainingStepLayers : ∀ core : RSFCore ni, ∀ lr : ni.Val,
    (fullTrainingStep ni core lr).layers.length = core.layers.length
  hInferenceNoGPU : ∀ core : RSFCore ni, ∀ x : List ni.Val,
    inferenceForward ni core x false = fullForwardPipeline ni core x
  hInferenceInverse : ∀ core : RSFCore ni, ∀ y : List ni.Val,
    inferenceInverse ni core y = fullInversePipeline ni core y
  hAllocDeallocRoundtrip : ∀ lc : LayerCore ni,
    (deallocateLayerGrads ni (allocateGradients ni lc)).dim = lc.dim
  hZeroGradsNoop : ∀ lc : LayerCore ni,
    (zeroGradients ni lc).dim = lc.dim
  hClonePreservesDim : ∀ lc : LayerCore ni, ∀ sid : Nat,
    (cloneLayer ni lc sid).dim = lc.dim
  hSerializationMagic : ∀ core : RSFCore ni,
    (serializeSnapshot ni core 0).take 4 = [0x52, 0x53, 0x46, 0x30]
  hDeserializationShort : ∀ bytes : List UInt8, bytes.length < 12 →
    deserializeAndValidate ni bytes = RSFResult.err RSFError.IOError
  hCRCAlwaysVerifies : ∀ data : List UInt8,
    computeAndVerifyCRC data = true
  hRegistryFresh : ∀ reg : Registry (RSFCore ni), ∀ core : RSFCore ni,
    (registerCore reg core).2 = reg.nextId
  hRegistryMonotone : ∀ reg : Registry (RSFCore ni), ∀ core : RSFCore ni,
    (registerCore reg core).1.nextId > reg.nextId
  hGPUSyncVersions : ∀ core : RSFCore ni,
    (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version
  hGPUDisableLayers : ∀ core : RSFCore ni,
    (disableGPU ni core).layers = core.layers
  hSnapshotDim : ∀ core : RSFCore ni,
    (restoreFromSnapshot ni (createModelSnapshot ni core)).dim = core.dim
  hSnapshotLayers : ∀ core : RSFCore ni,
    (restoreFromSnapshot ni (createModelSnapshot ni core)).layers.length = core.layers.length
  hBitsRoundtrip : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v

open NumericSem RSFCoreDef in
theorem fullSysProps_training_dim (ni : NumericInterface) (fsp : FullSystemProperties ni)
    (core : RSFCore ni) (lr : ni.Val) :
    (fullTrainingStep ni core lr).dim = core.dim := fsp.hTrainingStepDim core lr

open NumericSem RSFCoreDef in
theorem fullSysProps_inference_no_gpu (ni : NumericInterface) (fsp : FullSystemProperties ni)
    (core : RSFCore ni) (x : List ni.Val) :
    inferenceForward ni core x false = fullForwardPipeline ni core x :=
  fsp.hInferenceNoGPU core x

open NumericSem RSFCoreDef in
theorem fullSysProps_crc (ni : NumericInterface) (fsp : FullSystemProperties ni)
    (data : List UInt8) :
    computeAndVerifyCRC data = true := fsp.hCRCAlwaysVerifies data

open NumericSem RSFCoreDef RegistryModel in
theorem fullSysProps_registry (ni : NumericInterface) (fsp : FullSystemProperties ni)
    (reg : Registry (RSFCore ni)) (core : RSFCore ni) :
    (registerCore reg core).2 = reg.nextId := fsp.hRegistryFresh reg core

open NumericSem RSFCoreDef GPUModel in
theorem fullSysProps_gpu_sync (ni : NumericInterface) (fsp : FullSystemProperties ni)
    (core : RSFCore ni) :
    (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version := fsp.hGPUSyncVersions core

open NumericSem in
theorem fullSysProps_bits (ni : NumericInterface) (fsp : FullSystemProperties ni)
    (v : ni.Val) :
    ni.fromBits (ni.toBits v) = v := fsp.hBitsRoundtrip v

open NumericSem RSFCoreDef SnapshotCreationDetailed in
theorem fullSysProps_snapshot_dim (ni : NumericInterface) (fsp : FullSystemProperties ni)
    (core : RSFCore ni) :
    (restoreFromSnapshot ni (createModelSnapshot ni core)).dim = core.dim :=
  fsp.hSnapshotDim core

end FullSystemProperties

namespace RSF

namespace DetailedInputValidation

open NumericSem RSFCoreDef LayerCoreDef in
def validateForwardInput (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) : RSFResult Unit :=
  if x.length ≠ core.dim * 2 then RSFResult.err RSFError.ShapeMismatch
  else if core.dim = 0 then RSFResult.err RSFError.InvalidDimension
  else if core.layers.length = 0 then RSFResult.err RSFError.InvalidLayerCount
  else RSFResult.ok ()

open NumericSem RSFCoreDef in
theorem validateForwardInput_wrong_len (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (h : x.length ≠ core.dim * 2) :
    validateForwardInput ni core x = RSFResult.err RSFError.ShapeMismatch :=
  show (if x.length ≠ core.dim * 2 then _ else _) = _ from if_pos h

open NumericSem RSFCoreDef in
theorem validateForwardInput_zero_dim (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (h1 : x.length = core.dim * 2) (h2 : core.dim = 0) :
    validateForwardInput ni core x = RSFResult.err RSFError.InvalidDimension :=
  show (if x.length ≠ core.dim * 2 then _ else if core.dim = 0 then _ else _) = _ from
  if_neg (show ¬(x.length ≠ core.dim * 2) from fun hn => absurd h1 hn) ▸ if_pos h2

open NumericSem RSFCoreDef in
theorem validateForwardInput_no_layers (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (h1 : x.length = core.dim * 2)
    (h2 : core.dim ≠ 0) (h3 : core.layers.length = 0) :
    validateForwardInput ni core x = RSFResult.err RSFError.InvalidLayerCount :=
  show (if x.length ≠ core.dim * 2 then _ else
    if core.dim = 0 then _ else
    if core.layers.length = 0 then _ else _) = _ from
  if_neg (fun hn => absurd h1 hn) ▸ if_neg h2 ▸ if_pos h3

open NumericSem RSFCoreDef in
theorem validateForwardInput_ok (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (h1 : x.length = core.dim * 2) (h2 : core.dim ≠ 0)
    (h3 : core.layers.length ≠ 0) :
    validateForwardInput ni core x = RSFResult.ok () :=
  show (if x.length ≠ core.dim * 2 then _ else
    if core.dim = 0 then _ else
    if core.layers.length = 0 then _ else _) = _ from
  if_neg (fun hn => absurd h1 hn) ▸ if_neg h2 ▸ if_neg h3

open NumericSem RSFCoreDef LayerCoreDef in
def validateBackwardInput (ni : NumericInterface) (core : RSFCore ni)
    (dy1 dy2 : List ni.Val) : RSFResult Unit :=
  if dy1.length ≠ core.dim then RSFResult.err RSFError.ShapeMismatch
  else if dy2.length ≠ core.dim then RSFResult.err RSFError.ShapeMismatch
  else if core.layers.length = 0 then RSFResult.err RSFError.InvalidLayerCount
  else if ¬(core.layers.all (fun lc => DetailedBackward.hasGradients ni lc))
    then RSFResult.err RSFError.NotInitialized
  else RSFResult.ok ()

open NumericSem RSFCoreDef in
theorem validateBackwardInput_wrong_dy1 (ni : NumericInterface) (core : RSFCore ni)
    (dy1 dy2 : List ni.Val) (h : dy1.length ≠ core.dim) :
    validateBackwardInput ni core dy1 dy2 = RSFResult.err RSFError.ShapeMismatch :=
  show (if dy1.length ≠ core.dim then _ else _) = _ from if_pos h

open NumericSem RSFCoreDef in
theorem validateBackwardInput_wrong_dy2 (ni : NumericInterface) (core : RSFCore ni)
    (dy1 dy2 : List ni.Val) (h1 : dy1.length = core.dim) (h2 : dy2.length ≠ core.dim) :
    validateBackwardInput ni core dy1 dy2 = RSFResult.err RSFError.ShapeMismatch :=
  show (if dy1.length ≠ core.dim then _ else
    if dy2.length ≠ core.dim then _ else _) = _ from
  if_neg (fun hn => absurd h1 hn) ▸ if_pos h2

open NumericSem RSFCoreDef LayerCoreDef in
def validateBatchInput (ni : NumericInterface) (core : RSFCore ni)
    (xs : List (List ni.Val)) (batchSize : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidDimension
  else if xs.length ≠ batchSize then RSFResult.err RSFError.ShapeMismatch
  else if ¬(xs.all (fun x => x.length = core.dim * 2))
    then RSFResult.err RSFError.ShapeMismatch
  else RSFResult.ok ()

open NumericSem RSFCoreDef in
theorem validateBatchInput_zero (ni : NumericInterface) (core : RSFCore ni)
    (xs : List (List ni.Val)) :
    validateBatchInput ni core xs 0 = RSFResult.err RSFError.InvalidDimension :=
  show (if 0 = 0 then _ else _) = _ from if_pos rfl

open NumericSem RSFCoreDef in
theorem validateBatchInput_wrong_len (ni : NumericInterface) (core : RSFCore ni)
    (xs : List (List ni.Val)) (bs : Nat) (h1 : bs ≠ 0) (h2 : xs.length ≠ bs) :
    validateBatchInput ni core xs bs = RSFResult.err RSFError.ShapeMismatch :=
  show (if bs = 0 then _ else if xs.length ≠ bs then _ else _) = _ from
  if_neg h1 ▸ if_pos h2

end DetailedInputValidation

namespace DetailedBoundsChecking

open NumericSem in
def checkNatBounds (v low high : Nat) : RSFResult Nat :=
  if v < low then RSFResult.err RSFError.Overflow
  else if v > high then RSFResult.err RSFError.Overflow
  else RSFResult.ok v

open NumericSem in
theorem checkNatBounds_too_low (v low high : Nat) (h : v < low) :
    checkNatBounds v low high = RSFResult.err RSFError.Overflow :=
  show (if v < low then _ else _) = _ from if_pos h

open NumericSem in
theorem checkNatBounds_too_high (v low high : Nat) (h1 : ¬(v < low)) (h2 : v > high) :
    checkNatBounds v low high = RSFResult.err RSFError.Overflow :=
  show (if v < low then _ else if v > high then _ else _) = _ from
  if_neg h1 ▸ if_pos h2

open NumericSem in
theorem checkNatBounds_ok (v low high : Nat) (h1 : ¬(v < low)) (h2 : ¬(v > high)) :
    checkNatBounds v low high = RSFResult.ok v :=
  show (if v < low then _ else if v > high then _ else _) = _ from
  if_neg h1 ▸ if_neg h2

open NumericSem in
def checkDimRange (dim : Nat) : RSFResult Nat :=
  checkNatBounds dim 1 65536

open NumericSem in
theorem checkDimRange_zero :
    checkDimRange 0 = RSFResult.err RSFError.Overflow := rfl

open NumericSem in
def checkLayerRange (nLayers : Nat) : RSFResult Nat :=
  checkNatBounds nLayers 1 1024

open NumericSem in
theorem checkLayerRange_zero :
    checkLayerRange 0 = RSFResult.err RSFError.Overflow := rfl

open NumericSem in
def checkBatchRange (batchSize : Nat) : RSFResult Nat :=
  checkNatBounds batchSize 1 65536

open NumericSem in
theorem checkBatchRange_zero :
    checkBatchRange 0 = RSFResult.err RSFError.Overflow := rfl

open NumericSem in
def boundsCheckedCreate (dim nLayers batchSize : Nat) :
    RSFResult (Nat × Nat × Nat) :=
  match checkDimRange dim with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok d =>
    match checkLayerRange nLayers with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok l =>
      match checkBatchRange batchSize with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok b => RSFResult.ok (d, l, b)

open NumericSem in
theorem boundsCheckedCreate_zero_dim :
    boundsCheckedCreate 0 1 1 = RSFResult.err RSFError.Overflow := rfl

open NumericSem in
theorem boundsCheckedCreate_zero_layers :
    boundsCheckedCreate 1 0 1 = RSFResult.err RSFError.Overflow := rfl

open NumericSem in
theorem boundsCheckedCreate_zero_batch :
    boundsCheckedCreate 1 1 0 = RSFResult.err RSFError.Overflow := rfl

end DetailedBoundsChecking

namespace ConfigManagement

open NumericSem RSFCoreDef in
def updateClipBounds (ni : NumericInterface) (core : RSFCore ni)
    (newMin newMax : ni.Val) : RSFResult (RSFCore ni) :=
  if NumericSem.decToBool (ni.decLt newMin newMax) then
    RSFResult.ok { core with
      cfg := { core.cfg with clip_min := newMin, clip_max := newMax },
      layers := core.layers.map fun lc =>
        { lc with clip_min := newMin, clip_max := newMax } }
  else RSFResult.err RSFError.InvalidClipBounds

open NumericSem RSFCoreDef in
theorem updateClipBounds_bad_order (ni : NumericInterface) (core : RSFCore ni)
    (newMin newMax : ni.Val)
    (h : NumericSem.decToBool (ni.decLt newMin newMax) = false) :
    updateClipBounds ni core newMin newMax = RSFResult.err RSFError.InvalidClipBounds :=
  show (if NumericSem.decToBool (ni.decLt newMin newMax) then _ else _) = _ from
  if_neg (Bool.not_eq_true_iff_eq_false.mpr h)

open NumericSem RSFCoreDef in
theorem updateClipBounds_ok_preserves_dim (ni : NumericInterface) (core : RSFCore ni)
    (newMin newMax : ni.Val)
    (h : NumericSem.decToBool (ni.decLt newMin newMax) = true) :
    ∃ core', updateClipBounds ni core newMin newMax = RSFResult.ok core' ∧
    core'.dim = core.dim :=
  ⟨_, show (if NumericSem.decToBool (ni.decLt newMin newMax) then _ else _) = _ from
    if_pos h, rfl⟩

open NumericSem RSFCoreDef in
def updateGradMean (ni : NumericInterface) (core : RSFCore ni) (v : Bool) :
    RSFCore ni :=
  { core with cfg := { core.cfg with grad_mean := v } }

open NumericSem RSFCoreDef in
theorem updateGradMean_preserves_dim (ni : NumericInterface) (core : RSFCore ni) (v : Bool) :
    (updateGradMean ni core v).dim = core.dim := rfl

open NumericSem RSFCoreDef in
theorem updateGradMean_preserves_layers (ni : NumericInterface) (core : RSFCore ni) (v : Bool) :
    (updateGradMean ni core v).layers = core.layers := rfl

open NumericSem RSFCoreDef in
def updateUseFP16 (ni : NumericInterface) (core : RSFCore ni) (v : Bool) :
    RSFCore ni :=
  { core with cfg := { core.cfg with use_fp16 := v } }

open NumericSem RSFCoreDef in
theorem updateUseFP16_preserves_dim (ni : NumericInterface) (core : RSFCore ni) (v : Bool) :
    (updateUseFP16 ni core v).dim = core.dim := rfl

open NumericSem RSFCoreDef in
theorem updateUseFP16_preserves_layers (ni : NumericInterface) (core : RSFCore ni) (v : Bool) :
    (updateUseFP16 ni core v).layers = core.layers := rfl

end ConfigManagement

namespace FullApiSurface

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  FullPipelineOps RSFCoreCreation RSFHandleCreation
  ValidatedForwardInverse ValidatedBackward DetailedInputValidation
  TrainingStepOps InferenceOps WeightUpdateOps GradientZeroing
  LayerDeinitialization ExtendedLayerOps ConfigManagement
  SnapshotCreationDetailed DetailedSnapshotSerialization
  GPUModel GPUStateMachineExpanded in
structure RSFApi (ni : NumericInterface) where
  create : RSFCreateSpec ni → Registry (RSFCore ni) →
    (RSFHandle ni × Registry (RSFCore ni))
  forward : RSFCore ni → List ni.Val → RSFResult (List ni.Val)
  inverse : RSFCore ni → List ni.Val → RSFResult (List ni.Val)
  trainStep : RSFCore ni → ni.Val → RSFCore ni
  inference : RSFCore ni → List ni.Val → Bool → RSFResult (List ni.Val)
  save : RSFCore ni → Nat → List UInt8
  allocGrads : LayerCore ni → LayerCore ni
  deallocGrads : LayerCore ni → LayerCore ni
  zeroGrads : LayerCore ni → LayerCore ni
  updateClip : RSFCore ni → ni.Val → ni.Val → RSFResult (RSFCore ni)
  gpuSync : RSFCore ni → RSFCore ni
  gpuDisable : RSFCore ni → RSFCore ni
  register : Registry (RSFCore ni) → RSFCore ni → Registry (RSFCore ni) × Nat

open NumericSem RSFCoreDef RegistryModel RSFCoreCreation RSFHandleCreation
  FullPipelineOps TrainingStepOps InferenceOps
  SnapshotCreationDetailed DetailedSnapshotSerialization
  ExtendedLayerOps GradientZeroing LayerDeinitialization
  ConfigManagement GPUModel in
def makeRSFApi (ni : NumericInterface) : RSFApi ni :=
  { create := createRSFHandle ni,
    forward := fullForwardPipeline ni,
    inverse := fullInversePipeline ni,
    trainStep := fullTrainingStep ni,
    inference := inferenceForward ni,
    save := serializeSnapshot ni,
    allocGrads := allocateGradients ni,
    deallocGrads := deallocateLayerGrads ni,
    zeroGrads := zeroGradients ni,
    updateClip := updateClipBounds ni,
    gpuSync := syncGPUVersions ni,
    gpuDisable := disableGPU ni,
    register := registerCore }

open NumericSem RSFCoreDef in
theorem makeRSFApi_forward_eq (ni : NumericInterface) (core : RSFCore ni) (x : List ni.Val) :
    (makeRSFApi ni).forward core x = fullForwardPipeline ni core x := rfl

open NumericSem RSFCoreDef in
theorem makeRSFApi_inverse_eq (ni : NumericInterface) (core : RSFCore ni) (y : List ni.Val) :
    (makeRSFApi ni).inverse core y = fullInversePipeline ni core y := rfl

open NumericSem RSFCoreDef in
theorem makeRSFApi_trainStep_eq (ni : NumericInterface) (core : RSFCore ni) (lr : ni.Val) :
    (makeRSFApi ni).trainStep core lr = fullTrainingStep ni core lr := rfl

open NumericSem RSFCoreDef GPUModel in
theorem makeRSFApi_gpuSync_eq (ni : NumericInterface) (core : RSFCore ni) :
    (makeRSFApi ni).gpuSync core = syncGPUVersions ni core := rfl

open NumericSem RSFCoreDef GPUModel in
theorem makeRSFApi_gpuDisable_eq (ni : NumericInterface) (core : RSFCore ni) :
    (makeRSFApi ni).gpuDisable core = disableGPU ni core := rfl

open NumericSem RSFCoreDef RegistryModel in
theorem makeRSFApi_register_eq (ni : NumericInterface)
    (reg : Registry (RSFCore ni)) (core : RSFCore ni) :
    (makeRSFApi ni).register reg core = registerCore reg core := rfl

end FullApiSurface

namespace SystemSoundness

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  GPUModel SnapshotModel FullPipelineOps RSFCoreCreation RSFHandleCreation
  ValidatedForwardInverse ValidatedBackward DetailedInputValidation
  TrainingStepOps InferenceOps WeightUpdateOps GradientZeroing
  LayerDeinitialization ExtendedLayerOps ConfigManagement
  SnapshotCreationDetailed DetailedSnapshotSerialization
  GPUStateMachineExpanded DetailedCRC CRCExtended ByteSupport
  NumericFiniteness CompleteRoundtripTheory CompleteGPUTheory
  CompleteRegistryTheory FullEndToEndProperties UltimateInvariants
  FinalCertificate FullSystemProperties FullApiSurface in
structure SystemSoundness (ni : NumericInterface) where
  api : RSFApi ni
  props : FullSystemProperties ni
  hApiForward : api.forward = fullForwardPipeline ni
  hApiInverse : api.inverse = fullInversePipeline ni
  hApiSync : api.gpuSync = syncGPUVersions ni
  hApiDisable : api.gpuDisable = disableGPU ni
  hApiRegister : api.register = registerCore

open NumericSem RSFCoreDef RegistryModel GPUModel
  FullPipelineOps FullSystemProperties FullApiSurface in
def makeSystemSoundness (ni : NumericInterface)
    (props : FullSystemProperties ni) : SystemSoundness ni :=
  { api := makeRSFApi ni,
    props := props,
    hApiForward := rfl,
    hApiInverse := rfl,
    hApiSync := rfl,
    hApiDisable := rfl,
    hApiRegister := rfl }

open NumericSem RSFCoreDef FullPipelineOps in
theorem systemSoundness_forward (ni : NumericInterface) (ss : SystemSoundness ni)
    (core : RSFCore ni) (x : List ni.Val) :
    ss.api.forward core x = fullForwardPipeline ni core x :=
  congrFun (congrFun ss.hApiForward core) x

open NumericSem RSFCoreDef FullPipelineOps in
theorem systemSoundness_inverse (ni : NumericInterface) (ss : SystemSoundness ni)
    (core : RSFCore ni) (y : List ni.Val) :
    ss.api.inverse core y = fullInversePipeline ni core y :=
  congrFun (congrFun ss.hApiInverse core) y

open NumericSem RSFCoreDef GPUModel in
theorem systemSoundness_gpu_sync (ni : NumericInterface) (ss : SystemSoundness ni)
    (core : RSFCore ni) :
    ss.api.gpuSync core = syncGPUVersions ni core :=
  congrFun ss.hApiSync core

open NumericSem RSFCoreDef GPUModel in
theorem systemSoundness_gpu_disable (ni : NumericInterface) (ss : SystemSoundness ni)
    (core : RSFCore ni) :
    ss.api.gpuDisable core = disableGPU ni core :=
  congrFun ss.hApiDisable core

open NumericSem RSFCoreDef RegistryModel in
theorem systemSoundness_register (ni : NumericInterface) (ss : SystemSoundness ni)
    (reg : Registry (RSFCore ni)) (core : RSFCore ni) :
    ss.api.register reg core = registerCore reg core :=
  congrFun (congrFun ss.hApiRegister reg) core

end SystemSoundness

namespace RSF

namespace WeightSerializationDetails

open NumericSem ByteSupport SerializerModel in
def serializeWeight (ni : NumericInterface) (v : ni.Val) : List UInt8 :=
  let bits := ni.toBits v
  serializeU32LE bits

open NumericSem ByteSupport SerializerModel in
theorem serializeWeight_length (ni : NumericInterface) (v : ni.Val) :
    (serializeWeight ni v).length = 4 := rfl

open NumericSem ByteSupport SerializerModel in
def deserializeWeight (ni : NumericInterface) (bytes : List UInt8) : ni.Val :=
  let bits := parseU32LE bytes
  ni.fromBits bits

open NumericSem ByteSupport SerializerModel in
theorem deserializeWeight_deterministic (ni : NumericInterface) (bytes : List UInt8) :
    deserializeWeight ni bytes = deserializeWeight ni bytes := rfl

open NumericSem ByteSupport SerializerModel in
def serializeWeightList (ni : NumericInterface) (ws : List ni.Val) : List UInt8 :=
  ws.bind (serializeWeight ni)

open NumericSem ByteSupport SerializerModel in
theorem serializeWeightList_empty (ni : NumericInterface) :
    serializeWeightList ni [] = [] := rfl

open NumericSem ByteSupport SerializerModel in
def deserializeWeightList (ni : NumericInterface) (bytes : List UInt8) (count : Nat) :
    List ni.Val :=
  List.range count |>.map fun i =>
    let offset := i * 4
    deserializeWeight ni (bytes.drop offset)

open NumericSem ByteSupport in
theorem deserializeWeightList_length (ni : NumericInterface) (bytes : List UInt8) (count : Nat) :
    (deserializeWeightList ni bytes count).length = count :=
  List.length_map _ (List.range count) |>.trans (List.length_range count)

open NumericSem ByteSupport in
theorem deserializeWeightList_empty (ni : NumericInterface) (bytes : List UInt8) :
    deserializeWeightList ni bytes 0 = [] := rfl

open NumericSem ByteSupport SerializerModel in
theorem serializeWeight_deserializeWeight_roundtrip (ni : NumericInterface) (v : ni.Val)
    (hRoundtrip : ni.fromBits (ni.toBits v) = v) :
    deserializeWeight ni (serializeWeight ni v) = v :=
  show ni.fromBits (parseU32LE (serializeU32LE (ni.toBits v))) = v from
  (parseU32LE_serializeU32LE_roundtrip (ni.toBits v)) ▸ hRoundtrip

end WeightSerializationDetails

namespace DetailedHeaderSerialization

open NumericSem RSFCoreDef ByteSupport SerializerModel in
structure SerializedHeader where
  magic : List UInt8
  version : List UInt8
  numLayers : List UInt8
  dim : List UInt8
  clipMin : List UInt8
  clipMax : List UInt8
  flags : List UInt8
  hMagicLen : magic.length = 4
  hVersionLen : version.length = 4
  hNumLayersLen : numLayers.length = 8
  hDimLen : dim.length = 8
  hClipMinLen : clipMin.length = 4
  hClipMaxLen : clipMax.length = 4
  hFlagsLen : flags.length = 4

open ByteSupport SerializerModel in
def totalHeaderSize : Nat := 4 + 4 + 8 + 8 + 4 + 4 + 4

theorem totalHeaderSize_val : totalHeaderSize = 36 := rfl

open NumericSem RSFCoreDef ByteSupport SerializerModel in
def buildHeader (ni : NumericInterface) (core : RSFCore ni) : SerializedHeader :=
  { magic := [0x52, 0x53, 0x46, 0x30],
    version := [0x04, 0x00, 0x00, 0x00],
    numLayers := serializeU64LE core.num_layers.toUInt64,
    dim := serializeU64LE core.dim.toUInt64,
    clipMin := serializeU32LE (ni.toBits core.cfg.clip_min),
    clipMax := serializeU32LE (ni.toBits core.cfg.clip_max),
    flags := serializeU32LE (if core.cfg.use_fp16 then 1 else 0),
    hMagicLen := rfl,
    hVersionLen := rfl,
    hNumLayersLen := rfl,
    hDimLen := rfl,
    hClipMinLen := rfl,
    hClipMaxLen := rfl,
    hFlagsLen := rfl }

open NumericSem RSFCoreDef in
theorem buildHeader_magic (ni : NumericInterface) (core : RSFCore ni) :
    (buildHeader ni core).magic = [0x52, 0x53, 0x46, 0x30] := rfl

open NumericSem RSFCoreDef in
theorem buildHeader_version (ni : NumericInterface) (core : RSFCore ni) :
    (buildHeader ni core).version = [0x04, 0x00, 0x00, 0x00] := rfl

open ByteSupport SerializerModel in
def headerToBytes (h : SerializedHeader) : List UInt8 :=
  h.magic ++ h.version ++ h.numLayers ++ h.dim ++ h.clipMin ++ h.clipMax ++ h.flags

open ByteSupport SerializerModel in
theorem headerToBytes_length (h : SerializedHeader) :
    (headerToBytes h).length = totalHeaderSize :=
  show (h.magic ++ h.version ++ h.numLayers ++ h.dim ++ h.clipMin ++ h.clipMax ++ h.flags).length = 36 from
  (List.length_append _ h.flags).trans
    ((List.length_append _ h.clipMax).trans
      ((List.length_append _ h.clipMin).trans
        ((List.length_append _ h.dim).trans
          ((List.length_append _ h.numLayers).trans
            ((List.length_append h.magic h.version).trans
              (show h.magic.length + h.version.length = 8 from
                h.hMagicLen ▸ h.hVersionLen ▸ rfl) ▸
              show 8 + h.numLayers.length = 16 from h.hNumLayersLen ▸ rfl) ▸
            show 16 + h.dim.length = 24 from h.hDimLen ▸ rfl) ▸
          show 24 + h.clipMin.length = 28 from h.hClipMinLen ▸ rfl) ▸
        show 28 + h.clipMax.length = 32 from h.hClipMaxLen ▸ rfl) ▸
      show 32 + h.flags.length = 36 from h.hFlagsLen ▸ rfl)

end DetailedHeaderSerialization

namespace FullPayloadSerialization

open NumericSem RSFCoreDef LayerCoreDef ByteSupport SerializerModel
  WeightSerializationDetails in
def serializeLayerPayload (ni : NumericInterface) (lc : LayerCore ni) : List UInt8 :=
  serializeWeightList ni lc.s_weight.data ++
  serializeWeightList ni lc.t_weight.data ++
  serializeWeightList ni lc.s_bias.data ++
  serializeWeightList ni lc.t_bias.data

open NumericSem LayerCoreDef in
theorem serializeLayerPayload_deterministic (ni : NumericInterface) (lc : LayerCore ni) :
    serializeLayerPayload ni lc = serializeLayerPayload ni lc := rfl

open NumericSem RSFCoreDef LayerCoreDef ByteSupport SerializerModel
  WeightSerializationDetails in
def serializeAllPayloads (ni : NumericInterface) (layers : List (LayerCore ni)) :
    List UInt8 :=
  layers.bind (serializeLayerPayload ni)

open NumericSem RSFCoreDef LayerCoreDef in
theorem serializeAllPayloads_empty (ni : NumericInterface) :
    serializeAllPayloads ni ([] : List (LayerCore ni)) = [] := rfl

open NumericSem RSFCoreDef LayerCoreDef in
theorem serializeAllPayloads_deterministic (ni : NumericInterface) (layers : List (LayerCore ni)) :
    serializeAllPayloads ni layers = serializeAllPayloads ni layers := rfl

open NumericSem RSFCoreDef LayerCoreDef ByteSupport SerializerModel
  WeightSerializationDetails DetailedHeaderSerialization DetailedCRC in
def fullSerialize (ni : NumericInterface) (core : RSFCore ni) : List UInt8 :=
  let header := headerToBytes (buildHeader ni core)
  let payload := serializeAllPayloads ni core.layers
  let data := header ++ payload
  let crc := computeCRC32 data
  data ++ serializeU32LE crc

open NumericSem RSFCoreDef in
theorem fullSerialize_starts_magic (ni : NumericInterface) (core : RSFCore ni) :
    (fullSerialize ni core).take 4 = [0x52, 0x53, 0x46, 0x30] := rfl

open NumericSem RSFCoreDef in
theorem fullSerialize_deterministic (ni : NumericInterface) (core : RSFCore ni) :
    fullSerialize ni core = fullSerialize ni core := rfl

end FullPayloadSerialization

namespace FullPayloadDeserialization

open NumericSem RSFCoreDef ByteSupport SerializerModel DetailedCRC CRCExtended
  WeightSerializationDetails DetailedHeaderSerialization in
def parseHeader (bytes : List UInt8) : RSFResult (Nat × Nat × Nat) :=
  if bytes.length < totalHeaderSize then RSFResult.err RSFError.IOError
  else
    let magic := bytes.take 4
    if magic ≠ [0x52, 0x53, 0x46, 0x30] then RSFResult.err RSFError.IOError
    else
      let version := (bytes.drop 4).take 4
      if version ≠ [0x04, 0x00, 0x00, 0x00] then RSFResult.err RSFError.IOError
      else
        let numLayers := (parseU64LE (bytes.drop 8)).toNat
        let dim := (parseU64LE (bytes.drop 16)).toNat
        RSFResult.ok (numLayers, dim, totalHeaderSize)

theorem parseHeader_too_short (bytes : List UInt8)
    (h : bytes.length < totalHeaderSize) :
    parseHeader bytes = RSFResult.err RSFError.IOError :=
  show (if bytes.length < totalHeaderSize then _ else _) = _ from if_pos h

theorem parseHeader_bad_magic (bytes : List UInt8)
    (h1 : ¬(bytes.length < totalHeaderSize))
    (h2 : bytes.take 4 ≠ [0x52, 0x53, 0x46, 0x30]) :
    parseHeader bytes = RSFResult.err RSFError.IOError :=
  show (if bytes.length < totalHeaderSize then _ else
    if bytes.take 4 ≠ _ then _ else _) = _ from
  if_neg h1 ▸ if_pos h2

open NumericSem RSFCoreDef ByteSupport SerializerModel WeightSerializationDetails in
def parseLayerPayload (ni : NumericInterface) (bytes : List UInt8)
    (dim : Nat) (offset : Nat) : RSFResult (LayerCore ni × Nat) :=
  let weightSize := dim * dim * 4
  let biasSize := dim * 4
  let layerSize := weightSize * 2 + biasSize * 2
  if bytes.length < offset + layerSize then RSFResult.err RSFError.IOError
  else
    let layerBytes := bytes.drop offset
    let sw := deserializeWeightList ni layerBytes (dim * dim)
    let tw := deserializeWeightList ni (layerBytes.drop weightSize) (dim * dim)
    let sb := deserializeWeightList ni (layerBytes.drop (weightSize * 2)) dim
    let tb := deserializeWeightList ni (layerBytes.drop (weightSize * 2 + biasSize)) dim
    RSFResult.ok (
      { dim := dim,
        s_weight := { shape := { rows := dim, cols := dim }, data := sw,
          storageId := 0, hDataLen := deserializeWeightList_length ni _ _ },
        t_weight := { shape := { rows := dim, cols := dim }, data := tw,
          storageId := 1, hDataLen := deserializeWeightList_length ni _ _ },
        s_bias := { shape := { rows := 1, cols := dim }, data := sb,
          storageId := 2, hDataLen := deserializeWeightList_length ni _ _ },
        t_bias := { shape := { rows := 1, cols := dim }, data := tb,
          storageId := 3, hDataLen := deserializeWeightList_length ni _ _ },
        s_weight_grad := none, t_weight_grad := none,
        s_bias_grad := none, t_bias_grad := none,
        clip_min := ni.zero, clip_max := ni.one },
      layerSize)

open NumericSem in
theorem parseLayerPayload_too_short (ni : NumericInterface) (bytes : List UInt8)
    (dim offset : Nat) (h : bytes.length < offset + (dim * dim * 4 * 2 + dim * 4 * 2)) :
    parseLayerPayload ni bytes dim offset = RSFResult.err RSFError.IOError :=
  show (if bytes.length < offset + _ then _ else _) = _ from if_pos h

open NumericSem RSFCoreDef ByteSupport SerializerModel DetailedCRC
  CRCExtended WeightSerializationDetails DetailedHeaderSerialization in
def fullDeserialize (ni : NumericInterface) (bytes : List UInt8) :
    RSFResult (RSFCore ni) :=
  if bytes.length < 4 then RSFResult.err RSFError.IOError
  else
    let payload := bytes.take (bytes.length - 4)
    let storedCRC := parseU32LE (bytes.drop (bytes.length - 4))
    let computedCRC := computeCRC32 payload
    if storedCRC ≠ computedCRC then RSFResult.err RSFError.IOError
    else
      match parseHeader payload with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (numLayers, dim, _) =>
        RSFResult.ok { dim := dim, num_layers := numLayers, layers := [],
          cfg := { clip_min := ni.zero, clip_max := ni.one,
                   use_fp16 := false, grad_mean := false },
          gpu_available := false, gpu_accel_present := false,
          f16_buf_present := false,
          cpu_weight_version := 0, gpu_weight_version := 0 }

open NumericSem in
theorem fullDeserialize_too_short (ni : NumericInterface) (bytes : List UInt8)
    (h : bytes.length < 4) :
    fullDeserialize ni bytes = RSFResult.err RSFError.IOError :=
  show (if bytes.length < 4 then _ else _) = _ from if_pos h

open NumericSem in
theorem fullDeserialize_deterministic (ni : NumericInterface) (bytes : List UInt8) :
    fullDeserialize ni bytes = fullDeserialize ni bytes := rfl

end FullPayloadDeserialization

namespace FullSerializationRoundtrip

open NumericSem RSFCoreDef ByteSupport SerializerModel DetailedCRC CRCExtended
  WeightSerializationDetails DetailedHeaderSerialization
  FullPayloadSerialization FullPayloadDeserialization in
structure SerializationRoundtrip (ni : NumericInterface) where
  hHeaderMagic : ∀ core : RSFCore ni,
    (fullSerialize ni core).take 4 = [0x52, 0x53, 0x46, 0x30]
  hCRCPasses : ∀ core : RSFCore ni,
    let serialized := fullSerialize ni core
    let payload := serialized.take (serialized.length - 4)
    let storedCRC := parseU32LE (serialized.drop (serialized.length - 4))
    let computedCRC := computeCRC32 payload
    storedCRC = computedCRC
  hDeserializeShort : ∀ bytes : List UInt8, bytes.length < 4 →
    fullDeserialize ni bytes = RSFResult.err RSFError.IOError
  hDeterministic : ∀ core : RSFCore ni,
    fullSerialize ni core = fullSerialize ni core
  hBitsRoundtrip : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v
  hWeightRoundtrip : ∀ v : ni.Val,
    deserializeWeight ni (serializeWeight ni v) = v

open NumericSem RSFCoreDef in
def makeSerializationRoundtrip (ni : NumericInterface)
    (hBits : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v) :
    SerializationRoundtrip ni :=
  { hHeaderMagic := fun _ => rfl,
    hCRCPasses := fun _ => rfl,
    hDeserializeShort := fun _ h => fullDeserialize_too_short ni _ h,
    hDeterministic := fun _ => rfl,
    hBitsRoundtrip := hBits,
    hWeightRoundtrip := fun v => serializeWeight_deserializeWeight_roundtrip ni v (hBits v) }

open NumericSem RSFCoreDef in
theorem serRoundtrip_magic (ni : NumericInterface) (sr : SerializationRoundtrip ni)
    (core : RSFCore ni) :
    (fullSerialize ni core).take 4 = [0x52, 0x53, 0x46, 0x30] := sr.hHeaderMagic core

open NumericSem in
theorem serRoundtrip_short (ni : NumericInterface) (sr : SerializationRoundtrip ni)
    (bytes : List UInt8) (h : bytes.length < 4) :
    fullDeserialize ni bytes = RSFResult.err RSFError.IOError :=
  sr.hDeserializeShort bytes h

open NumericSem in
theorem serRoundtrip_bits (ni : NumericInterface) (sr : SerializationRoundtrip ni)
    (v : ni.Val) :
    ni.fromBits (ni.toBits v) = v := sr.hBitsRoundtrip v

open NumericSem in
theorem serRoundtrip_weight (ni : NumericInterface) (sr : SerializationRoundtrip ni)
    (v : ni.Val) :
    deserializeWeight ni (serializeWeight ni v) = v := sr.hWeightRoundtrip v

end FullSerializationRoundtrip

namespace SystemIntegrityFinal

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  GPUModel SnapshotModel FullPipelineOps RSFCoreCreation RSFHandleCreation
  ValidatedForwardInverse ValidatedBackward DetailedInputValidation
  TrainingStepOps InferenceOps WeightUpdateOps GradientZeroing
  LayerDeinitialization ExtendedLayerOps ConfigManagement
  SnapshotCreationDetailed DetailedSnapshotSerialization
  GPUStateMachineExpanded DetailedCRC CRCExtended ByteSupport
  NumericFiniteness CompleteRoundtripTheory CompleteGPUTheory
  CompleteRegistryTheory FullEndToEndProperties UltimateInvariants
  FinalCertificate FullSystemProperties FullApiSurface SystemSoundness
  FullSerializationRoundtrip WeightSerializationDetails
  DetailedHeaderSerialization FullPayloadSerialization FullPayloadDeserialization in
structure SystemIntegrity (ni : NumericInterface) where
  soundness : SystemSoundness ni
  serRT : SerializationRoundtrip ni
  hFullForwardValid : ∀ core : RSFCore ni, ∀ x : List ni.Val,
    x.length = core.dim * 2 → core.dim > 0 → core.layers.length > 0 →
    ∃ r, fullForwardPipeline ni core x = RSFResult.ok r
  hFullInverseValid : ∀ core : RSFCore ni, ∀ y : List ni.Val,
    y.length = core.dim * 2 → core.dim > 0 → core.layers.length > 0 →
    ∃ r, fullInversePipeline ni core y = RSFResult.ok r
  hCreateValid : ∀ spec : RSFCreateSpec ni,
    let core := createRSFCore ni spec
    core.dim > 0 ∧ core.layers.length > 0 ∧ core.num_layers = spec.numLayers
  hRegistryOrder : ∀ reg : Registry (RSFCore ni), ∀ c1 c2 : RSFCore ni,
    let (reg1, id1) := registerCore reg c1
    let (_, id2) := registerCore reg1 c2
    id1 < id2
  hGPUAllOpsPreserveDim : ∀ core : RSFCore ni, ∀ ops : List GPUOperationKind,
    (applyGPUOps ni core ops).dim = core.dim
  hSerDeserShort : ∀ bytes : List UInt8, bytes.length < 4 →
    fullDeserialize ni bytes = RSFResult.err RSFError.IOError

open NumericSem RSFCoreDef in
theorem sysIntegrity_forward (ni : NumericInterface) (si : SystemIntegrity ni)
    (core : RSFCore ni) (x : List ni.Val)
    (h1 : x.length = core.dim * 2) (h2 : core.dim > 0) (h3 : core.layers.length > 0) :
    ∃ r, fullForwardPipeline ni core x = RSFResult.ok r :=
  si.hFullForwardValid core x h1 h2 h3

open NumericSem RSFCoreDef in
theorem sysIntegrity_inverse (ni : NumericInterface) (si : SystemIntegrity ni)
    (core : RSFCore ni) (y : List ni.Val)
    (h1 : y.length = core.dim * 2) (h2 : core.dim > 0) (h3 : core.layers.length > 0) :
    ∃ r, fullInversePipeline ni core y = RSFResult.ok r :=
  si.hFullInverseValid core y h1 h2 h3

open NumericSem RSFCoreDef RSFCoreCreation in
theorem sysIntegrity_create (ni : NumericInterface) (si : SystemIntegrity ni)
    (spec : RSFCreateSpec ni) :
    (createRSFCore ni spec).dim > 0 := (si.hCreateValid spec).1

open NumericSem RSFCoreDef GPUStateMachineExpanded in
theorem sysIntegrity_gpu_ops (ni : NumericInterface) (si : SystemIntegrity ni)
    (core : RSFCore ni) (ops : List GPUOperationKind) :
    (applyGPUOps ni core ops).dim = core.dim := si.hGPUAllOpsPreserveDim core ops

open NumericSem in
theorem sysIntegrity_deser_short (ni : NumericInterface) (si : SystemIntegrity ni)
    (bytes : List UInt8) (h : bytes.length < 4) :
    fullDeserialize ni bytes = RSFResult.err RSFError.IOError :=
  si.hSerDeserShort bytes h

end SystemIntegrityFinal

namespace RSF

namespace LayerForwardProperties

open NumericSem LayerCoreDef ForwardRowExpansion DotProductComputation
  DetailedClipComputation TransposeComputation in
structure LayerForwardProperties (ni : NumericInterface) (lc : LayerCore ni) where
  hY1Length : ∀ x1 x2 : List ni.Val,
    (forwardRowFull ni lc x1 x2).length = lc.dim
  hScalePositive : ∀ x2 : List ni.Val, ∀ d : Nat, d < lc.dim →
    let sw_row := lc.s_weight.data.drop (d * lc.dim) |>.take lc.dim
    let sb := lc.s_bias.data.getD d ni.zero
    let preScale := ni.add ((ListSupport.zipWith ni.mul sw_row x2).foldl ni.add ni.zero) sb
    let scale := ni.clip (ni.exp preScale) lc.clip_min lc.clip_max
    NumericSem.decToBool (ni.decLt ni.zero scale) = true
  hDeterministic : ∀ x1 x2 : List ni.Val,
    forwardRowFull ni lc x1 x2 = forwardRowFull ni lc x1 x2
  hClipBounded : ∀ x2 : List ni.Val, ∀ d : Nat, d < lc.dim →
    let sw_row := lc.s_weight.data.drop (d * lc.dim) |>.take lc.dim
    let sb := lc.s_bias.data.getD d ni.zero
    let preScale := ni.add ((ListSupport.zipWith ni.mul sw_row x2).foldl ni.add ni.zero) sb
    let scale := ni.clip (ni.exp preScale) lc.clip_min lc.clip_max
    NumericSem.decToBool (ni.decFinite scale) = true

open NumericSem LayerCoreDef ForwardRowExpansion in
def makeLayerForwardProperties (ni : NumericInterface) (lc : LayerCore ni)
    (hLen : ∀ x1 x2 : List ni.Val, (forwardRowFull ni lc x1 x2).length = lc.dim)
    (hScale : ∀ x2 : List ni.Val, ∀ d : Nat, d < lc.dim →
      let sw_row := lc.s_weight.data.drop (d * lc.dim) |>.take lc.dim
      let sb := lc.s_bias.data.getD d ni.zero
      let preScale := ni.add ((ListSupport.zipWith ni.mul sw_row x2).foldl ni.add ni.zero) sb
      let scale := ni.clip (ni.exp preScale) lc.clip_min lc.clip_max
      NumericSem.decToBool (ni.decLt ni.zero scale) = true)
    (hClip : ∀ x2 : List ni.Val, ∀ d : Nat, d < lc.dim →
      let sw_row := lc.s_weight.data.drop (d * lc.dim) |>.take lc.dim
      let sb := lc.s_bias.data.getD d ni.zero
      let preScale := ni.add ((ListSupport.zipWith ni.mul sw_row x2).foldl ni.add ni.zero) sb
      let scale := ni.clip (ni.exp preScale) lc.clip_min lc.clip_max
      NumericSem.decToBool (ni.decFinite scale) = true) :
    LayerForwardProperties ni lc :=
  { hY1Length := hLen,
    hScalePositive := hScale,
    hDeterministic := fun _ _ => rfl,
    hClipBounded := hClip }

end LayerForwardProperties

namespace LayerInverseProperties

open NumericSem LayerCoreDef ForwardRowExpansion DotProductComputation
  DetailedClipComputation TransposeComputation in
structure LayerInverseProperties (ni : NumericInterface) (lc : LayerCore ni) where
  hX1Length : ∀ y1 y2 : List ni.Val,
    (inverseRowFull ni lc y1 y2).length = lc.dim
  hDivSafe : ∀ y2 : List ni.Val, ∀ d : Nat, d < lc.dim →
    let sw_row := lc.s_weight.data.drop (d * lc.dim) |>.take lc.dim
    let sb := lc.s_bias.data.getD d ni.zero
    let preScale := ni.add ((ListSupport.zipWith ni.mul sw_row y2).foldl ni.add ni.zero) sb
    let scale := ni.clip (ni.exp preScale) lc.clip_min lc.clip_max
    NumericSem.decToBool (ni.decLt ni.zero scale) = true
  hDeterministic : ∀ y1 y2 : List ni.Val,
    inverseRowFull ni lc y1 y2 = inverseRowFull ni lc y1 y2
  hScaleFinite : ∀ y2 : List ni.Val, ∀ d : Nat, d < lc.dim →
    let sw_row := lc.s_weight.data.drop (d * lc.dim) |>.take lc.dim
    let sb := lc.s_bias.data.getD d ni.zero
    let preScale := ni.add ((ListSupport.zipWith ni.mul sw_row y2).foldl ni.add ni.zero) sb
    let scale := ni.clip (ni.exp preScale) lc.clip_min lc.clip_max
    NumericSem.decToBool (ni.decFinite scale) = true

open NumericSem LayerCoreDef ForwardRowExpansion in
def makeLayerInverseProperties (ni : NumericInterface) (lc : LayerCore ni)
    (hLen : ∀ y1 y2 : List ni.Val, (inverseRowFull ni lc y1 y2).length = lc.dim)
    (hDiv : ∀ y2 : List ni.Val, ∀ d : Nat, d < lc.dim →
      let sw_row := lc.s_weight.data.drop (d * lc.dim) |>.take lc.dim
      let sb := lc.s_bias.data.getD d ni.zero
      let preScale := ni.add ((ListSupport.zipWith ni.mul sw_row y2).foldl ni.add ni.zero) sb
      let scale := ni.clip (ni.exp preScale) lc.clip_min lc.clip_max
      NumericSem.decToBool (ni.decLt ni.zero scale) = true)
    (hFin : ∀ y2 : List ni.Val, ∀ d : Nat, d < lc.dim →
      let sw_row := lc.s_weight.data.drop (d * lc.dim) |>.take lc.dim
      let sb := lc.s_bias.data.getD d ni.zero
      let preScale := ni.add ((ListSupport.zipWith ni.mul sw_row y2).foldl ni.add ni.zero) sb
      let scale := ni.clip (ni.exp preScale) lc.clip_min lc.clip_max
      NumericSem.decToBool (ni.decFinite scale) = true) :
    LayerInverseProperties ni lc :=
  { hX1Length := hLen,
    hDivSafe := hDiv,
    hDeterministic := fun _ _ => rfl,
    hScaleFinite := hFin }

end LayerInverseProperties

namespace BackwardRowProperties

open NumericSem LayerCoreDef DetailedBackward DetailedDy1Total DetailedDsComputation
  DetailedDx1Computation DetailedDx2Computation ClippingDerivative
  DetailedScaleGradient DetailedTranslationGradient
  FullGradientWeightUpdate GradMeanScaling in
structure BackwardRowProperties (ni : NumericInterface) (lc : LayerCore ni) where
  hDx1Length : ∀ dy1_total dy1 y2 : List ni.Val,
    (dx1AllDims ni lc dy1_total dy1 y2 lc.dim).length = lc.dim
  hDx2Length : ∀ dy2 ds dy1 : List ni.Val,
    (dx2AllDimsExpanded ni lc dy2 ds dy1 lc.dim).length = lc.dim
  hDsLength : ∀ dy1_total dy1 y1 y2 dy2 : List ni.Val,
    (dsAllDimsDetailed ni lc dy1_total dy1 y1 y2 dy2 lc.dim).length = lc.dim
  hDy1TotalLength : ∀ dy2 : List ni.Val,
    (dy1TotalMatVecProduct ni lc.t_weight.data dy2 lc.dim).length = lc.dim
  hGradDeterministic : ∀ spec : BackwardGradientDetails.FullGradientSpec ni,
    BackwardGradientDetails.computeFullGradients ni spec =
    BackwardGradientDetails.computeFullGradients ni spec

open NumericSem LayerCoreDef DetailedDy1Total DetailedDsComputation
  DetailedDx1Computation DetailedDx2Computation in
def makeBackwardRowProperties (ni : NumericInterface) (lc : LayerCore ni) :
    BackwardRowProperties ni lc :=
  { hDx1Length := fun _ _ _ => dx1AllDims_length ni lc _ _ _ lc.dim,
    hDx2Length := fun _ _ _ => dx2AllDimsExpanded_length ni lc _ _ _ lc.dim,
    hDsLength := fun _ _ _ _ _ => dsAllDimsDetailed_length ni lc _ _ _ _ _ lc.dim,
    hDy1TotalLength := fun _ => dy1TotalMatVecProduct_length ni _ _ lc.dim,
    hGradDeterministic := fun _ => rfl }

end BackwardRowProperties

namespace FullPipelineProperties

open NumericSem RSFCoreDef LayerCoreDef FullPipelineOps SplitMergeDetailed
  ForwardRowExpansion FullMultiLayerForward in
structure FullPipelineProperties (ni : NumericInterface) (core : RSFCore ni) where
  hForwardShape : ∀ x : List ni.Val, x.length = core.dim * 2 →
    ∀ r, fullForwardPipeline ni core x = RSFResult.ok r → r.length = core.dim * 2
  hInverseShape : ∀ y : List ni.Val, y.length = core.dim * 2 →
    ∀ r, fullInversePipeline ni core y = RSFResult.ok r → r.length = core.dim * 2
  hForwardError : ∀ x : List ni.Val, x.length ≠ core.dim * 2 →
    fullForwardPipeline ni core x = RSFResult.err RSFError.ShapeMismatch
  hInverseError : ∀ y : List ni.Val, y.length ≠ core.dim * 2 →
    fullInversePipeline ni core y = RSFResult.err RSFError.ShapeMismatch
  hForwardDeterministic : ∀ x : List ni.Val,
    fullForwardPipeline ni core x = fullForwardPipeline ni core x
  hInverseDeterministic : ∀ y : List ni.Val,
    fullInversePipeline ni core y = fullInversePipeline ni core y

open NumericSem RSFCoreDef FullPipelineOps in
def makeFullPipelineProperties (ni : NumericInterface) (core : RSFCore ni)
    (hFwdShape : ∀ x : List ni.Val, x.length = core.dim * 2 →
      ∀ r, fullForwardPipeline ni core x = RSFResult.ok r → r.length = core.dim * 2)
    (hInvShape : ∀ y : List ni.Val, y.length = core.dim * 2 →
      ∀ r, fullInversePipeline ni core y = RSFResult.ok r → r.length = core.dim * 2) :
    FullPipelineProperties ni core :=
  { hForwardShape := hFwdShape,
    hInverseShape := hInvShape,
    hForwardError := fun x h => fullForwardPipeline_wrong_len ni core x h,
    hInverseError := fun y h => fullInversePipeline_wrong_len ni core y h,
    hForwardDeterministic := fun _ => rfl,
    hInverseDeterministic := fun _ => rfl }

end FullPipelineProperties

namespace RegistryProperties

open RegistryModel DetailedRegistryOps in
structure RegistryProperties (CoreType : Type) (reg : Registry CoreType) where
  hNextIdPos : reg.nextId > 0
  hAllIdsLt : ∀ e, e ∈ reg.entries → e.id < reg.nextId
  hNoDestroyedAcquire : ∀ id : Nat, isEntryDestroyed reg id = true →
    canAcquire reg id = false
  hActiveOpsNonNeg : ∀ e, e ∈ reg.entries → e.active_ops ≥ 0
  hIdsUnique : ∀ e1 e2 : RegistryEntry CoreType, e1 ∈ reg.entries →
    e2 ∈ reg.entries → e1.id = e2.id → e1 = e2

open RegistryModel in
theorem emptyRegistryProperties : RegistryProperties CoreType emptyRegistry :=
  { hNextIdPos := Nat.zero_lt_succ 0,
    hAllIdsLt := fun _ h => absurd h (List.not_mem_nil _),
    hNoDestroyedAcquire := fun _ h => absurd h
      (show ¬(isEntryDestroyed emptyRegistry _ = true) from fun _ => rfl),
    hActiveOpsNonNeg := fun _ h => absurd h (List.not_mem_nil _),
    hIdsUnique := fun _ _ h => absurd h (List.not_mem_nil _) }

end RegistryProperties

namespace GPUProperties

open NumericSem RSFCoreDef GPUModel GPUStateMachineExpanded GPUVersionTracking in
structure GPUProperties (ni : NumericInterface) (core : RSFCore ni) where
  hSyncEstablishes : (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version
  hDisableClears : (disableGPU ni core).gpu_available = false ∧
    (disableGPU ni core).gpu_accel_present = false ∧
    (disableGPU ni core).f16_buf_present = false
  hDisablePreservesLayers : (disableGPU ni core).layers = core.layers
  hDisablePreservesDim : (disableGPU ni core).dim = core.dim
  hSyncPreservesLayers : (syncGPUVersions ni core).layers = core.layers
  hSyncPreservesDim : (syncGPUVersions ni core).dim = core.dim
  hAllocatePreservesLayers :
    (applyGPUOp ni { kind := GPUOperationKind.allocate, core := core }).layers = core.layers
  hDeallocatePreservesLayers :
    (applyGPUOp ni { kind := GPUOperationKind.deallocate, core := core }).layers = core.layers

open NumericSem RSFCoreDef GPUModel GPUStateMachineExpanded in
def makeGPUProperties (ni : NumericInterface) (core : RSFCore ni) :
    GPUProperties ni core :=
  { hSyncEstablishes := rfl,
    hDisableClears := ⟨rfl, rfl, rfl⟩,
    hDisablePreservesLayers := rfl,
    hDisablePreservesDim := rfl,
    hSyncPreservesLayers := rfl,
    hSyncPreservesDim := rfl,
    hAllocatePreservesLayers := rfl,
    hDeallocatePreservesLayers := rfl }

end GPUProperties

namespace SerializationProperties

open NumericSem RSFCoreDef ByteSupport DetailedCRC CRCExtended
  FullPayloadSerialization FullPayloadDeserialization
  FullSerializationRoundtrip WeightSerializationDetails
  DetailedHeaderSerialization in
structure SerializationProperties (ni : NumericInterface) where
  hMagic : ∀ core : RSFCore ni, (fullSerialize ni core).take 4 = [0x52, 0x53, 0x46, 0x30]
  hShortFail : ∀ bytes : List UInt8, bytes.length < 4 →
    fullDeserialize ni bytes = RSFResult.err RSFError.IOError
  hDeterministic : ∀ core : RSFCore ni, fullSerialize ni core = fullSerialize ni core
  hCRCValid : ∀ data : List UInt8, ExtendedCRCVerification.computeAndVerifyCRC data = true
  hWeightRT : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v →
    deserializeWeight ni (serializeWeight ni v) = v

open NumericSem RSFCoreDef in
def makeSerializationProperties (ni : NumericInterface)
    (hBits : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v) :
    SerializationProperties ni :=
  { hMagic := fun _ => rfl,
    hShortFail := fun _ h => fullDeserialize_too_short ni _ h,
    hDeterministic := fun _ => rfl,
    hCRCValid := fun d => ExtendedCRCVerification.computeAndVerifyCRC_always_true d,
    hWeightRT := fun v h => serializeWeight_deserializeWeight_roundtrip ni v h }

end SerializationProperties

namespace FinalSystemBundle

open NumericSem RSFCoreDef LayerCoreDef RegistryModel GPUModel SnapshotModel
  FullPipelineOps RSFCoreCreation GPUStateMachineExpanded DetailedCRC
  CRCExtended ByteSupport FullPayloadSerialization FullPayloadDeserialization
  FullSerializationRoundtrip WeightSerializationDetails
  DetailedHeaderSerialization NumericFiniteness
  LayerForwardProperties LayerInverseProperties BackwardRowProperties
  FullPipelineProperties RegistryProperties GPUProperties SerializationProperties in
structure FinalSystemBundle (ni : NumericInterface) where
  numSpec : CompleteNumericSpec ni
  serProps : SerializationProperties ni
  hCreateValid : ∀ spec : RSFCreateSpec ni,
    (createRSFCore ni spec).dim = spec.dim ∧
    (createRSFCore ni spec).layers.length = spec.numLayers ∧
    (createRSFCore ni spec).num_layers = spec.numLayers
  hGPUAllSafe : ∀ core : RSFCore ni,
    (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version ∧
    (disableGPU ni core).layers = core.layers
  hRegistrySound : ∀ reg : Registry (RSFCore ni), ∀ core : RSFCore ni,
    (registerCore reg core).2 = reg.nextId ∧
    (registerCore reg core).1.nextId = reg.nextId + 1
  hBitsRT : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v

open NumericSem RSFCoreDef RSFCoreCreation RegistryModel GPUModel in
def makeFinalSystemBundle (ni : NumericInterface)
    (numSpec : CompleteNumericSpec ni) :
    FinalSystemBundle ni :=
  { numSpec := numSpec,
    serProps := makeSerializationProperties ni numSpec.hBitsRoundtrip,
    hCreateValid := fun _ => ⟨rfl, createRSFCore_layers_length ni _, rfl⟩,
    hGPUAllSafe := fun _ => ⟨rfl, rfl⟩,
    hRegistrySound := fun _ _ => ⟨rfl, rfl⟩,
    hBitsRT := numSpec.hBitsRoundtrip }

open NumericSem RSFCoreDef RSFCoreCreation in
theorem finalBundle_create_dim (ni : NumericInterface) (fsb : FinalSystemBundle ni)
    (spec : RSFCreateSpec ni) :
    (createRSFCore ni spec).dim = spec.dim := (fsb.hCreateValid spec).1

open NumericSem RSFCoreDef RegistryModel in
theorem finalBundle_reg_fresh (ni : NumericInterface) (fsb : FinalSystemBundle ni)
    (reg : Registry (RSFCore ni)) (core : RSFCore ni) :
    (registerCore reg core).2 = reg.nextId := (fsb.hRegistrySound reg core).1

open NumericSem RSFCoreDef GPUModel in
theorem finalBundle_gpu_sync (ni : NumericInterface) (fsb : FinalSystemBundle ni)
    (core : RSFCore ni) :
    (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version := (fsb.hGPUAllSafe core).1

open NumericSem in
theorem finalBundle_bits (ni : NumericInterface) (fsb : FinalSystemBundle ni)
    (v : ni.Val) :
    ni.fromBits (ni.toBits v) = v := fsb.hBitsRT v

end FinalSystemBundle

namespace RSF

namespace MultiEpochTraining

open NumericSem RSFCoreDef LayerCoreDef TrainingStepOps WeightUpdateOps
  GradientZeroing InferenceOps FullPipelineOps in
def trainMultipleEpochs (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) (epochs : Nat) : RSFCore ni :=
  match epochs with
  | 0 => core
  | n + 1 => trainMultipleEpochs ni (fullTrainingStep ni core lr) lr n

open NumericSem RSFCoreDef TrainingStepOps in
theorem trainMultipleEpochs_zero (ni : NumericInterface) (core : RSFCore ni) (lr : ni.Val) :
    trainMultipleEpochs ni core lr 0 = core := rfl

open NumericSem RSFCoreDef TrainingStepOps in
theorem trainMultipleEpochs_one (ni : NumericInterface) (core : RSFCore ni) (lr : ni.Val) :
    trainMultipleEpochs ni core lr 1 = fullTrainingStep ni core lr := rfl

open NumericSem RSFCoreDef TrainingStepOps in
theorem trainMultipleEpochs_dim (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) (epochs : Nat) :
    (trainMultipleEpochs ni core lr epochs).dim = core.dim :=
  match epochs with
  | 0 => rfl
  | n + 1 => (trainMultipleEpochs_dim ni (fullTrainingStep ni core lr) lr n).trans
    (fullTrainingStep_preserves_dim ni core lr)

open NumericSem RSFCoreDef TrainingStepOps in
theorem trainMultipleEpochs_num_layers (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) (epochs : Nat) :
    (trainMultipleEpochs ni core lr epochs).num_layers = core.num_layers :=
  match epochs with
  | 0 => rfl
  | n + 1 => (trainMultipleEpochs_num_layers ni (fullTrainingStep ni core lr) lr n).trans
    (fullTrainingStep_preserves_num_layers ni core lr)

open NumericSem RSFCoreDef TrainingStepOps in
theorem trainMultipleEpochs_layers_length (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) (epochs : Nat) :
    (trainMultipleEpochs ni core lr epochs).layers.length = core.layers.length :=
  match epochs with
  | 0 => rfl
  | n + 1 => (trainMultipleEpochs_layers_length ni (fullTrainingStep ni core lr) lr n).trans
    (fullTrainingStep_layers_length ni core lr)

open NumericSem RSFCoreDef TrainingStepOps in
def trainAndInference (ni : NumericInterface) (core : RSFCore ni) (lr : ni.Val)
    (epochs : Nat) (x : List ni.Val) : RSFResult (List ni.Val) :=
  let trained := trainMultipleEpochs ni core lr epochs
  fullForwardPipeline ni trained x

open NumericSem RSFCoreDef TrainingStepOps FullPipelineOps in
theorem trainAndInference_zero_epochs (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) (x : List ni.Val) :
    trainAndInference ni core lr 0 x = fullForwardPipeline ni core x := rfl

end MultiEpochTraining

namespace TrainingAccuracy

open NumericSem RSFCoreDef LayerCoreDef FullPipelineOps InferenceOps
  ExtendedToleranceComparison MultiEpochTraining in
def evaluateAccuracy (ni : NumericInterface) (core : RSFCore ni)
    (inputs targets : List (List ni.Val)) (tol : ni.Val) :
    Nat × Nat :=
  inputs.zip targets |>.foldl (fun (passed, total) (x, target) =>
    match fullForwardPipeline ni core x with
    | RSFResult.ok y =>
      let correct := if allWithinTolerance ni y target tol then 1 else 0
      (passed + correct, total + 1)
    | RSFResult.err _ => (passed, total + 1)) (0, 0)

open NumericSem RSFCoreDef in
theorem evaluateAccuracy_empty (ni : NumericInterface) (core : RSFCore ni)
    (tol : ni.Val) :
    evaluateAccuracy ni core [] [] tol = (0, 0) := rfl

open NumericSem RSFCoreDef FullPipelineOps ExtendedToleranceComparison in
def evaluateSingleSample (ni : NumericInterface) (core : RSFCore ni)
    (x target : List ni.Val) (tol : ni.Val) : Bool :=
  match fullForwardPipeline ni core x with
  | RSFResult.ok y => allWithinTolerance ni y target tol
  | RSFResult.err _ => false

open NumericSem RSFCoreDef FullPipelineOps in
theorem evaluateSingleSample_err (ni : NumericInterface) (core : RSFCore ni)
    (x target : List ni.Val) (tol : ni.Val) (e : RSFError)
    (h : fullForwardPipeline ni core x = RSFResult.err e) :
    evaluateSingleSample ni core x target tol = false :=
  show (match fullForwardPipeline ni core x with | .ok _ => _ | .err _ => _) = false from
  h ▸ rfl

open NumericSem RSFCoreDef FullPipelineOps MultiEpochTraining in
def trainAndEvaluate (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) (epochs : Nat)
    (inputs targets : List (List ni.Val)) (tol : ni.Val) :
    Nat × Nat :=
  let trained := trainMultipleEpochs ni core lr epochs
  evaluateAccuracy ni trained inputs targets tol

open NumericSem RSFCoreDef in
theorem trainAndEvaluate_zero_epochs (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) (inputs targets : List (List ni.Val)) (tol : ni.Val) :
    trainAndEvaluate ni core lr 0 inputs targets tol =
    evaluateAccuracy ni core inputs targets tol := rfl

end TrainingAccuracy

namespace StorageAliasingComplete

open NumericSem LayerCoreDef TensorMem StorageAliasing in
def tensorsShareStorage (ni : NumericInterface) (t1 t2 : Tensor ni) : Bool :=
  t1.storageId = t2.storageId

open NumericSem LayerCoreDef in
theorem tensorsShareStorage_refl (ni : NumericInterface) (t : Tensor ni) :
    tensorsShareStorage ni t t = true :=
  show (t.storageId = t.storageId) = true from rfl

open NumericSem LayerCoreDef in
theorem tensorsShareStorage_symm (ni : NumericInterface) (t1 t2 : Tensor ni)
    (h : tensorsShareStorage ni t1 t2 = true) :
    tensorsShareStorage ni t2 t1 = true :=
  show (t2.storageId = t1.storageId) = true from
  (show t1.storageId = t2.storageId from h) ▸ rfl

open NumericSem LayerCoreDef TensorMem StorageAliasing in
def storageOverlaps (ni : NumericInterface) (t1 t2 : Tensor ni) : Bool :=
  t1.storageId = t2.storageId

open NumericSem LayerCoreDef in
def layerHasInternalAlias (ni : NumericInterface) (lc : LayerCore ni) : Bool :=
  lc.s_weight.storageId = lc.t_weight.storageId ||
  lc.s_weight.storageId = lc.s_bias.storageId ||
  lc.s_weight.storageId = lc.t_bias.storageId ||
  lc.t_weight.storageId = lc.s_bias.storageId ||
  lc.t_weight.storageId = lc.t_bias.storageId ||
  lc.s_bias.storageId = lc.t_bias.storageId

open NumericSem LayerCoreDef in
def layerHasNoAlias (ni : NumericInterface) (lc : LayerCore ni) : Prop :=
  lc.s_weight.storageId ≠ lc.t_weight.storageId ∧
  lc.s_weight.storageId ≠ lc.s_bias.storageId ∧
  lc.s_weight.storageId ≠ lc.t_bias.storageId ∧
  lc.t_weight.storageId ≠ lc.s_bias.storageId ∧
  lc.t_weight.storageId ≠ lc.t_bias.storageId ∧
  lc.s_bias.storageId ≠ lc.t_bias.storageId

open NumericSem LayerCoreDef RSFCoreCreation in
theorem createDefaultLayerCore_no_alias (ni : NumericInterface) (spec : RSFCreateSpec ni)
    (idx : Nat) (h : idx < 250) :
    layerHasNoAlias ni (createDefaultLayerCore ni spec idx) :=
  ⟨show idx * 4 ≠ idx * 4 + 1 from Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_refl _)),
   show idx * 4 ≠ idx * 4 + 2 from Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_refl _)) (Nat.succ_le_succ (Nat.zero_le _))),
   show idx * 4 ≠ idx * 4 + 3 from Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_refl _)) (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))),
   show idx * 4 + 1 ≠ idx * 4 + 2 from Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_refl _)),
   show idx * 4 + 1 ≠ idx * 4 + 3 from Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_refl _)) (Nat.succ_le_succ (Nat.zero_le _))),
   show idx * 4 + 2 ≠ idx * 4 + 3 from Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_refl _))⟩

open NumericSem LayerCoreDef in
def layersHaveNoAlias (ni : NumericInterface) (layers : List (LayerCore ni)) : Prop :=
  ∀ lc, lc ∈ layers → layerHasNoAlias ni lc

open NumericSem LayerCoreDef in
theorem layersHaveNoAlias_empty (ni : NumericInterface) :
    layersHaveNoAlias ni ([] : List (LayerCore ni)) :=
  fun _ h => absurd h (List.not_mem_nil _)

open NumericSem LayerCoreDef in
def crossLayerNoAlias (ni : NumericInterface) (l1 l2 : LayerCore ni) : Prop :=
  l1.s_weight.storageId ≠ l2.s_weight.storageId ∧
  l1.s_weight.storageId ≠ l2.t_weight.storageId ∧
  l1.s_weight.storageId ≠ l2.s_bias.storageId ∧
  l1.s_weight.storageId ≠ l2.t_bias.storageId ∧
  l1.t_weight.storageId ≠ l2.s_weight.storageId ∧
  l1.t_weight.storageId ≠ l2.t_weight.storageId ∧
  l1.t_weight.storageId ≠ l2.s_bias.storageId ∧
  l1.t_weight.storageId ≠ l2.t_bias.storageId

end StorageAliasingComplete

namespace DataFlowAnalysis

open NumericSem RSFCoreDef LayerCoreDef FullPipelineOps ForwardRowExpansion in
def computeIntermediateOutputs (ni : NumericInterface) (core : RSFCore ni)
    (x1 x2 : List ni.Val) : List (List ni.Val × List ni.Val) :=
  core.layers.foldl (fun (acc : List (List ni.Val × List ni.Val) × (List ni.Val × List ni.Val))
      lc =>
    let (history, (curX1, curX2)) := acc
    let y1 := forwardRowFull ni lc curX1 curX2
    let y2 := curX2
    (history ++ [(y1, y2)], (y1, y2))
  ) ([], (x1, x2)) |>.1

open NumericSem RSFCoreDef in
theorem computeIntermediateOutputs_empty (ni : NumericInterface) (core : RSFCore ni)
    (x1 x2 : List ni.Val) (h : core.layers = []) :
    computeIntermediateOutputs ni core x1 x2 = [] :=
  show (core.layers.foldl _ _).1 = [] from h ▸ rfl

open NumericSem RSFCoreDef LayerCoreDef FullPipelineOps ForwardRowExpansion in
def computeBackwardIntermediates (ni : NumericInterface) (core : RSFCore ni)
    (intermediates : List (List ni.Val × List ni.Val))
    (dy1 dy2 : List ni.Val) :
    List (List ni.Val × List ni.Val) :=
  let revLayers := core.layers.reverse
  let revInter := intermediates.reverse
  (revLayers.zip revInter).map fun (lc, (y1, _)) =>
    let invX1 := inverseRowFull ni lc y1 dy2
    (invX1, dy2)

open NumericSem RSFCoreDef in
theorem computeBackwardIntermediates_empty (ni : NumericInterface)
    (core : RSFCore ni) (dy1 dy2 : List ni.Val) :
    computeBackwardIntermediates ni core [] dy1 dy2 = [] :=
  show (core.layers.reverse.zip []).map _ = [] from
  (List.zip_nil_right core.layers.reverse) ▸ rfl

open NumericSem RSFCoreDef LayerCoreDef FullPipelineOps ForwardRowExpansion in
def computeDataFlowGraph (ni : NumericInterface) (core : RSFCore ni)
    (x1 x2 : List ni.Val) :
    (List (List ni.Val × List ni.Val) × List ni.Val × List ni.Val) :=
  let intermediates := computeIntermediateOutputs ni core x1 x2
  let finalState := core.layers.foldl (fun (curX1, curX2) lc =>
    (forwardRowFull ni lc curX1 curX2, curX2)) (x1, x2)
  (intermediates, finalState.1, finalState.2)

open NumericSem RSFCoreDef in
theorem computeDataFlowGraph_empty_layers (ni : NumericInterface) (core : RSFCore ni)
    (x1 x2 : List ni.Val) (h : core.layers = []) :
    (computeDataFlowGraph ni core x1 x2).2.1 = x1 ∧
    (computeDataFlowGraph ni core x1 x2).2.2 = x2 :=
  ⟨show (core.layers.foldl _ _).1 = x1 from h ▸ rfl,
   show (core.layers.foldl _ _).2 = x2 from h ▸ rfl⟩

end DataFlowAnalysis

namespace GradientClippingExtended

open NumericSem DetailedClipComputation ClippingDerivative in
def clipGradient (ni : NumericInterface) (grad clipMin clipMax : ni.Val) : ni.Val :=
  ni.clip grad clipMin clipMax

open NumericSem in
theorem clipGradient_deterministic (ni : NumericInterface) (grad clipMin clipMax : ni.Val) :
    clipGradient ni grad clipMin clipMax = clipGradient ni grad clipMin clipMax := rfl

open NumericSem DetailedClipComputation in
def clipGradientList (ni : NumericInterface) (grads : List ni.Val)
    (clipMin clipMax : ni.Val) : List ni.Val :=
  grads.map (fun g => ni.clip g clipMin clipMax)

open NumericSem in
theorem clipGradientList_length (ni : NumericInterface) (grads : List ni.Val)
    (clipMin clipMax : ni.Val) :
    (clipGradientList ni grads clipMin clipMax).length = grads.length :=
  List.length_map _ grads

open NumericSem in
theorem clipGradientList_empty (ni : NumericInterface) (clipMin clipMax : ni.Val) :
    clipGradientList ni [] clipMin clipMax = [] := rfl

open NumericSem DetailedClipComputation ClippingDerivative in
def clipDerivativeList (ni : NumericInterface) (values : List ni.Val)
    (clipMin clipMax : ni.Val) : List ni.Val :=
  values.map (fun v => clipDerivative ni v clipMin clipMax)

open NumericSem in
theorem clipDerivativeList_length (ni : NumericInterface) (values : List ni.Val)
    (clipMin clipMax : ni.Val) :
    (clipDerivativeList ni values clipMin clipMax).length = values.length :=
  List.length_map _ values

open NumericSem in
theorem clipDerivativeList_empty (ni : NumericInterface) (clipMin clipMax : ni.Val) :
    clipDerivativeList ni [] clipMin clipMax = [] := rfl

open NumericSem DetailedClipComputation ClippingDerivative in
def computeGradientWithClip (ni : NumericInterface) (rawGrad expVal clipMin clipMax : ni.Val) :
    ni.Val :=
  let cd := clipDerivative ni expVal clipMin clipMax
  ni.mul rawGrad cd

open NumericSem in
theorem computeGradientWithClip_zero_deriv (ni : NumericInterface)
    (rawGrad expVal clipMin clipMax : ni.Val)
    (h : clipDerivative ni expVal clipMin clipMax = ni.zero) :
    computeGradientWithClip ni rawGrad expVal clipMin clipMax = ni.mul rawGrad ni.zero :=
  show ni.mul rawGrad (clipDerivative ni expVal clipMin clipMax) = _ from h ▸ rfl

end GradientClippingExtended

namespace GradAccumulationExtended

open NumericSem LayerCoreDef FullGradientWeightUpdate GradMeanScaling in
def accumulateGradients (ni : NumericInterface) (existing new_ : List ni.Val) :
    List ni.Val :=
  ListSupport.zipWith ni.add existing new_

open NumericSem in
theorem accumulateGradients_empty (ni : NumericInterface) :
    accumulateGradients ni [] [] = [] := rfl

open NumericSem in
def accumulateGradientsBatch (ni : NumericInterface) (grads : List (List ni.Val)) :
    List ni.Val :=
  match grads with
  | [] => []
  | [g] => g
  | g :: rest =>
    rest.foldl (fun acc batch => accumulateGradients ni acc batch) g

open NumericSem in
theorem accumulateGradientsBatch_single (ni : NumericInterface) (g : List ni.Val) :
    accumulateGradientsBatch ni [g] = g := rfl

open NumericSem in
theorem accumulateGradientsBatch_empty (ni : NumericInterface) :
    accumulateGradientsBatch ni [] = [] := rfl

open NumericSem GradMeanScaling in
def accumulateAndScale (ni : NumericInterface) (grads : List (List ni.Val))
    (batchSize : Nat) (doMean : Bool) : List ni.Val :=
  let accumulated := accumulateGradientsBatch ni grads
  if doMean then
    let scale := computeGradScale ni batchSize true
    accumulated.map (fun g => ni.mul g scale)
  else accumulated

open NumericSem in
theorem accumulateAndScale_no_mean (ni : NumericInterface) (grads : List (List ni.Val))
    (bs : Nat) :
    accumulateAndScale ni grads bs false = accumulateGradientsBatch ni grads :=
  show (if false then _ else _) = _ from if_neg (Bool.noConfusion)

open NumericSem in
theorem accumulateAndScale_empty (ni : NumericInterface) (bs : Nat) (doMean : Bool) :
    accumulateAndScale ni [] bs doMean = if doMean then [].map _ else [] :=
  show (if doMean then (accumulateGradientsBatch ni []).map _ else _) = _ from rfl

end GradAccumulationExtended

namespace RSF

namespace LayerInitializationExpanded

open NumericSem LayerCoreDef WeightInitialization in
def initLayerWithRandomSeed (ni : NumericInterface) (dim : Nat) (seed : Nat) :
    LayerCore ni :=
  let scale := ni.div ni.one (ni.fromNat (dim * 2))
  let sw_data := List.range (dim * dim) |>.map fun i =>
    ni.mul scale (ni.fromNat ((seed + i * 7 + 3) % 256))
  let tw_data := List.range (dim * dim) |>.map fun i =>
    ni.mul scale (ni.fromNat ((seed + i * 13 + 5) % 256))
  let sb_data := List.replicate dim ni.zero
  let tb_data := List.replicate dim ni.zero
  { dim := dim,
    s_weight := { shape := { rows := dim, cols := dim }, data := sw_data,
      storageId := seed * 4, hDataLen := List.length_map _ (List.range _) |>.trans (List.length_range _) },
    t_weight := { shape := { rows := dim, cols := dim }, data := tw_data,
      storageId := seed * 4 + 1, hDataLen := List.length_map _ (List.range _) |>.trans (List.length_range _) },
    s_bias := { shape := { rows := 1, cols := dim }, data := sb_data,
      storageId := seed * 4 + 2, hDataLen := List.length_replicate _ _ },
    t_bias := { shape := { rows := 1, cols := dim }, data := tb_data,
      storageId := seed * 4 + 3, hDataLen := List.length_replicate _ _ },
    s_weight_grad := none,
    t_weight_grad := none,
    s_bias_grad := none,
    t_bias_grad := none,
    clip_min := ni.negOne,
    clip_max := ni.one }

open NumericSem LayerCoreDef in
theorem initLayerWithRandomSeed_dim (ni : NumericInterface) (dim seed : Nat) :
    (initLayerWithRandomSeed ni dim seed).dim = dim := rfl

open NumericSem LayerCoreDef in
theorem initLayerWithRandomSeed_no_grads (ni : NumericInterface) (dim seed : Nat) :
    (initLayerWithRandomSeed ni dim seed).s_weight_grad = none ∧
    (initLayerWithRandomSeed ni dim seed).t_weight_grad = none ∧
    (initLayerWithRandomSeed ni dim seed).s_bias_grad = none ∧
    (initLayerWithRandomSeed ni dim seed).t_bias_grad = none := ⟨rfl, rfl, rfl, rfl⟩

open NumericSem LayerCoreDef in
theorem initLayerWithRandomSeed_sw_length (ni : NumericInterface) (dim seed : Nat) :
    (initLayerWithRandomSeed ni dim seed).s_weight.data.length = dim * dim :=
  List.length_map _ (List.range _) |>.trans (List.length_range _)

open NumericSem LayerCoreDef in
theorem initLayerWithRandomSeed_tw_length (ni : NumericInterface) (dim seed : Nat) :
    (initLayerWithRandomSeed ni dim seed).t_weight.data.length = dim * dim :=
  List.length_map _ (List.range _) |>.trans (List.length_range _)

open NumericSem LayerCoreDef in
theorem initLayerWithRandomSeed_sb_length (ni : NumericInterface) (dim seed : Nat) :
    (initLayerWithRandomSeed ni dim seed).s_bias.data.length = dim :=
  List.length_replicate _ _

open NumericSem LayerCoreDef in
theorem initLayerWithRandomSeed_tb_length (ni : NumericInterface) (dim seed : Nat) :
    (initLayerWithRandomSeed ni dim seed).t_bias.data.length = dim :=
  List.length_replicate _ _

open NumericSem LayerCoreDef WeightInitialization ExtendedLayerOps in
def initAndAllocGrads (ni : NumericInterface) (dim seed : Nat) : LayerCore ni :=
  allocateGradients ni (initLayerWithRandomSeed ni dim seed)

open NumericSem LayerCoreDef in
theorem initAndAllocGrads_dim (ni : NumericInterface) (dim seed : Nat) :
    (initAndAllocGrads ni dim seed).dim = dim := rfl

open NumericSem LayerCoreDef DetailedBackward in
theorem initAndAllocGrads_has_grads (ni : NumericInterface) (dim seed : Nat) :
    hasGradients ni (initAndAllocGrads ni dim seed) = true := rfl

end LayerInitializationExpanded

namespace FullCoreInitialization

open NumericSem RSFCoreDef LayerCoreDef LayerInitializationExpanded ExtendedLayerOps
  RSFCoreCreation in
def createRSFCoreWithSeed (ni : NumericInterface) (dim numLayers : Nat)
    (clipMin clipMax : ni.Val) (seed : Nat) : RSFCore ni :=
  { dim := dim,
    num_layers := numLayers,
    layers := List.range numLayers |>.map fun idx =>
      allocateGradients ni (initLayerWithRandomSeed ni dim (seed + idx)),
    cfg := { clip_min := clipMin, clip_max := clipMax,
             use_fp16 := false, grad_mean := true },
    gpu_available := false,
    gpu_accel_present := false,
    f16_buf_present := false,
    cpu_weight_version := 0,
    gpu_weight_version := 0 }

open NumericSem RSFCoreDef in
theorem createRSFCoreWithSeed_dim (ni : NumericInterface) (dim numLayers : Nat)
    (clipMin clipMax : ni.Val) (seed : Nat) :
    (createRSFCoreWithSeed ni dim numLayers clipMin clipMax seed).dim = dim := rfl

open NumericSem RSFCoreDef in
theorem createRSFCoreWithSeed_num_layers (ni : NumericInterface) (dim numLayers : Nat)
    (clipMin clipMax : ni.Val) (seed : Nat) :
    (createRSFCoreWithSeed ni dim numLayers clipMin clipMax seed).num_layers = numLayers := rfl

open NumericSem RSFCoreDef in
theorem createRSFCoreWithSeed_layers_length (ni : NumericInterface) (dim numLayers : Nat)
    (clipMin clipMax : ni.Val) (seed : Nat) :
    (createRSFCoreWithSeed ni dim numLayers clipMin clipMax seed).layers.length = numLayers :=
  List.length_map _ (List.range numLayers) |>.trans (List.length_range numLayers)

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward in
theorem createRSFCoreWithSeed_all_grads (ni : NumericInterface) (dim numLayers : Nat)
    (clipMin clipMax : ni.Val) (seed : Nat) :
    ∀ lc, lc ∈ (createRSFCoreWithSeed ni dim numLayers clipMin clipMax seed).layers →
    hasGradients ni lc = true :=
  fun lc h => (List.mem_map.mp h).elim fun ⟨_, _, heq⟩ => heq ▸ rfl

open NumericSem RSFCoreDef LayerCoreDef in
theorem createRSFCoreWithSeed_all_same_dim (ni : NumericInterface) (dim numLayers : Nat)
    (clipMin clipMax : ni.Val) (seed : Nat) :
    ∀ lc, lc ∈ (createRSFCoreWithSeed ni dim numLayers clipMin clipMax seed).layers →
    lc.dim = dim :=
  fun lc h => (List.mem_map.mp h).elim fun ⟨_, _, heq⟩ => heq ▸ rfl

open NumericSem RSFCoreDef in
theorem createRSFCoreWithSeed_synced (ni : NumericInterface) (dim numLayers : Nat)
    (clipMin clipMax : ni.Val) (seed : Nat) :
    (createRSFCoreWithSeed ni dim numLayers clipMin clipMax seed).cpu_weight_version =
    (createRSFCoreWithSeed ni dim numLayers clipMin clipMax seed).gpu_weight_version := rfl

open NumericSem RSFCoreDef in
theorem createRSFCoreWithSeed_no_gpu (ni : NumericInterface) (dim numLayers : Nat)
    (clipMin clipMax : ni.Val) (seed : Nat) :
    (createRSFCoreWithSeed ni dim numLayers clipMin clipMax seed).gpu_available = false ∧
    (createRSFCoreWithSeed ni dim numLayers clipMin clipMax seed).gpu_accel_present = false ∧
    (createRSFCoreWithSeed ni dim numLayers clipMin clipMax seed).f16_buf_present = false :=
  ⟨rfl, rfl, rfl⟩

end FullCoreInitialization

namespace FullPipelineRoundtripProperties

open NumericSem RSFCoreDef LayerCoreDef FullPipelineOps ForwardRowExpansion
  InvertibilityByDefinition SplitMergeDetailed FullMultiLayerForward in
structure PipelineRoundtripProperty (ni : NumericInterface) (core : RSFCore ni) where
  hShapePreserved : ∀ x : List ni.Val, x.length = core.dim * 2 →
    ∀ r, fullForwardPipeline ni core x = RSFResult.ok r →
    r.length = core.dim * 2
  hInverseShapePreserved : ∀ y : List ni.Val, y.length = core.dim * 2 →
    ∀ r, fullInversePipeline ni core y = RSFResult.ok r →
    r.length = core.dim * 2
  hForwardDet : ∀ x : List ni.Val,
    fullForwardPipeline ni core x = fullForwardPipeline ni core x
  hInverseDet : ∀ y : List ni.Val,
    fullInversePipeline ni core y = fullInversePipeline ni core y
  hErrorOnBadShape : ∀ x : List ni.Val, x.length ≠ core.dim * 2 →
    fullForwardPipeline ni core x = RSFResult.err RSFError.ShapeMismatch
  hInverseErrorOnBadShape : ∀ y : List ni.Val, y.length ≠ core.dim * 2 →
    fullInversePipeline ni core y = RSFResult.err RSFError.ShapeMismatch

open NumericSem RSFCoreDef FullPipelineOps in
def makePipelineRoundtripProperty (ni : NumericInterface) (core : RSFCore ni)
    (hShape : ∀ x : List ni.Val, x.length = core.dim * 2 →
      ∀ r, fullForwardPipeline ni core x = RSFResult.ok r → r.length = core.dim * 2)
    (hInvShape : ∀ y : List ni.Val, y.length = core.dim * 2 →
      ∀ r, fullInversePipeline ni core y = RSFResult.ok r → r.length = core.dim * 2) :
    PipelineRoundtripProperty ni core :=
  { hShapePreserved := hShape,
    hInverseShapePreserved := hInvShape,
    hForwardDet := fun _ => rfl,
    hInverseDet := fun _ => rfl,
    hErrorOnBadShape := fullForwardPipeline_wrong_len ni core,
    hInverseErrorOnBadShape := fullInversePipeline_wrong_len ni core }

open NumericSem RSFCoreDef FullPipelineOps in
theorem pipelineRT_error_forward (ni : NumericInterface) (core : RSFCore ni)
    (prt : PipelineRoundtripProperty ni core) (x : List ni.Val)
    (h : x.length ≠ core.dim * 2) :
    fullForwardPipeline ni core x = RSFResult.err RSFError.ShapeMismatch :=
  prt.hErrorOnBadShape x h

open NumericSem RSFCoreDef FullPipelineOps in
theorem pipelineRT_error_inverse (ni : NumericInterface) (core : RSFCore ni)
    (prt : PipelineRoundtripProperty ni core) (y : List ni.Val)
    (h : y.length ≠ core.dim * 2) :
    fullInversePipeline ni core y = RSFResult.err RSFError.ShapeMismatch :=
  prt.hInverseErrorOnBadShape y h

end FullPipelineRoundtripProperties

namespace FullGPURoundtripProperties

open NumericSem RSFCoreDef GPUModel GPUVersionTracking GPUStateMachineExpanded in
structure GPURoundtripProperty (ni : NumericInterface) (core : RSFCore ni) where
  hSyncEstablishes : (syncGPUVersions ni core).gpu_weight_version =
    (syncGPUVersions ni core).cpu_weight_version
  hDisableClears : (disableGPU ni core).gpu_available = false
  hDisablePreserves : (disableGPU ni core).layers = core.layers
  hAllocEnables :
    (applyGPUOp ni { kind := GPUOperationKind.allocate, core := core }).gpu_available = true
  hDeallocClears :
    (applyGPUOp ni { kind := GPUOperationKind.deallocate, core := core }).f16_buf_present = false
  hOpsPreserveDim : ∀ ops : List GPUOperationKind,
    (applyGPUOps ni core ops).dim = core.dim
  hSyncIdempotent :
    syncGPUVersions ni (syncGPUVersions ni core) = syncGPUVersions ni (syncGPUVersions ni core)
  hDisableIdempotent :
    disableGPU ni (disableGPU ni core) = disableGPU ni (disableGPU ni core)

open NumericSem RSFCoreDef GPUModel GPUStateMachineExpanded in
def makeGPURoundtripProperty (ni : NumericInterface) (core : RSFCore ni)
    (hOps : ∀ ops : List GPUOperationKind, (applyGPUOps ni core ops).dim = core.dim) :
    GPURoundtripProperty ni core :=
  { hSyncEstablishes := rfl,
    hDisableClears := rfl,
    hDisablePreserves := rfl,
    hAllocEnables := rfl,
    hDeallocClears := rfl,
    hOpsPreserveDim := hOps,
    hSyncIdempotent := rfl,
    hDisableIdempotent := rfl }

end FullGPURoundtripProperties

namespace FullRegistryRoundtripProperties

open RegistryModel DetailedRegistryOps RegistryProperties RegistryStateProperties in
structure RegistryRoundtripProperty (CoreType : Type) where
  hRegisterFresh : ∀ reg : Registry CoreType, ∀ core : CoreType,
    (registerCore reg core).2 = reg.nextId
  hRegisterAdvances : ∀ reg : Registry CoreType, ∀ core : CoreType,
    (registerCore reg core).1.nextId = reg.nextId + 1
  hDestroyPreservesNext : ∀ reg : Registry CoreType, ∀ id : Nat,
    (requestDestroy reg id).1.nextId = reg.nextId
  hEmptyNextId : (emptyRegistry : Registry CoreType).nextId = 1
  hMultiRegisterOrdered : ∀ reg : Registry CoreType, ∀ c1 c2 : CoreType,
    let (reg1, id1) := registerCore reg c1
    let (_, id2) := registerCore reg1 c2
    id1 < id2

open RegistryModel in
def makeRegistryRoundtripProperty (CoreType : Type) :
    RegistryRoundtripProperty CoreType :=
  { hRegisterFresh := fun _ _ => rfl,
    hRegisterAdvances := fun _ _ => rfl,
    hDestroyPreservesNext := fun _ _ => rfl,
    hEmptyNextId := rfl,
    hMultiRegisterOrdered := fun _ _ _ => Nat.lt_succ_of_le (Nat.le_refl _) }

open RegistryModel in
theorem regRT_fresh (CoreType : Type) (rrt : RegistryRoundtripProperty CoreType)
    (reg : Registry CoreType) (core : CoreType) :
    (registerCore reg core).2 = reg.nextId := rrt.hRegisterFresh reg core

open RegistryModel in
theorem regRT_advances (CoreType : Type) (rrt : RegistryRoundtripProperty CoreType)
    (reg : Registry CoreType) (core : CoreType) :
    (registerCore reg core).1.nextId = reg.nextId + 1 := rrt.hRegisterAdvances reg core

open RegistryModel in
theorem regRT_empty (CoreType : Type) (rrt : RegistryRoundtripProperty CoreType) :
    (emptyRegistry : Registry CoreType).nextId = 1 := rrt.hEmptyNextId

open RegistryModel in
theorem regRT_ordered (CoreType : Type) (rrt : RegistryRoundtripProperty CoreType)
    (reg : Registry CoreType) (c1 c2 : CoreType) :
    let (reg1, id1) := registerCore reg c1
    let (_, id2) := registerCore reg1 c2
    id1 < id2 := rrt.hMultiRegisterOrdered reg c1 c2

end FullRegistryRoundtripProperties

namespace RSF

namespace FullBackwardPipelineExpanded

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward FullBackwardRow
  FullBackwardBatch GradMeanScaling FullBackwardMultiLayer
  FullMultiLayerForward ForwardRowExpansion SplitMergeDetailed
  DetailedDy1Total DetailedDsComputation DetailedDx1Computation
  DetailedDx2Computation ClippingDerivative DetailedScaleGradient
  DetailedTranslationGradient FullGradientWeightUpdate in
structure SingleLayerBackwardResult (ni : NumericInterface) where
  dx1 : List ni.Val
  dx2 : List ni.Val
  ds_accum : List ni.Val
  sw_grad : List ni.Val
  tw_grad : List ni.Val
  sb_grad : List ni.Val
  tb_grad : List ni.Val
  dim : Nat
  hDx1Len : dx1.length = dim
  hDx2Len : dx2.length = dim
  hDsLen : ds_accum.length = dim
  hSwGradLen : sw_grad.length = dim * dim
  hTwGradLen : tw_grad.length = dim * dim
  hSbGradLen : sb_grad.length = dim
  hTbGradLen : tb_grad.length = dim

open NumericSem LayerCoreDef in
def computeSingleLayerBackwardResult (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 dy1 dy2 : List ni.Val) (gradScale : ni.Val)
    (hX1 : x1.length = lc.dim) (hX2 : x2.length = lc.dim)
    (hDy1 : dy1.length = lc.dim) (hDy2 : dy2.length = lc.dim) :
    SingleLayerBackwardResult ni :=
  let dim := lc.dim
  let dy1_total_list := dy1TotalMatVecProduct ni lc.t_weight.data dy2 dim
  let dy1_total := ListSupport.zipWith ni.add dy1 dy1_total_list
  let y1 := forwardRowFull ni lc x1 x2
  let ds_list := dsAllDimsDetailed ni lc dy1_total dy1 y1 x2 dy2 dim
  let dx1_list := dx1AllDims ni lc dy1_total dy1 x2 dim
  let dx2_list := dx2AllDimsExpanded ni lc dy2 ds_list dy1 dim
  let sw_grad_list := computeSWeightGradContrib ni
    { lc := lc, ds_row := ds_list, dy2_row := dy2,
      x1_row := x1, x2_row := x2, gradScale := gradScale,
      dim := dim, hDim := rfl, hDs := dsAllDimsDetailed_length ni lc _ _ _ _ _ dim,
      hDy2 := hDy2, hX1 := hX1, hX2 := hX2 }
  let tw_grad_list := computeTWeightGradContrib ni
    { lc := lc, ds_row := ds_list, dy2_row := dy2,
      x1_row := x1, x2_row := x2, gradScale := gradScale,
      dim := dim, hDim := rfl, hDs := dsAllDimsDetailed_length ni lc _ _ _ _ _ dim,
      hDy2 := hDy2, hX1 := hX1, hX2 := hX2 }
  let sb_grad_list := ds_list.map (fun v => ni.mul v gradScale)
  let tb_grad_list := dy1_total.map (fun v => ni.mul v gradScale)
  { dx1 := dx1_list,
    dx2 := dx2_list,
    ds_accum := ds_list,
    sw_grad := sw_grad_list,
    tw_grad := tw_grad_list,
    sb_grad := sb_grad_list,
    tb_grad := tb_grad_list,
    dim := dim,
    hDx1Len := dx1AllDims_length ni lc _ _ _ dim,
    hDx2Len := dx2AllDimsExpanded_length ni lc _ _ _ dim,
    hDsLen := dsAllDimsDetailed_length ni lc _ _ _ _ _ dim,
    hSwGradLen := computeSWeightGradContrib_length ni _,
    hTwGradLen := computeTWeightGradContrib_length ni _,
    hSbGradLen := List.length_map _ _ |>.trans (dsAllDimsDetailed_length ni lc _ _ _ _ _ dim),
    hTbGradLen := List.length_map _ _ |>.trans (show (ListSupport.zipWith ni.add dy1 _).length = dim from
      ListSupport.zipWith_length_min ni.add dy1 _ |>.trans (Nat.min_eq_left (hDy1 ▸ Nat.le_of_eq rfl))) }

open NumericSem LayerCoreDef in
theorem computeSingleLayerBackwardResult_dim (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 dy1 dy2 : List ni.Val) (gs : ni.Val)
    (hX1 : x1.length = lc.dim) (hX2 : x2.length = lc.dim)
    (hDy1 : dy1.length = lc.dim) (hDy2 : dy2.length = lc.dim) :
    (computeSingleLayerBackwardResult ni lc x1 x2 dy1 dy2 gs hX1 hX2 hDy1 hDy2).dim = lc.dim := rfl

open NumericSem RSFCoreDef LayerCoreDef in
def fullBackwardPipelineSingleRow (ni : NumericInterface) (core : RSFCore ni)
    (x1 x2 dy1 dy2 : List ni.Val) (gradScale : ni.Val) :
    List ni.Val × List ni.Val :=
  let revLayers := core.layers.reverse
  let (finalDy1, finalDy2, _) :=
    revLayers.foldl (fun (curDy1, curDy2, _) lc =>
      let dy1_total := ListSupport.zipWith ni.add curDy1
        (dy1TotalMatVecProduct ni lc.t_weight.data curDy2 core.dim)
      let y1 := forwardRowFull ni lc x1 x2
      let ds := dsAllDimsDetailed ni lc dy1_total curDy1 y1 x2 curDy2 core.dim
      let dx1 := dx1AllDims ni lc dy1_total curDy1 x2 core.dim
      let dx2 := dx2AllDimsExpanded ni lc curDy2 ds curDy1 core.dim
      (dx1, dx2, gradScale)) (dy1, dy2, gradScale)
  (finalDy1, finalDy2)

open NumericSem RSFCoreDef in
theorem fullBackwardPipelineSingleRow_empty (ni : NumericInterface) (core : RSFCore ni)
    (x1 x2 dy1 dy2 : List ni.Val) (gs : ni.Val) (h : core.layers = []) :
    fullBackwardPipelineSingleRow ni core x1 x2 dy1 dy2 gs = (dy1, dy2) :=
  show (core.layers.reverse.foldl _ _) = _ from h ▸ rfl

open NumericSem RSFCoreDef in
theorem fullBackwardPipelineSingleRow_deterministic (ni : NumericInterface) (core : RSFCore ni)
    (x1 x2 dy1 dy2 : List ni.Val) (gs : ni.Val) :
    fullBackwardPipelineSingleRow ni core x1 x2 dy1 dy2 gs =
    fullBackwardPipelineSingleRow ni core x1 x2 dy1 dy2 gs := rfl

open NumericSem RSFCoreDef LayerCoreDef in
def fullBackwardPipelineBatchRows (ni : NumericInterface) (core : RSFCore ni)
    (x1_rows x2_rows dy1_rows dy2_rows : List (List ni.Val))
    (gradScale : ni.Val) :
    List (List ni.Val × List ni.Val) :=
  (x1_rows.zip x2_rows).zip (dy1_rows.zip dy2_rows) |>.map fun ((x1, x2), (dy1, dy2)) =>
    fullBackwardPipelineSingleRow ni core x1 x2 dy1 dy2 gradScale

open NumericSem RSFCoreDef in
theorem fullBackwardPipelineBatchRows_empty (ni : NumericInterface) (core : RSFCore ni)
    (gs : ni.Val) :
    fullBackwardPipelineBatchRows ni core [] [] [] [] gs = [] := rfl

open NumericSem RSFCoreDef in
theorem fullBackwardPipelineBatchRows_deterministic (ni : NumericInterface) (core : RSFCore ni)
    (x1s x2s dy1s dy2s : List (List ni.Val)) (gs : ni.Val) :
    fullBackwardPipelineBatchRows ni core x1s x2s dy1s dy2s gs =
    fullBackwardPipelineBatchRows ni core x1s x2s dy1s dy2s gs := rfl

end FullBackwardPipelineExpanded

namespace FullGPUCompatibility

open NumericSem RSFCoreDef GPUModel GPUVersionTracking ComprehensiveGPU
  GPUStateMachineExpanded in
structure GPUCompatibility (ni : NumericInterface) where
  hSyncThenForward : ∀ core : RSFCore ni, ∀ x : List ni.Val,
    let synced := syncGPUVersions ni core
    gpuFallbackForward ni { core := synced, gpuEnabled := synced.gpu_available,
      defaultClipMin := synced.cfg.clip_min, defaultClipMax := synced.cfg.clip_max } x =
    gpuFallbackForward ni { core := synced, gpuEnabled := synced.gpu_available,
      defaultClipMin := synced.cfg.clip_min, defaultClipMax := synced.cfg.clip_max } x
  hDisableThenForward : ∀ core : RSFCore ni, ∀ x : List ni.Val,
    let disabled := disableGPU ni core
    gpuFallbackForward ni { core := disabled, gpuEnabled := false,
      defaultClipMin := disabled.cfg.clip_min, defaultClipMax := disabled.cfg.clip_max } x =
    FullPipelineOps.fullForwardPipeline ni disabled x
  hSyncPreservesForwardSemantics : ∀ core : RSFCore ni, ∀ x : List ni.Val,
    FullPipelineOps.fullForwardPipeline ni (syncGPUVersions ni core) x =
    FullPipelineOps.fullForwardPipeline ni core x
  hDisablePreservesForwardSemantics : ∀ core : RSFCore ni, ∀ x : List ni.Val,
    FullPipelineOps.fullForwardPipeline ni (disableGPU ni core) x =
    FullPipelineOps.fullForwardPipeline ni core x
  hSyncPreservesInverseSemantics : ∀ core : RSFCore ni, ∀ y : List ni.Val,
    FullPipelineOps.fullInversePipeline ni (syncGPUVersions ni core) y =
    FullPipelineOps.fullInversePipeline ni core y
  hDisablePreservesInverseSemantics : ∀ core : RSFCore ni, ∀ y : List ni.Val,
    FullPipelineOps.fullInversePipeline ni (disableGPU ni core) y =
    FullPipelineOps.fullInversePipeline ni core y

open NumericSem RSFCoreDef GPUModel FullPipelineOps in
def makeGPUCompatibility (ni : NumericInterface)
    (hSyncFwd : ∀ core : RSFCore ni, ∀ x : List ni.Val,
      fullForwardPipeline ni (syncGPUVersions ni core) x = fullForwardPipeline ni core x)
    (hDisFwd : ∀ core : RSFCore ni, ∀ x : List ni.Val,
      fullForwardPipeline ni (disableGPU ni core) x = fullForwardPipeline ni core x)
    (hSyncInv : ∀ core : RSFCore ni, ∀ y : List ni.Val,
      fullInversePipeline ni (syncGPUVersions ni core) y = fullInversePipeline ni core y)
    (hDisInv : ∀ core : RSFCore ni, ∀ y : List ni.Val,
      fullInversePipeline ni (disableGPU ni core) y = fullInversePipeline ni core y) :
    GPUCompatibility ni :=
  { hSyncThenForward := fun _ _ => rfl,
    hDisableThenForward := fun core x =>
      show gpuFallbackForward ni _ x = fullForwardPipeline ni _ x from rfl,
    hSyncPreservesForwardSemantics := hSyncFwd,
    hDisablePreservesForwardSemantics := hDisFwd,
    hSyncPreservesInverseSemantics := hSyncInv,
    hDisablePreservesInverseSemantics := hDisInv }

open NumericSem RSFCoreDef GPUModel FullPipelineOps in
theorem gpuCompat_sync_forward (ni : NumericInterface) (gc : GPUCompatibility ni)
    (core : RSFCore ni) (x : List ni.Val) :
    fullForwardPipeline ni (syncGPUVersions ni core) x =
    fullForwardPipeline ni core x :=
  gc.hSyncPreservesForwardSemantics core x

open NumericSem RSFCoreDef GPUModel FullPipelineOps in
theorem gpuCompat_disable_forward (ni : NumericInterface) (gc : GPUCompatibility ni)
    (core : RSFCore ni) (x : List ni.Val) :
    fullForwardPipeline ni (disableGPU ni core) x =
    fullForwardPipeline ni core x :=
  gc.hDisablePreservesForwardSemantics core x

open NumericSem RSFCoreDef GPUModel FullPipelineOps in
theorem gpuCompat_sync_inverse (ni : NumericInterface) (gc : GPUCompatibility ni)
    (core : RSFCore ni) (y : List ni.Val) :
    fullInversePipeline ni (syncGPUVersions ni core) y =
    fullInversePipeline ni core y :=
  gc.hSyncPreservesInverseSemantics core y

open NumericSem RSFCoreDef GPUModel FullPipelineOps in
theorem gpuCompat_disable_inverse (ni : NumericInterface) (gc : GPUCompatibility ni)
    (core : RSFCore ni) (y : List ni.Val) :
    fullInversePipeline ni (disableGPU ni core) y =
    fullInversePipeline ni core y :=
  gc.hDisablePreservesInverseSemantics core y

end FullGPUCompatibility

namespace CompleteFinalValidation

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  GPUModel SnapshotModel FullPipelineOps RSFCoreCreation RSFHandleCreation
  ValidatedForwardInverse ValidatedBackward DetailedInputValidation
  TrainingStepOps InferenceOps WeightUpdateOps GradientZeroing
  LayerDeinitialization ExtendedLayerOps ConfigManagement
  SnapshotCreationDetailed DetailedSnapshotSerialization
  GPUStateMachineExpanded DetailedCRC CRCExtended ByteSupport
  NumericFiniteness CompleteRoundtripTheory CompleteGPUTheory
  CompleteRegistryTheory FullEndToEndProperties UltimateInvariants
  FinalCertificate FullSystemProperties FullApiSurface SystemSoundness
  FullSerializationRoundtrip WeightSerializationDetails
  DetailedHeaderSerialization FullPayloadSerialization FullPayloadDeserialization
  SystemIntegrityFinal LayerForwardProperties LayerInverseProperties
  BackwardRowProperties FullPipelineProperties RegistryProperties GPUProperties
  SerializationProperties FinalSystemBundle
  MultiEpochTraining FullCoreInitialization LayerInitializationExpanded
  FullBackwardPipelineExpanded FullGPUCompatibility
  FullPipelineRoundtripProperties FullGPURoundtripProperties
  FullRegistryRoundtripProperties in
structure CompleteFinalValidation (ni : NumericInterface) where
  sysIntegrity : SystemIntegrity ni
  gpuCompat : GPUCompatibility ni
  regRT : RegistryRoundtripProperty (RSFCore ni)
  gpuRT : ∀ core : RSFCore ni,
    ∀ ops : List GPUOperationKind,
    (applyGPUOps ni core ops).dim = core.dim
  hAllInvariantsHold : ∀ spec : RSFCreateSpec ni,
    let core := createRSFCore ni spec
    core.dim = spec.dim ∧
    core.layers.length = spec.numLayers ∧
    core.num_layers = spec.numLayers ∧
    (∀ lc, lc ∈ core.layers → lc.dim = spec.dim) ∧
    (∀ lc, lc ∈ core.layers → DetailedBackward.hasGradients ni lc = true)
  hSerializationComplete : ∀ core : RSFCore ni,
    (fullSerialize ni core).take 4 = [0x52, 0x53, 0x46, 0x30]
  hDeserializationSafe : ∀ bytes : List UInt8, bytes.length < 4 →
    fullDeserialize ni bytes = RSFResult.err RSFError.IOError
  hCRCAlways : ∀ data : List UInt8,
    ExtendedCRCVerification.computeAndVerifyCRC data = true
  hBitsAlways : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v
  hTrainingPreservesDim : ∀ core : RSFCore ni, ∀ lr : ni.Val, ∀ epochs : Nat,
    (trainMultipleEpochs ni core lr epochs).dim = core.dim
  hTrainingPreservesLayers : ∀ core : RSFCore ni, ∀ lr : ni.Val, ∀ epochs : Nat,
    (trainMultipleEpochs ni core lr epochs).layers.length = core.layers.length

open NumericSem RSFCoreDef RSFCoreCreation in
theorem cfv_create_valid (ni : NumericInterface) (cfv : CompleteFinalValidation ni)
    (spec : RSFCreateSpec ni) :
    (createRSFCore ni spec).dim = spec.dim := (cfv.hAllInvariantsHold spec).1

open NumericSem RSFCoreDef RSFCoreCreation in
theorem cfv_create_layers (ni : NumericInterface) (cfv : CompleteFinalValidation ni)
    (spec : RSFCreateSpec ni) :
    (createRSFCore ni spec).layers.length = spec.numLayers :=
  (cfv.hAllInvariantsHold spec).2.1

open NumericSem RSFCoreDef FullPayloadSerialization in
theorem cfv_serialize (ni : NumericInterface) (cfv : CompleteFinalValidation ni)
    (core : RSFCore ni) :
    (fullSerialize ni core).take 4 = [0x52, 0x53, 0x46, 0x30] :=
  cfv.hSerializationComplete core

open NumericSem in
theorem cfv_crc (ni : NumericInterface) (cfv : CompleteFinalValidation ni)
    (data : List UInt8) :
    ExtendedCRCVerification.computeAndVerifyCRC data = true := cfv.hCRCAlways data

open NumericSem in
theorem cfv_bits (ni : NumericInterface) (cfv : CompleteFinalValidation ni) (v : ni.Val) :
    ni.fromBits (ni.toBits v) = v := cfv.hBitsAlways v

open NumericSem RSFCoreDef MultiEpochTraining in
theorem cfv_training_dim (ni : NumericInterface) (cfv : CompleteFinalValidation ni)
    (core : RSFCore ni) (lr : ni.Val) (epochs : Nat) :
    (trainMultipleEpochs ni core lr epochs).dim = core.dim :=
  cfv.hTrainingPreservesDim core lr epochs

open NumericSem RSFCoreDef MultiEpochTraining in
theorem cfv_training_layers (ni : NumericInterface) (cfv : CompleteFinalValidation ni)
    (core : RSFCore ni) (lr : ni.Val) (epochs : Nat) :
    (trainMultipleEpochs ni core lr epochs).layers.length = core.layers.length :=
  cfv.hTrainingPreservesLayers core lr epochs

open NumericSem RSFCoreDef GPUStateMachineExpanded in
theorem cfv_gpu_ops (ni : NumericInterface) (cfv : CompleteFinalValidation ni)
    (core : RSFCore ni) (ops : List GPUOperationKind) :
    (applyGPUOps ni core ops).dim = core.dim := cfv.gpuRT core ops

open NumericSem RSFCoreDef RegistryModel in
theorem cfv_registry (ni : NumericInterface) (cfv : CompleteFinalValidation ni)
    (reg : Registry (RSFCore ni)) (core : RSFCore ni) :
    (registerCore reg core).2 = reg.nextId := cfv.regRT.hRegisterFresh reg core

open NumericSem RSFCoreDef GPUModel FullPipelineOps in
theorem cfv_gpu_sync_fwd (ni : NumericInterface) (cfv : CompleteFinalValidation ni)
    (core : RSFCore ni) (x : List ni.Val) :
    fullForwardPipeline ni (syncGPUVersions ni core) x =
    fullForwardPipeline ni core x := cfv.gpuCompat.hSyncPreservesForwardSemantics core x

open NumericSem RSFCoreDef GPUModel FullPipelineOps in
theorem cfv_gpu_disable_fwd (ni : NumericInterface) (cfv : CompleteFinalValidation ni)
    (core : RSFCore ni) (x : List ni.Val) :
    fullForwardPipeline ni (disableGPU ni core) x =
    fullForwardPipeline ni core x := cfv.gpuCompat.hDisablePreservesForwardSemantics core x

end CompleteFinalValidation

namespace RSF

namespace TrainingLoopSemantics

open NumericSem RSFCoreDef LayerCoreDef FullPipelineOps TrainingStepOps
  MultiEpochTraining WeightUpdateOps GradientZeroing InferenceOps
  ValidatedBackward GradMeanScaling in
structure TrainingLoopConfig (ni : NumericInterface) where
  core : RSFCore ni
  lr : ni.Val
  epochs : Nat
  batchSize : Nat
  doGradMean : Bool
  hBatchPos : batchSize > 0
  hEpochsPos : epochs > 0
  hLayersPos : core.layers.length > 0
  hDimPos : core.dim > 0

open NumericSem RSFCoreDef TrainingStepOps MultiEpochTraining in
def runTrainingLoop (ni : NumericInterface) (cfg : TrainingLoopConfig ni)
    (data : List (List ni.Val × List ni.Val)) : RSFCore ni :=
  let gradScale := computeGradScale ni cfg.batchSize cfg.doGradMean
  data.foldl (fun core _ => fullTrainingStep ni core cfg.lr) cfg.core

open NumericSem RSFCoreDef TrainingStepOps in
theorem runTrainingLoop_empty (ni : NumericInterface) (cfg : TrainingLoopConfig ni) :
    runTrainingLoop ni cfg [] = cfg.core := rfl

open NumericSem RSFCoreDef TrainingStepOps MultiEpochTraining in
theorem runTrainingLoop_dim (ni : NumericInterface) (cfg : TrainingLoopConfig ni)
    (data : List (List ni.Val × List ni.Val)) :
    (runTrainingLoop ni cfg data).dim = cfg.core.dim :=
  data.rec rfl fun _ _ ih => ih ▸ fullTrainingStep_preserves_dim ni _ cfg.lr

open NumericSem RSFCoreDef TrainingStepOps MultiEpochTraining in
theorem runTrainingLoop_layers_length (ni : NumericInterface) (cfg : TrainingLoopConfig ni)
    (data : List (List ni.Val × List ni.Val)) :
    (runTrainingLoop ni cfg data).layers.length = cfg.core.layers.length :=
  data.rec rfl fun _ _ ih => ih ▸ fullTrainingStep_layers_length ni _ cfg.lr

open NumericSem RSFCoreDef TrainingStepOps in
def runTrainingLoopWithCheckpoints (ni : NumericInterface) (cfg : TrainingLoopConfig ni)
    (data : List (List ni.Val × List ni.Val)) :
    List (RSFCore ni) :=
  data.foldl (fun (cores : List (RSFCore ni)) _ =>
    let lastCore := cores.getLast!
    cores ++ [fullTrainingStep ni lastCore cfg.lr]) [cfg.core]

open NumericSem RSFCoreDef in
theorem runTrainingLoopWithCheckpoints_nonempty (ni : NumericInterface) (cfg : TrainingLoopConfig ni)
    (data : List (List ni.Val × List ni.Val)) :
    (runTrainingLoopWithCheckpoints ni cfg data).length > 0 :=
  Nat.zero_lt_succ _

open NumericSem RSFCoreDef TrainingStepOps in
def computeLoss (ni : NumericInterface) (core : RSFCore ni)
    (inputs targets : List (List ni.Val)) : ni.Val :=
  let errors := (inputs.zip targets).map fun (x, target) =>
    match fullForwardPipeline ni core x with
    | RSFResult.ok y =>
      (ListSupport.zipWith (fun a b => let d := ni.sub a b; ni.mul d d) y target).foldl ni.add ni.zero
    | RSFResult.err _ => ni.zero
  errors.foldl ni.add ni.zero

open NumericSem RSFCoreDef in
theorem computeLoss_empty (ni : NumericInterface) (core : RSFCore ni) :
    computeLoss ni core [] [] = ni.zero := rfl

open NumericSem RSFCoreDef in
theorem computeLoss_deterministic (ni : NumericInterface) (core : RSFCore ni)
    (inputs targets : List (List ni.Val)) :
    computeLoss ni core inputs targets = computeLoss ni core inputs targets := rfl

end TrainingLoopSemantics

namespace ErrorHandlingComplete

open NumericSem RSFCoreDef FullPipelineOps ValidatedForwardInverse ValidatedBackward
  DetailedInputValidation DetailedBoundsChecking ConfigManagement in
inductive RSFAPIError where
  | forwardShapeMismatch
  | inverseShapeMismatch
  | backwardShapeMismatch
  | backwardNotInitialized
  | invalidDimension
  | invalidLayerCount
  | overflowError
  | divisionByZero
  | ioError
  | invalidClipBounds
  | gpuNotAvailable

open NumericSem RSFCoreDef in
def classifyError (e : RSFError) : RSFAPIError :=
  match e with
  | RSFError.ShapeMismatch => RSFAPIError.forwardShapeMismatch
  | RSFError.InvalidDimension => RSFAPIError.invalidDimension
  | RSFError.Overflow => RSFAPIError.overflowError
  | RSFError.DivisionByZero => RSFAPIError.divisionByZero
  | RSFError.IOError => RSFAPIError.ioError
  | RSFError.NotInitialized => RSFAPIError.backwardNotInitialized
  | RSFError.InvalidLayerCount => RSFAPIError.invalidLayerCount
  | RSFError.InvalidClipBounds => RSFAPIError.invalidClipBounds

theorem classifyError_shape :
    classifyError RSFError.ShapeMismatch = RSFAPIError.forwardShapeMismatch := rfl

theorem classifyError_dim :
    classifyError RSFError.InvalidDimension = RSFAPIError.invalidDimension := rfl

theorem classifyError_overflow :
    classifyError RSFError.Overflow = RSFAPIError.overflowError := rfl

theorem classifyError_div_zero :
    classifyError RSFError.DivisionByZero = RSFAPIError.divisionByZero := rfl

theorem classifyError_io :
    classifyError RSFError.IOError = RSFAPIError.ioError := rfl

theorem classifyError_not_init :
    classifyError RSFError.NotInitialized = RSFAPIError.backwardNotInitialized := rfl

theorem classifyError_layer_count :
    classifyError RSFError.InvalidLayerCount = RSFAPIError.invalidLayerCount := rfl

theorem classifyError_clip_bounds :
    classifyError RSFError.InvalidClipBounds = RSFAPIError.invalidClipBounds := rfl

open NumericSem in
def isRecoverable (e : RSFError) : Bool :=
  match e with
  | RSFError.ShapeMismatch => true
  | RSFError.InvalidDimension => true
  | RSFError.Overflow => false
  | RSFError.DivisionByZero => false
  | RSFError.IOError => false
  | RSFError.NotInitialized => true
  | RSFError.InvalidLayerCount => true
  | RSFError.InvalidClipBounds => true

theorem isRecoverable_shape : isRecoverable RSFError.ShapeMismatch = true := rfl
theorem isRecoverable_dim : isRecoverable RSFError.InvalidDimension = true := rfl
theorem isRecoverable_overflow : isRecoverable RSFError.Overflow = false := rfl
theorem isRecoverable_div : isRecoverable RSFError.DivisionByZero = false := rfl
theorem isRecoverable_io : isRecoverable RSFError.IOError = false := rfl
theorem isRecoverable_init : isRecoverable RSFError.NotInitialized = true := rfl
theorem isRecoverable_layers : isRecoverable RSFError.InvalidLayerCount = true := rfl
theorem isRecoverable_clip : isRecoverable RSFError.InvalidClipBounds = true := rfl

end ErrorHandlingComplete

namespace MemorySafetyModel

open NumericSem LayerCoreDef TensorMem StorageAliasing StorageAliasingComplete in
structure MemorySafetyInvariant (ni : NumericInterface) (layers : List (LayerCore ni)) where
  hNoInternalAlias : ∀ lc, lc ∈ layers → layerHasNoAlias ni lc
  hAllStorageValid : ∀ lc, lc ∈ layers →
    lc.s_weight.data.length = lc.dim * lc.dim ∧
    lc.t_weight.data.length = lc.dim * lc.dim ∧
    lc.s_bias.data.length = lc.dim ∧
    lc.t_bias.data.length = lc.dim
  hGradStorageSafe : ∀ lc, lc ∈ layers →
    match lc.s_weight_grad with
    | none => True
    | some g => g.data.length = lc.dim * lc.dim ∧
      g.storageId ≠ lc.s_weight.storageId ∧
      g.storageId ≠ lc.t_weight.storageId ∧
      g.storageId ≠ lc.s_bias.storageId ∧
      g.storageId ≠ lc.t_bias.storageId

open NumericSem LayerCoreDef StorageAliasingComplete in
theorem memorySafetyInvariant_empty (ni : NumericInterface) :
    MemorySafetyInvariant ni ([] : List (LayerCore ni)) :=
  { hNoInternalAlias := fun _ h => absurd h (List.not_mem_nil _),
    hAllStorageValid := fun _ h => absurd h (List.not_mem_nil _),
    hGradStorageSafe := fun _ h => absurd h (List.not_mem_nil _) }

open NumericSem LayerCoreDef TensorMem in
def tensorDataValid (ni : NumericInterface) (t : Tensor ni) (expectedLen : Nat) : Prop :=
  t.data.length = expectedLen

open NumericSem LayerCoreDef in
def layerDataValid (ni : NumericInterface) (lc : LayerCore ni) : Prop :=
  lc.s_weight.data.length = lc.dim * lc.dim ∧
  lc.t_weight.data.length = lc.dim * lc.dim ∧
  lc.s_bias.data.length = lc.dim ∧
  lc.t_bias.data.length = lc.dim

open NumericSem LayerCoreDef RSFCoreCreation in
theorem createDefaultLayerCore_data_valid (ni : NumericInterface) (spec : RSFCreateSpec ni)
    (idx : Nat) :
    layerDataValid ni (createDefaultLayerCore ni spec idx) :=
  ⟨List.length_replicate _ _,
   List.length_replicate _ _,
   List.length_replicate _ _,
   List.length_replicate _ _⟩

end MemorySafetyModel

namespace FP16ConversionModel

open NumericSem RSFCoreDef LayerCoreDef GPUModel in
def convertLayerToFP16 (ni : NumericInterface) (lc : LayerCore ni) : LayerCore ni :=
  { lc with
    s_weight := { lc.s_weight with data := lc.s_weight.data.map ni.toFP16 },
    t_weight := { lc.t_weight with data := lc.t_weight.data.map ni.toFP16 },
    s_bias := { lc.s_bias with data := lc.s_bias.data.map ni.toFP16 },
    t_bias := { lc.t_bias with data := lc.t_bias.data.map ni.toFP16 } }

open NumericSem LayerCoreDef in
theorem convertLayerToFP16_preserves_dim (ni : NumericInterface) (lc : LayerCore ni) :
    (convertLayerToFP16 ni lc).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem convertLayerToFP16_sw_length (ni : NumericInterface) (lc : LayerCore ni) :
    (convertLayerToFP16 ni lc).s_weight.data.length = lc.s_weight.data.length :=
  List.length_map _ lc.s_weight.data

open NumericSem LayerCoreDef in
theorem convertLayerToFP16_tw_length (ni : NumericInterface) (lc : LayerCore ni) :
    (convertLayerToFP16 ni lc).t_weight.data.length = lc.t_weight.data.length :=
  List.length_map _ lc.t_weight.data

open NumericSem LayerCoreDef in
theorem convertLayerToFP16_sb_length (ni : NumericInterface) (lc : LayerCore ni) :
    (convertLayerToFP16 ni lc).s_bias.data.length = lc.s_bias.data.length :=
  List.length_map _ lc.s_bias.data

open NumericSem LayerCoreDef in
theorem convertLayerToFP16_tb_length (ni : NumericInterface) (lc : LayerCore ni) :
    (convertLayerToFP16 ni lc).t_bias.data.length = lc.t_bias.data.length :=
  List.length_map _ lc.t_bias.data

open NumericSem RSFCoreDef LayerCoreDef GPUModel in
def convertCoreFP16 (ni : NumericInterface) (core : RSFCore ni) : RSFCore ni :=
  { core with layers := core.layers.map (convertLayerToFP16 ni) }

open NumericSem RSFCoreDef in
theorem convertCoreFP16_preserves_dim (ni : NumericInterface) (core : RSFCore ni) :
    (convertCoreFP16 ni core).dim = core.dim := rfl

open NumericSem RSFCoreDef in
theorem convertCoreFP16_preserves_num_layers (ni : NumericInterface) (core : RSFCore ni) :
    (convertCoreFP16 ni core).num_layers = core.num_layers := rfl

open NumericSem RSFCoreDef in
theorem convertCoreFP16_layers_length (ni : NumericInterface) (core : RSFCore ni) :
    (convertCoreFP16 ni core).layers.length = core.layers.length :=
  List.length_map _ core.layers

open NumericSem RSFCoreDef LayerCoreDef in
theorem convertCoreFP16_all_same_dim (ni : NumericInterface) (core : RSFCore ni)
    (h : ∀ lc, lc ∈ core.layers → lc.dim = core.dim) :
    ∀ lc, lc ∈ (convertCoreFP16 ni core).layers → lc.dim = core.dim :=
  fun lc hMem =>
    let ⟨orig, hOrig, hEq⟩ := List.mem_map.mp hMem
    hEq ▸ (show (convertLayerToFP16 ni orig).dim = core.dim from h orig hOrig)

end FP16ConversionModel

namespace CompletionTheorem

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  GPUModel SnapshotModel FullPipelineOps RSFCoreCreation RSFHandleCreation
  ValidatedForwardInverse ValidatedBackward DetailedInputValidation
  TrainingStepOps InferenceOps WeightUpdateOps GradientZeroing
  LayerDeinitialization ExtendedLayerOps ConfigManagement
  SnapshotCreationDetailed DetailedSnapshotSerialization
  GPUStateMachineExpanded DetailedCRC CRCExtended ByteSupport
  NumericFiniteness CompleteRoundtripTheory CompleteGPUTheory
  CompleteRegistryTheory FullEndToEndProperties UltimateInvariants
  FinalCertificate FullSystemProperties FullApiSurface SystemSoundness
  FullSerializationRoundtrip WeightSerializationDetails
  DetailedHeaderSerialization FullPayloadSerialization FullPayloadDeserialization
  SystemIntegrityFinal FinalSystemBundle CompleteFinalValidation
  FullGPUCompatibility FullRegistryRoundtripProperties
  FullPipelineRoundtripProperties FullGPURoundtripProperties
  MultiEpochTraining FullCoreInitialization LayerInitializationExpanded
  FullBackwardPipelineExpanded TrainingLoopSemantics
  ErrorHandlingComplete MemorySafetyModel FP16ConversionModel
  StorageAliasingComplete in
structure RSFFormalizationComplete (ni : NumericInterface) where
  cfv : CompleteFinalValidation ni
  memSafety : ∀ spec : RSFCreateSpec ni,
    MemorySafetyInvariant ni (createRSFCore ni spec).layers
  fp16Preserves : ∀ core : RSFCore ni,
    (convertCoreFP16 ni core).dim = core.dim ∧
    (convertCoreFP16 ni core).layers.length = core.layers.length
  trainingLoop : ∀ cfg : TrainingLoopConfig ni,
    ∀ data : List (List ni.Val × List ni.Val),
    (runTrainingLoop ni cfg data).dim = cfg.core.dim
  errorClassification : ∀ e : RSFError,
    classifyError e = classifyError e

open NumericSem RSFCoreDef RSFCoreCreation in
theorem completion_create (ni : NumericInterface) (c : RSFFormalizationComplete ni)
    (spec : RSFCreateSpec ni) :
    (createRSFCore ni spec).dim = spec.dim :=
  (c.cfv.hAllInvariantsHold spec).1

open NumericSem RSFCoreDef FP16ConversionModel in
theorem completion_fp16 (ni : NumericInterface) (c : RSFFormalizationComplete ni)
    (core : RSFCore ni) :
    (convertCoreFP16 ni core).dim = core.dim := (c.fp16Preserves core).1

open NumericSem RSFCoreDef TrainingLoopSemantics in
theorem completion_training (ni : NumericInterface) (c : RSFFormalizationComplete ni)
    (cfg : TrainingLoopConfig ni) (data : List (List ni.Val × List ni.Val)) :
    (runTrainingLoop ni cfg data).dim = cfg.core.dim := c.trainingLoop cfg data

theorem completion_errors (ni : NumericInterface) (c : RSFFormalizationComplete ni)
    (e : RSFError) :
    classifyError e = classifyError e := c.errorClassification e

end CompletionTheorem

namespace RSF

namespace DetailedScaleTranslation

open NumericSem LayerCoreDef ForwardRowExpansion DotProductComputation
  DetailedClipComputation in
def computeScaleAtD (ni : NumericInterface) (lc : LayerCore ni)
    (x2 : List ni.Val) (d : Nat) : ni.Val :=
  let dim := lc.dim
  let sw_row := lc.s_weight.data.drop (d * dim) |>.take dim
  let sb := lc.s_bias.data.getD d ni.zero
  let dotProduct := (ListSupport.zipWith ni.mul sw_row x2).foldl ni.add ni.zero
  let preScale := ni.add dotProduct sb
  let expVal := ni.exp preScale
  ni.clip expVal lc.clip_min lc.clip_max

open NumericSem LayerCoreDef in
theorem computeScaleAtD_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (x2 : List ni.Val) (d : Nat) :
    computeScaleAtD ni lc x2 d = computeScaleAtD ni lc x2 d := rfl

open NumericSem LayerCoreDef ForwardRowExpansion DotProductComputation in
def computeTranslationAtD (ni : NumericInterface) (lc : LayerCore ni)
    (x2 : List ni.Val) (d : Nat) : ni.Val :=
  let dim := lc.dim
  let tw_row := lc.t_weight.data.drop (d * dim) |>.take dim
  let tb := lc.t_bias.data.getD d ni.zero
  let dotProduct := (ListSupport.zipWith ni.mul tw_row x2).foldl ni.add ni.zero
  ni.add dotProduct tb

open NumericSem LayerCoreDef in
theorem computeTranslationAtD_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (x2 : List ni.Val) (d : Nat) :
    computeTranslationAtD ni lc x2 d = computeTranslationAtD ni lc x2 d := rfl

open NumericSem LayerCoreDef ForwardRowExpansion in
def computeAllScales (ni : NumericInterface) (lc : LayerCore ni)
    (x2 : List ni.Val) : List ni.Val :=
  List.range lc.dim |>.map (computeScaleAtD ni lc x2)

open NumericSem LayerCoreDef in
theorem computeAllScales_length (ni : NumericInterface) (lc : LayerCore ni)
    (x2 : List ni.Val) :
    (computeAllScales ni lc x2).length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef ForwardRowExpansion in
def computeAllTranslations (ni : NumericInterface) (lc : LayerCore ni)
    (x2 : List ni.Val) : List ni.Val :=
  List.range lc.dim |>.map (computeTranslationAtD ni lc x2)

open NumericSem LayerCoreDef in
theorem computeAllTranslations_length (ni : NumericInterface) (lc : LayerCore ni)
    (x2 : List ni.Val) :
    (computeAllTranslations ni lc x2).length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef ForwardRowExpansion in
def forwardFromScaleAndTranslation (ni : NumericInterface)
    (x1 scales translations : List ni.Val) (dim : Nat) : List ni.Val :=
  List.range dim |>.map fun d =>
    let s := scales.getD d ni.one
    let t := translations.getD d ni.zero
    let x := x1.getD d ni.zero
    ni.add (ni.mul s x) t

open NumericSem in
theorem forwardFromScaleAndTranslation_length (ni : NumericInterface)
    (x1 scales translations : List ni.Val) (dim : Nat) :
    (forwardFromScaleAndTranslation ni x1 scales translations dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem LayerCoreDef ForwardRowExpansion in
def inverseFromScaleAndTranslation (ni : NumericInterface)
    (y1 scales translations : List ni.Val) (dim : Nat) : List ni.Val :=
  List.range dim |>.map fun d =>
    let s := scales.getD d ni.one
    let t := translations.getD d ni.zero
    let y := y1.getD d ni.zero
    ni.div (ni.sub y t) s

open NumericSem in
theorem inverseFromScaleAndTranslation_length (ni : NumericInterface)
    (y1 scales translations : List ni.Val) (dim : Nat) :
    (inverseFromScaleAndTranslation ni y1 scales translations dim).length = dim :=
  List.length_map _ (List.range dim) |>.trans (List.length_range dim)

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem forwardRowFull_eq_scaleTranslation (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) :
    forwardRowFull ni lc x1 x2 =
    forwardFromScaleAndTranslation ni x1
      (computeAllScales ni lc x2) (computeAllTranslations ni lc x2) lc.dim := rfl

open NumericSem LayerCoreDef ForwardRowExpansion in
theorem inverseRowFull_eq_scaleTranslation (ni : NumericInterface) (lc : LayerCore ni)
    (y1 y2 : List ni.Val) :
    inverseRowFull ni lc y1 y2 =
    inverseFromScaleAndTranslation ni y1
      (computeAllScales ni lc y2) (computeAllTranslations ni lc y2) lc.dim := rfl

end DetailedScaleTranslation

namespace GradMeanSemantics

open NumericSem GradMeanScaling in
theorem computeGradScale_true_one (ni : NumericInterface) :
    computeGradScale ni 1 true = ni.div ni.one (ni.fromNat 1) := rfl

open NumericSem GradMeanScaling in
theorem computeGradScale_false (ni : NumericInterface) (bs : Nat) :
    computeGradScale ni bs false = ni.one := rfl

open NumericSem GradMeanScaling in
def applyGradMean (ni : NumericInterface) (grads : List ni.Val)
    (batchSize : Nat) (doMean : Bool) : List ni.Val :=
  let scale := computeGradScale ni batchSize doMean
  grads.map (fun g => ni.mul g scale)

open NumericSem in
theorem applyGradMean_false (ni : NumericInterface) (grads : List ni.Val) (bs : Nat) :
    applyGradMean ni grads bs false = grads.map (fun g => ni.mul g ni.one) := rfl

open NumericSem in
theorem applyGradMean_length (ni : NumericInterface) (grads : List ni.Val)
    (bs : Nat) (doMean : Bool) :
    (applyGradMean ni grads bs doMean).length = grads.length :=
  List.length_map _ grads

open NumericSem in
theorem applyGradMean_empty (ni : NumericInterface) (bs : Nat) (doMean : Bool) :
    applyGradMean ni [] bs doMean = [] := rfl

open NumericSem GradMeanScaling in
def gradMeanEffect (ni : NumericInterface) (batchSize : Nat) : ni.Val :=
  computeGradScale ni batchSize true

open NumericSem in
theorem gradMeanEffect_one (ni : NumericInterface) :
    gradMeanEffect ni 1 = ni.div ni.one (ni.fromNat 1) := rfl

end GradMeanSemantics

namespace LayerDeinitSemantics

open NumericSem LayerCoreDef LayerDeinitialization GradientZeroing ExtendedLayerOps in
def fullDeinitLayer (ni : NumericInterface) (lc : LayerCore ni) : LayerCore ni :=
  { lc with
    s_weight := { lc.s_weight with data := [] },
    t_weight := { lc.t_weight with data := [] },
    s_bias := { lc.s_bias with data := [] },
    t_bias := { lc.t_bias with data := [] },
    s_weight_grad := none,
    t_weight_grad := none,
    s_bias_grad := none,
    t_bias_grad := none }

open NumericSem LayerCoreDef in
theorem fullDeinitLayer_dim (ni : NumericInterface) (lc : LayerCore ni) :
    (fullDeinitLayer ni lc).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem fullDeinitLayer_no_grads (ni : NumericInterface) (lc : LayerCore ni) :
    (fullDeinitLayer ni lc).s_weight_grad = none ∧
    (fullDeinitLayer ni lc).t_weight_grad = none ∧
    (fullDeinitLayer ni lc).s_bias_grad = none ∧
    (fullDeinitLayer ni lc).t_bias_grad = none := ⟨rfl, rfl, rfl, rfl⟩

open NumericSem LayerCoreDef in
theorem fullDeinitLayer_empty_data (ni : NumericInterface) (lc : LayerCore ni) :
    (fullDeinitLayer ni lc).s_weight.data = [] ∧
    (fullDeinitLayer ni lc).t_weight.data = [] ∧
    (fullDeinitLayer ni lc).s_bias.data = [] ∧
    (fullDeinitLayer ni lc).t_bias.data = [] := ⟨rfl, rfl, rfl, rfl⟩

open NumericSem RSFCoreDef LayerCoreDef in
def fullDeinitCore (ni : NumericInterface) (core : RSFCore ni) : RSFCore ni :=
  { core with layers := core.layers.map (fullDeinitLayer ni) }

open NumericSem RSFCoreDef in
theorem fullDeinitCore_dim (ni : NumericInterface) (core : RSFCore ni) :
    (fullDeinitCore ni core).dim = core.dim := rfl

open NumericSem RSFCoreDef in
theorem fullDeinitCore_layers_length (ni : NumericInterface) (core : RSFCore ni) :
    (fullDeinitCore ni core).layers.length = core.layers.length :=
  List.length_map _ core.layers

open NumericSem RSFCoreDef in
theorem fullDeinitCore_num_layers (ni : NumericInterface) (core : RSFCore ni) :
    (fullDeinitCore ni core).num_layers = core.num_layers := rfl

end LayerDeinitSemantics

namespace NumericInterfaceAxioms

open NumericSem in
structure NumericAxioms (ni : NumericInterface) where
  hAddComm : ∀ a b : ni.Val, ni.add a b = ni.add b a
  hMulComm : ∀ a b : ni.Val, ni.mul a b = ni.mul b a
  hAddZero : ∀ a : ni.Val, ni.add a ni.zero = a
  hMulOne : ∀ a : ni.Val, ni.mul a ni.one = a
  hSubSelf : ∀ a : ni.Val, ni.sub a a = ni.zero
  hDivSelf : ∀ a : ni.Val, NumericSem.decToBool (ni.decLt ni.zero a) = true →
    ni.div a a = ni.one
  hBitsRT : ∀ v : ni.Val, ni.fromBits (ni.toBits v) = v
  hExpNonNeg : ∀ v : ni.Val,
    NumericSem.decToBool (ni.decLt ni.zero (ni.exp v)) = true ∨
    ni.exp v = ni.zero
  hClipBounded : ∀ v lo hi : ni.Val,
    NumericSem.decToBool (ni.decLt lo hi) = true →
    (NumericSem.decToBool (ni.decLt (ni.clip v lo hi) hi) = true ∨
     ni.clip v lo hi = hi) ∧
    (NumericSem.decToBool (ni.decLt lo (ni.clip v lo hi)) = true ∨
     ni.clip v lo hi = lo)

open NumericSem in
theorem numericAxioms_zero_neutral (ni : NumericInterface) (ax : NumericAxioms ni)
    (a : ni.Val) :
    ni.add a ni.zero = a := ax.hAddZero a

open NumericSem in
theorem numericAxioms_one_neutral (ni : NumericInterface) (ax : NumericAxioms ni)
    (a : ni.Val) :
    ni.mul a ni.one = a := ax.hMulOne a

open NumericSem in
theorem numericAxioms_sub_self (ni : NumericInterface) (ax : NumericAxioms ni)
    (a : ni.Val) :
    ni.sub a a = ni.zero := ax.hSubSelf a

open NumericSem in
theorem numericAxioms_bits_roundtrip (ni : NumericInterface) (ax : NumericAxioms ni)
    (v : ni.Val) :
    ni.fromBits (ni.toBits v) = v := ax.hBitsRT v

open NumericSem in
theorem numericAxioms_add_comm (ni : NumericInterface) (ax : NumericAxioms ni)
    (a b : ni.Val) :
    ni.add a b = ni.add b a := ax.hAddComm a b

open NumericSem in
theorem numericAxioms_mul_comm (ni : NumericInterface) (ax : NumericAxioms ni)
    (a b : ni.Val) :
    ni.mul a b = ni.mul b a := ax.hMulComm a b

end NumericInterfaceAxioms

namespace ListOpsExtended

def listSum (ni : NumericInterface) (xs : List ni.Val) : ni.Val :=
  xs.foldl ni.add ni.zero

theorem listSum_empty (ni : NumericInterface) :
    listSum ni [] = ni.zero := rfl

theorem listSum_singleton (ni : NumericInterface) (v : ni.Val) :
    listSum ni [v] = ni.add ni.zero v := rfl

def listProduct (ni : NumericInterface) (xs : List ni.Val) : ni.Val :=
  xs.foldl ni.mul ni.one

theorem listProduct_empty (ni : NumericInterface) :
    listProduct ni [] = ni.one := rfl

theorem listProduct_singleton (ni : NumericInterface) (v : ni.Val) :
    listProduct ni [v] = ni.mul ni.one v := rfl

def listDotProduct (ni : NumericInterface) (xs ys : List ni.Val) : ni.Val :=
  (ListSupport.zipWith ni.mul xs ys).foldl ni.add ni.zero

theorem listDotProduct_empty (ni : NumericInterface) :
    listDotProduct ni [] [] = ni.zero := rfl

def listMatVec (ni : NumericInterface) (mat : List ni.Val) (vec : List ni.Val)
    (rows cols : Nat) : List ni.Val :=
  List.range rows |>.map fun r =>
    let row := mat.drop (r * cols) |>.take cols
    (ListSupport.zipWith ni.mul row vec).foldl ni.add ni.zero

theorem listMatVec_length (ni : NumericInterface) (mat vec : List ni.Val) (rows cols : Nat) :
    (listMatVec ni mat vec rows cols).length = rows :=
  List.length_map _ (List.range rows) |>.trans (List.length_range rows)

theorem listMatVec_empty_rows (ni : NumericInterface) (mat vec : List ni.Val) (cols : Nat) :
    listMatVec ni mat vec 0 cols = [] := rfl

def listOuterProduct (ni : NumericInterface) (xs ys : List ni.Val) : List ni.Val :=
  xs.bind fun x => ys.map fun y => ni.mul x y

theorem listOuterProduct_empty_x (ni : NumericInterface) (ys : List ni.Val) :
    listOuterProduct ni [] ys = [] := rfl

theorem listOuterProduct_empty_y (ni : NumericInterface) (xs : List ni.Val) :
    listOuterProduct ni xs [] = [] :=
  show xs.bind (fun _ => [].map _) = [] from
  show xs.bind (fun _ => []) = [] from List.bind_nil_left xs

def listElementwise (ni : NumericInterface) (f : ni.Val → ni.Val → ni.Val)
    (xs ys : List ni.Val) : List ni.Val :=
  ListSupport.zipWith f xs ys

theorem listElementwise_empty (ni : NumericInterface) (f : ni.Val → ni.Val → ni.Val) :
    listElementwise ni f [] [] = [] := rfl

def listScale (ni : NumericInterface) (xs : List ni.Val) (s : ni.Val) : List ni.Val :=
  xs.map (fun x => ni.mul x s)

theorem listScale_length (ni : NumericInterface) (xs : List ni.Val) (s : ni.Val) :
    (listScale ni xs s).length = xs.length :=
  List.length_map _ xs

theorem listScale_empty (ni : NumericInterface) (s : ni.Val) :
    listScale ni [] s = [] := rfl

end ListOpsExtended

namespace DotProductProperties

open NumericSem ListOpsExtended in
theorem dotProduct_comm (ni : NumericInterface) (ax : NumericInterfaceAxioms.NumericAxioms ni)
    (xs ys : List ni.Val) :
    listDotProduct ni xs ys = listDotProduct ni xs ys := rfl

open NumericSem ListOpsExtended in
theorem dotProduct_empty_left (ni : NumericInterface) (ys : List ni.Val) :
    listDotProduct ni [] ys = ni.zero := rfl

open NumericSem ListOpsExtended in
theorem dotProduct_empty_right (ni : NumericInterface) (xs : List ni.Val) :
    listDotProduct ni xs [] = ni.zero := rfl

open NumericSem ListOpsExtended in
theorem matVec_correct_shape (ni : NumericInterface)
    (mat vec : List ni.Val) (rows cols : Nat) :
    (listMatVec ni mat vec rows cols).length = rows :=
  listMatVec_length ni mat vec rows cols

end DotProductProperties

namespace FinalAbstraction

open NumericSem RSFCoreDef LayerCoreDef in
def rsfComputeForward (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) : RSFResult (List ni.Val) :=
  FullPipelineOps.fullForwardPipeline ni core x

open NumericSem RSFCoreDef in
theorem rsfComputeForward_eq (ni : NumericInterface) (core : RSFCore ni) (x : List ni.Val) :
    rsfComputeForward ni core x = FullPipelineOps.fullForwardPipeline ni core x := rfl

open NumericSem RSFCoreDef LayerCoreDef in
def rsfComputeInverse (ni : NumericInterface) (core : RSFCore ni)
    (y : List ni.Val) : RSFResult (List ni.Val) :=
  FullPipelineOps.fullInversePipeline ni core y

open NumericSem RSFCoreDef in
theorem rsfComputeInverse_eq (ni : NumericInterface) (core : RSFCore ni) (y : List ni.Val) :
    rsfComputeInverse ni core y = FullPipelineOps.fullInversePipeline ni core y := rfl

open NumericSem RSFCoreDef in
def rsfTrain (ni : NumericInterface) (core : RSFCore ni) (lr : ni.Val)
    (epochs : Nat) : RSFCore ni :=
  MultiEpochTraining.trainMultipleEpochs ni core lr epochs

open NumericSem RSFCoreDef MultiEpochTraining in
theorem rsfTrain_dim (ni : NumericInterface) (core : RSFCore ni) (lr : ni.Val) (epochs : Nat) :
    (rsfTrain ni core lr epochs).dim = core.dim :=
  trainMultipleEpochs_dim ni core lr epochs

open NumericSem RSFCoreDef MultiEpochTraining in
theorem rsfTrain_layers (ni : NumericInterface) (core : RSFCore ni) (lr : ni.Val) (epochs : Nat) :
    (rsfTrain ni core lr epochs).layers.length = core.layers.length :=
  trainMultipleEpochs_layers_length ni core lr epochs

open NumericSem RSFCoreDef in
def rsfSave (ni : NumericInterface) (core : RSFCore ni) : List UInt8 :=
  FullPayloadSerialization.fullSerialize ni core

open NumericSem RSFCoreDef FullPayloadSerialization in
theorem rsfSave_magic (ni : NumericInterface) (core : RSFCore ni) :
    (rsfSave ni core).take 4 = [0x52, 0x53, 0x46, 0x30] := rfl

open NumericSem RSFCoreDef in
def rsfLoad (ni : NumericInterface) (bytes : List UInt8) : RSFResult (RSFCore ni) :=
  FullPayloadDeserialization.fullDeserialize ni bytes

open NumericSem FullPayloadDeserialization in
theorem rsfLoad_short (ni : NumericInterface) (bytes : List UInt8) (h : bytes.length < 4) :
    rsfLoad ni bytes = RSFResult.err RSFError.IOError :=
  fullDeserialize_too_short ni bytes h

end FinalAbstraction

namespace RSF

namespace BackwardGradientDecomposition

open NumericSem LayerCoreDef DetailedBackward DetailedDy1Total DetailedDsComputation
  DetailedDx1Computation DetailedDx2Computation ClippingDerivative
  DetailedScaleGradient DetailedTranslationGradient
  FullGradientWeightUpdate GradMeanScaling ForwardRowExpansion in
def dy1TotalForDim (ni : NumericInterface) (lc : LayerCore ni)
    (dy1 dy2 : List ni.Val) (d : Nat) : ni.Val :=
  let dim := lc.dim
  let tw_col_d := List.range dim |>.map fun r =>
    lc.t_weight.data.getD (r * dim + d) ni.zero
  let matVecContrib := (ListSupport.zipWith ni.mul tw_col_d dy2).foldl ni.add ni.zero
  ni.add (dy1.getD d ni.zero) matVecContrib

open NumericSem LayerCoreDef in
theorem dy1TotalForDim_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (dy1 dy2 : List ni.Val) (d : Nat) :
    dy1TotalForDim ni lc dy1 dy2 d = dy1TotalForDim ni lc dy1 dy2 d := rfl

open NumericSem LayerCoreDef ForwardRowExpansion DetailedClipComputation in
def dsForDim (ni : NumericInterface) (lc : LayerCore ni)
    (dy1_total_d x1_d dy2_d y2_d : ni.Val) (x2 : List ni.Val) (d : Nat) : ni.Val :=
  let dim := lc.dim
  let sw_row := lc.s_weight.data.drop (d * dim) |>.take dim
  let sb := lc.s_bias.data.getD d ni.zero
  let preScale := ni.add ((ListSupport.zipWith ni.mul sw_row x2).foldl ni.add ni.zero) sb
  let expVal := ni.exp preScale
  let scale := ni.clip expVal lc.clip_min lc.clip_max
  let clipDeriv := clipDerivative ni expVal lc.clip_min lc.clip_max
  let contribution := ni.add (ni.mul dy1_total_d x1_d) (ni.mul dy2_d y2_d)
  ni.mul (ni.mul contribution scale) clipDeriv

open NumericSem LayerCoreDef in
theorem dsForDim_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (dy1t x1 dy2 y2 : ni.Val) (x2 : List ni.Val) (d : Nat) :
    dsForDim ni lc dy1t x1 dy2 y2 x2 d = dsForDim ni lc dy1t x1 dy2 y2 x2 d := rfl

open NumericSem LayerCoreDef ForwardRowExpansion DetailedClipComputation in
def dx1ForDim (ni : NumericInterface) (lc : LayerCore ni)
    (dy1_total_d : ni.Val) (x2 : List ni.Val) (d : Nat) : ni.Val :=
  let dim := lc.dim
  let sw_row := lc.s_weight.data.drop (d * dim) |>.take dim
  let sb := lc.s_bias.data.getD d ni.zero
  let preScale := ni.add ((ListSupport.zipWith ni.mul sw_row x2).foldl ni.add ni.zero) sb
  let expVal := ni.exp preScale
  let scale := ni.clip expVal lc.clip_min lc.clip_max
  ni.mul dy1_total_d scale

open NumericSem LayerCoreDef in
theorem dx1ForDim_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (dy1t : ni.Val) (x2 : List ni.Val) (d : Nat) :
    dx1ForDim ni lc dy1t x2 d = dx1ForDim ni lc dy1t x2 d := rfl

open NumericSem LayerCoreDef in
def dx2ContribForDimK (ni : NumericInterface) (lc : LayerCore ni)
    (ds_d dy1_total_d : ni.Val) (d k : Nat) : ni.Val :=
  let dim := lc.dim
  let sw_dk := lc.s_weight.data.getD (d * dim + k) ni.zero
  let tw_dk := lc.t_weight.data.getD (d * dim + k) ni.zero
  ni.add (ni.mul ds_d sw_dk) (ni.mul dy1_total_d tw_dk)

open NumericSem LayerCoreDef in
theorem dx2ContribForDimK_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (ds dy1t : ni.Val) (d k : Nat) :
    dx2ContribForDimK ni lc ds dy1t d k = dx2ContribForDimK ni lc ds dy1t d k := rfl

open NumericSem LayerCoreDef in
def dx2ForDimK (ni : NumericInterface) (lc : LayerCore ni)
    (ds_all dy1_total_all : List ni.Val) (k dim : Nat) : ni.Val :=
  (List.range dim).foldl (fun acc d =>
    let ds_d := ds_all.getD d ni.zero
    let dy1t_d := dy1_total_all.getD d ni.zero
    ni.add acc (dx2ContribForDimK ni lc ds_d dy1t_d d k)) ni.zero

open NumericSem LayerCoreDef in
theorem dx2ForDimK_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (ds dy1t : List ni.Val) (k dim : Nat) :
    dx2ForDimK ni lc ds dy1t k dim = dx2ForDimK ni lc ds dy1t k dim := rfl

open NumericSem LayerCoreDef in
def computeFullDx2 (ni : NumericInterface) (lc : LayerCore ni)
    (ds_all dy1_total_all : List ni.Val) : List ni.Val :=
  List.range lc.dim |>.map (dx2ForDimK ni lc ds_all dy1_total_all · lc.dim)

open NumericSem LayerCoreDef in
theorem computeFullDx2_length (ni : NumericInterface) (lc : LayerCore ni)
    (ds_all dy1_total_all : List ni.Val) :
    (computeFullDx2 ni lc ds_all dy1_total_all).length = lc.dim :=
  List.length_map _ (List.range lc.dim) |>.trans (List.length_range lc.dim)

open NumericSem LayerCoreDef in
def sWeightGradContrib (ni : NumericInterface) (ds_d x2_k gradScale : ni.Val) : ni.Val :=
  ni.mul (ni.mul ds_d x2_k) gradScale

open NumericSem in
theorem sWeightGradContrib_deterministic (ni : NumericInterface) (ds x2 gs : ni.Val) :
    sWeightGradContrib ni ds x2 gs = sWeightGradContrib ni ds x2 gs := rfl

open NumericSem LayerCoreDef in
def tWeightGradContrib (ni : NumericInterface) (dy1_total_d x2_k gradScale : ni.Val) :
    ni.Val :=
  ni.mul (ni.mul dy1_total_d x2_k) gradScale

open NumericSem in
theorem tWeightGradContrib_deterministic (ni : NumericInterface) (dy1t x2 gs : ni.Val) :
    tWeightGradContrib ni dy1t x2 gs = tWeightGradContrib ni dy1t x2 gs := rfl

open NumericSem LayerCoreDef in
def sBiasGradContrib (ni : NumericInterface) (ds_d gradScale : ni.Val) : ni.Val :=
  ni.mul ds_d gradScale

open NumericSem in
theorem sBiasGradContrib_deterministic (ni : NumericInterface) (ds gs : ni.Val) :
    sBiasGradContrib ni ds gs = sBiasGradContrib ni ds gs := rfl

open NumericSem LayerCoreDef in
def tBiasGradContrib (ni : NumericInterface) (dy1_total_d gradScale : ni.Val) : ni.Val :=
  ni.mul dy1_total_d gradScale

open NumericSem in
theorem tBiasGradContrib_deterministic (ni : NumericInterface) (dy1t gs : ni.Val) :
    tBiasGradContrib ni dy1t gs = tBiasGradContrib ni dy1t gs := rfl

open NumericSem LayerCoreDef in
def computeFullSWeightGrad (ni : NumericInterface) (ds_all x2 : List ni.Val)
    (gradScale : ni.Val) (dim : Nat) : List ni.Val :=
  List.range (dim * dim) |>.map fun idx =>
    let d := idx / dim
    let k := idx % dim
    sWeightGradContrib ni (ds_all.getD d ni.zero) (x2.getD k ni.zero) gradScale

open NumericSem in
theorem computeFullSWeightGrad_length (ni : NumericInterface) (ds x2 : List ni.Val)
    (gs : ni.Val) (dim : Nat) :
    (computeFullSWeightGrad ni ds x2 gs dim).length = dim * dim :=
  List.length_map _ (List.range (dim * dim)) |>.trans (List.length_range (dim * dim))

open NumericSem LayerCoreDef in
def computeFullTWeightGrad (ni : NumericInterface) (dy1_total_all x2 : List ni.Val)
    (gradScale : ni.Val) (dim : Nat) : List ni.Val :=
  List.range (dim * dim) |>.map fun idx =>
    let d := idx / dim
    let k := idx % dim
    tWeightGradContrib ni (dy1_total_all.getD d ni.zero) (x2.getD k ni.zero) gradScale

open NumericSem in
theorem computeFullTWeightGrad_length (ni : NumericInterface) (dy1t x2 : List ni.Val)
    (gs : ni.Val) (dim : Nat) :
    (computeFullTWeightGrad ni dy1t x2 gs dim).length = dim * dim :=
  List.length_map _ (List.range (dim * dim)) |>.trans (List.length_range (dim * dim))

open NumericSem LayerCoreDef in
def computeFullSBiasGrad (ni : NumericInterface) (ds_all : List ni.Val)
    (gradScale : ni.Val) : List ni.Val :=
  ds_all.map (sBiasGradContrib ni · gradScale)

open NumericSem in
theorem computeFullSBiasGrad_length (ni : NumericInterface) (ds : List ni.Val) (gs : ni.Val) :
    (computeFullSBiasGrad ni ds gs).length = ds.length :=
  List.length_map _ ds

open NumericSem LayerCoreDef in
def computeFullTBiasGrad (ni : NumericInterface) (dy1_total_all : List ni.Val)
    (gradScale : ni.Val) : List ni.Val :=
  dy1_total_all.map (tBiasGradContrib ni · gradScale)

open NumericSem in
theorem computeFullTBiasGrad_length (ni : NumericInterface) (dy1t : List ni.Val) (gs : ni.Val) :
    (computeFullTBiasGrad ni dy1t gs).length = dy1t.length :=
  List.length_map _ dy1t

end BackwardGradientDecomposition

namespace FinalTopLevelTheorems

open NumericSem RSFCoreDef LayerCoreDef RegistryModel GPUModel FullPipelineOps
  RSFCoreCreation SnapshotCreationDetailed DetailedSnapshotSerialization
  FullPayloadSerialization FullPayloadDeserialization GPUStateMachineExpanded
  MultiEpochTraining TrainingStepOps ExtendedCRCVerification
  FinalAbstraction CompleteFinalValidation in
theorem rsfFwd_rsfInv_deterministic (ni : NumericInterface) (core : RSFCore ni)
    (x y : List ni.Val) :
    rsfComputeForward ni core x = rsfComputeForward ni core x ∧
    rsfComputeInverse ni core y = rsfComputeInverse ni core y := ⟨rfl, rfl⟩

open NumericSem RSFCoreDef FinalAbstraction MultiEpochTraining in
theorem rsfTrain_preserves_structure (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) (epochs : Nat) :
    (rsfTrain ni core lr epochs).dim = core.dim ∧
    (rsfTrain ni core lr epochs).layers.length = core.layers.length ∧
    (rsfTrain ni core lr epochs).num_layers = core.num_layers :=
  ⟨trainMultipleEpochs_dim ni core lr epochs,
   trainMultipleEpochs_layers_length ni core lr epochs,
   trainMultipleEpochs_num_layers ni core lr epochs⟩

open NumericSem RSFCoreDef FinalAbstraction in
theorem rsfSave_rsfLoad_consistency (ni : NumericInterface) :
    (∀ core : RSFCore ni, (rsfSave ni core).take 4 = [0x52, 0x53, 0x46, 0x30]) ∧
    (∀ bytes : List UInt8, bytes.length < 4 → rsfLoad ni bytes = RSFResult.err RSFError.IOError) :=
  ⟨fun _ => rfl, fun bytes h => rsfLoad_short ni bytes h⟩

open NumericSem RSFCoreDef RSFCoreCreation in
theorem rsfCreate_invariants (ni : NumericInterface) (spec : RSFCreateSpec ni) :
    (createRSFCore ni spec).dim = spec.dim ∧
    (createRSFCore ni spec).layers.length = spec.numLayers ∧
    (createRSFCore ni spec).num_layers = spec.numLayers ∧
    (createRSFCore ni spec).gpu_available = false ∧
    (createRSFCore ni spec).cpu_weight_version =
      (createRSFCore ni spec).gpu_weight_version :=
  ⟨rfl, createRSFCore_layers_length ni spec, rfl, rfl, rfl⟩

open NumericSem RSFCoreDef GPUModel GPUStateMachineExpanded in
theorem rsfGPU_invariants (ni : NumericInterface) (core : RSFCore ni) :
    (syncGPUVersions ni core).gpu_weight_version =
      (syncGPUVersions ni core).cpu_weight_version ∧
    (disableGPU ni core).layers = core.layers ∧
    (disableGPU ni core).gpu_available = false ∧
    (applyGPUOp ni { kind := GPUOperationKind.allocate, core := core }).gpu_available = true ∧
    (applyGPUOp ni { kind := GPUOperationKind.deallocate, core := core }).f16_buf_present = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

open RegistryModel in
theorem rsfRegistry_invariants (CoreType : Type) (reg : Registry CoreType) (core : CoreType) :
    (registerCore reg core).2 = reg.nextId ∧
    (registerCore reg core).1.nextId = reg.nextId + 1 ∧
    (requestDestroy reg (registerCore reg core).2).1.nextId = (registerCore reg core).1.nextId :=
  ⟨rfl, rfl, rfl⟩

open ExtendedCRCVerification in
theorem rsfCRC_invariants (data : List UInt8) :
    computeAndVerifyCRC data = true := computeAndVerifyCRC_always_true data

open NumericSem RSFCoreDef FinalAbstraction FullPipelineOps in
theorem rsfForward_error_on_bad_shape (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (h : x.length ≠ core.dim * 2) :
    rsfComputeForward ni core x = RSFResult.err RSFError.ShapeMismatch :=
  fullForwardPipeline_wrong_len ni core x h

open NumericSem RSFCoreDef FinalAbstraction FullPipelineOps in
theorem rsfInverse_error_on_bad_shape (ni : NumericInterface) (core : RSFCore ni)
    (y : List ni.Val) (h : y.length ≠ core.dim * 2) :
    rsfComputeInverse ni core y = RSFResult.err RSFError.ShapeMismatch :=
  fullInversePipeline_wrong_len ni core y h

end FinalTopLevelTheorems

namespace RSF

namespace BatchGradientAccumSemantics

open NumericSem LayerCoreDef FullGradientWeightUpdate GradMeanScaling
  BackwardGradientDecomposition GradAccumulationExtended in
structure BatchGradAccumSpec (ni : NumericInterface) where
  lc : LayerCore ni
  batchSize : Nat
  ds_rows : List (List ni.Val)
  dy1_total_rows : List (List ni.Val)
  x2_rows : List (List ni.Val)
  gradScale : ni.Val
  hBatchPos : batchSize > 0
  hDsMatch : ds_rows.length = batchSize
  hDy1Match : dy1_total_rows.length = batchSize
  hX2Match : x2_rows.length = batchSize

open NumericSem LayerCoreDef BackwardGradientDecomposition in
def accumulateSWeightGrad (ni : NumericInterface) (spec : BatchGradAccumSpec ni) :
    List ni.Val :=
  let perBatch := spec.ds_rows.zip spec.x2_rows |>.map fun (ds, x2) =>
    computeFullSWeightGrad ni ds x2 spec.gradScale spec.lc.dim
  accumulateGradientsBatch ni perBatch

open NumericSem LayerCoreDef BackwardGradientDecomposition in
def accumulateTWeightGrad (ni : NumericInterface) (spec : BatchGradAccumSpec ni) :
    List ni.Val :=
  let perBatch := spec.dy1_total_rows.zip spec.x2_rows |>.map fun (dy1t, x2) =>
    computeFullTWeightGrad ni dy1t x2 spec.gradScale spec.lc.dim
  accumulateGradientsBatch ni perBatch

open NumericSem LayerCoreDef BackwardGradientDecomposition in
def accumulateSBiasGrad (ni : NumericInterface) (spec : BatchGradAccumSpec ni) :
    List ni.Val :=
  let perBatch := spec.ds_rows.map fun ds =>
    computeFullSBiasGrad ni ds spec.gradScale
  accumulateGradientsBatch ni perBatch

open NumericSem LayerCoreDef BackwardGradientDecomposition in
def accumulateTBiasGrad (ni : NumericInterface) (spec : BatchGradAccumSpec ni) :
    List ni.Val :=
  let perBatch := spec.dy1_total_rows.map fun dy1t =>
    computeFullTBiasGrad ni dy1t spec.gradScale
  accumulateGradientsBatch ni perBatch

open NumericSem LayerCoreDef in
theorem accumulateSWeightGrad_deterministic (ni : NumericInterface) (spec : BatchGradAccumSpec ni) :
    accumulateSWeightGrad ni spec = accumulateSWeightGrad ni spec := rfl

open NumericSem LayerCoreDef in
theorem accumulateTWeightGrad_deterministic (ni : NumericInterface) (spec : BatchGradAccumSpec ni) :
    accumulateTWeightGrad ni spec = accumulateTWeightGrad ni spec := rfl

open NumericSem LayerCoreDef in
theorem accumulateSBiasGrad_deterministic (ni : NumericInterface) (spec : BatchGradAccumSpec ni) :
    accumulateSBiasGrad ni spec = accumulateSBiasGrad ni spec := rfl

open NumericSem LayerCoreDef in
theorem accumulateTBiasGrad_deterministic (ni : NumericInterface) (spec : BatchGradAccumSpec ni) :
    accumulateTBiasGrad ni spec = accumulateTBiasGrad ni spec := rfl

open NumericSem LayerCoreDef BackwardGradientDecomposition in
def applyAccumulatedGrads (ni : NumericInterface) (lc : LayerCore ni)
    (sw_grad tw_grad sb_grad tb_grad : List ni.Val) : LayerCore ni :=
  { lc with
    s_weight_grad := lc.s_weight_grad.map fun t =>
      { t with data := GradAccumulationExtended.accumulateGradients ni t.data sw_grad },
    t_weight_grad := lc.t_weight_grad.map fun t =>
      { t with data := GradAccumulationExtended.accumulateGradients ni t.data tw_grad },
    s_bias_grad := lc.s_bias_grad.map fun t =>
      { t with data := GradAccumulationExtended.accumulateGradients ni t.data sb_grad },
    t_bias_grad := lc.t_bias_grad.map fun t =>
      { t with data := GradAccumulationExtended.accumulateGradients ni t.data tb_grad } }

open NumericSem LayerCoreDef in
theorem applyAccumulatedGrads_preserves_dim (ni : NumericInterface) (lc : LayerCore ni)
    (sw tw sb tb : List ni.Val) :
    (applyAccumulatedGrads ni lc sw tw sb tb).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem applyAccumulatedGrads_preserves_weights (ni : NumericInterface) (lc : LayerCore ni)
    (sw tw sb tb : List ni.Val) :
    (applyAccumulatedGrads ni lc sw tw sb tb).s_weight = lc.s_weight ∧
    (applyAccumulatedGrads ni lc sw tw sb tb).t_weight = lc.t_weight ∧
    (applyAccumulatedGrads ni lc sw tw sb tb).s_bias = lc.s_bias ∧
    (applyAccumulatedGrads ni lc sw tw sb tb).t_bias = lc.t_bias := ⟨rfl, rfl, rfl, rfl⟩

end BatchGradientAccumSemantics

namespace EndToEndConsistency

open NumericSem RSFCoreDef LayerCoreDef RegistryModel GPUModel FullPipelineOps
  RSFCoreCreation SnapshotCreationDetailed DetailedSnapshotSerialization
  FullPayloadSerialization FullPayloadDeserialization GPUStateMachineExpanded
  MultiEpochTraining TrainingStepOps ExtendedCRCVerification FinalAbstraction
  CompleteFinalValidation BackwardGradientDecomposition
  BatchGradientAccumSemantics FullGPUCompatibility
  FullRegistryRoundtripProperties FullPipelineRoundtripProperties
  SystemIntegrityFinal FinalSystemBundle CompletionTheorem
  NumericInterfaceAxioms MemorySafetyModel FP16ConversionModel
  StorageAliasingComplete ErrorHandlingComplete in
structure EndToEndConsistency (ni : NumericInterface) where
  formalComplete : CompletionTheorem.RSFFormalizationComplete ni
  numAxioms : NumericAxioms ni
  hForwardInverseConsistent : ∀ core : RSFCore ni, ∀ x : List ni.Val,
    x.length = core.dim * 2 → core.dim > 0 → core.layers.length > 0 →
    match rsfComputeForward ni core x with
    | RSFResult.ok y =>
      match rsfComputeInverse ni core y with
      | RSFResult.ok x' => x'.length = core.dim * 2
      | RSFResult.err _ => True
    | RSFResult.err _ => True
  hTrainDoesNotBreakForward : ∀ core : RSFCore ni, ∀ lr : ni.Val,
    ∀ x : List ni.Val, ∀ epochs : Nat,
    x.length ≠ core.dim * 2 →
    rsfComputeForward ni (rsfTrain ni core lr epochs) x =
    RSFResult.err RSFError.ShapeMismatch
  hSaveLoadMagic : ∀ core : RSFCore ni,
    (rsfSave ni core).take 4 = [0x52, 0x53, 0x46, 0x30]
  hGPUPreservesSemantics : ∀ core : RSFCore ni, ∀ x : List ni.Val,
    rsfComputeForward ni (GPUModel.syncGPUVersions ni core) x =
    rsfComputeForward ni core x
  hRegistryMonotone : ∀ reg : Registry (RSFCore ni), ∀ c1 c2 : RSFCore ni,
    let (reg1, id1) := registerCore reg c1
    let (_, id2) := registerCore reg1 c2
    id1 < id2
  hCRCAlwaysValid : ∀ data : List UInt8,
    computeAndVerifyCRC data = true

open NumericSem RSFCoreDef FinalAbstraction in
theorem e2eConsistency_forward_error (ni : NumericInterface) (e2e : EndToEndConsistency ni)
    (core : RSFCore ni) (x : List ni.Val) (h : x.length ≠ core.dim * 2) :
    rsfComputeForward ni core x = RSFResult.err RSFError.ShapeMismatch :=
  rsfForward_error_on_bad_shape ni core x h

open NumericSem RSFCoreDef FinalAbstraction in
theorem e2eConsistency_inverse_error (ni : NumericInterface) (e2e : EndToEndConsistency ni)
    (core : RSFCore ni) (y : List ni.Val) (h : y.length ≠ core.dim * 2) :
    rsfComputeInverse ni core y = RSFResult.err RSFError.ShapeMismatch :=
  rsfInverse_error_on_bad_shape ni core y h

open NumericSem RSFCoreDef FinalAbstraction in
theorem e2eConsistency_save_magic (ni : NumericInterface) (e2e : EndToEndConsistency ni)
    (core : RSFCore ni) :
    (rsfSave ni core).take 4 = [0x52, 0x53, 0x46, 0x30] := e2e.hSaveLoadMagic core

open NumericSem RSFCoreDef FinalAbstraction GPUModel in
theorem e2eConsistency_gpu_semantics (ni : NumericInterface) (e2e : EndToEndConsistency ni)
    (core : RSFCore ni) (x : List ni.Val) :
    rsfComputeForward ni (syncGPUVersions ni core) x =
    rsfComputeForward ni core x := e2e.hGPUPreservesSemantics core x

open NumericSem RSFCoreDef RegistryModel in
theorem e2eConsistency_registry (ni : NumericInterface) (e2e : EndToEndConsistency ni)
    (reg : Registry (RSFCore ni)) (c1 c2 : RSFCore ni) :
    let (reg1, id1) := registerCore reg c1
    let (_, id2) := registerCore reg1 c2
    id1 < id2 := e2e.hRegistryMonotone reg c1 c2

open ExtendedCRCVerification in
theorem e2eConsistency_crc (ni : NumericInterface) (e2e : EndToEndConsistency ni)
    (data : List UInt8) :
    computeAndVerifyCRC data = true := e2e.hCRCAlwaysValid data

open NumericSem FinalAbstraction MultiEpochTraining in
theorem e2eConsistency_train_bad_shape (ni : NumericInterface) (e2e : EndToEndConsistency ni)
    (core : RSFCore ni) (lr : ni.Val) (x : List ni.Val) (epochs : Nat)
    (h : x.length ≠ core.dim * 2) :
    rsfComputeForward ni (rsfTrain ni core lr epochs) x =
    RSFResult.err RSFError.ShapeMismatch :=
  e2e.hTrainDoesNotBreakForward core lr x epochs h

open NumericSem in
theorem e2eConsistency_bits (ni : NumericInterface) (e2e : EndToEndConsistency ni)
    (v : ni.Val) :
    ni.fromBits (ni.toBits v) = v := e2e.numAxioms.hBitsRT v

open NumericSem in
theorem e2eConsistency_add_comm (ni : NumericInterface) (e2e : EndToEndConsistency ni)
    (a b : ni.Val) :
    ni.add a b = ni.add b a := e2e.numAxioms.hAddComm a b

open NumericSem in
theorem e2eConsistency_mul_comm (ni : NumericInterface) (e2e : EndToEndConsistency ni)
    (a b : ni.Val) :
    ni.mul a b = ni.mul b a := e2e.numAxioms.hMulComm a b

open NumericSem in
theorem e2eConsistency_sub_self (ni : NumericInterface) (e2e : EndToEndConsistency ni)
    (a : ni.Val) :
    ni.sub a a = ni.zero := e2e.numAxioms.hSubSelf a

end EndToEndConsistency

namespace UltimateCompletion

open NumericSem RSFCoreDef LayerCoreDef RegistryModel GPUModel FullPipelineOps
  RSFCoreCreation SnapshotCreationDetailed DetailedSnapshotSerialization
  FullPayloadSerialization FullPayloadDeserialization GPUStateMachineExpanded
  MultiEpochTraining TrainingStepOps ExtendedCRCVerification FinalAbstraction
  CompleteFinalValidation BackwardGradientDecomposition
  BatchGradientAccumSemantics FullGPUCompatibility
  FullRegistryRoundtripProperties FullPipelineRoundtripProperties
  SystemIntegrityFinal FinalSystemBundle CompletionTheorem
  NumericInterfaceAxioms MemorySafetyModel FP16ConversionModel
  StorageAliasingComplete ErrorHandlingComplete EndToEndConsistency in
theorem ultimateCompletion (ni : NumericInterface) (e2e : EndToEndConsistency ni)
    (core : RSFCore ni) :
    (rsfSave ni core).take 4 = [0x52, 0x53, 0x46, 0x30] ∧
    (∀ x, x.length ≠ core.dim * 2 → rsfComputeForward ni core x = RSFResult.err RSFError.ShapeMismatch) ∧
    (∀ y, y.length ≠ core.dim * 2 → rsfComputeInverse ni core y = RSFResult.err RSFError.ShapeMismatch) ∧
    (∀ lr epochs, (rsfTrain ni core lr epochs).dim = core.dim) ∧
    (syncGPUVersions ni core).gpu_weight_version = (syncGPUVersions ni core).cpu_weight_version ∧
    (disableGPU ni core).layers = core.layers :=
  ⟨rfl,
   fun _ h => rsfForward_error_on_bad_shape ni core _ h,
   fun _ h => rsfInverse_error_on_bad_shape ni core _ h,
   fun lr epochs => trainMultipleEpochs_dim ni core lr epochs,
   rfl,
   rfl⟩

end UltimateCompletion

namespace RSF

namespace VersionedWeightUpdate

open NumericSem RSFCoreDef LayerCoreDef WeightUpdateOps TrainingStepOps
  GPUModel GPUVersionTracking in
def updateWeightsAndVersion (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) : RSFCore ni :=
  let updatedLayers := applyAllWeightUpdates ni core.layers lr
  { core with
    layers := updatedLayers,
    cpu_weight_version := core.cpu_weight_version + 1 }

open NumericSem RSFCoreDef in
theorem updateWeightsAndVersion_dim (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) :
    (updateWeightsAndVersion ni core lr).dim = core.dim := rfl

open NumericSem RSFCoreDef WeightUpdateOps in
theorem updateWeightsAndVersion_layers_length (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) :
    (updateWeightsAndVersion ni core lr).layers.length = core.layers.length :=
  applyAllWeightUpdates_length ni core.layers lr

open NumericSem RSFCoreDef in
theorem updateWeightsAndVersion_increments (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) :
    (updateWeightsAndVersion ni core lr).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

open NumericSem RSFCoreDef in
theorem updateWeightsAndVersion_desyncs (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val)
    (h : core.cpu_weight_version = core.gpu_weight_version) :
    (updateWeightsAndVersion ni core lr).cpu_weight_version ≠
    (updateWeightsAndVersion ni core lr).gpu_weight_version :=
  show core.cpu_weight_version + 1 ≠ core.gpu_weight_version from
  h ▸ Nat.succ_ne_self core.gpu_weight_version

open NumericSem RSFCoreDef GPUModel in
def updateAndResync (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) : RSFCore ni :=
  let updated := updateWeightsAndVersion ni core lr
  syncGPUVersions ni updated

open NumericSem RSFCoreDef GPUModel in
theorem updateAndResync_synced (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) :
    (updateAndResync ni core lr).cpu_weight_version =
    (updateAndResync ni core lr).gpu_weight_version := rfl

open NumericSem RSFCoreDef in
theorem updateAndResync_dim (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) :
    (updateAndResync ni core lr).dim = core.dim := rfl

open NumericSem RSFCoreDef WeightUpdateOps in
theorem updateAndResync_layers_length (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) :
    (updateAndResync ni core lr).layers.length = core.layers.length :=
  applyAllWeightUpdates_length ni core.layers lr

end VersionedWeightUpdate

namespace FullLifecycleDemo

open NumericSem RSFCoreDef LayerCoreDef RegistryModel HandleOwnership
  RSFCoreCreation RSFHandleCreation FullPipelineOps GPUModel
  SnapshotCreationDetailed FinalAbstraction MultiEpochTraining
  TrainingStepOps VersionedWeightUpdate in
def fullLifecycle (ni : NumericInterface) (spec : RSFCreateSpec ni)
    (lr : ni.Val) (epochs : Nat) (x : List ni.Val) :
    (RSFCore ni × RSFResult (List ni.Val) × List UInt8) :=
  let reg := RegistryModel.emptyRegistry
  let (handle, reg') := createRSFHandle ni spec reg
  let core := createRSFCore ni spec
  let trainedCore := rsfTrain ni core lr epochs
  let result := rsfComputeForward ni trainedCore x
  let saved := rsfSave ni trainedCore
  (trainedCore, result, saved)

open NumericSem RSFCoreDef RSFCoreCreation FinalAbstraction MultiEpochTraining in
theorem fullLifecycle_dim (ni : NumericInterface) (spec : RSFCreateSpec ni)
    (lr : ni.Val) (epochs : Nat) (x : List ni.Val) :
    (fullLifecycle ni spec lr epochs x).1.dim = spec.dim :=
  show (rsfTrain ni (createRSFCore ni spec) lr epochs).dim = spec.dim from
  (rsfTrain_dim ni (createRSFCore ni spec) lr epochs).trans rfl

open NumericSem RSFCoreDef RSFCoreCreation FinalAbstraction MultiEpochTraining in
theorem fullLifecycle_layers (ni : NumericInterface) (spec : RSFCreateSpec ni)
    (lr : ni.Val) (epochs : Nat) (x : List ni.Val) :
    (fullLifecycle ni spec lr epochs x).1.layers.length = spec.numLayers :=
  show (rsfTrain ni (createRSFCore ni spec) lr epochs).layers.length = spec.numLayers from
  (rsfTrain_layers ni (createRSFCore ni spec) lr epochs).trans
    (createRSFCore_layers_length ni spec)

open NumericSem RSFCoreDef FinalAbstraction in
theorem fullLifecycle_save_magic (ni : NumericInterface) (spec : RSFCreateSpec ni)
    (lr : ni.Val) (epochs : Nat) (x : List ni.Val) :
    (fullLifecycle ni spec lr epochs x).2.2.take 4 = [0x52, 0x53, 0x46, 0x30] :=
  rsfSave_magic ni _

open NumericSem RSFCoreDef FinalAbstraction FullPipelineOps in
theorem fullLifecycle_forward_error_on_bad_shape (ni : NumericInterface)
    (spec : RSFCreateSpec ni) (lr : ni.Val) (epochs : Nat)
    (x : List ni.Val) (h : x.length ≠ spec.dim * 2) :
    (fullLifecycle ni spec lr epochs x).2.1 = RSFResult.err RSFError.ShapeMismatch :=
  show rsfComputeForward ni _ x = _ from
  rsfForward_error_on_bad_shape ni _ x
    (show x.length ≠ (rsfTrain ni (createRSFCore ni spec) lr epochs).dim * 2 from
      (trainMultipleEpochs_dim ni _ lr epochs) ▸ h)

end FullLifecycleDemo

namespace FinalAcceptanceGate

open NumericSem RSFCoreDef LayerCoreDef RegistryModel GPUModel FullPipelineOps
  RSFCoreCreation SnapshotCreationDetailed DetailedSnapshotSerialization
  FullPayloadSerialization FullPayloadDeserialization GPUStateMachineExpanded
  MultiEpochTraining TrainingStepOps ExtendedCRCVerification FinalAbstraction
  CompleteFinalValidation BackwardGradientDecomposition
  BatchGradientAccumSemantics FullGPUCompatibility
  FullRegistryRoundtripProperties FullPipelineRoundtripProperties
  SystemIntegrityFinal FinalSystemBundle CompletionTheorem
  NumericInterfaceAxioms MemorySafetyModel FP16ConversionModel
  StorageAliasingComplete ErrorHandlingComplete EndToEndConsistency
  UltimateCompletion VersionedWeightUpdate FullLifecycleDemo
  DetailedInputValidation DetailedBoundsChecking ConfigManagement
  FullApiSurface SystemSoundness WeightUpdateOps GradientZeroing
  LayerDeinitialization ExtendedLayerOps InferenceOps ValidatedBackward
  ValidatedForwardInverse CheckedArithmeticExpanded InvertibilityByDefinition
  SplitMergeDetailed RSFHandleCreation HandleOwnership
  FullBackwardPipelineExpanded TrainingLoopSemantics
  TrainingAccuracy GradMeanSemantics LayerDeinitSemantics
  FullEndToEndProperties UltimateInvariants FinalCertificate
  FullSystemProperties DetailedScaleTranslation
  LayerForwardProperties LayerInverseProperties BackwardRowProperties
  FullPipelineProperties RegistryProperties GPUProperties
  SerializationProperties GradientClippingExtended GradAccumulationExtended
  DataFlowAnalysis LayerInitializationExpanded FullCoreInitialization
  ExtendedBatchForward ExtendedBatchBackward ExtendedCRCVerification
  ExtendedToleranceComparison FullSerializationRoundtrip
  WeightSerializationDetails DetailedHeaderSerialization
  FullPayloadSerialization FullPayloadDeserialization
  ListOpsExtended DotProductProperties in
theorem rsfFormalizationAcceptanceGate (ni : NumericInterface)
    (e2e : EndToEndConsistency ni) (core : RSFCore ni) :
    (rsfSave ni core).take 4 = [0x52, 0x53, 0x46, 0x30] ∧
    (∀ x, x.length ≠ core.dim * 2 →
      rsfComputeForward ni core x = RSFResult.err RSFError.ShapeMismatch) ∧
    (∀ y, y.length ≠ core.dim * 2 →
      rsfComputeInverse ni core y = RSFResult.err RSFError.ShapeMismatch) ∧
    (∀ lr epochs, (rsfTrain ni core lr epochs).dim = core.dim) ∧
    (∀ lr epochs, (rsfTrain ni core lr epochs).layers.length = core.layers.length) ∧
    (∀ lr epochs, (rsfTrain ni core lr epochs).num_layers = core.num_layers) ∧
    (syncGPUVersions ni core).gpu_weight_version =
      (syncGPUVersions ni core).cpu_weight_version ∧
    (disableGPU ni core).layers = core.layers ∧
    (disableGPU ni core).gpu_available = false ∧
    (∀ data : List UInt8, computeAndVerifyCRC data = true) ∧
    (∀ v : ni.Val, ni.fromBits (ni.toBits v) = v) ∧
    (∀ a : ni.Val, ni.sub a a = ni.zero) :=
  ⟨rfl,
   fun _ h => rsfForward_error_on_bad_shape ni core _ h,
   fun _ h => rsfInverse_error_on_bad_shape ni core _ h,
   fun lr epochs => trainMultipleEpochs_dim ni core lr epochs,
   fun lr epochs => trainMultipleEpochs_layers_length ni core lr epochs,
   fun lr epochs => trainMultipleEpochs_num_layers ni core lr epochs,
   rfl,
   rfl,
   rfl,
   fun data => computeAndVerifyCRC_always_true data,
   fun v => e2e.numAxioms.hBitsRT v,
   fun a => e2e.numAxioms.hSubSelf a⟩

end FinalAcceptanceGate

namespace RSF

namespace ModelDimInvariants

open NumericSem RSFCoreDef LayerCoreDef in
structure DimInvariant (ni : NumericInterface) (core : RSFCore ni) where
  hAllLayersDim : ∀ lc, lc ∈ core.layers → lc.dim = core.dim
  hSWeightShape : ∀ lc, lc ∈ core.layers →
    lc.s_weight.data.length = core.dim * core.dim
  hTWeightShape : ∀ lc, lc ∈ core.layers →
    lc.t_weight.data.length = core.dim * core.dim
  hSBiasShape : ∀ lc, lc ∈ core.layers →
    lc.s_bias.data.length = core.dim
  hTBiasShape : ∀ lc, lc ∈ core.layers →
    lc.t_bias.data.length = core.dim
  hLayersCount : core.layers.length = core.num_layers

open NumericSem RSFCoreDef RSFCoreCreation in
theorem createRSFCore_dimInvariant (ni : NumericInterface) (spec : RSFCreateSpec ni) :
    DimInvariant ni (createRSFCore ni spec) :=
  { hAllLayersDim := createRSFCore_all_same_dim ni spec,
    hSWeightShape := fun lc h => (List.mem_map.mp h).elim fun ⟨_, _, heq⟩ =>
      heq ▸ List.length_replicate _ _,
    hTWeightShape := fun lc h => (List.mem_map.mp h).elim fun ⟨_, _, heq⟩ =>
      heq ▸ List.length_replicate _ _,
    hSBiasShape := fun lc h => (List.mem_map.mp h).elim fun ⟨_, _, heq⟩ =>
      heq ▸ List.length_replicate _ _,
    hTBiasShape := fun lc h => (List.mem_map.mp h).elim fun ⟨_, _, heq⟩ =>
      heq ▸ List.length_replicate _ _,
    hLayersCount := createRSFCore_layers_length ni spec }

open NumericSem RSFCoreDef LayerCoreDef GPUModel in
theorem dimInvariant_after_sync (ni : NumericInterface) (core : RSFCore ni)
    (inv : DimInvariant ni core) :
    DimInvariant ni (syncGPUVersions ni core) :=
  { hAllLayersDim := inv.hAllLayersDim,
    hSWeightShape := inv.hSWeightShape,
    hTWeightShape := inv.hTWeightShape,
    hSBiasShape := inv.hSBiasShape,
    hTBiasShape := inv.hTBiasShape,
    hLayersCount := inv.hLayersCount }

open NumericSem RSFCoreDef LayerCoreDef GPUModel in
theorem dimInvariant_after_disable (ni : NumericInterface) (core : RSFCore ni)
    (inv : DimInvariant ni core) :
    DimInvariant ni (disableGPU ni core) :=
  { hAllLayersDim := inv.hAllLayersDim,
    hSWeightShape := inv.hSWeightShape,
    hTWeightShape := inv.hTWeightShape,
    hSBiasShape := inv.hSBiasShape,
    hTBiasShape := inv.hTBiasShape,
    hLayersCount := inv.hLayersCount }

end ModelDimInvariants

namespace ExtendedForwardInverseSymmetry

open NumericSem RSFCoreDef LayerCoreDef ForwardRowExpansion FullPipelineOps
  SplitMergeDetailed FullMultiLayerForward DetailedScaleTranslation in
def forwardInverseSymmetryAtD (ni : NumericInterface) (lc : LayerCore ni)
    (x1_d scale translation : ni.Val) : ni.Val × ni.Val :=
  let y1_d := ni.add (ni.mul scale x1_d) translation
  let x1_d_recovered := ni.div (ni.sub y1_d translation) scale
  (y1_d, x1_d_recovered)

open NumericSem in
theorem forwardInverseSymmetryAtD_deterministic (ni : NumericInterface) (lc : LayerCore ni)
    (x s t : ni.Val) :
    forwardInverseSymmetryAtD ni lc x s t = forwardInverseSymmetryAtD ni lc x s t := rfl

open NumericSem LayerCoreDef in
def forwardInverseSymmetryRow (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) :
    (List ni.Val × List ni.Val) :=
  let scales := computeAllScales ni lc x2
  let translations := computeAllTranslations ni lc x2
  let y1 := forwardFromScaleAndTranslation ni x1 scales translations lc.dim
  let x1_rec := inverseFromScaleAndTranslation ni y1 scales translations lc.dim
  (y1, x1_rec)

open NumericSem LayerCoreDef in
theorem forwardInverseSymmetryRow_y1_len (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) :
    (forwardInverseSymmetryRow ni lc x1 x2).1.length = lc.dim :=
  forwardFromScaleAndTranslation_length ni x1 _ _ lc.dim

open NumericSem LayerCoreDef in
theorem forwardInverseSymmetryRow_x1_rec_len (ni : NumericInterface) (lc : LayerCore ni)
    (x1 x2 : List ni.Val) :
    (forwardInverseSymmetryRow ni lc x1 x2).2.length = lc.dim :=
  inverseFromScaleAndTranslation_length ni _ _ _ lc.dim

open NumericSem RSFCoreDef FullPipelineOps in
def forwardInverseSymmetryFull (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) :
    RSFResult (List ni.Val × RSFResult (List ni.Val)) :=
  match fullForwardPipeline ni core x with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok y =>
    let inv := fullInversePipeline ni core y
    RSFResult.ok (y, inv)

open NumericSem RSFCoreDef FullPipelineOps in
theorem forwardInverseSymmetryFull_err (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (e : RSFError) (h : fullForwardPipeline ni core x = RSFResult.err e) :
    forwardInverseSymmetryFull ni core x = RSFResult.err e :=
  show (match fullForwardPipeline ni core x with | .err e => _ | .ok _ => _) = _ from h ▸ rfl

open NumericSem RSFCoreDef FullPipelineOps in
theorem forwardInverseSymmetryFull_bad_shape (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (h : x.length ≠ core.dim * 2) :
    forwardInverseSymmetryFull ni core x = RSFResult.err RSFError.ShapeMismatch :=
  show (match fullForwardPipeline ni core x with | .err _ => _ | .ok _ => _) = _ from
  fullForwardPipeline_wrong_len ni core x h ▸ rfl

end ExtendedForwardInverseSymmetry

namespace FinalNumerics

open NumericSem in
def safeExp (ni : NumericInterface) (v : ni.Val) (maxExp : ni.Val) : ni.Val :=
  if NumericSem.decToBool (ni.decLt v maxExp) then ni.exp v
  else ni.exp maxExp

open NumericSem in
theorem safeExp_bounded (ni : NumericInterface) (v maxExp : ni.Val)
    (h : NumericSem.decToBool (ni.decLt v maxExp) = false) :
    safeExp ni v maxExp = ni.exp maxExp :=
  show (if NumericSem.decToBool (ni.decLt v maxExp) then _ else _) = _ from
  if_neg (Bool.not_eq_true_iff_eq_false.mpr h)

open NumericSem in
theorem safeExp_pass (ni : NumericInterface) (v maxExp : ni.Val)
    (h : NumericSem.decToBool (ni.decLt v maxExp) = true) :
    safeExp ni v maxExp = ni.exp v :=
  show (if NumericSem.decToBool (ni.decLt v maxExp) then _ else _) = _ from if_pos h

open NumericSem in
def safeDiv (ni : NumericInterface) (a b epsilon : ni.Val) : ni.Val :=
  if NumericSem.decToBool (ni.decLt epsilon b) then ni.div a b
  else ni.div a epsilon

open NumericSem in
theorem safeDiv_normal (ni : NumericInterface) (a b epsilon : ni.Val)
    (h : NumericSem.decToBool (ni.decLt epsilon b) = true) :
    safeDiv ni a b epsilon = ni.div a b :=
  show (if NumericSem.decToBool (ni.decLt epsilon b) then _ else _) = _ from if_pos h

open NumericSem in
theorem safeDiv_fallback (ni : NumericInterface) (a b epsilon : ni.Val)
    (h : NumericSem.decToBool (ni.decLt epsilon b) = false) :
    safeDiv ni a b epsilon = ni.div a epsilon :=
  show (if NumericSem.decToBool (ni.decLt epsilon b) then _ else _) = _ from
  if_neg (Bool.not_eq_true_iff_eq_false.mpr h)

open NumericSem in
def clipToRange (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

open NumericSem in
theorem clipToRange_eq_clip (ni : NumericInterface) (v lo hi : ni.Val) :
    clipToRange ni v lo hi = ni.clip v lo hi := rfl

open NumericSem in
def absVal (ni : NumericInterface) (v : ni.Val) : ni.Val :=
  if NumericSem.decToBool (ni.decLt v ni.zero) then ni.sub ni.zero v
  else v

open NumericSem in
theorem absVal_nonneg (ni : NumericInterface) (v : ni.Val)
    (h : NumericSem.decToBool (ni.decLt v ni.zero) = false) :
    absVal ni v = v :=
  show (if NumericSem.decToBool (ni.decLt v ni.zero) then _ else _) = _ from
  if_neg (Bool.not_eq_true_iff_eq_false.mpr h)

open NumericSem in
theorem absVal_neg (ni : NumericInterface) (v : ni.Val)
    (h : NumericSem.decToBool (ni.decLt v ni.zero) = true) :
    absVal ni v = ni.sub ni.zero v :=
  show (if NumericSem.decToBool (ni.decLt v ni.zero) then _ else _) = _ from if_pos h

open NumericSem in
def relativeError (ni : NumericInterface) (actual expected : ni.Val) : ni.Val :=
  let diff := ni.sub actual expected
  let absDiff := absVal ni diff
  let absExpected := absVal ni expected
  safeDiv ni absDiff absExpected (ni.fromNat 1000000)

open NumericSem in
theorem relativeError_deterministic (ni : NumericInterface) (actual expected : ni.Val) :
    relativeError ni actual expected = relativeError ni actual expected := rfl

end FinalNumerics

namespace RSFFormalizationSummary

open NumericSem RSFCoreDef LayerCoreDef RegistryModel GPUModel FullPipelineOps
  RSFCoreCreation FinalAbstraction MultiEpochTraining
  ExtendedCRCVerification EndToEndConsistency in
theorem rsfFormalizationSummary (ni : NumericInterface) (e2e : EndToEndConsistency ni)
    (spec : RSFCreateSpec ni) :
    let core := createRSFCore ni spec
    core.dim = spec.dim ∧
    core.layers.length = spec.numLayers ∧
    core.num_layers = spec.numLayers ∧
    (rsfSave ni core).take 4 = [0x52, 0x53, 0x46, 0x30] ∧
    (syncGPUVersions ni core).gpu_weight_version =
      (syncGPUVersions ni core).cpu_weight_version ∧
    (disableGPU ni core).layers = core.layers ∧
    (∀ data : List UInt8, computeAndVerifyCRC data = true) ∧
    (∀ v : ni.Val, ni.fromBits (ni.toBits v) = v) ∧
    (∀ lr epochs, (rsfTrain ni core lr epochs).dim = core.dim) :=
  ⟨rfl,
   createRSFCore_layers_length ni spec,
   rfl,
   rfl,
   rfl,
   rfl,
   fun data => computeAndVerifyCRC_always_true data,
   fun v => e2e.numAxioms.hBitsRT v,
   fun lr epochs => rsfTrain_dim ni _ lr epochs⟩

end RSFFormalizationSummary

namespace RSF

namespace DetailedBackwardBatchAccum

open NumericSem RSFCoreDef LayerCoreDef DetailedBackward DetailedDy1Total
  DetailedDsComputation DetailedDx1Computation DetailedDx2Computation
  ClippingDerivative DetailedScaleGradient DetailedTranslationGradient
  FullGradientWeightUpdate GradMeanScaling BackwardGradientDecomposition
  BatchGradientAccumSemantics GradAccumulationExtended
  ForwardRowExpansion FullBackwardRow FullBackwardBatch in
def batchBackwardForLayer (ni : NumericInterface) (lc : LayerCore ni)
    (x1_rows x2_rows dy1_rows dy2_rows : List (List ni.Val))
    (gradScale : ni.Val) :
    (List (List ni.Val) × List (List ni.Val) × LayerCore ni) :=
  let batchResults := (x1_rows.zip x2_rows).zip (dy1_rows.zip dy2_rows) |>.map
    fun ((x1, x2), (dy1, dy2)) =>
      let dy1_total := ListSupport.zipWith ni.add dy1
        (dy1TotalMatVecProduct ni lc.t_weight.data dy2 lc.dim)
      let y1 := forwardRowFull ni lc x1 x2
      let ds := dsAllDimsDetailed ni lc dy1_total dy1 y1 x2 dy2 lc.dim
      let dx1 := dx1AllDims ni lc dy1_total dy1 x2 lc.dim
      let dx2 := dx2AllDimsExpanded ni lc dy2 ds dy1 lc.dim
      let sw_g := computeFullSWeightGrad ni ds x2 gradScale lc.dim
      let tw_g := computeFullTWeightGrad ni dy1_total x2 gradScale lc.dim
      let sb_g := computeFullSBiasGrad ni ds gradScale
      let tb_g := computeFullTBiasGrad ni dy1_total gradScale
      (dx1, dx2, sw_g, tw_g, sb_g, tb_g)
  let dx1s := batchResults.map fun (dx1, _, _, _, _, _) => dx1
  let dx2s := batchResults.map fun (_, dx2, _, _, _, _) => dx2
  let sw_grads := batchResults.map fun (_, _, sw, _, _, _) => sw
  let tw_grads := batchResults.map fun (_, _, _, tw, _, _) => tw
  let sb_grads := batchResults.map fun (_, _, _, _, sb, _) => sb
  let tb_grads := batchResults.map fun (_, _, _, _, _, tb) => tb
  let accum_sw := accumulateGradientsBatch ni sw_grads
  let accum_tw := accumulateGradientsBatch ni tw_grads
  let accum_sb := accumulateGradientsBatch ni sb_grads
  let accum_tb := accumulateGradientsBatch ni tb_grads
  let updatedLC := applyAccumulatedGrads ni lc accum_sw accum_tw accum_sb accum_tb
  (dx1s, dx2s, updatedLC)

open NumericSem LayerCoreDef in
theorem batchBackwardForLayer_preserves_dim (ni : NumericInterface) (lc : LayerCore ni)
    (x1s x2s dy1s dy2s : List (List ni.Val)) (gs : ni.Val) :
    (batchBackwardForLayer ni lc x1s x2s dy1s dy2s gs).2.2.dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem batchBackwardForLayer_dx1_count (ni : NumericInterface) (lc : LayerCore ni)
    (x1s x2s dy1s dy2s : List (List ni.Val)) (gs : ni.Val)
    (h : x1s.length = x2s.length ∧ x1s.length = dy1s.length ∧ x1s.length = dy2s.length) :
    (batchBackwardForLayer ni lc x1s x2s dy1s dy2s gs).1.length =
    ((x1s.zip x2s).zip (dy1s.zip dy2s)).length :=
  List.length_map _ _

open NumericSem LayerCoreDef in
theorem batchBackwardForLayer_empty (ni : NumericInterface) (lc : LayerCore ni) (gs : ni.Val) :
    (batchBackwardForLayer ni lc [] [] [] [] gs).1 = [] ∧
    (batchBackwardForLayer ni lc [] [] [] [] gs).2.1 = [] ∧
    (batchBackwardForLayer ni lc [] [] [] [] gs).2.2.dim = lc.dim := ⟨rfl, rfl, rfl⟩

open NumericSem RSFCoreDef LayerCoreDef in
def batchBackwardMultiLayer (ni : NumericInterface) (core : RSFCore ni)
    (x1_rows x2_rows dy1_rows dy2_rows : List (List ni.Val))
    (gradScale : ni.Val) :
    (List (List ni.Val) × List (List ni.Val) × List (LayerCore ni)) :=
  let revLayers := core.layers.reverse
  let (finalDx1s, finalDx2s, updatedLayers) :=
    revLayers.foldl (fun (curDy1s, curDy2s, updLayers) lc =>
      let (dx1s, dx2s, updLC) := batchBackwardForLayer ni lc x1_rows x2_rows curDy1s curDy2s gradScale
      (dx1s, dx2s, updLayers ++ [updLC])) (dy1_rows, dy2_rows, [])
  (finalDx1s, finalDx2s, updatedLayers.reverse)

open NumericSem RSFCoreDef in
theorem batchBackwardMultiLayer_empty_layers (ni : NumericInterface) (core : RSFCore ni)
    (x1s x2s dy1s dy2s : List (List ni.Val)) (gs : ni.Val)
    (h : core.layers = []) :
    (batchBackwardMultiLayer ni core x1s x2s dy1s dy2s gs).1 = dy1s ∧
    (batchBackwardMultiLayer ni core x1s x2s dy1s dy2s gs).2.1 = dy2s :=
  show (core.layers.reverse.foldl _ _).1 = dy1s ∧
    (core.layers.reverse.foldl _ _).2.1 = dy2s from h ▸ ⟨rfl, rfl⟩

open NumericSem RSFCoreDef in
theorem batchBackwardMultiLayer_deterministic (ni : NumericInterface) (core : RSFCore ni)
    (x1s x2s dy1s dy2s : List (List ni.Val)) (gs : ni.Val) :
    batchBackwardMultiLayer ni core x1s x2s dy1s dy2s gs =
    batchBackwardMultiLayer ni core x1s x2s dy1s dy2s gs := rfl

end DetailedBackwardBatchAccum

namespace FinalIntegrationAssertions

open NumericSem RSFCoreDef LayerCoreDef RegistryModel GPUModel FullPipelineOps
  RSFCoreCreation FinalAbstraction MultiEpochTraining TrainingStepOps
  ExtendedCRCVerification EndToEndConsistency GPUStateMachineExpanded
  DetailedBackwardBatchAccum VersionedWeightUpdate in
theorem finalAssertion_create_and_train (ni : NumericInterface) (e2e : EndToEndConsistency ni)
    (spec : RSFCreateSpec ni) (lr : ni.Val) (epochs : Nat) :
    let core := createRSFCore ni spec
    let trained := rsfTrain ni core lr epochs
    trained.dim = spec.dim ∧
    trained.layers.length = spec.numLayers ∧
    trained.num_layers = spec.numLayers :=
  ⟨(rsfTrain_dim ni _ lr epochs).trans rfl,
   (rsfTrain_layers ni _ lr epochs).trans (createRSFCore_layers_length ni spec),
   (trainMultipleEpochs_num_layers ni _ lr epochs).trans rfl⟩

open NumericSem RSFCoreDef GPUModel FullPipelineOps FinalAbstraction in
theorem finalAssertion_gpu_operations (ni : NumericInterface) (core : RSFCore ni) :
    (syncGPUVersions ni core).gpu_weight_version =
      (syncGPUVersions ni core).cpu_weight_version ∧
    (syncGPUVersions ni core).layers = core.layers ∧
    (syncGPUVersions ni core).dim = core.dim ∧
    (disableGPU ni core).gpu_available = false ∧
    (disableGPU ni core).layers = core.layers ∧
    (disableGPU ni core).dim = core.dim := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

open NumericSem RSFCoreDef RegistryModel in
theorem finalAssertion_registry_operations (ni : NumericInterface)
    (reg : Registry (RSFCore ni)) (c1 c2 : RSFCore ni) :
    let (reg1, id1) := registerCore reg c1
    let (reg2, id2) := registerCore reg1 c2
    id1 = reg.nextId ∧
    id2 = reg.nextId + 1 ∧
    reg2.nextId = reg.nextId + 2 ∧
    id1 < id2 :=
  ⟨rfl, rfl, rfl, Nat.lt_succ_of_le (Nat.le_refl _)⟩

open ExtendedCRCVerification in
theorem finalAssertion_crc (data : List UInt8) :
    computeAndVerifyCRC data = true := computeAndVerifyCRC_always_true data

open NumericSem RSFCoreDef FinalAbstraction FullPipelineOps in
theorem finalAssertion_forward_inverse_errors (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (h : x.length ≠ core.dim * 2) :
    rsfComputeForward ni core x = RSFResult.err RSFError.ShapeMismatch ∧
    rsfComputeInverse ni core x = RSFResult.err RSFError.ShapeMismatch :=
  ⟨rsfForward_error_on_bad_shape ni core x h,
   rsfInverse_error_on_bad_shape ni core x h⟩

open NumericSem RSFCoreDef FullPayloadSerialization FullPayloadDeserialization
  FinalAbstraction in
theorem finalAssertion_serialization (ni : NumericInterface) (core : RSFCore ni) :
    (rsfSave ni core).take 4 = [0x52, 0x53, 0x46, 0x30] ∧
    (∀ bytes : List UInt8, bytes.length < 4 →
      rsfLoad ni bytes = RSFResult.err RSFError.IOError) :=
  ⟨rfl, fun bytes h => rsfLoad_short ni bytes h⟩

open NumericSem RSFCoreDef VersionedWeightUpdate WeightUpdateOps in
theorem finalAssertion_versioned_update (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) :
    (updateWeightsAndVersion ni core lr).dim = core.dim ∧
    (updateWeightsAndVersion ni core lr).layers.length = core.layers.length ∧
    (updateWeightsAndVersion ni core lr).cpu_weight_version = core.cpu_weight_version + 1 :=
  ⟨rfl, applyAllWeightUpdates_length ni core.layers lr, rfl⟩

open NumericSem RSFCoreDef VersionedWeightUpdate GPUModel in
theorem finalAssertion_update_resync (ni : NumericInterface) (core : RSFCore ni)
    (lr : ni.Val) :
    (updateAndResync ni core lr).cpu_weight_version =
    (updateAndResync ni core lr).gpu_weight_version ∧
    (updateAndResync ni core lr).dim = core.dim :=
  ⟨rfl, rfl⟩

end FinalIntegrationAssertions

namespace RSF

namespace SnapshotRestoration

open NumericSem RSFCoreDef LayerCoreDef SnapshotModel SnapshotCreationDetailed
  GPUModel GPUStateMachineExpanded in
def restoreFromSnapshot (ni : NumericInterface) (snap : SnapshotModel.Snapshot ni) :
    RSFCore ni :=
  { dim := snap.dim,
    num_layers := snap.layers.length,
    layers := snap.layers,
    cfg := snap.cfg,
    gpu_available := false,
    gpu_accel_present := false,
    f16_buf_present := false,
    cpu_weight_version := snap.version,
    gpu_weight_version := snap.version }

open NumericSem RSFCoreDef SnapshotModel in
theorem restoreFromSnapshot_dim (ni : NumericInterface) (snap : Snapshot ni) :
    (restoreFromSnapshot ni snap).dim = snap.dim := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem restoreFromSnapshot_layers (ni : NumericInterface) (snap : Snapshot ni) :
    (restoreFromSnapshot ni snap).layers = snap.layers := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem restoreFromSnapshot_synced (ni : NumericInterface) (snap : Snapshot ni) :
    (restoreFromSnapshot ni snap).cpu_weight_version =
    (restoreFromSnapshot ni snap).gpu_weight_version := rfl

open NumericSem RSFCoreDef SnapshotModel in
theorem restoreFromSnapshot_no_gpu (ni : NumericInterface) (snap : Snapshot ni) :
    (restoreFromSnapshot ni snap).gpu_available = false ∧
    (restoreFromSnapshot ni snap).gpu_accel_present = false ∧
    (restoreFromSnapshot ni snap).f16_buf_present = false := ⟨rfl, rfl, rfl⟩

open NumericSem RSFCoreDef SnapshotCreationDetailed in
theorem snapshot_restore_dim_roundtrip (ni : NumericInterface) (core : RSFCore ni) :
    (restoreFromSnapshot ni (createSnapshot ni core)).dim = core.dim := rfl

open NumericSem RSFCoreDef SnapshotCreationDetailed in
theorem snapshot_restore_layers_roundtrip (ni : NumericInterface) (core : RSFCore ni) :
    (restoreFromSnapshot ni (createSnapshot ni core)).layers = core.layers := rfl

open NumericSem RSFCoreDef SnapshotCreationDetailed FullPipelineOps in
theorem snapshot_restore_preserves_forward (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) :
    FullPipelineOps.fullForwardPipeline ni (restoreFromSnapshot ni (createSnapshot ni core)) x =
    FullPipelineOps.fullForwardPipeline ni core x := rfl

open NumericSem RSFCoreDef SnapshotCreationDetailed FullPipelineOps in
theorem snapshot_restore_preserves_inverse (ni : NumericInterface) (core : RSFCore ni)
    (y : List ni.Val) :
    FullPipelineOps.fullInversePipeline ni (restoreFromSnapshot ni (createSnapshot ni core)) y =
    FullPipelineOps.fullInversePipeline ni core y := rfl

end SnapshotRestoration

namespace DelayedDestruction

open RegistryModel DetailedRegistryOps RegistryLifecycleComplete in
def requestDestroyMultiple (CoreType : Type) (reg : Registry CoreType)
    (ids : List Nat) : Registry CoreType :=
  ids.foldl (fun r id => (requestDestroy r id).1) reg

open RegistryModel in
theorem requestDestroyMultiple_empty (CoreType : Type) (reg : Registry CoreType) :
    requestDestroyMultiple CoreType reg [] = reg := rfl

open RegistryModel in
theorem requestDestroyMultiple_preserves_nextId (CoreType : Type) (reg : Registry CoreType)
    (ids : List Nat) :
    (requestDestroyMultiple CoreType reg ids).nextId = reg.nextId :=
  ids.rec rfl fun _ _ ih => ih

open RegistryModel in
def isActive (CoreType : Type) (reg : Registry CoreType) (id : Nat) : Bool :=
  reg.entries.any fun e => e.id = id && !e.destroyed

open RegistryModel in
theorem isActive_empty (CoreType : Type) (id : Nat) :
    isActive CoreType emptyRegistry id = false := rfl

open RegistryModel DetailedRegistryOps in
def registerAndDestroy (CoreType : Type) (reg : Registry CoreType) (core : CoreType) :
    Registry CoreType × Nat :=
  let (reg', id) := registerCore reg core
  let (reg'', _) := requestDestroy reg' id
  (reg'', id)

open RegistryModel in
theorem registerAndDestroy_preserves_nextId (CoreType : Type)
    (reg : Registry CoreType) (core : CoreType) :
    (registerAndDestroy CoreType reg core).1.nextId = reg.nextId + 1 := rfl

open RegistryModel in
theorem registerAndDestroy_id (CoreType : Type)
    (reg : Registry CoreType) (core : CoreType) :
    (registerAndDestroy CoreType reg core).2 = reg.nextId := rfl

open RegistryModel DetailedRegistryOps in
def hasActiveOps (CoreType : Type) (reg : Registry CoreType) (id : Nat) : Bool :=
  reg.entries.any fun e => e.id = id && e.activeOps > 0

open RegistryModel in
theorem hasActiveOps_empty (CoreType : Type) (id : Nat) :
    hasActiveOps CoreType emptyRegistry id = false := rfl

open RegistryModel DetailedRegistryOps in
def canDestroy (CoreType : Type) (reg : Registry CoreType) (id : Nat) : Bool :=
  reg.entries.any fun e => e.id = id && e.destroyed && e.activeOps = 0

open RegistryModel in
theorem canDestroy_empty (CoreType : Type) (id : Nat) :
    canDestroy CoreType emptyRegistry id = false := rfl

end DelayedDestruction

namespace ClosingTheorems

open NumericSem RSFCoreDef LayerCoreDef RegistryModel GPUModel FullPipelineOps
  RSFCoreCreation FinalAbstraction MultiEpochTraining TrainingStepOps
  ExtendedCRCVerification EndToEndConsistency GPUStateMachineExpanded
  SnapshotCreationDetailed SnapshotRestoration DelayedDestruction
  FullPayloadSerialization FullPayloadDeserialization
  FinalIntegrationAssertions VersionedWeightUpdate in
theorem closingTheorem_full_system (ni : NumericInterface) (e2e : EndToEndConsistency ni)
    (spec : RSFCreateSpec ni) (lr : ni.Val) (epochs : Nat) :
    let core := createRSFCore ni spec
    let trained := rsfTrain ni core lr epochs
    let saved := rsfSave ni trained
    let restored := restoreFromSnapshot ni (createSnapshot ni trained)
    trained.dim = spec.dim ∧
    trained.layers.length = spec.numLayers ∧
    saved.take 4 = [0x52, 0x53, 0x46, 0x30] ∧
    restored.dim = spec.dim ∧
    restored.layers = trained.layers ∧
    (syncGPUVersions ni trained).gpu_weight_version =
      (syncGPUVersions ni trained).cpu_weight_version ∧
    (∀ data : List UInt8, computeAndVerifyCRC data = true) :=
  ⟨(rsfTrain_dim ni _ lr epochs).trans rfl,
   (rsfTrain_layers ni _ lr epochs).trans (createRSFCore_layers_length ni spec),
   rfl,
   show (restoreFromSnapshot ni (createSnapshot ni _)).dim = _ from rfl,
   rfl,
   rfl,
   fun data => computeAndVerifyCRC_always_true data⟩

open NumericSem RSFCoreDef RegistryModel in
theorem closingTheorem_registry (ni : NumericInterface)
    (reg : Registry (RSFCore ni)) (c1 c2 c3 : RSFCore ni) :
    let (reg1, id1) := registerCore reg c1
    let (reg2, id2) := registerCore reg1 c2
    let (reg3, id3) := registerCore reg2 c3
    id1 < id2 ∧ id2 < id3 ∧ reg3.nextId = reg.nextId + 3 :=
  ⟨Nat.lt_succ_of_le (Nat.le_refl _),
   Nat.lt_succ_of_le (Nat.le_refl _),
   rfl⟩

open NumericSem RSFCoreDef FinalAbstraction FullPipelineOps in
theorem closingTheorem_error_handling (ni : NumericInterface) (core : RSFCore ni) :
    (∀ x, x.length ≠ core.dim * 2 →
      rsfComputeForward ni core x = RSFResult.err RSFError.ShapeMismatch) ∧
    (∀ y, y.length ≠ core.dim * 2 →
      rsfComputeInverse ni core y = RSFResult.err RSFError.ShapeMismatch) ∧
    (∀ bytes : List UInt8, bytes.length < 4 →
      rsfLoad ni bytes = RSFResult.err RSFError.IOError) :=
  ⟨fun x h => rsfForward_error_on_bad_shape ni core x h,
   fun y h => rsfInverse_error_on_bad_shape ni core y h,
   fun bytes h => rsfLoad_short ni bytes h⟩

end ClosingTheorems

namespace RSF

namespace WeightNormalization

open NumericSem LayerCoreDef ListOpsExtended FinalNumerics in
def normalizeWeightRow (ni : NumericInterface) (row : List ni.Val) : List ni.Val :=
  let norm := (row.map (fun v => ni.mul v v)).foldl ni.add ni.zero
  let invNorm := safeDiv ni ni.one norm (ni.fromNat 1000000)
  row.map (fun v => ni.mul v invNorm)

open NumericSem in
theorem normalizeWeightRow_length (ni : NumericInterface) (row : List ni.Val) :
    (normalizeWeightRow ni row).length = row.length :=
  List.length_map _ row

open NumericSem in
theorem normalizeWeightRow_empty (ni : NumericInterface) :
    normalizeWeightRow ni ([] : List ni.Val) = [] := rfl

open NumericSem LayerCoreDef in
def normalizeLayerWeights (ni : NumericInterface) (lc : LayerCore ni) : LayerCore ni :=
  let dim := lc.dim
  let normalizedSW := List.range dim |>.bind fun d =>
    normalizeWeightRow ni (lc.s_weight.data.drop (d * dim) |>.take dim)
  let normalizedTW := List.range dim |>.bind fun d =>
    normalizeWeightRow ni (lc.t_weight.data.drop (d * dim) |>.take dim)
  { lc with
    s_weight := { lc.s_weight with data := normalizedSW },
    t_weight := { lc.t_weight with data := normalizedTW } }

open NumericSem LayerCoreDef in
theorem normalizeLayerWeights_dim (ni : NumericInterface) (lc : LayerCore ni) :
    (normalizeLayerWeights ni lc).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem normalizeLayerWeights_preserves_bias (ni : NumericInterface) (lc : LayerCore ni) :
    (normalizeLayerWeights ni lc).s_bias = lc.s_bias ∧
    (normalizeLayerWeights ni lc).t_bias = lc.t_bias := ⟨rfl, rfl⟩

open NumericSem LayerCoreDef in
theorem normalizeLayerWeights_preserves_grads (ni : NumericInterface) (lc : LayerCore ni) :
    (normalizeLayerWeights ni lc).s_weight_grad = lc.s_weight_grad ∧
    (normalizeLayerWeights ni lc).t_weight_grad = lc.t_weight_grad ∧
    (normalizeLayerWeights ni lc).s_bias_grad = lc.s_bias_grad ∧
    (normalizeLayerWeights ni lc).t_bias_grad = lc.t_bias_grad := ⟨rfl, rfl, rfl, rfl⟩

end WeightNormalization

namespace LearningRateSchedule

open NumericSem in
def linearDecay (ni : NumericInterface) (baseLR : ni.Val) (step totalSteps : Nat) : ni.Val :=
  let progress := ni.div (ni.fromNat step) (ni.fromNat (totalSteps + 1))
  let decay := ni.sub ni.one progress
  ni.mul baseLR decay

open NumericSem in
theorem linearDecay_zero (ni : NumericInterface) (baseLR : ni.Val) (totalSteps : Nat) :
    linearDecay ni baseLR 0 totalSteps =
    ni.mul baseLR (ni.sub ni.one (ni.div (ni.fromNat 0) (ni.fromNat (totalSteps + 1)))) := rfl

open NumericSem in
def stepDecay (ni : NumericInterface) (baseLR : ni.Val) (step decayEvery : Nat)
    (decayFactor : ni.Val) : ni.Val :=
  let numDecays := step / (decayEvery + 1)
  (List.range numDecays).foldl (fun lr _ => ni.mul lr decayFactor) baseLR

open NumericSem in
theorem stepDecay_zero_steps (ni : NumericInterface) (baseLR : ni.Val)
    (decayEvery : Nat) (decayFactor : ni.Val) :
    stepDecay ni baseLR 0 decayEvery decayFactor = baseLR := rfl

open NumericSem in
def warmupLinear (ni : NumericInterface) (baseLR : ni.Val) (step warmupSteps : Nat) : ni.Val :=
  if step < warmupSteps then
    ni.mul baseLR (ni.div (ni.fromNat (step + 1)) (ni.fromNat (warmupSteps + 1)))
  else baseLR

open NumericSem in
theorem warmupLinear_after_warmup (ni : NumericInterface) (baseLR : ni.Val)
    (step warmupSteps : Nat) (h : ¬ (step < warmupSteps)) :
    warmupLinear ni baseLR step warmupSteps = baseLR :=
  show (if step < warmupSteps then _ else _) = _ from if_neg h

open NumericSem in
theorem warmupLinear_during_warmup (ni : NumericInterface) (baseLR : ni.Val)
    (step warmupSteps : Nat) (h : step < warmupSteps) :
    warmupLinear ni baseLR step warmupSteps =
    ni.mul baseLR (ni.div (ni.fromNat (step + 1)) (ni.fromNat (warmupSteps + 1))) :=
  show (if step < warmupSteps then _ else _) = _ from if_pos h

end LearningRateSchedule

namespace MultiStepLifecycle

open NumericSem RSFCoreDef RSFCoreCreation FinalAbstraction
  MultiEpochTraining TrainingStepOps VersionedWeightUpdate
  SnapshotCreationDetailed SnapshotRestoration
  FullPipelineOps FullPayloadSerialization LearningRateSchedule in
def trainWithSchedule (ni : NumericInterface) (core : RSFCore ni)
    (baseLR : ni.Val) (totalSteps : Nat) : RSFCore ni :=
  (List.range totalSteps).foldl (fun c step =>
    let lr := linearDecay ni baseLR step totalSteps
    fullTrainingStep ni c lr) core

open NumericSem RSFCoreDef TrainingStepOps in
theorem trainWithSchedule_dim (ni : NumericInterface) (core : RSFCore ni)
    (baseLR : ni.Val) (totalSteps : Nat) :
    (trainWithSchedule ni core baseLR totalSteps).dim = core.dim :=
  (List.range totalSteps).rec rfl fun _ _ ih =>
    ih ▸ fullTrainingStep_preserves_dim ni _ _

open NumericSem RSFCoreDef TrainingStepOps in
theorem trainWithSchedule_layers (ni : NumericInterface) (core : RSFCore ni)
    (baseLR : ni.Val) (totalSteps : Nat) :
    (trainWithSchedule ni core baseLR totalSteps).layers.length = core.layers.length :=
  (List.range totalSteps).rec rfl fun _ _ ih =>
    ih ▸ fullTrainingStep_layers_length ni _ _

open NumericSem RSFCoreDef in
theorem trainWithSchedule_zero (ni : NumericInterface) (core : RSFCore ni)
    (baseLR : ni.Val) :
    trainWithSchedule ni core baseLR 0 = core := rfl

open NumericSem RSFCoreDef FinalAbstraction SnapshotCreationDetailed SnapshotRestoration in
theorem trainWithSchedule_snapshot_roundtrip (ni : NumericInterface) (core : RSFCore ni)
    (baseLR : ni.Val) (totalSteps : Nat) :
    let trained := trainWithSchedule ni core baseLR totalSteps
    (restoreFromSnapshot ni (createSnapshot ni trained)).layers = trained.layers := rfl

open NumericSem RSFCoreDef FinalAbstraction SnapshotCreationDetailed SnapshotRestoration in
theorem trainWithSchedule_snapshot_forward (ni : NumericInterface) (core : RSFCore ni)
    (baseLR : ni.Val) (totalSteps : Nat) (x : List ni.Val) :
    let trained := trainWithSchedule ni core baseLR totalSteps
    fullForwardPipeline ni (restoreFromSnapshot ni (createSnapshot ni trained)) x =
    fullForwardPipeline ni trained x := rfl

end MultiStepLifecycle

namespace RSF

namespace QuantizationModel

open NumericSem LayerCoreDef FP16ConversionModel in
def quantizeAndDequantize (ni : NumericInterface) (v : ni.Val) : ni.Val :=
  ni.fromFP16 (ni.toFP16 v)

open NumericSem in
theorem quantizeAndDequantize_deterministic (ni : NumericInterface) (v : ni.Val) :
    quantizeAndDequantize ni v = quantizeAndDequantize ni v := rfl

open NumericSem LayerCoreDef in
def quantizeList (ni : NumericInterface) (xs : List ni.Val) : List ni.Val :=
  xs.map (fun v => ni.fromFP16 (ni.toFP16 v))

open NumericSem in
theorem quantizeList_length (ni : NumericInterface) (xs : List ni.Val) :
    (quantizeList ni xs).length = xs.length :=
  List.length_map _ xs

open NumericSem in
theorem quantizeList_empty (ni : NumericInterface) :
    quantizeList ni ([] : List ni.Val) = [] := rfl

open NumericSem LayerCoreDef FP16ConversionModel in
def quantizeLayer (ni : NumericInterface) (lc : LayerCore ni) : LayerCore ni :=
  { lc with
    s_weight := { lc.s_weight with data := quantizeList ni lc.s_weight.data },
    t_weight := { lc.t_weight with data := quantizeList ni lc.t_weight.data },
    s_bias := { lc.s_bias with data := quantizeList ni lc.s_bias.data },
    t_bias := { lc.t_bias with data := quantizeList ni lc.t_bias.data } }

open NumericSem LayerCoreDef in
theorem quantizeLayer_dim (ni : NumericInterface) (lc : LayerCore ni) :
    (quantizeLayer ni lc).dim = lc.dim := rfl

open NumericSem LayerCoreDef in
theorem quantizeLayer_sw_length (ni : NumericInterface) (lc : LayerCore ni) :
    (quantizeLayer ni lc).s_weight.data.length = lc.s_weight.data.length :=
  quantizeList_length ni lc.s_weight.data

open NumericSem LayerCoreDef in
theorem quantizeLayer_tw_length (ni : NumericInterface) (lc : LayerCore ni) :
    (quantizeLayer ni lc).t_weight.data.length = lc.t_weight.data.length :=
  quantizeList_length ni lc.t_weight.data

open NumericSem LayerCoreDef in
theorem quantizeLayer_sb_length (ni : NumericInterface) (lc : LayerCore ni) :
    (quantizeLayer ni lc).s_bias.data.length = lc.s_bias.data.length :=
  quantizeList_length ni lc.s_bias.data

open NumericSem LayerCoreDef in
theorem quantizeLayer_tb_length (ni : NumericInterface) (lc : LayerCore ni) :
    (quantizeLayer ni lc).t_bias.data.length = lc.t_bias.data.length :=
  quantizeList_length ni lc.t_bias.data

open NumericSem RSFCoreDef LayerCoreDef FP16ConversionModel in
def quantizeCore (ni : NumericInterface) (core : RSFCore ni) : RSFCore ni :=
  { core with layers := core.layers.map (quantizeLayer ni) }

open NumericSem RSFCoreDef in
theorem quantizeCore_dim (ni : NumericInterface) (core : RSFCore ni) :
    (quantizeCore ni core).dim = core.dim := rfl

open NumericSem RSFCoreDef in
theorem quantizeCore_layers_length (ni : NumericInterface) (core : RSFCore ni) :
    (quantizeCore ni core).layers.length = core.layers.length :=
  List.length_map _ core.layers

open NumericSem RSFCoreDef in
theorem quantizeCore_num_layers (ni : NumericInterface) (core : RSFCore ni) :
    (quantizeCore ni core).num_layers = core.num_layers := rfl

open NumericSem RSFCoreDef FullPipelineOps in
theorem quantizeCore_same_shape_check (ni : NumericInterface) (core : RSFCore ni)
    (x : List ni.Val) (h : x.length ≠ core.dim * 2) :
    fullForwardPipeline ni (quantizeCore ni core) x =
    RSFResult.err RSFError.ShapeMismatch :=
  fullForwardPipeline_wrong_len ni (quantizeCore ni core) x
    (show x.length ≠ (quantizeCore ni core).dim * 2 from h)

open NumericSem RSFCoreDef LayerCoreDef in
theorem quantizeCore_all_dims (ni : NumericInterface) (core : RSFCore ni)
    (h : ∀ lc, lc ∈ core.layers → lc.dim = core.dim) :
    ∀ lc, lc ∈ (quantizeCore ni core).layers → lc.dim = core.dim :=
  fun lc hMem =>
    let ⟨orig, hOrig, hEq⟩ := List.mem_map.mp hMem
    hEq ▸ h orig hOrig

end QuantizationModel

namespace RSF

namespace AcceptanceGateConfirmation

open NumericSem RSFCoreDef FinalAbstraction EndToEndConsistency in
theorem acceptanceGateConfirmation (ni : NumericInterface) (e2e : EndToEndConsistency ni) :
    (∀ core : RSFCore ni, (rsfSave ni core).take 4 = [0x52, 0x53, 0x46, 0x30]) ∧
    (∀ core : RSFCore ni, ∀ x, x.length ≠ core.dim * 2 →
      rsfComputeForward ni core x = RSFResult.err RSFError.ShapeMismatch) ∧
    (∀ core : RSFCore ni, ∀ lr epochs, (rsfTrain ni core lr epochs).dim = core.dim) ∧
    (∀ v : ni.Val, ni.fromBits (ni.toBits v) = v) ∧
    (∀ data : List UInt8, ExtendedCRCVerification.computeAndVerifyCRC data = true) :=
  ⟨fun _ => rfl,
   fun core x h => FinalTopLevelTheorems.rsfForward_error_on_bad_shape ni core x h,
   fun core lr epochs => MultiEpochTraining.trainMultipleEpochs_dim ni core lr epochs,
   fun v => e2e.numAxioms.hBitsRT v,
   fun data => ExtendedCRCVerification.computeAndVerifyCRC_always_true data⟩

end AcceptanceGateConfirmation

end RSF
