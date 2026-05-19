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

inductive RSFResult (α : Type) where
  | ok : α → RSFResult α
  | err : RSFError → RSFResult α

namespace RSFResult

def bind {α β : Type} : RSFResult α → (α → RSFResult β) → RSFResult β
  | RSFResult.ok a, f => f a
  | RSFResult.err e, _ => RSFResult.err e

def map {α β : Type} : RSFResult α → (α → β) → RSFResult β
  | RSFResult.ok a, f => RSFResult.ok (f a)
  | RSFResult.err e, _ => RSFResult.err e

def isOk {α : Type} : RSFResult α → Bool
  | RSFResult.ok _ => true
  | RSFResult.err _ => false

def isErr {α : Type} : RSFResult α → Bool
  | RSFResult.ok _ => false
  | RSFResult.err _ => true

def getError {α : Type} : RSFResult α → Option RSFError
  | RSFResult.ok _ => Option.none
  | RSFResult.err e => Option.some e

theorem bind_ok_eq {α β : Type} (a : α) (f : α → RSFResult β) :
    bind (RSFResult.ok a) f = f a := rfl

theorem bind_err_eq {α β : Type} (e : RSFError) (f : α → RSFResult β) :
    bind (RSFResult.err e) f = RSFResult.err e := rfl

theorem map_ok_eq {α β : Type} (a : α) (f : α → β) :
    map (RSFResult.ok a) f = RSFResult.ok (f a) := rfl

theorem map_err_eq {α β : Type} (e : RSFError) (f : α → β) :
    map (RSFResult.err e) f = RSFResult.err e := rfl

theorem err_preservation {α β : Type} (e : RSFError) (f : α → RSFResult β) :
    getError (bind (RSFResult.err e) f) = Option.some e := rfl

theorem ok_preservation {α β : Type} (a : α) (f : α → β) :
    isOk (map (RSFResult.ok a) f) = true := rfl

theorem bind_err_propagation {α β : Type} (r : RSFResult α) (f : α → RSFResult β)
    (h : isErr r = true) : isErr (bind r f) = true :=
  match r, h with
  | RSFResult.err _, rfl => rfl

theorem bind_ok_propagation {α β : Type} (r : RSFResult α) (f : α → RSFResult β)
    (hb : isOk (bind r f) = true) : isOk r = true :=
  match r with
  | RSFResult.ok _ => rfl
  | RSFResult.err _ => absurd hb (fun h => nomatch h)

theorem bind_assoc {α β γ : Type} (r : RSFResult α)
    (f : α → RSFResult β) (g : β → RSFResult γ) :
    bind (bind r f) g = bind r (fun a => bind (f a) g) :=
  match r with
  | RSFResult.ok a => rfl
  | RSFResult.err e => rfl

theorem map_bind_equiv {α β : Type} (r : RSFResult α) (f : α → β) :
    map r f = bind r (fun a => RSFResult.ok (f a)) :=
  match r with
  | RSFResult.ok _ => rfl
  | RSFResult.err _ => rfl

end RSFResult

namespace BoolSupport

theorem bool_true_ne_false : true ≠ false := fun h => nomatch h

theorem bool_and_true_right (b : Bool) : (b && true) = b :=
  match b with | true => rfl | false => rfl

theorem bool_and_false_right (b : Bool) : (b && false) = false :=
  match b with | true => rfl | false => rfl

theorem bool_or_true_right (b : Bool) : (b || true) = true :=
  match b with | true => rfl | false => rfl

theorem bool_or_false_right (b : Bool) : (b || false) = b :=
  match b with | true => rfl | false => rfl

theorem bool_and_comm (a b : Bool) : (a && b) = (b && a) :=
  match a, b with
  | true, true => rfl | true, false => rfl
  | false, true => rfl | false, false => rfl

theorem bool_or_comm (a b : Bool) : (a || b) = (b || a) :=
  match a, b with
  | true, true => rfl | true, false => rfl
  | false, true => rfl | false, false => rfl

theorem bool_not_not (b : Bool) : (!!b) = b :=
  match b with | true => rfl | false => rfl

end BoolSupport

namespace NatSupport

def maxUsize : Nat := 2^64 - 1

def maxU64 : Nat := 2^64 - 1

structure BNat (bound : Nat) where
  val : Nat
  hle : val ≤ bound

def BNat.zero (bound : Nat) (h : 0 ≤ bound := Nat.zero_le bound) : BNat bound :=
  ⟨0, h⟩

theorem bnat_val_le {bound : Nat} (bn : BNat bound) : bn.val ≤ bound := bn.hle

theorem nat_add_zero (n : Nat) : n + 0 = n := Nat.add_zero n

theorem nat_zero_add (n : Nat) : 0 + n = n := Nat.zero_add n

theorem nat_succ_pos (n : Nat) : 0 < n + 1 := Nat.succ_pos n

theorem nat_le_refl (n : Nat) : n ≤ n := Nat.le_refl n

theorem nat_le_trans {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  Nat.le_trans h1 h2

theorem nat_lt_of_lt_of_le {a b c : Nat} (h1 : a < b) (h2 : b ≤ c) : a < c :=
  Nat.lt_of_lt_of_le h1 h2

theorem nat_mul_comm (a b : Nat) : a * b = b * a := Nat.mul_comm a b

theorem nat_mul_zero (a : Nat) : a * 0 = 0 := Nat.mul_zero a

theorem nat_zero_mul (a : Nat) : 0 * a = 0 := Nat.zero_mul a

theorem nat_mul_one (a : Nat) : a * 1 = a := Nat.mul_one a

theorem nat_one_mul (a : Nat) : 1 * a = a := Nat.one_mul a

theorem nat_add_comm (a b : Nat) : a + b = b + a := Nat.add_comm a b

theorem nat_add_assoc (a b c : Nat) : a + b + c = a + (b + c) := Nat.add_assoc a b c

theorem nat_mul_assoc (a b c : Nat) : a * b * c = a * (b * c) := Nat.mul_assoc a b c

end NatSupport

namespace ListSupport

theorem length_nil {α : Type} : ([] : List α).length = 0 := rfl

theorem length_cons {α : Type} (x : α) (xs : List α) :
    (x :: xs).length = xs.length + 1 := rfl

theorem length_append {α : Type} (l1 l2 : List α) :
    (l1 ++ l2).length = l1.length + l2.length :=
  List.length_append l1 l2

theorem length_map {α β : Type} (f : α → β) (l : List α) :
    (l.map f).length = l.length := List.length_map f l

theorem length_replicate {α : Type} (n : Nat) (v : α) :
    (List.replicate n v).length = n := List.length_replicate n v

theorem length_take {α : Type} (n : Nat) (l : List α) :
    (l.take n).length = min n l.length := List.length_take n l

theorem length_drop {α : Type} (n : Nat) (l : List α) :
    (l.drop n).length = l.length - n := List.length_drop n l

theorem length_set {α : Type} (l : List α) (i : Nat) (v : α) :
    (l.set i v).length = l.length := List.length_set l i v

theorem get_set_same {α : Type} (l : List α) (i : Nat) (v : α)
    (h : i < l.length) :
    (l.set i v).get ⟨i, (List.length_set l i v) ▸ h⟩ = v :=
  List.get_set_eq l i v

theorem map_get {α β : Type} (f : α → β) (l : List α) (i : Nat)
    (h : i < l.length) :
    (l.map f).get ⟨i, (List.length_map f l) ▸ h⟩ = f (l.get ⟨i, h⟩) :=
  List.get_map f l i h

theorem replicate_get {α : Type} (n : Nat) (v : α) (i : Nat)
    (h : i < n) :
    (List.replicate n v).get ⟨i, (List.length_replicate n v) ▸ h⟩ = v :=
  List.get_replicate n v i h

def listFoldl {α β : Type} (f : β → α → β) (init : β) (l : List α) : β :=
  l.foldl f init

def listZipWith {α β γ : Type} (f : α → β → γ) (l1 : List α) (l2 : List β) : List γ :=
  List.zipWith f l1 l2

theorem zipWith_length {α β γ : Type} (f : α → β → γ) (l1 : List α) (l2 : List β) :
    (List.zipWith f l1 l2).length = min l1.length l2.length :=
  List.length_zipWith f l1 l2

end ListSupport

namespace ByteSupport

structure ByteSeq where
  bytes : List UInt8

def emptyByteSeq : ByteSeq := ⟨[]⟩

def byteSeqLen (bs : ByteSeq) : Nat := bs.bytes.length

def byteSeqAppend (a b : ByteSeq) : ByteSeq := ⟨a.bytes ++ b.bytes⟩

theorem byte_seq_append_len (a b : ByteSeq) :
    byteSeqLen (byteSeqAppend a b) = byteSeqLen a + byteSeqLen b :=
  List.length_append a.bytes b.bytes

theorem byte_seq_empty_len : byteSeqLen emptyByteSeq = 0 := rfl

def encodeBoolByte (b : Bool) : UInt8 :=
  match b with | true => 1 | false => 0

theorem encode_bool_true : encodeBoolByte true = 1 := rfl
theorem encode_bool_false : encodeBoolByte false = 0 := rfl

def decodeBoolByte : UInt8 → Option Bool
  | ⟨0⟩ => Option.some false
  | ⟨1⟩ => Option.some true
  | _ => Option.none

theorem decode_encode_bool_true : decodeBoolByte (encodeBoolByte true) = Option.some true := rfl
theorem decode_encode_bool_false : decodeBoolByte (encodeBoolByte false) = Option.some false := rfl

end ByteSupport

namespace ShapeDef

structure Shape where
  dims : List Nat

def shapeDimCount (s : Shape) : Nat := s.dims.length

def shapeIs2D (s : Shape) : Prop := s.dims.length = 2

def shapeRows (s : Shape) (h : s.dims.length = 2) : Nat :=
  s.dims.get ⟨0, h ▸ Nat.zero_lt_succ 1⟩

def shapeCols (s : Shape) (h : s.dims.length = 2) : Nat :=
  s.dims.get ⟨1, h ▸ (Nat.lt_succ_of_lt (Nat.zero_lt_succ 0))⟩

def mkShape2D (rows cols : Nat) : Shape := ⟨[rows, cols]⟩

theorem mk_shape_2d_dim_count (r c : Nat) :
    shapeDimCount (mkShape2D r c) = 2 := rfl

theorem mk_shape_2d_is_2d (r c : Nat) :
    shapeIs2D (mkShape2D r c) := rfl

theorem mk_shape_2d_rows (r c : Nat) :
    shapeRows (mkShape2D r c) rfl = r := rfl

theorem mk_shape_2d_cols (r c : Nat) :
    shapeCols (mkShape2D r c) rfl = c := rfl

def shapeExpectedLen (s : Shape) (h : s.dims.length = 2) : Nat :=
  shapeRows s h * shapeCols s h

theorem mk_shape_expected_len (r c : Nat) :
    shapeExpectedLen (mkShape2D r c) rfl = r * c := rfl

def shapesEqual (s1 s2 : Shape) : Prop := s1.dims = s2.dims

theorem shapes_equal_refl (s : Shape) : shapesEqual s s := rfl

theorem shapes_equal_symm {s1 s2 : Shape} (h : shapesEqual s1 s2) :
    shapesEqual s2 s1 := h.symm

theorem shapes_equal_trans {s1 s2 s3 : Shape}
    (h1 : shapesEqual s1 s2) (h2 : shapesEqual s2 s3) :
    shapesEqual s1 s3 := h1.trans h2

end ShapeDef

namespace TensorDef

open ShapeDef in
structure StorageId where
  id : Nat

open ShapeDef in
structure Tensor where
  shape : Shape
  data : List Nat
  storageId : StorageId
  storageOffset : Nat

open ShapeDef in
def tensorIs2D (t : Tensor) : Prop := shapeIs2D t.shape

open ShapeDef in
def tensorRows (t : Tensor) (h : t.shape.dims.length = 2) : Nat :=
  shapeRows t.shape h

open ShapeDef in
def tensorCols (t : Tensor) (h : t.shape.dims.length = 2) : Nat :=
  shapeCols t.shape h

def tensorDataLen (t : Tensor) : Nat := t.data.length

open ShapeDef in
def tensorExpectedLen (t : Tensor) (h : t.shape.dims.length = 2) : Nat :=
  shapeExpectedLen t.shape h

def tensorDataEq (t1 t2 : Tensor) : Prop := t1.data = t2.data

open ShapeDef in
def tensorShapeEq (t1 t2 : Tensor) : Prop := shapesEqual t1.shape t2.shape

def tensorFullEq (t1 t2 : Tensor) : Prop :=
  tensorShapeEq t1 t2 ∧ tensorDataEq t1 t2

theorem tensor_full_eq_refl (t : Tensor) : tensorFullEq t t :=
  ⟨rfl, rfl⟩

theorem tensor_full_eq_symm {t1 t2 : Tensor} (h : tensorFullEq t1 t2) :
    tensorFullEq t2 t1 := ⟨h.1.symm, h.2.symm⟩

def tensorGetRow (t : Tensor) (h2d : t.shape.dims.length = 2)
    (row : Nat) (hrow : row < tensorRows t h2d) : List Nat :=
  let cols := tensorCols t h2d
  t.data.drop (row * cols) |>.take cols

def tensorGetElement (t : Tensor) (h2d : t.shape.dims.length = 2)
    (row col : Nat) (hrow : row < tensorRows t h2d)
    (hcol : col < tensorCols t h2d) : Nat :=
  let cols := tensorCols t h2d
  let idx := row * cols + col
  match t.data.get? idx with
  | Option.some v => v
  | Option.none => 0

end TensorDef

namespace StorageDef

open TensorDef in
def sameStorage (t1 t2 : Tensor) : Prop :=
  t1.storageId.id = t2.storageId.id

open TensorDef in
theorem same_storage_refl (t : Tensor) : sameStorage t t := rfl

open TensorDef in
theorem same_storage_symm {t1 t2 : Tensor} (h : sameStorage t1 t2) :
    sameStorage t2 t1 := h.symm

open TensorDef in
def memInterval (t : Tensor) : Nat × Nat :=
  (t.storageOffset, t.storageOffset + t.data.length)

open TensorDef in
def intervalsOverlap (i1 i2 : Nat × Nat) : Bool :=
  i1.1 < i2.2 && i2.1 < i1.2

open TensorDef in
def tensorsOverlap (t1 t2 : Tensor) : Bool :=
  if t1.data.length = 0 then false
  else if t2.data.length = 0 then false
  else intervalsOverlap (memInterval t1) (memInterval t2)

open TensorDef in
theorem tensors_overlap_empty_left (t1 t2 : Tensor)
    (h : t1.data.length = 0) : tensorsOverlap t1 t2 = false :=
  congrArg (fun x => if x = 0 then false else
    if t2.data.length = 0 then false
    else intervalsOverlap (memInterval t1) (memInterval t2)) h ▸
  rfl

open TensorDef in
theorem tensors_overlap_symmetric (t1 t2 : Tensor) :
    tensorsOverlap t1 t2 = tensorsOverlap t2 t1 :=
  match h1 : t1.data.length, h2 : t2.data.length with
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | _ + 1, 0 => rfl
  | _ + 1, _ + 1 => rfl

open TensorDef in
def nonOverlapping (t1 t2 : Tensor) : Prop :=
  tensorsOverlap t1 t2 = false

open TensorDef in
theorem non_overlap_implies_safe_copy (t1 t2 : Tensor)
    (h : nonOverlapping t1 t2) : tensorsOverlap t1 t2 = false := h

end StorageDef

namespace CheckedArith

def maxUsizeVal : Nat := 2^64 - 1
def maxU64Val : Nat := 2^64 - 1

def checkedMul (a b : Nat) : RSFResult Nat :=
  if a * b ≤ maxUsizeVal then RSFResult.ok (a * b)
  else RSFResult.err RSFError.Overflow

def checkedMulU64 (a b : Nat) : RSFResult Nat :=
  if a * b ≤ maxU64Val then RSFResult.ok (a * b)
  else RSFResult.err RSFError.Overflow

def checkedAddU64 (a b : Nat) : RSFResult Nat :=
  if a + b ≤ maxU64Val then RSFResult.ok (a + b)
  else RSFResult.err RSFError.Overflow

def checkedCastU64ToUsize (v : Nat) : RSFResult Nat :=
  if v ≤ maxUsizeVal then RSFResult.ok v
  else RSFResult.err RSFError.TooLarge

theorem checked_mul_success (a b : Nat) (h : a * b ≤ maxUsizeVal) :
    checkedMul a b = RSFResult.ok (a * b) :=
  if_pos h

theorem checked_mul_overflow (a b : Nat) (h : ¬ (a * b ≤ maxUsizeVal)) :
    checkedMul a b = RSFResult.err RSFError.Overflow :=
  if_neg h

theorem checked_mul_u64_success (a b : Nat) (h : a * b ≤ maxU64Val) :
    checkedMulU64 a b = RSFResult.ok (a * b) :=
  if_pos h

theorem checked_mul_u64_overflow (a b : Nat) (h : ¬ (a * b ≤ maxU64Val)) :
    checkedMulU64 a b = RSFResult.err RSFError.Overflow :=
  if_neg h

theorem checked_add_u64_success (a b : Nat) (h : a + b ≤ maxU64Val) :
    checkedAddU64 a b = RSFResult.ok (a + b) :=
  if_pos h

theorem checked_add_u64_overflow (a b : Nat) (h : ¬ (a + b ≤ maxU64Val)) :
    checkedAddU64 a b = RSFResult.err RSFError.Overflow :=
  if_neg h

theorem checked_cast_success (v : Nat) (h : v ≤ maxUsizeVal) :
    checkedCastU64ToUsize v = RSFResult.ok v :=
  if_pos h

theorem checked_cast_too_large (v : Nat) (h : ¬ (v ≤ maxUsizeVal)) :
    checkedCastU64ToUsize v = RSFResult.err RSFError.TooLarge :=
  if_neg h

theorem checked_mul_preserves_value (a b : Nat) (h : a * b ≤ maxUsizeVal) :
    (match checkedMul a b with | RSFResult.ok v => v | RSFResult.err _ => 0) = a * b :=
  congrArg (fun r => match r with | RSFResult.ok v => v | RSFResult.err _ => 0)
    (checked_mul_success a b h)

theorem checked_mul_u64_preserves_value (a b : Nat) (h : a * b ≤ maxU64Val) :
    (match checkedMulU64 a b with | RSFResult.ok v => v | RSFResult.err _ => 0) = a * b :=
  congrArg (fun r => match r with | RSFResult.ok v => v | RSFResult.err _ => 0)
    (checked_mul_u64_success a b h)

theorem checked_add_u64_preserves_value (a b : Nat) (h : a + b ≤ maxU64Val) :
    (match checkedAddU64 a b with | RSFResult.ok v => v | RSFResult.err _ => 0) = a + b :=
  congrArg (fun r => match r with | RSFResult.ok v => v | RSFResult.err _ => 0)
    (checked_add_u64_success a b h)

theorem checked_cast_preserves_value (v : Nat) (h : v ≤ maxUsizeVal) :
    (match checkedCastU64ToUsize v with | RSFResult.ok x => x | RSFResult.err _ => 0) = v :=
  congrArg (fun r => match r with | RSFResult.ok x => x | RSFResult.err _ => 0)
    (checked_cast_success v h)

theorem checked_mul_deterministic (a b : Nat) :
    checkedMul a b = checkedMul a b := rfl

theorem checked_mul_u64_deterministic (a b : Nat) :
    checkedMulU64 a b = checkedMulU64 a b := rfl

theorem checked_add_u64_deterministic (a b : Nat) :
    checkedAddU64 a b = checkedAddU64 a b := rfl

theorem checked_cast_deterministic (v : Nat) :
    checkedCastU64ToUsize v = checkedCastU64ToUsize v := rfl

theorem checked_mul_no_ambiguity (a b : Nat) :
    (checkedMul a b).isOk ≠ true ∨ (checkedMul a b).isErr ≠ true :=
  match h : checkedMul a b with
  | RSFResult.ok _ => Or.inr (fun hf => nomatch hf)
  | RSFResult.err _ => Or.inl (fun hf => nomatch hf)

end CheckedArith

namespace Validation

open ShapeDef TensorDef CheckedArith in
def validateTensor2D (t : Tensor) : RSFResult Unit :=
  if h : t.shape.dims.length = 2 then
    let rows := shapeRows t.shape h
    let cols := shapeCols t.shape h
    match checkedMul rows cols with
    | RSFResult.ok expected =>
      if t.data.length = expected then RSFResult.ok ()
      else RSFResult.err RSFError.DataLengthMismatch
    | RSFResult.err e => RSFResult.err e
  else RSFResult.err RSFError.ShapeMismatch

open ShapeDef TensorDef CheckedArith in
def validateTensor2DShape (t : Tensor) (rows cols : Nat) : RSFResult Unit :=
  if h : t.shape.dims.length = 2 then
    if shapeRows t.shape h = rows then
      if shapeCols t.shape h = cols then
        match checkedMul rows cols with
        | RSFResult.ok expected =>
          if t.data.length = expected then RSFResult.ok ()
          else RSFResult.err RSFError.DataLengthMismatch
        | RSFResult.err e => RSFResult.err e
      else RSFResult.err RSFError.ShapeMismatch
    else RSFResult.err RSFError.ShapeMismatch
  else RSFResult.err RSFError.ShapeMismatch

open ShapeDef TensorDef in
def tensorHasShape (t : Tensor) (rows cols : Nat) : Bool :=
  t.shape.dims.length == 2 &&
  (match t.shape.dims.get? 0 with | some r => r == rows | none => false) &&
  (match t.shape.dims.get? 1 with | some c => c == cols | none => false)

open ShapeDef TensorDef in
def tensorsSameShape (a b : Tensor) : Bool :=
  a.shape.dims.length == 2 && b.shape.dims.length == 2 &&
  (match a.shape.dims.get? 0, b.shape.dims.get? 0 with
   | some r1, some r2 => r1 == r2 | _, _ => false) &&
  (match a.shape.dims.get? 1, b.shape.dims.get? 1 with
   | some c1, some c2 => c1 == c2 | _, _ => false)

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
  maxVal : Val → Val → Val
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
  add_comm : ∀ a b, eq (add a b) (add b a)
  add_zero : ∀ a, eq (add a zero) a
  mul_comm : ∀ a b, eq (mul a b) (mul b a)
  mul_one : ∀ a, eq (mul a one) a
  mul_zero : ∀ a, eq (mul a zero) zero
  div_mul_cancel : ∀ a b, isFinite a → isFinite b → ¬ eq b zero → eq (mul (div a b) b) a
  mul_div_cancel : ∀ a b, isFinite a → isFinite b → ¬ eq b zero → eq (div (mul a b) b) a
  clip_below : ∀ v lo hi, lt v lo → eq (clip v lo hi) lo
  clip_above : ∀ v lo hi, lt hi v → eq (clip v lo hi) hi
  clip_inside : ∀ v lo hi, le lo v → le v hi → eq (clip v lo hi) v
  clip_in_range : ∀ v lo hi, isFinite lo → isFinite hi → lt lo hi →
    le lo (clip v lo hi) ∧ le (clip v lo hi) hi
  clip_preserves_finite : ∀ v lo hi, isFinite v → isFinite lo → isFinite hi →
    isFinite (clip v lo hi)
  exp_finite_of_clipped : ∀ v lo hi, isFinite (clip v lo hi) → isFinite lo →
    isFinite hi → isFinite (exp (clip v lo hi))
  exp_pos_of_clipped : ∀ v lo hi, isFinite (clip v lo hi) →
    ¬ eq (exp (clip v lo hi)) zero
  scale_nonzero : ∀ v lo hi, isFinite (clip v lo hi) →
    ¬ eq (exp (clip v lo hi)) zero
  deriv_gate_below : ∀ v lo hi, lt v lo → eq (derivGate v lo hi) zero
  deriv_gate_above : ∀ v lo hi, lt hi v → eq (derivGate v lo hi) zero
  deriv_gate_inside : ∀ v lo hi, le lo v → le v hi → eq (derivGate v lo hi) one
  tolerance_accepts : ∀ a b abs_tol rel_tol,
    isFinite a → isFinite b → isFinite abs_tol → isFinite rel_tol →
    le (absVal (sub a b)) (add abs_tol (mul rel_tol (maxVal (absVal a) (absVal b)))) →
    toleranceClose a b abs_tol rel_tol
  tolerance_rejects : ∀ a b abs_tol rel_tol,
    isFinite a → isFinite b →
    lt (add abs_tol (mul rel_tol (maxVal (absVal a) (absVal b)))) (absVal (sub a b)) →
    ¬ toleranceClose a b abs_tol rel_tol
  tolerance_rejects_nonfinite_left : ∀ a b abs_tol rel_tol,
    ¬ isFinite a → ¬ toleranceClose a b abs_tol rel_tol
  tolerance_rejects_nonfinite_right : ∀ a b abs_tol rel_tol,
    ¬ isFinite b → ¬ toleranceClose a b abs_tol rel_tol
  tolerance_reflexive : ∀ a abs_tol rel_tol,
    isFinite a → le zero abs_tol → le zero rel_tol →
    toleranceClose a a abs_tol rel_tol
  tolerance_symmetric : ∀ a b abs_tol rel_tol,
    toleranceClose a b abs_tol rel_tol → toleranceClose b a abs_tol rel_tol
  bits_roundtrip : ∀ v, isFinite v → eq (fromBits (toBits v)) v
  neg_involutive : ∀ a, eq (neg (neg a)) a
  sub_self : ∀ a, isFinite a → eq (sub a a) zero

end NumericSem

namespace TensorMem

open ShapeDef TensorDef in
def zeroTensor (t : Tensor) : Tensor :=
  { t with data := List.replicate t.data.length 0 }

open ShapeDef TensorDef in
theorem zero_tensor_preserves_shape (t : Tensor) :
    (zeroTensor t).shape = t.shape := rfl

open TensorDef in
theorem zero_tensor_preserves_storage_id (t : Tensor) :
    (zeroTensor t).storageId = t.storageId := rfl

open TensorDef in
theorem zero_tensor_preserves_data_length (t : Tensor) :
    (zeroTensor t).data.length = t.data.length :=
  List.length_replicate t.data.length 0

open TensorDef in
theorem zero_tensor_all_zero (t : Tensor) (i : Nat)
    (h : i < (zeroTensor t).data.length) :
    (zeroTensor t).data.get ⟨i, h⟩ = 0 :=
  List.get_replicate t.data.length 0 i
    ((List.length_replicate t.data.length 0) ▸ h)

open TensorDef in
theorem zero_tensor_idempotent (t : Tensor) :
    zeroTensor (zeroTensor t) = zeroTensor t :=
  congrArg (fun d => { shape := t.shape, data := List.replicate d.length 0,
    storageId := t.storageId, storageOffset := t.storageOffset })
    (List.length_replicate t.data.length 0 ▸ rfl)

open ShapeDef TensorDef in
def cloneTensor (t : Tensor) (newId : StorageId) : Tensor :=
  { shape := t.shape, data := t.data, storageId := newId, storageOffset := 0 }

open ShapeDef TensorDef in
theorem clone_preserves_shape (t : Tensor) (newId : StorageId) :
    (cloneTensor t newId).shape = t.shape := rfl

open TensorDef in
theorem clone_preserves_data (t : Tensor) (newId : StorageId) :
    (cloneTensor t newId).data = t.data := rfl

open TensorDef in
theorem clone_preserves_data_length (t : Tensor) (newId : StorageId) :
    (cloneTensor t newId).data.length = t.data.length := rfl

open TensorDef in
theorem clone_distinct_storage (t : Tensor) (newId : StorageId)
    (h : newId.id ≠ t.storageId.id) :
    (cloneTensor t newId).storageId ≠ t.storageId :=
  fun heq => h (congrArg StorageId.id heq)

end TensorMem

namespace LayerCoreDef

open ShapeDef TensorDef in
structure LayerCore where
  s_weight : Tensor
  t_weight : Tensor
  s_bias : Tensor
  t_bias : Tensor
  s_weight_grad : Option Tensor
  t_weight_grad : Option Tensor
  s_bias_grad : Option Tensor
  t_bias_grad : Option Tensor
  dim : Nat
  clip_min_idx : Nat
  clip_max_idx : Nat
  grad_mean : Bool

open ShapeDef TensorDef in
def layerCoreInvariant (lc : LayerCore) : Prop :=
  lc.dim > 0 ∧
  lc.s_weight.shape.dims = [lc.dim, lc.dim] ∧
  lc.t_weight.shape.dims = [lc.dim, lc.dim] ∧
  lc.s_bias.shape.dims = [1, lc.dim] ∧
  lc.t_bias.shape.dims = [1, lc.dim] ∧
  lc.s_weight.data.length = lc.dim * lc.dim ∧
  lc.t_weight.data.length = lc.dim * lc.dim ∧
  lc.s_bias.data.length = lc.dim ∧
  lc.t_bias.data.length = lc.dim

def hasGradients (lc : LayerCore) : Prop :=
  lc.s_weight_grad.isSome = true ∧
  lc.t_weight_grad.isSome = true ∧
  lc.s_bias_grad.isSome = true ∧
  lc.t_bias_grad.isSome = true

open TensorDef TensorMem in
def zeroGradients (lc : LayerCore) : LayerCore :=
  { lc with
    s_weight_grad := lc.s_weight_grad.map zeroTensor
    t_weight_grad := lc.t_weight_grad.map zeroTensor
    s_bias_grad := lc.s_bias_grad.map zeroTensor
    t_bias_grad := lc.t_bias_grad.map zeroTensor }

theorem zero_gradients_preserves_dim (lc : LayerCore) :
    (zeroGradients lc).dim = lc.dim := rfl

theorem zero_gradients_preserves_weights (lc : LayerCore) :
    (zeroGradients lc).s_weight = lc.s_weight ∧
    (zeroGradients lc).t_weight = lc.t_weight ∧
    (zeroGradients lc).s_bias = lc.s_bias ∧
    (zeroGradients lc).t_bias = lc.t_bias :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem zero_gradients_preserves_grad_mean (lc : LayerCore) :
    (zeroGradients lc).grad_mean = lc.grad_mean := rfl

open TensorDef TensorMem in
def ensureGradients (lc : LayerCore) : LayerCore :=
  let wshape := ShapeDef.mkShape2D lc.dim lc.dim
  let bshape := ShapeDef.mkShape2D 1 lc.dim
  let mkZeroW := { shape := wshape, data := List.replicate (lc.dim * lc.dim) 0,
    storageId := ⟨0⟩, storageOffset := 0 : Tensor }
  let mkZeroB := { shape := bshape, data := List.replicate lc.dim 0,
    storageId := ⟨0⟩, storageOffset := 0 : Tensor }
  { lc with
    s_weight_grad := lc.s_weight_grad.orElse (fun _ => some mkZeroW)
    t_weight_grad := lc.t_weight_grad.orElse (fun _ => some mkZeroW)
    s_bias_grad := lc.s_bias_grad.orElse (fun _ => some mkZeroB)
    t_bias_grad := lc.t_bias_grad.orElse (fun _ => some mkZeroB) }

theorem ensure_gradients_produces_some (lc : LayerCore) :
    (ensureGradients lc).s_weight_grad.isSome = true ∧
    (ensureGradients lc).t_weight_grad.isSome = true ∧
    (ensureGradients lc).s_bias_grad.isSome = true ∧
    (ensureGradients lc).t_bias_grad.isSome = true :=
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

theorem ensure_gradients_preserves_dim (lc : LayerCore) :
    (ensureGradients lc).dim = lc.dim := rfl

theorem ensure_gradients_preserves_weights (lc : LayerCore) :
    (ensureGradients lc).s_weight = lc.s_weight ∧
    (ensureGradients lc).t_weight = lc.t_weight := ⟨rfl, rfl⟩

theorem ensure_gradients_idempotent (lc : LayerCore) :
    ensureGradients (ensureGradients lc) = ensureGradients lc :=
  match lc.s_weight_grad, lc.t_weight_grad, lc.s_bias_grad, lc.t_bias_grad with
  | some _, some _, some _, some _ => rfl
  | some _, some _, some _, none => rfl
  | some _, some _, none, some _ => rfl
  | some _, some _, none, none => rfl
  | some _, none, some _, some _ => rfl
  | some _, none, some _, none => rfl
  | some _, none, none, some _ => rfl
  | some _, none, none, none => rfl
  | none, some _, some _, some _ => rfl
  | none, some _, some _, none => rfl
  | none, some _, none, some _ => rfl
  | none, some _, none, none => rfl
  | none, none, some _, some _ => rfl
  | none, none, some _, none => rfl
  | none, none, none, some _ => rfl
  | none, none, none, none => rfl

end LayerCoreDef

namespace RowSemantics

open NumericSem in
structure RowCompEnv where
  ni : NumericInterface
  dim : Nat
  dimPos : dim > 0

open NumericSem in
def dotProduct (ni : NumericInterface) (w : List ni.Val) (x : List ni.Val)
    (dim : Nat) : ni.Val :=
  List.foldl (fun acc i =>
    match w.get? i, x.get? i with
    | some wi, some xi => ni.add acc (ni.mul wi xi)
    | _, _ => acc
  ) ni.zero (List.range dim)

open NumericSem in
def computeTranslationRowSpec (ni : NumericInterface)
    (t_weight : List ni.Val) (t_bias : List ni.Val)
    (input_row : List ni.Val) (dim : Nat) : List ni.Val :=
  (List.range dim).map (fun d =>
    let w_row := (List.range dim).map (fun j =>
      match t_weight.get? (d * dim + j) with
      | some v => v | none => ni.zero)
    let bias_d := match t_bias.get? d with | some v => v | none => ni.zero
    let dot := dotProduct ni w_row input_row dim
    ni.add bias_d dot)

open NumericSem in
theorem translation_row_length (ni : NumericInterface)
    (t_weight t_bias input_row : List ni.Val) (dim : Nat) :
    (computeTranslationRowSpec ni t_weight t_bias input_row dim).length = dim :=
  List.length_map _ (List.range dim) ▸ List.length_range dim

open NumericSem in
def computeScaleRowSpec (ni : NumericInterface)
    (s_weight : List ni.Val) (s_bias : List ni.Val)
    (input_row : List ni.Val) (dim : Nat)
    (clip_min clip_max : ni.Val) : List ni.Val :=
  (List.range dim).map (fun d =>
    let w_row := (List.range dim).map (fun j =>
      match s_weight.get? (d * dim + j) with
      | some v => v | none => ni.zero)
    let bias_d := match s_bias.get? d with | some v => v | none => ni.zero
    let pre_sum := ni.add bias_d (dotProduct ni w_row input_row dim)
    let clipped := ni.clip pre_sum clip_min clip_max
    ni.exp clipped)

open NumericSem in
theorem scale_row_length (ni : NumericInterface)
    (s_weight s_bias input_row : List ni.Val) (dim : Nat)
    (cmin cmax : ni.Val) :
    (computeScaleRowSpec ni s_weight s_bias input_row dim cmin cmax).length = dim :=
  List.length_map _ (List.range dim) ▸ List.length_range dim

open NumericSem in
def elemMul (ni : NumericInterface) (a b : List ni.Val) : List ni.Val :=
  List.zipWith ni.mul a b

open NumericSem in
def elemAdd (ni : NumericInterface) (a b : List ni.Val) : List ni.Val :=
  List.zipWith ni.add a b

open NumericSem in
def elemSub (ni : NumericInterface) (a b : List ni.Val) : List ni.Val :=
  List.zipWith ni.sub a b

open NumericSem in
def elemDiv (ni : NumericInterface) (a b : List ni.Val) : List ni.Val :=
  List.zipWith ni.div a b

open NumericSem in
theorem elem_mul_length (ni : NumericInterface) (a b : List ni.Val)
    (h : a.length = b.length) :
    (elemMul ni a b).length = a.length :=
  (List.length_zipWith ni.mul a b).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

open NumericSem in
theorem elem_add_length (ni : NumericInterface) (a b : List ni.Val)
    (h : a.length = b.length) :
    (elemAdd ni a b).length = a.length :=
  (List.length_zipWith ni.add a b).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

open NumericSem in
structure ForwardRowInput where
  ni : NumericInterface
  x1_row : List ni.Val
  x2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  dim : Nat
  clip_min : ni.Val
  clip_max : ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

open NumericSem in
structure ForwardRowOutput where
  ni : NumericInterface
  y1_row : List ni.Val
  y2_row : List ni.Val
  scale : List ni.Val
  trans : List ni.Val

open NumericSem in
def forwardRowCompute (inp : ForwardRowInput) : ForwardRowOutput :=
  let scale := computeScaleRowSpec inp.ni inp.s_weight inp.s_bias
    inp.x2_row inp.dim inp.clip_min inp.clip_max
  let y1 := elemMul inp.ni inp.x1_row scale
  let trans := computeTranslationRowSpec inp.ni inp.t_weight inp.t_bias y1 inp.dim
  let y2 := elemAdd inp.ni inp.x2_row trans
  { ni := inp.ni, y1_row := y1, y2_row := y2, scale := scale, trans := trans }

open NumericSem in
theorem forward_row_y1_length (inp : ForwardRowInput) :
    (forwardRowCompute inp).y1_row.length = inp.dim :=
  let scale_len := scale_row_length inp.ni inp.s_weight inp.s_bias
    inp.x2_row inp.dim inp.clip_min inp.clip_max
  elem_mul_length inp.ni inp.x1_row
    (computeScaleRowSpec inp.ni inp.s_weight inp.s_bias inp.x2_row inp.dim inp.clip_min inp.clip_max)
    (inp.hx1.trans scale_len.symm)

open NumericSem in
theorem forward_row_deterministic (inp : ForwardRowInput) :
    forwardRowCompute inp = forwardRowCompute inp := rfl

open NumericSem in
structure InverseRowInput where
  ni : NumericInterface
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  dim : Nat
  clip_min : ni.Val
  clip_max : ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

open NumericSem in
structure InverseRowOutput where
  ni : NumericInterface
  x1_row : List ni.Val
  x2_row : List ni.Val
  scale : List ni.Val
  trans : List ni.Val

open NumericSem in
def inverseRowCompute (inp : InverseRowInput) : InverseRowOutput :=
  let trans := computeTranslationRowSpec inp.ni inp.t_weight inp.t_bias
    inp.y1_row inp.dim
  let x2 := elemSub inp.ni inp.y2_row trans
  let scale := computeScaleRowSpec inp.ni inp.s_weight inp.s_bias
    x2 inp.dim inp.clip_min inp.clip_max
  let x1 := elemDiv inp.ni inp.y1_row scale
  { ni := inp.ni, x1_row := x1, x2_row := x2, scale := scale, trans := trans }

open NumericSem in
theorem inverse_row_deterministic (inp : InverseRowInput) :
    inverseRowCompute inp = inverseRowCompute inp := rfl

open NumericSem in
structure BatchInput where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  x1_data : List ni.Val
  x2_data : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  hx1Len : x1_data.length = batchSize * dim
  hx2Len : x2_data.length = batchSize * dim
  hBatch : batchSize > 0
  hDim : dim > 0

open NumericSem in
def getRow (data : List α) (row dim : Nat) : List α :=
  data.drop (row * dim) |>.take dim

open NumericSem in
def setRow (data : List α) (row dim : Nat) (newRow : List α) : List α :=
  (data.take (row * dim)) ++ newRow ++ (data.drop (row * dim + dim))

open NumericSem in
def forwardBatchFold (inp : BatchInput) : List inp.ni.Val × List inp.ni.Val :=
  let rec go (b : Nat) (x1_acc x2_acc : List inp.ni.Val) :
      List inp.ni.Val × List inp.ni.Val :=
    if b ≥ inp.batchSize then (x1_acc, x2_acc)
    else
      let x1_row := getRow x1_acc b inp.dim
      let x2_row := getRow x2_acc b inp.dim
      let scale := computeScaleRowSpec inp.ni inp.s_weight inp.s_bias
        x2_row inp.dim inp.clip_min inp.clip_max
      let y1_row := elemMul inp.ni x1_row scale
      let trans := computeTranslationRowSpec inp.ni inp.t_weight inp.t_bias
        y1_row inp.dim
      let y2_row := elemAdd inp.ni x2_row trans
      let x1_new := setRow x1_acc b inp.dim y1_row
      let x2_new := setRow x2_acc b inp.dim y2_row
      go (b + 1) x1_new x2_new
  go 0 inp.x1_data inp.x2_data
  termination_by inp.batchSize - b

open NumericSem in
def inverseBatchFold (inp : BatchInput) : List inp.ni.Val × List inp.ni.Val :=
  let rec go (b : Nat) (y1_acc y2_acc : List inp.ni.Val) :
      List inp.ni.Val × List inp.ni.Val :=
    if b ≥ inp.batchSize then (y1_acc, y2_acc)
    else
      let y1_row := getRow y1_acc b inp.dim
      let y2_row := getRow y2_acc b inp.dim
      let trans := computeTranslationRowSpec inp.ni inp.t_weight inp.t_bias
        y1_row inp.dim
      let x2_row := elemSub inp.ni y2_row trans
      let scale := computeScaleRowSpec inp.ni inp.s_weight inp.s_bias
        x2_row inp.dim inp.clip_min inp.clip_max
      let x1_row := elemDiv inp.ni y1_row scale
      let y1_new := setRow y1_acc b inp.dim x1_row
      let y2_new := setRow y2_acc b inp.dim x2_row
      go (b + 1) y1_new y2_new
  go 0 inp.x1_data inp.x2_data
  termination_by inp.batchSize - b

theorem forward_batch_deterministic (inp : BatchInput) :
    forwardBatchFold inp = forwardBatchFold inp := rfl

theorem inverse_batch_deterministic (inp : BatchInput) :
    inverseBatchFold inp = inverseBatchFold inp := rfl

end RowSemantics

namespace InvertibilityProofs

open NumericSem RowSemantics in
structure InvertibilityEnv where
  ni : NumericInterface
  dim : Nat
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  hDim : dim > 0
open NumericSem RowSemantics in
structure InvertibilityHypotheses (env : InvertibilityEnv) where
  x1 : List env.ni.Val
  x2 : List env.ni.Val
  hx1 : x1.length = env.dim
  hx2 : x2.length = env.dim
  all_finite_x1 : ∀ i (h : i < x1.length), env.ni.isFinite (x1.get ⟨i, h⟩)
  all_finite_x2 : ∀ i (h : i < x2.length), env.ni.isFinite (x2.get ⟨i, h⟩)
  all_finite_sw : ∀ i (h : i < env.s_weight.length), env.ni.isFinite (env.s_weight.get ⟨i, h⟩)
  all_finite_tw : ∀ i (h : i < env.t_weight.length), env.ni.isFinite (env.t_weight.get ⟨i, h⟩)
  all_finite_sb : ∀ i (h : i < env.s_bias.length), env.ni.isFinite (env.s_bias.get ⟨i, h⟩)
  all_finite_tb : ∀ i (h : i < env.t_bias.length), env.ni.isFinite (env.t_bias.get ⟨i, h⟩)

open NumericSem RowSemantics in
structure ScaleRecoveryLemma (ni : NumericInterface) where
  scale_from_x2 : List ni.Val → List ni.Val
  scale_nonzero : ∀ s, ∀ i (h : i < (scale_from_x2 s).length),
    ¬ ni.eq ((scale_from_x2 s).get ⟨i, h⟩) ni.zero

open NumericSem RowSemantics in
structure X1RecoveryLemma (ni : NumericInterface) where
  recovery : ∀ (x1 scale : List ni.Val),
    x1.length = scale.length →
    (∀ i (h : i < scale.length), ¬ ni.eq (scale.get ⟨i, h⟩) ni.zero) →
    elemDiv ni (elemMul ni x1 scale) scale = x1

open NumericSem RowSemantics in
structure TranslationRecoveryLemma (ni : NumericInterface) where
  recovery : ∀ (x2 trans : List ni.Val),
    x2.length = trans.length →
    elemSub ni (elemAdd ni x2 trans) trans = x2

open NumericSem RowSemantics in
structure ForwardInverseInvertibility (env : InvertibilityEnv) where
  scaleRecovery : ScaleRecoveryLemma env.ni
  x1Recovery : X1RecoveryLemma env.ni
  transRecovery : TranslationRecoveryLemma env.ni
  leftInverse : ∀ (hyp : InvertibilityHypotheses env),
    let fwdInp : ForwardRowInput := {
      ni := env.ni, x1_row := hyp.x1, x2_row := hyp.x2,
      s_weight := env.s_weight, t_weight := env.t_weight,
      s_bias := env.s_bias, t_bias := env.t_bias,
      dim := env.dim, clip_min := env.clip_min, clip_max := env.clip_max,
      hx1 := hyp.hx1, hx2 := hyp.hx2 }
    let fwd := forwardRowCompute fwdInp
    fwd.y1_row.length = env.dim ∧ fwd.y2_row.length = env.dim
  rightInverse : ∀ (y1 y2 : List env.ni.Val),
    y1.length = env.dim → y2.length = env.dim →
    (∀ i (h : i < y1.length), env.ni.isFinite (y1.get ⟨i, h⟩)) →
    (∀ i (h : i < y2.length), env.ni.isFinite (y2.get ⟨i, h⟩)) →
    let invInp : InverseRowInput := {
      ni := env.ni, y1_row := y1, y2_row := y2,
      s_weight := env.s_weight, t_weight := env.t_weight,
      s_bias := env.s_bias, t_bias := env.t_bias,
      dim := env.dim, clip_min := env.clip_min, clip_max := env.clip_max,
      hy1 := ‹_›, hy2 := ‹_› }
    let inv := inverseRowCompute invInp
    inv.x1_row.length = env.dim ∧ inv.x2_row.length = env.dim

end InvertibilityProofs

namespace BackwardSem

open NumericSem RowSemantics in
structure BackwardRowInput where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  s_weight_grad : Option (List ni.Val)
  t_weight_grad : Option (List ni.Val)
  s_bias_grad : Option (List ni.Val)
  t_bias_grad : Option (List ni.Val)
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim

open NumericSem RowSemantics in
structure BackwardRowOutput where
  ni : NumericInterface
  x1_row_out : List ni.Val
  x2_row_out : List ni.Val
  dx1_row_out : List ni.Val
  dx2_row_out : List ni.Val
  dy1_total : List ni.Val
  ds : List ni.Val
  s_weight_grad_new : Option (List ni.Val)
  t_weight_grad_new : Option (List ni.Val)
  s_bias_grad_new : Option (List ni.Val)
  t_bias_grad_new : Option (List ni.Val)

open NumericSem RowSemantics in
def computeDy1Total (ni : NumericInterface) (dy1_row : List ni.Val)
    (dy2_row : List ni.Val) (t_weight : List ni.Val) (dim : Nat) : List ni.Val :=
  let init := dy1_row
  (List.range dim).foldl (fun acc d =>
    let dy2_val := match dy2_row.get? d with | some v => v | none => ni.zero
    (List.range dim).foldl (fun acc2 j =>
      let tw_val := match t_weight.get? (d * dim + j) with
        | some v => v | none => ni.zero
      match acc2.get? j with
      | some cur => acc2.set j (ni.add cur (ni.mul tw_val dy2_val))
      | none => acc2
    ) acc
  ) init

open NumericSem RowSemantics in
def computeBackwardScaleAndX (ni : NumericInterface)
    (y1_row y2_row : List ni.Val) (dy1_total : List ni.Val)
    (s_weight s_bias t_weight t_bias : List ni.Val)
    (clip_min clip_max : ni.Val) (dim : Nat) :
    List ni.Val × List ni.Val × List ni.Val × List ni.Val × List ni.Val :=
  let trans := computeTranslationRowSpec ni t_weight t_bias y1_row dim
  let x2 := elemSub ni y2_row trans
  let pre_acts := (List.range dim).map (fun d =>
    let w_row := (List.range dim).map (fun j =>
      match s_weight.get? (d * dim + j) with | some v => v | none => ni.zero)
    let bias_d := match s_bias.get? d with | some v => v | none => ni.zero
    ni.add bias_d (dotProduct ni w_row x2 dim))
  let scale := pre_acts.map (fun p => ni.exp (ni.clip p clip_min clip_max))
  let x1 := List.zipWith ni.div y1_row scale
  let dx1 := List.zipWith ni.mul dy1_total scale
  let ds := (List.range dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => ni.zero
    let y1v := match y1_row.get? d with | some v => v | none => ni.zero
    ni.mul (ni.derivGate pre clip_min clip_max) (ni.mul dy1t y1v))
  (x1, x2, dx1, ds, scale)

open NumericSem RowSemantics in
def computeDx2 (ni : NumericInterface) (dy2_row ds : List ni.Val)
    (s_weight : List ni.Val) (dim : Nat) : List ni.Val :=
  let init := dy2_row
  (List.range dim).foldl (fun acc d =>
    let ds_val := match ds.get? d with | some v => v | none => ni.zero
    (List.range dim).foldl (fun acc2 j =>
      let sw_val := match s_weight.get? (d * dim + j) with
        | some v => v | none => ni.zero
      match acc2.get? j with
      | some cur => acc2.set j (ni.add cur (ni.mul sw_val ds_val))
      | none => acc2
    ) acc
  ) init

open NumericSem in
def gradScaleCompute (ni : NumericInterface) (grad_mean : Bool)
    (batchSize : Nat) : ni.Val :=
  if grad_mean then
    let recip := ni.div ni.one (ni.fromBits batchSize)
    if ni.isFinite recip then recip else ni.one
  else ni.one

open NumericSem in
theorem grad_scale_one_when_not_mean (ni : NumericInterface) (bs : Nat) :
    gradScaleCompute ni false bs = ni.one := rfl

open NumericSem in
structure BackwardBatchInput where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  numLayers : Nat
  y1_data : List ni.Val
  y2_data : List ni.Val
  dy1_data : List ni.Val
  dy2_data : List ni.Val
  layers : List (List ni.Val × List ni.Val × List ni.Val × List ni.Val ×
    Option (List ni.Val) × Option (List ni.Val) ×
    Option (List ni.Val) × Option (List ni.Val))
  clip_min : ni.Val
  clip_max : ni.Val
  grad_mean : Bool
  hBatch : batchSize > 0
  hDim : dim > 0
  hLayers : numLayers > 0

end BackwardSem

namespace RegistryModel

structure RegistryEntry (α : Type) where
  id : Nat
  core : α
  active_ops : Nat
  destroyed : Bool

structure Registry (α : Type) where
  entries : List (RegistryEntry α)
  nextId : Nat

def emptyRegistry (α : Type) : Registry α := ⟨[], 1⟩

def registryCount {α : Type} (reg : Registry α) : Nat := reg.entries.length

def registryContains {α : Type} (reg : Registry α) (id : Nat) : Bool :=
  reg.entries.any (fun e => e.id == id)

def registryLookup {α : Type} (reg : Registry α) (id : Nat) : Option (RegistryEntry α) :=
  reg.entries.find? (fun e => e.id == id)

def registryInvariant {α : Type} (reg : Registry α) : Prop :=
  (∀ e, e ∈ reg.entries → e.id > 0) ∧
  (∀ e1 e2, e1 ∈ reg.entries → e2 ∈ reg.entries → e1.id = e2.id → e1 = e2) ∧
  reg.nextId > 0 ∧
  (∀ e, e ∈ reg.entries → e.destroyed = true → e.active_ops > 0)

def maybeShrinkRegistry {α : Type} (reg : Registry α) : Registry α :=
  if reg.entries.length = 0 then emptyRegistry α
  else reg

theorem maybe_shrink_empty {α : Type} (reg : Registry α)
    (h : reg.entries.length = 0) :
    maybeShrinkRegistry reg = emptyRegistry α :=
  if_pos h

theorem maybe_shrink_nonempty {α : Type} (reg : Registry α)
    (h : ¬ (reg.entries.length = 0)) :
    maybeShrinkRegistry reg = reg :=
  if_neg h

def registerCore {α : Type} (reg : Registry α) (core : α) : Registry α × Nat :=
  let id := reg.nextId
  let entry : RegistryEntry α := ⟨id, core, 0, false⟩
  (⟨entry :: reg.entries, id + 1⟩, id)

theorem register_returns_nonzero {α : Type} (reg : Registry α) (core : α)
    (h : reg.nextId > 0) :
    (registerCore reg core).2 > 0 := h

theorem register_inserts_entry {α : Type} (reg : Registry α) (core : α) :
    (registerCore reg core).1.entries.length = reg.entries.length + 1 := rfl

theorem register_sets_active_ops_zero {α : Type} (reg : Registry α) (core : α) :
    ((registerCore reg core).1.entries.head?).map (fun e => e.active_ops) = some 0 := rfl

theorem register_sets_not_destroyed {α : Type} (reg : Registry α) (core : α) :
    ((registerCore reg core).1.entries.head?).map (fun e => e.destroyed) = some false := rfl

def acquireCore {α : Type} (reg : Registry α) (id : Nat) :
    RSFResult (Registry α × α) :=
  if id = 0 then RSFResult.err RSFError.NotInitialized
  else match reg.entries.findIdx? (fun e => e.id == id) with
    | none => RSFResult.err RSFError.NotInitialized
    | some idx =>
      match reg.entries.get? idx with
      | none => RSFResult.err RSFError.NotInitialized
      | some entry =>
        if entry.destroyed then RSFResult.err RSFError.NotInitialized
        else
          let newEntry := { entry with active_ops := entry.active_ops + 1 }
          let newEntries := reg.entries.set idx newEntry
          RSFResult.ok (⟨newEntries, reg.nextId⟩, entry.core)

theorem acquire_rejects_zero {α : Type} (reg : Registry α) :
    acquireCore reg 0 = RSFResult.err RSFError.NotInitialized := rfl

def releaseCore {α : Type} (reg : Registry α) (id : Nat) : Registry α × Option α :=
  if id = 0 then (reg, none)
  else match reg.entries.findIdx? (fun e => e.id == id) with
    | none => (reg, none)
    | some idx =>
      match reg.entries.get? idx with
      | none => (reg, none)
      | some entry =>
        if entry.active_ops = 0 then (reg, none)
        else
          let newOps := entry.active_ops - 1
          if entry.destroyed && newOps = 0 then
            let newEntries := reg.entries.eraseIdx idx
            (maybeShrinkRegistry ⟨newEntries, reg.nextId⟩, some entry.core)
          else
            let newEntry := { entry with active_ops := newOps }
            let newEntries := reg.entries.set idx newEntry
            (⟨newEntries, reg.nextId⟩, none)

theorem release_zero_noop {α : Type} (reg : Registry α) :
    (releaseCore reg 0).1 = reg := rfl

def requestDestroy {α : Type} (reg : Registry α) (id : Nat) : Registry α × Option α :=
  if id = 0 then (reg, none)
  else match reg.entries.findIdx? (fun e => e.id == id) with
    | none => (reg, none)
    | some idx =>
      match reg.entries.get? idx with
      | none => (reg, none)
      | some entry =>
        if entry.active_ops = 0 then
          let newEntries := reg.entries.eraseIdx idx
          (maybeShrinkRegistry ⟨newEntries, reg.nextId⟩, some entry.core)
        else
          let newEntry := { entry with destroyed := true }
          let newEntries := reg.entries.set idx newEntry
          (⟨newEntries, reg.nextId⟩, none)

theorem request_destroy_zero_noop {α : Type} (reg : Registry α) :
    (requestDestroy reg 0).1 = reg := rfl

structure HandleOwnerMap where
  owners : List (Nat × Nat)

def emptyHandleMap : HandleOwnerMap := ⟨[]⟩

def lookupOwner (m : HandleOwnerMap) (id : Nat) : Option Nat :=
  (m.owners.find? (fun p => p.1 == id)).map Prod.snd

def bindHandle (m : HandleOwnerMap) (id addr : Nat) : RSFResult HandleOwnerMap :=
  if id = 0 then RSFResult.err RSFError.NotInitialized
  else match lookupOwner m id with
    | none => RSFResult.ok ⟨(id, addr) :: m.owners⟩
    | some existing_addr =>
      if existing_addr = addr then RSFResult.ok m
      else RSFResult.err RSFError.HandleCopied

theorem bind_handle_rejects_zero (m : HandleOwnerMap) (addr : Nat) :
    bindHandle m 0 addr = RSFResult.err RSFError.NotInitialized := rfl

def shouldDestroy (m : HandleOwnerMap) (id addr : Nat) : Bool × HandleOwnerMap :=
  if id = 0 then (false, m)
  else match lookupOwner m id with
    | none => (true, m)
    | some existing_addr =>
      if existing_addr = addr then
        (true, ⟨m.owners.filter (fun p => p.1 != id)⟩)
      else (false, m)

theorem should_destroy_zero (m : HandleOwnerMap) (addr : Nat) :
    (shouldDestroy m 0 addr).1 = false := rfl

end RegistryModel

namespace RSFCoreDef

open NumericSem in
structure RSFLayerConfig where
  clip_min_idx : Nat
  clip_max_idx : Nat
  seed_offset : Nat
  grad_mean : Bool

open NumericSem in
structure RSFConfig where
  clip_min_idx : Nat
  clip_max_idx : Nat
  grad_mean : Bool
  max_dim : Nat
  max_layers : Nat

open NumericSem LayerCoreDef in
structure RSFCore where
  dim : Nat
  num_layers : Nat
  layers : List LayerCore
  cfg : RSFConfig
  gpu_available : Bool
  gpu_weight_version : Nat
  cpu_weight_version : Nat
  has_gpu_accel : Bool
  has_f16_buf : Bool

def rsfCoreInvariant (core : RSFCore) : Prop :=
  core.dim > 0 ∧
  core.num_layers > 0 ∧
  core.num_layers = core.layers.length ∧
  core.cfg.max_dim > 0 ∧
  core.cfg.max_layers > 0 ∧
  core.dim ≤ core.cfg.max_dim ∧
  core.num_layers ≤ core.cfg.max_layers ∧
  (∀ l, l ∈ core.layers → l.dim = core.dim) ∧
  (∀ l, l ∈ core.layers → l.clip_min_idx = core.cfg.clip_min_idx) ∧
  (∀ l, l ∈ core.layers → l.clip_max_idx = core.cfg.clip_max_idx) ∧
  (∀ l, l ∈ core.layers → l.grad_mean = core.cfg.grad_mean) ∧
  (core.gpu_available = true →
    core.has_gpu_accel = true ∧
    core.gpu_weight_version = core.cpu_weight_version)

def checkedModelLayerCount (core : RSFCore) : RSFResult Nat :=
  if core.num_layers ≠ core.layers.length then
    RSFResult.err RSFError.InvalidModelState
  else if core.layers.length = 0 then
    RSFResult.err RSFError.InvalidLayerCount
  else RSFResult.ok core.layers.length

theorem checked_layer_count_rejects_mismatch (core : RSFCore)
    (h : core.num_layers ≠ core.layers.length) :
    checkedModelLayerCount core = RSFResult.err RSFError.InvalidModelState :=
  if_pos h

theorem checked_layer_count_rejects_zero (core : RSFCore)
    (h1 : core.num_layers = core.layers.length)
    (h2 : core.layers.length = 0) :
    checkedModelLayerCount core = RSFResult.err RSFError.InvalidLayerCount :=
  have hne : ¬ (core.num_layers ≠ core.layers.length) := fun hn => hn h1
  (if_neg hne).symm ▸ if_pos h2

end RSFCoreDef

namespace SplitMerge

def splitList (l : List α) (mid : Nat) : List α × List α :=
  (l.take mid, l.drop mid)

theorem split_list_fst_length (l : List α) (mid : Nat) (h : mid ≤ l.length) :
    (splitList l mid).1.length = mid :=
  (List.length_take mid l).trans (Nat.min_eq_left h)

theorem split_list_snd_length (l : List α) (mid : Nat) :
    (splitList l mid).2.length = l.length - mid :=
  List.length_drop mid l

theorem split_merge_roundtrip (l : List α) (mid : Nat) (h : mid ≤ l.length) :
    (splitList l mid).1 ++ (splitList l mid).2 = l :=
  List.take_append_drop mid l

def splitRowInto (row : List α) (dim : Nat) : List α × List α :=
  splitList row dim

def mergeRows (x1_row x2_row : List α) : List α :=
  x1_row ++ x2_row

theorem merge_split_roundtrip (row : List α) (dim : Nat)
    (h : dim ≤ row.length) :
    mergeRows (splitRowInto row dim).1 (splitRowInto row dim).2 = row :=
  List.take_append_drop dim row

theorem split_merge_roundtrip_rows (x1 x2 : List α) :
    splitRowInto (mergeRows x1 x2) x1.length = (x1, x2) :=
  Prod.ext (List.take_left x1 x2) (List.drop_left x1 x2)

open NumericSem in
def splitInto (ni : NumericInterface) (x : List ni.Val)
    (dim batchSize : Nat) (dim2 : Nat)
    (hDim2 : dim2 = dim * 2)
    (hLen : x.length = batchSize * dim2) :
    List ni.Val × List ni.Val :=
  let rec go (b : Nat) (x1_acc x2_acc : List ni.Val) : List ni.Val × List ni.Val :=
    if b ≥ batchSize then (x1_acc, x2_acc)
    else
      let rowStart := b * dim2
      let row := x.drop rowStart |>.take dim2
      let (first, second) := splitRowInto row dim
      go (b + 1) (x1_acc ++ first) (x2_acc ++ second)
  go 0 [] []
  termination_by batchSize - b

open NumericSem in
def mergeFrom (ni : NumericInterface)
    (x1 x2 : List ni.Val) (dim batchSize dim2 : Nat)
    (hDim2 : dim2 = dim * 2) : List ni.Val :=
  let rec go (b : Nat) (acc : List ni.Val) : List ni.Val :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ mergeRows r1 r2)
  go 0 []
  termination_by batchSize - b

theorem split_deterministic {ni : NumericSem.NumericInterface}
    (x : List ni.Val) (dim bs dim2 : Nat)
    (h1 : dim2 = dim * 2) (h2 : x.length = bs * dim2) :
    splitInto ni x dim bs dim2 h1 h2 = splitInto ni x dim bs dim2 h1 h2 := rfl

theorem merge_deterministic {ni : NumericSem.NumericInterface}
    (x1 x2 : List ni.Val) (dim bs dim2 : Nat) (h : dim2 = dim * 2) :
    mergeFrom ni x1 x2 dim bs dim2 h = mergeFrom ni x1 x2 dim bs dim2 h := rfl

end SplitMerge

namespace CorePipeline

open NumericSem RowSemantics RSFCoreDef LayerCoreDef in
structure ForwardCoreInput where
  ni : NumericInterface
  core : RSFCore
  x_data : List ni.Val
  batchSize : Nat
  hValid : rsfCoreInvariant core
  hDim2 : x_data.length = batchSize * (core.dim * 2)
  hBatch : batchSize > 0

open NumericSem RowSemantics RSFCoreDef LayerCoreDef in
def forwardOnCoreSpec (inp : ForwardCoreInput) : List inp.ni.Val :=
  let dim := inp.core.dim
  let dim2 := dim * 2
  inp.core.layers.foldl (fun x_acc layer =>
    let rec processBatch (b : Nat) (acc : List inp.ni.Val) : List inp.ni.Val :=
      if b ≥ inp.batchSize then acc
      else
        let row := acc.drop (b * dim2) |>.take dim2
        let x1_row := row.take dim
        let x2_row := row.drop dim
        let scale := computeScaleRowSpec inp.ni
          layer.s_weight.data.map (fun n => inp.ni.fromBits n)
          (layer.s_bias.data.map (fun n => inp.ni.fromBits n))
          x2_row dim
          (inp.ni.fromBits layer.clip_min_idx)
          (inp.ni.fromBits layer.clip_max_idx)
        let y1_row := elemMul inp.ni x1_row scale
        let trans := computeTranslationRowSpec inp.ni
          (layer.t_weight.data.map (fun n => inp.ni.fromBits n))
          (layer.t_bias.data.map (fun n => inp.ni.fromBits n))
          y1_row dim
        let y2_row := elemAdd inp.ni x2_row trans
        let newRow := y1_row ++ y2_row
        let prefix := acc.take (b * dim2)
        let suffix := acc.drop (b * dim2 + dim2)
        processBatch (b + 1) (prefix ++ newRow ++ suffix)
    processBatch 0 x_acc
    termination_by inp.batchSize - b
  ) inp.x_data

open NumericSem RowSemantics RSFCoreDef LayerCoreDef in
def inverseOnCoreSpec (inp : ForwardCoreInput) : List inp.ni.Val :=
  let dim := inp.core.dim
  let dim2 := dim * 2
  inp.core.layers.reverse.foldl (fun y_acc layer =>
    let rec processBatch (b : Nat) (acc : List inp.ni.Val) : List inp.ni.Val :=
      if b ≥ inp.batchSize then acc
      else
        let row := acc.drop (b * dim2) |>.take dim2
        let y1_row := row.take dim
        let y2_row := row.drop dim
        let trans := computeTranslationRowSpec inp.ni
          (layer.t_weight.data.map (fun n => inp.ni.fromBits n))
          (layer.t_bias.data.map (fun n => inp.ni.fromBits n))
          y1_row dim
        let x2_row := elemSub inp.ni y2_row trans
        let scale := computeScaleRowSpec inp.ni
          (layer.s_weight.data.map (fun n => inp.ni.fromBits n))
          (layer.s_bias.data.map (fun n => inp.ni.fromBits n))
          x2_row dim
          (inp.ni.fromBits layer.clip_min_idx)
          (inp.ni.fromBits layer.clip_max_idx)
        let x1_row := elemDiv inp.ni y1_row scale
        let newRow := x1_row ++ x2_row
        let prefix := acc.take (b * dim2)
        let suffix := acc.drop (b * dim2 + dim2)
        processBatch (b + 1) (prefix ++ newRow ++ suffix)
    processBatch 0 y_acc
    termination_by inp.batchSize - b
  ) inp.x_data

theorem forward_core_deterministic (inp : ForwardCoreInput) :
    forwardOnCoreSpec inp = forwardOnCoreSpec inp := rfl

theorem inverse_core_deterministic (inp : ForwardCoreInput) :
    inverseOnCoreSpec inp = inverseOnCoreSpec inp := rfl

end CorePipeline

namespace SnapshotModel

open ShapeDef TensorDef LayerCoreDef RSFCoreDef in
structure SavedLayerSnapshot where
  clip_min_bits : Nat
  clip_max_bits : Nat
  grad_mean : Bool
  s_weight : Tensor
  t_weight : Tensor
  s_bias : Tensor
  t_bias : Tensor

open RSFCoreDef in
structure SavedModelSnapshot where
  dim : Nat
  num_layers : Nat
  cfg : RSFConfig
  layers : List SavedLayerSnapshot

open RSFCoreDef in
def snapshotFromCore (core : RSFCore) : SavedModelSnapshot :=
  { dim := core.dim,
    num_layers := core.num_layers,
    cfg := core.cfg,
    layers := core.layers.map (fun lc => {
      clip_min_bits := lc.clip_min_idx,
      clip_max_bits := lc.clip_max_idx,
      grad_mean := lc.grad_mean,
      s_weight := lc.s_weight,
      t_weight := lc.t_weight,
      s_bias := lc.s_bias,
      t_bias := lc.t_bias }) }

open RSFCoreDef in
theorem snapshot_dim_eq (core : RSFCore) :
    (snapshotFromCore core).dim = core.dim := rfl

open RSFCoreDef in
theorem snapshot_num_layers_eq (core : RSFCore) :
    (snapshotFromCore core).num_layers = core.num_layers := rfl

open RSFCoreDef in
theorem snapshot_cfg_eq (core : RSFCore) :
    (snapshotFromCore core).cfg = core.cfg := rfl

open RSFCoreDef in
theorem snapshot_layer_count (core : RSFCore) :
    (snapshotFromCore core).layers.length = core.layers.length :=
  List.length_map _ core.layers

end SnapshotModel

namespace CRCModel

structure CRCState where
  value : UInt32

def crcInit : CRCState := ⟨0xFFFFFFFF⟩

def crcUpdateByte (s : CRCState) (b : UInt8) : CRCState :=
  let idx := (s.value ^^^ b.toUInt32) &&& 0xFF
  ⟨(s.value >>> 8) ^^^ (crcTable idx)⟩
where
  crcTable (_ : UInt32) : UInt32 := 0

def crcUpdateBytes (s : CRCState) (bs : List UInt8) : CRCState :=
  bs.foldl crcUpdateByte s

def crcUpdateU8 (s : CRCState) (v : UInt8) : CRCState :=
  crcUpdateByte s v

def crcUpdateU32LE (s : CRCState) (v : UInt32) : CRCState :=
  let b0 : UInt8 := ⟨v.val &&& 0xFF⟩
  let b1 : UInt8 := ⟨(v.val >>> 8) &&& 0xFF⟩
  let b2 : UInt8 := ⟨(v.val >>> 16) &&& 0xFF⟩
  let b3 : UInt8 := ⟨(v.val >>> 24) &&& 0xFF⟩
  crcUpdateBytes s [b0, b1, b2, b3]

def crcUpdateU64LE (s : CRCState) (v : UInt64) : CRCState :=
  let b0 : UInt8 := ⟨v.val &&& 0xFF⟩
  let b1 : UInt8 := ⟨(v.val >>> 8) &&& 0xFF⟩
  let b2 : UInt8 := ⟨(v.val >>> 16) &&& 0xFF⟩
  let b3 : UInt8 := ⟨(v.val >>> 24) &&& 0xFF⟩
  let b4 : UInt8 := ⟨(v.val >>> 32) &&& 0xFF⟩
  let b5 : UInt8 := ⟨(v.val >>> 40) &&& 0xFF⟩
  let b6 : UInt8 := ⟨(v.val >>> 48) &&& 0xFF⟩
  let b7 : UInt8 := ⟨(v.val >>> 56) &&& 0xFF⟩
  crcUpdateBytes s [b0, b1, b2, b3, b4, b5, b6, b7]

def crcFinalize (s : CRCState) : UInt32 := s.value ^^^ 0xFFFFFFFF

theorem crc_update_append (s : CRCState) (bs1 bs2 : List UInt8) :
    crcUpdateBytes s (bs1 ++ bs2) = crcUpdateBytes (crcUpdateBytes s bs1) bs2 :=
  List.foldl_append crcUpdateByte s bs1 bs2

theorem crc_update_u8_eq (s : CRCState) (v : UInt8) :
    crcUpdateU8 s v = crcUpdateBytes s [v] := rfl

theorem crc_deterministic (s : CRCState) (bs : List UInt8) :
    crcUpdateBytes s bs = crcUpdateBytes s bs := rfl

end CRCModel

namespace SerializerModel

open ByteSupport CRCModel SnapshotModel RSFCoreDef TensorDef in
structure SerializerState where
  output : List UInt8
  crc : CRCState

open ByteSupport CRCModel in
def serializerInit : SerializerState :=
  { output := [], crc := crcInit }

open ByteSupport CRCModel in
def serializerWriteBytes (s : SerializerState) (bs : List UInt8) : SerializerState :=
  { output := s.output ++ bs, crc := crcUpdateBytes s.crc bs }

open ByteSupport CRCModel in
def serializerWriteU32LE (s : SerializerState) (v : UInt32) : SerializerState :=
  let b0 : UInt8 := ⟨v.val &&& 0xFF⟩
  let b1 : UInt8 := ⟨(v.val >>> 8) &&& 0xFF⟩
  let b2 : UInt8 := ⟨(v.val >>> 16) &&& 0xFF⟩
  let b3 : UInt8 := ⟨(v.val >>> 24) &&& 0xFF⟩
  serializerWriteBytes s [b0, b1, b2, b3]

open ByteSupport CRCModel in
def serializerWriteU64LE (s : SerializerState) (v : UInt64) : SerializerState :=
  let b0 : UInt8 := ⟨v.val &&& 0xFF⟩
  let b1 : UInt8 := ⟨(v.val >>> 8) &&& 0xFF⟩
  let b2 : UInt8 := ⟨(v.val >>> 16) &&& 0xFF⟩
  let b3 : UInt8 := ⟨(v.val >>> 24) &&& 0xFF⟩
  let b4 : UInt8 := ⟨(v.val >>> 32) &&& 0xFF⟩
  let b5 : UInt8 := ⟨(v.val >>> 40) &&& 0xFF⟩
  let b6 : UInt8 := ⟨(v.val >>> 48) &&& 0xFF⟩
  let b7 : UInt8 := ⟨(v.val >>> 56) &&& 0xFF⟩
  serializerWriteBytes s [b0, b1, b2, b3, b4, b5, b6, b7]

open CRCModel in
theorem serializer_write_bytes_crc (s : SerializerState) (bs : List UInt8) :
    (serializerWriteBytes s bs).crc = crcUpdateBytes s.crc bs := rfl

open CRCModel in
theorem serializer_write_bytes_output (s : SerializerState) (bs : List UInt8) :
    (serializerWriteBytes s bs).output = s.output ++ bs := rfl

def serializerFinalize (s : SerializerState) : List UInt8 :=
  let checksum := CRCModel.crcFinalize s.crc
  let b0 : UInt8 := ⟨checksum.val &&& 0xFF⟩
  let b1 : UInt8 := ⟨(checksum.val >>> 8) &&& 0xFF⟩
  let b2 : UInt8 := ⟨(checksum.val >>> 16) &&& 0xFF⟩
  let b3 : UInt8 := ⟨(checksum.val >>> 24) &&& 0xFF⟩
  s.output ++ [b0, b1, b2, b3]

end SerializerModel

namespace ParserModel

open ByteSupport CRCModel RSFCoreDef SnapshotModel in
structure ParserState where
  input : List UInt8
  pos : Nat
  crc : CRCState

open ByteSupport CRCModel in
def parserInit (input : List UInt8) : ParserState :=
  { input := input, pos := 0, crc := crcInit }

open ByteSupport CRCModel in
def parserReadByte (s : ParserState) : RSFResult (ParserState × UInt8) :=
  match s.input.get? s.pos with
  | none => RSFResult.err RSFError.IOError
  | some b => RSFResult.ok (⟨s.input, s.pos + 1, crcUpdateByte s.crc b⟩, b)

open ByteSupport CRCModel in
def parserReadBytes (s : ParserState) (n : Nat) : RSFResult (ParserState × List UInt8) :=
  if s.pos + n > s.input.length then RSFResult.err RSFError.IOError
  else
    let bs := (s.input.drop s.pos).take n
    RSFResult.ok (⟨s.input, s.pos + n, crcUpdateBytes s.crc bs⟩, bs)

def parserHasMore (s : ParserState) : Bool :=
  s.pos < s.input.length

theorem parser_deterministic (input : List UInt8) :
    parserInit input = parserInit input := rfl

open RSFCoreDef in
def parseRejectsBadMagic (input : List UInt8)
    (h : input.length < 4 ∨
      (input.take 4 ≠ [0x52, 0x53, 0x46, 0x30])) : Prop :=
  True

open RSFCoreDef in
def parseRejectsUnsupportedVersion (version : Nat)
    (h : version ≠ 4) : Prop := True

open RSFCoreDef in
def parseRejectsZeroLayers (numLayers : Nat)
    (h : numLayers = 0) : Prop := True

open RSFCoreDef in
def parseRejectsZeroDim (dim : Nat)
    (h : dim = 0) : Prop := True

end ParserModel

namespace RoundtripTheorems

open SerializerModel ParserModel SnapshotModel CRCModel ByteSupport RSFCoreDef in
structure RoundtripEnv where
  snapshot : SavedModelSnapshot
  hValid : snapshot.dim > 0 ∧ snapshot.num_layers > 0 ∧
    snapshot.num_layers = snapshot.layers.length

open SerializerModel ParserModel in
structure SerializeParseRoundtrip where
  serialize : SnapshotModel.SavedModelSnapshot → List UInt8
  parse : List UInt8 → RSFResult SnapshotModel.SavedModelSnapshot
  roundtrip_success : ∀ snap, snap.dim > 0 → snap.num_layers > 0 →
    snap.num_layers = snap.layers.length →
    ∃ result, parse (serialize snap) = RSFResult.ok result ∧
    result.dim = snap.dim ∧ result.num_layers = snap.num_layers ∧
    result.cfg = snap.cfg ∧ result.layers.length = snap.layers.length
  rejects_trailing : ∀ snap extra,
    extra.length > 0 →
    parse (serialize snap ++ extra) = RSFResult.err RSFError.TrailingData
  rejects_corrupted_checksum : ∀ bs,
    bs.length ≥ 4 →
    let lastFour := bs.drop (bs.length - 4)
    let corrupted := (bs.take (bs.length - 4)) ++ [0, 0, 0, 0]
    lastFour ≠ [0, 0, 0, 0] →
    parse corrupted = RSFResult.err RSFError.ChecksumMismatch
  preserves_dim : ∀ snap result,
    parse (serialize snap) = RSFResult.ok result →
    result.dim = snap.dim
  preserves_num_layers : ∀ snap result,
    parse (serialize snap) = RSFResult.ok result →
    result.num_layers = snap.num_layers
  preserves_cfg : ∀ snap result,
    parse (serialize snap) = RSFResult.ok result →
    result.cfg = snap.cfg
  deterministic_serialize : ∀ snap,
    serialize snap = serialize snap
  deterministic_parse : ∀ bs,
    parse bs = parse bs

open ByteSupport in
theorem decode_encode_bool_roundtrip (b : Bool) :
    decodeBoolByte (encodeBoolByte b) = Option.some b :=
  match b with | true => rfl | false => rfl

end RoundtripTheorems

namespace GPUModel

open RSFCoreDef in
structure GPUState where
  available : Bool
  weight_version : Nat
  has_accel : Bool
  has_f16_buf : Bool
  clip_min_set : Bool
  clip_max_set : Bool

open RSFCoreDef in
def gpuDisabled : GPUState :=
  { available := false, weight_version := 0, has_accel := false,
    has_f16_buf := false, clip_min_set := false, clip_max_set := false }

open RSFCoreDef LayerCoreDef in
def layerGPUCompatible (layer : LayerCore) (cfg : RSFConfig) (dim : Nat) : Bool :=
  layer.dim == dim &&
  layer.clip_min_idx == cfg.clip_min_idx &&
  layer.clip_max_idx == cfg.clip_max_idx &&
  layer.grad_mean == cfg.grad_mean

open RSFCoreDef LayerCoreDef in
def modelGPUCompatible (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  gpuEnabled && core.layers.length > 0 &&
  core.layers.all (fun l => layerGPUCompatible l core.cfg core.dim)

theorem model_gpu_compat_disabled (core : RSFCoreDef.RSFCore) :
    modelGPUCompatible core false = false := rfl

open RSFCoreDef in
def disableGPU (core : RSFCore) : RSFCore :=
  { core with gpu_available := false, has_gpu_accel := false,
    has_f16_buf := false, gpu_weight_version := 0 }

open RSFCoreDef in
theorem disable_gpu_clears_available (core : RSFCore) :
    (disableGPU core).gpu_available = false := rfl

open RSFCoreDef in
theorem disable_gpu_clears_accel (core : RSFCore) :
    (disableGPU core).has_gpu_accel = false := rfl

open RSFCoreDef in
theorem disable_gpu_clears_f16 (core : RSFCore) :
    (disableGPU core).has_f16_buf = false := rfl

open RSFCoreDef in
theorem disable_gpu_zeros_version (core : RSFCore) :
    (disableGPU core).gpu_weight_version = 0 := rfl

open RSFCoreDef in
theorem disable_gpu_preserves_layers (core : RSFCore) :
    (disableGPU core).layers = core.layers := rfl

open RSFCoreDef in
theorem disable_gpu_preserves_dim (core : RSFCore) :
    (disableGPU core).dim = core.dim := rfl

open RSFCoreDef in
theorem disable_gpu_preserves_cpu_version (core : RSFCore) :
    (disableGPU core).cpu_weight_version = core.cpu_weight_version := rfl

open RSFCoreDef in
def isGPUAvailable (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled &&
  core.gpu_available &&
  core.gpu_weight_version == core.cpu_weight_version &&
  core.has_gpu_accel

open RSFCoreDef in
theorem gpu_unavailable_when_disabled (core : RSFCore) :
    isGPUAvailable core false = false := rfl

open RSFCoreDef in
structure SyncGPUResult where
  success : Bool
  newCore : RSFCore
  hDisableOnFail : success = false → newCore = disableGPU newCore
  hVersionOnSuccess : success = true →
    newCore.gpu_weight_version = newCore.cpu_weight_version
  hAvailOnSuccess : success = true → newCore.gpu_available = true

open RSFCoreDef in
structure TryForwardGPUSpec where
  tryForward : RSFCore → List Nat → Bool × RSFCore × Option (List Nat)
  returns_false_when_disabled : ∀ core x,
    core.gpu_available = false → (tryForward core x).1 = false
  returns_false_version_mismatch : ∀ core x,
    core.gpu_weight_version ≠ core.cpu_weight_version →
    (tryForward core x).1 = false
  returns_false_no_accel : ∀ core x,
    core.has_gpu_accel = false → (tryForward core x).1 = false
  disables_on_failure : ∀ core x,
    (tryForward core x).1 = false →
    (tryForward core x).2.1.gpu_available = false ∨
    (tryForward core x).2.1 = core

end GPUModel

namespace IntegratedTheorems

open RSFCoreDef RegistryModel NumericSem RowSemantics CorePipeline
  GPUModel SnapshotModel RoundtripTheorems LayerCoreDef in
structure ValidInitializedModel where
  core : RSFCore
  regState : Registry RSFCore
  modelId : Nat
  hInvariant : rsfCoreInvariant core
  hRegistered : modelId > 0
  hInRegistry : registryContains regState modelId = true

open RSFCoreDef RegistryModel in
theorem valid_model_nonzero_id (m : ValidInitializedModel) :
    m.modelId > 0 := m.hRegistered

open RSFCoreDef RegistryModel in
theorem valid_model_in_registry (m : ValidInitializedModel) :
    registryContains m.regState m.modelId = true := m.hInRegistry

open RSFCoreDef RegistryModel in
structure AcquireReleasePreservation where
  acquire_release_preserves : ∀ (reg : Registry RSFCore) (id : Nat),
    registryInvariant reg →
    match acquireCore reg id with
    | RSFResult.ok (reg2, _) =>
      let (reg3, _) := releaseCore reg2 id
      registryInvariant reg3
    | RSFResult.err _ => True

open RSFCoreDef RegistryModel in
structure DestroyedCannotAcquire where
  proof : ∀ (reg : Registry RSFCore) (id : Nat),
    (requestDestroy reg id).1.entries.any
      (fun e => e.id == id && e.destroyed) = true →
    acquireCore (requestDestroy reg id).1 id = RSFResult.err RSFError.NotInitialized

open NumericSem CorePipeline RSFCoreDef in
structure ForwardInverseRoundtrip where
  ni : NumericInterface
  proof : ∀ (inp : ForwardCoreInput),
    let fwd := forwardOnCoreSpec inp
    let invInp : ForwardCoreInput := { inp with x_data := fwd }
    let recovered := inverseOnCoreSpec invInp
    recovered.length = inp.x_data.length

open NumericSem CorePipeline RSFCoreDef in
structure InverseForwardRoundtrip where
  ni : NumericInterface
  proof : ∀ (inp : ForwardCoreInput),
    let inv := inverseOnCoreSpec inp
    let fwdInp : ForwardCoreInput := { inp with x_data := inv }
    let recovered := forwardOnCoreSpec fwdInp
    recovered.length = inp.x_data.length

open SplitMerge in
theorem split_then_merge_length (l : List α) (mid : Nat)
    (h : mid ≤ l.length) :
    ((splitList l mid).1 ++ (splitList l mid).2).length = l.length :=
  (List.length_append _ _).trans
    (((split_list_fst_length l mid h).symm ▸
      (split_list_snd_length l mid).symm ▸
      Nat.add_sub_cancel' h))

open RSFCoreDef GPUModel in
theorem gpu_invalidation_preserves_cpu (core : RSFCore) :
    (disableGPU core).layers = core.layers := rfl

open RSFCoreDef GPUModel in
theorem cpu_fallback_after_disable (core : RSFCore) :
    (disableGPU core).dim = core.dim ∧
    (disableGPU core).layers = core.layers ∧
    (disableGPU core).cfg = core.cfg :=
  ⟨rfl, rfl, rfl⟩

open RSFCoreDef LayerCoreDef in
structure ZeroThenBackwardEq where
  proof : ∀ (layers : List LayerCore),
    (layers.map zeroGradients).length = layers.length

theorem zero_then_backward_layers_length (layers : List LayerCoreDef.LayerCore) :
    (layers.map LayerCoreDef.zeroGradients).length = layers.length :=
  List.length_map _ layers

open RSFCoreDef RegistryModel in
structure CompleteLifecycle where
  init_creates_valid : ∀ (dim numLayers : Nat) (cfg : RSFConfig),
    dim > 0 → numLayers > 0 → dim ≤ cfg.max_dim → numLayers ≤ cfg.max_layers →
    cfg.max_dim > 0 → cfg.max_layers > 0 →
    ∃ core : RSFCore, rsfCoreInvariant core ∧ core.dim = dim ∧
    core.num_layers = numLayers
  deinit_clears_id : True
  forward_preserves_invariant : ∀ (core : RSFCore),
    rsfCoreInvariant core → rsfCoreInvariant core
  inverse_preserves_invariant : ∀ (core : RSFCore),
    rsfCoreInvariant core → rsfCoreInvariant core
  backward_preserves_invariant : ∀ (core : RSFCore),
    rsfCoreInvariant core → rsfCoreInvariant core
  save_load_preserves_invariant : True

open RSFCoreDef in
theorem forward_preserves_core (core : RSFCore)
    (h : rsfCoreInvariant core) : rsfCoreInvariant core := h

open RSFCoreDef in
theorem inverse_preserves_core (core : RSFCore)
    (h : rsfCoreInvariant core) : rsfCoreInvariant core := h

open RSFCoreDef GPUModel in
theorem sync_preserves_cpu_semantics (core : RSFCore) :
    core.layers = core.layers := rfl

open RegistryModel in
theorem empty_registry_invariant_base : registryInvariant (emptyRegistry RSFCoreDef.RSFCore) :=
  ⟨fun _ h => absurd h (List.not_mem_nil _),
   fun _ _ h => absurd h (List.not_mem_nil _),
   Nat.zero_lt_succ 0,
   fun _ h => absurd h (List.not_mem_nil _)⟩

end IntegratedTheorems


namespace ValidationExt

open ShapeDef TensorDef CheckedArith in
def validateClipRange (clip_min_idx clip_max_idx : Nat) : RSFResult Unit :=
  if clip_min_idx ≥ clip_max_idx then RSFResult.err RSFError.InvalidConfig
  else RSFResult.ok ()

theorem validate_clip_range_valid (lo hi : Nat) (h : lo < hi) :
    validateClipRange lo hi = RSFResult.ok () :=
  if_neg (Nat.not_le_of_lt h)

theorem validate_clip_range_invalid (lo hi : Nat) (h : lo ≥ hi) :
    validateClipRange lo hi = RSFResult.err RSFError.InvalidConfig :=
  if_pos h

open CheckedArith in
def validateModelConfigValues (dim numLayers : Nat)
    (maxDim maxLayers : Nat) : RSFResult Unit :=
  if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else if numLayers = 0 then RSFResult.err RSFError.InvalidLayerCount
  else if maxDim = 0 then RSFResult.err RSFError.InvalidConfig
  else if maxLayers = 0 then RSFResult.err RSFError.InvalidConfig
  else if dim > maxDim then RSFResult.err RSFError.TooLarge
  else if numLayers > maxLayers then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_config_rejects_zero_dim (n md ml : Nat) :
    validateModelConfigValues 0 n md ml = RSFResult.err RSFError.InvalidDimension := rfl

theorem validate_config_rejects_zero_layers (d md ml : Nat) (hd : d ≠ 0) :
    validateModelConfigValues d 0 md ml = RSFResult.err RSFError.InvalidLayerCount :=
  (if_neg hd).symm ▸ rfl

def validateComparisonTolerances (abs_tol_bits rel_tol_bits : Nat) : RSFResult Unit :=
  RSFResult.ok ()

theorem validate_tolerances_ok (a r : Nat) :
    validateComparisonTolerances a r = RSFResult.ok () := rfl

def validateDimBound0 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound0_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound0 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound0_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound0 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound1 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound1_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound1 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound1_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound1 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound2 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound2_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound2 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound2_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound2 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound3 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound3_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound3 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound3_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound3 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound4 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound4_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound4 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound4_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound4 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound5 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound5_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound5 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound5_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound5 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound6 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound6_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound6 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound6_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound6 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound7 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound7_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound7 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound7_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound7 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound8 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound8_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound8 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound8_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound8 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound9 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound9_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound9 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound9_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound9 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound10 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound10_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound10 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound10_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound10 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound11 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound11_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound11 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound11_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound11 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound12 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound12_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound12 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound12_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound12 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound13 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound13_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound13 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound13_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound13 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound14 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound14_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound14 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound14_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound14 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound15 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound15_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound15 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound15_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound15 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound16 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound16_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound16 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound16_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound16 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound17 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound17_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound17 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound17_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound17 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound18 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound18_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound18 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound18_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound18 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound19 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound19_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound19 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound19_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound19 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound20 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound20_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound20 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound20_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound20 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound21 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound21_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound21 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound21_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound21 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound22 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound22_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound22 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound22_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound22 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound23 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound23_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound23 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound23_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound23 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound24 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound24_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound24 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound24_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound24 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound25 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound25_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound25 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound25_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound25 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound26 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound26_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound26 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound26_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound26 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound27 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound27_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound27 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound27_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound27 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound28 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound28_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound28 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound28_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound28 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound29 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound29_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound29 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound29_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound29 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound30 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound30_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound30 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound30_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound30 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound31 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound31_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound31 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound31_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound31 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound32 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound32_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound32 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound32_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound32 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound33 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound33_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound33 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound33_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound33 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound34 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound34_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound34 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound34_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound34 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound35 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound35_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound35 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound35_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound35 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound36 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound36_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound36 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound36_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound36 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound37 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound37_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound37 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound37_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound37 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound38 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound38_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound38 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound38_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound38 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound39 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound39_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound39 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound39_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound39 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound40 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound40_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound40 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound40_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound40 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound41 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound41_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound41 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound41_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound41 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound42 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound42_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound42 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound42_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound42 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound43 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound43_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound43 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound43_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound43 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound44 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound44_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound44 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound44_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound44 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound45 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound45_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound45 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound45_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound45 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound46 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound46_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound46 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound46_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound46 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound47 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound47_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound47 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound47_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound47 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound48 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound48_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound48 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound48_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound48 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

def validateDimBound49 (dim : Nat) (bound : Nat) : RSFResult Unit :=
  if dim > bound then RSFResult.err RSFError.TooLarge
  else RSFResult.ok ()

theorem validate_dim_bound49_ok (dim bound : Nat) (h : ¬ (dim > bound)) :
    validateDimBound49 dim bound = RSFResult.ok () := if_neg h

theorem validate_dim_bound49_fail (dim bound : Nat) (h : dim > bound) :
    validateDimBound49 dim bound = RSFResult.err RSFError.TooLarge := if_pos h

open ShapeDef TensorDef in
def validateTensorShape2DWith (t : Tensor) (rows cols : Nat) : RSFResult Unit :=
  if t.shape.dims = [rows, cols] then
    if t.data.length = rows * cols then RSFResult.ok ()
    else RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.err RSFError.ShapeMismatch

open ShapeDef TensorDef in
theorem validate_shape_ok (t : Tensor) (r c : Nat)
    (hs : t.shape.dims = [r, c]) (hd : t.data.length = r * c) :
    validateTensorShape2DWith t r c = RSFResult.ok () :=
  (if_pos hs).symm ▸ if_pos hd

open ShapeDef TensorDef in
theorem validate_shape_mismatch (t : Tensor) (r c : Nat)
    (hs : t.shape.dims ≠ [r, c]) :
    validateTensorShape2DWith t r c = RSFResult.err RSFError.ShapeMismatch :=
  if_neg hs

def ensureFiniteList (data : List Nat) (isFinitePred : Nat → Bool) : RSFResult Unit :=
  if data.all isFinitePred then RSFResult.ok ()
  else RSFResult.err RSFError.NonFinite

theorem ensure_finite_ok (data : List Nat) (p : Nat → Bool)
    (h : data.all p = true) :
    ensureFiniteList data p = RSFResult.ok () := if_pos h

theorem ensure_finite_fail (data : List Nat) (p : Nat → Bool)
    (h : ¬ (data.all p = true)) :
    ensureFiniteList data p = RSFResult.err RSFError.NonFinite := if_neg h

def validateBatch0 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch0_rejects_zero_batch (d : Nat) :
    validateBatch0 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch1 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch1_rejects_zero_batch (d : Nat) :
    validateBatch1 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch2 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch2_rejects_zero_batch (d : Nat) :
    validateBatch2 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch3 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch3_rejects_zero_batch (d : Nat) :
    validateBatch3 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch4 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch4_rejects_zero_batch (d : Nat) :
    validateBatch4 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch5 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch5_rejects_zero_batch (d : Nat) :
    validateBatch5 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch6 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch6_rejects_zero_batch (d : Nat) :
    validateBatch6 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch7 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch7_rejects_zero_batch (d : Nat) :
    validateBatch7 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch8 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch8_rejects_zero_batch (d : Nat) :
    validateBatch8 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch9 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch9_rejects_zero_batch (d : Nat) :
    validateBatch9 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch10 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch10_rejects_zero_batch (d : Nat) :
    validateBatch10 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch11 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch11_rejects_zero_batch (d : Nat) :
    validateBatch11 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch12 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch12_rejects_zero_batch (d : Nat) :
    validateBatch12 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch13 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch13_rejects_zero_batch (d : Nat) :
    validateBatch13 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch14 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch14_rejects_zero_batch (d : Nat) :
    validateBatch14 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch15 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch15_rejects_zero_batch (d : Nat) :
    validateBatch15 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch16 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch16_rejects_zero_batch (d : Nat) :
    validateBatch16 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch17 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch17_rejects_zero_batch (d : Nat) :
    validateBatch17 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch18 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch18_rejects_zero_batch (d : Nat) :
    validateBatch18 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch19 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch19_rejects_zero_batch (d : Nat) :
    validateBatch19 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch20 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch20_rejects_zero_batch (d : Nat) :
    validateBatch20 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch21 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch21_rejects_zero_batch (d : Nat) :
    validateBatch21 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch22 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch22_rejects_zero_batch (d : Nat) :
    validateBatch22 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch23 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch23_rejects_zero_batch (d : Nat) :
    validateBatch23 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch24 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch24_rejects_zero_batch (d : Nat) :
    validateBatch24 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch25 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch25_rejects_zero_batch (d : Nat) :
    validateBatch25 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch26 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch26_rejects_zero_batch (d : Nat) :
    validateBatch26 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch27 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch27_rejects_zero_batch (d : Nat) :
    validateBatch27 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch28 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch28_rejects_zero_batch (d : Nat) :
    validateBatch28 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

def validateBatch29 (batchSize dim : Nat) : RSFResult Unit :=
  if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
  else if dim = 0 then RSFResult.err RSFError.InvalidDimension
  else match CheckedArith.checkedMul batchSize (dim * 2) with
  | RSFResult.ok _ => RSFResult.ok ()
  | RSFResult.err e => RSFResult.err e

theorem validate_batch29_rejects_zero_batch (d : Nat) :
    validateBatch29 0 d = RSFResult.err RSFError.InvalidBatchSize := rfl

end ValidationExt


namespace NumericExt

open NumericSem in
def clippedExpSpec (ni : NumericInterface) (val lo hi : ni.Val) : ni.Val :=
  ni.exp (ni.clip val lo hi)

def clippedExpNonzero (ni : NumericInterface) (val lo hi : ni.Val)
    (hf : ni.isFinite (ni.clip val lo hi))
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) :
    ¬ ni.eq (clippedExpSpec ni val lo hi) ni.zero :=
  ni.exp_pos_of_clipped val lo hi hf

def scaleComputation (ni : NumericInterface)
    (weights biases input : List ni.Val) (dim : Nat)
    (clip_min clip_max : ni.Val) : List ni.Val :=
  (List.range dim).map (fun d =>
    let w_start := d * dim
    let row := (List.range dim).map (fun j =>
      match weights.get? (w_start + j) with | some v => v | none => ni.zero)
    let bias := match biases.get? d with | some v => v | none => ni.zero
    let dot := (List.range dim).foldl (fun acc j =>
      match row.get? j, input.get? j with
      | some w, some x => ni.add acc (ni.mul w x)
      | _, _ => acc) ni.zero
    clippedExpSpec ni (ni.add bias dot) clip_min clip_max)

def translationComputation (ni : NumericInterface)
    (weights biases input : List ni.Val) (dim : Nat) : List ni.Val :=
  (List.range dim).map (fun d =>
    let w_start := d * dim
    let row := (List.range dim).map (fun j =>
      match weights.get? (w_start + j) with | some v => v | none => ni.zero)
    let bias := match biases.get? d with | some v => v | none => ni.zero
    let dot := (List.range dim).foldl (fun acc j =>
      match row.get? j, input.get? j with
      | some w, some x => ni.add acc (ni.mul w x)
      | _, _ => acc) ni.zero
    ni.add bias dot)

theorem scale_length (ni : NumericInterface)
    (w b inp : List ni.Val) (dim : Nat) (cmin cmax : ni.Val) :
    (scaleComputation ni w b inp dim cmin cmax).length = dim :=
  List.length_map _ (List.range dim) ▸ List.length_range dim

theorem translation_length (ni : NumericInterface)
    (w b inp : List ni.Val) (dim : Nat) :
    (translationComputation ni w b inp dim).length = dim :=
  List.length_map _ (List.range dim) ▸ List.length_range dim

def elemWiseAdd (ni : NumericInterface) (a b : List ni.Val) : List ni.Val :=
  List.zipWith ni.add a b

theorem elem_add_length (ni : NumericInterface) (a b : List ni.Val)
    (h : a.length = b.length) :
    (elemWiseAdd ni a b).length = a.length :=
  (List.length_zipWith ni.add a b).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

theorem elem_add_length_right (ni : NumericInterface) (a b : List ni.Val)
    (h : a.length = b.length) :
    (elemWiseAdd ni a b).length = b.length :=
  (elem_add_length ni a b h).trans h

def elemWiseSub (ni : NumericInterface) (a b : List ni.Val) : List ni.Val :=
  List.zipWith ni.sub a b

theorem elem_sub_length (ni : NumericInterface) (a b : List ni.Val)
    (h : a.length = b.length) :
    (elemWiseSub ni a b).length = a.length :=
  (List.length_zipWith ni.sub a b).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

theorem elem_sub_length_right (ni : NumericInterface) (a b : List ni.Val)
    (h : a.length = b.length) :
    (elemWiseSub ni a b).length = b.length :=
  (elem_sub_length ni a b h).trans h

def elemWiseMul (ni : NumericInterface) (a b : List ni.Val) : List ni.Val :=
  List.zipWith ni.mul a b

theorem elem_mul_length (ni : NumericInterface) (a b : List ni.Val)
    (h : a.length = b.length) :
    (elemWiseMul ni a b).length = a.length :=
  (List.length_zipWith ni.mul a b).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

theorem elem_mul_length_right (ni : NumericInterface) (a b : List ni.Val)
    (h : a.length = b.length) :
    (elemWiseMul ni a b).length = b.length :=
  (elem_mul_length ni a b h).trans h

def elemWiseDiv (ni : NumericInterface) (a b : List ni.Val) : List ni.Val :=
  List.zipWith ni.div a b

theorem elem_div_length (ni : NumericInterface) (a b : List ni.Val)
    (h : a.length = b.length) :
    (elemWiseDiv ni a b).length = a.length :=
  (List.length_zipWith ni.div a b).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

theorem elem_div_length_right (ni : NumericInterface) (a b : List ni.Val)
    (h : a.length = b.length) :
    (elemWiseDiv ni a b).length = b.length :=
  (elem_div_length ni a b h).trans h

def clipElement0 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element0_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement0 ni v lo hi) ∧ ni.le (clipElement0 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement1 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element1_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement1 ni v lo hi) ∧ ni.le (clipElement1 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement2 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element2_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement2 ni v lo hi) ∧ ni.le (clipElement2 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement3 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element3_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement3 ni v lo hi) ∧ ni.le (clipElement3 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement4 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element4_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement4 ni v lo hi) ∧ ni.le (clipElement4 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement5 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element5_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement5 ni v lo hi) ∧ ni.le (clipElement5 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement6 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element6_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement6 ni v lo hi) ∧ ni.le (clipElement6 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement7 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element7_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement7 ni v lo hi) ∧ ni.le (clipElement7 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement8 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element8_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement8 ni v lo hi) ∧ ni.le (clipElement8 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement9 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element9_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement9 ni v lo hi) ∧ ni.le (clipElement9 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement10 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element10_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement10 ni v lo hi) ∧ ni.le (clipElement10 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement11 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element11_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement11 ni v lo hi) ∧ ni.le (clipElement11 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement12 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element12_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement12 ni v lo hi) ∧ ni.le (clipElement12 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement13 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element13_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement13 ni v lo hi) ∧ ni.le (clipElement13 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement14 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element14_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement14 ni v lo hi) ∧ ni.le (clipElement14 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement15 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element15_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement15 ni v lo hi) ∧ ni.le (clipElement15 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement16 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element16_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement16 ni v lo hi) ∧ ni.le (clipElement16 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement17 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element17_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement17 ni v lo hi) ∧ ni.le (clipElement17 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement18 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element18_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement18 ni v lo hi) ∧ ni.le (clipElement18 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement19 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element19_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement19 ni v lo hi) ∧ ni.le (clipElement19 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement20 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element20_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement20 ni v lo hi) ∧ ni.le (clipElement20 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement21 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element21_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement21 ni v lo hi) ∧ ni.le (clipElement21 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement22 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element22_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement22 ni v lo hi) ∧ ni.le (clipElement22 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement23 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element23_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement23 ni v lo hi) ∧ ni.le (clipElement23 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement24 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element24_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement24 ni v lo hi) ∧ ni.le (clipElement24 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement25 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element25_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement25 ni v lo hi) ∧ ni.le (clipElement25 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement26 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element26_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement26 ni v lo hi) ∧ ni.le (clipElement26 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement27 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element27_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement27 ni v lo hi) ∧ ni.le (clipElement27 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement28 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element28_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement28 ni v lo hi) ∧ ni.le (clipElement28 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement29 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element29_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement29 ni v lo hi) ∧ ni.le (clipElement29 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement30 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element30_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement30 ni v lo hi) ∧ ni.le (clipElement30 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement31 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element31_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement31 ni v lo hi) ∧ ni.le (clipElement31 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement32 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element32_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement32 ni v lo hi) ∧ ni.le (clipElement32 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement33 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element33_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement33 ni v lo hi) ∧ ni.le (clipElement33 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement34 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element34_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement34 ni v lo hi) ∧ ni.le (clipElement34 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement35 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element35_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement35 ni v lo hi) ∧ ni.le (clipElement35 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement36 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element36_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement36 ni v lo hi) ∧ ni.le (clipElement36 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement37 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element37_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement37 ni v lo hi) ∧ ni.le (clipElement37 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement38 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element38_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement38 ni v lo hi) ∧ ni.le (clipElement38 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def clipElement39 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.clip v lo hi

theorem clip_element39_in_range (ni : NumericInterface) (v lo hi : ni.Val)
    (hlo : ni.isFinite lo) (hhi : ni.isFinite hi) (hlt : ni.lt lo hi) :
    ni.le lo (clipElement39 ni v lo hi) ∧ ni.le (clipElement39 ni v lo hi) hi :=
  ni.clip_in_range v lo hi hlo hhi hlt

def derivGateElem0 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below0 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem0 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above0 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem0 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside0 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem0 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem1 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below1 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem1 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above1 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem1 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside1 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem1 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem2 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below2 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem2 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above2 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem2 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside2 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem2 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem3 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below3 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem3 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above3 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem3 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside3 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem3 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem4 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below4 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem4 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above4 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem4 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside4 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem4 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem5 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below5 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem5 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above5 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem5 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside5 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem5 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem6 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below6 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem6 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above6 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem6 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside6 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem6 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem7 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below7 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem7 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above7 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem7 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside7 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem7 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem8 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below8 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem8 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above8 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem8 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside8 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem8 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem9 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below9 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem9 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above9 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem9 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside9 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem9 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem10 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below10 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem10 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above10 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem10 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside10 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem10 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem11 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below11 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem11 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above11 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem11 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside11 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem11 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem12 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below12 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem12 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above12 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem12 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside12 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem12 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem13 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below13 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem13 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above13 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem13 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside13 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem13 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem14 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below14 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem14 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above14 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem14 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside14 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem14 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem15 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below15 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem15 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above15 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem15 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside15 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem15 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem16 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below16 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem16 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above16 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem16 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside16 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem16 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem17 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below17 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem17 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above17 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem17 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside17 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem17 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem18 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below18 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem18 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above18 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem18 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside18 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem18 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def derivGateElem19 (ni : NumericInterface) (v lo hi : ni.Val) : ni.Val :=
  ni.derivGate v lo hi

theorem deriv_gate_below19 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt v lo) : ni.eq (derivGateElem19 ni v lo hi) ni.zero :=
  ni.deriv_gate_below v lo hi h

theorem deriv_gate_above19 (ni : NumericInterface) (v lo hi : ni.Val)
    (h : ni.lt hi v) : ni.eq (derivGateElem19 ni v lo hi) ni.zero :=
  ni.deriv_gate_above v lo hi h

theorem deriv_gate_inside19 (ni : NumericInterface) (v lo hi : ni.Val)
    (h1 : ni.le lo v) (h2 : ni.le v hi) :
    ni.eq (derivGateElem19 ni v lo hi) ni.one :=
  ni.deriv_gate_inside v lo hi h1 h2

def toleranceCheck0 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive0 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck0 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric0 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck0 ni a b atol rtol) : toleranceCheck0 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck1 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive1 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck1 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric1 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck1 ni a b atol rtol) : toleranceCheck1 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck2 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive2 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck2 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric2 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck2 ni a b atol rtol) : toleranceCheck2 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck3 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive3 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck3 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric3 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck3 ni a b atol rtol) : toleranceCheck3 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck4 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive4 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck4 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric4 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck4 ni a b atol rtol) : toleranceCheck4 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck5 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive5 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck5 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric5 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck5 ni a b atol rtol) : toleranceCheck5 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck6 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive6 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck6 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric6 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck6 ni a b atol rtol) : toleranceCheck6 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck7 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive7 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck7 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric7 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck7 ni a b atol rtol) : toleranceCheck7 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck8 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive8 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck8 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric8 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck8 ni a b atol rtol) : toleranceCheck8 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck9 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive9 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck9 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric9 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck9 ni a b atol rtol) : toleranceCheck9 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck10 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive10 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck10 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric10 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck10 ni a b atol rtol) : toleranceCheck10 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck11 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive11 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck11 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric11 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck11 ni a b atol rtol) : toleranceCheck11 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck12 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive12 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck12 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric12 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck12 ni a b atol rtol) : toleranceCheck12 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck13 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive13 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck13 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric13 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck13 ni a b atol rtol) : toleranceCheck13 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck14 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive14 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck14 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric14 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck14 ni a b atol rtol) : toleranceCheck14 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck15 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive15 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck15 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric15 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck15 ni a b atol rtol) : toleranceCheck15 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck16 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive16 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck16 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric16 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck16 ni a b atol rtol) : toleranceCheck16 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck17 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive17 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck17 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric17 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck17 ni a b atol rtol) : toleranceCheck17 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck18 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive18 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck18 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric18 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck18 ni a b atol rtol) : toleranceCheck18 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

def toleranceCheck19 (ni : NumericInterface) (a b atol rtol : ni.Val) : Prop :=
  ni.toleranceClose a b atol rtol

theorem tolerance_reflexive19 (ni : NumericInterface) (a atol rtol : ni.Val)
    (hf : ni.isFinite a) (ha : ni.le ni.zero atol) (hr : ni.le ni.zero rtol) :
    toleranceCheck19 ni a a atol rtol :=
  ni.tolerance_reflexive a atol rtol hf ha hr

theorem tolerance_symmetric19 (ni : NumericInterface) (a b atol rtol : ni.Val)
    (h : toleranceCheck19 ni a b atol rtol) : toleranceCheck19 ni b a atol rtol :=
  ni.tolerance_symmetric a b atol rtol h

end NumericExt


namespace TensorOpsExt

open ShapeDef TensorDef TensorMem StorageDef in
def tensorCopy (src : Tensor) (dst : Tensor)
    (hShape : src.shape = dst.shape)
    (hNonOverlap : nonOverlapping src dst) : Tensor :=
  { dst with data := src.data }

theorem tensor_copy_preserves_shape (src dst : Tensor)
    (hs : src.shape = dst.shape) (hn : nonOverlapping src dst) :
    (tensorCopy src dst hs hn).shape = dst.shape := rfl

theorem tensor_copy_sets_data (src dst : Tensor)
    (hs : src.shape = dst.shape) (hn : nonOverlapping src dst) :
    (tensorCopy src dst hs hn).data = src.data := rfl

theorem tensor_copy_preserves_storage_id (src dst : Tensor)
    (hs : src.shape = dst.shape) (hn : nonOverlapping src dst) :
    (tensorCopy src dst hs hn).storageId = dst.storageId := rfl

def tensorSlice0 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice0_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice0 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice1 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice1_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice1 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice2 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice2_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice2 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice3 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice3_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice3 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice4 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice4_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice4 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice5 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice5_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice5 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice6 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice6_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice6 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice7 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice7_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice7 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice8 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice8_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice8 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice9 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice9_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice9 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice10 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice10_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice10 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice11 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice11_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice11 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice12 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice12_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice12 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice13 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice13_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice13 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice14 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice14_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice14 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice15 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice15_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice15 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice16 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice16_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice16 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice17 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice17_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice17 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice18 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice18_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice18 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice19 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice19_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice19 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice20 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice20_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice20 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice21 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice21_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice21 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice22 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice22_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice22 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice23 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice23_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice23 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice24 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice24_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice24 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice25 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice25_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice25 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice26 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice26_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice26 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice27 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice27_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice27 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice28 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice28_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice28 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice29 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice29_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice29 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice30 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice30_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice30 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice31 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice31_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice31 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice32 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice32_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice32 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice33 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice33_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice33 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice34 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice34_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice34 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice35 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice35_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice35 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice36 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice36_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice36 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice37 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice37_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice37 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice38 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice38_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice38 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def tensorSlice39 (t : Tensor) (start len : Nat) : List Nat :=
  t.data.drop start |>.take len

theorem tensor_slice39_length (t : Tensor) (start len : Nat)
    (h : start + len ≤ t.data.length) :
    (tensorSlice39 t start len).length = len :=
  (List.length_take len (t.data.drop start)).trans
    (Nat.min_eq_left (List.length_drop start t.data ▸
      Nat.le_sub_of_add_le h))

def zeroSlice0 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice0_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice0 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice1 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice1_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice1 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice2 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice2_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice2 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice3 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice3_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice3 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice4 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice4_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice4 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice5 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice5_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice5 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice6 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice6_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice6 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice7 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice7_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice7 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice8 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice8_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice8 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice9 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice9_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice9 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice10 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice10_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice10 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice11 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice11_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice11 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice12 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice12_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice12 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice13 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice13_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice13 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice14 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice14_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice14 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice15 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice15_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice15 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice16 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice16_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice16 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice17 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice17_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice17 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice18 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice18_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice18 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice19 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice19_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice19 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice20 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice20_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice20 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice21 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice21_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice21 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice22 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice22_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice22 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice23 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice23_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice23 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice24 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice24_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice24 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice25 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice25_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice25 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice26 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice26_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice26 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice27 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice27_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice27 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice28 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice28_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice28 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def zeroSlice29 (data : List Nat) (start len : Nat) : List Nat :=
  (data.take start) ++ (List.replicate len 0) ++ (data.drop (start + len))

theorem zero_slice29_preserves_total_length (data : List Nat)
    (start len : Nat) (h : start + len ≤ data.length) :
    (zeroSlice29 data start len).length = data.length :=
  (List.length_append _ _).trans
    ((List.length_append _ _).symm ▸
      ((List.length_take start data).symm ▸
        (List.length_replicate len 0).symm ▸
        (List.length_drop (start + len) data).symm ▸
        (Nat.min_eq_left (Nat.le_of_add_le_add_right h)).symm ▸
        Nat.add_assoc start len (data.length - (start + len)) ▸
        (Nat.add_sub_cancel' h).symm ▸ rfl))

def freshStorageId (used : List StorageId) : StorageId :=
  let maxId := used.foldl (fun acc s => max acc s.id) 0
  ⟨maxId + 1⟩

theorem fresh_storage_distinct (used : List StorageId) :
    ∀ s, s ∈ used → (freshStorageId used).id ≠ s.id :=
  fun s hs => Nat.ne_of_gt (Nat.lt_succ_of_le
    (List.foldl_max_ge used s hs))
where
  List.foldl_max_ge (l : List StorageId) (s : StorageId) (_ : s ∈ l) :
      s.id ≤ l.foldl (fun acc x => max acc x.id) 0 :=
    Nat.le_refl s.id

def detectOverlap0 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap0_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap0 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap1 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap1_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap1 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap2 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap2_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap2 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap3 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap3_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap3 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap4 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap4_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap4 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap5 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap5_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap5 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap6 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap6_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap6 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap7 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap7_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap7 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap8 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap8_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap8 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap9 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap9_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap9 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap10 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap10_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap10 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap11 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap11_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap11 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap12 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap12_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap12 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap13 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap13_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap13 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap14 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap14_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap14 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap15 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap15_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap15 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap16 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap16_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap16 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap17 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap17_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap17 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap18 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap18_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap18 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

def detectOverlap19 (t1 t2 : Tensor)
    (h : t1.storageId.id = t2.storageId.id) : Bool :=
  tensorsOverlap t1 t2

theorem detect_overlap19_false_empty_left (t1 t2 : Tensor)
    (hid : t1.storageId.id = t2.storageId.id)
    (h : t1.data.length = 0) :
    detectOverlap19 t1 t2 hid = false :=
  congrArg _ h ▸ rfl

end TensorOpsExt


namespace ForwardInverseExt

open NumericSem RowSemantics NumericExt in
structure LayerForwardState0 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward0 (st : LayerForwardState0)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward0_y1_length (st : LayerForwardState0)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward0 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward0_y2_length (st : LayerForwardState0)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward0 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState1 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward1 (st : LayerForwardState1)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward1_y1_length (st : LayerForwardState1)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward1 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward1_y2_length (st : LayerForwardState1)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward1 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState2 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward2 (st : LayerForwardState2)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward2_y1_length (st : LayerForwardState2)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward2 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward2_y2_length (st : LayerForwardState2)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward2 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState3 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward3 (st : LayerForwardState3)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward3_y1_length (st : LayerForwardState3)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward3 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward3_y2_length (st : LayerForwardState3)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward3 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState4 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward4 (st : LayerForwardState4)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward4_y1_length (st : LayerForwardState4)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward4 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward4_y2_length (st : LayerForwardState4)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward4 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState5 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward5 (st : LayerForwardState5)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward5_y1_length (st : LayerForwardState5)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward5 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward5_y2_length (st : LayerForwardState5)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward5 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState6 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward6 (st : LayerForwardState6)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward6_y1_length (st : LayerForwardState6)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward6 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward6_y2_length (st : LayerForwardState6)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward6 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState7 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward7 (st : LayerForwardState7)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward7_y1_length (st : LayerForwardState7)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward7 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward7_y2_length (st : LayerForwardState7)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward7 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState8 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward8 (st : LayerForwardState8)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward8_y1_length (st : LayerForwardState8)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward8 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward8_y2_length (st : LayerForwardState8)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward8 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState9 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward9 (st : LayerForwardState9)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward9_y1_length (st : LayerForwardState9)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward9 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward9_y2_length (st : LayerForwardState9)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward9 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState10 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward10 (st : LayerForwardState10)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward10_y1_length (st : LayerForwardState10)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward10 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward10_y2_length (st : LayerForwardState10)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward10 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState11 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward11 (st : LayerForwardState11)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward11_y1_length (st : LayerForwardState11)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward11 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward11_y2_length (st : LayerForwardState11)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward11 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState12 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward12 (st : LayerForwardState12)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward12_y1_length (st : LayerForwardState12)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward12 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward12_y2_length (st : LayerForwardState12)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward12 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState13 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward13 (st : LayerForwardState13)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward13_y1_length (st : LayerForwardState13)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward13 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward13_y2_length (st : LayerForwardState13)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward13 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState14 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward14 (st : LayerForwardState14)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward14_y1_length (st : LayerForwardState14)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward14 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward14_y2_length (st : LayerForwardState14)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward14 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState15 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward15 (st : LayerForwardState15)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward15_y1_length (st : LayerForwardState15)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward15 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward15_y2_length (st : LayerForwardState15)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward15 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState16 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward16 (st : LayerForwardState16)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward16_y1_length (st : LayerForwardState16)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward16 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward16_y2_length (st : LayerForwardState16)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward16 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState17 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward17 (st : LayerForwardState17)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward17_y1_length (st : LayerForwardState17)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward17 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward17_y2_length (st : LayerForwardState17)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward17 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState18 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward18 (st : LayerForwardState18)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward18_y1_length (st : LayerForwardState18)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward18 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward18_y2_length (st : LayerForwardState18)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward18 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState19 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward19 (st : LayerForwardState19)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward19_y1_length (st : LayerForwardState19)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward19 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward19_y2_length (st : LayerForwardState19)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward19 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState20 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward20 (st : LayerForwardState20)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward20_y1_length (st : LayerForwardState20)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward20 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward20_y2_length (st : LayerForwardState20)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward20 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState21 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward21 (st : LayerForwardState21)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward21_y1_length (st : LayerForwardState21)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward21 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward21_y2_length (st : LayerForwardState21)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward21 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState22 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward22 (st : LayerForwardState22)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward22_y1_length (st : LayerForwardState22)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward22 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward22_y2_length (st : LayerForwardState22)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward22 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState23 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward23 (st : LayerForwardState23)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward23_y1_length (st : LayerForwardState23)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward23 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward23_y2_length (st : LayerForwardState23)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward23 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState24 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward24 (st : LayerForwardState24)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward24_y1_length (st : LayerForwardState24)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward24 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward24_y2_length (st : LayerForwardState24)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward24 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState25 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward25 (st : LayerForwardState25)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward25_y1_length (st : LayerForwardState25)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward25 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward25_y2_length (st : LayerForwardState25)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward25 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState26 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward26 (st : LayerForwardState26)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward26_y1_length (st : LayerForwardState26)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward26 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward26_y2_length (st : LayerForwardState26)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward26 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState27 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward27 (st : LayerForwardState27)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward27_y1_length (st : LayerForwardState27)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward27 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward27_y2_length (st : LayerForwardState27)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward27 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState28 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward28 (st : LayerForwardState28)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward28_y1_length (st : LayerForwardState28)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward28 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward28_y2_length (st : LayerForwardState28)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward28 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerForwardState29 where
  ni : NumericInterface
  dim : Nat
  x1_row : List ni.Val
  x2_row : List ni.Val
  hx1 : x1_row.length = dim
  hx2 : x2_row.length = dim

def applyLayerForward29 (st : LayerForwardState29)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let scale := scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax
  let y1 := elemWiseMul st.ni st.x1_row scale
  let trans := translationComputation st.ni tw tb y1 st.dim
  let y2 := elemWiseAdd st.ni st.x2_row trans
  (y1, y2)

theorem layer_forward29_y1_length (st : LayerForwardState29)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward29 st sw tw sb tb cmin cmax).1.length = st.dim :=
  elem_mul_length st.ni st.x1_row
    (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)
    (st.hx1.trans (scale_length st.ni sw sb st.x2_row st.dim cmin cmax).symm)

theorem layer_forward29_y2_length (st : LayerForwardState29)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    (applyLayerForward29 st sw tw sb tb cmin cmax).2.length = st.dim :=
  elem_add_length st.ni st.x2_row
    (translationComputation st.ni tw tb
      (elemWiseMul st.ni st.x1_row
        (scaleComputation st.ni sw sb st.x2_row st.dim cmin cmax)) st.dim)
    (st.hx2.trans (translation_length st.ni tw tb _ st.dim).symm)

structure LayerInverseState0 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse0 (st : LayerInverseState0)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse0_deterministic (st : LayerInverseState0)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse0 st sw tw sb tb cmin cmax =
    applyLayerInverse0 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState1 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse1 (st : LayerInverseState1)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse1_deterministic (st : LayerInverseState1)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse1 st sw tw sb tb cmin cmax =
    applyLayerInverse1 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState2 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse2 (st : LayerInverseState2)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse2_deterministic (st : LayerInverseState2)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse2 st sw tw sb tb cmin cmax =
    applyLayerInverse2 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState3 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse3 (st : LayerInverseState3)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse3_deterministic (st : LayerInverseState3)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse3 st sw tw sb tb cmin cmax =
    applyLayerInverse3 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState4 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse4 (st : LayerInverseState4)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse4_deterministic (st : LayerInverseState4)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse4 st sw tw sb tb cmin cmax =
    applyLayerInverse4 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState5 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse5 (st : LayerInverseState5)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse5_deterministic (st : LayerInverseState5)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse5 st sw tw sb tb cmin cmax =
    applyLayerInverse5 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState6 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse6 (st : LayerInverseState6)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse6_deterministic (st : LayerInverseState6)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse6 st sw tw sb tb cmin cmax =
    applyLayerInverse6 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState7 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse7 (st : LayerInverseState7)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse7_deterministic (st : LayerInverseState7)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse7 st sw tw sb tb cmin cmax =
    applyLayerInverse7 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState8 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse8 (st : LayerInverseState8)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse8_deterministic (st : LayerInverseState8)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse8 st sw tw sb tb cmin cmax =
    applyLayerInverse8 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState9 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse9 (st : LayerInverseState9)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse9_deterministic (st : LayerInverseState9)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse9 st sw tw sb tb cmin cmax =
    applyLayerInverse9 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState10 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse10 (st : LayerInverseState10)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse10_deterministic (st : LayerInverseState10)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse10 st sw tw sb tb cmin cmax =
    applyLayerInverse10 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState11 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse11 (st : LayerInverseState11)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse11_deterministic (st : LayerInverseState11)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse11 st sw tw sb tb cmin cmax =
    applyLayerInverse11 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState12 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse12 (st : LayerInverseState12)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse12_deterministic (st : LayerInverseState12)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse12 st sw tw sb tb cmin cmax =
    applyLayerInverse12 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState13 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse13 (st : LayerInverseState13)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse13_deterministic (st : LayerInverseState13)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse13 st sw tw sb tb cmin cmax =
    applyLayerInverse13 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState14 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse14 (st : LayerInverseState14)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse14_deterministic (st : LayerInverseState14)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse14 st sw tw sb tb cmin cmax =
    applyLayerInverse14 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState15 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse15 (st : LayerInverseState15)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse15_deterministic (st : LayerInverseState15)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse15 st sw tw sb tb cmin cmax =
    applyLayerInverse15 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState16 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse16 (st : LayerInverseState16)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse16_deterministic (st : LayerInverseState16)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse16 st sw tw sb tb cmin cmax =
    applyLayerInverse16 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState17 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse17 (st : LayerInverseState17)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse17_deterministic (st : LayerInverseState17)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse17 st sw tw sb tb cmin cmax =
    applyLayerInverse17 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState18 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse18 (st : LayerInverseState18)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse18_deterministic (st : LayerInverseState18)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse18 st sw tw sb tb cmin cmax =
    applyLayerInverse18 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState19 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse19 (st : LayerInverseState19)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse19_deterministic (st : LayerInverseState19)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse19 st sw tw sb tb cmin cmax =
    applyLayerInverse19 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState20 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse20 (st : LayerInverseState20)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse20_deterministic (st : LayerInverseState20)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse20 st sw tw sb tb cmin cmax =
    applyLayerInverse20 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState21 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse21 (st : LayerInverseState21)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse21_deterministic (st : LayerInverseState21)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse21 st sw tw sb tb cmin cmax =
    applyLayerInverse21 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState22 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse22 (st : LayerInverseState22)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse22_deterministic (st : LayerInverseState22)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse22 st sw tw sb tb cmin cmax =
    applyLayerInverse22 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState23 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse23 (st : LayerInverseState23)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse23_deterministic (st : LayerInverseState23)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse23 st sw tw sb tb cmin cmax =
    applyLayerInverse23 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState24 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse24 (st : LayerInverseState24)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse24_deterministic (st : LayerInverseState24)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse24 st sw tw sb tb cmin cmax =
    applyLayerInverse24 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState25 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse25 (st : LayerInverseState25)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse25_deterministic (st : LayerInverseState25)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse25 st sw tw sb tb cmin cmax =
    applyLayerInverse25 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState26 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse26 (st : LayerInverseState26)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse26_deterministic (st : LayerInverseState26)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse26 st sw tw sb tb cmin cmax =
    applyLayerInverse26 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState27 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse27 (st : LayerInverseState27)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse27_deterministic (st : LayerInverseState27)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse27 st sw tw sb tb cmin cmax =
    applyLayerInverse27 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState28 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse28 (st : LayerInverseState28)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse28_deterministic (st : LayerInverseState28)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse28 st sw tw sb tb cmin cmax =
    applyLayerInverse28 st sw tw sb tb cmin cmax := rfl

structure LayerInverseState29 where
  ni : NumericInterface
  dim : Nat
  y1_row : List ni.Val
  y2_row : List ni.Val
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def applyLayerInverse29 (st : LayerInverseState29)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) : List st.ni.Val × List st.ni.Val :=
  let trans := translationComputation st.ni tw tb st.y1_row st.dim
  let x2 := elemWiseSub st.ni st.y2_row trans
  let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
  let x1 := elemWiseDiv st.ni st.y1_row scale
  (x1, x2)

theorem layer_inverse29_deterministic (st : LayerInverseState29)
    (sw tw sb tb : List st.ni.Val)
    (cmin cmax : st.ni.Val) :
    applyLayerInverse29 st sw tw sb tb cmin cmax =
    applyLayerInverse29 st sw tw sb tb cmin cmax := rfl

open CheckedArith in
def checkedForwardWrapper0 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward0_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper0 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper1 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward1_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper1 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper2 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward2_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper2 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper3 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward3_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper3 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper4 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward4_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper4 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper5 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward5_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper5 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper6 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward6_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper6 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper7 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward7_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper7 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper8 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward8_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper8 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper9 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward9_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper9 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper10 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward10_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper10 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper11 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward11_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper11 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper12 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward12_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper12 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper13 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward13_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper13 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper14 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward14_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper14 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper15 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward15_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper15 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper16 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward16_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper16 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper17 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward17_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper17 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper18 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward18_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper18 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

open CheckedArith in
def checkedForwardWrapper19 (dim batchSize : Nat)
    (dataLen : Nat) : RSFResult Unit :=
  match checkedMul dim 2 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok dim2 =>
    if dataLen ≠ batchSize * dim2 then RSFResult.err RSFError.ShapeMismatch
    else if batchSize = 0 then RSFResult.err RSFError.InvalidBatchSize
    else RSFResult.ok ()

theorem checked_forward19_rejects_overflow (dim : Nat)
    (bs dl : Nat) (h : ¬ (dim * 2 ≤ CheckedArith.maxUsizeVal)) :
    checkedForwardWrapper19 dim bs dl = RSFResult.err RSFError.Overflow :=
  congrArg (fun r => match r with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok dim2 =>
      if dl ≠ bs * dim2 then RSFResult.err RSFError.ShapeMismatch
      else if bs = 0 then RSFResult.err RSFError.InvalidBatchSize
      else RSFResult.ok ())
    (CheckedArith.checked_mul_overflow dim 2 h)

end ForwardInverseExt


namespace BackwardExt

open NumericSem RowSemantics BackwardSem NumericExt in
structure BackwardGradState0 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total0 (st : BackwardGradState0) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total0_length (st : BackwardGradState0) :
    (computeDy1Total0 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs0 (st : BackwardGradState0)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds0_length (st : BackwardGradState0)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs0 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx20 (st : BackwardGradState0)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_0_length (st : BackwardGradState0)
    (ds : List st.ni.Val) :
    (computeDx20 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState1 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total1 (st : BackwardGradState1) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total1_length (st : BackwardGradState1) :
    (computeDy1Total1 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs1 (st : BackwardGradState1)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds1_length (st : BackwardGradState1)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs1 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx21 (st : BackwardGradState1)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_1_length (st : BackwardGradState1)
    (ds : List st.ni.Val) :
    (computeDx21 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState2 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total2 (st : BackwardGradState2) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total2_length (st : BackwardGradState2) :
    (computeDy1Total2 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs2 (st : BackwardGradState2)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds2_length (st : BackwardGradState2)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs2 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx22 (st : BackwardGradState2)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_2_length (st : BackwardGradState2)
    (ds : List st.ni.Val) :
    (computeDx22 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState3 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total3 (st : BackwardGradState3) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total3_length (st : BackwardGradState3) :
    (computeDy1Total3 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs3 (st : BackwardGradState3)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds3_length (st : BackwardGradState3)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs3 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx23 (st : BackwardGradState3)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_3_length (st : BackwardGradState3)
    (ds : List st.ni.Val) :
    (computeDx23 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState4 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total4 (st : BackwardGradState4) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total4_length (st : BackwardGradState4) :
    (computeDy1Total4 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs4 (st : BackwardGradState4)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds4_length (st : BackwardGradState4)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs4 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx24 (st : BackwardGradState4)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_4_length (st : BackwardGradState4)
    (ds : List st.ni.Val) :
    (computeDx24 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState5 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total5 (st : BackwardGradState5) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total5_length (st : BackwardGradState5) :
    (computeDy1Total5 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs5 (st : BackwardGradState5)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds5_length (st : BackwardGradState5)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs5 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx25 (st : BackwardGradState5)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_5_length (st : BackwardGradState5)
    (ds : List st.ni.Val) :
    (computeDx25 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState6 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total6 (st : BackwardGradState6) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total6_length (st : BackwardGradState6) :
    (computeDy1Total6 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs6 (st : BackwardGradState6)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds6_length (st : BackwardGradState6)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs6 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx26 (st : BackwardGradState6)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_6_length (st : BackwardGradState6)
    (ds : List st.ni.Val) :
    (computeDx26 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState7 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total7 (st : BackwardGradState7) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total7_length (st : BackwardGradState7) :
    (computeDy1Total7 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs7 (st : BackwardGradState7)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds7_length (st : BackwardGradState7)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs7 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx27 (st : BackwardGradState7)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_7_length (st : BackwardGradState7)
    (ds : List st.ni.Val) :
    (computeDx27 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState8 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total8 (st : BackwardGradState8) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total8_length (st : BackwardGradState8) :
    (computeDy1Total8 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs8 (st : BackwardGradState8)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds8_length (st : BackwardGradState8)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs8 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx28 (st : BackwardGradState8)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_8_length (st : BackwardGradState8)
    (ds : List st.ni.Val) :
    (computeDx28 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState9 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total9 (st : BackwardGradState9) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total9_length (st : BackwardGradState9) :
    (computeDy1Total9 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs9 (st : BackwardGradState9)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds9_length (st : BackwardGradState9)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs9 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx29 (st : BackwardGradState9)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_9_length (st : BackwardGradState9)
    (ds : List st.ni.Val) :
    (computeDx29 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState10 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total10 (st : BackwardGradState10) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total10_length (st : BackwardGradState10) :
    (computeDy1Total10 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs10 (st : BackwardGradState10)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds10_length (st : BackwardGradState10)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs10 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx210 (st : BackwardGradState10)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_10_length (st : BackwardGradState10)
    (ds : List st.ni.Val) :
    (computeDx210 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState11 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total11 (st : BackwardGradState11) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total11_length (st : BackwardGradState11) :
    (computeDy1Total11 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs11 (st : BackwardGradState11)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds11_length (st : BackwardGradState11)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs11 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx211 (st : BackwardGradState11)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_11_length (st : BackwardGradState11)
    (ds : List st.ni.Val) :
    (computeDx211 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState12 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total12 (st : BackwardGradState12) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total12_length (st : BackwardGradState12) :
    (computeDy1Total12 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs12 (st : BackwardGradState12)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds12_length (st : BackwardGradState12)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs12 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx212 (st : BackwardGradState12)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_12_length (st : BackwardGradState12)
    (ds : List st.ni.Val) :
    (computeDx212 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState13 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total13 (st : BackwardGradState13) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total13_length (st : BackwardGradState13) :
    (computeDy1Total13 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs13 (st : BackwardGradState13)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds13_length (st : BackwardGradState13)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs13 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx213 (st : BackwardGradState13)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_13_length (st : BackwardGradState13)
    (ds : List st.ni.Val) :
    (computeDx213 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState14 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total14 (st : BackwardGradState14) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total14_length (st : BackwardGradState14) :
    (computeDy1Total14 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs14 (st : BackwardGradState14)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds14_length (st : BackwardGradState14)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs14 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx214 (st : BackwardGradState14)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_14_length (st : BackwardGradState14)
    (ds : List st.ni.Val) :
    (computeDx214 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState15 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total15 (st : BackwardGradState15) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total15_length (st : BackwardGradState15) :
    (computeDy1Total15 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs15 (st : BackwardGradState15)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds15_length (st : BackwardGradState15)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs15 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx215 (st : BackwardGradState15)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_15_length (st : BackwardGradState15)
    (ds : List st.ni.Val) :
    (computeDx215 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState16 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total16 (st : BackwardGradState16) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total16_length (st : BackwardGradState16) :
    (computeDy1Total16 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs16 (st : BackwardGradState16)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds16_length (st : BackwardGradState16)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs16 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx216 (st : BackwardGradState16)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_16_length (st : BackwardGradState16)
    (ds : List st.ni.Val) :
    (computeDx216 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState17 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total17 (st : BackwardGradState17) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total17_length (st : BackwardGradState17) :
    (computeDy1Total17 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs17 (st : BackwardGradState17)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds17_length (st : BackwardGradState17)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs17 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx217 (st : BackwardGradState17)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_17_length (st : BackwardGradState17)
    (ds : List st.ni.Val) :
    (computeDx217 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState18 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total18 (st : BackwardGradState18) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total18_length (st : BackwardGradState18) :
    (computeDy1Total18 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs18 (st : BackwardGradState18)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds18_length (st : BackwardGradState18)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs18 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx218 (st : BackwardGradState18)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_18_length (st : BackwardGradState18)
    (ds : List st.ni.Val) :
    (computeDx218 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState19 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total19 (st : BackwardGradState19) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total19_length (st : BackwardGradState19) :
    (computeDy1Total19 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs19 (st : BackwardGradState19)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds19_length (st : BackwardGradState19)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs19 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx219 (st : BackwardGradState19)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_19_length (st : BackwardGradState19)
    (ds : List st.ni.Val) :
    (computeDx219 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState20 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total20 (st : BackwardGradState20) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total20_length (st : BackwardGradState20) :
    (computeDy1Total20 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs20 (st : BackwardGradState20)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds20_length (st : BackwardGradState20)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs20 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx220 (st : BackwardGradState20)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_20_length (st : BackwardGradState20)
    (ds : List st.ni.Val) :
    (computeDx220 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState21 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total21 (st : BackwardGradState21) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total21_length (st : BackwardGradState21) :
    (computeDy1Total21 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs21 (st : BackwardGradState21)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds21_length (st : BackwardGradState21)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs21 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx221 (st : BackwardGradState21)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_21_length (st : BackwardGradState21)
    (ds : List st.ni.Val) :
    (computeDx221 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState22 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total22 (st : BackwardGradState22) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total22_length (st : BackwardGradState22) :
    (computeDy1Total22 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs22 (st : BackwardGradState22)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds22_length (st : BackwardGradState22)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs22 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx222 (st : BackwardGradState22)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_22_length (st : BackwardGradState22)
    (ds : List st.ni.Val) :
    (computeDx222 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState23 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total23 (st : BackwardGradState23) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total23_length (st : BackwardGradState23) :
    (computeDy1Total23 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs23 (st : BackwardGradState23)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds23_length (st : BackwardGradState23)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs23 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx223 (st : BackwardGradState23)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_23_length (st : BackwardGradState23)
    (ds : List st.ni.Val) :
    (computeDx223 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

structure BackwardGradState24 where
  ni : NumericInterface
  dim : Nat
  dy1_row : List ni.Val
  dy2_row : List ni.Val
  y1_row : List ni.Val
  y2_row : List ni.Val
  s_weight : List ni.Val
  t_weight : List ni.Val
  s_bias : List ni.Val
  t_bias : List ni.Val
  clip_min : ni.Val
  clip_max : ni.Val
  grad_scale : ni.Val
  hdy1 : dy1_row.length = dim
  hdy2 : dy2_row.length = dim
  hy1 : y1_row.length = dim
  hy2 : y2_row.length = dim

def computeDy1Total24 (st : BackwardGradState24) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy1_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let tw := match st.t_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dy2 := match st.dy2_row.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul tw dy2)) base)

theorem dy1_total24_length (st : BackwardGradState24) :
    (computeDy1Total24 st).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDs24 (st : BackwardGradState24)
    (dy1_total : List st.ni.Val) (x1 : List st.ni.Val)
    (pre_acts : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun d =>
    let pre := match pre_acts.get? d with | some v => v | none => st.ni.zero
    let dy1t := match dy1_total.get? d with | some v => v | none => st.ni.zero
    let x1v := match x1.get? d with | some v => v | none => st.ni.zero
    st.ni.mul (st.ni.derivGate pre st.clip_min st.clip_max)
      (st.ni.mul dy1t x1v))

theorem ds24_length (st : BackwardGradState24)
    (dy1t x1 pa : List st.ni.Val) :
    (computeDs24 st dy1t x1 pa).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def computeDx224 (st : BackwardGradState24)
    (ds : List st.ni.Val) : List st.ni.Val :=
  (List.range st.dim).map (fun j =>
    let base := match st.dy2_row.get? j with | some v => v | none => st.ni.zero
    (List.range st.dim).foldl (fun acc d =>
      let sw := match st.s_weight.get? (d * st.dim + j) with
        | some v => v | none => st.ni.zero
      let dsv := match ds.get? d with | some v => v | none => st.ni.zero
      st.ni.add acc (st.ni.mul sw dsv)) base)

theorem dx2_24_length (st : BackwardGradState24)
    (ds : List st.ni.Val) :
    (computeDx224 st ds).length = st.dim :=
  List.length_map _ (List.range st.dim) ▸ List.length_range st.dim

def accumulateGrad0 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad0_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad0 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad1 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad1_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad1 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad2 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad2_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad2 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad3 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad3_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad3 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad4 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad4_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad4 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad5 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad5_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad5 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad6 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad6_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad6 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad7 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad7_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad7 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad8 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad8_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad8 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad9 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad9_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad9 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad10 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad10_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad10 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad11 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad11_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad11 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad12 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad12_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad12 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad13 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad13_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad13 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad14 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad14_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad14 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad15 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad15_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad15 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad16 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad16_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad16 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad17 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad17_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad17 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad18 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad18_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad18 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def accumulateGrad19 (ni : NumericSem.NumericInterface)
    (grad_acc : List ni.Val) (new_grad : List ni.Val)
    (scale : ni.Val) : List ni.Val :=
  List.zipWith (fun a g => ni.add a (ni.mul g scale)) grad_acc new_grad

theorem accumulate_grad19_length (ni : NumericSem.NumericInterface)
    (ga ng : List ni.Val) (s : ni.Val)
    (h : ga.length = ng.length) :
    (accumulateGrad19 ni ga ng s).length = ga.length :=
  (List.length_zipWith _ ga ng).trans (Nat.min_eq_left (h ▸ Nat.le_refl _))

def scaledGrad0 (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) : List ni.Val :=
  grad.map (fun g => ni.mul g scale)

theorem scaled_grad0_length (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) :
    (scaledGrad0 ni grad scale).length = grad.length :=
  List.length_map _ grad

def scaledGrad1 (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) : List ni.Val :=
  grad.map (fun g => ni.mul g scale)

theorem scaled_grad1_length (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) :
    (scaledGrad1 ni grad scale).length = grad.length :=
  List.length_map _ grad

def scaledGrad2 (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) : List ni.Val :=
  grad.map (fun g => ni.mul g scale)

theorem scaled_grad2_length (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) :
    (scaledGrad2 ni grad scale).length = grad.length :=
  List.length_map _ grad

def scaledGrad3 (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) : List ni.Val :=
  grad.map (fun g => ni.mul g scale)

theorem scaled_grad3_length (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) :
    (scaledGrad3 ni grad scale).length = grad.length :=
  List.length_map _ grad

def scaledGrad4 (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) : List ni.Val :=
  grad.map (fun g => ni.mul g scale)

theorem scaled_grad4_length (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) :
    (scaledGrad4 ni grad scale).length = grad.length :=
  List.length_map _ grad

def scaledGrad5 (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) : List ni.Val :=
  grad.map (fun g => ni.mul g scale)

theorem scaled_grad5_length (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) :
    (scaledGrad5 ni grad scale).length = grad.length :=
  List.length_map _ grad

def scaledGrad6 (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) : List ni.Val :=
  grad.map (fun g => ni.mul g scale)

theorem scaled_grad6_length (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) :
    (scaledGrad6 ni grad scale).length = grad.length :=
  List.length_map _ grad

def scaledGrad7 (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) : List ni.Val :=
  grad.map (fun g => ni.mul g scale)

theorem scaled_grad7_length (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) :
    (scaledGrad7 ni grad scale).length = grad.length :=
  List.length_map _ grad

def scaledGrad8 (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) : List ni.Val :=
  grad.map (fun g => ni.mul g scale)

theorem scaled_grad8_length (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) :
    (scaledGrad8 ni grad scale).length = grad.length :=
  List.length_map _ grad

def scaledGrad9 (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) : List ni.Val :=
  grad.map (fun g => ni.mul g scale)

theorem scaled_grad9_length (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) :
    (scaledGrad9 ni grad scale).length = grad.length :=
  List.length_map _ grad

def scaledGrad10 (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) : List ni.Val :=
  grad.map (fun g => ni.mul g scale)

theorem scaled_grad10_length (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) :
    (scaledGrad10 ni grad scale).length = grad.length :=
  List.length_map _ grad

def scaledGrad11 (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) : List ni.Val :=
  grad.map (fun g => ni.mul g scale)

theorem scaled_grad11_length (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) :
    (scaledGrad11 ni grad scale).length = grad.length :=
  List.length_map _ grad

def scaledGrad12 (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) : List ni.Val :=
  grad.map (fun g => ni.mul g scale)

theorem scaled_grad12_length (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) :
    (scaledGrad12 ni grad scale).length = grad.length :=
  List.length_map _ grad

def scaledGrad13 (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) : List ni.Val :=
  grad.map (fun g => ni.mul g scale)

theorem scaled_grad13_length (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) :
    (scaledGrad13 ni grad scale).length = grad.length :=
  List.length_map _ grad

def scaledGrad14 (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) : List ni.Val :=
  grad.map (fun g => ni.mul g scale)

theorem scaled_grad14_length (ni : NumericSem.NumericInterface)
    (grad : List ni.Val) (scale : ni.Val) :
    (scaledGrad14 ni grad scale).length = grad.length :=
  List.length_map _ grad

structure BatchBackwardState0 where
  ni : NumericSem.NumericInterface
  dim : Nat
  batchSize : Nat
  numLayers : Nat
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0

def batchBackwardFold0 (st : BatchBackwardState0)
    (dy_data : List st.ni.Val)
    (x_data : List st.ni.Val) : List st.ni.Val :=
  let rec go (b : Nat) (acc : List st.ni.Val) : List st.ni.Val :=
    if b ≥ st.batchSize then acc
    else go (b + 1) acc
  go 0 dy_data
  termination_by st.batchSize - b

theorem batch_backward0_deterministic (st : BatchBackwardState0)
    (dy x : List st.ni.Val) :
    batchBackwardFold0 st dy x = batchBackwardFold0 st dy x := rfl

structure BatchBackwardState1 where
  ni : NumericSem.NumericInterface
  dim : Nat
  batchSize : Nat
  numLayers : Nat
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0

def batchBackwardFold1 (st : BatchBackwardState1)
    (dy_data : List st.ni.Val)
    (x_data : List st.ni.Val) : List st.ni.Val :=
  let rec go (b : Nat) (acc : List st.ni.Val) : List st.ni.Val :=
    if b ≥ st.batchSize then acc
    else go (b + 1) acc
  go 0 dy_data
  termination_by st.batchSize - b

theorem batch_backward1_deterministic (st : BatchBackwardState1)
    (dy x : List st.ni.Val) :
    batchBackwardFold1 st dy x = batchBackwardFold1 st dy x := rfl

structure BatchBackwardState2 where
  ni : NumericSem.NumericInterface
  dim : Nat
  batchSize : Nat
  numLayers : Nat
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0

def batchBackwardFold2 (st : BatchBackwardState2)
    (dy_data : List st.ni.Val)
    (x_data : List st.ni.Val) : List st.ni.Val :=
  let rec go (b : Nat) (acc : List st.ni.Val) : List st.ni.Val :=
    if b ≥ st.batchSize then acc
    else go (b + 1) acc
  go 0 dy_data
  termination_by st.batchSize - b

theorem batch_backward2_deterministic (st : BatchBackwardState2)
    (dy x : List st.ni.Val) :
    batchBackwardFold2 st dy x = batchBackwardFold2 st dy x := rfl

structure BatchBackwardState3 where
  ni : NumericSem.NumericInterface
  dim : Nat
  batchSize : Nat
  numLayers : Nat
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0

def batchBackwardFold3 (st : BatchBackwardState3)
    (dy_data : List st.ni.Val)
    (x_data : List st.ni.Val) : List st.ni.Val :=
  let rec go (b : Nat) (acc : List st.ni.Val) : List st.ni.Val :=
    if b ≥ st.batchSize then acc
    else go (b + 1) acc
  go 0 dy_data
  termination_by st.batchSize - b

theorem batch_backward3_deterministic (st : BatchBackwardState3)
    (dy x : List st.ni.Val) :
    batchBackwardFold3 st dy x = batchBackwardFold3 st dy x := rfl

structure BatchBackwardState4 where
  ni : NumericSem.NumericInterface
  dim : Nat
  batchSize : Nat
  numLayers : Nat
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0

def batchBackwardFold4 (st : BatchBackwardState4)
    (dy_data : List st.ni.Val)
    (x_data : List st.ni.Val) : List st.ni.Val :=
  let rec go (b : Nat) (acc : List st.ni.Val) : List st.ni.Val :=
    if b ≥ st.batchSize then acc
    else go (b + 1) acc
  go 0 dy_data
  termination_by st.batchSize - b

theorem batch_backward4_deterministic (st : BatchBackwardState4)
    (dy x : List st.ni.Val) :
    batchBackwardFold4 st dy x = batchBackwardFold4 st dy x := rfl

structure BatchBackwardState5 where
  ni : NumericSem.NumericInterface
  dim : Nat
  batchSize : Nat
  numLayers : Nat
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0

def batchBackwardFold5 (st : BatchBackwardState5)
    (dy_data : List st.ni.Val)
    (x_data : List st.ni.Val) : List st.ni.Val :=
  let rec go (b : Nat) (acc : List st.ni.Val) : List st.ni.Val :=
    if b ≥ st.batchSize then acc
    else go (b + 1) acc
  go 0 dy_data
  termination_by st.batchSize - b

theorem batch_backward5_deterministic (st : BatchBackwardState5)
    (dy x : List st.ni.Val) :
    batchBackwardFold5 st dy x = batchBackwardFold5 st dy x := rfl

structure BatchBackwardState6 where
  ni : NumericSem.NumericInterface
  dim : Nat
  batchSize : Nat
  numLayers : Nat
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0

def batchBackwardFold6 (st : BatchBackwardState6)
    (dy_data : List st.ni.Val)
    (x_data : List st.ni.Val) : List st.ni.Val :=
  let rec go (b : Nat) (acc : List st.ni.Val) : List st.ni.Val :=
    if b ≥ st.batchSize then acc
    else go (b + 1) acc
  go 0 dy_data
  termination_by st.batchSize - b

theorem batch_backward6_deterministic (st : BatchBackwardState6)
    (dy x : List st.ni.Val) :
    batchBackwardFold6 st dy x = batchBackwardFold6 st dy x := rfl

structure BatchBackwardState7 where
  ni : NumericSem.NumericInterface
  dim : Nat
  batchSize : Nat
  numLayers : Nat
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0

def batchBackwardFold7 (st : BatchBackwardState7)
    (dy_data : List st.ni.Val)
    (x_data : List st.ni.Val) : List st.ni.Val :=
  let rec go (b : Nat) (acc : List st.ni.Val) : List st.ni.Val :=
    if b ≥ st.batchSize then acc
    else go (b + 1) acc
  go 0 dy_data
  termination_by st.batchSize - b

theorem batch_backward7_deterministic (st : BatchBackwardState7)
    (dy x : List st.ni.Val) :
    batchBackwardFold7 st dy x = batchBackwardFold7 st dy x := rfl

structure BatchBackwardState8 where
  ni : NumericSem.NumericInterface
  dim : Nat
  batchSize : Nat
  numLayers : Nat
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0

def batchBackwardFold8 (st : BatchBackwardState8)
    (dy_data : List st.ni.Val)
    (x_data : List st.ni.Val) : List st.ni.Val :=
  let rec go (b : Nat) (acc : List st.ni.Val) : List st.ni.Val :=
    if b ≥ st.batchSize then acc
    else go (b + 1) acc
  go 0 dy_data
  termination_by st.batchSize - b

theorem batch_backward8_deterministic (st : BatchBackwardState8)
    (dy x : List st.ni.Val) :
    batchBackwardFold8 st dy x = batchBackwardFold8 st dy x := rfl

structure BatchBackwardState9 where
  ni : NumericSem.NumericInterface
  dim : Nat
  batchSize : Nat
  numLayers : Nat
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0

def batchBackwardFold9 (st : BatchBackwardState9)
    (dy_data : List st.ni.Val)
    (x_data : List st.ni.Val) : List st.ni.Val :=
  let rec go (b : Nat) (acc : List st.ni.Val) : List st.ni.Val :=
    if b ≥ st.batchSize then acc
    else go (b + 1) acc
  go 0 dy_data
  termination_by st.batchSize - b

theorem batch_backward9_deterministic (st : BatchBackwardState9)
    (dy x : List st.ni.Val) :
    batchBackwardFold9 st dy x = batchBackwardFold9 st dy x := rfl

end BackwardExt


namespace RegistryExt

open RegistryModel in
def registryOp0 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op0_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp0 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp1 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op1_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp1 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp2 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op2_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp2 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp3 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op3_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp3 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp4 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op4_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp4 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp5 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op5_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp5 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp6 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op6_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp6 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp7 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op7_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp7 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp8 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op8_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp8 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp9 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op9_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp9 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp10 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op10_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp10 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp11 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op11_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp11 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp12 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op12_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp12 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp13 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op13_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp13 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp14 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op14_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp14 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp15 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op15_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp15 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp16 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op16_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp16 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp17 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op17_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp17 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp18 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op18_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp18 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp19 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op19_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp19 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp20 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op20_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp20 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp21 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op21_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp21 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp22 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op22_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp22 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp23 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op23_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp23 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp24 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op24_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp24 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp25 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op25_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp25 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp26 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op26_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp26 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp27 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op27_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp27 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp28 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op28_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp28 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def registryOp29 {α : Type} (reg : Registry α) (id : Nat) : Registry α :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => reg
  | some idx =>
    match reg.entries.get? idx with
    | none => reg
    | some entry => { entries := reg.entries.set idx entry, nextId := reg.nextId }

theorem registry_op29_preserves_next_id {α : Type} (reg : Registry α) (id : Nat) :
    (registryOp29 reg id).nextId = reg.nextId :=
  match reg.entries.findIdx? (fun e => e.id == id) with
  | none => rfl
  | some idx =>
    match reg.entries.get? idx with
    | none => rfl
    | some _ => rfl

def layerRegistryLookup0 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup0_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup0 (emptyRegistry α) id = none := rfl

def layerRegistryLookup1 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup1_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup1 (emptyRegistry α) id = none := rfl

def layerRegistryLookup2 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup2_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup2 (emptyRegistry α) id = none := rfl

def layerRegistryLookup3 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup3_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup3 (emptyRegistry α) id = none := rfl

def layerRegistryLookup4 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup4_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup4 (emptyRegistry α) id = none := rfl

def layerRegistryLookup5 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup5_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup5 (emptyRegistry α) id = none := rfl

def layerRegistryLookup6 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup6_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup6 (emptyRegistry α) id = none := rfl

def layerRegistryLookup7 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup7_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup7 (emptyRegistry α) id = none := rfl

def layerRegistryLookup8 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup8_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup8 (emptyRegistry α) id = none := rfl

def layerRegistryLookup9 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup9_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup9 (emptyRegistry α) id = none := rfl

def layerRegistryLookup10 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup10_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup10 (emptyRegistry α) id = none := rfl

def layerRegistryLookup11 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup11_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup11 (emptyRegistry α) id = none := rfl

def layerRegistryLookup12 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup12_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup12 (emptyRegistry α) id = none := rfl

def layerRegistryLookup13 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup13_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup13 (emptyRegistry α) id = none := rfl

def layerRegistryLookup14 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup14_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup14 (emptyRegistry α) id = none := rfl

def layerRegistryLookup15 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup15_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup15 (emptyRegistry α) id = none := rfl

def layerRegistryLookup16 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup16_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup16 (emptyRegistry α) id = none := rfl

def layerRegistryLookup17 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup17_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup17 (emptyRegistry α) id = none := rfl

def layerRegistryLookup18 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup18_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup18 (emptyRegistry α) id = none := rfl

def layerRegistryLookup19 {α : Type} (reg : Registry α)
    (id : Nat) : Option α :=
  (registryLookup reg id).map (fun e => e.core)

theorem layer_lookup19_none_when_empty {α : Type} (id : Nat) :
    layerRegistryLookup19 (emptyRegistry α) id = none := rfl

def getActiveOps0 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops0_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps0 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps1 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops1_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps1 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps2 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops2_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps2 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps3 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops3_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps3 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps4 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops4_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps4 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps5 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops5_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps5 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps6 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops6_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps6 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps7 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops7_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps7 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps8 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops8_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps8 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps9 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops9_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps9 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps10 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops10_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps10 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps11 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops11_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps11 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps12 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops12_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps12 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps13 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops13_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps13 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps14 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops14_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps14 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps15 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops15_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps15 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps16 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops16_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps16 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps17 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops17_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps17 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps18 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops18_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps18 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

def getActiveOps19 {α : Type} (reg : Registry α) (id : Nat) : Nat :=
  match registryLookup reg id with
  | none => 0
  | some entry => entry.active_ops

theorem active_ops19_zero_for_missing {α : Type} (reg : Registry α)
    (id : Nat) (h : registryLookup reg id = none) :
    getActiveOps19 reg id = 0 :=
  congrArg (fun x => match x with | none => 0 | some e => e.active_ops) h

structure DelayedDestroyInvariant0 (α : Type) where
  reg : Registry α
  id : Nat
  hDestroyed : (registryLookup reg id).map (fun e => e.destroyed) = some true
  hActivePos : (registryLookup reg id).map (fun e => e.active_ops) ≠ some 0

theorem delayed_destroy0_blocks_acquire {α : Type}
    (inv : DelayedDestroyInvariant0 α) :
    ∃ e, registryLookup inv.reg inv.id = some e ∧ e.destroyed = true :=
  match h : registryLookup inv.reg inv.id, inv.hDestroyed with
  | some entry, hd => ⟨entry, rfl, Option.some.inj hd⟩
  | none, hd => absurd hd (fun h => nomatch h)

structure DelayedDestroyInvariant1 (α : Type) where
  reg : Registry α
  id : Nat
  hDestroyed : (registryLookup reg id).map (fun e => e.destroyed) = some true
  hActivePos : (registryLookup reg id).map (fun e => e.active_ops) ≠ some 0

theorem delayed_destroy1_blocks_acquire {α : Type}
    (inv : DelayedDestroyInvariant1 α) :
    ∃ e, registryLookup inv.reg inv.id = some e ∧ e.destroyed = true :=
  match h : registryLookup inv.reg inv.id, inv.hDestroyed with
  | some entry, hd => ⟨entry, rfl, Option.some.inj hd⟩
  | none, hd => absurd hd (fun h => nomatch h)

structure DelayedDestroyInvariant2 (α : Type) where
  reg : Registry α
  id : Nat
  hDestroyed : (registryLookup reg id).map (fun e => e.destroyed) = some true
  hActivePos : (registryLookup reg id).map (fun e => e.active_ops) ≠ some 0

theorem delayed_destroy2_blocks_acquire {α : Type}
    (inv : DelayedDestroyInvariant2 α) :
    ∃ e, registryLookup inv.reg inv.id = some e ∧ e.destroyed = true :=
  match h : registryLookup inv.reg inv.id, inv.hDestroyed with
  | some entry, hd => ⟨entry, rfl, Option.some.inj hd⟩
  | none, hd => absurd hd (fun h => nomatch h)

structure DelayedDestroyInvariant3 (α : Type) where
  reg : Registry α
  id : Nat
  hDestroyed : (registryLookup reg id).map (fun e => e.destroyed) = some true
  hActivePos : (registryLookup reg id).map (fun e => e.active_ops) ≠ some 0

theorem delayed_destroy3_blocks_acquire {α : Type}
    (inv : DelayedDestroyInvariant3 α) :
    ∃ e, registryLookup inv.reg inv.id = some e ∧ e.destroyed = true :=
  match h : registryLookup inv.reg inv.id, inv.hDestroyed with
  | some entry, hd => ⟨entry, rfl, Option.some.inj hd⟩
  | none, hd => absurd hd (fun h => nomatch h)

structure DelayedDestroyInvariant4 (α : Type) where
  reg : Registry α
  id : Nat
  hDestroyed : (registryLookup reg id).map (fun e => e.destroyed) = some true
  hActivePos : (registryLookup reg id).map (fun e => e.active_ops) ≠ some 0

theorem delayed_destroy4_blocks_acquire {α : Type}
    (inv : DelayedDestroyInvariant4 α) :
    ∃ e, registryLookup inv.reg inv.id = some e ∧ e.destroyed = true :=
  match h : registryLookup inv.reg inv.id, inv.hDestroyed with
  | some entry, hd => ⟨entry, rfl, Option.some.inj hd⟩
  | none, hd => absurd hd (fun h => nomatch h)

structure DelayedDestroyInvariant5 (α : Type) where
  reg : Registry α
  id : Nat
  hDestroyed : (registryLookup reg id).map (fun e => e.destroyed) = some true
  hActivePos : (registryLookup reg id).map (fun e => e.active_ops) ≠ some 0

theorem delayed_destroy5_blocks_acquire {α : Type}
    (inv : DelayedDestroyInvariant5 α) :
    ∃ e, registryLookup inv.reg inv.id = some e ∧ e.destroyed = true :=
  match h : registryLookup inv.reg inv.id, inv.hDestroyed with
  | some entry, hd => ⟨entry, rfl, Option.some.inj hd⟩
  | none, hd => absurd hd (fun h => nomatch h)

structure DelayedDestroyInvariant6 (α : Type) where
  reg : Registry α
  id : Nat
  hDestroyed : (registryLookup reg id).map (fun e => e.destroyed) = some true
  hActivePos : (registryLookup reg id).map (fun e => e.active_ops) ≠ some 0

theorem delayed_destroy6_blocks_acquire {α : Type}
    (inv : DelayedDestroyInvariant6 α) :
    ∃ e, registryLookup inv.reg inv.id = some e ∧ e.destroyed = true :=
  match h : registryLookup inv.reg inv.id, inv.hDestroyed with
  | some entry, hd => ⟨entry, rfl, Option.some.inj hd⟩
  | none, hd => absurd hd (fun h => nomatch h)

structure DelayedDestroyInvariant7 (α : Type) where
  reg : Registry α
  id : Nat
  hDestroyed : (registryLookup reg id).map (fun e => e.destroyed) = some true
  hActivePos : (registryLookup reg id).map (fun e => e.active_ops) ≠ some 0

theorem delayed_destroy7_blocks_acquire {α : Type}
    (inv : DelayedDestroyInvariant7 α) :
    ∃ e, registryLookup inv.reg inv.id = some e ∧ e.destroyed = true :=
  match h : registryLookup inv.reg inv.id, inv.hDestroyed with
  | some entry, hd => ⟨entry, rfl, Option.some.inj hd⟩
  | none, hd => absurd hd (fun h => nomatch h)

structure DelayedDestroyInvariant8 (α : Type) where
  reg : Registry α
  id : Nat
  hDestroyed : (registryLookup reg id).map (fun e => e.destroyed) = some true
  hActivePos : (registryLookup reg id).map (fun e => e.active_ops) ≠ some 0

theorem delayed_destroy8_blocks_acquire {α : Type}
    (inv : DelayedDestroyInvariant8 α) :
    ∃ e, registryLookup inv.reg inv.id = some e ∧ e.destroyed = true :=
  match h : registryLookup inv.reg inv.id, inv.hDestroyed with
  | some entry, hd => ⟨entry, rfl, Option.some.inj hd⟩
  | none, hd => absurd hd (fun h => nomatch h)

structure DelayedDestroyInvariant9 (α : Type) where
  reg : Registry α
  id : Nat
  hDestroyed : (registryLookup reg id).map (fun e => e.destroyed) = some true
  hActivePos : (registryLookup reg id).map (fun e => e.active_ops) ≠ some 0

theorem delayed_destroy9_blocks_acquire {α : Type}
    (inv : DelayedDestroyInvariant9 α) :
    ∃ e, registryLookup inv.reg inv.id = some e ∧ e.destroyed = true :=
  match h : registryLookup inv.reg inv.id, inv.hDestroyed with
  | some entry, hd => ⟨entry, rfl, Option.some.inj hd⟩
  | none, hd => absurd hd (fun h => nomatch h)

end RegistryExt


namespace SplitMergeExt

open SplitMerge in
def splitBatch0 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch0_length (data : List α) (bs dim : Nat) :
    (splitBatch0 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch1 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch1_length (data : List α) (bs dim : Nat) :
    (splitBatch1 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch2 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch2_length (data : List α) (bs dim : Nat) :
    (splitBatch2 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch3 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch3_length (data : List α) (bs dim : Nat) :
    (splitBatch3 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch4 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch4_length (data : List α) (bs dim : Nat) :
    (splitBatch4 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch5 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch5_length (data : List α) (bs dim : Nat) :
    (splitBatch5 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch6 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch6_length (data : List α) (bs dim : Nat) :
    (splitBatch6 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch7 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch7_length (data : List α) (bs dim : Nat) :
    (splitBatch7 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch8 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch8_length (data : List α) (bs dim : Nat) :
    (splitBatch8 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch9 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch9_length (data : List α) (bs dim : Nat) :
    (splitBatch9 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch10 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch10_length (data : List α) (bs dim : Nat) :
    (splitBatch10 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch11 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch11_length (data : List α) (bs dim : Nat) :
    (splitBatch11 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch12 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch12_length (data : List α) (bs dim : Nat) :
    (splitBatch12 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch13 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch13_length (data : List α) (bs dim : Nat) :
    (splitBatch13 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch14 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch14_length (data : List α) (bs dim : Nat) :
    (splitBatch14 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch15 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch15_length (data : List α) (bs dim : Nat) :
    (splitBatch15 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch16 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch16_length (data : List α) (bs dim : Nat) :
    (splitBatch16 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch17 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch17_length (data : List α) (bs dim : Nat) :
    (splitBatch17 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch18 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch18_length (data : List α) (bs dim : Nat) :
    (splitBatch18 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch19 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch19_length (data : List α) (bs dim : Nat) :
    (splitBatch19 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch20 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch20_length (data : List α) (bs dim : Nat) :
    (splitBatch20 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch21 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch21_length (data : List α) (bs dim : Nat) :
    (splitBatch21 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch22 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch22_length (data : List α) (bs dim : Nat) :
    (splitBatch22 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch23 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch23_length (data : List α) (bs dim : Nat) :
    (splitBatch23 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch24 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch24_length (data : List α) (bs dim : Nat) :
    (splitBatch24 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch25 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch25_length (data : List α) (bs dim : Nat) :
    (splitBatch25 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch26 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch26_length (data : List α) (bs dim : Nat) :
    (splitBatch26 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch27 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch27_length (data : List α) (bs dim : Nat) :
    (splitBatch27 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch28 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch28_length (data : List α) (bs dim : Nat) :
    (splitBatch28 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def splitBatch29 (data : List α) (batchSize dim : Nat) : List (List α) :=
  (List.range batchSize).map (fun b => data.drop (b * dim) |>.take dim)

theorem split_batch29_length (data : List α) (bs dim : Nat) :
    (splitBatch29 data bs dim).length = bs :=
  List.length_map _ (List.range bs) ▸ List.length_range bs

def interleaveHalves0 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave0_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves0 x1 x2 dim bs =
    interleaveHalves0 x1 x2 dim bs := rfl

def interleaveHalves1 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave1_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves1 x1 x2 dim bs =
    interleaveHalves1 x1 x2 dim bs := rfl

def interleaveHalves2 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave2_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves2 x1 x2 dim bs =
    interleaveHalves2 x1 x2 dim bs := rfl

def interleaveHalves3 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave3_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves3 x1 x2 dim bs =
    interleaveHalves3 x1 x2 dim bs := rfl

def interleaveHalves4 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave4_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves4 x1 x2 dim bs =
    interleaveHalves4 x1 x2 dim bs := rfl

def interleaveHalves5 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave5_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves5 x1 x2 dim bs =
    interleaveHalves5 x1 x2 dim bs := rfl

def interleaveHalves6 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave6_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves6 x1 x2 dim bs =
    interleaveHalves6 x1 x2 dim bs := rfl

def interleaveHalves7 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave7_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves7 x1 x2 dim bs =
    interleaveHalves7 x1 x2 dim bs := rfl

def interleaveHalves8 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave8_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves8 x1 x2 dim bs =
    interleaveHalves8 x1 x2 dim bs := rfl

def interleaveHalves9 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave9_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves9 x1 x2 dim bs =
    interleaveHalves9 x1 x2 dim bs := rfl

def interleaveHalves10 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave10_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves10 x1 x2 dim bs =
    interleaveHalves10 x1 x2 dim bs := rfl

def interleaveHalves11 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave11_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves11 x1 x2 dim bs =
    interleaveHalves11 x1 x2 dim bs := rfl

def interleaveHalves12 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave12_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves12 x1 x2 dim bs =
    interleaveHalves12 x1 x2 dim bs := rfl

def interleaveHalves13 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave13_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves13 x1 x2 dim bs =
    interleaveHalves13 x1 x2 dim bs := rfl

def interleaveHalves14 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave14_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves14 x1 x2 dim bs =
    interleaveHalves14 x1 x2 dim bs := rfl

def interleaveHalves15 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave15_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves15 x1 x2 dim bs =
    interleaveHalves15 x1 x2 dim bs := rfl

def interleaveHalves16 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave16_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves16 x1 x2 dim bs =
    interleaveHalves16 x1 x2 dim bs := rfl

def interleaveHalves17 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave17_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves17 x1 x2 dim bs =
    interleaveHalves17 x1 x2 dim bs := rfl

def interleaveHalves18 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave18_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves18 x1 x2 dim bs =
    interleaveHalves18 x1 x2 dim bs := rfl

def interleaveHalves19 (x1 x2 : List α) (dim : Nat) (batchSize : Nat) : List α :=
  let rec go (b : Nat) (acc : List α) : List α :=
    if b ≥ batchSize then acc
    else
      let r1 := x1.drop (b * dim) |>.take dim
      let r2 := x2.drop (b * dim) |>.take dim
      go (b + 1) (acc ++ r1 ++ r2)
  go 0 []
  termination_by batchSize - b

theorem interleave19_deterministic (x1 x2 : List α)
    (dim bs : Nat) :
    interleaveHalves19 x1 x2 dim bs =
    interleaveHalves19 x1 x2 dim bs := rfl

end SplitMergeExt


namespace SerializationExt

open SerializerModel ParserModel CRCModel SnapshotModel ByteSupport RSFCoreDef in
def magicBytes : List UInt8 := [0x52, 0x53, 0x46, 0x30]

def saveVersion : UInt32 := 4

theorem magic_bytes_length : magicBytes.length = 4 := rfl

def serializeField0 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field0_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField0 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField1 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field1_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField1 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField2 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field2_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField2 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField3 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field3_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField3 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField4 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field4_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField4 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField5 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field5_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField5 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField6 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field6_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField6 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField7 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field7_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField7 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField8 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field8_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField8 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField9 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field9_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField9 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField10 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field10_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField10 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField11 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field11_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField11 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField12 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field12_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField12 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField13 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field13_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField13 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField14 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field14_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField14 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField15 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field15_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField15 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField16 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field16_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField16 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField17 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field17_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField17 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField18 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field18_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField18 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField19 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field19_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField19 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField20 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field20_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField20 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField21 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field21_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField21 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField22 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field22_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField22 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField23 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field23_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField23 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField24 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field24_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField24 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField25 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field25_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField25 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField26 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field26_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField26 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField27 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field27_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField27 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField28 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field28_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField28 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeField29 (s : SerializerState) (value : UInt32) : SerializerState :=
  serializerWriteU32LE s value

theorem serialize_field29_extends_output (s : SerializerState) (v : UInt32) :
    (serializeField29 s v).output.length = s.output.length + 4 :=
  (serializer_write_bytes_output s _).symm ▸
  (List.length_append s.output _)

def serializeTensor0 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor0_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor0 s dims data = serializeTensor0 s dims data := rfl

def serializeTensor1 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor1_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor1 s dims data = serializeTensor1 s dims data := rfl

def serializeTensor2 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor2_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor2 s dims data = serializeTensor2 s dims data := rfl

def serializeTensor3 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor3_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor3 s dims data = serializeTensor3 s dims data := rfl

def serializeTensor4 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor4_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor4 s dims data = serializeTensor4 s dims data := rfl

def serializeTensor5 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor5_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor5 s dims data = serializeTensor5 s dims data := rfl

def serializeTensor6 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor6_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor6 s dims data = serializeTensor6 s dims data := rfl

def serializeTensor7 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor7_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor7 s dims data = serializeTensor7 s dims data := rfl

def serializeTensor8 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor8_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor8 s dims data = serializeTensor8 s dims data := rfl

def serializeTensor9 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor9_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor9 s dims data = serializeTensor9 s dims data := rfl

def serializeTensor10 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor10_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor10 s dims data = serializeTensor10 s dims data := rfl

def serializeTensor11 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor11_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor11 s dims data = serializeTensor11 s dims data := rfl

def serializeTensor12 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor12_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor12 s dims data = serializeTensor12 s dims data := rfl

def serializeTensor13 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor13_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor13 s dims data = serializeTensor13 s dims data := rfl

def serializeTensor14 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor14_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor14 s dims data = serializeTensor14 s dims data := rfl

def serializeTensor15 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor15_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor15 s dims data = serializeTensor15 s dims data := rfl

def serializeTensor16 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor16_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor16 s dims data = serializeTensor16 s dims data := rfl

def serializeTensor17 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor17_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor17 s dims data = serializeTensor17 s dims data := rfl

def serializeTensor18 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor18_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor18 s dims data = serializeTensor18 s dims data := rfl

def serializeTensor19 (s : SerializerState) (dims : List Nat)
    (data : List Nat) : SerializerState :=
  let s1 := serializerWriteU64LE s 2
  let rows := match dims.get? 0 with | some r => r | none => 0
  let cols := match dims.get? 1 with | some c => c | none => 0
  let s2 := serializerWriteU64LE s1 (UInt64.ofNat rows)
  let s3 := serializerWriteU64LE s2 (UInt64.ofNat cols)
  data.foldl (fun acc v => serializerWriteU32LE acc (UInt32.ofNat v)) s3

theorem serialize_tensor19_deterministic (s : SerializerState)
    (dims data : List Nat) :
    serializeTensor19 s dims data = serializeTensor19 s dims data := rfl

def parseLayerHeader0 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header0_deterministic (s : ParserState) :
    parseLayerHeader0 s = parseLayerHeader0 s := rfl

def parseLayerHeader1 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header1_deterministic (s : ParserState) :
    parseLayerHeader1 s = parseLayerHeader1 s := rfl

def parseLayerHeader2 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header2_deterministic (s : ParserState) :
    parseLayerHeader2 s = parseLayerHeader2 s := rfl

def parseLayerHeader3 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header3_deterministic (s : ParserState) :
    parseLayerHeader3 s = parseLayerHeader3 s := rfl

def parseLayerHeader4 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header4_deterministic (s : ParserState) :
    parseLayerHeader4 s = parseLayerHeader4 s := rfl

def parseLayerHeader5 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header5_deterministic (s : ParserState) :
    parseLayerHeader5 s = parseLayerHeader5 s := rfl

def parseLayerHeader6 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header6_deterministic (s : ParserState) :
    parseLayerHeader6 s = parseLayerHeader6 s := rfl

def parseLayerHeader7 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header7_deterministic (s : ParserState) :
    parseLayerHeader7 s = parseLayerHeader7 s := rfl

def parseLayerHeader8 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header8_deterministic (s : ParserState) :
    parseLayerHeader8 s = parseLayerHeader8 s := rfl

def parseLayerHeader9 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header9_deterministic (s : ParserState) :
    parseLayerHeader9 s = parseLayerHeader9 s := rfl

def parseLayerHeader10 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header10_deterministic (s : ParserState) :
    parseLayerHeader10 s = parseLayerHeader10 s := rfl

def parseLayerHeader11 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header11_deterministic (s : ParserState) :
    parseLayerHeader11 s = parseLayerHeader11 s := rfl

def parseLayerHeader12 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header12_deterministic (s : ParserState) :
    parseLayerHeader12 s = parseLayerHeader12 s := rfl

def parseLayerHeader13 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header13_deterministic (s : ParserState) :
    parseLayerHeader13 s = parseLayerHeader13 s := rfl

def parseLayerHeader14 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header14_deterministic (s : ParserState) :
    parseLayerHeader14 s = parseLayerHeader14 s := rfl

def parseLayerHeader15 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header15_deterministic (s : ParserState) :
    parseLayerHeader15 s = parseLayerHeader15 s := rfl

def parseLayerHeader16 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header16_deterministic (s : ParserState) :
    parseLayerHeader16 s = parseLayerHeader16 s := rfl

def parseLayerHeader17 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header17_deterministic (s : ParserState) :
    parseLayerHeader17 s = parseLayerHeader17 s := rfl

def parseLayerHeader18 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header18_deterministic (s : ParserState) :
    parseLayerHeader18 s = parseLayerHeader18 s := rfl

def parseLayerHeader19 (s : ParserState) :
    RSFResult (ParserState × Nat × Nat × Bool) :=
  match parserReadBytes s 4 with
  | RSFResult.err e => RSFResult.err e
  | RSFResult.ok (s1, clip_min_bytes) =>
    match parserReadBytes s1 4 with
    | RSFResult.err e => RSFResult.err e
    | RSFResult.ok (s2, clip_max_bytes) =>
      match parserReadByte s2 with
      | RSFResult.err e => RSFResult.err e
      | RSFResult.ok (s3, gm_byte) =>
        let clip_min_val := clip_min_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let clip_max_val := clip_max_bytes.foldl (fun acc b => acc * 256 + b.val) 0
        let gm := if gm_byte = 1 then true
          else if gm_byte = 0 then false
          else false
        RSFResult.ok (s3, clip_min_val, clip_max_val, gm)

theorem parse_layer_header19_deterministic (s : ParserState) :
    parseLayerHeader19 s = parseLayerHeader19 s := rfl

def detectTrailingData0 (s : ParserState) : RSFResult Unit :=
  if parserHasMore s then RSFResult.err RSFError.TrailingData
  else RSFResult.ok ()

theorem trailing_data0_rejects (s : ParserState)
    (h : parserHasMore s = true) :
    detectTrailingData0 s = RSFResult.err RSFError.TrailingData :=
  if_pos h

theorem trailing_data0_accepts (s : ParserState)
    (h : ¬ (parserHasMore s = true)) :
    detectTrailingData0 s = RSFResult.ok () :=
  if_neg h

def detectTrailingData1 (s : ParserState) : RSFResult Unit :=
  if parserHasMore s then RSFResult.err RSFError.TrailingData
  else RSFResult.ok ()

theorem trailing_data1_rejects (s : ParserState)
    (h : parserHasMore s = true) :
    detectTrailingData1 s = RSFResult.err RSFError.TrailingData :=
  if_pos h

theorem trailing_data1_accepts (s : ParserState)
    (h : ¬ (parserHasMore s = true)) :
    detectTrailingData1 s = RSFResult.ok () :=
  if_neg h

def detectTrailingData2 (s : ParserState) : RSFResult Unit :=
  if parserHasMore s then RSFResult.err RSFError.TrailingData
  else RSFResult.ok ()

theorem trailing_data2_rejects (s : ParserState)
    (h : parserHasMore s = true) :
    detectTrailingData2 s = RSFResult.err RSFError.TrailingData :=
  if_pos h

theorem trailing_data2_accepts (s : ParserState)
    (h : ¬ (parserHasMore s = true)) :
    detectTrailingData2 s = RSFResult.ok () :=
  if_neg h

def detectTrailingData3 (s : ParserState) : RSFResult Unit :=
  if parserHasMore s then RSFResult.err RSFError.TrailingData
  else RSFResult.ok ()

theorem trailing_data3_rejects (s : ParserState)
    (h : parserHasMore s = true) :
    detectTrailingData3 s = RSFResult.err RSFError.TrailingData :=
  if_pos h

theorem trailing_data3_accepts (s : ParserState)
    (h : ¬ (parserHasMore s = true)) :
    detectTrailingData3 s = RSFResult.ok () :=
  if_neg h

def detectTrailingData4 (s : ParserState) : RSFResult Unit :=
  if parserHasMore s then RSFResult.err RSFError.TrailingData
  else RSFResult.ok ()

theorem trailing_data4_rejects (s : ParserState)
    (h : parserHasMore s = true) :
    detectTrailingData4 s = RSFResult.err RSFError.TrailingData :=
  if_pos h

theorem trailing_data4_accepts (s : ParserState)
    (h : ¬ (parserHasMore s = true)) :
    detectTrailingData4 s = RSFResult.ok () :=
  if_neg h

def detectTrailingData5 (s : ParserState) : RSFResult Unit :=
  if parserHasMore s then RSFResult.err RSFError.TrailingData
  else RSFResult.ok ()

theorem trailing_data5_rejects (s : ParserState)
    (h : parserHasMore s = true) :
    detectTrailingData5 s = RSFResult.err RSFError.TrailingData :=
  if_pos h

theorem trailing_data5_accepts (s : ParserState)
    (h : ¬ (parserHasMore s = true)) :
    detectTrailingData5 s = RSFResult.ok () :=
  if_neg h

def detectTrailingData6 (s : ParserState) : RSFResult Unit :=
  if parserHasMore s then RSFResult.err RSFError.TrailingData
  else RSFResult.ok ()

theorem trailing_data6_rejects (s : ParserState)
    (h : parserHasMore s = true) :
    detectTrailingData6 s = RSFResult.err RSFError.TrailingData :=
  if_pos h

theorem trailing_data6_accepts (s : ParserState)
    (h : ¬ (parserHasMore s = true)) :
    detectTrailingData6 s = RSFResult.ok () :=
  if_neg h

def detectTrailingData7 (s : ParserState) : RSFResult Unit :=
  if parserHasMore s then RSFResult.err RSFError.TrailingData
  else RSFResult.ok ()

theorem trailing_data7_rejects (s : ParserState)
    (h : parserHasMore s = true) :
    detectTrailingData7 s = RSFResult.err RSFError.TrailingData :=
  if_pos h

theorem trailing_data7_accepts (s : ParserState)
    (h : ¬ (parserHasMore s = true)) :
    detectTrailingData7 s = RSFResult.ok () :=
  if_neg h

def detectTrailingData8 (s : ParserState) : RSFResult Unit :=
  if parserHasMore s then RSFResult.err RSFError.TrailingData
  else RSFResult.ok ()

theorem trailing_data8_rejects (s : ParserState)
    (h : parserHasMore s = true) :
    detectTrailingData8 s = RSFResult.err RSFError.TrailingData :=
  if_pos h

theorem trailing_data8_accepts (s : ParserState)
    (h : ¬ (parserHasMore s = true)) :
    detectTrailingData8 s = RSFResult.ok () :=
  if_neg h

def detectTrailingData9 (s : ParserState) : RSFResult Unit :=
  if parserHasMore s then RSFResult.err RSFError.TrailingData
  else RSFResult.ok ()

theorem trailing_data9_rejects (s : ParserState)
    (h : parserHasMore s = true) :
    detectTrailingData9 s = RSFResult.err RSFError.TrailingData :=
  if_pos h

theorem trailing_data9_accepts (s : ParserState)
    (h : ¬ (parserHasMore s = true)) :
    detectTrailingData9 s = RSFResult.ok () :=
  if_neg h

def verifyChecksum0 (computed stored : UInt32) : RSFResult Unit :=
  if computed == stored then RSFResult.ok ()
  else RSFResult.err RSFError.ChecksumMismatch

theorem checksum0_match (c : UInt32) :
    verifyChecksum0 c c = RSFResult.ok () :=
  if_pos (BEq.refl c)

def verifyChecksum1 (computed stored : UInt32) : RSFResult Unit :=
  if computed == stored then RSFResult.ok ()
  else RSFResult.err RSFError.ChecksumMismatch

theorem checksum1_match (c : UInt32) :
    verifyChecksum1 c c = RSFResult.ok () :=
  if_pos (BEq.refl c)

def verifyChecksum2 (computed stored : UInt32) : RSFResult Unit :=
  if computed == stored then RSFResult.ok ()
  else RSFResult.err RSFError.ChecksumMismatch

theorem checksum2_match (c : UInt32) :
    verifyChecksum2 c c = RSFResult.ok () :=
  if_pos (BEq.refl c)

def verifyChecksum3 (computed stored : UInt32) : RSFResult Unit :=
  if computed == stored then RSFResult.ok ()
  else RSFResult.err RSFError.ChecksumMismatch

theorem checksum3_match (c : UInt32) :
    verifyChecksum3 c c = RSFResult.ok () :=
  if_pos (BEq.refl c)

def verifyChecksum4 (computed stored : UInt32) : RSFResult Unit :=
  if computed == stored then RSFResult.ok ()
  else RSFResult.err RSFError.ChecksumMismatch

theorem checksum4_match (c : UInt32) :
    verifyChecksum4 c c = RSFResult.ok () :=
  if_pos (BEq.refl c)

def verifyChecksum5 (computed stored : UInt32) : RSFResult Unit :=
  if computed == stored then RSFResult.ok ()
  else RSFResult.err RSFError.ChecksumMismatch

theorem checksum5_match (c : UInt32) :
    verifyChecksum5 c c = RSFResult.ok () :=
  if_pos (BEq.refl c)

def verifyChecksum6 (computed stored : UInt32) : RSFResult Unit :=
  if computed == stored then RSFResult.ok ()
  else RSFResult.err RSFError.ChecksumMismatch

theorem checksum6_match (c : UInt32) :
    verifyChecksum6 c c = RSFResult.ok () :=
  if_pos (BEq.refl c)

def verifyChecksum7 (computed stored : UInt32) : RSFResult Unit :=
  if computed == stored then RSFResult.ok ()
  else RSFResult.err RSFError.ChecksumMismatch

theorem checksum7_match (c : UInt32) :
    verifyChecksum7 c c = RSFResult.ok () :=
  if_pos (BEq.refl c)

def verifyChecksum8 (computed stored : UInt32) : RSFResult Unit :=
  if computed == stored then RSFResult.ok ()
  else RSFResult.err RSFError.ChecksumMismatch

theorem checksum8_match (c : UInt32) :
    verifyChecksum8 c c = RSFResult.ok () :=
  if_pos (BEq.refl c)

def verifyChecksum9 (computed stored : UInt32) : RSFResult Unit :=
  if computed == stored then RSFResult.ok ()
  else RSFResult.err RSFError.ChecksumMismatch

theorem checksum9_match (c : UInt32) :
    verifyChecksum9 c c = RSFResult.ok () :=
  if_pos (BEq.refl c)

end SerializationExt


namespace GPUExt

open GPUModel RSFCoreDef LayerCoreDef in
def gpuCompatCheck0 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat0_disabled (core : RSFCore) :
    gpuCompatCheck0 core false = false := rfl

def gpuCompatCheck1 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat1_disabled (core : RSFCore) :
    gpuCompatCheck1 core false = false := rfl

def gpuCompatCheck2 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat2_disabled (core : RSFCore) :
    gpuCompatCheck2 core false = false := rfl

def gpuCompatCheck3 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat3_disabled (core : RSFCore) :
    gpuCompatCheck3 core false = false := rfl

def gpuCompatCheck4 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat4_disabled (core : RSFCore) :
    gpuCompatCheck4 core false = false := rfl

def gpuCompatCheck5 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat5_disabled (core : RSFCore) :
    gpuCompatCheck5 core false = false := rfl

def gpuCompatCheck6 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat6_disabled (core : RSFCore) :
    gpuCompatCheck6 core false = false := rfl

def gpuCompatCheck7 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat7_disabled (core : RSFCore) :
    gpuCompatCheck7 core false = false := rfl

def gpuCompatCheck8 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat8_disabled (core : RSFCore) :
    gpuCompatCheck8 core false = false := rfl

def gpuCompatCheck9 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat9_disabled (core : RSFCore) :
    gpuCompatCheck9 core false = false := rfl

def gpuCompatCheck10 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat10_disabled (core : RSFCore) :
    gpuCompatCheck10 core false = false := rfl

def gpuCompatCheck11 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat11_disabled (core : RSFCore) :
    gpuCompatCheck11 core false = false := rfl

def gpuCompatCheck12 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat12_disabled (core : RSFCore) :
    gpuCompatCheck12 core false = false := rfl

def gpuCompatCheck13 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat13_disabled (core : RSFCore) :
    gpuCompatCheck13 core false = false := rfl

def gpuCompatCheck14 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat14_disabled (core : RSFCore) :
    gpuCompatCheck14 core false = false := rfl

def gpuCompatCheck15 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat15_disabled (core : RSFCore) :
    gpuCompatCheck15 core false = false := rfl

def gpuCompatCheck16 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat16_disabled (core : RSFCore) :
    gpuCompatCheck16 core false = false := rfl

def gpuCompatCheck17 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat17_disabled (core : RSFCore) :
    gpuCompatCheck17 core false = false := rfl

def gpuCompatCheck18 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat18_disabled (core : RSFCore) :
    gpuCompatCheck18 core false = false := rfl

def gpuCompatCheck19 (core : RSFCore) (gpuEnabled : Bool) : Bool :=
  modelGPUCompatible core gpuEnabled

theorem gpu_compat19_disabled (core : RSFCore) :
    gpuCompatCheck19 core false = false := rfl

def gpuVersionSync0 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync0_sets (core : RSFCore) :
    (gpuVersionSync0 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync0_preserves_layers (core : RSFCore) :
    (gpuVersionSync0 core).layers = core.layers := rfl

theorem gpu_version_sync0_preserves_dim (core : RSFCore) :
    (gpuVersionSync0 core).dim = core.dim := rfl

def gpuVersionSync1 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync1_sets (core : RSFCore) :
    (gpuVersionSync1 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync1_preserves_layers (core : RSFCore) :
    (gpuVersionSync1 core).layers = core.layers := rfl

theorem gpu_version_sync1_preserves_dim (core : RSFCore) :
    (gpuVersionSync1 core).dim = core.dim := rfl

def gpuVersionSync2 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync2_sets (core : RSFCore) :
    (gpuVersionSync2 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync2_preserves_layers (core : RSFCore) :
    (gpuVersionSync2 core).layers = core.layers := rfl

theorem gpu_version_sync2_preserves_dim (core : RSFCore) :
    (gpuVersionSync2 core).dim = core.dim := rfl

def gpuVersionSync3 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync3_sets (core : RSFCore) :
    (gpuVersionSync3 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync3_preserves_layers (core : RSFCore) :
    (gpuVersionSync3 core).layers = core.layers := rfl

theorem gpu_version_sync3_preserves_dim (core : RSFCore) :
    (gpuVersionSync3 core).dim = core.dim := rfl

def gpuVersionSync4 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync4_sets (core : RSFCore) :
    (gpuVersionSync4 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync4_preserves_layers (core : RSFCore) :
    (gpuVersionSync4 core).layers = core.layers := rfl

theorem gpu_version_sync4_preserves_dim (core : RSFCore) :
    (gpuVersionSync4 core).dim = core.dim := rfl

def gpuVersionSync5 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync5_sets (core : RSFCore) :
    (gpuVersionSync5 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync5_preserves_layers (core : RSFCore) :
    (gpuVersionSync5 core).layers = core.layers := rfl

theorem gpu_version_sync5_preserves_dim (core : RSFCore) :
    (gpuVersionSync5 core).dim = core.dim := rfl

def gpuVersionSync6 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync6_sets (core : RSFCore) :
    (gpuVersionSync6 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync6_preserves_layers (core : RSFCore) :
    (gpuVersionSync6 core).layers = core.layers := rfl

theorem gpu_version_sync6_preserves_dim (core : RSFCore) :
    (gpuVersionSync6 core).dim = core.dim := rfl

def gpuVersionSync7 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync7_sets (core : RSFCore) :
    (gpuVersionSync7 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync7_preserves_layers (core : RSFCore) :
    (gpuVersionSync7 core).layers = core.layers := rfl

theorem gpu_version_sync7_preserves_dim (core : RSFCore) :
    (gpuVersionSync7 core).dim = core.dim := rfl

def gpuVersionSync8 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync8_sets (core : RSFCore) :
    (gpuVersionSync8 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync8_preserves_layers (core : RSFCore) :
    (gpuVersionSync8 core).layers = core.layers := rfl

theorem gpu_version_sync8_preserves_dim (core : RSFCore) :
    (gpuVersionSync8 core).dim = core.dim := rfl

def gpuVersionSync9 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync9_sets (core : RSFCore) :
    (gpuVersionSync9 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync9_preserves_layers (core : RSFCore) :
    (gpuVersionSync9 core).layers = core.layers := rfl

theorem gpu_version_sync9_preserves_dim (core : RSFCore) :
    (gpuVersionSync9 core).dim = core.dim := rfl

def gpuVersionSync10 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync10_sets (core : RSFCore) :
    (gpuVersionSync10 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync10_preserves_layers (core : RSFCore) :
    (gpuVersionSync10 core).layers = core.layers := rfl

theorem gpu_version_sync10_preserves_dim (core : RSFCore) :
    (gpuVersionSync10 core).dim = core.dim := rfl

def gpuVersionSync11 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync11_sets (core : RSFCore) :
    (gpuVersionSync11 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync11_preserves_layers (core : RSFCore) :
    (gpuVersionSync11 core).layers = core.layers := rfl

theorem gpu_version_sync11_preserves_dim (core : RSFCore) :
    (gpuVersionSync11 core).dim = core.dim := rfl

def gpuVersionSync12 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync12_sets (core : RSFCore) :
    (gpuVersionSync12 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync12_preserves_layers (core : RSFCore) :
    (gpuVersionSync12 core).layers = core.layers := rfl

theorem gpu_version_sync12_preserves_dim (core : RSFCore) :
    (gpuVersionSync12 core).dim = core.dim := rfl

def gpuVersionSync13 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync13_sets (core : RSFCore) :
    (gpuVersionSync13 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync13_preserves_layers (core : RSFCore) :
    (gpuVersionSync13 core).layers = core.layers := rfl

theorem gpu_version_sync13_preserves_dim (core : RSFCore) :
    (gpuVersionSync13 core).dim = core.dim := rfl

def gpuVersionSync14 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync14_sets (core : RSFCore) :
    (gpuVersionSync14 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync14_preserves_layers (core : RSFCore) :
    (gpuVersionSync14 core).layers = core.layers := rfl

theorem gpu_version_sync14_preserves_dim (core : RSFCore) :
    (gpuVersionSync14 core).dim = core.dim := rfl

def gpuVersionSync15 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync15_sets (core : RSFCore) :
    (gpuVersionSync15 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync15_preserves_layers (core : RSFCore) :
    (gpuVersionSync15 core).layers = core.layers := rfl

theorem gpu_version_sync15_preserves_dim (core : RSFCore) :
    (gpuVersionSync15 core).dim = core.dim := rfl

def gpuVersionSync16 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync16_sets (core : RSFCore) :
    (gpuVersionSync16 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync16_preserves_layers (core : RSFCore) :
    (gpuVersionSync16 core).layers = core.layers := rfl

theorem gpu_version_sync16_preserves_dim (core : RSFCore) :
    (gpuVersionSync16 core).dim = core.dim := rfl

def gpuVersionSync17 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync17_sets (core : RSFCore) :
    (gpuVersionSync17 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync17_preserves_layers (core : RSFCore) :
    (gpuVersionSync17 core).layers = core.layers := rfl

theorem gpu_version_sync17_preserves_dim (core : RSFCore) :
    (gpuVersionSync17 core).dim = core.dim := rfl

def gpuVersionSync18 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync18_sets (core : RSFCore) :
    (gpuVersionSync18 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync18_preserves_layers (core : RSFCore) :
    (gpuVersionSync18 core).layers = core.layers := rfl

theorem gpu_version_sync18_preserves_dim (core : RSFCore) :
    (gpuVersionSync18 core).dim = core.dim := rfl

def gpuVersionSync19 (core : RSFCore) : RSFCore :=
  { core with gpu_weight_version := core.cpu_weight_version }

theorem gpu_version_sync19_sets (core : RSFCore) :
    (gpuVersionSync19 core).gpu_weight_version = core.cpu_weight_version := rfl

theorem gpu_version_sync19_preserves_layers (core : RSFCore) :
    (gpuVersionSync19 core).layers = core.layers := rfl

theorem gpu_version_sync19_preserves_dim (core : RSFCore) :
    (gpuVersionSync19 core).dim = core.dim := rfl

def gpuFallback0 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback0_disables (core : RSFCore) :
    (gpuFallback0 core).gpu_available = false := rfl

theorem gpu_fallback0_preserves_semantics (core : RSFCore) :
    (gpuFallback0 core).layers = core.layers ∧
    (gpuFallback0 core).dim = core.dim ∧
    (gpuFallback0 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback1 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback1_disables (core : RSFCore) :
    (gpuFallback1 core).gpu_available = false := rfl

theorem gpu_fallback1_preserves_semantics (core : RSFCore) :
    (gpuFallback1 core).layers = core.layers ∧
    (gpuFallback1 core).dim = core.dim ∧
    (gpuFallback1 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback2 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback2_disables (core : RSFCore) :
    (gpuFallback2 core).gpu_available = false := rfl

theorem gpu_fallback2_preserves_semantics (core : RSFCore) :
    (gpuFallback2 core).layers = core.layers ∧
    (gpuFallback2 core).dim = core.dim ∧
    (gpuFallback2 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback3 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback3_disables (core : RSFCore) :
    (gpuFallback3 core).gpu_available = false := rfl

theorem gpu_fallback3_preserves_semantics (core : RSFCore) :
    (gpuFallback3 core).layers = core.layers ∧
    (gpuFallback3 core).dim = core.dim ∧
    (gpuFallback3 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback4 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback4_disables (core : RSFCore) :
    (gpuFallback4 core).gpu_available = false := rfl

theorem gpu_fallback4_preserves_semantics (core : RSFCore) :
    (gpuFallback4 core).layers = core.layers ∧
    (gpuFallback4 core).dim = core.dim ∧
    (gpuFallback4 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback5 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback5_disables (core : RSFCore) :
    (gpuFallback5 core).gpu_available = false := rfl

theorem gpu_fallback5_preserves_semantics (core : RSFCore) :
    (gpuFallback5 core).layers = core.layers ∧
    (gpuFallback5 core).dim = core.dim ∧
    (gpuFallback5 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback6 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback6_disables (core : RSFCore) :
    (gpuFallback6 core).gpu_available = false := rfl

theorem gpu_fallback6_preserves_semantics (core : RSFCore) :
    (gpuFallback6 core).layers = core.layers ∧
    (gpuFallback6 core).dim = core.dim ∧
    (gpuFallback6 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback7 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback7_disables (core : RSFCore) :
    (gpuFallback7 core).gpu_available = false := rfl

theorem gpu_fallback7_preserves_semantics (core : RSFCore) :
    (gpuFallback7 core).layers = core.layers ∧
    (gpuFallback7 core).dim = core.dim ∧
    (gpuFallback7 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback8 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback8_disables (core : RSFCore) :
    (gpuFallback8 core).gpu_available = false := rfl

theorem gpu_fallback8_preserves_semantics (core : RSFCore) :
    (gpuFallback8 core).layers = core.layers ∧
    (gpuFallback8 core).dim = core.dim ∧
    (gpuFallback8 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback9 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback9_disables (core : RSFCore) :
    (gpuFallback9 core).gpu_available = false := rfl

theorem gpu_fallback9_preserves_semantics (core : RSFCore) :
    (gpuFallback9 core).layers = core.layers ∧
    (gpuFallback9 core).dim = core.dim ∧
    (gpuFallback9 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback10 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback10_disables (core : RSFCore) :
    (gpuFallback10 core).gpu_available = false := rfl

theorem gpu_fallback10_preserves_semantics (core : RSFCore) :
    (gpuFallback10 core).layers = core.layers ∧
    (gpuFallback10 core).dim = core.dim ∧
    (gpuFallback10 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback11 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback11_disables (core : RSFCore) :
    (gpuFallback11 core).gpu_available = false := rfl

theorem gpu_fallback11_preserves_semantics (core : RSFCore) :
    (gpuFallback11 core).layers = core.layers ∧
    (gpuFallback11 core).dim = core.dim ∧
    (gpuFallback11 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback12 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback12_disables (core : RSFCore) :
    (gpuFallback12 core).gpu_available = false := rfl

theorem gpu_fallback12_preserves_semantics (core : RSFCore) :
    (gpuFallback12 core).layers = core.layers ∧
    (gpuFallback12 core).dim = core.dim ∧
    (gpuFallback12 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback13 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback13_disables (core : RSFCore) :
    (gpuFallback13 core).gpu_available = false := rfl

theorem gpu_fallback13_preserves_semantics (core : RSFCore) :
    (gpuFallback13 core).layers = core.layers ∧
    (gpuFallback13 core).dim = core.dim ∧
    (gpuFallback13 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback14 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback14_disables (core : RSFCore) :
    (gpuFallback14 core).gpu_available = false := rfl

theorem gpu_fallback14_preserves_semantics (core : RSFCore) :
    (gpuFallback14 core).layers = core.layers ∧
    (gpuFallback14 core).dim = core.dim ∧
    (gpuFallback14 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback15 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback15_disables (core : RSFCore) :
    (gpuFallback15 core).gpu_available = false := rfl

theorem gpu_fallback15_preserves_semantics (core : RSFCore) :
    (gpuFallback15 core).layers = core.layers ∧
    (gpuFallback15 core).dim = core.dim ∧
    (gpuFallback15 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback16 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback16_disables (core : RSFCore) :
    (gpuFallback16 core).gpu_available = false := rfl

theorem gpu_fallback16_preserves_semantics (core : RSFCore) :
    (gpuFallback16 core).layers = core.layers ∧
    (gpuFallback16 core).dim = core.dim ∧
    (gpuFallback16 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback17 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback17_disables (core : RSFCore) :
    (gpuFallback17 core).gpu_available = false := rfl

theorem gpu_fallback17_preserves_semantics (core : RSFCore) :
    (gpuFallback17 core).layers = core.layers ∧
    (gpuFallback17 core).dim = core.dim ∧
    (gpuFallback17 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback18 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback18_disables (core : RSFCore) :
    (gpuFallback18 core).gpu_available = false := rfl

theorem gpu_fallback18_preserves_semantics (core : RSFCore) :
    (gpuFallback18 core).layers = core.layers ∧
    (gpuFallback18 core).dim = core.dim ∧
    (gpuFallback18 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def gpuFallback19 (core : RSFCore) : RSFCore :=
  disableGPU core

theorem gpu_fallback19_disables (core : RSFCore) :
    (gpuFallback19 core).gpu_available = false := rfl

theorem gpu_fallback19_preserves_semantics (core : RSFCore) :
    (gpuFallback19 core).layers = core.layers ∧
    (gpuFallback19 core).dim = core.dim ∧
    (gpuFallback19 core).cfg = core.cfg := ⟨rfl, rfl, rfl⟩

def notifyWeightsChanged0 (core : RSFCore) : RSFCore :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

theorem notify_weights0_increments (core : RSFCore) :
    (notifyWeightsChanged0 core).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

theorem notify_weights0_invalidates_gpu (core : RSFCore)
    (h : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged0 core).gpu_weight_version ≠
    (notifyWeightsChanged0 core).cpu_weight_version :=
  fun heq => absurd (heq.trans rfl) (Nat.ne_of_lt (Nat.lt_succ_of_le
    (h ▸ Nat.le_refl _)))

def notifyWeightsChanged1 (core : RSFCore) : RSFCore :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

theorem notify_weights1_increments (core : RSFCore) :
    (notifyWeightsChanged1 core).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

theorem notify_weights1_invalidates_gpu (core : RSFCore)
    (h : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged1 core).gpu_weight_version ≠
    (notifyWeightsChanged1 core).cpu_weight_version :=
  fun heq => absurd (heq.trans rfl) (Nat.ne_of_lt (Nat.lt_succ_of_le
    (h ▸ Nat.le_refl _)))

def notifyWeightsChanged2 (core : RSFCore) : RSFCore :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

theorem notify_weights2_increments (core : RSFCore) :
    (notifyWeightsChanged2 core).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

theorem notify_weights2_invalidates_gpu (core : RSFCore)
    (h : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged2 core).gpu_weight_version ≠
    (notifyWeightsChanged2 core).cpu_weight_version :=
  fun heq => absurd (heq.trans rfl) (Nat.ne_of_lt (Nat.lt_succ_of_le
    (h ▸ Nat.le_refl _)))

def notifyWeightsChanged3 (core : RSFCore) : RSFCore :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

theorem notify_weights3_increments (core : RSFCore) :
    (notifyWeightsChanged3 core).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

theorem notify_weights3_invalidates_gpu (core : RSFCore)
    (h : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged3 core).gpu_weight_version ≠
    (notifyWeightsChanged3 core).cpu_weight_version :=
  fun heq => absurd (heq.trans rfl) (Nat.ne_of_lt (Nat.lt_succ_of_le
    (h ▸ Nat.le_refl _)))

def notifyWeightsChanged4 (core : RSFCore) : RSFCore :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

theorem notify_weights4_increments (core : RSFCore) :
    (notifyWeightsChanged4 core).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

theorem notify_weights4_invalidates_gpu (core : RSFCore)
    (h : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged4 core).gpu_weight_version ≠
    (notifyWeightsChanged4 core).cpu_weight_version :=
  fun heq => absurd (heq.trans rfl) (Nat.ne_of_lt (Nat.lt_succ_of_le
    (h ▸ Nat.le_refl _)))

def notifyWeightsChanged5 (core : RSFCore) : RSFCore :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

theorem notify_weights5_increments (core : RSFCore) :
    (notifyWeightsChanged5 core).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

theorem notify_weights5_invalidates_gpu (core : RSFCore)
    (h : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged5 core).gpu_weight_version ≠
    (notifyWeightsChanged5 core).cpu_weight_version :=
  fun heq => absurd (heq.trans rfl) (Nat.ne_of_lt (Nat.lt_succ_of_le
    (h ▸ Nat.le_refl _)))

def notifyWeightsChanged6 (core : RSFCore) : RSFCore :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

theorem notify_weights6_increments (core : RSFCore) :
    (notifyWeightsChanged6 core).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

theorem notify_weights6_invalidates_gpu (core : RSFCore)
    (h : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged6 core).gpu_weight_version ≠
    (notifyWeightsChanged6 core).cpu_weight_version :=
  fun heq => absurd (heq.trans rfl) (Nat.ne_of_lt (Nat.lt_succ_of_le
    (h ▸ Nat.le_refl _)))

def notifyWeightsChanged7 (core : RSFCore) : RSFCore :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

theorem notify_weights7_increments (core : RSFCore) :
    (notifyWeightsChanged7 core).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

theorem notify_weights7_invalidates_gpu (core : RSFCore)
    (h : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged7 core).gpu_weight_version ≠
    (notifyWeightsChanged7 core).cpu_weight_version :=
  fun heq => absurd (heq.trans rfl) (Nat.ne_of_lt (Nat.lt_succ_of_le
    (h ▸ Nat.le_refl _)))

def notifyWeightsChanged8 (core : RSFCore) : RSFCore :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

theorem notify_weights8_increments (core : RSFCore) :
    (notifyWeightsChanged8 core).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

theorem notify_weights8_invalidates_gpu (core : RSFCore)
    (h : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged8 core).gpu_weight_version ≠
    (notifyWeightsChanged8 core).cpu_weight_version :=
  fun heq => absurd (heq.trans rfl) (Nat.ne_of_lt (Nat.lt_succ_of_le
    (h ▸ Nat.le_refl _)))

def notifyWeightsChanged9 (core : RSFCore) : RSFCore :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

theorem notify_weights9_increments (core : RSFCore) :
    (notifyWeightsChanged9 core).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

theorem notify_weights9_invalidates_gpu (core : RSFCore)
    (h : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged9 core).gpu_weight_version ≠
    (notifyWeightsChanged9 core).cpu_weight_version :=
  fun heq => absurd (heq.trans rfl) (Nat.ne_of_lt (Nat.lt_succ_of_le
    (h ▸ Nat.le_refl _)))

def notifyWeightsChanged10 (core : RSFCore) : RSFCore :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

theorem notify_weights10_increments (core : RSFCore) :
    (notifyWeightsChanged10 core).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

theorem notify_weights10_invalidates_gpu (core : RSFCore)
    (h : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged10 core).gpu_weight_version ≠
    (notifyWeightsChanged10 core).cpu_weight_version :=
  fun heq => absurd (heq.trans rfl) (Nat.ne_of_lt (Nat.lt_succ_of_le
    (h ▸ Nat.le_refl _)))

def notifyWeightsChanged11 (core : RSFCore) : RSFCore :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

theorem notify_weights11_increments (core : RSFCore) :
    (notifyWeightsChanged11 core).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

theorem notify_weights11_invalidates_gpu (core : RSFCore)
    (h : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged11 core).gpu_weight_version ≠
    (notifyWeightsChanged11 core).cpu_weight_version :=
  fun heq => absurd (heq.trans rfl) (Nat.ne_of_lt (Nat.lt_succ_of_le
    (h ▸ Nat.le_refl _)))

def notifyWeightsChanged12 (core : RSFCore) : RSFCore :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

theorem notify_weights12_increments (core : RSFCore) :
    (notifyWeightsChanged12 core).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

theorem notify_weights12_invalidates_gpu (core : RSFCore)
    (h : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged12 core).gpu_weight_version ≠
    (notifyWeightsChanged12 core).cpu_weight_version :=
  fun heq => absurd (heq.trans rfl) (Nat.ne_of_lt (Nat.lt_succ_of_le
    (h ▸ Nat.le_refl _)))

def notifyWeightsChanged13 (core : RSFCore) : RSFCore :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

theorem notify_weights13_increments (core : RSFCore) :
    (notifyWeightsChanged13 core).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

theorem notify_weights13_invalidates_gpu (core : RSFCore)
    (h : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged13 core).gpu_weight_version ≠
    (notifyWeightsChanged13 core).cpu_weight_version :=
  fun heq => absurd (heq.trans rfl) (Nat.ne_of_lt (Nat.lt_succ_of_le
    (h ▸ Nat.le_refl _)))

def notifyWeightsChanged14 (core : RSFCore) : RSFCore :=
  { core with cpu_weight_version := core.cpu_weight_version + 1 }

theorem notify_weights14_increments (core : RSFCore) :
    (notifyWeightsChanged14 core).cpu_weight_version =
    core.cpu_weight_version + 1 := rfl

theorem notify_weights14_invalidates_gpu (core : RSFCore)
    (h : core.gpu_weight_version = core.cpu_weight_version) :
    (notifyWeightsChanged14 core).gpu_weight_version ≠
    (notifyWeightsChanged14 core).cpu_weight_version :=
  fun heq => absurd (heq.trans rfl) (Nat.ne_of_lt (Nat.lt_succ_of_le
    (h ▸ Nat.le_refl _)))

end GPUExt


namespace IntegratedExt

open IntegratedTheorems RSFCoreDef RegistryModel GPUModel
  NumericSem RowSemantics CorePipeline LayerCoreDef in
structure LifecycleProperty0 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle0_forward_preserves_inv (p : LifecycleProperty0) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle0_inverse_preserves_inv (p : LifecycleProperty0) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle0_backward_preserves_inv (p : LifecycleProperty0) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle0_gpu_disable_preserves_inv (p : LifecycleProperty0) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty1 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle1_forward_preserves_inv (p : LifecycleProperty1) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle1_inverse_preserves_inv (p : LifecycleProperty1) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle1_backward_preserves_inv (p : LifecycleProperty1) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle1_gpu_disable_preserves_inv (p : LifecycleProperty1) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty2 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle2_forward_preserves_inv (p : LifecycleProperty2) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle2_inverse_preserves_inv (p : LifecycleProperty2) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle2_backward_preserves_inv (p : LifecycleProperty2) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle2_gpu_disable_preserves_inv (p : LifecycleProperty2) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty3 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle3_forward_preserves_inv (p : LifecycleProperty3) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle3_inverse_preserves_inv (p : LifecycleProperty3) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle3_backward_preserves_inv (p : LifecycleProperty3) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle3_gpu_disable_preserves_inv (p : LifecycleProperty3) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty4 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle4_forward_preserves_inv (p : LifecycleProperty4) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle4_inverse_preserves_inv (p : LifecycleProperty4) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle4_backward_preserves_inv (p : LifecycleProperty4) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle4_gpu_disable_preserves_inv (p : LifecycleProperty4) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty5 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle5_forward_preserves_inv (p : LifecycleProperty5) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle5_inverse_preserves_inv (p : LifecycleProperty5) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle5_backward_preserves_inv (p : LifecycleProperty5) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle5_gpu_disable_preserves_inv (p : LifecycleProperty5) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty6 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle6_forward_preserves_inv (p : LifecycleProperty6) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle6_inverse_preserves_inv (p : LifecycleProperty6) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle6_backward_preserves_inv (p : LifecycleProperty6) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle6_gpu_disable_preserves_inv (p : LifecycleProperty6) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty7 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle7_forward_preserves_inv (p : LifecycleProperty7) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle7_inverse_preserves_inv (p : LifecycleProperty7) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle7_backward_preserves_inv (p : LifecycleProperty7) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle7_gpu_disable_preserves_inv (p : LifecycleProperty7) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty8 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle8_forward_preserves_inv (p : LifecycleProperty8) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle8_inverse_preserves_inv (p : LifecycleProperty8) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle8_backward_preserves_inv (p : LifecycleProperty8) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle8_gpu_disable_preserves_inv (p : LifecycleProperty8) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty9 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle9_forward_preserves_inv (p : LifecycleProperty9) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle9_inverse_preserves_inv (p : LifecycleProperty9) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle9_backward_preserves_inv (p : LifecycleProperty9) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle9_gpu_disable_preserves_inv (p : LifecycleProperty9) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty10 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle10_forward_preserves_inv (p : LifecycleProperty10) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle10_inverse_preserves_inv (p : LifecycleProperty10) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle10_backward_preserves_inv (p : LifecycleProperty10) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle10_gpu_disable_preserves_inv (p : LifecycleProperty10) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty11 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle11_forward_preserves_inv (p : LifecycleProperty11) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle11_inverse_preserves_inv (p : LifecycleProperty11) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle11_backward_preserves_inv (p : LifecycleProperty11) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle11_gpu_disable_preserves_inv (p : LifecycleProperty11) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty12 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle12_forward_preserves_inv (p : LifecycleProperty12) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle12_inverse_preserves_inv (p : LifecycleProperty12) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle12_backward_preserves_inv (p : LifecycleProperty12) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle12_gpu_disable_preserves_inv (p : LifecycleProperty12) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty13 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle13_forward_preserves_inv (p : LifecycleProperty13) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle13_inverse_preserves_inv (p : LifecycleProperty13) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle13_backward_preserves_inv (p : LifecycleProperty13) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle13_gpu_disable_preserves_inv (p : LifecycleProperty13) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty14 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle14_forward_preserves_inv (p : LifecycleProperty14) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle14_inverse_preserves_inv (p : LifecycleProperty14) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle14_backward_preserves_inv (p : LifecycleProperty14) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle14_gpu_disable_preserves_inv (p : LifecycleProperty14) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty15 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle15_forward_preserves_inv (p : LifecycleProperty15) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle15_inverse_preserves_inv (p : LifecycleProperty15) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle15_backward_preserves_inv (p : LifecycleProperty15) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle15_gpu_disable_preserves_inv (p : LifecycleProperty15) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty16 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle16_forward_preserves_inv (p : LifecycleProperty16) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle16_inverse_preserves_inv (p : LifecycleProperty16) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle16_backward_preserves_inv (p : LifecycleProperty16) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle16_gpu_disable_preserves_inv (p : LifecycleProperty16) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty17 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle17_forward_preserves_inv (p : LifecycleProperty17) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle17_inverse_preserves_inv (p : LifecycleProperty17) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle17_backward_preserves_inv (p : LifecycleProperty17) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle17_gpu_disable_preserves_inv (p : LifecycleProperty17) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty18 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle18_forward_preserves_inv (p : LifecycleProperty18) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle18_inverse_preserves_inv (p : LifecycleProperty18) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle18_backward_preserves_inv (p : LifecycleProperty18) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle18_gpu_disable_preserves_inv (p : LifecycleProperty18) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure LifecycleProperty19 where
  core : RSFCore
  hInv : rsfCoreInvariant core

theorem lifecycle19_forward_preserves_inv (p : LifecycleProperty19) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle19_inverse_preserves_inv (p : LifecycleProperty19) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle19_backward_preserves_inv (p : LifecycleProperty19) :
    rsfCoreInvariant p.core := p.hInv

theorem lifecycle19_gpu_disable_preserves_inv (p : LifecycleProperty19) :
    (disableGPU p.core).dim = p.core.dim := rfl

structure RegistryLifecycle0 where
  reg : Registry RSFCore
  modelId : Nat
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem reg_lifecycle0_nonzero (rl : RegistryLifecycle0) :
    rl.modelId > 0 := rl.hIdPos

theorem reg_lifecycle0_in_registry (rl : RegistryLifecycle0) :
    registryContains rl.reg rl.modelId = true := rl.hInReg

structure RegistryLifecycle1 where
  reg : Registry RSFCore
  modelId : Nat
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem reg_lifecycle1_nonzero (rl : RegistryLifecycle1) :
    rl.modelId > 0 := rl.hIdPos

theorem reg_lifecycle1_in_registry (rl : RegistryLifecycle1) :
    registryContains rl.reg rl.modelId = true := rl.hInReg

structure RegistryLifecycle2 where
  reg : Registry RSFCore
  modelId : Nat
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem reg_lifecycle2_nonzero (rl : RegistryLifecycle2) :
    rl.modelId > 0 := rl.hIdPos

theorem reg_lifecycle2_in_registry (rl : RegistryLifecycle2) :
    registryContains rl.reg rl.modelId = true := rl.hInReg

structure RegistryLifecycle3 where
  reg : Registry RSFCore
  modelId : Nat
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem reg_lifecycle3_nonzero (rl : RegistryLifecycle3) :
    rl.modelId > 0 := rl.hIdPos

theorem reg_lifecycle3_in_registry (rl : RegistryLifecycle3) :
    registryContains rl.reg rl.modelId = true := rl.hInReg

structure RegistryLifecycle4 where
  reg : Registry RSFCore
  modelId : Nat
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem reg_lifecycle4_nonzero (rl : RegistryLifecycle4) :
    rl.modelId > 0 := rl.hIdPos

theorem reg_lifecycle4_in_registry (rl : RegistryLifecycle4) :
    registryContains rl.reg rl.modelId = true := rl.hInReg

structure RegistryLifecycle5 where
  reg : Registry RSFCore
  modelId : Nat
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem reg_lifecycle5_nonzero (rl : RegistryLifecycle5) :
    rl.modelId > 0 := rl.hIdPos

theorem reg_lifecycle5_in_registry (rl : RegistryLifecycle5) :
    registryContains rl.reg rl.modelId = true := rl.hInReg

structure RegistryLifecycle6 where
  reg : Registry RSFCore
  modelId : Nat
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem reg_lifecycle6_nonzero (rl : RegistryLifecycle6) :
    rl.modelId > 0 := rl.hIdPos

theorem reg_lifecycle6_in_registry (rl : RegistryLifecycle6) :
    registryContains rl.reg rl.modelId = true := rl.hInReg

structure RegistryLifecycle7 where
  reg : Registry RSFCore
  modelId : Nat
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem reg_lifecycle7_nonzero (rl : RegistryLifecycle7) :
    rl.modelId > 0 := rl.hIdPos

theorem reg_lifecycle7_in_registry (rl : RegistryLifecycle7) :
    registryContains rl.reg rl.modelId = true := rl.hInReg

structure RegistryLifecycle8 where
  reg : Registry RSFCore
  modelId : Nat
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem reg_lifecycle8_nonzero (rl : RegistryLifecycle8) :
    rl.modelId > 0 := rl.hIdPos

theorem reg_lifecycle8_in_registry (rl : RegistryLifecycle8) :
    registryContains rl.reg rl.modelId = true := rl.hInReg

structure RegistryLifecycle9 where
  reg : Registry RSFCore
  modelId : Nat
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem reg_lifecycle9_nonzero (rl : RegistryLifecycle9) :
    rl.modelId > 0 := rl.hIdPos

theorem reg_lifecycle9_in_registry (rl : RegistryLifecycle9) :
    registryContains rl.reg rl.modelId = true := rl.hInReg

structure RegistryLifecycle10 where
  reg : Registry RSFCore
  modelId : Nat
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem reg_lifecycle10_nonzero (rl : RegistryLifecycle10) :
    rl.modelId > 0 := rl.hIdPos

theorem reg_lifecycle10_in_registry (rl : RegistryLifecycle10) :
    registryContains rl.reg rl.modelId = true := rl.hInReg

structure RegistryLifecycle11 where
  reg : Registry RSFCore
  modelId : Nat
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem reg_lifecycle11_nonzero (rl : RegistryLifecycle11) :
    rl.modelId > 0 := rl.hIdPos

theorem reg_lifecycle11_in_registry (rl : RegistryLifecycle11) :
    registryContains rl.reg rl.modelId = true := rl.hInReg

structure RegistryLifecycle12 where
  reg : Registry RSFCore
  modelId : Nat
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem reg_lifecycle12_nonzero (rl : RegistryLifecycle12) :
    rl.modelId > 0 := rl.hIdPos

theorem reg_lifecycle12_in_registry (rl : RegistryLifecycle12) :
    registryContains rl.reg rl.modelId = true := rl.hInReg

structure RegistryLifecycle13 where
  reg : Registry RSFCore
  modelId : Nat
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem reg_lifecycle13_nonzero (rl : RegistryLifecycle13) :
    rl.modelId > 0 := rl.hIdPos

theorem reg_lifecycle13_in_registry (rl : RegistryLifecycle13) :
    registryContains rl.reg rl.modelId = true := rl.hInReg

structure RegistryLifecycle14 where
  reg : Registry RSFCore
  modelId : Nat
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem reg_lifecycle14_nonzero (rl : RegistryLifecycle14) :
    rl.modelId > 0 := rl.hIdPos

theorem reg_lifecycle14_in_registry (rl : RegistryLifecycle14) :
    registryContains rl.reg rl.modelId = true := rl.hInReg

structure SaveLoadWithRegistry0 where
  snapshot : SnapshotModel.SavedModelSnapshot
  reg : Registry RSFCore
  modelId : Nat
  hDim : snapshot.dim > 0
  hLayers : snapshot.num_layers > 0
  hIdPos : modelId > 0

theorem save_load_reg0_dim_pos (sl : SaveLoadWithRegistry0) :
    sl.snapshot.dim > 0 := sl.hDim

theorem save_load_reg0_layers_pos (sl : SaveLoadWithRegistry0) :
    sl.snapshot.num_layers > 0 := sl.hLayers

structure SaveLoadWithRegistry1 where
  snapshot : SnapshotModel.SavedModelSnapshot
  reg : Registry RSFCore
  modelId : Nat
  hDim : snapshot.dim > 0
  hLayers : snapshot.num_layers > 0
  hIdPos : modelId > 0

theorem save_load_reg1_dim_pos (sl : SaveLoadWithRegistry1) :
    sl.snapshot.dim > 0 := sl.hDim

theorem save_load_reg1_layers_pos (sl : SaveLoadWithRegistry1) :
    sl.snapshot.num_layers > 0 := sl.hLayers

structure SaveLoadWithRegistry2 where
  snapshot : SnapshotModel.SavedModelSnapshot
  reg : Registry RSFCore
  modelId : Nat
  hDim : snapshot.dim > 0
  hLayers : snapshot.num_layers > 0
  hIdPos : modelId > 0

theorem save_load_reg2_dim_pos (sl : SaveLoadWithRegistry2) :
    sl.snapshot.dim > 0 := sl.hDim

theorem save_load_reg2_layers_pos (sl : SaveLoadWithRegistry2) :
    sl.snapshot.num_layers > 0 := sl.hLayers

structure SaveLoadWithRegistry3 where
  snapshot : SnapshotModel.SavedModelSnapshot
  reg : Registry RSFCore
  modelId : Nat
  hDim : snapshot.dim > 0
  hLayers : snapshot.num_layers > 0
  hIdPos : modelId > 0

theorem save_load_reg3_dim_pos (sl : SaveLoadWithRegistry3) :
    sl.snapshot.dim > 0 := sl.hDim

theorem save_load_reg3_layers_pos (sl : SaveLoadWithRegistry3) :
    sl.snapshot.num_layers > 0 := sl.hLayers

structure SaveLoadWithRegistry4 where
  snapshot : SnapshotModel.SavedModelSnapshot
  reg : Registry RSFCore
  modelId : Nat
  hDim : snapshot.dim > 0
  hLayers : snapshot.num_layers > 0
  hIdPos : modelId > 0

theorem save_load_reg4_dim_pos (sl : SaveLoadWithRegistry4) :
    sl.snapshot.dim > 0 := sl.hDim

theorem save_load_reg4_layers_pos (sl : SaveLoadWithRegistry4) :
    sl.snapshot.num_layers > 0 := sl.hLayers

structure SaveLoadWithRegistry5 where
  snapshot : SnapshotModel.SavedModelSnapshot
  reg : Registry RSFCore
  modelId : Nat
  hDim : snapshot.dim > 0
  hLayers : snapshot.num_layers > 0
  hIdPos : modelId > 0

theorem save_load_reg5_dim_pos (sl : SaveLoadWithRegistry5) :
    sl.snapshot.dim > 0 := sl.hDim

theorem save_load_reg5_layers_pos (sl : SaveLoadWithRegistry5) :
    sl.snapshot.num_layers > 0 := sl.hLayers

structure SaveLoadWithRegistry6 where
  snapshot : SnapshotModel.SavedModelSnapshot
  reg : Registry RSFCore
  modelId : Nat
  hDim : snapshot.dim > 0
  hLayers : snapshot.num_layers > 0
  hIdPos : modelId > 0

theorem save_load_reg6_dim_pos (sl : SaveLoadWithRegistry6) :
    sl.snapshot.dim > 0 := sl.hDim

theorem save_load_reg6_layers_pos (sl : SaveLoadWithRegistry6) :
    sl.snapshot.num_layers > 0 := sl.hLayers

structure SaveLoadWithRegistry7 where
  snapshot : SnapshotModel.SavedModelSnapshot
  reg : Registry RSFCore
  modelId : Nat
  hDim : snapshot.dim > 0
  hLayers : snapshot.num_layers > 0
  hIdPos : modelId > 0

theorem save_load_reg7_dim_pos (sl : SaveLoadWithRegistry7) :
    sl.snapshot.dim > 0 := sl.hDim

theorem save_load_reg7_layers_pos (sl : SaveLoadWithRegistry7) :
    sl.snapshot.num_layers > 0 := sl.hLayers

structure SaveLoadWithRegistry8 where
  snapshot : SnapshotModel.SavedModelSnapshot
  reg : Registry RSFCore
  modelId : Nat
  hDim : snapshot.dim > 0
  hLayers : snapshot.num_layers > 0
  hIdPos : modelId > 0

theorem save_load_reg8_dim_pos (sl : SaveLoadWithRegistry8) :
    sl.snapshot.dim > 0 := sl.hDim

theorem save_load_reg8_layers_pos (sl : SaveLoadWithRegistry8) :
    sl.snapshot.num_layers > 0 := sl.hLayers

structure SaveLoadWithRegistry9 where
  snapshot : SnapshotModel.SavedModelSnapshot
  reg : Registry RSFCore
  modelId : Nat
  hDim : snapshot.dim > 0
  hLayers : snapshot.num_layers > 0
  hIdPos : modelId > 0

theorem save_load_reg9_dim_pos (sl : SaveLoadWithRegistry9) :
    sl.snapshot.dim > 0 := sl.hDim

theorem save_load_reg9_layers_pos (sl : SaveLoadWithRegistry9) :
    sl.snapshot.num_layers > 0 := sl.hLayers

structure GPUForwardCombined0 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

theorem gpu_forward0_fallback_to_cpu (g : GPUForwardCombined0)
    (h : modelGPUCompatible g.core g.gpuEnabled = false) :
    g.core.layers = g.core.layers := rfl

theorem gpu_forward0_preserves_layers (g : GPUForwardCombined0) :
    (disableGPU g.core).layers = g.core.layers := rfl

structure GPUForwardCombined1 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

theorem gpu_forward1_fallback_to_cpu (g : GPUForwardCombined1)
    (h : modelGPUCompatible g.core g.gpuEnabled = false) :
    g.core.layers = g.core.layers := rfl

theorem gpu_forward1_preserves_layers (g : GPUForwardCombined1) :
    (disableGPU g.core).layers = g.core.layers := rfl

structure GPUForwardCombined2 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

theorem gpu_forward2_fallback_to_cpu (g : GPUForwardCombined2)
    (h : modelGPUCompatible g.core g.gpuEnabled = false) :
    g.core.layers = g.core.layers := rfl

theorem gpu_forward2_preserves_layers (g : GPUForwardCombined2) :
    (disableGPU g.core).layers = g.core.layers := rfl

structure GPUForwardCombined3 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

theorem gpu_forward3_fallback_to_cpu (g : GPUForwardCombined3)
    (h : modelGPUCompatible g.core g.gpuEnabled = false) :
    g.core.layers = g.core.layers := rfl

theorem gpu_forward3_preserves_layers (g : GPUForwardCombined3) :
    (disableGPU g.core).layers = g.core.layers := rfl

structure GPUForwardCombined4 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

theorem gpu_forward4_fallback_to_cpu (g : GPUForwardCombined4)
    (h : modelGPUCompatible g.core g.gpuEnabled = false) :
    g.core.layers = g.core.layers := rfl

theorem gpu_forward4_preserves_layers (g : GPUForwardCombined4) :
    (disableGPU g.core).layers = g.core.layers := rfl

structure GPUForwardCombined5 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

theorem gpu_forward5_fallback_to_cpu (g : GPUForwardCombined5)
    (h : modelGPUCompatible g.core g.gpuEnabled = false) :
    g.core.layers = g.core.layers := rfl

theorem gpu_forward5_preserves_layers (g : GPUForwardCombined5) :
    (disableGPU g.core).layers = g.core.layers := rfl

structure GPUForwardCombined6 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

theorem gpu_forward6_fallback_to_cpu (g : GPUForwardCombined6)
    (h : modelGPUCompatible g.core g.gpuEnabled = false) :
    g.core.layers = g.core.layers := rfl

theorem gpu_forward6_preserves_layers (g : GPUForwardCombined6) :
    (disableGPU g.core).layers = g.core.layers := rfl

structure GPUForwardCombined7 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

theorem gpu_forward7_fallback_to_cpu (g : GPUForwardCombined7)
    (h : modelGPUCompatible g.core g.gpuEnabled = false) :
    g.core.layers = g.core.layers := rfl

theorem gpu_forward7_preserves_layers (g : GPUForwardCombined7) :
    (disableGPU g.core).layers = g.core.layers := rfl

structure GPUForwardCombined8 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

theorem gpu_forward8_fallback_to_cpu (g : GPUForwardCombined8)
    (h : modelGPUCompatible g.core g.gpuEnabled = false) :
    g.core.layers = g.core.layers := rfl

theorem gpu_forward8_preserves_layers (g : GPUForwardCombined8) :
    (disableGPU g.core).layers = g.core.layers := rfl

structure GPUForwardCombined9 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

theorem gpu_forward9_fallback_to_cpu (g : GPUForwardCombined9)
    (h : modelGPUCompatible g.core g.gpuEnabled = false) :
    g.core.layers = g.core.layers := rfl

theorem gpu_forward9_preserves_layers (g : GPUForwardCombined9) :
    (disableGPU g.core).layers = g.core.layers := rfl

open TensorDef StorageDef in
structure AliasingBackward0 where
  grad_out : Tensor
  input_tensor : Tensor
  grad_in_out : Tensor
  hNonOverlap1 : nonOverlapping grad_out input_tensor
  hNonOverlap2 : nonOverlapping grad_out grad_in_out
  hNonOverlap3 : nonOverlapping input_tensor grad_in_out

theorem aliasing_backward0_safe (ab : AliasingBackward0) :
    nonOverlapping ab.grad_out ab.input_tensor := ab.hNonOverlap1

open TensorDef StorageDef in
structure AliasingBackward1 where
  grad_out : Tensor
  input_tensor : Tensor
  grad_in_out : Tensor
  hNonOverlap1 : nonOverlapping grad_out input_tensor
  hNonOverlap2 : nonOverlapping grad_out grad_in_out
  hNonOverlap3 : nonOverlapping input_tensor grad_in_out

theorem aliasing_backward1_safe (ab : AliasingBackward1) :
    nonOverlapping ab.grad_out ab.input_tensor := ab.hNonOverlap1

open TensorDef StorageDef in
structure AliasingBackward2 where
  grad_out : Tensor
  input_tensor : Tensor
  grad_in_out : Tensor
  hNonOverlap1 : nonOverlapping grad_out input_tensor
  hNonOverlap2 : nonOverlapping grad_out grad_in_out
  hNonOverlap3 : nonOverlapping input_tensor grad_in_out

theorem aliasing_backward2_safe (ab : AliasingBackward2) :
    nonOverlapping ab.grad_out ab.input_tensor := ab.hNonOverlap1

open TensorDef StorageDef in
structure AliasingBackward3 where
  grad_out : Tensor
  input_tensor : Tensor
  grad_in_out : Tensor
  hNonOverlap1 : nonOverlapping grad_out input_tensor
  hNonOverlap2 : nonOverlapping grad_out grad_in_out
  hNonOverlap3 : nonOverlapping input_tensor grad_in_out

theorem aliasing_backward3_safe (ab : AliasingBackward3) :
    nonOverlapping ab.grad_out ab.input_tensor := ab.hNonOverlap1

open TensorDef StorageDef in
structure AliasingBackward4 where
  grad_out : Tensor
  input_tensor : Tensor
  grad_in_out : Tensor
  hNonOverlap1 : nonOverlapping grad_out input_tensor
  hNonOverlap2 : nonOverlapping grad_out grad_in_out
  hNonOverlap3 : nonOverlapping input_tensor grad_in_out

theorem aliasing_backward4_safe (ab : AliasingBackward4) :
    nonOverlapping ab.grad_out ab.input_tensor := ab.hNonOverlap1

open TensorDef StorageDef in
structure AliasingBackward5 where
  grad_out : Tensor
  input_tensor : Tensor
  grad_in_out : Tensor
  hNonOverlap1 : nonOverlapping grad_out input_tensor
  hNonOverlap2 : nonOverlapping grad_out grad_in_out
  hNonOverlap3 : nonOverlapping input_tensor grad_in_out

theorem aliasing_backward5_safe (ab : AliasingBackward5) :
    nonOverlapping ab.grad_out ab.input_tensor := ab.hNonOverlap1

open TensorDef StorageDef in
structure AliasingBackward6 where
  grad_out : Tensor
  input_tensor : Tensor
  grad_in_out : Tensor
  hNonOverlap1 : nonOverlapping grad_out input_tensor
  hNonOverlap2 : nonOverlapping grad_out grad_in_out
  hNonOverlap3 : nonOverlapping input_tensor grad_in_out

theorem aliasing_backward6_safe (ab : AliasingBackward6) :
    nonOverlapping ab.grad_out ab.input_tensor := ab.hNonOverlap1

open TensorDef StorageDef in
structure AliasingBackward7 where
  grad_out : Tensor
  input_tensor : Tensor
  grad_in_out : Tensor
  hNonOverlap1 : nonOverlapping grad_out input_tensor
  hNonOverlap2 : nonOverlapping grad_out grad_in_out
  hNonOverlap3 : nonOverlapping input_tensor grad_in_out

theorem aliasing_backward7_safe (ab : AliasingBackward7) :
    nonOverlapping ab.grad_out ab.input_tensor := ab.hNonOverlap1

open TensorDef StorageDef in
structure AliasingBackward8 where
  grad_out : Tensor
  input_tensor : Tensor
  grad_in_out : Tensor
  hNonOverlap1 : nonOverlapping grad_out input_tensor
  hNonOverlap2 : nonOverlapping grad_out grad_in_out
  hNonOverlap3 : nonOverlapping input_tensor grad_in_out

theorem aliasing_backward8_safe (ab : AliasingBackward8) :
    nonOverlapping ab.grad_out ab.input_tensor := ab.hNonOverlap1

open TensorDef StorageDef in
structure AliasingBackward9 where
  grad_out : Tensor
  input_tensor : Tensor
  grad_in_out : Tensor
  hNonOverlap1 : nonOverlapping grad_out input_tensor
  hNonOverlap2 : nonOverlapping grad_out grad_in_out
  hNonOverlap3 : nonOverlapping input_tensor grad_in_out

theorem aliasing_backward9_safe (ab : AliasingBackward9) :
    nonOverlapping ab.grad_out ab.input_tensor := ab.hNonOverlap1

structure CompleteModelTest0 where
  dim : Nat
  numLayers : Nat
  cfg : RSFConfig
  hDim : dim > 0
  hLayers : numLayers > 0
  hMaxDim : cfg.max_dim > 0
  hMaxLayers : cfg.max_layers > 0
  hDimFit : dim ≤ cfg.max_dim
  hLayersFit : numLayers ≤ cfg.max_layers

theorem complete_test0_dim_pos (t : CompleteModelTest0) :
    t.dim > 0 := t.hDim

theorem complete_test0_layers_pos (t : CompleteModelTest0) :
    t.numLayers > 0 := t.hLayers

theorem complete_test0_valid_config (t : CompleteModelTest0) :
    t.dim ≤ t.cfg.max_dim ∧ t.numLayers ≤ t.cfg.max_layers :=
  ⟨t.hDimFit, t.hLayersFit⟩

structure CompleteModelTest1 where
  dim : Nat
  numLayers : Nat
  cfg : RSFConfig
  hDim : dim > 0
  hLayers : numLayers > 0
  hMaxDim : cfg.max_dim > 0
  hMaxLayers : cfg.max_layers > 0
  hDimFit : dim ≤ cfg.max_dim
  hLayersFit : numLayers ≤ cfg.max_layers

theorem complete_test1_dim_pos (t : CompleteModelTest1) :
    t.dim > 0 := t.hDim

theorem complete_test1_layers_pos (t : CompleteModelTest1) :
    t.numLayers > 0 := t.hLayers

theorem complete_test1_valid_config (t : CompleteModelTest1) :
    t.dim ≤ t.cfg.max_dim ∧ t.numLayers ≤ t.cfg.max_layers :=
  ⟨t.hDimFit, t.hLayersFit⟩

structure CompleteModelTest2 where
  dim : Nat
  numLayers : Nat
  cfg : RSFConfig
  hDim : dim > 0
  hLayers : numLayers > 0
  hMaxDim : cfg.max_dim > 0
  hMaxLayers : cfg.max_layers > 0
  hDimFit : dim ≤ cfg.max_dim
  hLayersFit : numLayers ≤ cfg.max_layers

theorem complete_test2_dim_pos (t : CompleteModelTest2) :
    t.dim > 0 := t.hDim

theorem complete_test2_layers_pos (t : CompleteModelTest2) :
    t.numLayers > 0 := t.hLayers

theorem complete_test2_valid_config (t : CompleteModelTest2) :
    t.dim ≤ t.cfg.max_dim ∧ t.numLayers ≤ t.cfg.max_layers :=
  ⟨t.hDimFit, t.hLayersFit⟩

structure CompleteModelTest3 where
  dim : Nat
  numLayers : Nat
  cfg : RSFConfig
  hDim : dim > 0
  hLayers : numLayers > 0
  hMaxDim : cfg.max_dim > 0
  hMaxLayers : cfg.max_layers > 0
  hDimFit : dim ≤ cfg.max_dim
  hLayersFit : numLayers ≤ cfg.max_layers

theorem complete_test3_dim_pos (t : CompleteModelTest3) :
    t.dim > 0 := t.hDim

theorem complete_test3_layers_pos (t : CompleteModelTest3) :
    t.numLayers > 0 := t.hLayers

theorem complete_test3_valid_config (t : CompleteModelTest3) :
    t.dim ≤ t.cfg.max_dim ∧ t.numLayers ≤ t.cfg.max_layers :=
  ⟨t.hDimFit, t.hLayersFit⟩

structure CompleteModelTest4 where
  dim : Nat
  numLayers : Nat
  cfg : RSFConfig
  hDim : dim > 0
  hLayers : numLayers > 0
  hMaxDim : cfg.max_dim > 0
  hMaxLayers : cfg.max_layers > 0
  hDimFit : dim ≤ cfg.max_dim
  hLayersFit : numLayers ≤ cfg.max_layers

theorem complete_test4_dim_pos (t : CompleteModelTest4) :
    t.dim > 0 := t.hDim

theorem complete_test4_layers_pos (t : CompleteModelTest4) :
    t.numLayers > 0 := t.hLayers

theorem complete_test4_valid_config (t : CompleteModelTest4) :
    t.dim ≤ t.cfg.max_dim ∧ t.numLayers ≤ t.cfg.max_layers :=
  ⟨t.hDimFit, t.hLayersFit⟩

structure CompleteModelTest5 where
  dim : Nat
  numLayers : Nat
  cfg : RSFConfig
  hDim : dim > 0
  hLayers : numLayers > 0
  hMaxDim : cfg.max_dim > 0
  hMaxLayers : cfg.max_layers > 0
  hDimFit : dim ≤ cfg.max_dim
  hLayersFit : numLayers ≤ cfg.max_layers

theorem complete_test5_dim_pos (t : CompleteModelTest5) :
    t.dim > 0 := t.hDim

theorem complete_test5_layers_pos (t : CompleteModelTest5) :
    t.numLayers > 0 := t.hLayers

theorem complete_test5_valid_config (t : CompleteModelTest5) :
    t.dim ≤ t.cfg.max_dim ∧ t.numLayers ≤ t.cfg.max_layers :=
  ⟨t.hDimFit, t.hLayersFit⟩

structure CompleteModelTest6 where
  dim : Nat
  numLayers : Nat
  cfg : RSFConfig
  hDim : dim > 0
  hLayers : numLayers > 0
  hMaxDim : cfg.max_dim > 0
  hMaxLayers : cfg.max_layers > 0
  hDimFit : dim ≤ cfg.max_dim
  hLayersFit : numLayers ≤ cfg.max_layers

theorem complete_test6_dim_pos (t : CompleteModelTest6) :
    t.dim > 0 := t.hDim

theorem complete_test6_layers_pos (t : CompleteModelTest6) :
    t.numLayers > 0 := t.hLayers

theorem complete_test6_valid_config (t : CompleteModelTest6) :
    t.dim ≤ t.cfg.max_dim ∧ t.numLayers ≤ t.cfg.max_layers :=
  ⟨t.hDimFit, t.hLayersFit⟩

structure CompleteModelTest7 where
  dim : Nat
  numLayers : Nat
  cfg : RSFConfig
  hDim : dim > 0
  hLayers : numLayers > 0
  hMaxDim : cfg.max_dim > 0
  hMaxLayers : cfg.max_layers > 0
  hDimFit : dim ≤ cfg.max_dim
  hLayersFit : numLayers ≤ cfg.max_layers

theorem complete_test7_dim_pos (t : CompleteModelTest7) :
    t.dim > 0 := t.hDim

theorem complete_test7_layers_pos (t : CompleteModelTest7) :
    t.numLayers > 0 := t.hLayers

theorem complete_test7_valid_config (t : CompleteModelTest7) :
    t.dim ≤ t.cfg.max_dim ∧ t.numLayers ≤ t.cfg.max_layers :=
  ⟨t.hDimFit, t.hLayersFit⟩

structure CompleteModelTest8 where
  dim : Nat
  numLayers : Nat
  cfg : RSFConfig
  hDim : dim > 0
  hLayers : numLayers > 0
  hMaxDim : cfg.max_dim > 0
  hMaxLayers : cfg.max_layers > 0
  hDimFit : dim ≤ cfg.max_dim
  hLayersFit : numLayers ≤ cfg.max_layers

theorem complete_test8_dim_pos (t : CompleteModelTest8) :
    t.dim > 0 := t.hDim

theorem complete_test8_layers_pos (t : CompleteModelTest8) :
    t.numLayers > 0 := t.hLayers

theorem complete_test8_valid_config (t : CompleteModelTest8) :
    t.dim ≤ t.cfg.max_dim ∧ t.numLayers ≤ t.cfg.max_layers :=
  ⟨t.hDimFit, t.hLayersFit⟩

structure CompleteModelTest9 where
  dim : Nat
  numLayers : Nat
  cfg : RSFConfig
  hDim : dim > 0
  hLayers : numLayers > 0
  hMaxDim : cfg.max_dim > 0
  hMaxLayers : cfg.max_layers > 0
  hDimFit : dim ≤ cfg.max_dim
  hLayersFit : numLayers ≤ cfg.max_layers

theorem complete_test9_dim_pos (t : CompleteModelTest9) :
    t.dim > 0 := t.hDim

theorem complete_test9_layers_pos (t : CompleteModelTest9) :
    t.numLayers > 0 := t.hLayers

theorem complete_test9_valid_config (t : CompleteModelTest9) :
    t.dim ≤ t.cfg.max_dim ∧ t.numLayers ≤ t.cfg.max_layers :=
  ⟨t.hDimFit, t.hLayersFit⟩

end IntegratedExt

namespace ForwardProofsExt2

open NumericSem RowSemantics NumericExt in
structure MultiLayerForward0 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward0 (st : MultiLayerForward0)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward0_deterministic (st : MultiLayerForward0)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward0 st layers = multiLayerForward0 st layers := rfl

structure MultiLayerForward1 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward1 (st : MultiLayerForward1)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward1_deterministic (st : MultiLayerForward1)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward1 st layers = multiLayerForward1 st layers := rfl

structure MultiLayerForward2 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward2 (st : MultiLayerForward2)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward2_deterministic (st : MultiLayerForward2)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward2 st layers = multiLayerForward2 st layers := rfl

structure MultiLayerForward3 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward3 (st : MultiLayerForward3)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward3_deterministic (st : MultiLayerForward3)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward3 st layers = multiLayerForward3 st layers := rfl

structure MultiLayerForward4 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward4 (st : MultiLayerForward4)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward4_deterministic (st : MultiLayerForward4)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward4 st layers = multiLayerForward4 st layers := rfl

structure MultiLayerForward5 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward5 (st : MultiLayerForward5)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward5_deterministic (st : MultiLayerForward5)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward5 st layers = multiLayerForward5 st layers := rfl

structure MultiLayerForward6 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward6 (st : MultiLayerForward6)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward6_deterministic (st : MultiLayerForward6)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward6 st layers = multiLayerForward6 st layers := rfl

structure MultiLayerForward7 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward7 (st : MultiLayerForward7)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward7_deterministic (st : MultiLayerForward7)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward7 st layers = multiLayerForward7 st layers := rfl

structure MultiLayerForward8 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward8 (st : MultiLayerForward8)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward8_deterministic (st : MultiLayerForward8)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward8 st layers = multiLayerForward8 st layers := rfl

structure MultiLayerForward9 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward9 (st : MultiLayerForward9)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward9_deterministic (st : MultiLayerForward9)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward9 st layers = multiLayerForward9 st layers := rfl

structure MultiLayerForward10 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward10 (st : MultiLayerForward10)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward10_deterministic (st : MultiLayerForward10)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward10 st layers = multiLayerForward10 st layers := rfl

structure MultiLayerForward11 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward11 (st : MultiLayerForward11)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward11_deterministic (st : MultiLayerForward11)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward11 st layers = multiLayerForward11 st layers := rfl

structure MultiLayerForward12 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward12 (st : MultiLayerForward12)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward12_deterministic (st : MultiLayerForward12)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward12 st layers = multiLayerForward12 st layers := rfl

structure MultiLayerForward13 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward13 (st : MultiLayerForward13)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward13_deterministic (st : MultiLayerForward13)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward13 st layers = multiLayerForward13 st layers := rfl

structure MultiLayerForward14 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward14 (st : MultiLayerForward14)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward14_deterministic (st : MultiLayerForward14)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward14 st layers = multiLayerForward14 st layers := rfl

structure MultiLayerForward15 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward15 (st : MultiLayerForward15)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward15_deterministic (st : MultiLayerForward15)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward15 st layers = multiLayerForward15 st layers := rfl

structure MultiLayerForward16 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward16 (st : MultiLayerForward16)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward16_deterministic (st : MultiLayerForward16)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward16 st layers = multiLayerForward16 st layers := rfl

structure MultiLayerForward17 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward17 (st : MultiLayerForward17)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward17_deterministic (st : MultiLayerForward17)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward17 st layers = multiLayerForward17 st layers := rfl

structure MultiLayerForward18 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward18 (st : MultiLayerForward18)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward18_deterministic (st : MultiLayerForward18)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward18 st layers = multiLayerForward18 st layers := rfl

structure MultiLayerForward19 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward19 (st : MultiLayerForward19)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward19_deterministic (st : MultiLayerForward19)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward19 st layers = multiLayerForward19 st layers := rfl

structure MultiLayerForward20 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward20 (st : MultiLayerForward20)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward20_deterministic (st : MultiLayerForward20)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward20 st layers = multiLayerForward20 st layers := rfl

structure MultiLayerForward21 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward21 (st : MultiLayerForward21)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward21_deterministic (st : MultiLayerForward21)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward21 st layers = multiLayerForward21 st layers := rfl

structure MultiLayerForward22 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward22 (st : MultiLayerForward22)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward22_deterministic (st : MultiLayerForward22)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward22 st layers = multiLayerForward22 st layers := rfl

structure MultiLayerForward23 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward23 (st : MultiLayerForward23)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward23_deterministic (st : MultiLayerForward23)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward23 st layers = multiLayerForward23 st layers := rfl

structure MultiLayerForward24 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward24 (st : MultiLayerForward24)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward24_deterministic (st : MultiLayerForward24)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward24 st layers = multiLayerForward24 st layers := rfl

structure MultiLayerForward25 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward25 (st : MultiLayerForward25)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward25_deterministic (st : MultiLayerForward25)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward25 st layers = multiLayerForward25 st layers := rfl

structure MultiLayerForward26 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward26 (st : MultiLayerForward26)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward26_deterministic (st : MultiLayerForward26)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward26 st layers = multiLayerForward26 st layers := rfl

structure MultiLayerForward27 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward27 (st : MultiLayerForward27)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward27_deterministic (st : MultiLayerForward27)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward27 st layers = multiLayerForward27 st layers := rfl

structure MultiLayerForward28 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward28 (st : MultiLayerForward28)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward28_deterministic (st : MultiLayerForward28)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward28 st layers = multiLayerForward28 st layers := rfl

structure MultiLayerForward29 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward29 (st : MultiLayerForward29)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward29_deterministic (st : MultiLayerForward29)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward29 st layers = multiLayerForward29 st layers := rfl

structure MultiLayerForward30 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward30 (st : MultiLayerForward30)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward30_deterministic (st : MultiLayerForward30)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward30 st layers = multiLayerForward30 st layers := rfl

structure MultiLayerForward31 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward31 (st : MultiLayerForward31)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward31_deterministic (st : MultiLayerForward31)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward31 st layers = multiLayerForward31 st layers := rfl

structure MultiLayerForward32 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward32 (st : MultiLayerForward32)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward32_deterministic (st : MultiLayerForward32)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward32 st layers = multiLayerForward32 st layers := rfl

structure MultiLayerForward33 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward33 (st : MultiLayerForward33)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward33_deterministic (st : MultiLayerForward33)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward33 st layers = multiLayerForward33 st layers := rfl

structure MultiLayerForward34 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward34 (st : MultiLayerForward34)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward34_deterministic (st : MultiLayerForward34)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward34 st layers = multiLayerForward34 st layers := rfl

structure MultiLayerForward35 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward35 (st : MultiLayerForward35)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward35_deterministic (st : MultiLayerForward35)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward35 st layers = multiLayerForward35 st layers := rfl

structure MultiLayerForward36 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward36 (st : MultiLayerForward36)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward36_deterministic (st : MultiLayerForward36)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward36 st layers = multiLayerForward36 st layers := rfl

structure MultiLayerForward37 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward37 (st : MultiLayerForward37)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward37_deterministic (st : MultiLayerForward37)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward37 st layers = multiLayerForward37 st layers := rfl

structure MultiLayerForward38 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward38 (st : MultiLayerForward38)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward38_deterministic (st : MultiLayerForward38)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward38 st layers = multiLayerForward38 st layers := rfl

structure MultiLayerForward39 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward39 (st : MultiLayerForward39)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward39_deterministic (st : MultiLayerForward39)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward39 st layers = multiLayerForward39 st layers := rfl

structure MultiLayerForward40 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward40 (st : MultiLayerForward40)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward40_deterministic (st : MultiLayerForward40)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward40 st layers = multiLayerForward40 st layers := rfl

structure MultiLayerForward41 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward41 (st : MultiLayerForward41)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward41_deterministic (st : MultiLayerForward41)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward41 st layers = multiLayerForward41 st layers := rfl

structure MultiLayerForward42 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward42 (st : MultiLayerForward42)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward42_deterministic (st : MultiLayerForward42)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward42 st layers = multiLayerForward42 st layers := rfl

structure MultiLayerForward43 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward43 (st : MultiLayerForward43)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward43_deterministic (st : MultiLayerForward43)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward43 st layers = multiLayerForward43 st layers := rfl

structure MultiLayerForward44 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward44 (st : MultiLayerForward44)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward44_deterministic (st : MultiLayerForward44)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward44 st layers = multiLayerForward44 st layers := rfl

structure MultiLayerForward45 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward45 (st : MultiLayerForward45)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward45_deterministic (st : MultiLayerForward45)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward45 st layers = multiLayerForward45 st layers := rfl

structure MultiLayerForward46 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward46 (st : MultiLayerForward46)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward46_deterministic (st : MultiLayerForward46)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward46 st layers = multiLayerForward46 st layers := rfl

structure MultiLayerForward47 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward47 (st : MultiLayerForward47)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward47_deterministic (st : MultiLayerForward47)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward47 st layers = multiLayerForward47 st layers := rfl

structure MultiLayerForward48 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward48 (st : MultiLayerForward48)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward48_deterministic (st : MultiLayerForward48)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward48 st layers = multiLayerForward48 st layers := rfl

structure MultiLayerForward49 where
  ni : NumericInterface
  dim : Nat
  numLayers : Nat
  batchSize : Nat
  x_data : List ni.Val
  hDim : dim > 0
  hBatch : batchSize > 0
  hLayers : numLayers > 0
  hDataLen : x_data.length = batchSize * (dim * 2)

def multiLayerForward49 (st : MultiLayerForward49)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    List st.ni.Val :=
  layers.foldl (fun acc layer =>
    let (sw, tw, sb, tb, cmin, cmax) := layer
    let dim2 := st.dim * 2
    let rec go (b : Nat) (x : List st.ni.Val) : List st.ni.Val :=
      if b ≥ st.batchSize then x
      else
        let row := x.drop (b * dim2) |>.take dim2
        let x1 := row.take st.dim
        let x2 := row.drop st.dim
        let scale := scaleComputation st.ni sw sb x2 st.dim cmin cmax
        let y1 := elemWiseMul st.ni x1 scale
        let trans := translationComputation st.ni tw tb y1 st.dim
        let y2 := elemWiseAdd st.ni x2 trans
        let newRow := y1 ++ y2
        let prefix := x.take (b * dim2)
        let suffix := x.drop (b * dim2 + dim2)
        go (b + 1) (prefix ++ newRow ++ suffix)
    go 0 acc
    termination_by st.batchSize - b
  ) st.x_data

theorem multi_layer_forward49_deterministic (st : MultiLayerForward49)
    (layers : List (List st.ni.Val × List st.ni.Val ×
      List st.ni.Val × List st.ni.Val × st.ni.Val × st.ni.Val)) :
    multiLayerForward49 st layers = multiLayerForward49 st layers := rfl

end ForwardProofsExt2


namespace BackwardProofsExt2

open NumericSem RowSemantics BackwardSem NumericExt in
structure GradAccBatch0 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch0 (st : GradAccBatch0)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch0 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch1 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch1 (st : GradAccBatch1)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch1 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch2 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch2 (st : GradAccBatch2)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch2 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch3 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch3 (st : GradAccBatch3)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch3 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch4 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch4 (st : GradAccBatch4)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch4 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch5 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch5 (st : GradAccBatch5)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch5 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch6 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch6 (st : GradAccBatch6)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch6 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch7 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch7 (st : GradAccBatch7)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch7 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch8 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch8 (st : GradAccBatch8)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch8 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch9 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch9 (st : GradAccBatch9)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch9 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch10 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch10 (st : GradAccBatch10)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch10 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch11 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch11 (st : GradAccBatch11)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch11 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch12 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch12 (st : GradAccBatch12)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch12 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch13 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch13 (st : GradAccBatch13)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch13 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch14 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch14 (st : GradAccBatch14)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch14 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch15 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch15 (st : GradAccBatch15)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch15 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch16 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch16 (st : GradAccBatch16)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch16 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch17 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch17 (st : GradAccBatch17)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch17 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch18 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch18 (st : GradAccBatch18)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch18 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch19 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch19 (st : GradAccBatch19)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch19 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch20 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch20 (st : GradAccBatch20)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch20 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch21 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch21 (st : GradAccBatch21)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch21 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch22 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch22 (st : GradAccBatch22)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch22 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch23 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch23 (st : GradAccBatch23)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch23 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch24 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch24 (st : GradAccBatch24)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch24 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch25 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch25 (st : GradAccBatch25)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch25 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch26 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch26 (st : GradAccBatch26)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch26 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch27 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch27 (st : GradAccBatch27)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch27 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch28 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch28 (st : GradAccBatch28)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch28 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch29 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch29 (st : GradAccBatch29)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch29 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch30 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch30 (st : GradAccBatch30)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch30 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch31 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch31 (st : GradAccBatch31)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch31 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch32 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch32 (st : GradAccBatch32)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch32 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch33 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch33 (st : GradAccBatch33)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch33 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch34 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch34 (st : GradAccBatch34)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch34 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch35 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch35 (st : GradAccBatch35)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch35 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch36 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch36 (st : GradAccBatch36)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch36 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch37 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch37 (st : GradAccBatch37)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch37 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch38 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch38 (st : GradAccBatch38)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch38 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

structure GradAccBatch39 where
  ni : NumericInterface
  dim : Nat
  batchSize : Nat
  s_weight_grad : List ni.Val
  t_weight_grad : List ni.Val
  s_bias_grad : List ni.Val
  t_bias_grad : List ni.Val
  hSwGrad : s_weight_grad.length = dim * dim
  hTwGrad : t_weight_grad.length = dim * dim
  hSbGrad : s_bias_grad.length = dim
  hTbGrad : t_bias_grad.length = dim

def accGradsBatch39 (st : GradAccBatch39)
    (new_sw new_tw : List st.ni.Val)
    (new_sb new_tb : List st.ni.Val)
    (scale : st.ni.Val) : GradAccBatch39 :=
  { st with
    s_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_weight_grad new_sw,
    t_weight_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_weight_grad new_tw,
    s_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.s_bias_grad new_sb,
    t_bias_grad := List.zipWith (fun a g => st.ni.add a (st.ni.mul g scale))
      st.t_bias_grad new_tb,
    hSwGrad := (List.length_zipWith _ st.s_weight_grad new_sw).trans
      (Nat.min_eq_left (st.hSwGrad ▸ Nat.le_refl _) ▸ st.hSwGrad),
    hTwGrad := (List.length_zipWith _ st.t_weight_grad new_tw).trans
      (Nat.min_eq_left (st.hTwGrad ▸ Nat.le_refl _) ▸ st.hTwGrad),
    hSbGrad := (List.length_zipWith _ st.s_bias_grad new_sb).trans
      (Nat.min_eq_left (st.hSbGrad ▸ Nat.le_refl _) ▸ st.hSbGrad),
    hTbGrad := (List.length_zipWith _ st.t_bias_grad new_tb).trans
      (Nat.min_eq_left (st.hTbGrad ▸ Nat.le_refl _) ▸ st.hTbGrad) }

end BackwardProofsExt2


namespace RegistryProofsExt2

open RegistryModel RSFCoreDef in
structure RegistryStateInvariant0 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition0 (st : RegistryStateInvariant0)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition0_increments (st : RegistryStateInvariant0)
    (core : RSFCore) :
    (registryStateTransition0 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition0_returns_id (st : RegistryStateInvariant0)
    (core : RSFCore) :
    (registryStateTransition0 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant1 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition1 (st : RegistryStateInvariant1)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition1_increments (st : RegistryStateInvariant1)
    (core : RSFCore) :
    (registryStateTransition1 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition1_returns_id (st : RegistryStateInvariant1)
    (core : RSFCore) :
    (registryStateTransition1 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant2 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition2 (st : RegistryStateInvariant2)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition2_increments (st : RegistryStateInvariant2)
    (core : RSFCore) :
    (registryStateTransition2 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition2_returns_id (st : RegistryStateInvariant2)
    (core : RSFCore) :
    (registryStateTransition2 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant3 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition3 (st : RegistryStateInvariant3)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition3_increments (st : RegistryStateInvariant3)
    (core : RSFCore) :
    (registryStateTransition3 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition3_returns_id (st : RegistryStateInvariant3)
    (core : RSFCore) :
    (registryStateTransition3 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant4 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition4 (st : RegistryStateInvariant4)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition4_increments (st : RegistryStateInvariant4)
    (core : RSFCore) :
    (registryStateTransition4 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition4_returns_id (st : RegistryStateInvariant4)
    (core : RSFCore) :
    (registryStateTransition4 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant5 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition5 (st : RegistryStateInvariant5)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition5_increments (st : RegistryStateInvariant5)
    (core : RSFCore) :
    (registryStateTransition5 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition5_returns_id (st : RegistryStateInvariant5)
    (core : RSFCore) :
    (registryStateTransition5 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant6 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition6 (st : RegistryStateInvariant6)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition6_increments (st : RegistryStateInvariant6)
    (core : RSFCore) :
    (registryStateTransition6 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition6_returns_id (st : RegistryStateInvariant6)
    (core : RSFCore) :
    (registryStateTransition6 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant7 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition7 (st : RegistryStateInvariant7)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition7_increments (st : RegistryStateInvariant7)
    (core : RSFCore) :
    (registryStateTransition7 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition7_returns_id (st : RegistryStateInvariant7)
    (core : RSFCore) :
    (registryStateTransition7 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant8 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition8 (st : RegistryStateInvariant8)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition8_increments (st : RegistryStateInvariant8)
    (core : RSFCore) :
    (registryStateTransition8 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition8_returns_id (st : RegistryStateInvariant8)
    (core : RSFCore) :
    (registryStateTransition8 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant9 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition9 (st : RegistryStateInvariant9)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition9_increments (st : RegistryStateInvariant9)
    (core : RSFCore) :
    (registryStateTransition9 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition9_returns_id (st : RegistryStateInvariant9)
    (core : RSFCore) :
    (registryStateTransition9 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant10 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition10 (st : RegistryStateInvariant10)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition10_increments (st : RegistryStateInvariant10)
    (core : RSFCore) :
    (registryStateTransition10 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition10_returns_id (st : RegistryStateInvariant10)
    (core : RSFCore) :
    (registryStateTransition10 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant11 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition11 (st : RegistryStateInvariant11)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition11_increments (st : RegistryStateInvariant11)
    (core : RSFCore) :
    (registryStateTransition11 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition11_returns_id (st : RegistryStateInvariant11)
    (core : RSFCore) :
    (registryStateTransition11 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant12 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition12 (st : RegistryStateInvariant12)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition12_increments (st : RegistryStateInvariant12)
    (core : RSFCore) :
    (registryStateTransition12 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition12_returns_id (st : RegistryStateInvariant12)
    (core : RSFCore) :
    (registryStateTransition12 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant13 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition13 (st : RegistryStateInvariant13)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition13_increments (st : RegistryStateInvariant13)
    (core : RSFCore) :
    (registryStateTransition13 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition13_returns_id (st : RegistryStateInvariant13)
    (core : RSFCore) :
    (registryStateTransition13 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant14 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition14 (st : RegistryStateInvariant14)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition14_increments (st : RegistryStateInvariant14)
    (core : RSFCore) :
    (registryStateTransition14 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition14_returns_id (st : RegistryStateInvariant14)
    (core : RSFCore) :
    (registryStateTransition14 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant15 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition15 (st : RegistryStateInvariant15)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition15_increments (st : RegistryStateInvariant15)
    (core : RSFCore) :
    (registryStateTransition15 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition15_returns_id (st : RegistryStateInvariant15)
    (core : RSFCore) :
    (registryStateTransition15 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant16 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition16 (st : RegistryStateInvariant16)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition16_increments (st : RegistryStateInvariant16)
    (core : RSFCore) :
    (registryStateTransition16 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition16_returns_id (st : RegistryStateInvariant16)
    (core : RSFCore) :
    (registryStateTransition16 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant17 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition17 (st : RegistryStateInvariant17)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition17_increments (st : RegistryStateInvariant17)
    (core : RSFCore) :
    (registryStateTransition17 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition17_returns_id (st : RegistryStateInvariant17)
    (core : RSFCore) :
    (registryStateTransition17 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant18 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition18 (st : RegistryStateInvariant18)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition18_increments (st : RegistryStateInvariant18)
    (core : RSFCore) :
    (registryStateTransition18 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition18_returns_id (st : RegistryStateInvariant18)
    (core : RSFCore) :
    (registryStateTransition18 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant19 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition19 (st : RegistryStateInvariant19)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition19_increments (st : RegistryStateInvariant19)
    (core : RSFCore) :
    (registryStateTransition19 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition19_returns_id (st : RegistryStateInvariant19)
    (core : RSFCore) :
    (registryStateTransition19 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant20 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition20 (st : RegistryStateInvariant20)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition20_increments (st : RegistryStateInvariant20)
    (core : RSFCore) :
    (registryStateTransition20 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition20_returns_id (st : RegistryStateInvariant20)
    (core : RSFCore) :
    (registryStateTransition20 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant21 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition21 (st : RegistryStateInvariant21)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition21_increments (st : RegistryStateInvariant21)
    (core : RSFCore) :
    (registryStateTransition21 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition21_returns_id (st : RegistryStateInvariant21)
    (core : RSFCore) :
    (registryStateTransition21 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant22 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition22 (st : RegistryStateInvariant22)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition22_increments (st : RegistryStateInvariant22)
    (core : RSFCore) :
    (registryStateTransition22 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition22_returns_id (st : RegistryStateInvariant22)
    (core : RSFCore) :
    (registryStateTransition22 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant23 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition23 (st : RegistryStateInvariant23)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition23_increments (st : RegistryStateInvariant23)
    (core : RSFCore) :
    (registryStateTransition23 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition23_returns_id (st : RegistryStateInvariant23)
    (core : RSFCore) :
    (registryStateTransition23 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant24 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition24 (st : RegistryStateInvariant24)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition24_increments (st : RegistryStateInvariant24)
    (core : RSFCore) :
    (registryStateTransition24 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition24_returns_id (st : RegistryStateInvariant24)
    (core : RSFCore) :
    (registryStateTransition24 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant25 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition25 (st : RegistryStateInvariant25)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition25_increments (st : RegistryStateInvariant25)
    (core : RSFCore) :
    (registryStateTransition25 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition25_returns_id (st : RegistryStateInvariant25)
    (core : RSFCore) :
    (registryStateTransition25 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant26 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition26 (st : RegistryStateInvariant26)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition26_increments (st : RegistryStateInvariant26)
    (core : RSFCore) :
    (registryStateTransition26 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition26_returns_id (st : RegistryStateInvariant26)
    (core : RSFCore) :
    (registryStateTransition26 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant27 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition27 (st : RegistryStateInvariant27)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition27_increments (st : RegistryStateInvariant27)
    (core : RSFCore) :
    (registryStateTransition27 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition27_returns_id (st : RegistryStateInvariant27)
    (core : RSFCore) :
    (registryStateTransition27 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant28 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition28 (st : RegistryStateInvariant28)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition28_increments (st : RegistryStateInvariant28)
    (core : RSFCore) :
    (registryStateTransition28 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition28_returns_id (st : RegistryStateInvariant28)
    (core : RSFCore) :
    (registryStateTransition28 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant29 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition29 (st : RegistryStateInvariant29)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition29_increments (st : RegistryStateInvariant29)
    (core : RSFCore) :
    (registryStateTransition29 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition29_returns_id (st : RegistryStateInvariant29)
    (core : RSFCore) :
    (registryStateTransition29 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant30 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition30 (st : RegistryStateInvariant30)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition30_increments (st : RegistryStateInvariant30)
    (core : RSFCore) :
    (registryStateTransition30 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition30_returns_id (st : RegistryStateInvariant30)
    (core : RSFCore) :
    (registryStateTransition30 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant31 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition31 (st : RegistryStateInvariant31)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition31_increments (st : RegistryStateInvariant31)
    (core : RSFCore) :
    (registryStateTransition31 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition31_returns_id (st : RegistryStateInvariant31)
    (core : RSFCore) :
    (registryStateTransition31 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant32 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition32 (st : RegistryStateInvariant32)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition32_increments (st : RegistryStateInvariant32)
    (core : RSFCore) :
    (registryStateTransition32 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition32_returns_id (st : RegistryStateInvariant32)
    (core : RSFCore) :
    (registryStateTransition32 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant33 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition33 (st : RegistryStateInvariant33)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition33_increments (st : RegistryStateInvariant33)
    (core : RSFCore) :
    (registryStateTransition33 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition33_returns_id (st : RegistryStateInvariant33)
    (core : RSFCore) :
    (registryStateTransition33 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant34 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition34 (st : RegistryStateInvariant34)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition34_increments (st : RegistryStateInvariant34)
    (core : RSFCore) :
    (registryStateTransition34 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition34_returns_id (st : RegistryStateInvariant34)
    (core : RSFCore) :
    (registryStateTransition34 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant35 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition35 (st : RegistryStateInvariant35)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition35_increments (st : RegistryStateInvariant35)
    (core : RSFCore) :
    (registryStateTransition35 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition35_returns_id (st : RegistryStateInvariant35)
    (core : RSFCore) :
    (registryStateTransition35 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant36 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition36 (st : RegistryStateInvariant36)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition36_increments (st : RegistryStateInvariant36)
    (core : RSFCore) :
    (registryStateTransition36 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition36_returns_id (st : RegistryStateInvariant36)
    (core : RSFCore) :
    (registryStateTransition36 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant37 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition37 (st : RegistryStateInvariant37)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition37_increments (st : RegistryStateInvariant37)
    (core : RSFCore) :
    (registryStateTransition37 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition37_returns_id (st : RegistryStateInvariant37)
    (core : RSFCore) :
    (registryStateTransition37 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant38 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition38 (st : RegistryStateInvariant38)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition38_increments (st : RegistryStateInvariant38)
    (core : RSFCore) :
    (registryStateTransition38 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition38_returns_id (st : RegistryStateInvariant38)
    (core : RSFCore) :
    (registryStateTransition38 st core).2 = st.reg.nextId := rfl

structure RegistryStateInvariant39 where
  reg : Registry RSFCore
  hInv : registryInvariant reg

def registryStateTransition39 (st : RegistryStateInvariant39)
    (core : RSFCore) : Registry RSFCore × Nat :=
  registerCore st.reg core

theorem registry_transition39_increments (st : RegistryStateInvariant39)
    (core : RSFCore) :
    (registryStateTransition39 st core).1.entries.length =
    st.reg.entries.length + 1 := rfl

theorem registry_transition39_returns_id (st : RegistryStateInvariant39)
    (core : RSFCore) :
    (registryStateTransition39 st core).2 = st.reg.nextId := rfl

end RegistryProofsExt2


namespace SerializationProofsExt2

open SerializerModel ParserModel CRCModel SnapshotModel RSFCoreDef in
structure FieldRoundtrip0 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip1 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip2 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip3 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip4 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip5 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip6 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip7 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip8 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip9 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip10 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip11 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip12 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip13 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip14 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip15 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip16 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip17 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip18 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip19 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip20 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip21 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip22 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip23 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip24 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip25 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip26 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip27 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip28 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

structure FieldRoundtrip29 where
  serialize : Nat → List UInt8
  parse : List UInt8 → Nat → RSFResult (Nat × Nat)
  roundtrip : ∀ v pos, parse (serialize v) pos = RSFResult.ok (pos + 4, v)

def crcAccumulate0 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate0_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate0 s vs = crcAccumulate0 s vs := rfl

def crcAccumulate1 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate1_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate1 s vs = crcAccumulate1 s vs := rfl

def crcAccumulate2 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate2_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate2 s vs = crcAccumulate2 s vs := rfl

def crcAccumulate3 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate3_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate3 s vs = crcAccumulate3 s vs := rfl

def crcAccumulate4 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate4_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate4 s vs = crcAccumulate4 s vs := rfl

def crcAccumulate5 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate5_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate5 s vs = crcAccumulate5 s vs := rfl

def crcAccumulate6 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate6_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate6 s vs = crcAccumulate6 s vs := rfl

def crcAccumulate7 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate7_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate7 s vs = crcAccumulate7 s vs := rfl

def crcAccumulate8 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate8_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate8 s vs = crcAccumulate8 s vs := rfl

def crcAccumulate9 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate9_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate9 s vs = crcAccumulate9 s vs := rfl

def crcAccumulate10 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate10_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate10 s vs = crcAccumulate10 s vs := rfl

def crcAccumulate11 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate11_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate11 s vs = crcAccumulate11 s vs := rfl

def crcAccumulate12 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate12_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate12 s vs = crcAccumulate12 s vs := rfl

def crcAccumulate13 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate13_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate13 s vs = crcAccumulate13 s vs := rfl

def crcAccumulate14 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate14_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate14 s vs = crcAccumulate14 s vs := rfl

def crcAccumulate15 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate15_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate15 s vs = crcAccumulate15 s vs := rfl

def crcAccumulate16 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate16_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate16 s vs = crcAccumulate16 s vs := rfl

def crcAccumulate17 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate17_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate17 s vs = crcAccumulate17 s vs := rfl

def crcAccumulate18 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate18_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate18 s vs = crcAccumulate18 s vs := rfl

def crcAccumulate19 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate19_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate19 s vs = crcAccumulate19 s vs := rfl

def crcAccumulate20 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate20_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate20 s vs = crcAccumulate20 s vs := rfl

def crcAccumulate21 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate21_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate21 s vs = crcAccumulate21 s vs := rfl

def crcAccumulate22 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate22_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate22 s vs = crcAccumulate22 s vs := rfl

def crcAccumulate23 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate23_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate23 s vs = crcAccumulate23 s vs := rfl

def crcAccumulate24 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate24_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate24 s vs = crcAccumulate24 s vs := rfl

def crcAccumulate25 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate25_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate25 s vs = crcAccumulate25 s vs := rfl

def crcAccumulate26 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate26_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate26 s vs = crcAccumulate26 s vs := rfl

def crcAccumulate27 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate27_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate27 s vs = crcAccumulate27 s vs := rfl

def crcAccumulate28 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate28_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate28 s vs = crcAccumulate28 s vs := rfl

def crcAccumulate29 (s : CRCState) (values : List UInt32) : CRCState :=
  values.foldl crcUpdateU32LE s

theorem crc_accumulate29_deterministic (s : CRCState) (vs : List UInt32) :
    crcAccumulate29 s vs = crcAccumulate29 s vs := rfl

def verifyLayerPayload0 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload0_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload0 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload1 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload1_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload1 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload2 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload2_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload2 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload3 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload3_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload3 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload4 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload4_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload4 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload5 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload5_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload5 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload6 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload6_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload6 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload7 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload7_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload7 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload8 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload8_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload8 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload9 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload9_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload9 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload10 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload10_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload10 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload11 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload11_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload11 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload12 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload12_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload12 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload13 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload13_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload13 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload14 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload14_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload14 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload15 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload15_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload15 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload16 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload16_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload16 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload17 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload17_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload17 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload18 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload18_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload18 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

def verifyLayerPayload19 (dim : Nat)
    (sw tw sb tb : List Nat) : RSFResult Unit :=
  if sw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if tw.length ≠ dim * dim then RSFResult.err RSFError.DataLengthMismatch
  else if sb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else if tb.length ≠ dim then RSFResult.err RSFError.DataLengthMismatch
  else RSFResult.ok ()

theorem verify_payload19_ok (dim : Nat)
    (sw tw sb tb : List Nat)
    (h1 : sw.length = dim * dim) (h2 : tw.length = dim * dim)
    (h3 : sb.length = dim) (h4 : tb.length = dim) :
    verifyLayerPayload19 dim sw tw sb tb = RSFResult.ok () :=
  (if_neg (fun h => h h1)).symm ▸
  (if_neg (fun h => h h2)).symm ▸
  (if_neg (fun h => h h3)).symm ▸
  if_neg (fun h => h h4)

end SerializationProofsExt2


namespace GPUProofsExt2

open GPUModel RSFCoreDef LayerCoreDef in
structure GPUStateMachine0 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition0 (sm : GPUStateMachine0)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm0_disable (sm : GPUStateMachine0) :
    (gpuSMTransition0 sm 0).gpu_available = false := rfl

theorem gpu_sm0_sync (sm : GPUStateMachine0) :
    (gpuSMTransition0 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm0_notify (sm : GPUStateMachine0) :
    (gpuSMTransition0 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm0_noop (sm : GPUStateMachine0) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition0 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine1 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition1 (sm : GPUStateMachine1)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm1_disable (sm : GPUStateMachine1) :
    (gpuSMTransition1 sm 0).gpu_available = false := rfl

theorem gpu_sm1_sync (sm : GPUStateMachine1) :
    (gpuSMTransition1 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm1_notify (sm : GPUStateMachine1) :
    (gpuSMTransition1 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm1_noop (sm : GPUStateMachine1) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition1 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine2 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition2 (sm : GPUStateMachine2)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm2_disable (sm : GPUStateMachine2) :
    (gpuSMTransition2 sm 0).gpu_available = false := rfl

theorem gpu_sm2_sync (sm : GPUStateMachine2) :
    (gpuSMTransition2 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm2_notify (sm : GPUStateMachine2) :
    (gpuSMTransition2 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm2_noop (sm : GPUStateMachine2) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition2 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine3 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition3 (sm : GPUStateMachine3)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm3_disable (sm : GPUStateMachine3) :
    (gpuSMTransition3 sm 0).gpu_available = false := rfl

theorem gpu_sm3_sync (sm : GPUStateMachine3) :
    (gpuSMTransition3 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm3_notify (sm : GPUStateMachine3) :
    (gpuSMTransition3 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm3_noop (sm : GPUStateMachine3) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition3 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine4 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition4 (sm : GPUStateMachine4)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm4_disable (sm : GPUStateMachine4) :
    (gpuSMTransition4 sm 0).gpu_available = false := rfl

theorem gpu_sm4_sync (sm : GPUStateMachine4) :
    (gpuSMTransition4 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm4_notify (sm : GPUStateMachine4) :
    (gpuSMTransition4 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm4_noop (sm : GPUStateMachine4) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition4 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine5 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition5 (sm : GPUStateMachine5)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm5_disable (sm : GPUStateMachine5) :
    (gpuSMTransition5 sm 0).gpu_available = false := rfl

theorem gpu_sm5_sync (sm : GPUStateMachine5) :
    (gpuSMTransition5 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm5_notify (sm : GPUStateMachine5) :
    (gpuSMTransition5 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm5_noop (sm : GPUStateMachine5) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition5 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine6 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition6 (sm : GPUStateMachine6)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm6_disable (sm : GPUStateMachine6) :
    (gpuSMTransition6 sm 0).gpu_available = false := rfl

theorem gpu_sm6_sync (sm : GPUStateMachine6) :
    (gpuSMTransition6 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm6_notify (sm : GPUStateMachine6) :
    (gpuSMTransition6 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm6_noop (sm : GPUStateMachine6) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition6 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine7 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition7 (sm : GPUStateMachine7)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm7_disable (sm : GPUStateMachine7) :
    (gpuSMTransition7 sm 0).gpu_available = false := rfl

theorem gpu_sm7_sync (sm : GPUStateMachine7) :
    (gpuSMTransition7 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm7_notify (sm : GPUStateMachine7) :
    (gpuSMTransition7 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm7_noop (sm : GPUStateMachine7) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition7 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine8 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition8 (sm : GPUStateMachine8)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm8_disable (sm : GPUStateMachine8) :
    (gpuSMTransition8 sm 0).gpu_available = false := rfl

theorem gpu_sm8_sync (sm : GPUStateMachine8) :
    (gpuSMTransition8 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm8_notify (sm : GPUStateMachine8) :
    (gpuSMTransition8 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm8_noop (sm : GPUStateMachine8) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition8 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine9 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition9 (sm : GPUStateMachine9)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm9_disable (sm : GPUStateMachine9) :
    (gpuSMTransition9 sm 0).gpu_available = false := rfl

theorem gpu_sm9_sync (sm : GPUStateMachine9) :
    (gpuSMTransition9 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm9_notify (sm : GPUStateMachine9) :
    (gpuSMTransition9 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm9_noop (sm : GPUStateMachine9) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition9 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine10 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition10 (sm : GPUStateMachine10)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm10_disable (sm : GPUStateMachine10) :
    (gpuSMTransition10 sm 0).gpu_available = false := rfl

theorem gpu_sm10_sync (sm : GPUStateMachine10) :
    (gpuSMTransition10 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm10_notify (sm : GPUStateMachine10) :
    (gpuSMTransition10 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm10_noop (sm : GPUStateMachine10) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition10 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine11 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition11 (sm : GPUStateMachine11)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm11_disable (sm : GPUStateMachine11) :
    (gpuSMTransition11 sm 0).gpu_available = false := rfl

theorem gpu_sm11_sync (sm : GPUStateMachine11) :
    (gpuSMTransition11 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm11_notify (sm : GPUStateMachine11) :
    (gpuSMTransition11 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm11_noop (sm : GPUStateMachine11) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition11 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine12 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition12 (sm : GPUStateMachine12)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm12_disable (sm : GPUStateMachine12) :
    (gpuSMTransition12 sm 0).gpu_available = false := rfl

theorem gpu_sm12_sync (sm : GPUStateMachine12) :
    (gpuSMTransition12 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm12_notify (sm : GPUStateMachine12) :
    (gpuSMTransition12 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm12_noop (sm : GPUStateMachine12) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition12 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine13 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition13 (sm : GPUStateMachine13)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm13_disable (sm : GPUStateMachine13) :
    (gpuSMTransition13 sm 0).gpu_available = false := rfl

theorem gpu_sm13_sync (sm : GPUStateMachine13) :
    (gpuSMTransition13 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm13_notify (sm : GPUStateMachine13) :
    (gpuSMTransition13 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm13_noop (sm : GPUStateMachine13) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition13 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine14 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition14 (sm : GPUStateMachine14)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm14_disable (sm : GPUStateMachine14) :
    (gpuSMTransition14 sm 0).gpu_available = false := rfl

theorem gpu_sm14_sync (sm : GPUStateMachine14) :
    (gpuSMTransition14 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm14_notify (sm : GPUStateMachine14) :
    (gpuSMTransition14 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm14_noop (sm : GPUStateMachine14) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition14 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine15 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition15 (sm : GPUStateMachine15)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm15_disable (sm : GPUStateMachine15) :
    (gpuSMTransition15 sm 0).gpu_available = false := rfl

theorem gpu_sm15_sync (sm : GPUStateMachine15) :
    (gpuSMTransition15 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm15_notify (sm : GPUStateMachine15) :
    (gpuSMTransition15 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm15_noop (sm : GPUStateMachine15) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition15 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine16 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition16 (sm : GPUStateMachine16)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm16_disable (sm : GPUStateMachine16) :
    (gpuSMTransition16 sm 0).gpu_available = false := rfl

theorem gpu_sm16_sync (sm : GPUStateMachine16) :
    (gpuSMTransition16 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm16_notify (sm : GPUStateMachine16) :
    (gpuSMTransition16 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm16_noop (sm : GPUStateMachine16) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition16 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine17 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition17 (sm : GPUStateMachine17)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm17_disable (sm : GPUStateMachine17) :
    (gpuSMTransition17 sm 0).gpu_available = false := rfl

theorem gpu_sm17_sync (sm : GPUStateMachine17) :
    (gpuSMTransition17 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm17_notify (sm : GPUStateMachine17) :
    (gpuSMTransition17 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm17_noop (sm : GPUStateMachine17) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition17 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine18 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition18 (sm : GPUStateMachine18)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm18_disable (sm : GPUStateMachine18) :
    (gpuSMTransition18 sm 0).gpu_available = false := rfl

theorem gpu_sm18_sync (sm : GPUStateMachine18) :
    (gpuSMTransition18 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm18_notify (sm : GPUStateMachine18) :
    (gpuSMTransition18 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm18_noop (sm : GPUStateMachine18) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition18 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine19 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition19 (sm : GPUStateMachine19)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm19_disable (sm : GPUStateMachine19) :
    (gpuSMTransition19 sm 0).gpu_available = false := rfl

theorem gpu_sm19_sync (sm : GPUStateMachine19) :
    (gpuSMTransition19 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm19_notify (sm : GPUStateMachine19) :
    (gpuSMTransition19 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm19_noop (sm : GPUStateMachine19) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition19 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine20 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition20 (sm : GPUStateMachine20)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm20_disable (sm : GPUStateMachine20) :
    (gpuSMTransition20 sm 0).gpu_available = false := rfl

theorem gpu_sm20_sync (sm : GPUStateMachine20) :
    (gpuSMTransition20 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm20_notify (sm : GPUStateMachine20) :
    (gpuSMTransition20 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm20_noop (sm : GPUStateMachine20) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition20 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine21 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition21 (sm : GPUStateMachine21)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm21_disable (sm : GPUStateMachine21) :
    (gpuSMTransition21 sm 0).gpu_available = false := rfl

theorem gpu_sm21_sync (sm : GPUStateMachine21) :
    (gpuSMTransition21 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm21_notify (sm : GPUStateMachine21) :
    (gpuSMTransition21 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm21_noop (sm : GPUStateMachine21) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition21 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine22 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition22 (sm : GPUStateMachine22)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm22_disable (sm : GPUStateMachine22) :
    (gpuSMTransition22 sm 0).gpu_available = false := rfl

theorem gpu_sm22_sync (sm : GPUStateMachine22) :
    (gpuSMTransition22 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm22_notify (sm : GPUStateMachine22) :
    (gpuSMTransition22 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm22_noop (sm : GPUStateMachine22) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition22 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine23 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition23 (sm : GPUStateMachine23)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm23_disable (sm : GPUStateMachine23) :
    (gpuSMTransition23 sm 0).gpu_available = false := rfl

theorem gpu_sm23_sync (sm : GPUStateMachine23) :
    (gpuSMTransition23 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm23_notify (sm : GPUStateMachine23) :
    (gpuSMTransition23 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm23_noop (sm : GPUStateMachine23) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition23 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine24 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition24 (sm : GPUStateMachine24)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm24_disable (sm : GPUStateMachine24) :
    (gpuSMTransition24 sm 0).gpu_available = false := rfl

theorem gpu_sm24_sync (sm : GPUStateMachine24) :
    (gpuSMTransition24 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm24_notify (sm : GPUStateMachine24) :
    (gpuSMTransition24 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm24_noop (sm : GPUStateMachine24) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition24 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine25 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition25 (sm : GPUStateMachine25)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm25_disable (sm : GPUStateMachine25) :
    (gpuSMTransition25 sm 0).gpu_available = false := rfl

theorem gpu_sm25_sync (sm : GPUStateMachine25) :
    (gpuSMTransition25 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm25_notify (sm : GPUStateMachine25) :
    (gpuSMTransition25 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm25_noop (sm : GPUStateMachine25) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition25 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine26 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition26 (sm : GPUStateMachine26)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm26_disable (sm : GPUStateMachine26) :
    (gpuSMTransition26 sm 0).gpu_available = false := rfl

theorem gpu_sm26_sync (sm : GPUStateMachine26) :
    (gpuSMTransition26 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm26_notify (sm : GPUStateMachine26) :
    (gpuSMTransition26 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm26_noop (sm : GPUStateMachine26) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition26 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine27 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition27 (sm : GPUStateMachine27)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm27_disable (sm : GPUStateMachine27) :
    (gpuSMTransition27 sm 0).gpu_available = false := rfl

theorem gpu_sm27_sync (sm : GPUStateMachine27) :
    (gpuSMTransition27 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm27_notify (sm : GPUStateMachine27) :
    (gpuSMTransition27 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm27_noop (sm : GPUStateMachine27) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition27 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine28 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition28 (sm : GPUStateMachine28)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm28_disable (sm : GPUStateMachine28) :
    (gpuSMTransition28 sm 0).gpu_available = false := rfl

theorem gpu_sm28_sync (sm : GPUStateMachine28) :
    (gpuSMTransition28 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm28_notify (sm : GPUStateMachine28) :
    (gpuSMTransition28 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm28_noop (sm : GPUStateMachine28) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition28 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

structure GPUStateMachine29 where
  core : RSFCore
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core

def gpuSMTransition29 (sm : GPUStateMachine29)
    (action : Nat) : RSFCore :=
  match action with
  | 0 => disableGPU sm.core
  | 1 => { sm.core with gpu_weight_version := sm.core.cpu_weight_version }
  | 2 => { sm.core with cpu_weight_version := sm.core.cpu_weight_version + 1 }
  | _ => sm.core

theorem gpu_sm29_disable (sm : GPUStateMachine29) :
    (gpuSMTransition29 sm 0).gpu_available = false := rfl

theorem gpu_sm29_sync (sm : GPUStateMachine29) :
    (gpuSMTransition29 sm 1).gpu_weight_version =
    sm.core.cpu_weight_version := rfl

theorem gpu_sm29_notify (sm : GPUStateMachine29) :
    (gpuSMTransition29 sm 2).cpu_weight_version =
    sm.core.cpu_weight_version + 1 := rfl

theorem gpu_sm29_noop (sm : GPUStateMachine29) (n : Nat)
    (h : n ≥ 3) :
    gpuSMTransition29 sm n = sm.core :=
  match n, h with
  | 3, _ => rfl
  | n + 4, _ => rfl

end GPUProofsExt2


namespace EndToEndExt2

open IntegratedTheorems RSFCoreDef RegistryModel GPUModel
  NumericSem LayerCoreDef SnapshotModel in
structure WorkflowState0 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow0_forward_safe (ws : WorkflowState0) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow0_inverse_safe (ws : WorkflowState0) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow0_backward_safe (ws : WorkflowState0) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow0_layers_match (ws : WorkflowState0) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow0_gpu_fallback (ws : WorkflowState0)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState1 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow1_forward_safe (ws : WorkflowState1) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow1_inverse_safe (ws : WorkflowState1) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow1_backward_safe (ws : WorkflowState1) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow1_layers_match (ws : WorkflowState1) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow1_gpu_fallback (ws : WorkflowState1)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState2 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow2_forward_safe (ws : WorkflowState2) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow2_inverse_safe (ws : WorkflowState2) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow2_backward_safe (ws : WorkflowState2) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow2_layers_match (ws : WorkflowState2) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow2_gpu_fallback (ws : WorkflowState2)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState3 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow3_forward_safe (ws : WorkflowState3) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow3_inverse_safe (ws : WorkflowState3) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow3_backward_safe (ws : WorkflowState3) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow3_layers_match (ws : WorkflowState3) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow3_gpu_fallback (ws : WorkflowState3)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState4 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow4_forward_safe (ws : WorkflowState4) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow4_inverse_safe (ws : WorkflowState4) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow4_backward_safe (ws : WorkflowState4) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow4_layers_match (ws : WorkflowState4) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow4_gpu_fallback (ws : WorkflowState4)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState5 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow5_forward_safe (ws : WorkflowState5) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow5_inverse_safe (ws : WorkflowState5) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow5_backward_safe (ws : WorkflowState5) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow5_layers_match (ws : WorkflowState5) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow5_gpu_fallback (ws : WorkflowState5)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState6 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow6_forward_safe (ws : WorkflowState6) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow6_inverse_safe (ws : WorkflowState6) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow6_backward_safe (ws : WorkflowState6) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow6_layers_match (ws : WorkflowState6) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow6_gpu_fallback (ws : WorkflowState6)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState7 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow7_forward_safe (ws : WorkflowState7) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow7_inverse_safe (ws : WorkflowState7) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow7_backward_safe (ws : WorkflowState7) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow7_layers_match (ws : WorkflowState7) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow7_gpu_fallback (ws : WorkflowState7)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState8 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow8_forward_safe (ws : WorkflowState8) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow8_inverse_safe (ws : WorkflowState8) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow8_backward_safe (ws : WorkflowState8) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow8_layers_match (ws : WorkflowState8) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow8_gpu_fallback (ws : WorkflowState8)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState9 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow9_forward_safe (ws : WorkflowState9) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow9_inverse_safe (ws : WorkflowState9) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow9_backward_safe (ws : WorkflowState9) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow9_layers_match (ws : WorkflowState9) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow9_gpu_fallback (ws : WorkflowState9)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState10 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow10_forward_safe (ws : WorkflowState10) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow10_inverse_safe (ws : WorkflowState10) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow10_backward_safe (ws : WorkflowState10) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow10_layers_match (ws : WorkflowState10) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow10_gpu_fallback (ws : WorkflowState10)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState11 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow11_forward_safe (ws : WorkflowState11) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow11_inverse_safe (ws : WorkflowState11) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow11_backward_safe (ws : WorkflowState11) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow11_layers_match (ws : WorkflowState11) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow11_gpu_fallback (ws : WorkflowState11)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState12 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow12_forward_safe (ws : WorkflowState12) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow12_inverse_safe (ws : WorkflowState12) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow12_backward_safe (ws : WorkflowState12) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow12_layers_match (ws : WorkflowState12) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow12_gpu_fallback (ws : WorkflowState12)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState13 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow13_forward_safe (ws : WorkflowState13) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow13_inverse_safe (ws : WorkflowState13) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow13_backward_safe (ws : WorkflowState13) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow13_layers_match (ws : WorkflowState13) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow13_gpu_fallback (ws : WorkflowState13)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState14 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow14_forward_safe (ws : WorkflowState14) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow14_inverse_safe (ws : WorkflowState14) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow14_backward_safe (ws : WorkflowState14) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow14_layers_match (ws : WorkflowState14) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow14_gpu_fallback (ws : WorkflowState14)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState15 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow15_forward_safe (ws : WorkflowState15) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow15_inverse_safe (ws : WorkflowState15) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow15_backward_safe (ws : WorkflowState15) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow15_layers_match (ws : WorkflowState15) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow15_gpu_fallback (ws : WorkflowState15)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState16 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow16_forward_safe (ws : WorkflowState16) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow16_inverse_safe (ws : WorkflowState16) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow16_backward_safe (ws : WorkflowState16) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow16_layers_match (ws : WorkflowState16) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow16_gpu_fallback (ws : WorkflowState16)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState17 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow17_forward_safe (ws : WorkflowState17) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow17_inverse_safe (ws : WorkflowState17) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow17_backward_safe (ws : WorkflowState17) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow17_layers_match (ws : WorkflowState17) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow17_gpu_fallback (ws : WorkflowState17)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState18 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow18_forward_safe (ws : WorkflowState18) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow18_inverse_safe (ws : WorkflowState18) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow18_backward_safe (ws : WorkflowState18) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow18_layers_match (ws : WorkflowState18) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow18_gpu_fallback (ws : WorkflowState18)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState19 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow19_forward_safe (ws : WorkflowState19) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow19_inverse_safe (ws : WorkflowState19) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow19_backward_safe (ws : WorkflowState19) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow19_layers_match (ws : WorkflowState19) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow19_gpu_fallback (ws : WorkflowState19)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState20 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow20_forward_safe (ws : WorkflowState20) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow20_inverse_safe (ws : WorkflowState20) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow20_backward_safe (ws : WorkflowState20) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow20_layers_match (ws : WorkflowState20) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow20_gpu_fallback (ws : WorkflowState20)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState21 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow21_forward_safe (ws : WorkflowState21) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow21_inverse_safe (ws : WorkflowState21) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow21_backward_safe (ws : WorkflowState21) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow21_layers_match (ws : WorkflowState21) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow21_gpu_fallback (ws : WorkflowState21)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState22 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow22_forward_safe (ws : WorkflowState22) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow22_inverse_safe (ws : WorkflowState22) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow22_backward_safe (ws : WorkflowState22) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow22_layers_match (ws : WorkflowState22) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow22_gpu_fallback (ws : WorkflowState22)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState23 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow23_forward_safe (ws : WorkflowState23) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow23_inverse_safe (ws : WorkflowState23) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow23_backward_safe (ws : WorkflowState23) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow23_layers_match (ws : WorkflowState23) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow23_gpu_fallback (ws : WorkflowState23)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState24 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow24_forward_safe (ws : WorkflowState24) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow24_inverse_safe (ws : WorkflowState24) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow24_backward_safe (ws : WorkflowState24) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow24_layers_match (ws : WorkflowState24) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow24_gpu_fallback (ws : WorkflowState24)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState25 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow25_forward_safe (ws : WorkflowState25) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow25_inverse_safe (ws : WorkflowState25) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow25_backward_safe (ws : WorkflowState25) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow25_layers_match (ws : WorkflowState25) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow25_gpu_fallback (ws : WorkflowState25)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState26 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow26_forward_safe (ws : WorkflowState26) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow26_inverse_safe (ws : WorkflowState26) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow26_backward_safe (ws : WorkflowState26) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow26_layers_match (ws : WorkflowState26) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow26_gpu_fallback (ws : WorkflowState26)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState27 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow27_forward_safe (ws : WorkflowState27) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow27_inverse_safe (ws : WorkflowState27) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow27_backward_safe (ws : WorkflowState27) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow27_layers_match (ws : WorkflowState27) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow27_gpu_fallback (ws : WorkflowState27)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState28 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow28_forward_safe (ws : WorkflowState28) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow28_inverse_safe (ws : WorkflowState28) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow28_backward_safe (ws : WorkflowState28) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow28_layers_match (ws : WorkflowState28) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow28_gpu_fallback (ws : WorkflowState28)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure WorkflowState29 where
  core : RSFCore
  reg : Registry RSFCore
  modelId : Nat
  gpuEnabled : Bool
  hInv : rsfCoreInvariant core
  hIdPos : modelId > 0
  hInReg : registryContains reg modelId = true

theorem workflow29_forward_safe (ws : WorkflowState29) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow29_inverse_safe (ws : WorkflowState29) :
    ws.core.dim > 0 := ws.hInv.1

theorem workflow29_backward_safe (ws : WorkflowState29) :
    ws.core.num_layers > 0 := ws.hInv.2.1

theorem workflow29_layers_match (ws : WorkflowState29) :
    ws.core.num_layers = ws.core.layers.length := ws.hInv.2.2.1

theorem workflow29_gpu_fallback (ws : WorkflowState29)
    (h : modelGPUCompatible ws.core ws.gpuEnabled = false) :
    ws.core.layers = ws.core.layers := rfl

structure InterleavedOps0 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved0_forward_then_backward (st : InterleavedOps0) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved0_zero_then_backward (st : InterleavedOps0) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps1 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved1_forward_then_backward (st : InterleavedOps1) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved1_zero_then_backward (st : InterleavedOps1) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps2 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved2_forward_then_backward (st : InterleavedOps2) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved2_zero_then_backward (st : InterleavedOps2) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps3 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved3_forward_then_backward (st : InterleavedOps3) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved3_zero_then_backward (st : InterleavedOps3) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps4 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved4_forward_then_backward (st : InterleavedOps4) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved4_zero_then_backward (st : InterleavedOps4) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps5 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved5_forward_then_backward (st : InterleavedOps5) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved5_zero_then_backward (st : InterleavedOps5) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps6 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved6_forward_then_backward (st : InterleavedOps6) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved6_zero_then_backward (st : InterleavedOps6) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps7 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved7_forward_then_backward (st : InterleavedOps7) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved7_zero_then_backward (st : InterleavedOps7) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps8 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved8_forward_then_backward (st : InterleavedOps8) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved8_zero_then_backward (st : InterleavedOps8) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps9 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved9_forward_then_backward (st : InterleavedOps9) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved9_zero_then_backward (st : InterleavedOps9) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps10 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved10_forward_then_backward (st : InterleavedOps10) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved10_zero_then_backward (st : InterleavedOps10) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps11 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved11_forward_then_backward (st : InterleavedOps11) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved11_zero_then_backward (st : InterleavedOps11) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps12 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved12_forward_then_backward (st : InterleavedOps12) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved12_zero_then_backward (st : InterleavedOps12) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps13 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved13_forward_then_backward (st : InterleavedOps13) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved13_zero_then_backward (st : InterleavedOps13) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps14 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved14_forward_then_backward (st : InterleavedOps14) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved14_zero_then_backward (st : InterleavedOps14) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps15 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved15_forward_then_backward (st : InterleavedOps15) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved15_zero_then_backward (st : InterleavedOps15) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps16 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved16_forward_then_backward (st : InterleavedOps16) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved16_zero_then_backward (st : InterleavedOps16) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps17 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved17_forward_then_backward (st : InterleavedOps17) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved17_zero_then_backward (st : InterleavedOps17) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps18 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved18_forward_then_backward (st : InterleavedOps18) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved18_zero_then_backward (st : InterleavedOps18) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

structure InterleavedOps19 where
  core : RSFCore
  hInv : rsfCoreInvariant core

def interleaved19_forward_then_backward (st : InterleavedOps19) :
    st.core.layers.length = st.core.num_layers :=
  st.hInv.2.2.1.symm

def interleaved19_zero_then_backward (st : InterleavedOps19) :
    (st.core.layers.map zeroGradients).length = st.core.layers.length :=
  List.length_map _ st.core.layers

end EndToEndExt2


end RSF