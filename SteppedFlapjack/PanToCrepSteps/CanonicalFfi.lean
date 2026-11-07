import Flapjack.FfiBridge

/-! Construct an executable FFI state corresponding to an arbitrary HOL state. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Basis.Pure.MlString

/-- Interpret an executable FFI name in the HOL carrier. -/
def sourceHolFfiName : FfiName → HolFfiName
  | .extCall name => .extCall (ofString name)
  | .sharedMem .mappedRead => .sharedMem .mappedRead
  | .sharedMem .mappedWrite => .sharedMem .mappedWrite

/-- Interpret a HOL FFI name in the executable carrier. -/
def sourceFfiName : HolFfiName → FfiName
  | .extCall name => .extCall (toStringOfBytes name)
  | .sharedMem .mappedRead => .sharedMem .mappedRead
  | .sharedMem .mappedWrite => .sharedMem .mappedWrite

/-- Every exact FFI name is represented by its decoded executable name. -/
theorem sourceFfiName_rel (name : HolFfiName) : FfiNameRel (sourceFfiName name) name := by
  cases name with
  | extCall name => simp [sourceFfiName,FfiNameRel,ofString_toStringOfBytes]
  | sharedMem op => cases op <;> simp [sourceFfiName,FfiNameRel,ShmemOpRel]

/-- A related name is uniquely determined on the HOL side. -/
theorem sourceHolFfiName_of_rel (name : FfiName) (holName : HolFfiName)
    (rel : FfiNameRel name holName) : sourceHolFfiName name = holName := by
  cases name <;> cases holName <;> simp_all [FfiNameRel,sourceHolFfiName,ShmemOpRel]
  all_goals rename_i op hop; cases op <;> cases hop <;> simp_all

/-- Decoding HOL bytes preserves their numeric values. -/
theorem sourceBitsToByte_toNat (byte : BitVec 8) : (bitsToByte byte).toNat = byte.toNat := by
  simp [bitsToByte]

/-- Decoding a HOL byte list gives a related executable list. -/
theorem sourceBits_bytesRel (bytes : List (BitVec 8)) : BytesRel (bytes.map bitsToByte) bytes := by
  simp [BytesRel,List.map_map,sourceBitsToByte_toNat]

/-- Related byte lists are exactly the byte encoding of their executable values. -/
theorem sourceBytesRel_eq (bytes : List UInt8) (holBytes : List (BitVec 8))
    (rel : BytesRel bytes holBytes) : holBytes = bytes.map byteToBits := by
  induction bytes generalizing holBytes with
  | nil => cases holBytes <;> simp_all [BytesRel]
  | cons byte bytes ih =>
    cases holBytes with
    | nil => simp [BytesRel] at rel
    | cons h hs =>
      simp only [BytesRel,List.map_cons,List.cons.injEq] at rel
      have head : h = byteToBits byte := BitVec.eq_of_toNat_eq (by simpa [byteToBits_toNat] using rel.1)
      have tail : hs = bytes.map byteToBits := ih hs rel.2
      simp [head,tail]

/-- Decode one exact I/O event. -/
def sourceFfiEvent (event : HolIoEvent) : FfiEvent :=
  { name := sourceFfiName event.name
    configuration := event.configuration.map bitsToByte
    bytes := event.bytes.map (fun pair => (bitsToByte pair.1,bitsToByte pair.2)) }

/-- The decoded event is related to the original HOL event. -/
theorem sourceFfiEvent_rel (event : HolIoEvent) : FfiEventRel (sourceFfiEvent event) event := by
  refine ⟨sourceFfiName_rel _,sourceBits_bytesRel _,?_⟩
  simp [BytesPairRel,sourceFfiEvent,List.map_map,sourceBitsToByte_toNat]

/-- An executable oracle can forward every request to the HOL oracle. -/
def sourceFfiOracle {σ : Type} (oracle : HolOracle σ) : FfiOracle σ :=
  fun name state config bytes =>
    match oracle (sourceHolFfiName name) state (config.map byteToBits) (bytes.map byteToBits) with
    | .ret state' bytes' => .returned state' (bytes'.map bitsToByte)
    | .final .failed => .final .failed
    | .final .diverged => .final .diverged

/-- The forwarding oracle satisfies the full persistent oracle relation. -/
theorem sourceFfiOracle_rel {σ : Type} (oracle : HolOracle σ) : OracleRel (sourceFfiOracle oracle) oracle := by
  intro name holName nameRel state config holConfig bytes holBytes configRel bytesRel
  rw [sourceBytesRel_eq config holConfig configRel,sourceBytesRel_eq bytes holBytes bytesRel]
  have hname := sourceHolFfiName_of_rel name holName nameRel
  unfold sourceFfiOracle
  rw [hname]
  cases h : oracle holName state (config.map byteToBits) (bytes.map byteToBits) with
  | ret state' bytes' => simp [OracleResultRel,sourceBits_bytesRel]
  | final outcome => cases outcome <;> simp [OracleResultRel,OutcomeRel]

/-- Construct a matching executable FFI state from any exact HOL FFI state. -/
def sourceFfiState {σ : Type} (state : HolFfiState σ) : FfiState σ :=
  { oracle := sourceFfiOracle state.oracle
    state := state.ffiState
    ioEvents := state.ioEvents.map sourceFfiEvent }

/-- The construction discharges the complete FFI state relation. -/
theorem sourceFfiState_rel {σ : Type} (state : HolFfiState σ) : FfiStateRel (sourceFfiState state) state := by
  refine ⟨rfl,?_,sourceFfiOracle_rel state.oracle⟩
  change FfiEventListRel (state.ioEvents.map sourceFfiEvent) state.ioEvents
  have events : ∀ es, FfiEventListRel (es.map sourceFfiEvent) es := by
    intro es
    induction es with
    | nil => trivial
    | cons event rest ih => exact ⟨sourceFfiEvent_rel event,ih⟩
  exact events state.ioEvents

end SteppedFlapjack.PanToCrepSteps
