import SteppedFlapjack.PanValueFfiSemantics
/-!
# FFI event-prefix monotonicity

These are the local transition lemmas used by Cake's
`evaluate_io_events_mono`.  The concrete Cake FFI paths append events through
`callFfi`, so their incoming event trace is always a prefix of the outgoing
trace.  User-supplied accelerator handlers are intentionally not included:
they are arbitrary state transformers and need an explicit event-preservation
premise before they can participate in the same theorem.
-/

namespace Flapjack

variable {α σ : Type}

def panValueFfiSharedResultFfi : PanValueFfiSharedResult α σ → FfiState σ
  | .loaded ffi _ => ffi
  | .stored ffi => ffi
  | .final ffi _ => ffi

def panValueFfiExtCallResultFfi : PanValueFfiExtCallResult α σ → FfiState σ
  | .returned _ ffi => ffi
  | .final ffi _ => ffi

theorem panValueFfiSharedLoad_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : PanValueFfiContext α) (ffi : FfiState σ)
    (size : OpSize) (address : α) (result : PanValueFfiSharedResult α σ)
    (hresult : panValueFfiSharedLoad context ffi size address = some result) :
    ffi.ioEvents <+: (panValueFfiSharedResultFfi result).ioEvents := by
  unfold panValueFfiSharedLoad at hresult
  by_cases hdomain :
      context.sharedDomain (panValueFfiSharedAddress context size address) = true
  · simp [hdomain] at hresult
    cases hcall : callFfi ffi (.sharedMem .mappedRead)
        [UInt8.ofNat (panValueFfiWidth size)] (context.wordToBytes address false) with
    | returned nextFfi bytes =>
      rw [hcall] at hresult
      simp only [Option.some.injEq] at hresult
      have hprefix := callFfi_return_ioEvents_prefix ffi (.sharedMem .mappedRead)
        [UInt8.ofNat (panValueFfiWidth size)] (context.wordToBytes address false)
        nextFfi bytes hcall
      cases hresult
      simpa [panValueFfiSharedResultFfi] using hprefix
    | final event =>
      rw [hcall] at hresult
      simp only [Option.some.injEq] at hresult
      cases hresult
      exact ⟨[], by simp [panValueFfiSharedResultFfi]⟩
  · simp [hdomain] at hresult

theorem panValueFfiSharedStore_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : PanValueFfiContext α) (ffi : FfiState σ)
    (size : OpSize) (address value : α)
    (result : PanValueFfiSharedResult α σ)
    (hresult : panValueFfiSharedStore context ffi size address value = some result) :
    ffi.ioEvents <+: (panValueFfiSharedResultFfi result).ioEvents := by
  unfold panValueFfiSharedStore at hresult
  by_cases hdomain :
      context.sharedDomain (panValueFfiSharedAddress context size address) = true
  · simp [hdomain] at hresult
    cases hcall : callFfi ffi (.sharedMem .mappedWrite)
        [UInt8.ofNat (panValueFfiWidth size)] _ with
    | returned nextFfi bytes =>
      rw [hcall] at hresult
      simp only [Option.some.injEq] at hresult
      have hprefix := callFfi_return_ioEvents_prefix ffi (.sharedMem .mappedWrite)
        [UInt8.ofNat (panValueFfiWidth size)] _ nextFfi bytes hcall
      cases hresult
      simpa [panValueFfiSharedResultFfi] using hprefix
    | final event =>
      rw [hcall] at hresult
      simp only [Option.some.injEq] at hresult
      cases hresult
      exact ⟨[], by simp [panValueFfiSharedResultFfi]⟩
  · simp [hdomain] at hresult

theorem panValueFfiExtCall_ioEvents_prefix
    [BEq α] [Add α] [OfNat α 1]
    (access : PanValueMemoryAccess α) (context : PanValueFfiContext α)
    (memory : α → Option (PanValue α)) (bytesInWord : α)
    (ffi : FfiState σ) (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (result : PanValueFfiExtCallResult α σ)
    (hresult : panValueFfiExtCall access context memory bytesInWord ffi function
      configuration configurationLength array arrayLength = some result) :
    ffi.ioEvents <+: (panValueFfiExtCallResultFfi result).ioEvents := by
  simp [panValueFfiExtCall] at hresult
  cases hconfiguration : panValueFfiReadBytes access context memory bytesInWord
      configuration (context.valueToNat configurationLength) with
  | none => rw [hconfiguration] at hresult; simp at hresult
  | some configurationBytes =>
    rw [hconfiguration] at hresult
    cases harray : panValueFfiReadBytes access context memory bytesInWord
        array (context.valueToNat arrayLength) with
    | none => rw [harray] at hresult; simp at hresult
    | some arrayBytes =>
      rw [harray] at hresult
      simp only [Option.bind_some] at hresult
      cases hcall : callFfi ffi (.extCall function) configurationBytes arrayBytes with
      | returned nextFfi bytes =>
        rw [hcall] at hresult
        simp only [Option.some.injEq] at hresult
        have hprefix := callFfi_return_ioEvents_prefix ffi (.extCall function)
          configurationBytes arrayBytes nextFfi bytes hcall
        cases hresult
        simpa [panValueFfiExtCallResultFfi] using hprefix
      | final event =>
        rw [hcall] at hresult
        simp only [Option.some.injEq] at hresult
        cases hresult
        exact ⟨[], by simp [panValueFfiExtCallResultFfi]⟩

theorem evalPanValueFfiProgSteps_shMemLoad_normal_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp α)
    (access : PanValueMemoryAccess α) (contracts : Option PanValueCallContracts)
    (addressWord : α) (addressSteps : Nat)
    (nextLocals nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (haddress : evalPanValueExpCounted structs locals globals memory
      baseAddress topAddress bytesInWord address (memoryAccess := some access) =
      some (.word addressWord, addressSteps))
    (hresult : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.shMemLoad size kind name address) (memoryAccess := some access)
      (contracts := contracts) =
      some (.normal nextLocals nextGlobals nextMemory nextFfi, addressSteps + 1)) :
    ffi.ioEvents <+: nextFfi.ioEvents := by
  simp [evalPanValueFfiProgSteps, panValueShMemLoadSteps, haddress] at hresult
  by_cases hvalid :
      panValueSharedLoadValid structs locals globals kind name (.word 0) = true
  · simp [hvalid] at hresult
    cases hload : panValueFfiSharedLoad context ffi size addressWord with
    | none => simp [hload] at hresult
    | some result =>
      cases result with
      | loaded loadedFfi value =>
        rw [hload] at hresult
        cases kind <;> simp at hresult
        all_goals
          rcases hresult with ⟨_, ⟨_, ⟨_, hffi⟩⟩⟩
          rw [← hffi]
          exact panValueFfiSharedLoad_ioEvents_prefix context ffi size addressWord
            (.loaded loadedFfi value) hload
      | stored storedFfi => simp [hload] at hresult
      | final finalFfi event => simp [hload] at hresult
  · simp [hvalid] at hresult

theorem evalPanValueFfiProgSteps_shMemLoad_finalFfi_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp α)
    (access : PanValueMemoryAccess α) (contracts : Option PanValueCallContracts)
    (addressWord : α) (addressSteps : Nat)
    (nextFfi : FfiState σ) (event : FfiFinalEvent)
    (haddress : evalPanValueExpCounted structs locals globals memory
      baseAddress topAddress bytesInWord address (memoryAccess := some access) =
      some (.word addressWord, addressSteps))
    (hresult : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.shMemLoad size kind name address) (memoryAccess := some access)
      (contracts := contracts) =
      some (.finalFfi (fun _ => none) globals memory nextFfi event,
        addressSteps + 1)) :
    ffi.ioEvents <+: nextFfi.ioEvents := by
  simp [evalPanValueFfiProgSteps, panValueShMemLoadSteps, haddress] at hresult
  by_cases hvalid :
      panValueSharedLoadValid structs locals globals kind name (.word 0) = true
  · simp [hvalid] at hresult
    cases hload : panValueFfiSharedLoad context ffi size addressWord with
    | none => simp [hload] at hresult
    | some loadResult =>
      cases loadResult with
      | loaded loadedFfi value => cases kind <;> simp [hload] at hresult
      | stored storedFfi => simp [hload] at hresult
      | final finalFfi finalEvent =>
        have hprefix := panValueFfiSharedLoad_ioEvents_prefix context ffi size addressWord
          (.final finalFfi finalEvent) hload
        rw [hload] at hresult
        simp at hresult
        rcases hresult with ⟨hffi, hevent⟩
        cases hffi
        cases hevent
        simpa [panValueFfiSharedResultFfi] using hprefix
  · simp [hvalid] at hresult

theorem evalPanValueFfiProgSteps_shMemStore_normal_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (size : OpSize) (address value : Exp α)
    (access : PanValueMemoryAccess α) (contracts : Option PanValueCallContracts)
    (addressWord valueWord : α) (addressSteps valueSteps : Nat)
    (nextLocals nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (haddress : evalPanValueExpCounted structs locals globals memory
      baseAddress topAddress bytesInWord address (memoryAccess := some access) =
      some (.word addressWord, addressSteps))
    (hvalue : evalPanValueExpCounted structs locals globals memory
      baseAddress topAddress bytesInWord value (memoryAccess := some access) =
      some (.word valueWord, valueSteps))
    (hresult : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.shMemStore size address value) (memoryAccess := some access)
      (contracts := contracts) =
      some (.normal nextLocals nextGlobals nextMemory nextFfi,
        addressSteps + valueSteps + 1)) :
    ffi.ioEvents <+: nextFfi.ioEvents := by
  simp [evalPanValueFfiProgSteps, panValueShMemStoreSteps, haddress, hvalue] at hresult
  cases hstore : panValueFfiSharedStore context ffi size addressWord valueWord with
  | none => simp [hstore] at hresult
  | some result =>
    cases result with
    | loaded loadedFfi loadedValue => simp [hstore] at hresult
    | stored storedFfi =>
      rw [hstore] at hresult
      simp at hresult
      rcases hresult with ⟨_, ⟨_, ⟨_, hffi⟩⟩⟩
      rw [← hffi]
      exact panValueFfiSharedStore_ioEvents_prefix context ffi size addressWord valueWord
        (.stored storedFfi) hstore
    | final finalFfi event => simp [hstore] at hresult

theorem evalPanValueFfiProgSteps_shMemStore_finalFfi_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (size : OpSize) (address value : Exp α)
    (access : PanValueMemoryAccess α) (contracts : Option PanValueCallContracts)
    (addressWord valueWord : α) (addressSteps valueSteps : Nat)
    (nextFfi : FfiState σ) (event : FfiFinalEvent)
    (haddress : evalPanValueExpCounted structs locals globals memory
      baseAddress topAddress bytesInWord address (memoryAccess := some access) =
      some (.word addressWord, addressSteps))
    (hvalue : evalPanValueExpCounted structs locals globals memory
      baseAddress topAddress bytesInWord value (memoryAccess := some access) =
      some (.word valueWord, valueSteps))
    (hresult : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.shMemStore size address value) (memoryAccess := some access)
      (contracts := contracts) =
      some (.finalFfi locals globals memory nextFfi event,
        addressSteps + valueSteps + 1)) :
    ffi.ioEvents <+: nextFfi.ioEvents := by
  simp [evalPanValueFfiProgSteps, panValueShMemStoreSteps, haddress, hvalue] at hresult
  cases hstore : panValueFfiSharedStore context ffi size addressWord valueWord with
  | none => simp [hstore] at hresult
  | some storeResult =>
    cases storeResult with
    | loaded loadedFfi loadedValue => simp [hstore] at hresult
    | stored storedFfi => simp [hstore] at hresult
    | final finalFfi finalEvent =>
      have hprefix := panValueFfiSharedStore_ioEvents_prefix context ffi size
        addressWord valueWord (.final finalFfi finalEvent) hstore
      rw [hstore] at hresult
      simp at hresult
      rcases hresult with ⟨hffi, hevent⟩
      cases hffi
      cases hevent
      simpa [panValueFfiSharedResultFfi] using hprefix

end Flapjack
