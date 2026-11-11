import SteppedFlapjack.Concrete.Fragment
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang

def WordLocals (locals : VarName → Option (PanValue (RiscV.Word 64))) : Prop :=
  ∀ name value, locals name = some value → ∃ word, value = .word word

theorem wordLocals_empty : WordLocals (fun _ => none) := by
  intro name value found
  simp at found

theorem wordLocals_update {locals : VarName → Option (PanValue (RiscV.Word 64))}
    (words : WordLocals locals) (name : VarName) (word : BitVec 64) :
    WordLocals (updatePanValueMap locals name (.word word)) := by
  intro key value found
  by_cases same : key = name
  · subst key
    simp [updatePanValueMap] at found
    exact ⟨word,found.symm⟩
  · apply words key value
    simpa [updatePanValueMap,same] using found

/-- Binding word arguments gives a callee environment containing only words. -/
theorem wordLocals_bind (parameters : List VarName) (values : List (PanValue (RiscV.Word 64)))
    (locals : VarName → Option (PanValue (RiscV.Word 64)))
    (words : ∀ value ∈ values, ∃ word, value = .word word)
    (bind : bindPanValueParameters parameters values = some locals) : WordLocals locals := by
  have fold : ∀ (ps : List VarName) (vs : List (PanValue (RiscV.Word 64)))
      (acc : VarName → Option (PanValue (RiscV.Word 64))),
      WordLocals acc → (∀ v ∈ vs, ∃ word, v = .word word) →
      WordLocals ((ps.zip vs).foldl (fun acc (name,value) => updatePanValueMap acc name value) acc) := by
    intro ps
    induction ps with
    | nil => intro vs acc ha hv; simpa using ha
    | cons p ps ih =>
      intro vs acc ha hv
      cases vs with
      | nil => simpa using ha
      | cons v vs =>
        obtain ⟨word,rfl⟩ := hv v (by simp)
        simp only [List.zip_cons_cons,List.foldl_cons]
        apply ih vs (updatePanValueMap acc p (.word word)) (wordLocals_update ha p word)
        intro v member
        exact hv v (by simp [member])
  unfold bindPanValueParameters at bind
  split at bind
  · simp at bind
  · simp only [Option.some.injEq] at bind
    subst locals
    exact fold parameters values _ wordLocals_empty words

theorem wordLocals_restore {current original : VarName → Option (PanValue (RiscV.Word 64))}
    (currentWords : WordLocals current) (originalWords : WordLocals original) (name : VarName) :
    WordLocals (restorePanValueLocal current name (original name)) := by
  intro key value found
  by_cases same : key = name
  · subst key
    apply originalWords name value
    simpa [restorePanValueLocal] using found
  · apply currentWords key value
    simpa [restorePanValueLocal,same] using found

theorem scalar_eval_word {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (words : WordLocals production.locals) (value : PanValue (RiscV.Word 64))
    (evaluated : evalPanSemStateExp production expression = some value) : ∃ word, value = .word word := by
  rw [evalPanSemStateExp_64_eq_previous] at evaluated
  induction scalar generalizing value with
  | const n => simp [evalPanValueExp] at evaluated; subst value; exact ⟨n,rfl⟩
  | «local» name member =>
    simp only [evalPanValueExp] at evaluated
    exact words name value evaluated
  | @op operator a b ha hb iha ihb =>
    simp only [evalPanValueExp] at evaluated
    cases argsRun : evalPanValueExp.evalPanValueExps production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord [a,b]
        (some (panSemBitVec64MemoryAccess production)) with
    | none => simp [argsRun] at evaluated
    | some values =>
      cases projected : values.mapM panValueWordProjection with
      | none => simp [argsRun,projected] at evaluated
      | some nums =>
        cases opRun : (panSemBitVec64MemoryAccess production).wordOp operator nums with
        | none => simp [argsRun,projected,opRun] at evaluated
        | some w =>
          simp [argsRun,projected,opRun] at evaluated
          subst value
          exact ⟨w,rfl⟩
  | @cmp operator a b ha hb iha ihb =>
    simp only [evalPanValueExp] at evaluated
    cases leftRun : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord a
        (some (panSemBitVec64MemoryAccess production)) with
    | none => simp [leftRun] at evaluated
    | some left =>
      cases rightRun : evalPanValueExp production.structs production.locals production.globals production.memory
          production.baseAddress production.topAddress panSemBitVec64BytesInWord b
          (some (panSemBitVec64MemoryAccess production)) with
      | none => simp [leftRun,rightRun] at evaluated
      | some right =>
        obtain ⟨leftWord,rfl⟩ := iha left leftRun
        obtain ⟨rightWord,rfl⟩ := ihb right rightRun
        simp [leftRun,rightRun] at evaluated
        subst value
        exact ⟨_,rfl⟩
  | @shift operator a b ha hb iha ihb =>
    simp only [evalPanValueExp] at evaluated
    cases leftRun : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord a
        (some (panSemBitVec64MemoryAccess production)) with
    | none => simp [leftRun] at evaluated
    | some left =>
      cases rightRun : evalPanValueExp production.structs production.locals production.globals production.memory
          production.baseAddress production.topAddress panSemBitVec64BytesInWord b
          (some (panSemBitVec64MemoryAccess production)) with
      | none => simp [leftRun,rightRun] at evaluated
      | some right =>
        obtain ⟨leftWord,rfl⟩ := iha left leftRun
        obtain ⟨rightWord,rfl⟩ := ihb right rightRun
        cases shiftRun : (panSemBitVec64MemoryAccess production).shift operator leftWord rightWord with
        | none => simp [leftRun,rightRun,shiftRun] at evaluated
        | some word =>
          simp [leftRun,rightRun,shiftRun] at evaluated
          subst value
          exact ⟨word,rfl⟩
end SteppedFlapjack.Concrete
