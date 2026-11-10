import SteppedFlapjack.CrepToLoopSteps.InlineEntry
import SteppedFlapjack.LoopSteps.Defs
import SteppedFlapjack.LoopLiveSteps.Consumption
import Flapjack.Pancake.CrepToLoop.StateRel
import SteppedFlapjack.CrepToLoopSteps.ConditionPrefix
import SteppedFlapjack.CrepToLoopSteps.WordSimpSequence
import SteppedFlapjack.CrepToLoopSteps.BackendReady

/-! Source-shaped bounds for compiled zero-argument Crep tail calls. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Direct argument expressions compile without auxiliary Loop code. -/
theorem directExpressions_noCode {width : Nat} [NeZero width]
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) :
    ∃ values, compileExpsHOLExact ctxt tmp live args = ([],values,tmp,live) ∧ values.length = args.length := by
  induction args with
  | nil => exact ⟨[],by simp [compileExpsHOLExact],rfl⟩
  | cons e es ih =>
    obtain ⟨value,head⟩ := directExpression_noCode (shape e (by simp)) ctxt tmp live
    obtain ⟨values,tail,len⟩ := ih (fun x hx => shape x (by simp [hx]))
    refine ⟨value :: values,?_,by simp [len]⟩
    simp [compileExpsHOLExact,head,tail]

/-- Direct arguments are assigned to temporaries before a tail call. -/
theorem compile_tailCall_direct {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e) :
    ∃ values, values.length = args.length ∧
      compileHOLExact ctxt live (.call none name args) =
        loopNestedSeqHOL ((genTemps (ctxt.vmax+1) args.length).zipWith HolLoopProg.assign values ++
          [.call none (some (findLabExact ctxt name)) (genTemps (ctxt.vmax+1) args.length) none]) := by
  obtain ⟨values,compiled,len⟩ := directExpressions_noCode args shape ctxt (ctxt.vmax+1) live
  refine ⟨values,len,?_⟩
  simp [compileHOLExact,compiled,len]

/-- Direct arguments are assigned to temporaries before a returning call. -/
theorem compile_returningCall_direct {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e)
    (names returnNames : List Nat) (mapped : names.mapM ctxt.vars.lookup = some returnNames) :
    ∃ values, values.length = args.length ∧
      compileHOLExact ctxt live (.call (some (names,none)) name args) =
        loopNestedSeqHOL ((genTemps (ctxt.vmax+1) args.length).zipWith HolLoopProg.assign values ++
          [.call (some (returnNames,live)) (some (findLabExact ctxt name)) (genTemps (ctxt.vmax+1) args.length)
            (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))]) := by
  obtain ⟨values,compiled,len⟩ := directExpressions_noCode args shape ctxt (ctxt.vmax+1) live
  refine ⟨values,len,?_⟩
  simp [compileHOLExact,compiled,len,mapped]

/-- Generated argument assignments cost at most two visits each, plus the
reached call and its final wrapper. -/
theorem assignmentPrefix_steps {width : Nat} [NeZero width] {F : Type}
    (registers : List Nat) (values : List (HolLoopExp width)) (call : HolLoopProg width)
    (s : LoopSemStateFiniteExact width F) :
    LoopSteps.steps (loopNestedSeqHOL (registers.zipWith HolLoopProg.assign values ++ [call])) s ≤
      2 * (registers.zip values).length + 2 +
        match evaluate (loopNestedSeqHOL (registers.zipWith HolLoopProg.assign values)) s with
        | (none,t) => LoopSteps.steps call t
        | _ => 0 := by
  induction registers generalizing values s with
  | nil =>
    simp only [List.zipWith_nil_left,List.zip_nil_left,List.length_nil,List.nil_append,loopNestedSeqHOL,LoopSteps.steps_seq,evaluate]
    rcases run : evaluate call s with ⟨out,post⟩
    cases out with
    | none =>
      simp only
      have h := LoopSteps.steps_leaf (.skip : HolLoopProg width) post rfl
      omega
    | some r => simp only; omega
  | cons reg rest ih =>
    cases values with
    | nil =>
      simp only [List.zipWith_nil_right,List.zip_nil_right,List.length_nil,List.nil_append,loopNestedSeqHOL,LoopSteps.steps_seq,evaluate]
      rcases run : evaluate call s with ⟨out,post⟩
      cases out with
      | none =>
        simp only
        have h := LoopSteps.steps_leaf (.skip : HolLoopProg width) post rfl
        omega
      | some r => simp only; omega
    | cons exp es =>
      simp only [List.zipWith_cons_cons,List.zip_cons_cons,List.length_cons,List.cons_append,loopNestedSeqHOL,LoopSteps.steps_seq,evaluate_seq]
      have leaf := LoopSteps.steps_leaf (.assign reg exp : HolLoopProg width) s rfl
      rcases run : evaluate (.assign reg exp : HolLoopProg width) s with ⟨out,post⟩
      cases out with
      | none =>
        simp only
        have bound := ih es post
        omega
      | some r => simp only; omega

/-- The direct-argument tail-call wrapper has linear cost in its arity. -/
theorem compile_tailCall_direct_steps {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e)
    (s : LoopSemStateFiniteExact width F) :
    let values := (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).2.1
    let regs := genTemps (ctxt.vmax+1) args.length
      let call : HolLoopProg width := .call none (some (findLabExact ctxt name)) regs none
      LoopSteps.steps (compileHOLExact ctxt live (.call none name args)) s ≤
        2 * args.length + 2 +
          match evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign values)) s with
          | (none,t) => LoopSteps.steps call t
          | _ => 0 := by
  obtain ⟨values,compiled,len⟩ := directExpressions_noCode args shape ctxt (ctxt.vmax+1) live
  have callShape : compileHOLExact ctxt live (.call none name args) =
      loopNestedSeqHOL ((genTemps (ctxt.vmax+1) args.length).zipWith HolLoopProg.assign values ++
        [.call none (some (findLabExact ctxt name)) (genTemps (ctxt.vmax+1) args.length) none]) := by
    simp [compileHOLExact,compiled,len]
  dsimp only
  rw [compiled,callShape]
  have bound := assignmentPrefix_steps (genTemps (ctxt.vmax+1) args.length) values
    (.call none (some (findLabExact ctxt name)) (genTemps (ctxt.vmax+1) args.length) none) s
  simpa [List.length_zip,genTemps,len] using bound

/-- The direct-argument returning-call wrapper has linear cost in its arity. -/
theorem compile_returningCall_direct_steps {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e)
    (names returnNames : List Nat) (mapped : names.mapM ctxt.vars.lookup = some returnNames)
    (s : LoopSemStateFiniteExact width F) :
    let values := (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).2.1
    let regs := genTemps (ctxt.vmax+1) args.length
      let call : HolLoopProg width := .call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
        (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))
      LoopSteps.steps (compileHOLExact ctxt live (.call (some (names,none)) name args)) s ≤
        2 * args.length + 2 +
          match evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign values)) s with
          | (none,t) => LoopSteps.steps call t
          | _ => 0 := by
  obtain ⟨values,compiled,len⟩ := directExpressions_noCode args shape ctxt (ctxt.vmax+1) live
  have callShape : compileHOLExact ctxt live (.call (some (names,none)) name args) =
      loopNestedSeqHOL ((genTemps (ctxt.vmax+1) args.length).zipWith HolLoopProg.assign values ++
        [.call (some (returnNames,live)) (some (findLabExact ctxt name)) (genTemps (ctxt.vmax+1) args.length)
          (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))]) := by
    simp [compileHOLExact,compiled,len,mapped]
  dsimp only
  rw [compiled,callShape]
  have bound := assignmentPrefix_steps (genTemps (ctxt.vmax+1) args.length) values
    (.call (some (returnNames,live)) (some (findLabExact ctxt name)) (genTemps (ctxt.vmax+1) args.length)
      (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) s
  simpa [List.length_zip,genTemps,len] using bound

/-- The exact Crep compiler emits one Loop call, in its nested-sequence
wrapper, for a zero-argument tail call. -/
theorem compile_tailCall_nil {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString) :
    compileHOLExact ctxt live (.call none name [] : CrepProgHOL width) =
      .seq (.call none (some (findLabExact ctxt name)) [] none) .skip := by
  obtain ⟨values,len,compiled⟩ := compile_tailCall_direct (width := width) ctxt live name [] (by simp)
  have empty : values = [] := by simpa using len
  subst values
  simpa [genTemps,loopNestedSeqHOL] using compiled

/-- The compiler code relation determines the actual callee and its argument
registers for every function arity. -/
theorem call_lookup {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (name : MlString) (params : List Nat)
    (body : CrepProgHOL width) (values : List (WordLocW width))
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some (params,body)) (arity : values.length = params.length) :
    findCode (some (findLabExact ctxt name)) values target.code =
      some (sptFromAList ((List.range params.length).zip values),
        ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
          (listToNumSetHOLExact (List.range params.length)) body) := by
  obtain ⟨loc,len,hlab,hlen,hcode⟩ := codeRel.2 name params body found
  subst len
  have label : findLabExact ctxt name = loc := by simp [findLabExact,hlab]
  rw [label]
  simp [findCode,hcode,arity]

/-- The code relation identifies the exact optimized zero-argument callee and
the numeric call target. -/
theorem tailCall_nil_lookup {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (name : MlString) (body : CrepProgHOL width)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some ([],body)) :
    findCode (some (findLabExact ctxt name)) [] target.code =
      some (.ln,ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body) := by
  simpa [sptFromAList,listToNumSetHOLExact] using call_lookup ctxt source target name [] body [] codeRel found rfl

/-- A direct call with evaluated arguments counts the actual compiled callee. -/
theorem call_tail_steps {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (name : MlString) (params args : List Nat)
    (body : CrepProgHOL width) (values : List (WordLocW width))
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some (params,body)) (arity : values.length = params.length)
    (get : getVars args target = some values) (clock : target.clock ≠ 0) :
    LoopSteps.steps (.call none (some (findLabExact ctxt name)) args none) target =
      1 + LoopSteps.steps
        (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
          (listToNumSetHOLExact (List.range params.length)) body)
        {decClock target with locals := sptFromAList ((List.range params.length).zip values)} := by
  exact LoopSteps.steps_call_tail _ _ _ _ _ _ get (call_lookup ctxt source target name params body values codeRel found arity) clock

/-- A successful returning call counts its compiled callee and normal continuation. -/
theorem call_returning_steps {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (source : CrepSemHOLState width F)
    (target cut post : LoopSemStateFiniteExact width F) (name : MlString) (params args names : List Nat)
    (live liveOut : NumSet) (exception : Nat) (handler normal : HolLoopProg width)
    (body : CrepProgHOL width) (values returned : List (WordLocW width))
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some (params,body)) (arity : values.length = params.length)
    (get : getVars args target = some values) (distinct : names.Nodup)
    (cutRun : cutRes live (none,target) = (none,cut))
    (bodyRun : evaluate
      (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
      {cut with locals := sptFromAList ((List.range params.length).zip values)} = (some (.result returned),post))
    (returnedArity : returned.length = names.length) :
    LoopSteps.steps (.call (some (names,live)) (some (findLabExact ctxt name)) args
      (some (exception,handler,normal,liveOut))) target =
      1 + LoopSteps.steps
        (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
          (listToNumSetHOLExact (List.range params.length)) body)
        {cut with locals := sptFromAList ((List.range params.length).zip values)} +
      LoopSteps.steps normal (setVars names returned {post with locals := cut.locals}) := by
  have h := LoopSteps.steps_call_returning (some (findLabExact ctxt name)) args names live
    (some (exception,handler,normal,liveOut)) target cut post values
    (sptFromAList ((List.range params.length).zip values))
    (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
      (listToNumSetHOLExact (List.range params.length)) body) (some (.result returned))
    get (call_lookup ctxt source target name params body values codeRel found arity) distinct cutRun bodyRun
  simpa [returnedArity] using h

/-- A successful compiled zero-argument tail call visits the actual optimized
callee, with at most two extra Loop wrapper nodes. -/
theorem compile_tailCall_nil_steps {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (name : MlString) (body : CrepProgHOL width)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some ([],body)) (clock : target.clock ≠ 0) :
    LoopSteps.steps (compileHOLExact ctxt live (.call none name [])) target ≤
      3 + LoopSteps.steps (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
        {decClock target with locals := .ln} := by
  have bound := compile_tailCall_direct_steps (width := width) ctxt live name [] (by simp) target
  have call := call_tail_steps ctxt source target name [] [] body [] codeRel found rfl (by rfl) clock
  simp only [List.length_nil,List.range_zero,List.zip_nil_left,sptFromAList,listToNumSetHOLExact] at call
  simp only [compileExpsHOLExact,genTemps,List.length_nil,List.range_zero,List.map_nil,List.zipWith_nil_left,loopNestedSeqHOL,evaluate] at bound
  rw [call] at bound
  simp only [decClock] at bound ⊢
  omega

/-- A zero-argument returning call without an exception handler compiles to a
Loop call with the compiler-generated normal and exceptional continuations. -/
theorem compile_returningCall_nil {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (names returnNames : List Nat) (mapped : names.mapM ctxt.vars.lookup = some returnNames) :
    compileHOLExact ctxt live (.call (some (names,none)) name [] : CrepProgHOL width) =
      .seq (.call (some (returnNames,live)) (some (findLabExact ctxt name)) []
        (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) .skip := by
  obtain ⟨values,len,compiled⟩ := compile_returningCall_direct (width := width) ctxt live name [] (by simp) names returnNames mapped
  have empty : values = [] := by simpa using len
  subst values
  simpa [genTemps,loopNestedSeqHOL] using compiled

/-- A successful compiled returning call counts its reached callee and at most
four call and continuation nodes. The code relation selects the actual callee. -/
theorem compile_returningCall_nil_steps {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (source : CrepSemHOLState width F)
    (target cut post : LoopSemStateFiniteExact width F) (name : MlString) (body : CrepProgHOL width)
    (names returnNames : List Nat) (values : List (WordLocW width))
    (mapped : names.mapM ctxt.vars.lookup = some returnNames) (distinct : returnNames.Nodup)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some ([],body))
    (cutRun : cutRes live (none,target) = (none,cut))
    (run : evaluate (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
      {cut with locals := .ln} = (some (.result values),post))
    (arity : values.length = returnNames.length) :
    LoopSteps.steps (compileHOLExact ctxt live (.call (some (names,none)) name [])) target ≤
      4 + LoopSteps.steps (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
        {cut with locals := .ln} := by
  have bound := compile_returningCall_direct_steps (width := width) ctxt live name [] (by simp) names returnNames mapped target
  have call := call_returning_steps ctxt source target cut post name [] [] returnNames live live
    (ctxt.vmax+1) (.raise (ctxt.vmax+1)) .skip body [] values codeRel found rfl (by rfl)
    distinct cutRun (by simpa [sptFromAList,listToNumSetHOLExact] using run) arity
  simp only [List.length_nil,List.range_zero,List.zip_nil_left,sptFromAList,listToNumSetHOLExact] at call
  simp only [compileExpsHOLExact,genTemps,List.length_nil,List.range_zero,List.map_nil,List.zipWith_nil_left,loopNestedSeqHOL,evaluate] at bound
  rw [call] at bound
  have skip := LoopSteps.steps_leaf (.skip : HolLoopProg width) (setVars returnNames values {post with locals := cut.locals}) rfl
  omega

/-- A completed supported callee execution gives a source-visit bound for its
actual optimized Loop tail call, with a constant call-wrapper overhead. -/
theorem compile_tailCall_nil_optimised_bound {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (source : CrepSemHOLState 64 F)
    (target final : LoopSemStateFiniteExact 64 F) (name : MlString) (body : CrepProgHOL 64)
    (result : Option (LoopResultExact 64)) (limit : Nat)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some ([],body)) (clock : target.clock ≠ 0)
    (shape : SteppedFlapjack.LoopToWordSteps.LoopSequenceSource
      (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body))
    (run : evaluate (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
      {decClock target with locals := .ln} = (result,final))
    (complete : SteppedFlapjack.LoopToWordSteps.CompleteLoopResult result)
    (sourceBound : LoopSteps.steps (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
      {decClock target with locals := .ln} ≤ limit) :
    LoopSteps.steps (compileHOLExact ctxt live (.call none name [])) target ≤
      3 + sizeOf (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body) * (2 * limit + 1) := by
  have callBound := compile_tailCall_nil_steps ctxt live source target name body codeRel found clock
  obtain ⟨_,_,optBound⟩ := LoopLiveSteps.optimise_complete_source_steps shape
    {decClock target with locals := .ln} final result run complete
  have scaled := Nat.mul_le_mul_left
    (sizeOf (optimiseHOL (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)))
    (show 2 * LoopSteps.steps (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
      {decClock target with locals := .ln} + 1 ≤ 2 * limit + 1 by omega)
  unfold ocompileHOLExact at callBound ⊢
  omega

/-- A supported completed Crep callee bounds the actual optimized Loop tail
call, after the proved compiler clock extension, by its Crep visits. -/
theorem compile_tailCall_nil_crep_bound {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (callerSource : CrepSemHOLState 64 F)
    (target : LoopSemStateFiniteExact 64 F) (name : MlString)
    (init : CrepProgHOL 64) (initShape : BranchProgram init)
    (condition : CrepExpHOL 64) (conditionShape : BranchCondition condition)
    (body tail : CrepProgHOL 64) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (source post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (codeRel : crepToLoopCodeRelExact ctxt callerSource.code target.code)
    (found : callerSource.code.lookup name = some ([],.seq init (.seq (.while condition body) tail)))
    (clock : target.clock ≠ 0)
    (run : evalCrepSemHOLProgExact source (.seq init (.seq (.while condition body) tail)) = (result,post))
    (complete : CompleteCrepResult result)
    (stateRel : crepToLoopStateRelExact source {decClock target with locals := .ln})
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (calleeCodeRel : crepToLoopCodeRelExact (ctxtFcExact ctxt.target ctxt.funcs [] []) source.code target.code)
    (localsRel : crepToLoopLocalsRelExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln source.locals .ln) :
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    let p := .seq init (.seq (.while condition body) tail)
    let factor := 1 + sizeOf (compileHOLExact c .ln init) +
      (1 + (1 + sizeOf (compileHOLExact c .ln (.while condition body))) *
        (sizeOf (loopNestedSeqHOL (compileExpHOLExact c (c.vmax+1) .ln condition).1) +
          sizeOf (compileHOLExact c .ln body)+3) + sizeOf (compileHOLExact c .ln tail))
    ∃ extra final,
      evaluate (compileHOLExact ctxt live (.call none name [])) {target with clock := target.clock+extra} =
        (resultToLoop result,final) ∧
      crepToLoopStateRelExact post final ∧
      LoopSteps.steps (compileHOLExact ctxt live (.call none name [])) {target with clock := target.clock+extra} ≤
        3 + sizeOf (ocompileHOLExact c .ln p) * (2 * (factor * (CrepSteps.steps p source+1)) + 1) := by
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  let p : CrepProgHOL 64 := .seq init (.seq (.while condition body) tail)
  let entry : LoopSemStateFiniteExact 64 F := {decClock target with locals := .ln}
  obtain ⟨extra,final,loopRun,postRel,_,_,_,_,loopBound⟩ :=
    branchConditionWhileBranch_programBound init initShape condition conditionShape body tail bodyShape tailShape c .ln
      source post result entry run (completeCrep_nonerror complete) stateRel memRel globalsRel calleeCodeRel localsRel
  have shift : ({decClock {target with clock := target.clock+extra} with locals := .ln} : LoopSemStateFiniteExact 64 F) =
      {entry with clock := entry.clock+extra} := by
    simp only [entry,decClock]
    congr 1
    omega
  have extendedRun : evaluate (compileHOLExact c .ln p) {decClock {target with clock := target.clock+extra} with locals := .ln} =
      (resultToLoop result,final) := by rw [shift]; exact loopRun
  have extendedBound : LoopSteps.steps (compileHOLExact c .ln p) {decClock {target with clock := target.clock+extra} with locals := .ln} ≤
      (1 + sizeOf (compileHOLExact c .ln init) +
        (1 + (1 + sizeOf (compileHOLExact c .ln (.while condition body))) *
          (sizeOf (loopNestedSeqHOL (compileExpHOLExact c (c.vmax+1) .ln condition).1) +
            sizeOf (compileHOLExact c .ln body)+3) + sizeOf (compileHOLExact c .ln tail))) * (CrepSteps.steps p source+1) := by
    rw [shift]; exact loopBound
  have codeRel' : crepToLoopCodeRelExact ctxt callerSource.code {target with clock := target.clock+extra}.code := codeRel
  have optimizedRun := (LoopLiveSteps.optimise_complete_source_steps
    (branchConditionWhileBranch_wordSimpShape init initShape condition conditionShape body tail bodyShape tailShape c .ln)
    {decClock {target with clock := target.clock+extra} with locals := .ln} final (resultToLoop result)
    extendedRun (completeCrep_loop complete)).1
  have callLookup := tailCall_nil_lookup ctxt callerSource {target with clock := target.clock+extra} name p codeRel' found
  have compiledRun : evaluate (compileHOLExact ctxt live (.call none name [])) {target with clock := target.clock+extra} =
      (resultToLoop result,final) := by
    rw [compile_tailCall_nil,evaluate_seq]
    have callRun : evaluate (.call none (some (findLabExact ctxt name)) [] none) {target with clock := target.clock+extra} =
        (resultToLoop result,final) := by
      rw [evaluate]
      simp only [show getVars [] {target with clock := target.clock+extra} = some [] from rfl,
        callLookup,Option.isSome_none,Bool.false_eq_true,if_false]
      have nz : target.clock + extra ≠ 0 := by omega
      simp only [nz, dite_false]
      simp only [ocompileHOLExact]
      rw [optimizedRun]
      cases complete <;> rfl
    rw [callRun]
    cases complete <;> rfl
  refine ⟨extra,final,compiledRun,postRel,?_⟩
  exact compile_tailCall_nil_optimised_bound ctxt live callerSource {target with clock := target.clock+extra} final name p
    (resultToLoop result) _ codeRel' found (by simp; omega)
    (branchConditionWhileBranch_wordSimpShape init initShape condition conditionShape body tail bodyShape tailShape c .ln)
    extendedRun (completeCrep_loop complete) extendedBound

/-- A call with evaluated arguments preserves the compiler relations at the
parameterized callee entry. -/
theorem call_entry_relations {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (name : MlString) (params : List Nat) (body : CrepProgHOL width)
    (expressions : List (CrepExpHOL width)) (values : List (HolWordLab width))
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (found : source.code.lookup name = some (params,body))
    (distinct : params.Nodup) (arity : values.length = params.length)
    (evaluated : expressions.map (evalCrepSemHOLExp source) = values.map some) :
    let sourceEntry := decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}
    let regs := List.range params.length
    let targetEntry : LoopSemStateFiniteExact width F := {decClock target with locals := sptFromAList (regs.zip (values.map wlabWlocExact))}
    let calleeCtxt := ctxtFcExact ctxt.target ctxt.funcs params regs
    crepToLoopStateRelExact sourceEntry targetEntry ∧
    crepToLoopMemRelHOLExact sourceEntry.memory targetEntry.memory sourceEntry.memaddrs ∧
    crepToLoopGlobalsRelHOLExact sourceEntry.globals targetEntry.globals ∧
    crepToLoopCodeRelExact calleeCtxt sourceEntry.code targetEntry.code ∧
    crepToLoopLocalsRelExact calleeCtxt (listToNumSetHOLExact regs) sourceEntry.locals targetEntry.locals := by
  obtain ⟨loc,len,hlab,hlen,_⟩ := codeRel.2 name params body found
  subst len
  have preserved := crepToLoopCallPreserveStateCodeLocalsRelExact params (List.range params.length) values source target ctxt live name expressions body loc
    distinct List.nodup_range (by simp) (by simpa using arity) stateRel memRel globalsRel codeRel localsRel found (by simpa using hlab) evaluated
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [decClockCrepSemHOL,decClock] using preserved.1
  · simpa [decClockCrepSemHOL,decClock] using memRel
  · simpa [decClockCrepSemHOL,decClock] using globalsRel
  · simpa [decClockCrepSemHOL,decClock] using preserved.2.1
  · simpa [decClockCrepSemHOL,decClock] using preserved.2.2

/-- The ordinary caller state/code/locals relations derive all callee-entry
relations for an empty-argument call, including the actual compiler context. -/
theorem tailCall_nil_entry_relations {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (name : MlString) (body : CrepProgHOL width)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (found : source.code.lookup name = some ([],body)) :
    let sourceEntry := decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList []}
    let targetEntry : LoopSemStateFiniteExact width F := {decClock target with locals := .ln}
    let calleeCtxt := ctxtFcExact ctxt.target ctxt.funcs [] []
    crepToLoopStateRelExact sourceEntry targetEntry ∧
    crepToLoopMemRelHOLExact sourceEntry.memory targetEntry.memory sourceEntry.memaddrs ∧
    crepToLoopGlobalsRelHOLExact sourceEntry.globals targetEntry.globals ∧
    crepToLoopCodeRelExact calleeCtxt sourceEntry.code targetEntry.code ∧
    crepToLoopLocalsRelExact calleeCtxt .ln sourceEntry.locals targetEntry.locals := by
  simpa [sptFromAList,listToNumSetHOLExact] using
    call_entry_relations ctxt live source target name [] body [] [] stateRel memRel globalsRel codeRel localsRel
      found (by simp) rfl (by rfl)

end SteppedFlapjack.CrepToLoopSteps
