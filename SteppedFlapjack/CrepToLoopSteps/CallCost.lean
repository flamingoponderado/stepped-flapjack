import SteppedFlapjack.CrepSteps.CallClock
import SteppedFlapjack.CrepToLoopSteps.ScalarPrefixOutput
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack SteppedFlapjack.LoopToWordSteps SteppedFlapjack.CrepSteps
variable {width : Nat} [NeZero width]

/-- Concrete scalar-prefix cost, computed in a fixed reference context. -/
def callExpressionCost (c : CrepToLoopContextExact) (e : CrepExpHOL width) : Nat :=
  LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact c (c.vmax+1) .ln e).1)
/-- Concrete call-argument prefix cost in the reference context. -/
def callArgumentsCost (c : CrepToLoopContextExact) (es : List (CrepExpHOL width)) : Nat :=
  LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpsHOLExact c (c.vmax+1) .ln es).1)
/-- A structural upper bound for compiling a call-aware Crep function. -/
def callSyntaxCost (c : CrepToLoopContextExact) : CrepProgHOL width → Nat
  | .return es => callArgumentsCost c es + 2*es.length+2
  | .assign _ e => callExpressionCost c e + 2
  | .store a b => callExpressionCost c a + callExpressionCost c b + 3
  | .dec _ e p => callExpressionCost c e + callSyntaxCost c p + 3
  | .seq a b => 1 + callSyntaxCost c a + callSyntaxCost c b
  | .ite e a b => callExpressionCost c e + callSyntaxCost c a + callSyntaxCost c b + 5
  | .while e p => callExpressionCost c e + callSyntaxCost c p + 8
  | .call _ _ es => callArgumentsCost c es + 2*es.length+2
  | _ => 1

private theorem nested_add (a b : List (HolLoopProg width)) :
 loopVisitWeight (loopNestedSeqHOL (a++b)) + 1 = loopVisitWeight (loopNestedSeqHOL a) + loopVisitWeight (loopNestedSeqHOL b) := by
 induction a with
 | nil => simp [loopNestedSeqHOL,loopVisitWeight, Nat.add_comm]
 | cons a as ih => simp only [List.cons_append,loopNestedSeqHOL,loopVisitWeight]; omega

private theorem exprWeight {e : CrepExpHOL width} (shape : CompiledScalar e)
 (c d : CrepToLoopContextExact) (t : Nat) (live : NumSet) :
 loopVisitWeight (loopNestedSeqHOL (compileExpHOLExact c t live e).1) = callExpressionCost d e := by
 obtain ⟨code,value,next,outLive,h,hpref⟩ := compiledScalar_prefix shape c t live
 have branch := nestedSeq_branched code hpref.1
 have hcost := scalarExpressionWeight shape c d t (d.vmax+1) live .ln
 simp only [callExpressionCost, h, ← branched_visitWeight branch] at hcost ⊢
 exact hcost

private theorem argsWeight (es : List (CrepExpHOL width)) (shape : ∀ e ∈ es, CompiledScalar e)
 (c d : CrepToLoopContextExact) (t : Nat) (live : NumSet) :
 loopVisitWeight (loopNestedSeqHOL (compileExpsHOLExact c t live es).1) = callArgumentsCost d es := by
 obtain ⟨code,values,next,outLive,h,len,hpref⟩ := compiledScalars_prefix es shape c t live
 have branch := nestedSeq_branched code hpref.1
 have hcost := scalarArgumentWeight es shape c d t (d.vmax+1) live .ln
 simp only [callArgumentsCost, h, ← branched_visitWeight branch] at hcost ⊢
 exact hcost

private theorem scalarCost {p : CrepProgHOL width} (shape : ScalarProgram p) (ref : CrepToLoopContextExact) :
 ∀ c live, loopVisitWeight (compileHOLExact c live p) ≤ callSyntaxCost ref p := by
 induction shape with
 | skip | tick | «break» _ | «continue» _ => intro c live; simp [compileHOLExact,loopVisitWeight,callSyntaxCost]
 | @ret e he =>
   intro c live
   have ew := argsWeight [e] (by simp [he]) c ref (c.vmax+1) live
   rcases compiled : compileExpsHOLExact c (c.vmax+1) live [e] with ⟨code,values,tmp,outLive⟩
   simp only [compiled] at ew
   have len : values.length = 1 := by
     obtain ⟨cc,vv,nn,ll,hh,hlen,_⟩ := compiledScalars_prefix [e] (by simp [he]) c (c.vmax+1) live
     rw [compiled] at hh
     cases hh
     simpa using hlen
   cases values with
   | nil => simp at len
   | cons value rest =>
     have : rest = [] := by simpa using len
     subst rest
     have n := nested_add code [.assign tmp value,.return [tmp]]
     simp only [loopNestedSeqHOL,loopVisitWeight] at n
     simp only [compileHOLExact,compiled,callSyntaxCost,genTemps,List.length_cons,List.length_nil,
       List.range_succ,List.range_zero]
     simp only [List.nil_append,List.map_cons,List.map_nil,Nat.add_zero,List.zipWith_cons_cons,List.zipWith_nil_left,List.append_assoc,List.cons_append,List.nil_append]
     omega
 | @assign name e he =>
   intro c live
   have ew := exprWeight he c ref (c.vmax+1) live
   rcases compiled : compileExpHOLExact c (c.vmax+1) live e with ⟨code,value,tmp,outLive⟩
   simp only [compiled] at ew
   cases lookup : c.vars.lookup name with
   | none => simp [compileHOLExact,lookup,loopVisitWeight,callSyntaxCost]
   | some reg =>
     have n := nested_add code [.assign reg value]
     simp only [loopNestedSeqHOL,loopVisitWeight] at n
     simp only [compileHOLExact,lookup,compiled,callSyntaxCost]
     omega
 | @store a b ha hb =>
   intro c live
   have ea := exprWeight ha c ref (c.vmax+1) live
   have eb := exprWeight hb c ref (compileExpHOLExact c (c.vmax+1) live a).2.2.1 (compileExpHOLExact c (c.vmax+1) live a).2.2.2
   rcases ca : compileExpHOLExact c (c.vmax+1) live a with ⟨ac,av,atmp,alive⟩
   simp only [ca] at ea eb
   rcases cb : compileExpHOLExact c atmp alive b with ⟨bc,bv,btmp,blive⟩
   simp only [cb] at eb
   have n1 := nested_add ac bc
   have n2 := nested_add (ac ++ bc) [.assign btmp bv,.store av btmp]
   simp only [loopNestedSeqHOL,loopVisitWeight] at n2
   simp only [compileHOLExact,ca,cb,callSyntaxCost]
   omega
 | @dec name e p he hp ih =>
   intro c live
   have ew := exprWeight he c ref (c.vmax+1) live
   have b := ih {c with vars := c.vars.updateEq (name,(compileExpHOLExact c (c.vmax+1) live e).2.2.1), vmax := (compileExpHOLExact c (c.vmax+1) live e).2.2.1} (sptInsert (compileExpHOLExact c (c.vmax+1) live e).2.2.1 () live)
   rcases compiled : compileExpHOLExact c (c.vmax+1) live e with ⟨code,value,tmp,outlive⟩
   simp only [compiled] at ew b
   simp only [compileHOLExact,compiled,loopVisitWeight,callSyntaxCost]
   rw [ew]
   omega
 | @seq a b ha hb ia ib =>
   intro c live
   simp only [compileHOLExact,loopVisitWeight,callSyntaxCost]
   have x := ia c live
   have y := ib c live
   omega
 | @ite e a b he ha hb ia ib =>
   intro c live
   have ew := exprWeight he c ref (c.vmax+1) live
   have x := ia c live
   have y := ib c live
   have n := nested_add (compileExpHOLExact c (c.vmax+1) live e).1
     [.assign (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (compileExpHOLExact c (c.vmax+1) live e).2.1,
      .ite .notEqual (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (.imm (0 : BitVec width))
       (compileHOLExact c live a) (compileHOLExact c live b) live]
   simp only [loopNestedSeqHOL,loopVisitWeight] at n
   have n' : loopVisitWeight (loopNestedSeqHOL ((compileExpHOLExact c (c.vmax+1) live e).1 ++
       [.assign (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (compileExpHOLExact c (c.vmax+1) live e).2.1,
        .ite .notEqual (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (.imm (0 : BitVec width))
         (compileHOLExact c live a) (compileHOLExact c live b) live]) ) =
     loopVisitWeight (loopNestedSeqHOL (compileExpHOLExact c (c.vmax+1) live e).1) +
       loopVisitWeight (compileHOLExact c live a) + loopVisitWeight (compileHOLExact c live b) + 4 := by omega
   simp only [compileHOLExact, callSyntaxCost]
   rw [n',ew]
   omega
 | @«while» e p he hp ih =>
   intro c live
   have ew := exprWeight he c ref (c.vmax+1) live
   have x := ih c live
   have n := nested_add (compileExpHOLExact c (c.vmax+1) live e).1
     [.assign (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (compileExpHOLExact c (c.vmax+1) live e).2.1,
      .ite .notEqual (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (.imm (0 : BitVec width))
       (.seq (compileHOLExact c live p) (.continue 0)) (.break 0) live]
   simp only [loopNestedSeqHOL,loopVisitWeight] at n
   have n' : loopVisitWeight (loopNestedSeqHOL ((compileExpHOLExact c (c.vmax+1) live e).1 ++
       [.assign (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (compileExpHOLExact c (c.vmax+1) live e).2.1,
        .ite .notEqual (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (.imm (0 : BitVec width))
         (.seq (compileHOLExact c live p) (.continue 0)) (.break 0) live]) ) =
     loopVisitWeight (loopNestedSeqHOL (compileExpHOLExact c (c.vmax+1) live e).1) +
       loopVisitWeight (compileHOLExact c live p) + 7 := by omega
   simp only [compileHOLExact, callSyntaxCost,loopVisitWeight]
   rw [n',ew]
   omega
private theorem assignsWeight (names : List Nat) (values : List (HolLoopExp width)) :
 loopVisitWeight (loopNestedSeqHOL (names.zipWith HolLoopProg.assign values)) = 1 + 2 * min names.length values.length := by
 induction names generalizing values with
 | nil => simp [loopNestedSeqHOL,loopVisitWeight]
 | cons name names ih =>
   cases values with
   | nil => simp [loopNestedSeqHOL,loopVisitWeight]
   | cons value values =>
     simp only [List.zipWith_cons_cons,loopNestedSeqHOL,loopVisitWeight,List.length_cons,Nat.succ_min_succ,ih]
     omega

private theorem callCost (ret : Option (List Nat)) (name : Flapjack.Basis.Pure.MlString.MlString)
 (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
 (ref c : CrepToLoopContextExact) (live : NumSet) :
 loopVisitWeight (compileHOLExact c live (.call (ret.map (fun ns => (ns,none))) name args)) ≤
 callSyntaxCost ref (.call (ret.map (fun ns => (ns,none))) name args) := by
 have ew := argsWeight args shape c ref (c.vmax+1) live
 obtain ⟨code,values,tmp,outLive,compiled,len,hp⟩ := compiledScalars_prefix args shape c (c.vmax+1) live
 simp only [compiled] at ew
 let names := genTemps tmp values.length
 have namesLen : names.length = args.length := by simp [names,genTemps,len]
 have wa := assignsWeight names values
 have n1 := nested_add code (names.zipWith HolLoopProg.assign values)
 cases ret with
 | none =>
   have n2 := nested_add (code ++ names.zipWith HolLoopProg.assign values)
     [.call none (some (findLabExact c name)) names none]
   simp only [loopNestedSeqHOL,loopVisitWeight] at n2
   simp only [compileHOLExact,Option.map_none,compiled,callSyntaxCost]
   change loopVisitWeight (loopNestedSeqHOL (code ++ names.zipWith HolLoopProg.assign values ++
     [.call none (some (findLabExact c name)) names none])) ≤ _
   rw [namesLen,len] at wa
   simp only [Nat.min_self] at wa
   omega
 | some retNames =>
   let mapped := match retNames.mapM c.vars.lookup with | none => [c.vmax+2] | some ns => ns
   have n2 := nested_add (code ++ names.zipWith HolLoopProg.assign values)
     [.call (some (mapped,live)) (some (findLabExact c name)) names
       (some (c.vmax+1,.raise (c.vmax+1),.skip,live))]
   simp only [loopNestedSeqHOL,loopVisitWeight] at n2
   simp only [compileHOLExact,Option.map_some,compiled,callSyntaxCost]
   change loopVisitWeight (loopNestedSeqHOL (code ++ names.zipWith HolLoopProg.assign values ++
     [.call (some (mapped,live)) (some (findLabExact c name)) names
       (some (c.vmax+1,.raise (c.vmax+1),.skip,live))])) ≤ _
   rw [namesLen,len] at wa
   simp only [Nat.min_self] at wa
   omega
/-- The syntax cost bounds compilation in every context and live set. -/
theorem callScalar_syntaxCost {p : CrepProgHOL width} (shape : CallScalarProgram p) (ref : CrepToLoopContextExact) :
 ∀ c live, loopVisitWeight (compileHOLExact c live p) ≤ callSyntaxCost ref p := by
 induction shape with
 | base h => exact scalarCost h ref
 | @dec name e p he hp ih =>
   intro c live
   have ew := exprWeight he c ref (c.vmax+1) live
   have b := ih {c with vars := c.vars.updateEq (name,(compileExpHOLExact c (c.vmax+1) live e).2.2.1), vmax := (compileExpHOLExact c (c.vmax+1) live e).2.2.1} (sptInsert (compileExpHOLExact c (c.vmax+1) live e).2.2.1 () live)
   rcases compiled : compileExpHOLExact c (c.vmax+1) live e with ⟨code,value,tmp,outlive⟩
   simp only [compiled] at ew b
   simp only [compileHOLExact,compiled,loopVisitWeight,callSyntaxCost]
   rw [ew]
   omega
 | @seq a b ha hb ia ib =>
   intro c live
   simp only [compileHOLExact,loopVisitWeight,callSyntaxCost]
   have x := ia c live
   have y := ib c live
   omega
 | @ite e a b he ha hb ia ib =>
   intro c live
   have ew := exprWeight he c ref (c.vmax+1) live
   have x := ia c live
   have y := ib c live
   have n := nested_add (compileExpHOLExact c (c.vmax+1) live e).1
     [.assign (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (compileExpHOLExact c (c.vmax+1) live e).2.1,
      .ite .notEqual (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (.imm (0 : BitVec width))
       (compileHOLExact c live a) (compileHOLExact c live b) live]
   simp only [loopNestedSeqHOL,loopVisitWeight] at n
   have n' : loopVisitWeight (loopNestedSeqHOL ((compileExpHOLExact c (c.vmax+1) live e).1 ++
       [.assign (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (compileExpHOLExact c (c.vmax+1) live e).2.1,
        .ite .notEqual (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (.imm (0 : BitVec width))
         (compileHOLExact c live a) (compileHOLExact c live b) live]) ) =
     loopVisitWeight (loopNestedSeqHOL (compileExpHOLExact c (c.vmax+1) live e).1) +
       loopVisitWeight (compileHOLExact c live a) + loopVisitWeight (compileHOLExact c live b) + 4 := by omega
   simp only [compileHOLExact, callSyntaxCost]
   rw [n',ew]
   omega
 | @loop e p he hp ih =>
   intro c live
   have ew := exprWeight he c ref (c.vmax+1) live
   have x := ih c live
   have n := nested_add (compileExpHOLExact c (c.vmax+1) live e).1
     [.assign (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (compileExpHOLExact c (c.vmax+1) live e).2.1,
      .ite .notEqual (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (.imm (0 : BitVec width))
       (.seq (compileHOLExact c live p) (.continue 0)) (.break 0) live]
   simp only [loopNestedSeqHOL,loopVisitWeight] at n
   have n' : loopVisitWeight (loopNestedSeqHOL ((compileExpHOLExact c (c.vmax+1) live e).1 ++
       [.assign (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (compileExpHOLExact c (c.vmax+1) live e).2.1,
        .ite .notEqual (compileExpHOLExact c (c.vmax+1) live e).2.2.1 (.imm (0 : BitVec width))
         (.seq (compileHOLExact c live p) (.continue 0)) (.break 0) live]) ) =
     loopVisitWeight (loopNestedSeqHOL (compileExpHOLExact c (c.vmax+1) live e).1) +
       loopVisitWeight (compileHOLExact c live p) + 7 := by omega
   simp only [compileHOLExact, callSyntaxCost,loopVisitWeight]
   rw [n',ew]
   omega | call ret name args h =>
   intro c live
   exact callCost ret name args h ref c live
/-- Maximum function cost over an explicit, computationally available code list. -/
def callTableCost (ref : CrepToLoopContextExact) (rows : List (List Nat × CrepProgHOL width)) : Nat :=
  (rows.map (fun row => callSyntaxCost ref row.2)).foldr max 1

theorem callSyntaxCost_le_table (ref : CrepToLoopContextExact)
    (rows : List (List Nat × CrepProgHOL width)) (params : List Nat) (body : CrepProgHOL width)
    (member : (params,body) ∈ rows) : callSyntaxCost ref body ≤ callTableCost ref rows := by
  induction rows with
  | nil => simp at member
  | cons row rest ih =>
    simp only [List.mem_cons] at member
    simp only [callTableCost,List.map_cons,List.foldr_cons]
    rcases member with same | tail
    · cases same
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih tail) (Nat.le_max_right _ _)

/-- Every supported member of the concrete code list fits its table maximum. -/
theorem callScalar_tableCost (ref c : CrepToLoopContextExact) (live : NumSet)
    (rows : List (List Nat × CrepProgHOL width)) (params : List Nat) (body : CrepProgHOL width)
    (member : (params,body) ∈ rows) (shape : CallScalarProgram body) :
    loopVisitWeight (compileHOLExact c live body) ≤ callTableCost ref rows :=
  (callScalar_syntaxCost shape ref c live).trans (callSyntaxCost_le_table ref rows params body member)
end SteppedFlapjack.CrepToLoopSteps
