import SteppedFlapjack.WordToStackSteps.CallSequence

/-! Code-map stability needed for composing target cost bounds. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps
open SteppedFlapjack.StackRemoveSteps.CompCorrect

/-- Equal source code domains force equal related target code domains. -/
theorem relatedTargetCodeDomains {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat) (lens : List Nat)
    (s t : WordSemStateFiniteExact width (Nat × C) F)
    (u v : StackSemStateFiniteExact width C F)
    (before : stateRel ac k f frame s u lens 0)
    (after : stateRel ac k f frame t v lens 0)
    (sameCode : t.code = s.code) : sptDomain v.code = sptDomain u.code := by
  have r1 := before
  have r2 := after
  unfold stateRel at r1 r2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, d1, _⟩ := r1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, d2, _⟩ := r2
  rw [d1, d2, sameCode]

/-- Growth plus equal domains preserves each code lookup. -/
theorem lookup_eq_of_growth_and_domain {α : Type} (old new : Spt α)
    (growth : sptSubspt old new) (domain : sptDomain new = sptDomain old) :
    ∀ key, sptLookup key new = sptLookup key old := by
  intro key
  cases h : sptLookup key old with
  | some value => simpa only [h] using (growth key (by simp [sptMem, sptDomain, h])).2
  | none =>
    have missing : ¬ sptDomain new key := by rw [domain]; simp [sptDomain,h]
    cases hnew : sptLookup key new with
    | none => rfl
    | some value => exact False.elim (missing (by simp [sptDomain,hnew]))

/-- A pair listed by the finite code map is an actual lookup. -/
theorem sptToAList_entry_lookup {α : Type} (code : Spt α) (key : Nat) (value : α)
    (member : (key,value) ∈ sptToAList code) : sptLookup key code = some value := by
  have fold : (key,value) ∈ sptFoldi (fun k v entries => (k,v) :: entries) 0 [] code := by
    simpa [sptToAList] using member
  rcases sptFoldi_mem_address code 0 [] key value fold with impossible | ⟨localKey, address, lookup⟩
  · simp at impossible
  · have eq : key = localKey := by simpa [sptAcc_eq,lrNext] using address
    subst localKey
    exact lookup

/-- Extensional code equality gives the same computable maximum loop cost. -/
theorem loopCodeCost_eq_of_lookup {width : Nat} [NeZero width]
    (clock : Nat) (a b : Spt (HolProg width))
    (same : ∀ key, sptLookup key a = sptLookup key b) :
    loopCodeCost clock a = loopCodeCost clock b := by
  have maxBound (xs : List Nat) (bound : Nat) (h : ∀ z, z ∈ xs → z ≤ bound) : maxListNat xs ≤ bound := by
    induction xs with
    | nil => simp [maxListNat]
    | cons z zs ih =>
      simp only [maxListNat, max_le_iff]
      exact ⟨h z (by simp), ih (by intro w hw; exact h w (by simp [hw]))⟩
  have bound (x y : Spt (HolProg width)) (h : ∀ key, sptLookup key x = sptLookup key y) :
      loopCodeCost clock x ≤ loopCodeCost clock y := by
    apply maxBound
    intro z hz
    obtain ⟨⟨key,value⟩, hm, rfl⟩ := List.mem_map.mp hz
    have lookup := sptToAList_entry_lookup x key value hm
    exact loopCodeCost_bound clock y key value ((h key).symm.trans lookup)

  exact Nat.le_antisymm (bound a b same) (bound b a (fun key => (same key).symm))


/-- A continuing related execution preserves the source code map's target
cost: the source no-install theorem fixes the domain, while StackSem code
monotonicity fixes the entries in that domain. -/
theorem continuingCodeCost_stable {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame clock : Nat) (lens : List Nat)
    (p : WordLangProgHOL (BitVec width)) (compiled : HolProg width)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target targetPost : StackSemStateFiniteExact width C F)
    (sourceRun : WordSemStateFiniteExact.evaluate p source = (none,sourcePost))
    (targetRun : StackSemEvaluate.evaluate (compiled,target) = (none,targetPost))
    (related : stateRel ac k f frame source target lens 0)
    (conclusion : compCorrectResult ac k f frame source sourcePost targetPost none none lens)
    (noInstall : noInstallSubprogsHOL p = true) (noInstallCode : WordProps.noInstallCode source.code) :
    loopCodeCost clock targetPost.code = loopCodeCost clock target.code := by
  have sourceSame := WordSemStateFiniteExact.code_evaluate p source noInstall noInstallCode
  rw [sourceRun] at sourceSame
  have postRelated : stateRel ac k f frame sourcePost targetPost lens 0 := by
    simpa [compCorrectResult] using conclusion
  have domain := relatedTargetCodeDomains ac k f frame lens source sourcePost target targetPost related postRelated sourceSame
  have growth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono compiled target targetPost none targetRun).2
  exact loopCodeCost_eq_of_lookup clock targetPost.code target.code
    (lookup_eq_of_growth_and_domain target.code targetPost.code growth domain)


/-- Structural loop cost is monotone in the clock limit. -/
theorem loopOnlyCost_mono {width : Nat} [NeZero width] (p : HolProg width)
    {lo hi : Nat} (h : lo ≤ hi) : loopOnlyCost lo p ≤ loopOnlyCost hi p := by
  cases hp : p <;> simp only [loopOnlyCost]
  case seq a b =>
    have ha := loopOnlyCost_mono a h
    have hb := loopOnlyCost_mono b h
    omega
  case ite cmp r ri a b =>
    have ha := loopOnlyCost_mono a h
    have hb := loopOnlyCost_mono b h
    omega
  case loop body =>
    have hb := loopOnlyCost_mono body h
    exact Nat.mul_le_mul (Nat.add_le_add_right hb 1) (Nat.add_le_add_right h 1)
  all_goals omega
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf; try omega

/-- The maximum loop cost over a finite code map is monotone in the clock. -/
theorem loopCodeCost_mono {width : Nat} [NeZero width] (code : Spt (HolProg width))
    {lo hi : Nat} (h : lo ≤ hi) : loopCodeCost lo code ≤ loopCodeCost hi code := by
  have bound (entries : List (Nat × HolProg width)) :
      maxListNat (entries.map (fun entry => loopOnlyCost lo entry.2)) ≤
      maxListNat (entries.map (fun entry => loopOnlyCost hi entry.2)) := by
    induction entries with
    | nil => simp [maxListNat]
    | cons entry entries ih =>
      simp only [List.map_cons,maxListNat]
      exact max_le_max (loopOnlyCost_mono entry.2 h) ih
  exact bound (sptToAList code)

/-- A handler continuation's structural cost is monotone in the clock. -/
theorem handlerCost_mono {width : Nat} [NeZero width]
    (handler : Option (HolProg width × Nat × Nat)) {lo hi : Nat} (h : lo ≤ hi) :
    handlerCost lo handler ≤ handlerCost hi handler := by
  cases handler with
  | none => rfl
  | some v => rcases v with ⟨p,a,b⟩; exact loopOnlyCost_mono p h

/-- The complete generated returning-call bound is monotone in the clock. -/
theorem returningChainCost_mono {width : Nat} [NeZero width]
    (code : Spt (HolProg width)) (p : HolProg width) {lo hi : Nat} (h : lo ≤ hi) :
    returningChainCost lo code p ≤ returningChainCost hi code p := by
  cases hp : p <;> try simp only [returningChainCost]
  case seq a b =>
    have ha := loopOnlyCost_mono a h
    have hb := returningChainCost_mono code b h
    omega
  case call ret dest handler =>
    cases ret with
    | none => simp [returningChainCost]
    | some r =>
      rcases r with ⟨p,link,l1,l2⟩
      simp only [returningChainCost]
      have hc := loopCodeCost_mono code h
      have hp := loopOnlyCost_mono p h
      have hh := handlerCost_mono handler h
      omega
  all_goals omega
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf; try omega


/-- A related returning call is bounded using any larger common clock limit. -/
theorem compiledReturning_related_bound_at {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (live : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (bs : AppList (BitVec width) × Nat) (k f frame limit : Nat) (lens : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) (target : StackSemStateFiniteExact width C F)
    (related : stateRel ac k f frame source target lens 0) (clockBound : source.clock ≤ limit)
    (code : ∀ label arity p, sptLookup label source.code = some (arity,p) → LoopBlock p)
    (retBlock : LoopBlock retCode)
    (handlerBlock : ∀ v p a b, handler = some (v,p,a,b) → LoopBlock p) :
    StackSteps.steps ((Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false
      (.call (some (values,live,retCode,l1,l2)) dest args handler) bs (k,f,frame)).1,target) ≤
      returningChainCost limit target.code (Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false
        (.call (some (values,live,retCode,l1,l2)) dest args handler) bs (k,f,frame)).1 := by
  have initial := compiledReturning_related_bound ac values live retCode l1 l2 dest args handler bs
    k f frame lens source target related code retBlock handlerBlock
  exact initial.trans (returningChainCost_mono target.code _ clockBound)


/-- The generated returning-call cost depends on the code map only through
its maximum callee cost. -/
theorem returningChainCost_eq_of_codeCost {width : Nat} [NeZero width]
    (clock : Nat) (a b : Spt (HolProg width)) (p : HolProg width)
    (sameCost : loopCodeCost clock a = loopCodeCost clock b) :
    returningChainCost clock a p = returningChainCost clock b p := by
  cases hp : p <;> try simp only [returningChainCost]
  case seq first second =>
    rw [returningChainCost_eq_of_codeCost clock a b second sameCost]
  case call ret dest handler =>
    cases ret with
    | none => rfl
    | some r =>
      rcases r with ⟨body,link,l1,l2⟩
      simp only [returningChainCost,sameCost]
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf; try omega

/-- A continuing related execution preserves the cost of any generated
returning-call program, at every common clock bound. -/
theorem continuingReturningCost_stable {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame clock : Nat) (lens : List Nat)
    (p : WordLangProgHOL (BitVec width)) (compiled next : HolProg width)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target targetPost : StackSemStateFiniteExact width C F)
    (sourceRun : WordSemStateFiniteExact.evaluate p source = (none,sourcePost))
    (targetRun : StackSemEvaluate.evaluate (compiled,target) = (none,targetPost))
    (related : stateRel ac k f frame source target lens 0)
    (conclusion : compCorrectResult ac k f frame source sourcePost targetPost none none lens)
    (noInstall : noInstallSubprogsHOL p = true) (noInstallCode : WordProps.noInstallCode source.code) :
    returningChainCost clock targetPost.code next = returningChainCost clock target.code next := by
  apply returningChainCost_eq_of_codeCost
  exact continuingCodeCost_stable ac k f frame clock lens p compiled source sourcePost target targetPost
    sourceRun targetRun related conclusion noInstall noInstallCode

end SteppedFlapjack.WordToStackSteps
