import SteppedFlapjack.Concrete.CountdownWordSimpLiteral
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend SteppedFlapjack.Concrete

private def inSpine (x : BitVec 64) (a b c d e : WordLangProgHOL (BitVec 64)) : WordLangProgHOL (BitVec 64) :=
  .seq (.seq (.seq (.seq (.seq (.inst (.const 2 x)) a) b) c) d) e

def countdownSsaReplaceConstant (x : BitVec 64) : WordLangProgHOL (BitVec 64) → WordLangProgHOL (BitVec 64)
  | .seq (.seq (.seq (.seq (.seq (.inst (.const reg _)) a) b) c) d) e =>
      .seq (.seq (.seq (.seq (.seq (.inst (.const reg x)) a) b) c) d) e
  | p => p
set_option maxHeartbeats 1000000 in
private theorem ssaSpine_constant (x y : BitVec 64) (a b c d e : WordLangProgHOL (BitVec 64)) (ssa : Spt Nat) (na : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit)) :
    let r := WordAlloc.ssaCcTrans (inSpine y a b c d e) ssa na lt
    WordAlloc.ssaCcTrans (inSpine x a b c d e) ssa na lt = (countdownSsaReplaceConstant x r.1,r.2) := by
  unfold inSpine
  simp only [WordAlloc.ssaCcTrans,WordAlloc.ssaCcTransInst]
  rfl

private theorem ssaUnfold (p : WordLangProgHOL (BitVec 64)) :
  WordAlloc.fullSsaCcTrans 1 p =
    let setup := WordAlloc.setupSSA (outputWidth := 64) 1 (WordAlloc.limitVar p) p
    .seq setup.1 (WordAlloc.ssaCcTrans p setup.2.1 setup.2.2 []).1 := by
  unfold WordAlloc.fullSsaCcTrans
  cases h : WordAlloc.setupSSA (outputWidth := 64) 1 (WordAlloc.limitVar p) p with
  | mk mov rest =>
    cases rest with
    | mk s na =>
      cases h2 : WordAlloc.ssaCcTrans p s na [] with
      | mk body final => cases final; simp only [h, h2]

set_option maxHeartbeats 1000000 in
/-- SSA changes only the initial constant, with the same register-renaming suffix. -/
theorem countdown_ssa_constant (x : BitVec 64) :
    let setup := WordAlloc.setupSSA (inputWidth := 64) (outputWidth := 64) 1 9 (countdownSelectedWord 5)
    WordAlloc.fullSsaCcTrans 1 (countdownSelectedWord x) =
      .seq setup.1 (countdownSsaReplaceConstant x (WordAlloc.ssaCcTrans (countdownSelectedWord 5) setup.2.1 setup.2.2 []).1) := by
  let loop : WordLangProgHOL (BitVec 64) := .loop (.bs (.ls ()) () .ln)
      (.seq (.seq (.move 0 [(4,2)])
        (.ite .notEqual 4 (.imm 0)
          (.seq (.seq (.seq (.move 0 [(5,2)]) (.inst (.arith (.binop .add 4 5 (.imm (-1)))))) (.move 0 [(2,4)])) (.continue 0))
          (.break 0))) .tick) (.ls ())
  let setup := WordAlloc.setupSSA (inputWidth := 64) (outputWidth := 64) 1 9 (countdownSelectedWord 5)
  have h := ssaSpine_constant x 5 .tick loop .tick (.inst (.const 4 0)) (.return 0 [4]) setup.2.1 setup.2.2 []
  have q := congrArg Prod.fst h
  rw [ssaUnfold,countdownSelectedWord_limit]
  change WordLangProgHOL.seq setup.1 (WordAlloc.ssaCcTrans (inSpine x .tick loop .tick (.inst (.const 4 0)) (.return 0 [4])) setup.2.1 setup.2.2 []).1 =
    WordLangProgHOL.seq setup.1 (countdownSsaReplaceConstant x (WordAlloc.ssaCcTrans (inSpine 5 .tick loop .tick (.inst (.const 4 0)) (.return 0 [4])) setup.2.1 setup.2.2 []).1)
  exact congrArg (fun body => WordLangProgHOL.seq setup.1 body) q

/-- Replace the count in the SSA entry's constant instruction. -/
private def replaceSsaRoot (x : BitVec 64) : WordLangProgHOL (BitVec 64) → WordLangProgHOL (BitVec 64)
  | .seq entry body => .seq entry (countdownSsaReplaceConstant x body)
  | p => p

private theorem countdown_ssa_replace (x : BitVec 64) :
    WordAlloc.fullSsaCcTrans 1 (countdownSelectedWord x) =
      replaceSsaRoot x (WordAlloc.fullSsaCcTrans 1 (countdownSelectedWord 5)) := by
  rw [ssaUnfold (countdownSelectedWord 5), countdownSelectedWord_limit]
  exact countdown_ssa_constant x

/-- Exact SSA countdown code; the count occurs in one constant instruction. -/
def countdownSsaWord (x : BitVec 64) : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.seq
  (Flapjack.WordLangProgHOL.move 1 [(9, 0)])
  (Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.seq
      (Flapjack.WordLangProgHOL.seq
        (Flapjack.WordLangProgHOL.seq
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 13 x))
            (Flapjack.WordLangProgHOL.tick))
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.seq
              (Flapjack.WordLangProgHOL.skip)
              (Flapjack.WordLangProgHOL.move 0 [(17, 9), (21, 13)]))
            (Flapjack.WordLangProgHOL.loop
              (Flapjack.Spt.bn
                (Flapjack.Spt.ln)
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.ls ()))
                    (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.ls ())))
                  (Flapjack.Spt.ln)))
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.seq
                  (Flapjack.WordLangProgHOL.seq
                    (Flapjack.WordLangProgHOL.move 0 [(25, 21)])
                    (Flapjack.WordLangProgHOL.ite
                      (Flapjack.Cmp.notEqual)
                      25
                      (Flapjack.WordRegImm.imm 0x0000000000000000#64)
                      (Flapjack.WordLangProgHOL.seq
                        (Flapjack.WordLangProgHOL.seq
                          (Flapjack.WordLangProgHOL.seq
                            (Flapjack.WordLangProgHOL.seq
                              (Flapjack.WordLangProgHOL.move 0 [(29, 25)])
                              (Flapjack.WordLangProgHOL.inst
                                (Flapjack.WordLangInst.arith
                                  (Flapjack.WordLangArith.binop
                                    (Flapjack.BinOp.add)
                                    33
                                    29
                                    (Flapjack.WordRegImm.imm 0xffffffffffffffff#64)))))
                            (Flapjack.WordLangProgHOL.move 0 [(37, 33)]))
                          (Flapjack.WordLangProgHOL.seq
                            (Flapjack.WordLangProgHOL.move 1 [(21, 37)])
                            (Flapjack.WordLangProgHOL.continue 0)))
                        (Flapjack.WordLangProgHOL.seq
                          (Flapjack.WordLangProgHOL.move 1 [(45, 37), (41, 37)])
                          (Flapjack.WordLangProgHOL.seq
                            (Flapjack.WordLangProgHOL.skip)
                            (Flapjack.WordLangProgHOL.move 1 [(49, 29)]))))
                      (Flapjack.WordLangProgHOL.seq
                        (Flapjack.WordLangProgHOL.break 0)
                        (Flapjack.WordLangProgHOL.seq
                          (Flapjack.WordLangProgHOL.move 1 [(45, 25), (41, 25)])
                          (Flapjack.WordLangProgHOL.seq
                            (Flapjack.WordLangProgHOL.skip)
                            (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 49 0x0000000000000000#64)))))))
                  (Flapjack.WordLangProgHOL.tick))
                (Flapjack.WordLangProgHOL.move 1 [(21, 41)]))
              (Flapjack.Spt.bn
                (Flapjack.Spt.ln)
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.ls ())))
                  (Flapjack.Spt.ln))))))
        (Flapjack.WordLangProgHOL.tick))
      (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 53 0x0000000000000000#64)))
    (Flapjack.WordLangProgHOL.seq (Flapjack.WordLangProgHOL.move 0 [(2, 53)]) (Flapjack.WordLangProgHOL.return 17 [2])))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem countdown_ssa_baseline :
    WordAlloc.fullSsaCcTrans 1 (countdownSelectedWord 5) = countdownSsaWord 5 := by
  with_unfolding_all rfl

/-- The SSA pass emits the literal for every countdown value. -/
theorem countdown_ssa_literal (x : BitVec 64) :
    WordAlloc.fullSsaCcTrans 1 (countdownSelectedWord x) = countdownSsaWord x := by
  rw [countdown_ssa_replace, countdown_ssa_baseline]
  rfl

end SteppedFlapjack.Concrete
