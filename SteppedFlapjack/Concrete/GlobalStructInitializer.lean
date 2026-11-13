import SteppedFlapjack.PanToCrepSteps.GlobalInitialState
import SteppedFlapjack.Concrete.GlobalStructCrep
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.StackRemove SteppedFlapjack.PanToCrepSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem domain_same (a : BitVec 64) :
    ordinaryAddress a ∧ ¬ addresses globalStructSourceTop 2 a ↔ globalStructSourceDomain a := by
  constructor
  · rintro ⟨ordinary, noSlot⟩
    refine ⟨ordinary,?_⟩
    by_contra notBelow
    have range := ordinary
    unfold ordinaryAddress at range
    have cases : a.toNat = globalStructSourceTop.toNat ∨ a.toNat = (globalStructSourceTop + 8).toNat := by
      have top : globalStructSourceTop.toNat = 33806089680 := by decide
      have next : (globalStructSourceTop + 8).toNat = 33806089688 := by decide
      have limit : fixtureHeapEnd = 33806089696 := by decide
      have lower : 33806089680 ≤ a.toNat := by simpa [top] using notBelow
      have upper : a.toNat < 33806089696 := by simpa [limit] using range.2.1
      have align : a.toNat % 8 = 0 := range.2.2
      rw [top,next]
      omega
    rcases cases with h | h
    · have eq : a = globalStructSourceTop := BitVec.eq_of_toNat_eq h
      subst a
      apply noSlot
      rw [mem_addresses]
      exact ⟨0,by decide,by simp [bytesInWord]⟩
    · have eq : a = globalStructSourceTop + 8 := BitVec.eq_of_toNat_eq h
      subst a
      apply noSlot
      rw [mem_addresses]
      exact ⟨1,by decide,by simp [bytesInWord]⟩
  · intro h
    exact ⟨h.1,globalStructSlots_disjoint a h⟩
theorem pairBefore_eq : beforeGlobals globalStructTarget 16 2 = globalStructBase := by
  have h : (fun a => ordinaryAddress a ∧ ¬ addresses globalStructSourceTop 2 a) = globalStructSourceDomain := by
    funext a
    exact propext (domain_same a)
  change {sourceTemplate with topAddr := globalStructSourceTop, memaddrs := (fun a => ordinaryAddress a ∧ ¬ addresses globalStructSourceTop 2 a), globals := HolFiniteMapExact.empty, code := HolFiniteMapExact.empty, structs := []} = globalStructBase
  rw [h]
  rfl

theorem globalStructSlots_allocated : ∀ a, addresses (globalStructTarget.topAddr - 16) 2 a → globalStructTarget.memaddrs a := by
  intro a ha
  rw [mem_addresses] at ha
  obtain ⟨i,hi,heq⟩ := ha
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · have eq : a = globalStructSourceTop := by simpa [globalStructTarget,globalStructSourceTop,sourceTemplate,bytesInWord] using heq
    subst a
    exact globalStructTarget_layout.2.1
  · have eq : a = globalStructSourceTop + 8 := by simpa [globalStructTarget,globalStructSourceTop,sourceTemplate,bytesInWord] using heq
    subst a
    exact globalStructTarget_layout.2.2.1
end SteppedFlapjack.Concrete
