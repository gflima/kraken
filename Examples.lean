module

import Kraken.AArch64.OmniSemantics
import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.AArch64.Sep
import Kraken.Eval
import Kraken.SeparationTactics
import Kraken.Tactics
import Std.Tactic.BVDecide

open Kraken (Layout WellFormedLayout)
open Kraken.AArch64
open Kraken.AArch64.Parser

attribute [ksimp]
  BitVec.add_zero
  BitVec.ofInt_add
  BitVec.ofInt_ofNat
  BitVec.ofInt_toInt
  BitVec.ofNat_uInt64ToNat
  BitVec.setWidth_eq
  Int.add_zero
  Int64.toInt_neg
  Nat.shiftRight_zero
  Nat.sub_zero
  UInt64.ofBitVec_add
  UInt64.ofBitVec_ofNat
  UInt64.ofBitVec_sub
  UInt64.ofBitVec_toBitVec
  UInt64.sub_add_cancel
  UInt64.toBitVec_ofNat
  UInt64.toBitVec_sub
  UInt64.toNat_toBitVec

/-! # Simple -/

def simple : Program := ⸨prog|
  add x2, x1, x0
  sub x2, x2, x1
⸩

-- theorem simple_spec (pc a b : BitVec 64) :
--     arm.Ensures
--     (fun s ↦                    -- precondition
--       s.AlignedBytesLoaded pc simple ∧
--       s.read PC = pc ∧
--       s.read X0 = a ∧
--       s.read X1 = b)
--     (fun s ↦                    -- postcondition
--       s.read PC = pc + 8 ∧
--       s.read X2 = a)
--     (MayChange [PC, X2]) := by  -- frame
--   simp [Rel.Ensures]; intro s hl hPC hX0 hX1
--   sorry

theorem simple_spec [layout : WellFormedLayout simple] (d : MachineData) :
    Eventually (step1 simple.toExecutable)
      (fun s' =>
        s'.pc = simple.toExecutable.addrOf simple.length ∧
        s'.1.regs.getRegOrZr .X2 = d.regs.getRegOrZr .X0)
      ⟨d, layout.start⟩ := by
  kprologue simple with d
  sym => kstep; tactic =>
  refine .done _ ⟨rfl, ?_⟩; grind
