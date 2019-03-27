open import Size
open import Codata.Thunk
open import Data.Fin
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Vec hiding (insert)
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module CounterMachine where

open import Data.AVL <-isStrictTotalOrder as AVL renaming (Tree to Tree′)

Tree = Tree′ (const ℕ)

_ : Tree
_ = insert 0 1 empty

inc : {n : ℕ} → Fin n → Maybe (Fin n)
inc {suc (suc n)} zero = just (suc zero)
inc {suc n} (suc x) with inc {n} x
... | just j  = just (suc j)
... | nothing = nothing
inc {suc n} zero = nothing
inc {zero} ()

_ : inc {5} (suc (suc (suc zero))) ≡ just (suc (suc (suc (suc zero))))
_ = refl

RegisterLabel = ℕ

InstructionIndex = Fin

Registers = Tree

-- https://en.wikipedia.org/wiki/Random-access_machine#Refresher:_The_counter-machine_model

data Instruction {progLen : ℕ} : Set where
  Incr : RegisterLabel → Instruction
  Decr : RegisterLabel → Instruction
  JZ   : RegisterLabel → InstructionIndex progLen → Instruction
  Halt : Instruction

data MachineState {progLen : ℕ}  : Set where
  Running : Fin progLen × Registers → MachineState
  Halted  : Registers → MachineState
  Crash   : MachineState

modifyRegister : {n : ℕ} → (ℕ → ℕ) → RegisterLabel → Registers → Registers
modifyRegister f label registers with AVL.lookup label registers
... | just val = insert label (f val) registers
... | nothing  = insert label (f 0) registers

advancePointer : {n : ℕ} → MachineState {n} → MachineState {n}
advancePointer {n} (Running (ip , r)) with inc ip
... | just ip′ = Running (ip′ , r)
... | nothing  = Crash
advancePointer s = s

jumpIfZero
  : {n : ℕ} → RegisterLabel → InstructionIndex n → InstructionIndex n → Registers
  → InstructionIndex n
jumpIfZero label target current registers with AVL.lookup label registers
... | just zero = target
... | _ = current

runInstruction : {n : ℕ} → Instruction {n} → MachineState {n} → MachineState {n}
runInstruction {n} (Incr r) (Running (ip , registers)) =
  advancePointer (Running (ip , modifyRegister {n} (Data.Nat._+ 1) r registers))
runInstruction {n} (Decr r) (Running (ip , registers)) = 
  advancePointer (Running (ip , modifyRegister {n} Data.Nat.pred r registers))
runInstruction (JZ r z) (Running (ip , registers)) =
  Running (jumpIfZero r z ip registers , registers)
runInstruction Halt (Running (ip , registers)) = Halted registers
runInstruction _ s = s

-- Fuel version!
runMachine : {n : ℕ} → ℕ → Vec (Instruction {n}) n → MachineState {n} → Maybe Registers
runMachine zero _ _ = nothing
runMachine _ _ (Halted x) = just x
runMachine _ _ Crash = nothing
runMachine (suc n) program state@(Running (ip , _)) =
  runMachine n program (runInstruction (Data.Vec.lookup ip program) state)

program : Vec (Instruction {2}) 2
program = Incr 1 ∷ Halt ∷ []

_ : runInstruction {2} (Incr 1) (Running (zero , empty)) ≡ Running (suc zero , insert 1 1 empty)
_ = refl

_ : runMachine 10 program (Running (zero , empty)) ≡ just (insert 1 1 empty)
_ = refl

data State (n : ℕ) (i : Size) : Set where
  Crashed : State n i
  Stop : MachineState {n} → State n i
  Step : MachineState {n} → Thunk (State n) i → State n i

run : {n : ℕ} → Vec (Instruction {n}) n → MachineState {n} → State n ∞
run program state@(Running (ip , _)) with runInstruction (Data.Vec.lookup ip program) state
... | Crash = Crashed
... | Halted x = Stop (Halted x)
... | Running state′ = Step (Running state′) ?
run program state = Stop state
