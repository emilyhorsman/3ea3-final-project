open import Data.Fin
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Sum
open import Data.Vec
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable using (False)
open ≡-Reasoning

inc : {n : ℕ} → Fin n → Maybe (Fin n)
inc {suc (suc n)} zero = just (suc zero)
inc {suc n} (suc x) with inc {n} x
... | just j  = just (suc j)
... | nothing = nothing
inc {suc n} zero = nothing
inc {zero} ()

data Instruction : Set where
  Next : Instruction
  Rest : Instruction
  Halt : Instruction

data Status : Set

record State : Set where
  coinductive
  field
    step : Status

data Status where
  Halted : ℕ → Status
  Running : State → Status

open State

run
  : {n : ℕ} → {nonempty : False (n Data.Nat.≟ 0)}
  → Vec Instruction n → Fin n → ℕ → State
step (run {n} {nonempty} prog ip init) with lookup ip prog
… | Halt = Halted init
… | Rest = Running
  (run {n} {nonempty} prog (_mod_ n n {nonempty}) init)
… | Next with inc ip
…   | just ip′ = Running (run {n} {nonempty} prog ip′ (init Data.Nat.+ 1))
…   | nothing  = Halted 0

program₁ : Vec Instruction 2
program₁ = Next ∷ Halt ∷ []

program₂ : Vec Instruction 1
program₂ = Next ∷ []

_ : step (run program₂ zero 0) ≡ Halted 0
_ = refl

_f_ : Status → ℕ → Status
(Running x) f (suc n) = (step x) f n
x f _ = x

_ : (step (run program₁ zero 0)) f 1 ≡ Halted 1
_ = refl

program₃ : Vec Instruction 1
program₃ = Rest ∷ []

pf₀ : ∀ (n : ℕ) → step (run {1} program₃ zero 0) ≢ Halted n
pf₀ n ()

pf₁ : ∀ {n : ℕ} (steps : ℕ) → step (run {1} program₃ zero 0) f steps ≢ Halted n
pf₁ zero ()
pf₁ (suc steps) = {!!}
