open import Data.Fin
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Sum
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (False)

data Instruction : Set where
  Next : Instruction
  Rest : Instruction
  Halt : Instruction

record State : Set where
  coinductive
  field
    step : ℕ ⊎ State

open State

run
  : {n : ℕ} → {nonempty : False (n Data.Nat.≟ 0)}
  → Vec Instruction n → Fin n → ℕ → State
step (run {n} {nonempty} prog ip init) with lookup ip prog
… | Halt = inj₁ (init Data.Nat.+ 1)
… | Rest = inj₂
  (run {n} {nonempty} prog (_mod_ n n {nonempty}) init)
… | Next = inj₂
  (run {n} {nonempty} prog
    (_mod_ (suc (toℕ ip)) n {nonempty})
    (init Data.Nat.+ 1))

program₁ : Vec Instruction 2
program₁ = Next ∷ Rest ∷ []

program₂ : Vec Instruction 1
program₂ = Next ∷ []

_ : step (run program₁ zero 0) ≡ step (run program₂ zero 0)
_ = {!!}
