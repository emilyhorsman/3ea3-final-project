open import Data.Fin
open import Data.Maybe
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Product
open import Data.Sum
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable using (False)
open ≡-Reasoning

{- Z-notation for sums -}
Σ∶• : ∀{a b} (A : Set a) (B : A → Set b) → Set _
Σ∶• = Σ
infix -666 Σ∶•
syntax Σ∶• A (λ x → B) = Σ x ∶ A • B  -- \:

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

-- This should never terminate!
program₃ : Vec Instruction 2
program₃ = Next ∷ Rest ∷ []

-- We will not halt no matter which instruction pointer we observe from.
pf₁
  : ∀ {n init : ℕ} (ip : Fin 2)
  → (step (run {2} program₃ ip init)) f 2 ≢ Halted n
pf₁ zero ()
pf₁ (suc zero) ()
pf₁ (suc (suc ()))

-- How do we prove that we will never halt when starting from the beginning
-- of this program?
program₄ : Vec Instruction 3
program₄ = Next ∷ Rest ∷ Next ∷ []

pf₂
  : ∀ {n init : ℕ} (steps : ℕ)
  → (step (run {3} program₄ zero init)) f steps ≢ Halted n
pf₂ zero ()
pf₂ (suc zero) ()
pf₂ (suc (suc steps)) = {!!}
