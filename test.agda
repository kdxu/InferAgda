module test where

open import mgu
open import term
open import infer
open import Data.Unit using (tt)
open import Data.Nat
open import Data.Vec hiding (_++_)
open import Data.Vec.Properties
open import Data.Product
open import Data.Fin hiding (_+_; _≤_)
open import Data.Maybe
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Nat.Properties
open import Algebra.Structures
open import Function using (_∘_)
open import Relation.Binary hiding (_⇒_)
------------------------------------
-- for test

Var1 : WellScopedTerm 1
Var1 = Var (fromℕ 0)

CxtE : {m : ℕ} → Cxt {m} 1
CxtE = (TVar {! fromℕ  !}) ∷ []

{-
test1 : (m : ℕ) → {n : ℕ} → (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m'' ∈ ℕ ]
                Σ[ m' ∈ ℕ ]
                Σ[ m≤m'' ∈ m ≤ m'' ]
                Σ[ σ ∈ AListType m'' m' ]
                Σ[ τ ∈ Type m' ]
                WellTypedTerm (substCxt≤ σ m≤m'' Γ) τ)
test1 = infer [] (Var 1)
-}
