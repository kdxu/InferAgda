module Infer where
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning 
open import Data.Nat
open import Data.Vec
open import Data.Product
open import Data.Empty
open import Data.Fin
open import Data.Sum
open import Data.Bool
open import Level
-----------------------------------------------

--Termにはwellscopedtermを使うといい．
--TypeにはFUSRのtermが使える．

data Type (n : ℕ) : Set where
  ι : (x : Fin n) → Type n -- 変数 (de bruijn index) 
  leaf : Type n -- base case の型
  _fork_ : (s t : Type n) → Type n -- arrow 型

data AList : ℕ →  Set where
  anil : {m : ℕ} → AList m
  _acons_/_ : {m : ℕ} → (σ : AList m) → (t : Type m) → (x : Fin (ℕ.suc m)) → AList (ℕ.suc m)

Cxt : ℕ → Set
Cxt n = AList n

data WellScopedTerm {n : ℕ} (Γ : Cxt n) : Set where
  Var : Fin n → WellScopedTerm Γ
  Lam : (τ : Type) → WellScopedTerm (τ ∷ Γ) → WellScopedTerm Γ
  App : WellScopedTerm Γ → WellScopedTerm Γ → WellScopedTerm Γ
