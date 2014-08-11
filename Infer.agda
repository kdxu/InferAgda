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
open import Data.List
open import Data.Maybe
import FUSR 
import Level
-----------------------------------------------

--Termにはwellscopedtermを使うといい．
--TypeにはFUSRのtermが使える．

data Type (n : ℕ) : Set where
  ι : (x : Fin n) → Type n -- 変数 (de bruijn index) 
  leaf : Type n -- base case の型
  _fork_ : (s t : Type n) → Type n -- arrow 型


data AList : ℕ → ℕ → Set where
  anil : {m : ℕ} → AList m m
  _asnoc_/_ : {m : ℕ} {n : ℕ} → (σ : AList m n) → (t' : Type m) → (x : Fin (suc m)) → AList (suc m) n

Cxt : {m : ℕ} → ℕ → Set
Cxt {m} n = Vec (Type m) n -- ここのmをどう持ち歩いてよいか分からない．

data WellScopedTerm {m n : ℕ} (Γ : Cxt {m} n) : Set where
  Var : Fin n → WellScopedTerm Γ
  Lam : (τ : Type m) → WellScopedTerm {m} (τ ∷ Γ) → WellScopedTerm Γ
  App : WellScopedTerm {m} Γ → WellScopedTerm {m} Γ → WellScopedTerm Γ

unify : {m : ℕ} → Type m → Type m → Maybe (∃ (AList m))
unify {m} t1 t2 = {!!}
inferW : {m n l : ℕ} →  {Γ : Cxt {m} n} → WellScopedTerm Γ →  (WellScopedTerm Γ × Type l)
inferW (Var x) = {!!}
inferW (Lam τ t) = {!!}
inferW (App t t₁) = {!!}
