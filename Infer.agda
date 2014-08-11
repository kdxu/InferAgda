module Infer where
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning 
open import Data.Nat
open import Data.Vec 
open import Data.Product
open import Data.Empty
open import Data.Fin hiding (_+_)
open import Data.Sum
open import Data.Bool
open import Data.List
open import Data.Maybe
open import lib
open import Function
import Level

+-right-identity : ∀ n → n + 0 ≡ n
+-right-identity zero = refl
+-right-identity (suc n) = cong suc $ +-right-identity n

--injectv₁ : ∀ {m} → Fin m → Fin (suc m)
--injectv₁ zero    = zero
--injectv₁ (suc i) = suc (inject₁ i)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

vecinject : {m m' n : ℕ} → (Type m → Type m') → Vec (Type m) n → Vec (Type m') n
vecinject f [] = []
vecinject f (x ∷ v) = (f x) ∷ vecinject f v

-----------------------------------------------

--Termにはwellscopedtermを使うといい．
--TypeにはFUSRのtermが使える．

Cxt : {m : ℕ} → ℕ → Set
Cxt {m} n = Vec (Type m) n -- ここのmをどう持ち歩いてよいか分からない．

data WellScopedTerm (n : ℕ) : Set where
  Var : Fin n → WellScopedTerm n
  Lam : WellScopedTerm (suc n) → WellScopedTerm n
  App : WellScopedTerm n → WellScopedTerm n → WellScopedTerm n

{-
data WellScopedTerm {m n : ℕ} (Γ : Cxt {m} n) : Set where
  Var : Fin n → WellScopedTerm Γ
  Lam : (τ : Type m) → WellScopedTerm {m} (τ ∷ Γ) → WellScopedTerm Γ
  App : WellScopedTerm {m} Γ → WellScopedTerm {m} Γ → WellScopedTerm Γ

terminject : {m m' n : ℕ} → (Type m → Type m') → {Γ : Cxt {m} n} → {Γ' : Cxt {m'} n} → WellScopedTerm Γ → WellScopedTerm Γ'
terminject f (Var x) = Var x
terminject f (Lam τ t) = Lam (f τ) (terminject f t)
terminject f (App t t₁) = App (terminject f t) (terminject f t₁)
-}

unify : {m : ℕ} → Type m → Type m → Maybe (∃ (AList m))
unify {m} t1 t2 = mgu {m} t1 t2

count : {n : ℕ} → (t : WellScopedTerm n) → ℕ
count (Var x) = zero
count (Lam t) = suc (count t)
count (App t t₁) = count t + suc (count t₁) 

inferW : {m n : ℕ} →  (Γ : Cxt {m} n) → (e : WellScopedTerm n) → (Σ[ m' ∈ ℕ ] AList (m + count e) m' × Type m')
inferW {m} Γ (Var x) rewrite (+-right-identity m) = m , (anil , lookup x Γ)
inferW {m} Γ (Lam e) with inferW {suc m} (ι (fromℕ m) ∷ (vecinject (▹◃ inject₁) Γ)) e
inferW {m} Γ (Lam e) | m' , s₁ , τ₁ rewrite +-suc m (count e) = m' , (s₁ , (sub s₁ (inject+ (count e) (fromℕ m))) fork τ₁)
inferW Γ (App e e₁) = {!!}
--inferW {m} {n} Γ (Var x) rewrite (+-right-identity m) = m , (anil , lookup x Γ) --m , anil , lookup x Γ
--inferW {m} Γ (Lam τ t) with (inferW {suc m} ((ι (fromℕ m)) ∷ (vecinject (▹◃ inject₁) Γ)) (terminject (▹◃ inject₁) t))
--... | b = {!!}
--inferW {m} Γ (Lam τ t) | m' , (s₁ , τ₁) = m' , ({!!} , {!!} fork τ₁)
--inferW Γ (App t t₁) = {!!}
