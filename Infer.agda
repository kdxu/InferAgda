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

unify : {m : ℕ} → Type m → Type m → Maybe (∃ (AList m))
unify {m} t1 t2 = mgu {m} t1 t2

count : {n : ℕ} → (t : WellScopedTerm n) → ℕ
count (Var x) = zero
count (Lam t) = suc (count t)
count (App t t₁) = count t + suc (count t₁) 

-- e は最大 n 個の自由変数を持つ項
-- Γは、その n 個の自由変数の型を与える型環境
-- 型環境中の各型は、最大で m 個の型変数を含む
inferW : {m n : ℕ} →  (Γ : Cxt {m} n) → (e : WellScopedTerm n) → Maybe (Σ[ m' ∈ ℕ ] AList (m + count e) m' × Type m')
inferW {m} Γ (Var x) rewrite (+-right-identity m) = just ( m , (anil , lookup x Γ))
inferW {m} Γ (Lam e) with inferW {suc m} (ι (fromℕ m) ∷ (vecinject (▹◃ inject₁) Γ)) e
inferW {m} Γ (Lam e) | just (m' , s₁ , τ₁) rewrite +-suc m (count e) = just ( m' , (s₁ , (sub s₁ (inject+ (count e) (fromℕ m))) fork τ₁))
inferW {m} Γ (Lam e) | nothing = nothing
inferW {m} Γ (App e e₁) with inferW {m} Γ e
inferW {m} Γ (App e e₁) | nothing = nothing
inferW {m} Γ (App e e₁) | just (m' , σ , τ) with inferW {m} Γ e₁
inferW {m} Γ (App e e₁) | just (m' , σ , τ) | just (m'' , σ₁ , τ₁) with unify (sub σ₁ (inject+ (count e₁) {!fromℕ!})) ({!!} fork ι {!fromℕ!})
inferW {m} Γ (App e e₁) | just (m' , σ , τ) | just (m'' , σ₁ , τ₁) | just (m''' , σ₂) = just (m''' , (σ₂ ⊹⊹ (σ₁ ⊹⊹ {!σ!}) , {!!})) ---just (m' , (σ ⊹⊹ ({!σ₂!} ⊹⊹ {!!}) , sub {!σ₂!} (fromℕ m'')))
inferW Γ (App e e₁) | just (m' , σ , τ) | just (m'' , σ₁ , τ₁) | nothing = nothing
inferW Γ (App e e₁) | just (m' , σ , τ) | nothing = nothing

