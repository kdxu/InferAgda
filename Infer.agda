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

{- TODO : Let 多相を入れる -}

+-right-identity : ∀ n → n + 0 ≡ n
+-right-identity zero = refl
+-right-identity (suc n) = cong suc $ +-right-identity n

+-assoc : ∀ m n o → (m + n) + o ≡  m + (n + o)
+-assoc zero n o = refl
+-assoc (suc m) n o = cong suc $ +-assoc m n o

--Termにはwellscopedtermを使うといい．
--TypeにはFUSRのtermが使える．

Cxt : {m : ℕ} → ℕ → Set
Cxt {m} n = Vec (Type m) n -- ここのmをどう持ち歩いてよいか分からない． 

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)


-- Cxt を持ち上げるやつ
vecinject : {m m' n : ℕ} → (Type m → Type m') → Cxt {m} n -> Cxt {m'} n --Vec (Type m) n → Vec (Type m') n
vecinject f [] = []
vecinject f (x ∷ v) = (f x) ∷ vecinject f v

-- AList m n → Type m → Type n
-- Type に σ を適用させるやつ
substtype :{m n : ℕ} → AList m n → Type m → Type n 
substtype a = (sub a) ◃

-- AList m m' → Cxt m n → Cxt m' n 
-- Cxt に σ を適用させるやつ
substenv : {m m' n : ℕ} → AList m m' → Cxt {m} n → Cxt {m'} n 
substenv a [] = []
substenv a (x ∷ c) = substtype a x ∷ substenv a c

liftAList₁ : {m m' : ℕ} → AList m m' → AList (suc m) (suc m')
liftAList₁ {m} {.m}  anil = anil 
liftAList₁ (a asnoc t' / x) = (liftAList₁ a) asnoc ▹◃ inject₁ t' / inject₁ x

liftAList : {m m' : ℕ} → (n : ℕ) → AList m m' → AList (m + n) (m' + n)
liftAList {m} {.m}  n anil = anil 
liftAList n (a asnoc t' / x) = (liftAList n a) asnoc ▹◃ (inject+ n) t' / inject+ n x

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

liftσ₂ : {m m' m'' m''' n : ℕ} → (e e₁ : WellScopedTerm n) →  AList (m + count e) m'  → AList (m + count e + suc (count e₁)) (suc (m' + count e₁))
liftσ₂ {m} {m'} {m''} {m'''} {n} e e₁ alist rewrite (sym (+-suc m' (count e₁))) = liftAList (suc (count e₁)) alist

-- e は最大 n 個の自由変数を持つ項
-- Γは、その n 個の自由変数の型を与える型環境
-- 型環境中の各型は、最大で m 個の型変数を含む
inferW : {m n : ℕ} →  (Γ : Cxt {m} n) → (e : WellScopedTerm n) → Maybe (Σ[ m' ∈ ℕ ] AList (m + count e) m' × Type m')
inferW {m} Γ (Var x) rewrite (+-right-identity m) = just ( m , (anil , lookup x Γ))
inferW {m} Γ (Lam e) with inferW {suc m} (ι (fromℕ m) ∷ (vecinject (▹◃ inject₁) Γ)) e
inferW {m} Γ (Lam e) | just (m' , s₁ , τ₁) rewrite +-suc m (count e) = just ( m' , (s₁ , (sub s₁ (inject+ (count e) (fromℕ m))) fork τ₁))
inferW {m} Γ (Lam e) | nothing = nothing
inferW {m} Γ (App e e₁) with inferW {m} Γ e -- App の型推論，infer m Γ e の結果で場合分けする
inferW {m} Γ (App e e₁) | nothing = nothing --σ  : AList (m + count e) m'
inferW {m} Γ (App e e₁) | just (m' , σ , τ) with inferW (substenv σ (vecinject (▹◃ (inject+ (count e))) Γ)) e₁ -- m',m'' : e,e₁ の中の型変数の数 (たかだかm+count e個) 
inferW {m} Γ (App e e₁) | just (m' , σ , τ) | just (m'' , σ₁ , τ₁) with unify (▹◃ inject₁ ((substtype σ₁ (▹◃ (inject+ (count e₁)) τ))))  (▹◃ inject₁ τ₁ fork ι (fromℕ m''))
inferW {m} Γ (App e e₁) | just (m' , σ , τ) | just (m'' , σ₁ , τ₁) | just (m''' , σ₂)  rewrite (sym (+-assoc m (count e) (suc (count e₁)))) = just (m''' , σ₂ ⊹⊹ ((liftAList₁ σ₁) ⊹⊹  liftσ₂ {m} {m'} {m''} {m'''} {_} e e₁ σ ), (substtype σ₂ (ι (fromℕ m''))))
inferW Γ (App e e₁) | just (m' , σ , τ) | just (m'' , σ₁ , τ₁) | nothing = nothing
inferW Γ (App e e₁) | just (m' , σ , τ) | nothing = nothing

test1 : WellScopedTerm 0
test1 = Lam (Var zero)
infer1 : inferW {0} [] test1 ≡ just (1 , anil , ι zero fork ι zero)
infer1 = refl

test2 : WellScopedTerm 0
test2 = Lam (Lam (Var zero))
infer2 : inferW {0} [] test2 ≡ just (2 , anil , ι zero fork (ι (suc zero) fork ι (suc zero)))
infer2 = refl 

test3 : WellScopedTerm 0
test3 = Lam (Lam (App (Var zero) (Var (suc zero))))
infer3 : inferW {0} [] test3  ≡ just
  (2 ,
  anil asnoc ι zero fork ι (suc zero) / suc zero ,
  ι zero fork ((ι zero fork ι (suc zero)) fork ι (suc zero)))
infer3 = refl

test4 : WellScopedTerm 0
test4 = Lam (App (Var zero) (Var zero))
infer4 : inferW {0} [] test4 ≡ nothing
infer4 = refl




