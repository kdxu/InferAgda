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
--import Level

{-
TODO : Let 多相を入れる 
       推論が正しいことを証明する
         -->部分評価器の正当性
  -}

+-right-identity : (n : ℕ) → n + 0 ≡ n
+-right-identity zero = refl
+-right-identity (suc n) = cong suc $ +-right-identity n

+-assoc : ∀ m n o → (m + n) + o ≡  m + (n + o)
+-assoc zero n o = refl
+-assoc (suc m) n o = cong suc $ +-assoc m n o

-- 型環境
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
--  Let : Fin n → WellScopedTerm n → WellScopedTerm n → WellScopedTerm n 

data WellTypedTerm {m n : ℕ} (Γ : Cxt n) : Type m → Set where
  Var : (x : Fin n) → WellTypedTerm Γ (lookup x Γ)
  Lam : (σ : Type m) → {t : Type m} → WellTypedTerm (σ ∷ Γ) t → WellTypedTerm Γ (σ fork t)
  App : {σ t : Type m} → WellTypedTerm Γ (σ fork t) → WellTypedTerm Γ σ → WellTypedTerm Γ t

unify : {m : ℕ} → Type m → Type m → Maybe (∃ (AList m))
unify {m} t1 t2 = mgu {m} t1 t2

count : (n : ℕ) → (t : WellScopedTerm n) → ℕ
count n (Var x) = zero
count n (Lam t) = suc (count (suc n) t)
count n (App t t₁) = count n t + suc (count n t₁) 
--count (Let x e e₁) = (count e₁) -- ? 

liftterm : {n : ℕ} → (e : WellScopedTerm n) → (m : ℕ) → WellScopedTerm (n + m)
liftterm (Var x) m = Var (inject+ m x)
liftterm (Lam e) m = Lam (liftterm e m)
liftterm (App e e₁) m = App (liftterm e m) (liftterm e₁ m)
--liftterm (Let x e e₁) m = Let (inject+ m x) (liftterm e m) (liftterm e₁ m)

inferVar : (n : ℕ) → AList (n + 0) n
inferVar n rewrite (+-right-identity n) = anil

-- m + suc n ≡ suc (m + n)
inferLam : {m n m' : ℕ} → (e : WellScopedTerm n) → AList (suc (m + count n e)) m' →  AList (m + suc (count n e)) m' 
inferLam {m} {n} {m'} e l rewrite +-suc m (count n e) = l

liftσ₂ : {m m' m'' m''' n : ℕ} → (e e₁ : WellScopedTerm n) →  AList (m + count n e) m'  → AList (m + count n e + suc (count n e₁)) (suc (m' + count n e₁))
liftσ₂ {m} {m'} {m''} {m'''} {n} e e₁ alist rewrite (sym (+-suc m' (count n e₁))) = liftAList (suc (count n e₁)) alist

-- +-assoc : ∀ m n o → (m + n) + o ≡  m + (n + o)
inferApp : {m m' n : ℕ} →  (e e₁ : WellScopedTerm n) → AList (m + count n e + suc (count n e₁)) (suc (m' + count n e₁)) → AList (m + (count n e + suc (count n e₁))) (suc (m' + count n e₁))
inferApp {m} {m'} {n} e e₁ l rewrite (sym (+-assoc m (count n e) (suc (count n e₁)))) = l

{-
-- e は最大 n 個の自由変数を持つ項
-- Γは、その n 個の自由変数の型を与える型環境
-- 型環境中の各型は、最大で m 個の型変数を含む
inferW' : (n : ℕ) → (m : ℕ) →  (Γ : Cxt {m} n) → (e : WellScopedTerm n) → Maybe (Σ[ m' ∈ ℕ ] Σ[ σ ∈ AList (m + (count n e)) m' ] Σ[ t ∈ Type m' ] WellTypedTerm (substenv {m + count n e} {m'} {n} σ (vecinject (▹◃ (inject+ (count n e))) Γ)) t)
--inferW' n m Γ (Var x)  = just ({!!} , (anil , {!!}))
--inferW' n m Γ (Var x) with (count n (Var x)) + m
--... | a = just (m , ({!anil!} , {!!}))
inferW' n m Γ (Var x) = just (m , (inferVar m , ((lookup x (substenv (inferVar m) (vecinject (▹◃ (inject+ 0)) Γ))) , (Var x))))
inferW' n m Γ (Lam e) with inferW' (suc n) (suc m) (ι (fromℕ m) ∷ (vecinject (▹◃ inject₁) Γ)) e
inferW' n m  Γ (Lam e) | just (m' , s₁ , t₁ , e') = just (m' , (inferLam {m} e s₁ , (sub s₁ (inject+ (count (suc n) e) (fromℕ m))) fork t₁ , Lam (sub s₁ (inject+ (count (suc n) e) (fromℕ m))) {!!})) --TODO: rewrite +-suc m (count e)
inferW' n m Γ (Lam e) | nothing = nothing
inferW' n m Γ (App e e₁) with inferW' n m Γ e
inferW' n m Γ (App e e₁) | just (m' , σ , t , e') with inferW' n m' (substenv σ (vecinject (▹◃ (inject+ (count n e))) Γ)) e₁
inferW' n m Γ (App e e₁) | just (m' , σ , t , e') | just (m'' , σ₁ , t₁ , e'') with unify (▹◃ inject₁ ((substtype σ₁ (▹◃ (inject+ (count n e₁)) t))))  (▹◃ inject₁ t₁ fork ι (fromℕ m''))
inferW' n m Γ (App e e₁) | just (m' , σ , t , e') | just (m'' , σ₁ , t₁ , e'') | just (m''' , σ₂)  = just (m''' , (σ₂ ⊹⊹ ((liftAList₁ σ₁) ⊹⊹  inferApp {m} {m'} {_} e e₁ (liftσ₂ {m} {m'} {m'' } {m'''} e e₁ σ)) , ((substtype σ₂ (ι (fromℕ m''))) , App {!e'!} {!e''!}))) -- TODO :  rewrite (sym (+-assoc m (count e) (suc (count e₁))))
inferW' n m Γ (App e e₁) | just (m' , σ , t , e') | just (m'' , σ₁ , t₁ , e'') | nothing = nothing
inferW' n m Γ (App e e₁) | just (m' , σ , t , e') | nothing = nothing
inferW' n m Γ (App e e₁) | nothing = nothing
-}

-- inferWを論文で読める格好にする 
-- iota,fork等を見られる格好にする
-- asnoc :

inferW : {m n : ℕ} →  (Γ : Cxt {m} n) → (e : WellScopedTerm n) → Maybe (Σ[ m' ∈ ℕ ] AList (m + count n e) m' × Type m')
inferW {m} Γ (Var x) rewrite (+-right-identity m) = just ( m , (anil , lookup x Γ))
inferW {m} Γ (Lam e) with inferW {suc m} (ι (fromℕ m) ∷ (vecinject (▹◃ inject₁) Γ)) e
inferW  {m} {n} Γ (Lam e) | just (m' , s₁ , t₁) rewrite +-suc m (count (suc n) e) = just ( m' , (s₁ , (sub s₁ (inject+ (count (suc n) e) (fromℕ m))) fork t₁))
inferW {m} Γ (Lam e) | nothing = nothing
inferW {m} Γ (App e e₁) with inferW {m} Γ e -- App の型推論，infer m Γ e の結果で場合分けする
inferW {m} Γ (App e e₁) | nothing = nothing --σ  : AList (m + count e) m'
inferW {m} {n} Γ (App e e₁) | just (m' , σ , t) with inferW (substenv σ (vecinject (▹◃ (inject+ (count n e))) Γ)) e₁ -- m',m'' : e,e₁ の中の型変数の数 (たかだかm+count e個) 
inferW {m} {n} Γ (App e e₁) | just (m' , σ , t) | just (m'' , σ₁ , t₁) with unify (▹◃ inject₁ ((substtype σ₁ (▹◃ (inject+ (count n e₁)) t))))  (▹◃ inject₁ t₁ fork ι (fromℕ m''))
inferW {m} {n} Γ (App e e₁) | just (m' , σ , t) | just (m'' , σ₁ , t₁) | just (m''' , σ₂)  rewrite (sym (+-assoc m (count n e) (suc (count n e₁)))) = just (m''' , σ₂ ⊹⊹ ((liftAList₁ σ₁) ⊹⊹  liftσ₂ {m} {m'} {m''} {m'''} {_} e e₁ σ ), (substtype σ₂ (ι (fromℕ m''))))
inferW Γ (App e e₁) | just (m' , σ , t) | just (m'' , σ₁ , t₁) | nothing = nothing
inferW Γ (App e e₁) | just (m' , σ , t) | nothing = nothing
--inferW Γ (Let x e e₁) with inferW Γ e
-- inferW let x = e in e₁ =
-- let inferW Γ e = (σ,t) in
-- let inferW (σ Γx ∪ {x : substenv(σ Γ) (t)}) e₁ = (σ₁, t₁) in
-- (σ₁ σ, t₁)
--inferW {m} Γ (Let x e e₁) | just (m' , σ , t) with inferW ((ι (fromℕ m')) ∷ (substenv (liftAList₁ σ) (vecinject (▹◃ inject) Γ))) (liftterm {!!} {!!})
--inferW {m} Γ (Let x e e₁) | just (m' , σ , t) | just (m'' , σ₁ , t₁) = just (m'' , ({!!} , t₁))
--inferW {m} Γ (Let x e e₁) | just (m' , σ , t) | nothing = nothing
--inferW {m} Γ (Let x e e₁) | nothing = nothing



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

