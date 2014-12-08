\agdaIgnore{
\begin{code}
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
open import Library
open import Function
\end{code}
}

\agdaSnippet\PlusRightIdentity{
\begin{code}
+-right-identity : (n : ℕ) → n + 0 ≡ n
+-right-identity zero = refl
+-right-identity (suc n) = cong suc $ +-right-identity n
\end{code}
}

\agdaSnippet\PlusAssoc{
\begin{code}
+-assoc : ∀ m n o → (m + n) + o ≡  m + (n + o)
+-assoc zero n o = refl
+-assoc (suc m) n o = cong suc $ +-assoc m n o
\end{code}}

\agdaSnippet\Cxt{
\begin{code}
Cxt : {m : ℕ} → ℕ → Set
Cxt {m} n = Vec (Type m) n 
\end{code}}

\agdaSnippet\PlusSucc{
\begin{code}
+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)
\end{code}}

\agdaSnippet\VecInject{
\begin{code}
vecinject : {m m' n : ℕ} → (Type m → Type m') → Cxt {m} n -> Cxt {m'} n
vecinject f [] = []
vecinject f (x ∷ v) = (f x) ∷ vecinject f v
\end{code}}

\agdaSnippet\SubstType{
\begin{code}
-- Type に σ を適用させる
substType :{m n : ℕ} → AList m n → Type m → Type n 
substType a = (sub a) ◃
\end{code}}

\agdaSnippet\SubstEnv{
\begin{code}
-- Cxt に σ を適用させる
substenv : {m m' n : ℕ} → AList m m' → Cxt {m} n → Cxt {m'} n 
substenv a [] = []
substenv a (x ∷ c) = substType a x ∷ substenv a c
\end{code}}

\agdaSnippet\LiftAListA{
\begin{code}
liftAList₁ : {m m' : ℕ} → AList m m' → AList (suc m) (suc m')
liftAList₁ {m} {.m}  anil = anil 
liftAList₁ (a asnoc t' / x) = (liftAList₁ a) asnoc ▹◃ inject₁ t' / inject₁ x
\end{code}}

\agdaSnippet\LiftAListB{
\begin{code}
liftAList : {m m' : ℕ} → (n : ℕ) → AList m m' → AList (m + n) (m' + n)
liftAList {m} {.m}  n anil = anil 
liftAList n (a asnoc t' / x) = (liftAList n a) asnoc ▹◃ (inject+ n) t' / inject+ n x
\end{code}}

\agdaSnippet\WellScopedTerm{
\begin{code}
data WellScopedTerm (n : ℕ) : Set where
  Var : Fin n → WellScopedTerm n
  Lam : WellScopedTerm (suc n) → WellScopedTerm n
  App : WellScopedTerm n →
                       WellScopedTerm n → WellScopedTerm n
--  Let : Fin n → WellScopedTerm n →
--        WellScopedTerm n → WellScopedTerm n
\end{code}}

\agdaSnippet\WellTypedTerm{
\begin{code}
data WellTypedTerm {m n : ℕ} (Γ : Cxt n) : Type m → Set where
  Var : (x : Fin n) → WellTypedTerm Γ (lookup x Γ)
  Lam : (σ : Type m) → {t : Type m} → WellTypedTerm (σ ∷ Γ) t
           → WellTypedTerm Γ (σ fork t)
  App : {σ t : Type m} → WellTypedTerm Γ (σ fork t)
           → WellTypedTerm Γ σ → WellTypedTerm Γ t
\end{code}}

\agdaSnippet\UnifyType{
\begin{code}
unify : {m : ℕ} → Type m → Type m → Maybe (∃ (AList m))
unify {m} t1 t2 = mgu {m} t1 t2
\end{code}}


\agdaSnippet\CountType{
\begin{code}
count : (n : ℕ) → (t : WellScopedTerm n) → ℕ
count n (Var x) = zero
count n (Lam t) = suc (count (suc n) t)
count n (App t t₁) = count n t + suc (count n t₁)
\end{code}}

\agdaSnippet\LiftTerm{
\begin{code}
liftterm : {n : ℕ} → (e : WellScopedTerm n) → (m : ℕ) → WellScopedTerm (n + m)
liftterm (Var x) m = Var (inject+ m x)
liftterm (Lam e) m = Lam (liftterm e m)
liftterm (App e e₁) m = App (liftterm e m) (liftterm e₁ m)
--liftterm (Let x e e₁) m = Let (inject+ m x) (liftterm e m) (liftterm e₁ m)
\end{code}}

\agdaSnippet\InferVar{
\begin{code}
inferVar : (n : ℕ) → AList (n + 0) n
inferVar n rewrite (+-right-identity n) = anil
\end{code}}

\agdaSnippet\InferLam{
\begin{code}
-- m + suc n ≡ suc (m + n)
inferLam : {m n m' : ℕ} → (e : WellScopedTerm n) → AList (suc (m + count n e)) m'
         →  AList (m + suc (count n e)) m' 
inferLam {m} {n} {m'} e l rewrite +-suc m (count n e) = l
\end{code}}

\agdaSnippet\InferApp{
\begin{code}
-- +-assoc : ∀ m n o → (m + n) + o ≡  m + (n + o)
inferApp : {m m' n : ℕ} →  (e e₁ : WellScopedTerm n)
           → AList (m + count n e + suc (count n e₁)) (suc (m' + count n e₁))
             → AList (m + (count n e + suc (count n e₁))) (suc (m' + count n e₁))
inferApp {m} {m'} {n} e e₁ l
         rewrite (sym (+-assoc m (count n e) (suc (count n e₁)))) = l
\end{code}}


\agdaSnippet\LiftSigTwo{
\begin{code}
liftσ₂ : {m m' m'' m''' n : ℕ} → (e e₁ : WellScopedTerm n) →  AList (m + count n e) m'
         → AList (m + count n e + suc (count n e₁)) (suc (m' + count n e₁))
liftσ₂ {m} {m'} {m''} {m'''} {n} e e₁ alist rewrite (sym (+-suc m' (count n e₁)))
           = liftAList (suc (count n e₁)) alist
\end{code}}

\agdaSnippet\InferW{
\begin{code}
inferW : {m n : ℕ} →  (Γ : Cxt {m} n) → (e : WellScopedTerm n)
         → Maybe (Σ[ m' ∈ ℕ ] AList (m + count n e) m' × Type m')
inferW {m} Γ (Var x) rewrite (+-right-identity m) =
       just ( m , (anil , lookup x Γ))
inferW {m} Γ (Lam e) with inferW {suc m} (ι (fromℕ m) ∷ (vecinject (▹◃ inject₁) Γ)) e
inferW  {m} {n} Γ (Lam e) | just (m' , s₁ , t₁) rewrite +-suc m (count (suc n) e)
        = just ( m' , (s₁ , (sub s₁ (inject+ (count (suc n) e) (fromℕ m))) fork t₁))
inferW {m} Γ (Lam e) | nothing = nothing
inferW {m} Γ (App e e₁) with inferW {m} Γ e 
inferW {m} Γ (App e e₁) | nothing = nothing 
inferW {m} {n} Γ (App e e₁) | just (m' , σ , t)
           with inferW (substenv σ (vecinject (▹◃ (inject+ (count n e))) Γ)) e₁
inferW {m} {n} Γ (App e e₁) | just (m' , σ , t) | just (m'' , σ₁ , t₁)
           with unify (▹◃ inject₁ ((substType σ₁ (▹◃ (inject+ (count n e₁)) t))))
                      (▹◃ inject₁ t₁ fork ι (fromℕ m''))
inferW {m} {n} Γ (App e e₁) | just (m' , σ , t) | just (m'' , σ₁ , t₁) | just (m''' , σ₂)
           rewrite (sym (+-assoc m (count n e) (suc (count n e₁))))
                  = just (m''' , σ₂ ⊹⊹ ((liftAList₁ σ₁)
                         ⊹⊹  liftσ₂ {m} {m'} {m''} {m'''} {_} e e₁ σ ),
                             (substType σ₂ (ι (fromℕ m''))))
inferW Γ (App e e₁) | just (m' , σ , t) | just (m'' , σ₁ , t₁) | nothing = nothing
inferW Γ (App e e₁) | just (m' , σ , t) | nothing = nothing

\end{code}}

\agdaIgnore{
\begin{code}
--inferW Γ (Let x e e₁) with inferW Γ e
-- inferW let x = e in e₁ =
-- let inferW Γ e = (σ,t) in
-- let inferW (σ Γx ∪ {x : substenv(σ Γ) (t)}) e₁ = (σ₁, t₁) in
-- (σ₁ σ, t₁)
--inferW {m} Γ (Let x e e₁) | just (m' , σ , t) with inferW ((ι (fromℕ m')) ∷ (substenv (liftAList₁ σ) (vecinject (▹◃ inject) Γ))) (liftterm {!!} {!!})
--inferW {m} Γ (Let x e e₁) | just (m' , σ , t) | just (m'' , σ₁ , t₁) = just (m'' , ({!!} , t₁))
--inferW {m} Γ (Let x e e₁) | just (m' , σ , t) | nothing = nothing
--inferW {m} Γ (Let x e e₁) | nothing = nothing
\end{code}}

\agdaSnippet\TestCodes{
\begin{code}
test1 : WellScopedTerm 0
test1 = Lam (Var zero)
infer1 : inferW {0} [] test1
         ≡ just (1 , anil , ι zero fork ι zero)
infer1 = refl

test2 : WellScopedTerm 0
test2 = Lam (Lam (Var zero))
infer2 : inferW {0} [] test2
         ≡ just (2 , anil , ι zero fork (ι (suc zero) fork ι (suc zero)))
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
\end{code}}
