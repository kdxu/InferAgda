\agdaIgnore{
\begin{code}
module lib where
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning 
open import Data.Nat
open import Data.Product
open import Data.Empty
open import Data.Fin
open import Data.Sum
open import Data.Bool
open import Data.Maybe
open import Data.List
import Level
\end{code}}

\agdaSnippet\LeftF{
\begin{code}
lf : {S T : Set} → (f : S → T) → (S → Maybe T)
lf f = λ x → just (f x)
\end{code}}

\agdaSnippet\RightF{
\begin{code}
rf : {S T : Set} → (f : S → Maybe T) → (Maybe S → Maybe T)
rf f nothing = nothing
rf f (just x) = f x
\end{code}}

\agdaSnippet\LRF{
\begin{code}
lrf :{S T : Set} → (f : S → T) → (Maybe S → Maybe T)
lrf f = rf (lf f)
_∘_ : {A B C : Set} → (f : B → C) → (g : A → B) → (A → C)
f ∘ g = λ x → f (g x)
\end{code}}

\agdaSnippet\LRF2{
\begin{code}
lf2 : {R S T : Set} → (f : R → S → T) → (R → S → Maybe T)
lf2 f = λ x x₁ → just (f x x₁)

rf2 : {R S T : Set} → (f : R → S → Maybe T) → (R → Maybe S → Maybe T)
rf2 f x nothing = nothing
rf2 f x (just x₁) = f x x₁

cf2 : {R S T : Set} → (f : R → Maybe S → Maybe T) → (Maybe R → Maybe S → Maybe T)
cf2 f nothing nothing = nothing
cf2 f nothing (just x) = nothing
cf2 f (just x) nothing = f x nothing
cf2 f (just x) (just x₁) = f x (just x₁)

lrf2 : {R S T : Set} → (f : R → S → T) → (Maybe R → Maybe S → Maybe T)
lrf2 f = cf2 (rf2 (lf2 f))
\end{code}}

record Top : Set where

data Bot : Set where

empty : Fin zero → Set
empty x = Top

Fin' : ℕ →  Set
Fin' zero = Bot
Fin' (suc n) = Maybe (Fin' n)

data Type (n : ℕ) : Set where
   ι : (x : Fin n) → Type n -- 変数 (de bruijn index) 
   leaf : Type n -- base case の型
   _fork_ : (s t : Type n) → Type n -- arrow 型
--   ∀regs : reg n → Type n

--data Scheme (n : ℕ) : Set where
--   τ : Type n → scheme n
--   ατ : (a : Fin (Data.Nat._+_ n 1)) → (scheme (Data.Nat._+_ n 1)) → scheme n


▹ : {n m : ℕ} → (r : Fin m → Fin n) → (Fin m → Type n)
▹ r = ι ∘ r

_◃_ : {n m : ℕ} → (f : Fin m → Type n) → (Type m → Type n)
_◃_ f (ι x) = f x
_◃_ f leaf = leaf
_◃_ f (s fork t) = (f ◃ s) fork (f ◃ t) 

_◃ : {n m : ℕ} → (f : Fin m → Type n) → (Type m → Type n)
f ◃ = λ x → f ◃ x

▹◃ :  {n m : ℕ} → (f : Fin m → Fin n) → (Type m → Type n)
▹◃ f = (▹ f) ◃

_≐_ : {n m : ℕ} → (f g : Fin m → Type n) → Set
_≐_ {n} {m} f g = (x : Fin m) → f x ≡ g x

_◇_ : {m n l : ℕ} → (f : Fin m → Type n) → (g : Fin l → Type m) → (Fin l → Type n)
f ◇ g = (f ◃) ∘ g

-- (ι s) fork (ι t) ⇒ ι (s fork t) = s fork t
-- ι s = s
-- ι t = t
-- p9

thin : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)  -- thin <-> thick
thin {n} zero y = suc y
thin {suc n} (suc x) zero = zero
thin {suc n} (suc x) (suc y) = suc (thin x y)


thick : {n : ℕ} → (x y : Fin (suc n)) → Maybe (Fin n)
thick {n} zero zero = nothing
thick {n} zero (suc y) = just y
thick {zero} (suc ()) zero
thick {suc n} (suc x) zero = just zero
thick {zero} (suc ()) (suc y)
thick {suc n} (suc x) (suc y) = lrf suc (thick {n} x y)

check : {n : ℕ} → Fin (suc n) → Type (suc n) → Maybe (Type n)
check x (ι y) = lrf ι (thick x y)
check x leaf = just leaf
check x (s fork t) = lrf2 _fork_ (check x s) (check x t)

_for_ : {n : ℕ} → (t' : Type n) → (x : Fin (suc n)) → (Fin (suc n) → Type n)
_for_ t' x y with thick x y
_for_ t' x y | nothing = t'
_for_ t' x y | just y' = ι y'


data AList : ℕ → ℕ → Set where
  anil : {m : ℕ} → AList m m
  _asnoc_/_ : {m : ℕ} {n : ℕ} → (σ : AList m n) → (t' : Type m) → (x : Fin (suc m)) → AList (suc m) n
--asnoc : consの逆 []::2 ::3 :: ...
_asnoc'_/_ : {m : ℕ} → (a : ∃ (AList m)) → (t' : Type m) → (x : Fin (suc m)) → ∃ (AList (suc m))
( s , t ) asnoc' t' / x = ( s , t asnoc t' / x )

--_◇_ : {m n l : ℕ} → (f : Fin m → Type n) → (g : Fin l → Type m) → (Fin l → Type n)
sub : {m n : ℕ} → (σ : AList m n) → Fin m → Type n
sub anil = ι --m≡nなら何もしない
sub (σ asnoc t' / x) = (sub σ) ◇ (t' for x)

_⊹⊹_ : {l m n : ℕ} → (ρ : AList m n) → (σ : AList l m) →  AList l n
ρ ⊹⊹ anil = ρ
ρ ⊹⊹ (alist asnoc t / x) = (ρ ⊹⊹ alist) asnoc t / x


data AList' : ℕ →  Set where
  anil' : {m : ℕ} → AList' m
  _acons'_/_ : {m : ℕ} → (σ : AList' m) → (t' : Type m) → (x : Fin (suc m)) → AList' (suc m)

targ : {m : ℕ} → (σ : AList' m) → ℕ
targ {m} anil' = m
targ (a acons' t' / x) = targ a

_⊹⊹'_ : {m : ℕ} → (σ : AList' m) → (ρ : AList' (targ σ)) → AList' m
_⊹⊹'_ anil' ρ = ρ
_⊹⊹'_ (alist acons' t' / x)  ρ = (_⊹⊹'_ alist ρ) acons' t' / x


sub' : {m : ℕ} →  (σ : AList' m) → (Fin m → Type (targ σ))
sub' anil' = ι
sub' (σ acons' t' / x) =  (sub' σ) ◇ (t' for x)


-- p14

flexFlex : {m : ℕ} → (x y : Fin m) → (∃ (AList m))
flexFlex {suc m} x y with thick x y 
flexFlex {suc m} x y | nothing = ( (suc m) , anil )
flexFlex {suc m} x y | just y' = ( m , anil asnoc (ι y') / x )
flexFlex {zero} () y

flexRigid : {m : ℕ} → (x : Fin m) → (t : Type m) → Maybe (∃ (AList m))
flexRigid {zero} () t
flexRigid {suc m} x t with check x t
flexRigid {suc m} x t | nothing = nothing
flexRigid {suc m} x t | just t' = just ( m , (anil asnoc t' / x) )

amgu : {m : ℕ} → (s t : Type m) → (acc : ∃ (AList m)) →  Maybe (∃ (AList m))
amgu {suc m} s t ( n , σ asnoc r / z ) = lrf (λ σ₁ → σ₁ asnoc' r / z) (amgu {m} ((r for z) ◃ s) ((r for z) ◃ t) ( n , σ ))
amgu leaf leaf acc = just acc
amgu leaf (t fork t₁) acc = nothing
amgu (ι x) (ι x₁) ( s , anil ) = just (flexFlex x x₁)
amgu t (ι x) acc = flexRigid x t
amgu (ι x) t acc = flexRigid x t
amgu (s fork s₁) leaf acc = nothing
amgu {m} (s fork s₁) (t fork t₁) acc = rf (amgu {m} s₁ t₁) (amgu {m} s t acc)

mgu : {m : ℕ} → (s t : Type m) → Maybe (∃ (AList m))
mgu {m} s t = amgu {m} s t ( m , anil )

-- test

t1 : Type 4
t1 = (ι zero) fork (ι zero)

t2 : Type 4
t2 = ((ι (suc zero)) fork (ι (suc (suc zero)))) fork (ι (suc (suc (suc zero))))

u12 : Maybe (∃ (AList 4))
u12 = (mgu t1 t2)

t3 : Type 4
t3 = ((ι zero) fork (ι (suc (suc zero)))) fork (ι (suc (suc (suc zero))))

u13 : Maybe (∃ (AList 4))
u13 = (mgu t1 t3)

\end{code}}
