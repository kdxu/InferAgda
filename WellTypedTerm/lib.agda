module lib where

open import Data.Nat
open import Data.Product
open import Data.Fin
open import Data.Product
open import Data.Empty
open import Data.Sum
open import Data.Maybe
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
-- open import Relation.Binary.HeterogeneousEquality

---------------------------------------------------------------

-- Type n : 最大で n 個の型変数を持つ型を表す型。
data Type (n : ℕ) : Set where
  TVar : (x : Fin n) → Type n -- 型変数 (de Bruijn index) 
  TInt : Type n -- base case の型
  _⇒_ : (s t : Type n) → Type n -- arrow 型



-- f ◃ t : 型 t 中の型変数部分に f を施した型を返す
_◃_ : {n m : ℕ} → (f : Fin m → Type n) → (Type m → Type n)
_◃_ f (TVar x) = f x
_◃_ f TInt = TInt
_◃_ f (s ⇒ t) = (f ◃ s) ⇒ (f ◃ t) 

-- f ◃ t : 型 t 中の型変数部分に f を施した型を返す
_◃ : {n m : ℕ} → (f : Fin m → Type n) → (Type m → Type n)
f ◃ = λ x → f ◃ x

-- 型の中の全ての型変数に f を施す（Infer.agda でのみ使う）
▹◃ :  {n m : ℕ} → (f : Fin m → Fin n) → (Type m → Type n)
▹◃ f = (TVar ∘ f) ◃

-- 全ての型変数に TVar を付け直すだけなら変化なし（Infer.agda でのみ使う）
TVarId : {m : ℕ} → (t : Type m) → TVar ◃ t ≡ t
TVarId (TVar x) = refl
TVarId TInt = refl
TVarId (t1 ⇒ t2) = cong₂ _⇒_ (TVarId t1) (TVarId t2)

-- thin x y : 変数 y を x の位置で「薄める」
-- （x 未満の変数はそのまま。x 以上の変数は +1 される。
--   thin の結果が x になることはない。）
thin : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)  -- thin <-> thick
thin {n} zero y = suc y
thin {suc n} (suc x) zero = zero
thin {suc n} (suc x) (suc y) = suc (thin x y)

-- thick x y : 変数 y を x の位置で「濃縮する」
-- （x 未満の変数はそのまま。x より大きい変数は -1 される。
--   x と y が同じ場合は濃縮できないので nothing が返る。）
thick : {n : ℕ} → (x y : Fin (suc n)) → Maybe (Fin n)
thick {n} zero zero = nothing -- x = y だった
thick {n} zero (suc y) = just y -- 濃縮する
thick {zero} (suc ()) zero
thick {suc n} (suc x) zero = just zero -- x 未満なのでそのまま
thick {zero} (suc ()) (suc y)
thick {suc n} (suc x) (suc y) with thick {n} x y
... | just x' = just (suc x')
... | nothing = nothing -- x = y だった

thickxx≡nothing : ∀ {n} (x : Fin (suc n)) → thick x x ≡ nothing
thickxx≡nothing zero = refl
thickxx≡nothing {zero} (suc ())
thickxx≡nothing {suc n} (suc x) with thickxx≡nothing x
... | a rewrite a = refl

thickxy-x≡y : ∀ {n} (x y : Fin (suc n)) → thick x y ≡ nothing → x ≡ y
thickxy-x≡y zero zero eq = refl
thickxy-x≡y zero (suc y) ()
thickxy-x≡y {zero} (suc ()) zero eq
thickxy-x≡y {suc n} (suc x) zero ()
thickxy-x≡y {zero} (suc ()) (suc y) eq
thickxy-x≡y {suc n} (suc x) (suc y) eq with thick x y | inspect (thick x) y
thickxy-x≡y {suc n} (suc x) (suc y) () | just x' | [ eq' ]
... | nothing | [ eq' ] = cong suc (thickxy-x≡y x y eq')

-- check x t : x 番の型変数が型 t の中に現れるかをチェックする。
-- 現れなければ、型 t を x で thick できるはずなので、それを返す。
-- 現れたら、nothing を返す。
check : {n : ℕ} → Fin (suc n) → Type (suc n) → Maybe (Type n)
check x (TVar y) with thick x y
... | just y' = just (TVar y')
... | nothing = nothing -- x が現れた（x = y だった）
check x TInt = just TInt
check x (s ⇒ t) with check x s | check x t
... | just s' | just t' = just (s' ⇒ t')
... | just s' | nothing = nothing
... | nothing | just t' = nothing
... | nothing | nothing = nothing

checkInvArrow : ∀ {n : ℕ} (x : Fin (suc n)) (t1 t2 : Type (suc n)) {t' : Type n} →
                check x (t1 ⇒ t2) ≡ just t' → 
                Σ[ t1' ∈ Type n ] Σ[ t2' ∈ Type n ]
                (t' ≡ t1' ⇒ t2') × (check x t1 ≡ just t1') × (check x t2 ‌≡ just t2')
checkInvArrow x t1 t2 eq with check x t1 | check x t2
checkInvArrow x t1 t2 refl | just t1' | just t2' = (t1' , t2' , refl , refl , refl)
checkInvArrow x t1 t2 () | just t1' | nothing
checkInvArrow x t1 t2 () | nothing | just t2'
checkInvArrow x t1 t2 () | nothing | nothing

checkInvVar : ∀ {n : ℕ} (x y : Fin (suc n)) {t' : Type n} →
                check x (TVar y) ≡ just t' → 
                Σ[ y' ∈ Fin n ] 
                (t' ≡ TVar y') × (thick x y ≡ just y') 
checkInvVar x y eq with thick x y 
checkInvVar x y refl | just x₁ = x₁ , (refl , refl)
checkInvVar x y () | nothing

-- t' for x : x 番の型変数を型 t' に unify するような unifier を返す。
_for_ : {n : ℕ} → (t' : Type n) → (x : Fin (suc n)) → Fin (suc n) → Type n
_for_ t' x y with thick x y
... | just y' = TVar y'
... | nothing = t'

-- AList m n : m 個の型変数を持つ型を n 個の型変数を持つ型にする代入
data AList : ℕ → ℕ → Set where
  anil : {m : ℕ} → AList m m -- 何もしない代入
  _asnoc_/_ : {m : ℕ} {n : ℕ} → (σ : AList m n) → (t' : Type m) →
              (x : Fin (suc m)) → AList (suc m) n
          -- x を t' にした上で、さらにσを行う代入

-- 型変数に代入σを施す（Infer.agda でのみ使う）
sub : {m n : ℕ} → (σ : AList m n) → Fin m → Type n
sub anil = TVar
sub (σ asnoc t' / x) = (sub σ) ◇ (t' for x)
  where _◇_ : {m n l : ℕ} → (f : Fin m → Type n) → (g : Fin l → Type m) → (Fin l → Type n)
        f ◇ g = (f ◃) ∘ g

-- ふたつの代入をくっつける（Infer.agda でのみ使う）
_⊹⊹_ : {l m n : ℕ} → (ρ : AList m n) → (σ : AList l m) →  AList l n
ρ ⊹⊹ anil = ρ
ρ ⊹⊹ (alist asnoc t / x) = (ρ ⊹⊹ alist) asnoc t / x

-- 型変数 x と y を unify する代入を返す 
flexFlex : {m : ℕ} → (x y : Fin m) → Σ[ n ∈ ℕ ] AList m n
flexFlex {zero} () y
flexFlex {suc m} x y with thick x y 
... | nothing = (suc m , anil) -- x = y だった。代入の必要なし
... | just y' = (m , anil asnoc (TVar y') / x) -- TVar y' for x を返す

-- 型変数 x と型 t を unify する代入を返す
-- x が t に現れていたら nothing を返す
flexRigid : {m : ℕ} → (x : Fin m) → (t : Type m) →
                Maybe (Σ[ n ∈ ℕ ] AList m n)
flexRigid {zero} () t
flexRigid {suc m} x t with check x t
... | nothing = nothing -- x が t に現れていた
... | just t' = just (m , anil asnoc t' / x) -- t' for x を返す

-- 型 s と t（に acc をかけたもの）を unify する代入を返す
amgu : {m : ℕ} → (s t : Type m) → (acc : Σ[ n ∈ ℕ ] AList m n) →
                Maybe (Σ[ n ∈ ℕ ] AList m n)
amgu TInt     TInt     acc        = just acc
amgu TInt     (t ⇒ t₁) acc        = nothing
amgu (s ⇒ s₁) TInt     acc        = nothing
amgu (s ⇒ s₁) (t ⇒ t₁) acc        with amgu s t acc
...                               | just acc' = amgu s₁ t₁ acc'
...                               | nothing = nothing
amgu (TVar x) (TVar y) (s , anil) = just (flexFlex x y)
amgu (TVar x) t        (s , anil) = flexRigid x t
amgu t        (TVar x) (s , anil) = flexRigid x t
amgu {suc m} s t (n , σ asnoc r / z)
  with amgu {m} ((r for z) ◃ s) ((r for z) ◃ t) (n , σ)
... | just (n' , σ') = just (n' , σ' asnoc r / z)
... | nothing = nothing

-- 型 s と t を unify する代入を返す
mgu : {m : ℕ} → (s t : Type m) → Maybe (Σ[ n ∈ ℕ ] AList m n)
mgu {m} s t = amgu {m} s t (m , anil)

-- test

t1 : Type 4
t1 = (TVar zero) ⇒ (TVar zero)

t2 : Type 4
t2 = ((TVar (suc zero)) ⇒ (TVar (suc (suc zero)))) ⇒ (TVar (suc (suc (suc zero))))

u12 : Maybe (∃ (AList 4))
u12 = (mgu t1 t2)

t3 : Type 4
t3 = ((TVar zero) ⇒ (TVar (suc (suc zero)))) ⇒ (TVar (suc (suc (suc zero))))

u13 : Maybe (∃ (AList 4))
u13 = (mgu t1 t3)

-- substType σ t : t に σ を適用した型を返す
substType : {m m' : ℕ} → AList m m' → Type m → Type m' 
substType σ t = sub σ ◃ t

--「σ' は σ の拡張になっている」という命題
_extends_ : ∀ {m} (σ' : Σ[ n' ∈ ℕ ] AList m n') (σ : Σ[ n ∈ ℕ ] AList m n) → Set
_extends_ {m} (n' , σ') (n , σ) =
  ∀ (s t : Type m) → substType σ s ≡ substType σ t → substType σ' s ≡ substType σ' t

-- 自分自身は自分自身の拡張になっている
σextendsσ : ∀ {m} (σ : Σ[ n ∈ ℕ ] AList m n) → σ extends σ
σextendsσ σ s t eq = eq

-- 任意のσは anil の拡張になっている
σextendsNil : ∀ {m} (σ : Σ[ n ∈ ℕ ] AList m n) → σ extends (m , anil)
σextendsNil σ s t eq rewrite TVarId s | TVarId t = cong (substType (proj₂ σ)) eq

-- 型変数 x と y を unify する代入を返す 
flexFlex2 : {m : ℕ} → (x y : Fin m) → ( Σ[ σ ∈ Σ[ n ∈ ℕ ] AList m n ]
            substType (proj₂ σ) (TVar x) ≡ substType (proj₂ σ) (TVar y))
flexFlex2 {zero} () y
flexFlex2 {suc m} x y with thick x y | inspect (thick x) y
... | nothing | [ thickxy≡nothing ] =
  ((suc m , anil) , cong TVar (thickxy-x≡y x y thickxy≡nothing))  -- x = y だった。代入の必要なし
... | just y' | [ thickxy≡justy' ] =
  ((m , anil asnoc TVar y' / x) , cong (TVar ◃) eq)  -- TVar y' for x を返す
  where eq : (TVar y' for x) ◃ (TVar x) ≡ (TVar y' for x) ◃ (TVar y)
        eq rewrite thickxx≡nothing x | thickxy≡justy' = refl
        

forTVarLem : {m : ℕ} → (x : Fin (suc m)) → ∀(t : Type  m) → t ≡ (t for x) ◃ (TVar x)
forTVarLem x t rewrite thickxx≡nothing x  = refl

flexRigidLem : {m : ℕ} → {t' : Type m} → ∀{t'' : Type m} → (x : Fin (suc m)) → (t : Type (suc m)) → check x t ≡ just t' →  TVar ◃ ((t' for x) ◃ (TVar x)) ≡ (λ y → TVar ◃ (t'' for x) y) ◃ t

flexRigidLem x (TVar x₁) p with check x (TVar x₁) | inspect (check x) (TVar x₁)
flexRigidLem x (TVar x₁) refl | just x₂ | [ eq ] with checkInvVar x x₁ eq
flexRigidLem x (TVar x₁) refl | just .(TVar x₂) | [ eq ] | x₂ , refl , proj₃ rewrite proj₃ |  thickxx≡nothing x = refl
flexRigidLem x (TVar x₁) () | nothing | [ eq ]
flexRigidLem x TInt p with check x TInt | inspect (check x) TInt
flexRigidLem x TInt p | just (TVar x₁) | [ () ]
flexRigidLem x TInt refl | just TInt | [ refl ] rewrite thickxx≡nothing x = refl
flexRigidLem x TInt p | just (x₁ ⇒ x₂) | [ () ]
flexRigidLem x TInt () | nothing | [ eq ] 
flexRigidLem x (t ⇒ t₁) p with check x (t ⇒ t₁)  | inspect (check x) (t ⇒ t₁)
flexRigidLem x (t ⇒ t₁) refl | just (TVar x₁) | [ eq ] with checkInvArrow x t t₁ eq
... | (t1' , t2' , () , b , c)
flexRigidLem x (t ⇒ t₁) p | just TInt | [ eq ] with checkInvArrow x t t₁ eq
... | (t1' , t2' , () , b , c)
flexRigidLem x (t ⇒ t₁) refl | just (x₁ ⇒ x₂) | [ eq ] with checkInvArrow x t t₁ eq
flexRigidLem {t'' = t''} x (t ⇒ t₁) refl | just (x₁ ⇒ x₂) | [ eq ] | .x₁ , .x₂ , refl , b , c rewrite thickxx≡nothing x = 
  cong₂ _⇒_ p q -- (flexRigidLem  t' t b) {!!}
  where p : TVar ◃ x₁ ≡ (λ y → TVar ◃ (t'' for x) y) ◃ t
        p = begin
              TVar ◃ x₁
            ≡⟨  cong (λ x₃ → TVar ◃ x₃) (forTVarLem x x₁) ⟩
              TVar ◃ ((x₁ for x) ◃ (TVar x))
            ≡⟨ flexRigidLem x t b ⟩
              (λ y → TVar ◃ (t'' for x) y) ◃ t
            ∎
        q : TVar ◃ x₂ ≡ (λ y → TVar ◃ (t'' for x) y) ◃ t₁
        q = begin
              TVar ◃ x₂
            ≡⟨  cong (λ x₃ → TVar ◃ x₃) (forTVarLem x x₂) ⟩
              TVar ◃ ((x₂ for x) ◃ (TVar x))
            ≡⟨ flexRigidLem x t₁ c ⟩
              (λ y → TVar ◃ (t'' for x) y) ◃ t₁
            ∎
--  cong₂ _⇒_ (flexRigidLem  t' t b) {!!}
--Goal: x₁ ⇒ x₂ ≡
--      ((λ y → TVar ◃ ((.t'' for x) y | thick x y)) ◃ t) ⇒
--      ((λ y → TVar ◃ ((.t'' for x) y | thick x y)) ◃ t₁)
flexRigidLem x (t ⇒ t₁) () | nothing | [ eq ]



-- 型変数 x と型 t を unify する代入を返す
-- x が t に現れていたら nothing を返す
flexRigid2 : {m : ℕ} → (x : Fin m) → (t : Type m) →
             Maybe (Σ[ σ ∈ Σ[ n ∈ ℕ ] AList m n ] substType (proj₂ σ) (TVar x) ≡ substType (proj₂ σ) t)
flexRigid2 {zero} () t
flexRigid2 {suc m} x t with check x t | inspect (check x) t
... | nothing | [ checkxt≡nothing ] = nothing -- x が t に現れていた
... | just t' | [ checkxt≡justt' ] = just ((m , anil asnoc t' / x) , flexRigidLem x t checkxt≡justt') -- t' for x を返す
  -- goal : TVar ◃ ((t' for x) ◃ (TVar x)) ≡ (λ y → TVar ◃ (t' for x) y) ◃ t

substTypeForCommute : ∀ {m n} (σ : AList m n) (r : Type m) (z : Fin (suc m)) (s : Type (suc m)) →
                      substType (σ asnoc r / z) s ‌≡ substType σ ((r for z) ◃ s)
substTypeForCommute σ r z (TVar x) = refl
substTypeForCommute σ r z TInt = refl
substTypeForCommute σ r z (s1 ⇒ s2) =
  cong₂ _⇒_ (substTypeForCommute σ r z s1) (substTypeForCommute σ r z s2)

substTypeForEq1 : ∀ {m n} (σ : AList m n) (r : Type m) (z : Fin (suc m)) (s t : Type (suc m)) →
                  substType (σ asnoc r / z) s ‌≡ substType (σ asnoc r / z) t →
                  substType σ ((r for z) ◃ s) ‌≡ substType σ ((r for z) ◃ t)
substTypeForEq1 σ r z s t eq = 
  begin
    substType σ ((r for z) ◃ s)
  ≡⟨ sym (substTypeForCommute σ r z s)  ⟩
    substType (σ asnoc r / z) s
  ≡⟨ eq ⟩
    substType (σ asnoc r / z) t
  ≡⟨ substTypeForCommute σ r z t ⟩
    substType σ ((r for z) ◃ t)
  ∎

substTypeForEq2 : ∀ {m n} (σ : AList m n) (r : Type m) (z : Fin (suc m)) (s t : Type (suc m)) →
                  substType σ ((r for z) ◃ s) ‌≡ substType σ ((r for z) ◃ t) →
                  substType (σ asnoc r / z) s ‌≡ substType (σ asnoc r / z) t
substTypeForEq2 σ r z s t eq = 
  begin
    substType (σ asnoc r / z) s
  ≡⟨ substTypeForCommute σ r z s ⟩
    substType σ ((r for z) ◃ s)
  ≡⟨ eq ⟩
    substType σ ((r for z) ◃ t)
  ≡⟨ sym (substTypeForCommute σ r z t)  ⟩
    substType (σ asnoc r / z) t
  ∎

-- 型 s と t（に acc をかけたもの）を unify する代入を返す
amgu2 : {m : ℕ} → (s t : Type m) → (acc : Σ[ n ∈ ℕ ] AList m n) →
                Maybe (Σ[ σ ∈ Σ[ n ∈ ℕ ] AList m n ]
                       σ extends acc × substType (proj₂ σ) s ≡ substType (proj₂ σ) t)
amgu2 TInt     TInt     acc        = just (acc , σextendsσ acc , refl) -- just acc
amgu2 TInt     (t ⇒ t₁) acc        = nothing
amgu2 (s ⇒ s₁) TInt     acc        = nothing
amgu2 (s ⇒ s₁) (t ⇒ t₁) acc        with amgu2 s t acc
...                               | nothing = nothing
...                               | just (acc' , ex , eq)
                                    with amgu2 s₁ t₁ acc'
...                               | nothing = nothing
...                               | just (acc'' , ex2 , eq2) =
                                    just (acc'' , (λ s₂ t₂ → ex2 s₂ t₂ ∘ ex s₂ t₂) ,
                                                  cong₂ _⇒_ (ex2 s t eq) eq2)
amgu2 (TVar x) (TVar y) (s , anil) with flexFlex2 x y -- just (flexFlex x y)
...                               | (σ' , eq) = just (σ' , σextendsNil σ' , eq)
amgu2 (TVar x) t        (s , anil) with flexRigid2 x t
...                               | just (σ' , eq) = just (σ' , σextendsNil σ' , eq)
...                               | nothing = nothing
amgu2 t        (TVar x) (s , anil) with flexRigid2 x t
...                               | just (σ' , eq) = just (σ' , σextendsNil σ' , sym eq)
...                               | nothing = nothing
amgu2 {suc m} s t (n , σ asnoc r / z)
  with amgu2 {m} ((r for z) ◃ s) ((r for z) ◃ t) (n , σ)
... | nothing = nothing
... | just ((n' , σ') , ex , eq) =
      just ((n' , σ' asnoc r / z) , (λ s' t' ex' → substTypeForEq2 σ' r z s' t'
                                                        (ex ((r for z) ◃ s') ((r for z) ◃ t')
                                                            (substTypeForEq1 σ r z s' t' ex'))) ,
                                     substTypeForEq2 σ' r z s t eq)

-- 型 s と t を unify する代入を返す
mgu2 : {m : ℕ} → (s t : Type m) →
       Maybe (Σ[ n ∈ ℕ ] Σ[ σ ∈ AList m n ] substType σ s ≡ substType σ t)
mgu2 {m} s t with amgu2 {m} s t (m , anil)
... | just ((n , σ) , ex , eq) = just (n , σ , eq)
... | nothing = nothing
