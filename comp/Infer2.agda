module Infer2 where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Vec 
open import Data.Product
open import Data.Fin hiding (_+_; _≤_)
open import Data.Maybe
open import Data.Sum
open import lib
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Binary.HeterogeneousEquality
  renaming (sym to hsym; trans to htrans; cong to hcong; cong₂ to hcong₂; subst to hsubst; subst₂ to hsubst₂; refl to hrefl)

open import Data.Nat.Properties
 -- for the concrete record, such as isCommutativeSemiring
open import Algebra.Structures
 -- for type definitions, such as IsCommutativeSemiring
private module M = IsCommutativeSemiring

+-right-identity : ∀ n → n + 0 ≡ n
+-right-identity = proj₂ (M.+-identity isCommutativeSemiring)

+-assoc : ∀ m n o → (m + n) + o ≡  m + (n + o)
+-assoc = M.+-assoc isCommutativeSemiring

+-comm : ∀ m n → m + n ≡  n + m
+-comm = M.+-comm isCommutativeSemiring

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)
-- +-suc m n rewrite +-comm m n = +-comm m (suc n)

-- 型変数の数が m 個で長さが n の型環境
Cxt : {m : ℕ} → ℕ → Set
Cxt {m} n = Vec (Type m) n

-- Fin の inject+ は結論部が Fin (m + n)
inject+' : ∀ {m} n → Fin m → Fin (n + m)
inject+' zero m = m
inject+' (suc n) m = inject₁ (inject+' n m)

-- liftCxt m' Γ : Γ の中の型変数の数を m' だけ増やす
liftCxt : (m' : ℕ) → {m n : ℕ} → Cxt {m} n → Cxt {m' + m} n
-- liftCxt m' {m} {n} Γ = Data.Vec.map f Γ
--   where f : Type m → Type (m' + m)
--         f rewrite +-comm m' m = ▹◃ (inject+ m')
-- liftCxt m' {m} Γ rewrite +-comm m' m = Data.Vec.map (▹◃ (inject+ m')) Γ
liftCxt m' {m} Γ = Data.Vec.map (▹◃ (inject+' m')) Γ

-- eqCxt : {m m' n : ℕ} → m ≡ m' → Cxt {m} n → Cxt {m'} n
-- eqCxt {m} {m'} {n} m≡m' Γ = subst (λ m → Cxt {m} n) m≡m' Γ 

liftCxtZero : {m n : ℕ} → (Γ : Cxt {m} n) → liftCxt 0 Γ ≡ Γ
liftCxtZero [] = refl
liftCxtZero (x ∷ Γ) = cong₂ _∷_ (TVarId x) (liftCxtZero Γ)

-- liftCxtZero [] = refl
-- liftCxtZero (x ∷ Γ) = cong₂ _∷_ (TVarId x) (liftCxtZero Γ)

-- 本当は liftCxt だけにしたかったが...
-- liftCxt2 : (m' : ℕ) → {m n : ℕ} → Cxt {m} n → Cxt {m + m'} n
-- liftCxt2 m' {m} Γ = Data.Vec.map (▹◃ (inject+ m')) Γ

-- liftType m' t : t の中の型変数の数を m' だけ増やす
liftType : (m' : ℕ) → {m : ℕ} → Type m → Type (m' + m)
liftType m' {m} t = ▹◃ (inject+' m') t
-- liftType m' {m} t rewrite +-comm m' m = ▹◃ (inject+ m') t

-- 本当は liftType だけにしたかったが...
-- liftType : (m' : ℕ) → {m : ℕ} → Type m → Type (m + m')
-- liftType m' {m} t = ▹◃ (inject+ m') t

-- liftAList n lst : lst の中の型変数の数を m' だけ増やす
-- liftAList : {m m' : ℕ} → (n : ℕ) → AList m m' → AList (m + n) (m' + n)
-- liftAList n anil = anil 
-- liftAList n (a asnoc t' / x) = (liftAList n a) asnoc (liftType n t') / (inject+ n x)

liftAList1 : {m m' : ℕ} → AList m m' → AList (suc m) (suc m')
liftAList1 anil = anil
liftAList1 (σ asnoc t / x) = liftAList1 σ asnoc liftType 1 t / inject₁ x

-- 本当は liftAList だけにしたかったが...
liftAList : {m m' : ℕ} → (n : ℕ) → AList m m' → AList (n + m) (n + m')
liftAList zero σ = σ
liftAList (suc n) σ = liftAList1 (liftAList n σ)
-- liftAList n anil = anil 
-- liftAList {suc m} n (a asnoc t' / x) rewrite +-suc n m = (liftAList n a) asnoc (liftType n t') / x'
--   where x' : Fin (suc (n + m))
--         x' rewrite sym (+-suc n m) = inject≤ x (n≤m+n n (suc m))

-- substType σ t : t に σ を適用した型を返す
substType : {m m' : ℕ} → AList m m' → Type m → Type m' 
substType σ t = sub σ ◃ t

-- substCxt σ Γ : Γ に σ を適用した型環境を返す
substCxt : {m m' n : ℕ} → AList m m' → Cxt {m} n → Cxt {m'} n 
substCxt σ Γ = Data.Vec.map (substType σ) Γ 

substCxtAnil : {m n : ℕ} → (Γ : Cxt {m} n) → substCxt anil Γ ≡ Γ 
substCxtAnil [] = refl
substCxtAnil (x ∷ Γ) = cong₂ _∷_ (TVarId x) (substCxtAnil Γ)

-- 自由変数の数が n 個の well-socpe な項
data WellScopedTerm (n : ℕ) : Set where
  Var : Fin n → WellScopedTerm n
  Lam : WellScopedTerm (suc n) → WellScopedTerm n
  App : WellScopedTerm n → WellScopedTerm n → WellScopedTerm n

-- WellTypedTerm Γ t : 自由変数の数が n 個、型が t であるような well-typed な項
data WellTypedTerm {m n : ℕ} (Γ : Cxt n) : Type m → Set where
  Var : (x : Fin n) → WellTypedTerm Γ (lookup x Γ)
  Lam : (t : Type m) → {t' : Type m} → WellTypedTerm (t ∷ Γ) t' →
        WellTypedTerm Γ (t ⇒ t')
  App : {t t' : Type m} → WellTypedTerm Γ (t ⇒ t') → WellTypedTerm Γ t →
        WellTypedTerm Γ t'

-- lookup と liftCxt は順番を変えても良い
lookupLiftCxtCommute : (m' : ℕ) {n m : ℕ} (x : Fin n) (Γ : Cxt {m} n) →
                       liftType m' (lookup x Γ) ≡ lookup x (liftCxt m' Γ)
lookupLiftCxtCommute m' {zero} () Γ
lookupLiftCxtCommute m' {suc n} zero (t ∷ Γ) = refl
lookupLiftCxtCommute m' {suc n} (suc x) (t ∷ Γ) = lookupLiftCxtCommute m' x Γ

-- WellTypedTerm を lift する
liftWTerm : (m' : ℕ) {m n : ℕ} → {Γ : Cxt {m} n} → {t : Type m} → WellTypedTerm Γ t →
            WellTypedTerm (liftCxt m' Γ) (liftType m' t)
liftWTerm m' {Γ = Γ} (Var x) rewrite lookupLiftCxtCommute m' x Γ = Var x
liftWTerm m' (Lam t w) = Lam (liftType m' t) (liftWTerm m' w)
liftWTerm m' (App w1 w2) = App (liftWTerm m' w1) (liftWTerm m' w2)

-- lookup と substCxt は順番を変えても良い
lookupSubstCxtCommute : {n m' m : ℕ} (x : Fin n) (Γ : Cxt {m} n) → (σ : AList m m') →
                       substType σ (lookup x Γ) ≡ lookup x (substCxt σ Γ)
lookupSubstCxtCommute {zero} () Γ σ
lookupSubstCxtCommute {suc n} zero (t ∷ Γ) σ = refl
lookupSubstCxtCommute {suc n} (suc x) (t ∷ Γ) σ = lookupSubstCxtCommute x Γ σ

-- substWTerm σ w : w に σ を適用した WellTypedTerm を返す
substWTerm : {m' m n : ℕ} → {Γ : Cxt {m} n} → {t : Type m} →
             (σ : AList m m') → WellTypedTerm Γ t → WellTypedTerm (substCxt σ Γ) (substType σ t)
substWTerm {Γ = Γ} σ (Var x) rewrite lookupSubstCxtCommute x Γ σ = Var x
substWTerm σ (Lam t w) = Lam (substType σ t) (substWTerm σ w)
substWTerm σ (App w1 w2) = App (substWTerm σ w1) (substWTerm σ w2)

-- unify t1 t2 : 型変数が m 個であるような型 t1 と t2 を unify する代入を返す
unify : {m : ℕ} → Type m → Type m → Maybe (Σ[ n ∈ ℕ ] AList m n)
unify {m} t1 t2 = mgu {m} t1 t2

-- Well-scope な項の中の Lam と App のノード数を数える
-- （その数が、新たに導入される型変数の数になる）
count : {n : ℕ} → (s : WellScopedTerm n) → ℕ
count (Var x) = zero
count (Lam s) = suc (count s)
count (App s1 s2) = count s1 + suc (count s2)

{-

-- inferW Γ s : Γ のもとで s を型推論する。
-- もとの型変数の数が m だったとき、推論結果として (m', 代入, 型) を返す。
-- ここで m' は返って来た型の中に含まれる型変数の数。
-- あらかじめ s の中の Lam, App ノードに型変数をひとつ割り振ったとすると、
-- 型変数の合計は、もともと m + count s となる。
-- 返ってくる代入は、型変数の数を m + count s から m' に落とすものになる。
inferW : {m n : ℕ} →  (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m' ∈ ℕ ] AList (count s + m) m' × Type m')
inferW {m} Γ (Var x) = just (m , anil , lookup x Γ)
inferW {m} Γ (Lam s) with inferW (TVar (fromℕ m) ∷ liftCxt 1 Γ) s -- TVar (fromℕ m) が引数の型
... | nothing = nothing -- s に型がつかなかった
... | just (m' , σ , t) rewrite +-suc (count s) m =
  just (m' , σ , substType σ tx ⇒ t) -- TVar (fromℕ m) ⇒ t が Lam s の型
  where tx : Type (suc (count s) + m)
        tx rewrite sym (+-suc (count s) m) = liftType (count s) (TVar (fromℕ m))
inferW {m} Γ (App s1 s2)
      with inferW Γ s1
... | nothing = nothing -- s1 に型がつかなかった
... | just (m1 , σ1 , t1) -- s1 の型が t1
      with inferW (substCxt σ1 (liftCxt (count s1) Γ)) s2
... | nothing = nothing -- s2 に型がつかなかった
... | just (m2 , σ2 , t2) -- s2 の型が t2。m2 を App s1 s2 の返り値の型に割り当てる
      with unify (liftType 1 (substType σ2 (liftType (count s2) t1))) -- t1
                 (liftType 1 t2 ⇒ TVar (fromℕ m2)) -- t2 ⇒ TVar (fromℕ m2)
... | nothing = nothing -- unify できなかった
... | just (m3 , σ3) = -- rewrite (+-assoc m (count s1) (suc (count s2)))
  just (m3 , σ3 ⊹⊹ (σ2' ⊹⊹ σ1') , substType σ3 (TVar (fromℕ m2))) 
  where σ1' : AList (count s1 + suc (count s2) + m) (suc (count s2 + m1))
        σ1' rewrite +-comm (count s1) (suc (count s2)) | +-assoc (count s2) (count s1) m
          = liftAList (suc (count s2)) σ1
        σ2' : AList (suc (count s2 + m1)) (suc m2)
        σ2' = liftAList 1 σ2

-- test

test1 : WellScopedTerm 0
test1 = Lam (Var zero)
infer1 : inferW {0} [] test1 ≡ just (1 , anil , TVar zero ⇒ TVar zero)
infer1 = refl

test2 : WellScopedTerm 0
test2 = Lam (Lam (Var zero))
infer2 : inferW {0} [] test2 ≡ just (2 , anil , TVar zero ⇒ (TVar (suc zero) ⇒ TVar (suc zero)))
infer2 = refl 

test2b : WellScopedTerm 0
test2b = Lam (Lam (Var (suc zero)))
infer2b : inferW {0} [] test2b ≡ just (2 , anil , TVar zero ⇒ (TVar (suc zero) ⇒ TVar zero))
infer2b = refl 

-- λx. λy. y x
test3 : WellScopedTerm 0
test3 = Lam (Lam (App (Var zero) (Var (suc zero))))
infer3 : inferW {0} [] test3  ≡ just
  (2 ,
  anil asnoc TVar zero ⇒ TVar (suc zero) / suc zero ,
  TVar zero ⇒ ((TVar zero ⇒ TVar (suc zero)) ⇒ TVar (suc zero)))
infer3 = refl

test4 : WellScopedTerm 0
test4 = Lam (App (Var zero) (Var zero))
infer4 : inferW {0} [] test4 ≡ nothing
infer4 = refl

-}

{-
hsubst' : {C1 C2 : Set} {x : C1} {y : C2}
        -> (P : {C : Set} -> C -> Set)
        -> x ≅ y
        -> P x
        -> P y
hsubst' _ hrefl x = x
-}

hsubst' : ∀ {a b c} {I : Set a} {i j : I}
       -> (A : I -> Set b) {x' : A i} {y : A j}
       -> i ≡ j
       -> (P : {i : I} -> A i -> Set c)
       -> x' ≅ y
       -> P x' → P y
hsubst' _ refl P hrefl px = px

{-
hsubst₂' : ∀ {a b c d} {I : Set a} {i1 i2 : I}
          (A : I → Set b)
          (B : I → Set c)
          {x : A i1} {y : A i2} {u : B i1} {v : B i2}
        -> i1 ≡ i2
        -> (P : {i : I} -> (x : A i) -> (y : B i) -> Set d)
        -> x ≅ y
        -> u ≅ v
        -> P x u
        -> P y v
hsubst₂' _ _ refl P hrefl hrefl x = x
-}

hcong' : ∀ {α β γ} {I : Set α} {i j : I}
       -> (A : I -> Set β) {B : {k : I} -> A k -> Set γ} {x : A i} {y : A j}
       -> i ≡ j
       -> (f : {k : I} -> (x : A k) -> B x)
       -> x ≅ y
       -> f x ≅ f y
hcong' _ refl _ hrefl = hrefl

-- cong : ∀ {a b} {A : Set a} {B : A → Set b} {x y}
--       (f : (x : A) → B x) → x ≅ y → f x ≅ f y
-- cong f refl = refl

{-
hcong₂' : ∀ {a b c d} {I J : Set a} {i1 i2 : I} {j1 j2 : J}
          (A : I → Set b)
          (B : {i : I} → (j : J) → A i → Set c)
          {C : {i : I} → (x : A i) → {j : J} → B j x → Set d}
          {x : A i1} {y : A i2} {u : B j1 x} {v : B j2 y} →
        i1 ≡ i2 → j1 ≡ j2 →
        (f : {i : I} → {j : J} → (x : A i) → (y : B j x) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
hcong₂' _ _ refl refl f hrefl hrefl = hrefl
-}

hcong₂' : ∀ {a b c d} {I : Set a} {i1 i2 : I}
          (A : I → Set b)
          (B : I → Set c)
          {C : {i : I} → A i → B i → Set d}
          {x : A i1} {y : A i2} {u : B i1} {v : B i2} →
        i1 ≡ i2 →
        (f : {i : I} → (x : A i) → (y : B i) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
hcong₂' _ _ refl f hrefl hrefl = hrefl

injectSuc : ∀ m' {n} (x : Fin n) → inject+' m' (inject₁ x) ≅ inject₁ (inject+' m' x)
injectSuc zero x = hrefl
injectSuc (suc m') {n} x = hcong' Fin (+-suc m' n) inject₁ (injectSuc m' x)

injectAdd : ∀ {m} m1 m2 → (x : Fin m) → inject+' m1 (inject+' m2 x) ≅ inject+' (m1 + m2) x
injectAdd zero m2 x = hrefl
injectAdd {m} (suc m1) m2 x = hcong' Fin (sym (+-assoc m1 m2 m)) inject₁ (injectAdd m1 m2 x)

liftTypeSuc : {m m' : ℕ} → (t : Type m) → liftType m' (liftType 1 t) ≅ liftType (suc m') t
liftTypeSuc {m} {m'} (TVar x) = hcong' Fin (+-suc m' m) TVar (injectSuc m' x)
liftTypeSuc {m} {m'} TInt rewrite +-suc m' m = hrefl
liftTypeSuc {m} {m'} (t1 ⇒ t2) =
  hcong₂' Type Type (+-suc m' m) _⇒_ (liftTypeSuc {m} {m'} t1) (liftTypeSuc {m} {m'} t2)

liftTypeAdd : ∀ {m} m1 m2 → (t : Type m) → liftType m1 (liftType m2 t) ≅ liftType (m1 + m2) t
liftTypeAdd {m} m1 m2 (TVar x) = hcong' Fin (sym (+-assoc m1 m2 m)) TVar (injectAdd m1 m2 x)
liftTypeAdd {m} m1 m2 TInt rewrite sym (+-assoc m1 m2 m) = hrefl
liftTypeAdd {m} m1 m2 (t1 ⇒ t2) =
  hcong₂' Type Type (sym (+-assoc m1 m2 m)) _⇒_ (liftTypeAdd m1 m2 t1) (liftTypeAdd m1 m2 t2)

liftCxtSuc : ∀ {m} m' {n} → (Γ : Cxt {m} n) → liftCxt m' (liftCxt 1 Γ) ≅ liftCxt (suc m') Γ
liftCxtSuc {m} m' [] rewrite +-suc m' m = hrefl
liftCxtSuc {m} m' {suc n} (t ∷ Γ) =
  hcong₂' Type (λ m → Cxt {m} n) (+-suc m' m) _∷_ (liftTypeSuc {m} {m'} t) (liftCxtSuc {m} m' Γ)

liftCxtAdd : ∀ {m} m1 m2 {n} → (Γ : Cxt {m} n) → liftCxt m1 (liftCxt m2 Γ) ≅ liftCxt (m1 + m2) Γ
liftCxtAdd {m} m1 m2 [] rewrite sym (+-assoc m1 m2 m) = hrefl
liftCxtAdd {m} m1 m2 {suc n} (t ∷ Γ) =
  hcong₂' Type (λ m → Cxt {m} n) (sym (+-assoc m1 m2 m)) _∷_ (liftTypeAdd m1 m2 t) (liftCxtAdd m1 m2 Γ)

substConsCommute : ∀ {m m' n} (eq : m ≡ m') (t : Type m) (Γ : Cxt {m} n) →
                   subst (λ m → Cxt {m} (suc n)) eq (t ∷ Γ) ≡ 
                   subst Type eq t ∷ subst (λ m → Cxt {m} n) eq Γ
substConsCommute refl t Γ = refl

substArrowCommute : ∀ {m m'} (eq : m ≡ m') (t1 t2 : Type m) →
                    subst Type eq (t1 ⇒ t2) ≡ subst Type eq t1 ⇒ subst Type eq t2
substArrowCommute refl t1 t2 = refl

thickInject1 : ∀ {n} (x y : Fin (suc n)) →
               (thick x y ≡ nothing × thick (inject₁ x) (inject₁ y) ≡ nothing) ⊎
               (Σ[ y' ∈ Fin n ] thick x y ≡ just y' × thick (inject₁ x) (inject₁ y) ≡ just (inject₁ y'))
thickInject1 zero zero = inj₁ (refl , refl)
thickInject1 zero (suc y) = inj₂ (y , refl , refl)
thickInject1 {zero} (suc ()) zero
thickInject1 {suc n} (suc x) zero = inj₂ (zero , refl , refl)
thickInject1 {zero} (suc ()) (suc y)
thickInject1 {suc n} (suc x) (suc y) with thickInject1 x y
... | inj₁ (eq1 , eq2) rewrite eq1 | eq2 = inj₁ (refl , refl)
... | inj₂ (y' , eq1 , eq2) rewrite eq1 | eq2 = inj₂ (suc y' , refl , refl)

AListNoLess : ∀ {m n} (σ : AList m n) → n ≤′ m
AListNoLess anil = ≤′-refl
AListNoLess (σ asnoc t' / x) = ≤′-step (AListNoLess σ)

mutual
  liftSub1Commute : ∀ {m' m} (σ : AList m' m) (x : Fin m') →
                    liftType 1 (sub σ x) ≡ sub (liftAList1 σ) (inject₁ x)
  liftSub1Commute σ x with AListNoLess σ
  ... | ≤′-refl = {!!}
  ... | ≤′-step a = {!!}
--  liftSub1Commute {zero} anil x = refl
--  liftSub1Commute {zero} (σ asnoc t' / x) x₁ = {!!}
--  liftSub1Commute {suc s} σ x = {!!}
--  以下の定義は termination check にひっかかる。AList の長さについて再帰したいが、
--  AList (s + m) m の s で再帰するのではうまくいかない。AList の定義を変更しなくてはだめか。
--  liftSub1Commute anil x = refl
--  liftSub1Commute {suc s} (σ asnoc t / y) x with thickInject1 y x
--  ... | inj₁ (eq1 , eq2) rewrite eq1 | eq2 = liftSubstCommute {s} (suc zero) σ t
--  ... | inj₂ (x' , eq1 , eq2) rewrite eq1 | eq2 = liftSub1Commute σ x'

  liftSubCommute : ∀ {m' m} c (σ : AList m' m) (x : Fin m') →
                   liftType c (sub σ x) ≡ sub (liftAList c σ) (inject+' c x)
  liftSubCommute zero σ x rewrite TVarId (sub σ x) = refl
  liftSubCommute (suc c) σ x =
    begin
      liftType (suc c) (sub σ x)
    ≡⟨ sym (≅-to-≡ (liftTypeAdd 1 c (sub σ x))) ⟩
      liftType 1 (liftType c (sub σ x))
    ≡⟨ cong (liftType 1) (liftSubCommute c σ x) ⟩
      liftType 1 (sub (liftAList c σ) (inject+' c x))
    ≡⟨ liftSub1Commute (liftAList c σ) (inject+' c x) ⟩
      sub (liftAList1 (liftAList c σ)) (inject₁ (inject+' c x))
    ∎

  liftSubstCommute : ∀ {m' m} c (σ : AList m' m) (t : Type m') →
                     liftType c (substType σ t) ≡ substType (liftAList c σ) (liftType c t)
  liftSubstCommute c σ (TVar x) = liftSubCommute c σ x
  liftSubstCommute c σ TInt = refl
  liftSubstCommute c σ (t1 ⇒ t2) = cong₂ _⇒_ (liftSubstCommute c σ t1) (liftSubstCommute c σ t2)

substLiftTypeAdd : ∀ {m m2 m1} c2 c1 (σ2 : AList (c2 + m1) m2) (σ1 : AList (c1 + m) m1) (t : Type m) →
                   substType σ2 (liftType c2 (substType σ1 (liftType c1 t))) ≅
                   substType (σ2 ⊹⊹ liftAList c2 σ1)
                             (subst Type (+-assoc c2 c1 m) (liftType (c2 + c1) t))
substLiftTypeAdd {m} c2 c1 σ2 σ1 (TVar x) = {!!}
substLiftTypeAdd {m} c2 c1 σ2 σ1 TInt rewrite +-assoc c2 c1 m = hrefl
substLiftTypeAdd {m} c2 c1 σ2 σ1 (t1 ⇒ t2)
  rewrite substArrowCommute (+-assoc c2 c1 m) (liftType (c2 + c1) t1) (liftType (c2 + c1) t2) =
  hcong₂ _⇒_ (substLiftTypeAdd c2 c1 σ2 σ1 t1) (substLiftTypeAdd c2 c1 σ2 σ1 t2)

substLiftCxtAdd : ∀ {m n m2 m1} c2 c1 (σ2 : AList (c2 + m1) m2) (σ1 : AList (c1 + m) m1) (Γ : Cxt {m} n) →
               substCxt σ2 (liftCxt c2 (substCxt σ1 (liftCxt c1 Γ))) ≅
               substCxt (σ2 ⊹⊹ liftAList c2 σ1)
                        (subst (λ m → Cxt {m} n) (+-assoc c2 c1 m) (liftCxt (c2 + c1) Γ))
substLiftCxtAdd {m} c2 c1 σ2 σ1 [] rewrite +-assoc c2 c1 m = hrefl
substLiftCxtAdd {m} {suc n} c2 c1 σ2 σ1 (t ∷ Γ)
  rewrite substConsCommute (+-assoc c2 c1 m) (liftType (c2 + c1) t) (liftCxt (c2 + c1) Γ) =
  hcong₂ _∷_ (substLiftTypeAdd c2 c1 σ2 σ1 t) (substLiftCxtAdd c2 c1 σ2 σ1 Γ)

{-

infer : {m n : ℕ} → (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
        Maybe (Σ[ m' ∈ ℕ ]
               Σ[ σ ∈ AList (count s + m) m' ]
               Σ[ τ ∈ Type m' ]
               WellTypedTerm (substCxt σ (liftCxt (count s) Γ)) τ)
infer {m} Γ (Var x) rewrite liftCxtZero Γ =
  just (m , anil , lookup x Γ , VarX)
  where VarX : WellTypedTerm (substCxt anil Γ) (lookup x Γ)
        VarX rewrite substCxtAnil Γ = Var x
infer {m} {n} Γ (Lam s) with infer (TVar (fromℕ m) ∷ liftCxt 1 Γ) s -- TVar (fromℕ m) が引数の型
... | nothing = nothing
... | just (m' , σ , t , w) =
  just (m' , σ' , tx ⇒ t , LamW)
  where σ' : AList (suc (count s + m)) m' 
        σ' = subst (λ m → AList m m') (+-suc (count s) m) σ
        -- σ' rewrite sym (+-suc (count s) m) = σ
        tx : Type m'
        tx = substType σ (liftType (count s) (TVar (fromℕ m)))
        LamW : WellTypedTerm (substCxt σ' (liftCxt (count (Lam s)) Γ)) (tx ⇒ t)
        LamW = Lam tx w'
               where w' : WellTypedTerm (tx ∷ (substCxt σ' (liftCxt (count (Lam s)) Γ))) t
                     w' = subst (λ l → WellTypedTerm (tx ∷ l) t) eq w
                          where eq : substCxt σ (liftCxt (count s) (liftCxt 1 Γ)) ≡
                                     substCxt σ' (liftCxt (count (Lam s)) Γ)
                                eq = ≅-to-≡ (hcong₂' (λ c → AList c m') (λ c → Cxt {c} n)
                                                     (+-suc (count s) m)
                                                     substCxt
                                                     (hsym (≡-subst-removable (λ m → AList m m')
                                                                              (+-suc (count s) m) σ))
                                                     (liftCxtSuc (count s) Γ))
infer {m} {n} Γ (App s1 s2)
      with infer Γ s1
... | nothing = nothing -- s1 に型がつかなかった
... | just (m1 , σ1 , t1 , w1) -- s1 の型が t1
      with infer (substCxt σ1 (liftCxt (count s1) Γ)) s2
... | nothing = nothing -- s2 に型がつかなかった
... | just (m2 , σ2 , t2 , w2) -- s2 の型が t2。m2 を App s1 s2 の返り値の型に割り当てる
      with unify (liftType 1 (substType σ2 (liftType (count s2) t1))) -- t1
                 (liftType 1 t2 ⇒ TVar (fromℕ m2)) -- t2 ⇒ TVar (fromℕ m2)
... | nothing = nothing -- unify できなかった
... | just (m3 , σ3) =
  just (m3 , σ3 ⊹⊹ (σ2' ⊹⊹ σ1') , substType σ3 (TVar (fromℕ m2)) , AppW1W2) 
  where σ1' : AList (count s1 + suc (count s2) + m) (suc (count s2 + m1))
        σ1' rewrite +-comm (count s1) (suc (count s2)) | +-assoc (count s2) (count s1) m
          = liftAList (suc (count s2)) σ1
        σ2' : AList (suc (count s2 + m1)) (suc m2)
        σ2' = liftAList 1 σ2
        AppW1W2 : WellTypedTerm (substCxt (σ3 ⊹⊹ (σ2' ⊹⊹ σ1')) (liftCxt (count (App s1 s2)) Γ))
                                (substType σ3 (TVar (fromℕ m2)))
        AppW1W2 = App w1' w2'
                  where w1' : WellTypedTerm (substCxt (σ3 ⊹⊹ (σ2' ⊹⊹ σ1')) (liftCxt (count (App s1 s2)) Γ))
                                            (substType σ3 (liftType 1 t2 ⇒ TVar (fromℕ m2)))
                        w1' = {!!}
                        w1o : WellTypedTerm (substCxt σ1 (liftCxt (count s1) Γ)) t1
                        w1o = w1
                        -- σ1 : AList (count s1 + m) m1
                        -- σ1': AList (count s1 + suc (count s2) + m) (suc (count s2 + m1))
                        -- σ2 : AList (count s2 + m1) m2
                        -- σ2': AList (suc (count s2 + m1)) (suc m2)
                        -- σ3 : AList (suc m2) m3
                        -- σ2' ⊹⊹ σ1' : AList (count s1 + suc (count s2) + m) (suc m2)
                        Γ1 : Cxt {m1} n
                        Γ1 = substCxt σ1 (liftCxt (count s1) Γ)
                        Γ2 : Cxt {m2} n
                        Γ2 = substCxt σ2 (liftCxt (count s2) Γ1)
                        Γ3 : Cxt {m3} n
                        Γ3 = substCxt σ3 (liftCxt 1 Γ2)
                        Γ4 : Cxt {m3} n
                        Γ4 = substCxt (σ3 ⊹⊹ (σ2' ⊹⊹ σ1')) (liftCxt (count (App s1 s2)) Γ)
                        w2o : WellTypedTerm Γ2 t2
                        w2o = w2
                        w2o2 : WellTypedTerm (liftCxt 1 Γ2) (liftType 1 t2)
                        w2o2 = liftWTerm 1 w2
                        w2o3 : WellTypedTerm (substCxt σ3 (liftCxt 1 Γ2)) (substType σ3 (liftType 1 t2))
                        w2o3 = substWTerm σ3 (liftWTerm 1 w2)
                        eq : Γ3 ≅ Γ4
                        eq = htrans {!!} {!!}
                        w2' : WellTypedTerm (substCxt (σ3 ⊹⊹ (σ2' ⊹⊹ σ1')) (liftCxt (count (App s1 s2)) Γ))
                                            (substType σ3 (liftType 1 t2))
                        w2' = hsubst (λ Γ → WellTypedTerm Γ (substType σ3 (liftType 1 t2)))
                                     eq w2o3
-- hsubst' _ refl P hrefl x = x
-}
