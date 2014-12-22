module Infer where

--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Vec 
open import Data.Product
open import Data.Fin hiding (_+_)
open import Data.Maybe
open import lib

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
+-suc m n rewrite +-comm m n = +-comm m (suc n)

-- 型変数の数が m 個で長さが n の型環境
Cxt : {m : ℕ} → ℕ → Set
Cxt {m} n = Vec (Type m) n

-- liftCxt m' Γ : Γ の中の型変数の数を m' だけ増やす
liftCxt : (m' : ℕ) → {m n : ℕ} → Cxt {m} n -> Cxt {m' + m} n
liftCxt m' {m} Γ rewrite +-comm m' m = Data.Vec.map (▹◃ (inject+ m')) Γ

-- 本当は liftCxt だけにしたかったが...
liftCxt2 : (m' : ℕ) → {m n : ℕ} → Cxt {m} n -> Cxt {m + m'} n
liftCxt2 m' {m} Γ = Data.Vec.map (▹◃ (inject+ m')) Γ

-- liftType m' t : t の中の型変数の数を m' だけ増やす
liftType : (m' : ℕ) → {m : ℕ} → Type m -> Type (m' + m)
liftType m' {m} t rewrite +-comm m' m = ▹◃ (inject+ m') t

-- 本当は liftType だけにしたかったが...
liftType2 : (m' : ℕ) → {m : ℕ} → Type m -> Type (m + m')
liftType2 m' {m} t = ▹◃ (inject+ m') t

-- liftAList n lst : lst の中の型変数の数を m' だけ増やす
liftAList : {m m' : ℕ} → (n : ℕ) → AList m m' → AList (m + n) (m' + n)
liftAList n anil = anil 
liftAList n (a asnoc t' / x) = (liftAList n a) asnoc (liftType2 n t') / (inject+ n x)

-- 本当は liftAList だけにしたかったが...
liftAList2 : {m m' : ℕ} → (n : ℕ) → AList m m' → AList (n + m) (n + m')
liftAList2 {m} {m'} n lst rewrite +-comm n m | +-comm n m' = liftAList n lst

-- substType σ t : t に σ を適用した型を返す
substType :{m m' : ℕ} → AList m m' → Type m → Type m' 
substType σ t = sub σ ◃ t

-- substCxt σ Γ : Γ に σ を適用した型環境を返す
substCxt : {m m' n : ℕ} → AList m m' → Cxt {m} n → Cxt {m'} n 
substCxt σ Γ = Data.Vec.map (substType σ) Γ 

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

-- unify t1 t2 : 型変数が m 個であるような型 t1 と t2 を unify する代入を返す
unify : {m : ℕ} → Type m → Type m → Maybe (Σ[ n ∈ ℕ ] AList m n)
unify {m} t1 t2 = mgu {m} t1 t2

-- Well-scope な項の中の Lam と App のノード数を数える
-- （その数が、新たに導入される型変数の数になる）
count : {n : ℕ} → (s : WellScopedTerm n) → ℕ
count (Var x) = zero
count (Lam s) = suc (count s)
count (App s1 s2) = count s1 + suc (count s2) 

-- inferW Γ s : Γ のもとで s を型推論する。
-- もとの型変数の数が m だったとき、推論結果として (m', 代入, 型) を返す。
-- ここで m' は返って来た型の中に含まれる型変数の数。
-- あらかじめ s の中の Lam, App ノードに型変数をひとつ割り振ったとすると、
-- 型変数の合計は、もともと m + count s となる。
-- 返ってくる代入は、型変数の数を m + count s から m' に落とすものになる。
inferW : {m n : ℕ} →  (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m' ∈ ℕ ] AList (m + count s) m' × Type m')
inferW {m} Γ (Var x) rewrite +-right-identity m = just (m , anil , lookup x Γ)
inferW {m} Γ (Lam s) with inferW (TVar (fromℕ m) ∷ liftCxt 1 Γ) s -- TVar (fromℕ m) が引数の型
... | nothing = nothing -- s に型がつかなかった
... | just (m' , σ , t) rewrite +-suc m (count s) =
  just (m' , σ , substType σ (liftType2 (count s) (TVar (fromℕ m))) ⇒ t) -- TVar (fromℕ m) ⇒ t が Lam s の型
inferW {m} Γ (App s1 s2)
      with inferW Γ s1
... | nothing = nothing -- s1 に型がつかなかった
... | just (m1 , σ1 , t1) -- s1 の型が t1
      with inferW (substCxt σ1 (liftCxt2 (count s1) Γ)) s2
... | nothing = nothing -- s2 に型がつかなかった
... | just (m2 , σ2 , t2) -- s2 の型が t2。m2 を App s1 s2 の返り値の型に割り当てる
      with unify (liftType 1 (substType σ2 (liftType2 (count s2) t1))) -- t1
                 (liftType 1 t2 ⇒ TVar (fromℕ m2)) -- t2 ⇒ TVar (fromℕ m2)
... | nothing = nothing -- unify できなかった
... | just (m3 , σ3) rewrite sym (+-assoc m (count s1) (suc (count s2)))
      with liftAList2 1 σ2
... | σ2' rewrite sym (+-suc m1 (count s2))
      with liftAList (suc (count s2)) σ1
... | σ1' =
      just (m3 , σ3 ⊹⊹ (σ2' ⊹⊹ σ1') , substType σ3 (TVar (fromℕ m2))) 

--inferW Γ (Let x e e₁) with inferW Γ e
-- inferW let x = e in e₁ =
-- let inferW Γ e = (σ,t) in
-- let inferW (σ Γx ∪ {x : substenv(σ Γ) (t)}) e₁ = (σ₁, t₁) in
-- (σ₁ σ, t₁)
--inferW {m} Γ (Let x e e₁) | just (m' , σ , t) with inferW ((ι (fromℕ m')) ∷ (substenv (liftAList₁ σ) (vecinject (▹◃ inject) Γ))) (liftterm {!!} {!!})
--inferW {m} Γ (Let x e e₁) | just (m' , σ , t) | just (m'' , σ₁ , t₁) = just (m'' , ({!!} , t₁))
--inferW {m} Γ (Let x e e₁) | just (m' , σ , t) | nothing = nothing
--inferW {m} Γ (Let x e e₁) | nothing = nothing




inferW' : (n : ℕ) → (m : ℕ) →  (Γ : Cxt {m} n) → (e : WellScopedTerm n) → Maybe (Σ[ m' ∈ ℕ ] Σ[ σ ∈ AList (m + (count n e)) m' ] Σ[ t ∈ Type m' ] WellTypedTerm (σ Γ) t)
inferW' n m Γ e = ?
-- inferW' n m Γ (Var x) = just (m , (inferVar m , ((lookup x (substenv (inferVar m) (vecinject (▹◃ (inject+ 0)) Γ))) , (Var x))))
-- inferW' n m Γ (Lam e) with inferW' (suc n) (suc m) (TVar (fromℕ m) ∷ (vecinject (▹◃ inject₁) Γ)) e
-- inferW' n m  Γ (Lam e) | just (m' , s₁ , t₁ , e') = just (m' , (inferLam {m} e s₁ , (sub s₁ (inject+ (count (suc n) e) (fromℕ m))) ⇒ t₁ , Lam (sub s₁ (inject+ (count (suc n) e) (fromℕ m))) {!!})) --TODO: rewrite +-suc m (count e)
-- inferW' n m Γ (Lam e) | nothing = nothing
-- inferW' n m Γ (App e e₁) with inferW' n m Γ e
-- inferW' n m Γ (App e e₁) | just (m' , σ , t , e') with inferW' n m' (substenv σ (vecinject (▹◃ (inject+ (count n e))) Γ)) e₁
-- inferW' n m Γ (App e e₁) | just (m' , σ , t , e') | just (m'' , σ₁ , t₁ , e'') with unify (▹◃ inject₁ ((substtype σ₁ (▹◃ (inject+ (count n e₁)) t))))  (▹◃ inject₁ t₁ ⇒ TVar (fromℕ m''))
-- inferW' n m Γ (App e e₁) | just (m' , σ , t , e') | just (m'' , σ₁ , t₁ , e'') | just (m''' , σ₂)  = just (m''' , (σ₂ ⊹⊹ ((liftAList₁ σ₁) ⊹⊹  inferApp {m} {m'} {_} e e₁ (liftσ₂ {m} {m'} {m'' } {m'''} e e₁ σ)) , ((substtype σ₂ (TVar (fromℕ m''))) , App {!e'!} {!e''!}))) -- TODO :  rewrite (sym (+-assoc m (count e) (suc (count e₁))))
-- inferW' n m Γ (App e e₁) | just (m' , σ , t , e') | just (m'' , σ₁ , t₁ , e'') | nothing = nothing
-- inferW' n m Γ (App e e₁) | just (m' , σ , t , e') | nothing = nothing
-- inferW' n m Γ (App e e₁) | nothing = nothing



-- -- test

-- test1 : WellScopedTerm 0
-- test1 = Lam (Var zero)
-- infer1 : inferW {0} [] test1 ≡ just (1 , anil , TVar zero ⇒ TVar zero)
-- infer1 = refl

-- test2 : WellScopedTerm 0
-- test2 = Lam (Lam (Var zero))
-- infer2 : inferW {0} [] test2 ≡ just (2 , anil , TVar zero ⇒ (TVar (suc zero) ⇒ TVar (suc zero)))
-- infer2 = refl 

-- test3 : WellScopedTerm 0
-- test3 = Lam (Lam (App (Var zero) (Var (suc zero))))
-- infer3 : inferW {0} [] test3  ≡ just
--   (2 ,
--   anil asnoc TVar zero ⇒ TVar (suc zero) / suc zero ,
--   TVar zero ⇒ ((TVar zero ⇒ TVar (suc zero)) ⇒ TVar (suc zero)))
-- infer3 = refl

-- test4 : WellScopedTerm 0
-- test4 = Lam (App (Var zero) (Var zero))
-- infer4 : inferW {0} [] test4 ≡ nothing
-- infer4 = refl

