module Infer where

open import Data.Nat
open import Data.Fin hiding (_+_; _≤_)
open import Data.Vec
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality
  renaming (sym to hsym; trans to htrans; cong to hcong; cong₂ to hcong₂; subst to hsubst; subst₂ to hsubst₂; refl to hrefl)
private module H = ≅-Reasoning

open import lib
open import Term

--------------------------------------------------------------------------------

-- inferW Γ s : Γ のもとで s を型推論する。
-- もとの型変数の数が m だったとき、推論結果として (m', 代入, 型) を返す。
-- ここで m' は返って来た型の中に含まれる型変数の数。
-- あらかじめ s の中の Lam, App ノードに型変数をひとつ割り振ったとすると、
-- 型変数の合計は、もともと m + count s となる。
-- 返ってくる代入は、型変数の数を m + count s から m' に落とすものになる。
infer : {m n : ℕ} →  (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m' ∈ ℕ ] AList (count s + m) m' × Type m')
infer {m} Γ (Var x) = just (m , anil , lookup x Γ)
infer {m} Γ (Lam s) with infer (TVar (fromℕ m) ∷ liftCxt 1 Γ) s -- TVar (fromℕ m) が引数の型
... | nothing = nothing -- s に型がつかなかった
... | just (m' , σ , t) =  just (m' , σ' , tx ⇒ t) -- TVar (fromℕ m) ⇒ t が Lam s の型
  where σ' : AList (suc (count s + m)) m' 
        σ' = subst (λ m → AList m m') (+-suc (count s) m) σ
        tx : Type m'
        tx = substType σ (liftType (count s) (TVar (fromℕ m))) -- σ (↑s m)
infer {m} Γ (App s1 s2)
      with infer Γ s1
... | nothing = nothing -- s1 に型がつかなかった
... | just (m1 , σ1 , t1) -- s1 の型が t1
      with infer (substCxt σ1 (liftCxt (count s1) Γ)) s2
... | nothing = nothing -- s2 に型がつかなかった
... | just (m2 , σ2 , t2) -- s2 の型が t2。m2 を App s1 s2 の返り値の型に割り当てる
      with unify (liftType 1 (substType σ2 (liftType (count s2) t1))) -- t1
                 (liftType 1 t2 ⇒ TVar (fromℕ m2)) -- t2 ⇒ TVar (fromℕ m2)
... | nothing = nothing -- unify できなかった
... | just (m3 , σ3) =
  just (m3 , σ3 +!+ (σ2' +!+ σ1') , substType σ3 (TVar (fromℕ m2))) 
  where σ1' : AList (count s1 + suc (count s2) + m) (suc (count s2 + m1))
        σ1' rewrite +-comm (count s1) (suc (count s2)) | +-assoc (count s2) (count s1) m
          = liftAList (suc (count s2)) σ1
        σ2' : AList (suc (count s2 + m1)) (suc m2)
        σ2' = liftAList 1 σ2

infer2 : {m n : ℕ} → (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m' ∈ ℕ ] Σ[ m'' ∈ ℕ ] (m'' ≡ count s + m) × AList m'' m' ×  Type m')

infer2 {m} Γ (Var x) = just (m , (m , (refl , (anil , (lookup x Γ)))))
infer2 Γ (Lam s) = {!!}
infer2 Γ (App s1 s2) = {!!}
