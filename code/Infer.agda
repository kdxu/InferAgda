module Infer where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_+_; _≤_)
open import Data.Vec
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import lib
open import Term

--------------------------------------------------------------------------------

{-
infer : {m n : ℕ} →  (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m' ∈ ℕ ] AList (count s + m) m' × Type m')
         -- infer : {m n : ℕ} →  (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
            -- Maybe (Σ[ m' ∈ ℕ ] Σ[ m'' ∈ ℕ ] (m'' ≡ count s + m) × AList m'' m' × Type m')
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
          = liftAList (suc (count s2)) σ'
        σ2' : AList (suc (count s2 + m1)) (suc m2)
        σ2' = liftAList 1 σ2
--}
liftCxt≤ : {m m' n : ℕ} → (m ≤ m') → Cxt {m} n → Cxt {m'} n
liftCxt≤ {m} {m'} {n} leq Γ = Data.Vec.map (▹◃ (λ x → inject≤ x leq)) Γ -- Data.Vec.map (▹◃ (inject+' m')) Γ

substCxt≤ :{m m' m'' n : ℕ} → AList m m' → m'' ≤ m → Cxt {m''} n → Cxt {m'} n
substCxt≤ σ leq Γ = substCxt σ (liftCxt≤ leq Γ)

-- liftType m' t : t の中の型変数の数を m' だけ増やす
liftType≤ : {m m' : ℕ} → m ≤ m' → Type m → Type m'
liftType≤ leq t = ▹◃ (λ x → inject≤ x leq) t --▹◃ (inject+' m') t

substType≤ : {m m' m'' : ℕ} → AList m m' → m'' ≤ m → Type m'' → Type m'
substType≤ σ leq t = substType σ (liftType≤ leq t) --sub σ ◃ t


--liftAList : {m m' : ℕ} {m'≤′m : m' ≤′ m} → (n : ℕ) → AList m'≤′m → AList (k+n≤′k+m n m'≤′m)
--liftAList zero σ = σ
--liftAList (suc n) σ = liftAList1 (liftAList n σ)
--m'-m = d
--d + m = m'
-- n≤m+n∸m


n≡m+n∸m : (m n : ℕ) → (m ≤ n) → n ≡ m + (n ∸ m)
n≡m+n∸m zero n leq = refl
n≡m+n∸m (suc m) zero ()
n≡m+n∸m (suc m) (suc n) (s≤s leq) = cong suc (n≡m+n∸m m n leq) 

liftAList≤ : {m m'  n : ℕ} → (ρ : AList m n) → (m ≤ m') →  AList m' (n + (m' ∸ m))
liftAList≤ {m} {m'} {.m} (anil {m = .m}) leq rewrite sym (n≡m+n∸m m m' leq) = anil
liftAList≤ {suc m} {suc m'} (r asnoc t' / x) (s≤s leq) = (liftAList≤ r leq) asnoc (liftType≤ leq t') / (inject≤ x (s≤s leq))


-- ふたつの代入を不等号付きでくっつける
_++<_>_ : {l m m' n : ℕ} → (ρ : AList m n) → (m ≤ m') → (σ : AList l m') →  AList l (n + (m' ∸ m))
ρ ++< leq > σ = liftAList≤ ρ leq +!+ σ

infer2 : {m n : ℕ} → (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m' ∈ ℕ ] Σ[ m'' ∈ ℕ ] (m'' ≡ count s + m) × AList m'' m' ×  Type m')

infer2 {m} Γ (Var x) = just (m , (m , (refl , (anil , (lookup x Γ)))))
infer2 {m} Γ (Lam s) with infer2 (TVar (fromℕ m) ∷ liftCxt 1 Γ) s
infer2 Γ (Lam s) | nothing = nothing
infer2 {m} Γ (Lam s) | just (m' , m'' , eq , σ , t) = just (m' , (m'' , (eq' , (σ , t)))) 
       where eq' : (m'' ≡ suc (count s + m))
             eq' = begin 
                      m''
                   ≡⟨ eq ⟩
                     count s + suc m
                   ≡⟨ +-suc (count s) m ⟩
                     suc (count s + m)
                   ∎
infer2 {m} Γ (App s1 s2) with infer2 Γ s1
infer2 Γ (App s1 s2) | nothing = nothing
infer2 {m} Γ (App s1 s2) | just (m' , m'' , eq , σ , t)  with infer2 (substCxt≤ σ leq Γ) s2 -- liftcxt wo kutikusuru
       where leq : m ≤ m''
             leq rewrite eq = n≤m+n (count s1) m 
-- m'' ≤ m , m' ≡  (m'' - (m - m'))
-- substCxtが中で勝手にLift する
infer2 Γ (App s1 s2) | just (m' , m'' , eq , σ , t) | nothing = nothing
infer2 Γ (App s1 s2) | just (m' , m'' , eq , σ , t) | just (m2' , m2'' , eq2 , σ2 , t2) with unify (liftType 1 (substType≤ σ2 leq1 t)) (liftType 1 t2 ⇒ TVar (fromℕ m2'))
      where leq1 : m' ≤ m2''
            leq1 rewrite eq2 = n≤m+n (count s2) m'
infer2 Γ (App s1 s2) | just (m' , m'' , eq , σ , t) | just (m2' , m2'' , eq2 , σ2 , t2) | nothing = nothing
infer2 Γ (App s1 s2) | just (m' , m'' , eq , σ , t) | just (m2' , m2'' , eq2 , σ2 , t2) | just (m3 , σ3) = just (m3 , {!!} , ({!!} , ({!!} , (substType σ3 (TVar (fromℕ m2'))))))
--  just (m3 , σ3 +!+ (σ2' +!+ σ1') , substType σ3 (TVar (fromℕ m2))) 
--  where σ1' : AList (count s1 + suc (count s2) + m) (suc (count s2 + m1))
--        σ1' rewrite +-comm (count s1) (suc (count s2)) | +-assoc (count s2) (count s1) m
--          = liftAList (suc (count s2)) σ'
--        σ2' : AList (suc (count s2 + m1)) (suc m2)
--        σ2' = liftAList 1 σ2

