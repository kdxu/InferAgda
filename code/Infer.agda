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

n≡m+n∸m : (m n : ℕ) → (m ≤ n) → n ≡ m + (n ∸ m)
n≡m+n∸m zero n leq = refl
n≡m+n∸m (suc m) zero ()
n≡m+n∸m (suc m) (suc n) (s≤s leq) = cong suc (n≡m+n∸m m n leq) 

liftAList≤ : {l m m' : ℕ} → (σ : AList l m') → (m' ≤ m) →  AList (l + (m ∸ m')) m
liftAList≤ {l} {m} {.l} (anil {m = .l}) leq rewrite sym (n≡m+n∸m l m leq) = anil
liftAList≤ {.(suc m₁)} {m} {n} (_asnoc_/_ {m = m₁} {n = .n} σ t' x) leq = (liftAList≤ σ leq) asnoc (liftType≤ m₁≤m₁+m∸n t') / (inject≤ x (s≤s m₁≤m₁+m∸n))
  where m₁≤m₁+m∸n : m₁ ≤ m₁ + (m ∸ n)
        m₁≤m₁+m∸n = m≤m+n m₁ (m ∸ n)

-- ふたつの代入を不等号付きでくっつける
_++<_>_ : {l m m' n : ℕ} → (ρ : AList m n) → (m' ≤ m) → (σ : AList l m') →  AList (l + (m ∸ m')) n
ρ ++< leq > σ = ρ +!+ liftAList≤ σ leq -- liftAList≤ ρ leq +!+ σ

infer2 : {m n : ℕ} → (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m' ∈ ℕ ] Σ[ m'' ∈ ℕ ] (m'' ≡ count s + m) × AList m'' m' ×  Type m')

-- Maybe (Σ[ m' ∈ ℕ ] Σ[ m'' ∈ ℕ ] (m'' ≥ m')  × AList m'' m' ×  Type m')

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
infer2 {m} Γ (App s1 s2) | just (m' , m'' , eq , σ , t) | just (m2' , m2'' , eq2 , σ2 , t2) | just (m3 , σ3) = just (m3 , m'' + (m2'' ∸ m') + (suc m2' ∸ m2')   , (eq4 , ( σ3 ++< n≤1+n m2' > (σ2 ++< leq2 > σ)  , (substType σ3 (TVar (fromℕ m2'))))))
  where leq2 : m' ≤ m2''
        leq2 rewrite eq2 = n≤m+n (count s2) m'
        eq3 : suc (count s2 + m'') ≡ count s1 + suc (count s2) + m
        eq3 = sym
              (begin 
                count s1 + suc (count s2) + m
              ≡⟨ +-assoc (count s1) (suc (count s2)) m ⟩
              count s1 + (suc (count s2) + m)
              ≡⟨ cong (λ x → count s1 + x) (sym (+-comm m (suc (count s2)))) ⟩
                (count s1 + (m + suc (count s2)))
              ≡⟨ sym (+-assoc (count s1) m (suc (count s2))) ⟩
                (count s1 + m) + suc (count s2) 
              ≡⟨ cong (λ x → x + suc (count s2)) (sym eq) ⟩
                 m'' + suc (count s2)
              ≡⟨ +-suc m'' (count s2) ⟩
                suc (m'' + count s2)
              ≡⟨ cong suc (+-comm m'' (count s2)) ⟩
                suc (count s2 + m'')
              ∎)

        eq4 : m'' + (m2'' ∸ m') + (suc m2' ∸ m2') ≡ count s1 + suc (count s2) + m
        eq4 rewrite eq | eq2 | eq3 =
          begin
            count s1 + m + (count s2 + m' ∸ m') + (suc m2' ∸ m2')
          ≡⟨ cong (λ x → count s1 + m + x + (suc m2' ∸ m2')) (+-∸-assoc (count s2) (n≤m+n 0 m')) ⟩
            count s1 + m + (count s2 + (m' ∸ m')) + (suc m2' ∸ m2')
          ≡⟨ cong (λ x → count s1 + m + (count s2 + x) + (suc m2' ∸ m2')) (n∸n≡0 m') ⟩
            count s1 + m + (count s2 + 0) + (suc m2' ∸ m2')
          ≡⟨ cong (λ x → count s1 + m + x + (suc m2' ∸ m2')) (+-comm (count s2) 0) ⟩
            count s1 + m + (count s2) + (suc m2' ∸ m2')
          ≡⟨ refl ⟩
            count s1 + m + (count s2) + (1 + m2' ∸ m2')
          ≡⟨ cong (λ x → count s1 + m + count s2 + x) (+-∸-assoc 1 (n≤m+n 0 m2')) ⟩
            count s1 + m + (count s2) + (1 + (m2' ∸ m2'))
          ≡⟨ cong (λ x → count s1 + m + count s2 + (1 + x)) (n∸n≡0 m2') ⟩
            ((count s1 + m) + (count s2)) + 1
          ≡⟨ +-assoc (count s1 + m) (count s2) (suc zero) ⟩
            (count s1 + m) + ((count s2) + 1)
          ≡⟨ cong (λ x → count s1 + m + x) (+-comm (count s2) 1) ⟩
            count s1 + m + suc (count s2) 
          ≡⟨ +-assoc (count s1) m (suc (count s2)) ⟩
            count s1 + (m + suc (count s2))
          ≡⟨ cong (λ x → count s1 + x) (+-comm m (suc (count s2))) ⟩
            count s1 + (suc (count s2) + m)
          ≡⟨ sym (+-assoc (count s1) (suc (count s2)) m) ⟩
            count s1 + suc (count s2) + m
          ∎
