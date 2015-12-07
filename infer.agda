module infer where

open import Data.Nat
open import Data.Vec
open import Data.Vec.Properties
open import Data.Product
open import Data.Fin hiding (_+_; _≤_)
open import Data.Maybe
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Nat.Properties
open import Algebra.Structures
open import Relation.Binary hiding (_⇒_)
private module M = IsCommutativeSemiring
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□)
open import Relation.Binary.HeterogeneousEquality
  renaming (sym to hsym; trans to htrans; cong to hcong; cong₂ to hcong₂; subst to hsubst; subst₂ to hsubst₂; refl to hrefl)
open import mgu
open import term

--------------------------------------------------------------------------------

m≤m :  ∀ m →  m ≤ m
m≤m zero = z≤n
m≤m (suc m) = s≤s (m≤m m)

m≤m' :  ∀ m m' →  m ≤ m' →  m ≤ suc m'
m≤m' zero m' x = z≤n
m≤m' (suc m) ._ (s≤s x) = s≤s (m≤m' m _ x)

m≤m'≡k+m≤k+m' :  ∀ k m m' →  m ≤ m' → k + m ≤ k + m'
m≤m'≡k+m≤k+m' zero m m' x = x
m≤m'≡k+m≤k+m' (suc k) m m' x = s≤s (m≤m'≡k+m≤k+m' k m m' x)

m≤m'≡k'+m≤k+m :  ∀ k k' m →  k ≤ k' → k + m ≤ k' + m
m≤m'≡k'+m≤k+m .0 zero m z≤n = m≤m m
m≤m'≡k'+m≤k+m zero (suc k') m leq = ≤-step (≤-steps k' (m≤m m))
m≤m'≡k'+m≤k+m (suc k) (suc k') m (s≤s leq) = s≤s (m≤m'≡k'+m≤k+m k k' m leq)

lemma : ∀ m1 → (suc (suc m1)) ∸ m1 ≡ suc (suc (m1 ∸ m1))
lemma zero = refl
lemma (suc m1) = cong (λ x → x) (lemma m1)

m≤m'≡k+m≤k'+m' :  ∀ k k'  m m' →  m ≤ m' → k ≤ k' →  (k + m ≤ k' + m')
m≤m'≡k+m≤k'+m' k k' m m' leq leq2  =
          start
            k + m
          ≤⟨ m≤m'≡k+m≤k+m' k m m' leq ⟩
            k + m'
          ≤⟨ m≤m'≡k'+m≤k+m k k' m' leq2 ⟩
            k' + m'
           □

≡-to-≤ : ∀ m m' → m ≡ m' → m ≤ m'
≡-to-≤ zero .0 refl = z≤n
≡-to-≤ (suc m) zero ()
≡-to-≤ (suc m) (suc .m) refl = s≤s (≡-to-≤ m m refl)

hcong₂' : ∀ {a b c d} {I J : Set a} {i1 i2 : I} {j1 j2 : J}
          (A : I → Set b)
          (B : {i : I} → (j : J) → A i → Set c)
          {C : {i : I} → (x : A i) → {j : J} → B j x → Set d}
          {x : A i1} {y : A i2} {u : B j1 x} {v : B j2 y} →
        i1 ≡ i2 → j1 ≡ j2 →
        (f : {i : I} → {j : J} → (x : A i) → (y : B j x) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
hcong₂' _ _ refl refl f hrefl hrefl = hrefl

-- liftType≤+k : {m m' : ℕ} → (k : ℕ) → (x : Type m) → (k+m≤m' : k + m ≤ m') → (m≤m' : m ≤ m') →
--           liftType≤ k+m≤m' (liftType k x) ≡ liftType≤ m≤m' x
-- liftType≤+k k x k+m≤m' m≤m' = {!refl!}

substCxt≤+1 : {m m' m''  n : ℕ} → (Γ : Cxt {m} n) → (leq : suc m ≤ m'') → (leq' : m ≤ m'') → (σ : AListType m'' m') → substCxt≤ σ leq (liftCxt 1 Γ) ≡ substCxt≤ σ leq' Γ
substCxt≤+1 [] leq leq' σ = refl
substCxt≤+1 (x ∷ Γ) leq leq' σ = cong₂ _∷_ (cong (substType σ) (liftType≤add 1 x leq leq')) (substCxt≤+1 Γ leq leq' σ)

infer : (m : ℕ) → {n : ℕ} → (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m'' ∈ ℕ ]
                Σ[ m' ∈ ℕ ]
                Σ[ m≤m'' ∈ m ≤ m'' ]
                Σ[ σ ∈ AListType m'' m' ]
                Σ[ τ ∈ Type m' ]
                WellTypedTerm (substCxt≤ σ m≤m'' Γ) τ)
infer m Γ (Var x) = just (m , (m , ((n≤m+n 0 m) , (anil , ((lookup x Γ) , VarX)))))
   where
     VarX : WellTypedTerm (substCxt≤ anil (n≤m+n 0 m) Γ) (lookup x Γ)
     VarX rewrite substCxt≤Anil Γ (n≤m+n 0 m) = Var x
infer m Γ (Lam s) with infer (suc m) (TVar (fromℕ m) ∷ liftCxt 1 Γ)
         s
... | just  (m'' , m' , leq , σ , t , w) =
  just (m'' , (m' , (leq' , (σ , (tx ⇒ t , LamS)))))
  where
    leq' : m ≤ m''
    leq' = DecTotalOrder.trans decTotalOrder (n≤m+n 1 m) leq

    tx : Type m'
    tx = substType≤ σ leq (TVar (fromℕ m))

    LamS : WellTypedTerm (substCxt≤ σ leq' Γ) (tx ⇒ t)
    LamS = Lam (mvar-sub σ (inject≤ (fromℕ m) leq)) w'
     where
        w' : WellTypedTerm (tx ∷ substCxt≤ σ leq' Γ) t
        w' = subst (λ l → WellTypedTerm (tx ∷ l) t) eq w
           where eq : substCxt≤ σ leq (liftCxt 1 Γ) ≡ substCxt≤ σ leq' Γ
                 eq = substCxt≤+1 Γ leq leq' σ

infer m Γ (Lam s) | nothing = nothing
infer m Γ (App s1 s2) with infer m Γ s1
infer m Γ (App s1 s2)  | just (m'' , m' , leq , σ , t , w) with
         infer m' (substCxt σ (liftCxt≤ leq Γ)) s2
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | nothing = nothing
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just
         (m1'' , m1' , leq1 , σ1 , t1 , w1) with mgu (liftType 1
         (substType σ1 (liftType≤ leq1 t))) (liftType 1 t1 ⇒ TVar
         (fromℕ m1'))
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just (m1'' , m1' , leq1 , σ1 , t1 , w1) | just (m2 , σ2) = just (suc m1' ∸ m1' + (m1'' ∸ m' + m'') , (m2 , (leq2 , (σ2 +⟨ n≤m+n 1 m1' ⟩ (σ1 +⟨ leq1 ⟩ σ) , (substType σ2 (TVar (fromℕ m1')) , AppS1S2)))))
  where
    leq2 : m ≤ suc m1' ∸ m1' + (m1'' ∸ m' + m'')
    leq2 = start
                m
              ≤⟨ leq ⟩
                m''
              ≤⟨ n≤m+n (m1'' ∸ m') m'' ⟩
                m1'' ∸ m' + m''
              ≤⟨ n≤m+n (suc m1' ∸ m1') (m1'' ∸ m' + m'') ⟩
                suc m1' ∸ m1' + (m1'' ∸ m' + m'')
               □
    AppS1S2 : WellTypedTerm (substCxt≤ (σ2 +⟨ n≤m+n 1 m1' ⟩ (σ1 +⟨ leq1 ⟩ σ)) leq2 Γ) (substType σ2 (TVar (fromℕ m1')))
    AppS1S2 = App s1' s2'
            where
              s1' : WellTypedTerm (substCxt≤ (σ2 +⟨ (n≤m+n 1 m1') ⟩ (σ1 +⟨ leq1 ⟩ σ)) leq2 Γ) (substType σ2 {! substCxt≤ σ m≤m'' Γ) τ  !})
              s1' = {!   !}
              s2' : WellTypedTerm {!   !} {!   !}
              s2' = {!   !}

infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just (m1'' , m1' , leq1 , σ1 , t1 , w1) | nothing = nothing
infer m Γ (App s1 s2) | nothing = nothing
infer m Γ (Fst s)
    with infer m Γ s
... | nothing = nothing
... | just (m1' , m1 , m≦m1' , σ , t1 , w)
    with mgu  (liftType 2 t1)  (liftType 1 (TVar (fromℕ m1)) ∏ ((TVar (fromℕ (suc m1)))))
... | nothing = nothing
... | just (m2 , σ2) =
    just (suc (suc m1) ∸ m1 + m1' , (m2 , (leq' , (σ' , ( τ , FstW)))))
    where
          leq' : m ≤ (suc (suc m1) ∸ m1) + m1'
          leq' =　start
                      m
                    ≤⟨ m≦m1' ⟩
                      m1'
                    ≤⟨ ≡-to-≤ m1' m1' refl ⟩
                      zero + m1'
                    ≤⟨ m≤m'≡k'+m≤k+m zero (suc (suc m1) ∸ m1) m1' z≤n ⟩
                      (suc (suc m1) ∸ m1) + m1'
                  □
          τ : Fix (base :+: rec :*: rec :+: rec :*: rec) m2
          τ = substType σ2 (TVar (fromℕ (suc m1)))
          σ' : AListType (suc (suc m1) ∸ m1 + m1') m2
          σ' = σ2 +⟨ ≤-steps 2 (n≤m+n 0 m1) ⟩ σ
          w' : WellTypedTerm (substCxt≤ σ m≦m1' Γ) t1
          w' = w
          W : WellTypedTerm (substCxt≤ σ' leq' Γ) {!   !}
          W = {!   !}
          FstW : WellTypedTerm (substCxt≤ σ' leq' Γ) τ
          FstW = Fst W
infer m Γ (Snd s) = {!   !}
infer m Γ (Cons t1 t2) = {!   !}
