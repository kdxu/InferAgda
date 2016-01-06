module infer where

open import nat
open import mgu
open import term

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_+_; _≤_)
open import Data.Vec
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------

mutual
  infer : (m : ℕ) → {n : ℕ} → (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m'' ∈ ℕ ]
                Σ[ m' ∈ ℕ ]
                Σ[ m≤m'' ∈ m ≤ m'' ]
                Σ[ σ ∈ AListType m'' m' ]
                Σ[ τ ∈ Type m' ]
                Σ[ w ∈ WellTypedTerm (substCxt≤ σ m≤m'' Γ) τ ]
                erase w ≡ s)
  infer m Γ (Var x) = infer-Var m Γ x
  infer m Γ (Lam s) = infer-Lam m Γ s
  infer m Γ (App s1 s2) = infer-App m Γ s1 s2
  infer m Γ (Fst s) = infer-Fst m Γ s
  infer m Γ (Snd s) = infer-Snd m Γ s
  infer m Γ (Cons s1 s2) = infer-Cons m Γ s1 s2

  infer-Var : (m : ℕ) → {n : ℕ} → (Γ : Cxt {m} n) → (x : Fin n) →
         Maybe (Σ[ m'' ∈ ℕ ]
                Σ[ m' ∈ ℕ ]
                Σ[ m≤m'' ∈ m ≤ m'' ]
                Σ[ σ ∈ AListType m'' m' ]
                Σ[ τ ∈ Type m' ]
                Σ[ w ∈ WellTypedTerm (substCxt≤ σ m≤m'' Γ) τ ]
                erase w ≡ Var x)
  infer-Var m Γ x = just (m , m , m≤m m , anil , τ , VarX , eq)
    where
      τ : Type m
      τ = lookup x Γ
      VarX : WellTypedTerm (substCxt≤ anil (m≤m m) Γ) τ
      VarX rewrite substCxt≤Anil Γ (m≤m m) = Var x
      eq : erase VarX ≡ Var x
      eq rewrite substCxt≤Anil Γ (m≤m m) = refl

  infer-Lam : (m : ℕ) → {n : ℕ} → (Γ : Cxt {m} n) → (s : WellScopedTerm (suc n)) →
         Maybe (Σ[ m'' ∈ ℕ ]
                Σ[ m' ∈ ℕ ]
                Σ[ m≤m'' ∈ m ≤ m'' ]
                Σ[ σ ∈ AListType m'' m' ]
                Σ[ τ ∈ Type m' ]
                Σ[ w ∈ WellTypedTerm (substCxt≤ σ m≤m'' Γ) τ ]
                erase w ≡ Lam s)
  infer-Lam m {n} Γ s
    with let tx : Type (suc m)
             tx = TVar (fromℕ m) -- new type variable
             Γ' : Cxt {suc m} n
             Γ' = liftCxt 1 Γ
         in infer (suc m) (tx ∷ Γ') s
  ... | nothing = nothing
  ... | just (m'' , m' , 1+m≤m'' , σ , τ , w , eraseW≡S) =
    just (m'' , m' , m≤m'' , σ , tx' ⇒ τ , LamW , eraseLamW≡LamS)
    where
      tx : Type (suc m) -- the same as above
      tx = TVar (fromℕ m)
      Γ' : Cxt {suc m} n -- the same as above
      Γ' = liftCxt 1 Γ
      m≤m'' : m ≤ m'' -- m ≤ 1 + m ≤ m''
      m≤m'' = ≤-trans (n≤m+n 1 m) 1+m≤m''
      tx' : Type m'
      tx' = substType≤ σ 1+m≤m'' tx
      σΓ'≡σΓ : substCxt≤ σ 1+m≤m'' Γ' ≡ substCxt≤ σ m≤m'' Γ
      σΓ'≡σΓ = substCxt≤+1 Γ 1+m≤m'' m≤m'' σ
      LamW : WellTypedTerm (substCxt≤ σ m≤m'' Γ) (tx' ⇒ τ)
      LamW rewrite sym σΓ'≡σΓ = Lam tx' w
      eraseLamW≡LamS : erase LamW ≡ Lam s
      eraseLamW≡LamS rewrite sym σΓ'≡σΓ = cong Lam eraseW≡S

  infer-App : (m : ℕ) → {n : ℕ} → (Γ : Cxt {m} n) → (s1 s2 : WellScopedTerm n) →
         Maybe (Σ[ m'' ∈ ℕ ]
                Σ[ m' ∈ ℕ ]
                Σ[ m≤m'' ∈ m ≤ m'' ]
                Σ[ σ ∈ AListType m'' m' ]
                Σ[ τ ∈ Type m' ]
                Σ[ w ∈ WellTypedTerm (substCxt≤ σ m≤m'' Γ) τ ]
                erase w ≡ App s1 s2)
  infer-App m {n} Γ s1 s2
    with infer m Γ s1
  ... | nothing = nothing
  ... | just (m1'' , m1' , m≤m1'' , σ1 , t1 , w1 , eraseW1≡S1)
    with let σ1Γ : Cxt {m1'} n
             σ1Γ = substCxt≤ σ1 m≤m1'' Γ
         in infer m1' σ1Γ s2
  ... | nothing = nothing
  ... | just (m2'' , m2' , m1'≤m2'' , σ2 , t2 , w2 , eraseW2≡S2)
    with let t : Type (suc m2')
             t = TVar (fromℕ m2') -- new type variable
             σ2t1 : Type m2'
             σ2t1 = substType≤ σ2 m1'≤m2'' t1
         in mgu2 (liftType≤ (n≤m+n 1 m2') σ2t1) (liftType≤ (n≤m+n 1 m2') t2 ⇒ t)
  ... | nothing = nothing
  ... | just (m3' , σ3 , σ3σ2t1≡σ3t2⇒σ3t) =
    just (m3'' , m3' , m≤m3'' , σ , σ3t , AppW1W2 , eraseAppW1W2≡AppS1S2)
    where
      m3'' : ℕ
      m3'' = suc m2' ∸ m2' + (m2'' ∸ m1' + m1'')
      m≤m2''∸m1'+m1'' : m ≤ m2'' ∸ m1' + m1''
      m≤m2''∸m1'+m1'' =
        begin m    ≤⟨ m≤m1'' ⟩
              m1'' ≤⟨ n≤m+n (m2'' ∸ m1') m1'' ⟩
              m2'' ∸ m1' + m1''
        ∎ where open ≤-Reasoning
      m≤m3'' : m ≤ m3''
      m≤m3'' = begin m                 ≤⟨ m≤m2''∸m1'+m1'' ⟩
                     m2'' ∸ m1' + m1'' ≤⟨ n≤m+n (suc m2' ∸ m2') (m2'' ∸ m1' + m1'') ⟩
                     m3'' ∎ where open ≤-Reasoning
      σ21 : AListType (m2'' ∸ m1' + m1'') m2'
      σ21 = σ2 +⟨ m1'≤m2'' ⟩ σ1
      σ : AListType m3'' m3'
      σ = σ3 +⟨ n≤m+n 1 m2' ⟩ σ21
      -- Γ
      σ1Γ : Cxt {m1'} n -- the same as above
      σ1Γ = substCxt≤ σ1 m≤m1'' Γ
      σ2σ1Γ : Cxt {m2'} n
      σ2σ1Γ = substCxt≤ σ2 m1'≤m2'' σ1Γ
      σ21Γ : Cxt {m2'} n
      σ21Γ = substCxt≤ (σ2 +⟨ m1'≤m2'' ⟩ σ1) m≤m2''∸m1'+m1'' Γ
      σ21Γ≡σ2σ1Γ : σ21Γ ≡ σ2σ1Γ
      σ21Γ≡σ2σ1Γ = begin
          σ21Γ
        ≡⟨ substCxtTrans Γ σ1 σ2 σ21 m≤m1'' m1'≤m2'' m≤m2''∸m1'+m1'' refl ⟩
          σ2σ1Γ
        ∎ where open ≡-Reasoning
      σ3σ2σ1Γ : Cxt {m3'} n
      σ3σ2σ1Γ = substCxt≤ σ3 (n≤m+n 1 m2') σ2σ1Γ
      σΓ : Cxt {m3'} n
      σΓ = substCxt≤ σ m≤m3'' Γ
      σΓ≡σ3σ2σ1Γ : σΓ ≡ σ3σ2σ1Γ
      σΓ≡σ3σ2σ1Γ = begin
          σΓ
        ≡⟨ substCxtTrans Γ σ21 σ3 σ m≤m2''∸m1'+m1'' (n≤m+n 1 m2') m≤m3'' refl ⟩
          substCxt≤ σ3 (n≤m+n 1 m2') σ21Γ
        ≡⟨ cong (substCxt≤ σ3 (n≤m+n 1 m2')) σ21Γ≡σ2σ1Γ ⟩
          σ3σ2σ1Γ
        ∎ where open ≡-Reasoning
      -- w1
      σ2t1 : Type m2' -- the same as above
      σ2t1 = substType≤ σ2 m1'≤m2'' t1
      σ3σ2t1 : Type m3'
      σ3σ2t1 = substType≤ σ3 (n≤m+n 1 m2') σ2t1
      σ2w1 : WellTypedTerm σ2σ1Γ σ2t1
      σ2w1 = substWTerm≤ σ2 m1'≤m2'' w1
      σ3σ2w1 : WellTypedTerm σ3σ2σ1Γ σ3σ2t1
      σ3σ2w1 = substWTerm≤ σ3 (n≤m+n 1 m2') σ2w1
      -- w2
      σ3t2 : Type m3'
      σ3t2 = substType≤ σ3 (n≤m+n 1 m2') t2
      σ3w2 : WellTypedTerm σ3σ2σ1Γ σ3t2
      σ3w2 = substWTerm≤ σ3 (n≤m+n 1 m2') w2
      -- mgu
      t : Type (suc m2') -- the same as above
      t = TVar (fromℕ m2')
      σ3t : Type m3'
      σ3t = substType σ3 t
      σ3t2⇒σ3t≡σ3σ2t1 : σ3t2 ⇒ σ3t ≡ σ3σ2t1
      σ3t2⇒σ3t≡σ3σ2t1 = sym σ3σ2t1≡σ3t2⇒σ3t
      -- App w1 w2
      W1 : WellTypedTerm σΓ (σ3t2 ⇒ σ3t)
      W1 rewrite σΓ≡σ3σ2σ1Γ | σ3t2⇒σ3t≡σ3σ2t1 = σ3σ2w1
      W2 : WellTypedTerm σΓ σ3t2
      W2 rewrite σΓ≡σ3σ2σ1Γ = σ3w2
      AppW1W2 : WellTypedTerm σΓ σ3t
      AppW1W2 = App W1 W2
      -- erase
      eraseAppW1W2≡AppS1S2 : erase AppW1W2 ≡ App s1 s2
      eraseAppW1W2≡AppS1S2
        rewrite σΓ≡σ3σ2σ1Γ | σ3t2⇒σ3t≡σ3σ2t1
              | eraseSubstWTerm≤ σ3 (n≤m+n 1 m2') σ2w1
              | eraseSubstWTerm≤ σ2 m1'≤m2'' w1
              | eraseSubstWTerm≤ σ3 (n≤m+n 1 m2') w2 =
        cong₂ App eraseW1≡S1 eraseW2≡S2

  infer-Fst : (m : ℕ) → {n : ℕ} → (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m'' ∈ ℕ ]
                Σ[ m' ∈ ℕ ]
                Σ[ m≤m'' ∈ m ≤ m'' ]
                Σ[ σ ∈ AListType m'' m' ]
                Σ[ τ ∈ Type m' ]
                Σ[ w ∈ WellTypedTerm (substCxt≤ σ m≤m'' Γ) τ ]
                erase w ≡ Fst s)
  infer-Fst m {n} Γ s
    with infer m Γ s
  ... | nothing = nothing
  ... | just (m1'' , m1' , m≤m1'' , σ1 , t , w , eraseW≡S)
    with let t1 : Type (suc (suc m1')) -- new type variable
             t1 = liftType≤ (n≤m+n 1 (suc m1')) (TVar (fromℕ m1'))
             t2 : Type (suc (suc m1')) -- new type variable
             t2 = TVar (fromℕ (suc m1'))
         in mgu2 (liftType≤ (n≤m+n 2 m1') t) (t1 ∏ t2)
  ... | nothing = nothing
  ... | just (m2' , σ2 , σ2t≡σ2t1∏σ2t2) =
    just (m2'' , m2' , m≤m2'' , σ , σ2t1 , FstW , eraseFstW≡FstS)
    where
      m2'' : ℕ
      m2'' = suc (suc m1') ∸ m1' + m1''
      m≤m2'' : m ≤ m2''
      m≤m2'' =
        begin m    ≤⟨ m≤m1'' ⟩
              m1'' ≤⟨ n≤m+n (suc (suc m1') ∸ m1') m1'' ⟩
              suc (suc m1') ∸ m1' + m1''
        ∎ where open ≤-Reasoning
      σ : AListType (suc (suc m1') ∸ m1' + m1'') m2'
      σ = σ2 +⟨ n≤m+n 2 m1' ⟩ σ1
      -- Γ
      σ1Γ : Cxt {m1'} n
      σ1Γ = substCxt≤ σ1 m≤m1'' Γ
      σ2σ1Γ : Cxt {m2'} n
      σ2σ1Γ = substCxt≤ σ2 (n≤m+n 2 m1') σ1Γ
      σΓ : Cxt {m2'} n
      σΓ = substCxt≤ σ m≤m2'' Γ
      σΓ≡σ2σ1Γ : σΓ ≡ σ2σ1Γ
      σΓ≡σ2σ1Γ = begin
          σΓ
        ≡⟨ substCxtTrans Γ σ1 σ2 σ m≤m1'' (n≤m+n 2 m1') m≤m2'' refl ⟩
          σ2σ1Γ
        ∎ where open ≡-Reasoning
      -- w
      σ2t : Type m2'
      σ2t = substType≤ σ2 (n≤m+n 2 m1') t
      σ2w : WellTypedTerm σ2σ1Γ σ2t
      σ2w = substWTerm≤ σ2 (n≤m+n 2 m1') w
      -- mgu
      t1 : Type (suc (suc m1')) -- the same as above
      t1 = liftType≤ (n≤m+n 1 (suc m1')) (TVar (fromℕ m1'))
      σ2t1 : Type m2'
      σ2t1 = substType σ2 t1
      t2 : Type (suc (suc m1')) -- new same as above
      t2 = TVar (fromℕ (suc m1'))
      σ2t2 : Type m2'
      σ2t2 = substType σ2 t2
      σ2t1∏σ2t2'≡σ2t : σ2t1 ∏ σ2t2 ≡ σ2t
      σ2t1∏σ2t2'≡σ2t = sym σ2t≡σ2t1∏σ2t2
      -- Fst w
      W : WellTypedTerm σΓ (σ2t1 ∏ σ2t2)
      W rewrite σΓ≡σ2σ1Γ | σ2t1∏σ2t2'≡σ2t = σ2w
      FstW : WellTypedTerm σΓ σ2t1
      FstW = Fst W
      -- erase
      eraseFstW≡FstS : erase FstW ≡ Fst s
      eraseFstW≡FstS
        rewrite σΓ≡σ2σ1Γ | σ2t1∏σ2t2'≡σ2t
              | eraseSubstWTerm≤ σ2 (n≤m+n 2 m1') w =
        cong Fst eraseW≡S

  infer-Snd : (m : ℕ) → {n : ℕ} → (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m'' ∈ ℕ ]
                Σ[ m' ∈ ℕ ]
                Σ[ m≤m'' ∈ m ≤ m'' ]
                Σ[ σ ∈ AListType m'' m' ]
                Σ[ τ ∈ Type m' ]
                Σ[ w ∈ WellTypedTerm (substCxt≤ σ m≤m'' Γ) τ ]
                erase w ≡ Snd s)
  infer-Snd m {n} Γ s
    with infer m Γ s
  ... | nothing = nothing
  ... | just (m1'' , m1' , m≤m1'' , σ1 , t , w , eraseW≡S)
    with let t1 : Type (suc (suc m1')) -- new type variable
             t1 = liftType≤ (n≤m+n 1 (suc m1')) (TVar (fromℕ m1'))
             t2 : Type (suc (suc m1')) -- new type variable
             t2 = TVar (fromℕ (suc m1'))
         in mgu2 (liftType≤ (n≤m+n 2 m1') t) (t1 ∏ t2)
  ... | nothing = nothing
  ... | just (m2' , σ2 , σ2t≡σ2t1∏σ2t2) =
    just (m2'' , m2' , m≤m2'' , σ , σ2t2 , SndW , eraseSndW≡SndS)
    where
      m2'' : ℕ
      m2'' = suc (suc m1') ∸ m1' + m1''
      m≤m2'' : m ≤ m2''
      m≤m2'' =
        begin m    ≤⟨ m≤m1'' ⟩
              m1'' ≤⟨ n≤m+n (suc (suc m1') ∸ m1') m1'' ⟩
              suc (suc m1') ∸ m1' + m1''
        ∎ where open ≤-Reasoning
      σ : AListType (suc (suc m1') ∸ m1' + m1'') m2'
      σ = σ2 +⟨ n≤m+n 2 m1' ⟩ σ1
      -- Γ
      σ1Γ : Cxt {m1'} n
      σ1Γ = substCxt≤ σ1 m≤m1'' Γ
      σ2σ1Γ : Cxt {m2'} n
      σ2σ1Γ = substCxt≤ σ2 (n≤m+n 2 m1') σ1Γ
      σΓ : Cxt {m2'} n
      σΓ = substCxt≤ σ m≤m2'' Γ
      σΓ≡σ2σ1Γ : σΓ ≡ σ2σ1Γ
      σΓ≡σ2σ1Γ = begin
          σΓ
        ≡⟨ substCxtTrans Γ σ1 σ2 σ m≤m1'' (n≤m+n 2 m1') m≤m2'' refl ⟩
          σ2σ1Γ
        ∎ where open ≡-Reasoning
      -- w
      σ2t : Type m2'
      σ2t = substType≤ σ2 (n≤m+n 2 m1') t
      σ2w : WellTypedTerm σ2σ1Γ σ2t
      σ2w = substWTerm≤ σ2 (n≤m+n 2 m1') w
      -- mgu
      t1 : Type (suc (suc m1')) -- the same as above
      t1 = liftType≤ (n≤m+n 1 (suc m1')) (TVar (fromℕ m1'))
      σ2t1 : Type m2'
      σ2t1 = substType σ2 t1
      t2 : Type (suc (suc m1')) -- new same as above
      t2 = TVar (fromℕ (suc m1'))
      σ2t2 : Type m2'
      σ2t2 = substType σ2 t2
      σ2t1∏σ2t2'≡σ2t : σ2t1 ∏ σ2t2 ≡ σ2t
      σ2t1∏σ2t2'≡σ2t = sym σ2t≡σ2t1∏σ2t2
      -- Snd w
      W : WellTypedTerm σΓ (σ2t1 ∏ σ2t2)
      W rewrite σΓ≡σ2σ1Γ | σ2t1∏σ2t2'≡σ2t = σ2w
      SndW : WellTypedTerm σΓ σ2t2
      SndW = Snd W
      -- erase
      eraseSndW≡SndS : erase SndW ≡ Snd s
      eraseSndW≡SndS
        rewrite σΓ≡σ2σ1Γ | σ2t1∏σ2t2'≡σ2t
              | eraseSubstWTerm≤ σ2 (n≤m+n 2 m1') w =
        cong Snd eraseW≡S

  infer-Cons : (m : ℕ) → {n : ℕ} → (Γ : Cxt {m} n) → (s1 s2 : WellScopedTerm n) →
         Maybe (Σ[ m'' ∈ ℕ ]
                Σ[ m' ∈ ℕ ]
                Σ[ m≤m'' ∈ m ≤ m'' ]
                Σ[ σ ∈ AListType m'' m' ]
                Σ[ τ ∈ Type m' ]
                Σ[ w ∈ WellTypedTerm (substCxt≤ σ m≤m'' Γ) τ ]
                erase w ≡ Cons s1 s2)
  infer-Cons m {n} Γ s1 s2
    with infer m Γ s1
  ... | nothing = nothing
  ... | just (m1'' , m1' , m≤m1'' , σ1 , t1 , w1 , eraseW1≡S1)
    with let σ1Γ : Cxt {m1'} n
             σ1Γ = substCxt≤ σ1 m≤m1'' Γ
         in infer m1' σ1Γ s2
  ... | nothing = nothing
  ... | just (m2'' , m2' , m1'≤m2'' , σ2 , t2 , w2 , eraseW2≡S2) =
    just (m2'' ∸ m1' + m1'' , m2' , m≤m2''∸m1'+m1'' , σ , τ , ConsW1W2 , eraseConsW1W2≡ConsS1S2)
    where
      m≤m2''∸m1'+m1'' : m ≤ m2'' ∸ m1' + m1''
      m≤m2''∸m1'+m1'' =
        begin m    ≤⟨ m≤m1'' ⟩
              m1'' ≤⟨ n≤m+n (m2'' ∸ m1') m1'' ⟩
              m2'' ∸ m1' + m1''
        ∎ where open ≤-Reasoning
      σ : AListType (m2'' ∸ m1' + m1'') m2'
      σ = σ2 +⟨ m1'≤m2'' ⟩ σ1
      -- Γ
      σ1Γ : Cxt {m1'} n -- the same as above
      σ1Γ = substCxt≤ σ1 m≤m1'' Γ
      σ2σ1Γ : Cxt {m2'} n
      σ2σ1Γ = substCxt≤ σ2 m1'≤m2'' σ1Γ
      σΓ : Cxt {m2'} n
      σΓ = substCxt≤ σ m≤m2''∸m1'+m1'' Γ
      σΓ≡σ2σ1Γ : σΓ ≡ σ2σ1Γ
      σΓ≡σ2σ1Γ = begin
          σΓ
        ≡⟨ substCxtTrans Γ σ1 σ2 σ m≤m1'' m1'≤m2'' m≤m2''∸m1'+m1'' refl ⟩
          σ2σ1Γ
        ∎ where open ≡-Reasoning
      -- w1
      σ2t1 : Type m2'
      σ2t1 = substType≤ σ2 m1'≤m2'' t1
      σ2w1 : WellTypedTerm σ2σ1Γ σ2t1
      σ2w1 = substWTerm≤ σ2 m1'≤m2'' w1
      -- w2
   -- w2 : WellTypedTerm σ2σ1Γ t2
   -- w2 = w2
      -- Cons w1 w2
      W1 : WellTypedTerm σΓ σ2t1
      W1 rewrite σΓ≡σ2σ1Γ = σ2w1
      W2 : WellTypedTerm σΓ t2
      W2 rewrite σΓ≡σ2σ1Γ = w2
      τ : Type m2'
      τ = σ2t1 ∏ t2
      ConsW1W2 : WellTypedTerm σΓ τ
      ConsW1W2 = Cons W1 W2
      -- erase
      eraseConsW1W2≡ConsS1S2 : erase ConsW1W2 ≡ Cons s1 s2
      eraseConsW1W2≡ConsS1S2
        rewrite σΓ≡σ2σ1Γ
              | eraseSubstWTerm≤ σ2 m1'≤m2'' w1
        = cong₂ Cons eraseW1≡S1 eraseW2≡S2
