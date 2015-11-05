module infer where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_+_; _≤_; pred )
open import Data.Vec
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□)
open import mgu
open import term

--------------------------------------------------------------------------------

infer : (m : ℕ) → {n : ℕ} → (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m'' ∈ ℕ ] -- 3 C-c C-a
                Σ[ m' ∈ ℕ ] -- 3 C-c C-a
                Σ[ m≤m'' ∈ m ≤ m'' ] -- 4 証明すべきものは定まっているので、それを自分で証明する
                Σ[ σ ∈ AListType m'' m' ] -- 2
                Σ[ τ ∈ Type m' ] -- 1
                WellTypedTerm (substCxt≤ σ m≤m'' Γ) τ) -- 5 where 以下で作る
infer m Γ (Var x) = just (m , m , n≤m+n 0 m , anil , lookup x Γ , VarX)
  where
    VarX : WellTypedTerm (substCxt≤ anil (n≤m+n 0 m) Γ) (lookup x Γ)
    VarX = {!!}
infer m Γ (Lam s) with infer (suc m) (TVar (fromℕ m) ∷ liftCxt 1 Γ) s
infer m Γ (Lam s) | nothing = nothing
infer m Γ (Lam s) | just (m'' , m' , leq , σ , t , w)= just (m'' , (m' , (≤⇒pred≤ (suc m) m'' leq , (σ , (tx ⇒ t , {!!})))))
  where  tx : Type m'
         tx = substType≤ σ leq (TVar (fromℕ m))
infer m Γ (App s1 s2)  with infer m Γ s1
infer m Γ (App s1 s2) | nothing = nothing
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) with  infer m' (substCxt σ (liftCxt≤ leq Γ)) s2
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | nothing = nothing
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just (m1'' , m1' , leq1 , σ1 , t1 , w1) with mgu (liftType 1 (substType σ1 (liftType≤ leq1 t))) (liftType 1 t1 ⇒ TVar (fromℕ m1'))
infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just (m1'' , m1' , leq1 , σ1 , t1 , w1) | just (m2 , σ2)
          = just (suc m1' ∸ m1' + (m1'' ∸ m' + m'') , (m2 , (leq2 , (σ2 +⟨ n≤m+n 1 m1' ⟩ (σ1 +⟨ leq1 ⟩ σ) , (substType σ2 (TVar (fromℕ m1')) , {!!})))))
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

infer m Γ (App s1 s2) | just (m'' , m' , leq , σ , t , w) | just (m1'' , m1' , leq1 , σ1 , t1 , w1) | nothing = nothing

infer m Γ (Fst s) = {!!}
infer m Γ (Snd s) = {!!}
infer m Γ (Cons a b) = {!!}

{-
infer {m} Γ (Var x) = just (m , anil , lookup x Γ , VarX)
  where
    VarX  : WellTypedTerm (substCxt anil (liftCxt 0 Γ)) (lookup x Γ)
    VarX rewrite liftCxtZero Γ | substCxtAnil Γ = Var x
 -- Var x : WellTypedTerm Γ (lookup x Γ)
infer {m} {n} Γ (Lam s)
  with infer (TVar (fromℕ m) ∷ liftCxt 1 Γ) s -- TVar (fromℕ m) が引数の型
... | nothing = nothing -- s に型がつかなかった
... | just (m' , σ , t , w) =
  just (m' , σ' , tx ⇒ t , LamW)
  where σ' : AList (suc (count s + m)) m' 
        σ' = subst (λ m → AList m m') (+-suc (count s) m) σ
        tx : Type m'
        tx = substType σ (liftType (count s) (TVar (fromℕ m))) -- σ (↑s m)
        LamW : WellTypedTerm (substCxt σ' (liftCxt (count (Lam s)) Γ)) (tx ⇒ t)
        LamW = Lam tx w'
 tx : Type m'               where w' : WellTypedTerm (tx ∷ (substCxt σ' (liftCxt (count (Lam s)) Γ))) t
                  -- w  : WellTypedTerm (substCxt σ (liftCxt (count s) (TVar (fromℕ m) ∷ liftCxt 1 Γ))) t
                  --    = WellTypedTerm (substType σ (liftType (count s) (TVar (fromℕ m))) ∷
                  --                     substCxt  σ (liftCxt  (count s) (liftCxt 1 Γ))) t
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
... | just (m1 , σ1 , t1 , w1)
      with infer (substCxt σ1 (liftCxt (count s1) Γ)) s2
... | nothing = nothing -- s2 に型がつかなかった
... | just (m2 , σ2 , t2 , w2)
      -- m2 を App s1 s2 の返り値の型に割り当てる
      with unify2 (liftType 1 (substType σ2 (liftType (count s2) t1)))
                  (liftType 1 t2 ⇒ TVar (fromℕ m2))
... | nothing = nothing -- unify できなかった
... | just (m3 , σ3 , eq') =
  just (m3 , σ3 ⊹⊹ (σ2' ⊹⊹ σ1') , substType σ3 (TVar (fromℕ m2)) , AppW1W2) 
  where σ1' : AList (count s1 + suc (count s2) + m) (suc (count s2 + m1))
        σ1' rewrite +-comm (count s1) (suc (count s2)) | +-assoc (count s2) (count s1) m
          = liftAList (suc (count s2)) σ1
        σ2' : AList (suc (count s2 + m1)) (suc m2)
        σ2' = liftAList 1 σ2
        AppW1W2 : WellTypedTerm (substCxt (σ3 ⊹⊹ (σ2' ⊹⊹ σ1')) (liftCxt (count (App s1 s2)) Γ))
                                (substType σ3 (TVar (fromℕ m2)))
        AppW1W2 = App w1' w2'
                  where
                        Γ1 : Cxt {m1} n
                        Γ1 = substCxt σ1 (liftCxt (count s1) Γ)
                        Γ2 : Cxt {m2} n
                        Γ2 = substCxt σ2 (liftCxt (count s2) Γ1)
                        Γ3 : Cxt {m3} n
                        Γ3 = substCxt σ3 (liftCxt 1 Γ2)
                        Γ4 : Cxt {m3} n
                        Γ4 = substCxt (σ3 ⊹⊹ (σ2' ⊹⊹ σ1')) (liftCxt (count (App s1 s2)) Γ)
                     -- w1' : WellTypedTerm (substCxt (σ3 ⊹⊹ (σ2' ⊹⊹ σ1')) (liftCxt (count (App s1 s2)) Γ))
                     -- w1o : WellTypedTerm (substCxt σ1 (liftCxt (count s1) Γ)) t1
                     -- w1o = w1
                     {-
                        w1o1 : WellTypedTerm (liftCxt (count s2) Γ1) (liftType (count s2) t1)
                        w1o1 = liftWTerm (count s2) w1
                        w1o2 : WellTypedTerm (substCxt σ2 (liftCxt (count s2) Γ1)) (substType σ2 (liftType (count s2) t1))
                        w1o2 = substWTerm σ2 w1o1
                        w1o3 : WellTypedTerm (liftCxt 1 (substCxt σ2 (liftCxt (count s2) Γ1))) (liftType 1 (substType σ2 (liftType (count s2) t1)))
                        w1o3 = liftWTerm 1 w1o2
                        w1o4 : WellTypedTerm Γ3 (substType σ3 (liftType 1 (substType σ2 (liftType (count s2) t1))))
                        w1o4 = substWTerm σ3 w1o3
                     -}
                        w1o4 : WellTypedTerm Γ3 (substType σ3 (liftType 1 (substType σ2 (liftType (count s2) t1))))
                        w1o4 = substWTerm σ3 (liftWTerm 1 (substWTerm σ2 (liftWTerm (count s2) w1)))
                        
                    --  w2o : WellTypedTerm Γ2 t2
                    --  w2o = w2
                    --  w2o2 : WellTypedTerm (liftCxt 1 Γ2) (liftType 1 t2)
                    --  w2o2 = liftWTerm 1 w2
                        w2o3 : WellTypedTerm (substCxt σ3 (liftCxt 1 Γ2)) (substType σ3 (liftType 1 t2))
                        w2o3 = substWTerm σ3 (liftWTerm 1 w2)              

                        eqσ : liftAList (suc (count s2)) σ1 ≅ σ1'
                        eqσ rewrite +-comm (count s1) (suc (count s2)) | +-assoc (count s2) (count s1) m = hrefl

                        eq : Γ3 ≅ Γ4
                        eq  =
                          H.begin
                            Γ3
                          H.≅⟨ hcong (λ x → substCxt σ3 (liftCxt 1 x)) (substLiftCxtAdd (count s2) (count s1) σ2 σ1 Γ) ⟩
                            substCxt σ3 (liftCxt 1 (substCxt (σ2 ⊹⊹ liftAList (count s2) σ1) (subst (λ m → Cxt {m} n) (+-assoc (count s2) (count s1) m) (liftCxt (count s2 + count s1) Γ))))
                          H.≅⟨ hcong (λ x →
                                          substCxt σ3
                                          (liftCxt 1 (substCxt (σ2 ⊹⊹ liftAList (count s2) σ1) x))) (≡-to-≅ (substLiftCommute (count s2) (count s1) σ2 σ1 Γ)) ⟩
                            substCxt σ3 (liftCxt 1 (substCxt (σ2 ⊹⊹ liftAList (count s2) σ1)  (liftCxt (count s2) (liftCxt (count s1) Γ))))
                          H.≅⟨ substLiftCxtAdd2 1 (count s2) σ3 (σ2 ⊹⊹ liftAList (count s2) σ1) (liftCxt (count s1) Γ) ⟩
                            substCxt (σ3 ⊹⊹ (liftAList 1 (σ2 ⊹⊹ (liftAList (count s2) σ1))))  (liftCxt 1 (liftCxt (count s2) (liftCxt (count s1) Γ)))
                          H.≅⟨ hcong (λ x → substCxt (σ3 ⊹⊹ x)
                                                (liftCxt 1 (liftCxt (count s2) (liftCxt (count s1) Γ)))) (lift1Suc (count s1) (count s2) σ1 σ2) ⟩
                            substCxt (σ3 ⊹⊹ (σ2' ⊹⊹ (liftAList (suc (count s2)) σ1))) (liftCxt 1 (liftCxt (count s2) (liftCxt (count s1) Γ)))
                          H.≅⟨ substLiftCxtEq  (suc+-lem m (count s1) (count s2)) (hcong' (λ m₁ → AList m₁ (suc (count s2 + m1))) (suc+-lem m (count s1) (count s2)) (λ x → σ3 ⊹⊹ (σ2' ⊹⊹ x)) eqσ) (liftCxtAddEq (count s1) (count s2) Γ) ⟩
                            substCxt (σ3 ⊹⊹ (σ2' ⊹⊹ σ1'))  (liftCxt ((count s1)  + suc (count s2)) Γ)                           
                          H.≅⟨ hrefl ⟩
                            Γ4
                          H.∎
                          
                        σ3→Commute : (substType σ3 (liftType 1 t2 ⇒ TVar (fromℕ m2))) ≡ (substType σ3 (liftType 1 (substType σ2 (liftType (count s2) t1))))
                        σ3→Commute = sym eq'
                       
                        w1' : WellTypedTerm (substCxt (σ3 ⊹⊹ (σ2' ⊹⊹ σ1')) (liftCxt (count (App s1 s2)) Γ))
                                            (substType σ3 (liftType 1 t2 ⇒ TVar (fromℕ m2)))
                        w1' rewrite σ3→Commute = hsubst (λ Γ → WellTypedTerm Γ (substType σ3 (liftType 1 (substType σ2 (liftType (count s2) t1))))) eq w1o4
                        
                        w2' : WellTypedTerm (substCxt (σ3 ⊹⊹ (σ2' ⊹⊹ σ1')) (liftCxt (count (App s1 s2)) Γ))
                                            (substType σ3 (liftType 1 t2))
                        w2' = hsubst (λ Γ → WellTypedTerm Γ (substType σ3 (liftType 1 t2)))
                                     eq w2o3
-}

-- inferW Γ s : Γ のもとで s を型推論する。
-- もとの型変数の数が m だったとき、推論結果として (m', 代入, 型) を返す。
-- ここで m' は返って来た型の中に含まれる型変数の数。
-- あらかじめ s の中の Lam, App ノードに型変数をひとつ割り振ったとすると、
-- 型変数の合計は、もともと m + count s となる。
-- 返ってくる代入は、型変数の数を m + count s から m' に落とすものになる。

-- 不等式を入れて具体的な値を書かないようにしたバージョン
lemma1 : {m m1 m1' : ℕ} → (m ≤ m1') → (m ≤ suc (suc m1) ∸ m1 + m1')
lemma1 {m} {m1} {m1'} leq rewrite m+n∸n≡m 2 m1 = ≤-steps (suc (suc zero)) leq

inferW : (m : ℕ) → {n : ℕ} →  (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m'' ∈ ℕ ] Σ[ m' ∈ ℕ ]
                (m ≤ m'') × AListType m'' m' × Type m')
inferW m Γ (Var x) = just (m , m , n≤m+n 0 m , anil , lookup x Γ)
inferW m Γ (Lam s) with inferW (suc m) (TVar (fromℕ m) ∷ liftCxt 1 Γ) s
inferW m Γ (Lam s) | nothing = nothing
inferW m Γ (Lam s) | just (m'' , m' , 1+m≤m'' , σ , t) =
  just (m'' , m' , m≤m'' , σ , tx ⇒ t)
    where m≤m'' : m ≤ m''
          m≤m'' = DecTotalOrder.trans decTotalOrder (n≤m+n 1 m) 1+m≤m''
          tx : Type m'
          tx = substType≤ σ 1+m≤m'' (TVar (fromℕ m)) 
inferW m Γ (App s1 s2)  with inferW m Γ s1
inferW m Γ (App s1 s2) | nothing = nothing
inferW m Γ (App s1 s2) | just  (m1' , m1 , m≤m1' , σ1 , t1) with inferW m1 (substCxt≤ σ1 m≤m1' Γ) s2
inferW m Γ (App s1 s2) | just (m1' , m1 , m≤m1' , σ1 , t1) | nothing = nothing
inferW m Γ (App s1 s2) | just (m1' , m1 , m≤m1' , σ1 , t1) | just (m2' , m2 , m1≤m2' , σ2 , t2)
      with mgu (liftType 1 (substType≤ σ2 m1≤m2' t1)) -- t1
               (liftType 1 t2 ⇒ TVar (fromℕ m2)) -- t2 ⇒ TVar (fromℕ m2)
inferW m Γ (App s1 s2) | just (m1' , m1 , m≤m1' , σ1 , t1) | just (m2' , m2 , m1≤m2' , σ2 , t2) | nothing = nothing
inferW m Γ (App s1 s2) | just (m1' , m1 , m≤m1' , σ1 , t1) | just (m2' , m2 , m1≤m2' , σ2 , t2) | just (m3 , σ3) =
       just (suc m2 ∸ m2 + (m2' ∸ m1 + m1') , m3 , leq ,
        σ3 +⟨ n≤m+n 1 m2 ⟩ (σ2 +⟨ m1≤m2' ⟩ σ1) ,
        substType σ3 (TVar (fromℕ m2))) 
  where leq : m ≤ suc m2 ∸ m2 + (m2' ∸ m1 + m1')
        leq = start
                m
              ≤⟨ m≤m1' ⟩
                m1'
              ≤⟨ n≤m+n (m2' ∸ m1) m1' ⟩
                m2' ∸ m1 + m1'
              ≤⟨ n≤m+n (suc m2 ∸ m2) (m2' ∸ m1 + m1') ⟩
                suc m2 ∸ m2 + (m2' ∸ m1 + m1')
              □
inferW m Γ (Fst t) with inferW m Γ t
inferW m Γ (Fst t) | nothing = nothing
inferW m Γ (Fst t) | just (m1' , m1 , m≤m1' , σ1 , t1)
         with mgu  (liftType 2 t1)  (liftType 1 (TVar (fromℕ m1)) ∏ ((TVar (fromℕ (suc m1)))))
inferW m Γ (Fst t) | just (m1' , m1 , m≤m1' , σ1 , t1) | just (m2 , σ2) = just (suc (suc m1) ∸ m1 + m1' , (m2 , (lemma1 {m} {m1} {m1'} m≤m1' , (σ2 +⟨ ≤-steps 2 (n≤m+n 0 m1) ⟩ σ1 , substType σ2 (liftType 1 (TVar (fromℕ m1)))))))
inferW m Γ (Fst t) | just (m1' , m1 , m≤m1' , σ1 , t1) | nothing = nothing
inferW m Γ (Snd t) with inferW m Γ t
inferW m Γ (Snd t) | nothing = nothing
inferW m Γ (Snd t) | just  (m1' , m1 , m≤m1' , σ1 , t1) with mgu  (liftType 2 t1)  (liftType 1 (TVar (fromℕ m1)) ∏ ((TVar (fromℕ (suc m1)))))
inferW m Γ (Snd t) | just (m1' , m1 , m≤m1' , σ1 , t1) | nothing = nothing
inferW m Γ (Snd t) | just (m1' , m1 , m≤m1' , σ1 , t1) | just (m2 , σ2) = just (suc (suc m1) ∸ m1 + m1' , (m2 , (lemma1 {m} {m1} {m1'} m≤m1' , (σ2 +⟨ ≤-steps 2 (n≤m+n 0 m1) ⟩ σ1 , substType σ2 (TVar (fromℕ (suc m1)))))))

inferW m Γ (Cons t t₁) with inferW m Γ t
inferW m Γ (Cons t t₁) | nothing = nothing
inferW m Γ (Cons t t₁) | just(m1' , m1 , m≤m1' , σ1 , t1) with mgu  (liftType 2 t1)  (liftType 1 (TVar (fromℕ m1)) ∏ ((TVar (fromℕ (suc m1)))))
inferW m Γ (Cons t t₁) | just (m1' , m1 , m≤m1' , σ1 , t1) | just (m2 , σ2) = just (suc (suc m1) ∸ m1 + m1' , (m2 , (lemma1 {m} {m1} {m1'} m≤m1' , (σ2 +⟨ ≤-steps 2 (n≤m+n 0 m1) ⟩ σ1 , substType σ2 (TVar (fromℕ (suc m1)))))))
inferW m Γ (Cons t t₁) | just (m1' , m1 , m≤m1' , σ1 , t1) | nothing = nothing
