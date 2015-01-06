\agdaIgnore{
\begin{code}

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
\end{code}
}
\agdaSnippet\InferWDef{
\begin{code}
-- inferW Γ s : Γ のもとで s を型推論する。
-- もとの型変数の数が m だったとき、推論結果として (m', 代入, 型) を返す。
-- ここで m' は返って来た型の中に含まれる型変数の数。
-- あらかじめ s の中の Lam, App ノードに型変数をひとつ割り振ったとすると、
-- 型変数の合計は、もともと m + count s となる。
-- 返ってくる代入は、型変数の数を m + count s から m' に落とすものになる。
infer : {m n : ℕ} →  (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m' ∈ ℕ ] AList (count s + m) m' × Type m')
\end{code}
}
\agdaSnippet\InferWVar{
\begin{code}
infer {m} Γ (Var x) = just (m , anil , lookup x Γ)
\end{code}
}
\agdaSnippet\InferWLam{
\begin{code}
infer {m} Γ (Lam s) with infer (TVar (fromℕ m) ∷ liftCxt 1 Γ) s -- TVar (fromℕ m) が引数の型
... | nothing = nothing -- s に型がつかなかった
... | just (m' , σ , t) =
  just (m' , σ' , tx ⇒ t) -- TVar (fromℕ m) ⇒ t が Lam s の型
  where σ' : AList (suc (count s + m)) m' 
        σ' = subst (λ m → AList m m') (+-suc (count s) m) σ
        tx : Type m'
        tx = substType σ (liftType (count s) (TVar (fromℕ m))) -- σ (↑s m)
\end{code}
}
\agdaSnippet\InferWApp{
\begin{code}
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

\end{code}
}


\agdaSnippet\InferTwoDef{
\begin{code}
infer2 : {m n : ℕ} → (Γ : Cxt {m} n) → (s : WellScopedTerm n) →
         Maybe (Σ[ m' ∈ ℕ ]
                Σ[ σ ∈ AList (count s + m) m' ]
                Σ[ τ ∈ Type m' ]
                WellTypedTerm (substCxt σ (liftCxt (count s) Γ)) τ)

\end{code}
}
\agdaSnippet\InferTwoVar{
\begin{code}
infer2 {m} Γ (Var x)  = just (m , anil , lookup x Γ , VarX)
  where
    VarX : WellTypedTerm (substCxt anil (liftCxt 0 Γ)) (lookup x Γ)
    VarX rewrite substCxtAnil Γ | liftCxtZero Γ = Var x
    -- Var x : WellTypedTerm Γ (lookup x Γ)
\end{code}
}
\agdaSnippet\InferTwoLam{
\begin{code}
infer2 {m} {n} Γ (Lam s) with infer2 (TVar (fromℕ m) ∷ liftCxt 1 Γ) s -- TVar (fromℕ m) が引数の型
... | nothing = nothing -- s に型がつかなかった
... | just (m' , σ , t , w) = just (m' , σ' , tx ⇒ t , LamW) 
  where
    σ' : AList (suc (count s + m)) m' 
    σ' = subst (λ m → AList m m') (+-suc (count s) m) σ
    tx : Type m'
    tx = substType σ (liftType (count s) (TVar (fromℕ m))) -- σ (↑s m)
    LamW : WellTypedTerm (substCxt σ' (liftCxt (count (Lam s)) Γ)) (tx ⇒ t)
    LamW = Lam tx w'
      where
        w' : WellTypedTerm (tx ∷ (substCxt σ' (liftCxt (count (Lam s)) Γ))) t 
        -- w  : WellTypedTerm (substCxt σ (liftCxt (count s) (TVar (fromℕ m) ∷ liftCxt 1 Γ))) t
        --    = WellTypedTerm (substType σ (liftType (count s) (TVar (fromℕ m))) ∷
        --                     substCxt  σ (liftCxt  (count s) (liftCxt 1 Γ))) t
        w' = subst (λ l → WellTypedTerm (tx ∷ l) t) eq w
          where
            eq : substCxt σ (liftCxt (count s) (liftCxt 1 Γ)) ≡ substCxt σ' (liftCxt (count (Lam s)) Γ)
            -- eq = ...
\end{code}
}
\agdaSnippet\InferTwoLamEq{
\begin{code}
            eq = ≅-to-≡ (hcong₂' (λ c → AList c m') (λ c → Cxt {c} n) (+-suc (count s) m)
                                                     substCxt
                                                     (hsym (≡-subst-removable (λ m → AList m m')
                                                                              (+-suc (count s) m) σ))
                                                     (liftCxtSuc (count s) Γ))
\end{code}
}
\agdaSnippet\InferTwoApp{
\begin{code}                                               
infer2 {m} {n} Γ (App s1 s2)
      with infer2 Γ s1
... | nothing = nothing -- s1 に型がつかなかった
... | just (m1 , σ1 , t1 , w1)
                              
      with infer2 (substCxt σ1 (liftCxt (count s1) Γ)) s2
... | nothing = nothing -- s2 に型がつかなかった
... | just (m2 , σ2 , t2 , w2) -- m2 を App s1 s2 の返り値の型に割り当てる
      with unify2 (liftType 1 (substType σ2 (liftType (count s2) t1)))
                 (liftType 1 t2 ⇒ TVar (fromℕ m2)) 
... | nothing = nothing -- unify できなかった
... | just (m3 , σ3 , eq') =
  just (m3 , σ3 +!+ (σ2' +!+ σ1') , substType σ3 (TVar (fromℕ m2)) , AppW1W2) 
  where
    σ1' : AList (count s1 + suc (count s2) + m) (suc (count s2 + m1))
    σ1' rewrite +-comm (count s1) (suc (count s2)) | +-assoc (count s2) (count s1) m
          = liftAList (suc (count s2)) σ1 -- liftAList 1 liftAList count s1
    σ2' : AList (suc (count s2 + m1)) (suc m2)
    σ2' = liftAList 1 σ2
    AppW1W2 : WellTypedTerm (substCxt (σ3 +!+ (σ2' +!+ σ1')) (liftCxt (count (App s1 s2)) Γ))
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
            Γ4 = substCxt (σ3 +!+ (σ2' +!+ σ1')) (liftCxt (count (App s1 s2)) Γ)

            w1o4 : WellTypedTerm Γ3 (substType σ3 (liftType 1 (substType σ2 (liftType (count s2) t1))))
            w1o4 = substWTerm σ3 (liftWTerm 1 (substWTerm σ2 (liftWTerm (count s2) w1)))
                        
            w2o3 : WellTypedTerm (substCxt σ3 (liftCxt 1 Γ2)) (substType σ3 (liftType 1 t2))
            w2o3 = substWTerm σ3 (liftWTerm 1 w2)              

            eqσ : liftAList (suc (count s2)) σ1 ≅ σ1'
            eqσ rewrite +-comm (count s1) (suc (count s2)) | +-assoc (count s2) (count s1) m = hrefl

            eq : Γ3 ≅ Γ4
            eq  = --...
 \end{code}
}
\agdaSnippet\InferTwoAppProof{
\begin{code}    
                     H.begin
                       Γ3
                      H.≅⟨ hcong (λ x → substCxt σ3 (liftCxt 1 x)) (substLiftCxtAdd (count s2) (count s1) σ2 σ1 Γ) ⟩
                       substCxt σ3 (liftCxt 1 (substCxt (σ2 +!+ liftAList (count s2) σ1)
                                (subst (λ m → Cxt {m} n) (+-assoc (count s2) (count s1) m)
                                                                  (liftCxt (count s2 + count s1) Γ))))
                      H.≅⟨ hcong (λ x →
                                     substCxt σ3
                                     (liftCxt 1 (substCxt (σ2 +!+ liftAList (count s2) σ1) x)))
                                              (≡-to-≅ (substLiftCommute (count s2) (count s1) σ2 σ1 Γ)) ⟩
                       substCxt σ3 (liftCxt 1 (substCxt (σ2 +!+ liftAList (count s2) σ1)
                                              (liftCxt (count s2) (liftCxt (count s1) Γ))))
                     H.≅⟨ substLiftCxtAdd2 1 (count s2) σ3 (σ2 +!+ liftAList (count s2) σ1) (liftCxt (count s1) Γ) ⟩
                       substCxt (σ3 +!+ (liftAList 1 (σ2 +!+ (liftAList (count s2) σ1))))
                                        (liftCxt 1 (liftCxt (count s2) (liftCxt (count s1) Γ)))
                     H.≅⟨ hcong (λ x → substCxt (σ3 +!+ x)
                                           (liftCxt 1 (liftCxt (count s2) (liftCxt (count s1) Γ))))
                                             (lift1Suc (count s1) (count s2) σ1 σ2) ⟩
                       substCxt (σ3 +!+ (σ2' +!+ (liftAList (suc (count s2)) σ1)))
                                       (liftCxt 1 (liftCxt (count s2) (liftCxt (count s1) Γ)))
                     H.≅⟨ substLiftCxtEq  (suc+-lem m (count s1) (count s2))
                        (hcong' (λ m₁ → AList m₁ (suc (count s2 + m1)))
                          (suc+-lem m (count s1) (count s2)) (λ x → σ3 +!+ (σ2' +!+ x)) eqσ)
                                                        (liftCxtAddEq (count s1) (count s2) Γ) ⟩
                       substCxt (σ3 +!+ (σ2' +!+ σ1'))  (liftCxt ((count s1)  + suc (count s2)) Γ)                           
                     H.≅⟨ hrefl ⟩
                       Γ4
                     H.∎
\end{code}
}
\agdaSnippet\InferTwoAppRest{
\begin{code} 
            σ3→Commute : (substType σ3 (liftType 1 t2 ⇒ TVar (fromℕ m2))) ≡
                             (substType σ3 (liftType 1 (substType σ2 (liftType (count s2) t1))))
            σ3→Commute = sym eq'
                       
            w1' : WellTypedTerm (substCxt (σ3 +!+ (σ2' +!+ σ1')) (liftCxt (count (App s1 s2)) Γ))
                                       (substType σ3 (liftType 1 t2 ⇒ TVar (fromℕ m2)))
            w1' rewrite σ3→Commute
                 = hsubst (λ Γ → WellTypedTerm Γ (substType σ3 (liftType 1
                                               (substType σ2 (liftType (count s2) t1))))) eq w1o4
                     
            w2' : WellTypedTerm (substCxt (σ3 +!+ (σ2' +!+ σ1')) (liftCxt (count (App s1 s2)) Γ))
                                       (substType σ3 (liftType 1 t2))
            w2' = hsubst (λ Γ → WellTypedTerm Γ (substType σ3 (liftType 1 t2)))
                                     eq w2o3

\end{code}
}
