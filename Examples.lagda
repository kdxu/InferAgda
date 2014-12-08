\agdaIgnore{
\begin{code}
module Examples where
open import Lib
open import Base
open import TwoLevel
open import Data.Empty
open import CtxExtension

-- (We pre-define some De Bruijn indices to improve
-- readability of the examples:)
\end{code}}
\agdaSnippet\btaExZero{
\begin{code}
ex0 : AExp [] (D (Fun Num Num))
ex0 =
  DApp
  (DLam (DLam
    (DAdd (Lift (SAdd (SCst 5) (SCst 6))) (Var (tl hd)))))
  (DCst 31)
\end{code}}
\agdaSnippet\btaExZeroSpec{
\begin{code}
ex0-spec : Exp [] (Fun Num Num)
ex0-spec =
  EApp
  (ELam (ELam
    (EAdd (ECst 11) (EVar (tl hd)))))
  (ECst 31)
\end{code}}
\agdaSnippet\btaTIntZero{
\begin{code}
ATInt₀ : Ctx → AType → Set
ATInt₀ _ SNum   = ℕ
ATInt₀ Γ (D τ)  = Exp Γ τ 
ATInt₀ _ _      = ⊥
\end{code}}
\agdaSnippet\btaAEnvZero{
\begin{code}
data AEnv0 (Γ : Ctx) : ACtx → Set where
  []   : AEnv0 Γ []
  _∷_  : ∀ {α Δ} →
        ATInt₀ Γ α → AEnv0 Γ Δ → AEnv0 Γ (α ∷ Δ)
\end{code}}
\agdaSnippet\btaAEnvZeroFive{
\begin{code}
AEnv05 : Set
AEnv05 = List (∃₂ λ α Γ → ATInt₀ Γ α)
\end{code}}
\agdaSnippet\btaAEnvZeroSimple{
\begin{code}
data AEnv0Simple : ACtx → Set where
  [] : AEnv0Simple []
  _∷_ : ∀ {α Γ Δ} →
        ATInt₀ Γ α → AEnv0Simple Δ → AEnv0Simple (α ∷ Δ)

lookup0Simple : ∀ {α Δ} →
           α ∈ Δ → AEnv0Simple Δ → ∃ λ Γ → ATInt₀ Γ α
lookup0Simple hd (x ∷ _)      = _ , x
lookup0Simple (tl x) (_ ∷ ρ)  = lookup0Simple x ρ
\end{code}}
\agdaSnippet\btaLookupZero{
\begin{code}
lookup0 : ∀ {α Γ Δ} → α ∈ Δ → AEnv0 Γ Δ → ATInt₀ Γ α 
lookup0 hd (x ∷ _)      = x
lookup0 (tl x) (_ ∷ ρ)  = lookup0 x ρ
\end{code}}
\agdaSnippet\btaShiftZero{
\begin{code}
int↑0 : ∀ {α τ' Γ} → ATInt₀ Γ α → ATInt₀ (τ' ∷ Γ) α
int↑0 {D τ} (EVar x) = EVar (tl x)
int↑0 _ = {!!}
\end{code}}
\agdaSnippet\btaShiftEnvZero{
\begin{code}
env↑0 : ∀ {τ Δ Γ} → AEnv0 Γ Δ → AEnv0 (τ ∷ Γ) Δ
env↑0 [] = []
env↑0 (x ∷ env) = int↑0 x ∷ env↑0 env
\end{code}}
\agdaSnippet\btaConsFreshZero{
\begin{code}
addFresh0 : ∀ {τ Γ Δ} → AEnv0 Γ Δ → AEnv0 (τ ∷ Γ) (D τ ∷ Δ)
addFresh0 ρ = EVar hd ∷ env↑0 ρ
\end{code}}
\agdaIgnore{
\begin{code}
module Pe0 where
\end{code}
}
\agdaSnippet\btaPeZeroSig{
\begin{code}
  pe0 : ∀ {α Δ} → let Γ = map erase Δ in
    AExp Δ α → AEnv0 Γ Δ → ATInt₀ Γ α
\end{code}}
\agdaSnippet\btaPeZero{
\begin{code}
  pe0 (SCst x)      ρ = x
  pe0 (DCst x)      ρ = ECst x
  pe0 (SAdd e f)    ρ = (pe0 e ρ) + (pe0 f ρ) 
  pe0 (DAdd e f)    ρ = EAdd (pe0 e ρ) (pe0 f ρ) 
  pe0 (Lift e)      ρ = ECst (pe0 e ρ)
  pe0 (DLam {τ} e)  ρ = ELam (pe0 e (addFresh0 ρ))
  pe0 (DApp f e)    ρ = EApp (pe0 f ρ) (pe0 e ρ)
  pe0 {D τ} (Var x)  ρ = lookup0 x ρ
  pe0 _             ρ = {!!} 
\end{code}}
\agdaIgnore{
\begin{code}

  check-ex0 : pe0 ex0 [] ≡ ex0-spec
  check-ex0 = refl
\end{code}
}
\agdaSnippet\btaExOne{
\begin{code}
ex1 : AExp [] (D (Fun Num (Fun Num Num)))
ex1 = DLam (SApp (SLam (DLam (DAdd ((Var (tl (tl hd)))) (Var (tl hd))))) (DAdd (Var hd) (DCst 5)))
\end{code}}
\agdaSnippet\btaExOneSpec{
\begin{code}
ex1-spec : Exp [] (Fun Num (Fun Num Num))
ex1-spec = ELam (ELam (EAdd (EVar (tl hd)) (EAdd (EVar (tl hd)) (ECst 5))))
\end{code}
}
\agdaSnippet\btaImpOne{
\begin{code}
ATInt₁ : Ctx → AType → Set
ATInt₁ _ SNum          = ℕ
ATInt₁ Γ (D σ)         = Exp Γ σ
ATInt₁ Γ (SFun α₁ α₂)   = ATInt₁ Γ α₁ → ATInt₁ Γ α₂
\end{code}
}
\agdaSnippet\btaAEnvOne{
\begin{code}
data AEnv1 (Γ : Ctx) : ACtx → Set where
  [] : AEnv1 Γ []
  _∷_ : ∀ {α Δ} →
      ATInt₁ Γ α → AEnv1 Γ Δ → AEnv1 Γ (α ∷ Δ)
\end{code}}
\agdaSnippet\btaInject{
\begin{code}
inject : ∀ {α Γ' Γ} → ATInt₁ Γ α → ATInt₁ Γ' α
inject {SNum} n            = n
inject {D Num} (ECst n)  = (ECst n)
inject {D Num} (EAdd e f)  = EAdd (inject e)
                                     (inject f)
inject {SFun α α₁} v  = (λ x → inject (v (inject x)))
inject  _                = {!!} 
\end{code}}
\agdaIgnore{
\begin{code}
elevate-var : ∀ {Γ Γ'} {τ : Type} → Γ ↝ Γ' → τ ∈ Γ → τ ∈ Γ'
elevate-var refl x = x
elevate-var (extend Γ↝Γ') x = tl (elevate-var Γ↝Γ' x)

elevate-var2 : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → τ ∈ Γ → τ ∈ Γ''
elevate-var2 (refl x) x₁ = elevate-var x x₁
elevate-var2 (extend Γ↝Γ'↝Γ'') hd = hd
elevate-var2 (extend Γ↝Γ'↝Γ'') (tl x) = tl (elevate-var2 Γ↝Γ'↝Γ'' x)

elevate : ∀ {Γ Γ' Γ'' τ} → Γ ↝ Γ' ↝ Γ'' → Exp Γ τ → Exp Γ'' τ
elevate Γ↝Γ'↝Γ'' (EVar x) = EVar (elevate-var2 Γ↝Γ'↝Γ'' x)
elevate Γ↝Γ'↝Γ'' (ECst x) = ECst x
elevate Γ↝Γ'↝Γ'' (EAdd e e₁) = EAdd (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)
elevate Γ↝Γ'↝Γ'' (ELam e) = ELam (elevate (extend Γ↝Γ'↝Γ'') e)
elevate Γ↝Γ'↝Γ'' (EApp e e₁) = EApp (elevate Γ↝Γ'↝Γ'' e) (elevate Γ↝Γ'↝Γ'' e₁)


\end{code}}
\agdaSnippet\btaShiftExp{
\begin{code}
exp↑ : ∀ {τ τ' Γ} → Exp Γ τ' → Exp (τ ∷ Γ) τ'
exp↑ (EVar x) = EVar (tl x)
-- ...
\end{code}}
\agdaIgnore{
\begin{code}
exp↑ e = elevate (refl (extend refl)) e
\end{code}}
\agdaSnippet\btaShiftOne{
\begin{code}
int↑₁ : ∀ {α τ' Γ} → ATInt₁ Γ α → ATInt₁ (τ' ∷ Γ) α
int↑₁ {D τ} e = exp↑ e
int↑₁ _ = {!!}
\end{code}}
\agdaSnippet\btaShiftEnvOne{
\begin{code}
env↑₁ : ∀ {τ Δ Γ} → AEnv1 Γ Δ → AEnv1 (τ ∷ Γ) Δ
env↑₁ [] = []
env↑₁ (x ∷ env) = int↑₁ x ∷ env↑₁ env
\end{code}}
\agdaSnippet\btaConsFreshOne{
\begin{code}
addFresh1 : ∀ {τ Γ Δ} → AEnv1 Γ Δ → AEnv1 (τ ∷ Γ) (D τ ∷ Δ)
addFresh1 ρ = EVar hd ∷ env↑₁ ρ
\end{code}}
\agdaSnippet\btaLookupOne{
\begin{code}
lookup1 : ∀ {Γ Δ α} → α ∈ Δ → AEnv1 Γ Δ → ATInt₁ Γ α
lookup1 hd (v ∷ _) = v 
lookup1 (tl x) (_ ∷ ρ) = lookup1 x ρ
\end{code}
}
\agdaSnippet\btaAddVal{
\begin{code}
addValue1 : ∀ {α Γ Δ} → ATInt₁ Γ α → AEnv1 Γ Δ → AEnv1 Γ (α ∷ Δ)
addValue1 v ρ = v ∷ ρ
\end{code}
}
\agdaIgnore{
\begin{code}
module Pe1 where
\end{code}
}
\agdaSnippet\btaPeOneSig{
\begin{code}
  pe1 : ∀ {Γ Δ α} → 
          AExp Δ α → AEnv1 Γ Δ → ATInt₁ Γ α
\end{code}}
\agdaSnippet\btaPeOne{
\begin{code}
  pe1 (Var x) ρ       = lookup1 x ρ
  pe1 (DLam e) ρ      = ELam (pe1 e (addFresh1 ρ))
\end{code}
}
\agdaSnippet\btaPeOneStatic{
\begin{code}
  pe1 (SApp f e) ρ    = (pe1 f ρ) (pe1 e ρ)
  pe1 (SLam {α} e) ρ  = λ x → pe1 e (x ∷ ρ)
\end{code}
}
\agdaIgnore{
\begin{code}
  pe1 (DApp f e) ρ    = EApp (pe1 f ρ) (pe1 e ρ)
  pe1 (SCst x) _      = x
  pe1 (DCst x) _      = ECst x
  pe1 (SAdd e f) ρ    = (pe1 e ρ) + (pe1 f ρ) 
  pe1 (DAdd e f) ρ    = EAdd (pe1 e ρ) (pe1 f ρ) 
  pe1 (Lift e) ρ      = ECst (pe1 e ρ)
\end{code}
}
\agdaIgnore{
\begin{code}
  check-ex1 : pe1 ex1 [] ≡ (ex1-spec)
  check-ex1 = refl
\end{code}
}
\agdaSnippet\btaImp{
\begin{code}
ATInt : Ctx → AType → Set
ATInt _ SNum          = ℕ
ATInt Γ (D σ)         = Exp Γ σ
ATInt Γ (SFun α₁ α₂)  =
  ∀ {Γ'} → Γ ↝ Γ' → ATInt Γ' α₁ → ATInt Γ' α₂
\end{code}
}
\agdaSnippet\btaAEnv{
\begin{code}
data AEnv (Γ : Ctx) : ACtx → Set where
  [] : AEnv Γ []
  _∷_ : ∀ {α Δ} → ATInt Γ α → AEnv Γ Δ → AEnv Γ (α ∷ Δ)
\end{code}}

\agdaSnippet\btaShift{
\begin{code}
int↑ : ∀ {α Γ Γ'} → Γ ↝ Γ' → ATInt Γ α → ATInt Γ' α
int↑ refl v = v
int↑ {D τ} (extend Γ↝Γ') e = exp↑ (int↑ Γ↝Γ' e)
int↑ {SNum} _ v = v
int↑ {SFun α α₁} Γ↝Γ' f = λ Γ'↝Γ'' → f (Γ↝Γ' ⊕ Γ'↝Γ'')
\end{code}}
\agdaSnippet\btaShiftEnv{
\begin{code}
env↑ : ∀ {Δ Γ Γ'} → Γ ↝ Γ' → AEnv Γ Δ → AEnv Γ' Δ
env↑ _ [] = []
env↑ Γ↝Γ' (x ∷ ρ) = int↑ Γ↝Γ' x ∷ env↑ Γ↝Γ' ρ
\end{code}}
\agdaSnippet\btaConsFresh{
\begin{code}
addFresh : ∀ {τ Γ Δ} → AEnv Γ Δ → AEnv (τ ∷ Γ) (D τ ∷ Δ)
addFresh ρ = EVar hd ∷ env↑ (extend refl) ρ
\end{code}}
\agdaSnippet\btaLookup{
\begin{code}
lookup : ∀ {Γ Δ α} → α ∈ Δ → AEnv Γ Δ → ATInt Γ α
lookup hd (v ∷ _) = v 
lookup (tl x) (_ ∷ ρ) = lookup x ρ
\end{code}
}
\agdaSnippet\btaPe{
\begin{code}
pe : ∀ {Γ Δ α} → AExp Δ α → AEnv Γ Δ → ATInt Γ α
pe (SCst x) _      = x
pe (SAdd e f) ρ    = (pe e ρ) + (pe f ρ) 
pe (Var x) ρ       = lookup x ρ
pe (SLam e) ρ      = λ Γ↝Γ' x → pe e (x ∷ env↑ Γ↝Γ' ρ)
pe (SApp f e) ρ    = (pe f ρ) refl (pe e ρ)
pe (Lift e) ρ      = ECst (pe e ρ)
pe (DCst x) _      = ECst x
pe (DAdd e f) ρ    = EAdd (pe e ρ) (pe f ρ) 
pe (DLam e) ρ      = ELam (pe e (addFresh ρ))
pe (DApp f e) ρ    = EApp (pe f ρ) (pe e ρ)
\end{code}
}

\agdaSnippet\btaExTwo{
\begin{code}
ex2 : AExp [] (D (Fun Num (Fun Num Num)))
ex2 = DLam (SApp (SLam (DLam (DAdd ((Var (tl (tl hd)))) (SApp (Var (tl hd)) (DCst 5))))) (SLam (Var (tl hd))))
ex2-spec : Exp [] (Fun Num (Fun Num Num))
ex2-spec = ELam (ELam (EAdd (EVar (tl hd)) (EVar (tl hd))))
\end{code}
}

\agdaIgnore{
\begin{code}

check-ex2 : pe ex2 [] ≡ (ex2-spec)
check-ex2 = refl
\end{code}}

\agdaIgnore{
\begin{code}
module ExamplesSignatures where
\end{code}}
\agdaSnippet\btaPeZeroReturnType{
\begin{code}
  pe0 : ∀ {α Δ} → let Γ = map erase Δ in
        AExp Δ α → {!!} → ATInt₀ Γ α
\end{code}}
\agdaIgnore{
\begin{code}
  pe0 e ρ = {!!}
\end{code}}
\agdaSnippet\btaPeOneWrong{
\begin{code}
  pe1 : ∀ { Δ α } → let Γ = map erase Δ in
           AExp Δ α → AEnv1 Γ Δ → ATInt₁ Γ α
  pe1 (SApp f e) ρ    = (pe1 f ρ) (pe1 e ρ)
  pe1 (SLam {α} e) ρ  = λ x → {!pe1 e (x ∷ ρ)!} 
\end{code}
}
\agdaIgnore{
\begin{code}
  pe1 _ _ = ignore
    where postulate ignore : _
\end{code}}

\agdaSnippet\btaShiftPrime{
\begin{code}
  int↑₂ : ∀ {α Γ τ} → ATInt₁ Γ α → ATInt₁ (τ ∷ Γ) α
  int↑₂ {D τ}  e = exp↑ e
  int↑₂ {SNum} v = v
  int↑₂ {SFun α₁ α₂} {Γ} {τ} f = f' 
    where
      f' : ATInt₁ (τ ∷ Γ) α₁ → ATInt₁ (τ ∷ Γ) α₂
      f' x = {!!} 
\end{code}}

