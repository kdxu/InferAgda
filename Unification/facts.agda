module facts where
open import FUSR
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning 
open import Data.Nat
open import Data.Product
open import Data.Empty
open import Data.Fin
open import Data.Sum
open import Data.Bool
import Level

-------------------------------------------

fact : {S T R : Set} → ∀(f : S → Maybe T)  → ∀ (g : R → S) → ∀ (s : Maybe R) → rf (f ∘ g) s ≡ (rf f ∘ lrf g) s
fact f g no = refl
fact f g (yes x) = refl

fact2 : {n : ℕ} →  (t : Term n) → (ι ◃ t ≡ t)
fact2 (ι x) = refl
fact2 leaf = refl
fact2 (s fork t) = cong₂ _fork_ (fact2 s) (fact2 t)

fact3 : {l m n : ℕ} → (f : Fin m → Term n) →  (g : Fin l → Term m)  → (t : Term l)
        → (f ◇ g) ◃ t ≡ f ◃ (g ◃ t)
fact3 f g (ι x) = refl
fact3 f g leaf = refl
fact3 f g (t fork t₁) = cong₂ _fork_ (fact3 f g t) (fact3 f g t₁)

fact4 : {l m n : ℕ} → (f : Fin m → Term n) → (r : Fin l → Fin m) → ((f ◇ (▹ r)) ≐ (f ∘ r))
fact4 = λ f r x → refl

-- suc a ≡ suc b → a ≡ b 
lemma1 : {n : ℕ} → (a b : Fin n) → (_≡_ {_} {Fin (suc n)} (suc a) (suc b))  → a ≡ b
lemma1 .b b refl = refl

fact5 : {n : ℕ} → (x : Fin (suc n)) → (y : Fin n) → (z : Fin n) → thin x y ≡ thin x z → y ≡ z
fact5 zero zero zero a = refl
fact5 zero zero (suc z) ()
fact5 zero (suc y) .(suc y) refl = refl
fact5 (suc x) zero zero a = refl
fact5 (suc x) zero (suc z) ()
fact5 (suc x) (suc y) zero ()
fact5 (suc x) (suc y) (suc z) a = cong suc (fact5 x y z (lemma1 (thin x y) (thin x z) a))

fact6 : {n : ℕ} → (x : Fin (suc n))  → (y : Fin n) → ((thin x y ≡ x) → ⊥)
fact6 zero zero ()
-- a  : suc zero ≡ zero
fact6 zero (suc y) ()
fact6 (suc x) zero ()
fact6 (suc x) (suc y) a = fact6 x y (lemma1 (thin x y) x a)

fact7 : {n : ℕ} → (x y : Fin (suc n)) → (x ≡ y → ⊥) → Σ[ y' ∈ Fin n ] (thin x y' ≡ y)
fact7 zero zero a = ⊥-elim (a refl)
fact7 zero (suc y) a = y , refl 
fact7 {zero} (suc ()) zero a
fact7 {suc n} (suc x) zero a = zero , refl
fact7 {zero} (suc ()) (suc y) a
fact7 {suc n} (suc x) (suc y) a with fact7 x y (λ x₁ → a (cong suc x₁))
fact7 {suc n} (suc x) (suc y) a | y' , p = (suc y') , cong suc p

lemma2 : {n : ℕ} → (x : Fin (suc n)) → (y : Fin (suc n)) → (((y ≡ x) × (thick x y) ≡ no) ⊎ (Σ[ y' ∈ Fin n ] y ≡ (thin x y') × ((thick x y) ≡ yes y') ))
lemma2 zero zero = inj₁ (refl , refl)
lemma2 zero (suc y) = inj₂ (y , (refl , refl))
lemma2 {zero} (suc ()) zero
lemma2 {suc n} (suc x) zero = inj₂ (zero , (refl , refl))
lemma2 {zero} (suc ()) (suc y)
lemma2 {suc n} (suc x) (suc y) with lemma2 x y
lemma2 {suc n} (suc x) (suc .x) | inj₁ (refl , thickxx≡no) = inj₁ (refl , cong (λ (a : Maybe (Fin n)) → rf (λ x₁ → yes (suc x₁)) a) thickxx≡no)
lemma2 {suc n} (suc x) (suc y) | inj₂ (y' , proj₂ , proj₃) = inj₂ (suc y' , (cong suc proj₂ , cong (λ a → rf (λ x₁ → yes (suc x₁)) a) proj₃))

fact8 : {n : ℕ} → (x : Fin (suc n)) → (y : Fin (suc n)) → (r : Maybe (Fin n)) → (r ≡ thick x y) →  (((y ≡ x) × r ≡ no) ⊎ (Σ[ y' ∈ Fin n ] y ≡ (thin x y') × (r ≡ yes y') ))
fact8 x y .(thick x y) refl = lemma2 x y

fact9 : {n : ℕ} →  (t' : Term n) →  (x : Fin (suc n)) →  ((_for_ t' x) ∘ thin x) ≐ ι
fact9 {n} t' x y with lemma2 x (thin x y)
fact9 t' x y | inj₁ (proj₁ , proj₂)  with fact6 x y proj₁ 
fact9 t' x y | inj₁ (proj₁ , proj₂) | ()
fact9 t' x y | inj₂ (proj₁ , proj₂ , proj₃) with fact5 x y proj₁ proj₂
fact9 t' x .proj₁ | inj₂ (proj₁ , proj₂ , proj₃) | refl rewrite proj₃ = refl

lemma3 : {n : ℕ} → (f : Fin n → Fin (suc n)) → (t : Term n) → (g : Fin (suc n) → Term n)  → g ◃ (▹ f ◃ t) ≡  (g ∘ f) ◃ t
lemma3 f (ι x) g = refl
lemma3 f leaf g = refl
lemma3 f (t fork t₁) g = cong₂ (λ x x₁ → x fork x₁) (lemma3 f t g) (lemma3 f t₁ g)

lemma6 : {m n : ℕ} → (f : Fin m → Term n) →(g : Fin m → Term n) → (t' : Term m) → (f ≐ g) → (f ◃ t' ≡ g ◃ t')
lemma6 f g (ι x) = λ x₁ → x₁ x
lemma6 f g leaf = λ x → refl
lemma6 f g (t' fork t'') = λ x → cong₂ (λ x₁ x₂ → x₁ fork x₂) (lemma6 f g t' x) (lemma6 f g t'' x)

--((_for_ t' x) ∘ thin x) ≐ ι
lemma4 : {n : ℕ} → (t' : Term n) → (x : Fin (suc n)) →  ((_for_ t' x) ∘ thin x) ◃ t' ≡ t' 
lemma4 t' x = begin
  ((_for_ t' x) ∘ thin x) ◃ t'
  ≡⟨ lemma6 ((t' for x) ∘ thin x) ι t' (fact9 t' x) ⟩
    ι ◃ t'
  ≡⟨ fact2 t' ⟩
  t'
  ∎
lemma7 : {n : ℕ} → (x : Fin (suc n)) → ((thick x x) ≡ no)
lemma7 zero = refl
lemma7 {zero} (suc ())
lemma7 {suc n} (suc x) = cong (rf (λ x₁ → yes (suc x₁))) (lemma7 x) 
--rf (λ x₁ → yes (suc x₁)) (thick x x) ≡ no

lemma5 : {n : ℕ} → (t' : Term n) → (x : Fin (suc n)) →  t' ≡ (t' for x) x
lemma5 t' x rewrite lemma7 x = refl

lemma10 : {A : Set} → {a b : A} → (x y : Maybe A) → ((x ≡ y) × (x ≡ yes a) × (y ≡ yes b)) → (a ≡ b)
lemma10 no no (refl , () , proj₃)
lemma10 no (yes x) (proj₁ , () , proj₃)
lemma10 (yes x) no (proj₁ , proj₂ , ())
lemma10 {A} {.b} {b} (yes .b) (yes .b) (refl , refl , refl) = refl

lemma10' : {A : Set} → {a b : A} → ((yes a) ≡ (yes b)) → (a ≡ b)
lemma10' refl = refl

lemma11 : {A : Set} → {x : A} → (a b : Maybe A) → (f : A → A → A) → ((lrf2 f) a b ≡ yes x) →  Σ[ p' ∈ A ]  Σ[ q' ∈ A ] ((a ≡ yes p') × (b ≡ yes q'))
lemma11 no no f ()
lemma11 no (yes x₁) f ()
lemma11 (yes x₁) no f ()
lemma11 (yes p') (yes q') f refl = p' , q' , refl , refl

lemma8 : {n : ℕ} → (x : Fin (suc n)) → (t : Term (suc n)) → (t' : Term n) → (check x t  ≡  yes t') → (t ≡  (▹ (thin x) ◃ t'))
lemma8 x (ι y) t' p with lemma2 x y
lemma8 x (ι .x) t' p | inj₁ (refl , proj₂) rewrite proj₂ with p
... | ()
lemma8 x (ι y) t' p | inj₂ (y' , proj₁ , proj₂) rewrite proj₂ with lemma10' p
... | a rewrite (sym a) | proj₁ = refl
lemma8 x leaf .leaf refl = refl
lemma8 x (t fork t₁) t' p with lemma11 (check x t) (check x t₁) (_fork_) p
lemma8 x (s₁ fork s₂) t' p | s₁' , s₂' , proj₃ , proj₄ 
                             with lemma8 x s₁ s₁' proj₃ | lemma8 x s₂ s₂' proj₄
... | a | b rewrite proj₃ | proj₄ with lemma10' p
... | c  rewrite (sym c) = cong₂ _fork_ a b

fact10 :{n : ℕ} → (x : Fin (suc n)) → (t : Term (suc n)) → (t' : Term n) → (check x t  ≡  yes t') → (t' for x) ◃ t ≡ (t' for x) x
fact10 {n} x t t' p = begin 
  (t' for x) ◃ t 
  ≡⟨ cong (λ (x₁ : Term (suc n)) → (t' for x) ◃ x₁) (lemma8 x t t' p) ⟩
  (t' for x) ◃ (▹ (thin x) ◃ t')
  ≡⟨ lemma3 (thin x) t' (t' for x)  ⟩
  ((t' for x) ∘ thin x) ◃ t'
  ≡⟨ lemma4 t' x ⟩
  t'
  ≡⟨ lemma5 t' x ⟩
  (t' for x) x
  ∎

--postulate
--  ext : {A B : Set} → (f g : (A → B)) → {x : A} → (f x ≡ g x) → (f ≡ g)
-- thick x p で場合分けすると、証明する式が簡単になる。
-- さらに t' で場合分けをすると ext が必要そうだったところが、引数が渡
--  される形になって ext なしで証明できるようになる。
-- でも、その中で t' に関する再帰が必要になるので、それを別途、相互再帰
--  させて証明する。

mutual
  fact11 : {m n l : ℕ} → (ρ : AList m n) → (σ : AList l m) → (sub (ρ ⊹⊹ σ)) ≐ ((sub ρ) ◇ (sub σ))
  fact11 ρ anil p = refl
  fact11 ρ (σ asnoc t' / x) p with thick x p
  fact11 ρ (σ asnoc t' / x) p | no = fact11' ρ σ t'
  fact11 ρ (σ asnoc t' / x) p | yes y = fact11 ρ σ y

  fact11' : {m n l : ℕ} → (ρ : AList m n) → (σ : AList l m) → (t : Term l) → (sub (ρ ⊹⊹ σ) ◃ t) ≡ sub ρ ◃ (sub σ ◃ t)
  fact11' ρ σ (ι x) = fact11 ρ σ x
  fact11' ρ σ leaf = refl
  fact11' ρ σ (t1 fork t2) = cong₂ _fork_ (fact11' ρ σ t1) (fact11' ρ σ t2)
