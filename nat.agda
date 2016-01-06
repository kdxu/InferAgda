module nat where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Nullary using (¬_)
open import Relation.Binary using (DecTotalOrder)
open import Relation.Binary.PropositionalEquality

---------------------------------------------------------------

m≤m :  ∀ m →  m ≤ m
m≤m m = n≤m+n zero m

≤-trans : ∀ {m j k} → (m≤j : m ≤ j) → (j≤k : j ≤ k) → m ≤ k
≤-trans = DecTotalOrder.trans decTotalOrder

m<′m'→¬m'<′m : {m m' : ℕ} → m <′ m' → ¬ m' <′ m
m<′m'→¬m'<′m {zero} m<′m' ()
m<′m'→¬m'<′m {suc m} {zero} () m'<′m
m<′m'→¬m'<′m {suc m} {suc m'} 1+m<′1+m' 1+m'<′1+m
  with ≤′⇒≤ 1+m<′1+m' | ≤′⇒≤ 1+m'<′1+m
... | s≤s m<′m' | s≤s m'<′m = m<′m'→¬m'<′m (≤⇒≤′ m<′m') (≤⇒≤′ m'<′m)

m<′m'-step : {m m' : ℕ} → m ≤′ m' → (m≤′1+m' : m ≤′ suc m') → Σ[ m≤′m' ∈ m ≤′ m' ] (m≤′1+m' ≡ ≤′-step m≤′m')
m<′m'-step m<′m ≤′-refl with m<′m'→¬m'<′m m<′m m<′m
... | ()
m<′m'-step leq (≤′-step m≤′m') = (m≤′m' , refl)
