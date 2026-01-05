{-# OPTIONS --cubical --guardedness -WnoUnreachableClauses #-}

module MorphogeneticAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_; predℕ)
open import Cubical.Data.Nat.Properties using (discreteℕ; +-suc; +-comm; znots; +-assoc)
open import Cubical.Data.Nat.Order using (_≤_; _<_)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)
open import Cubical.Data.Empty using (⊥) renaming (elim to ⊥-elim)
open import Cubical.Data.Bool using (Bool; if_then_else_; true; false; not)

------------------------------------------------------------------------------
-- 1. 距離空間の定義
------------------------------------------------------------------------------
Length = ℕ

record MetricSpace : Type₁ where
 field
   Carrier   : Type
   dist      : Carrier → Carrier → Length
   dist-refl : ∀ x → dist x x ≡ 0
   dist-zero : ∀ {x y} → dist x y ≡ 0 → x ≡ y
   dist-tri  : ∀ x y z → dist x z ≤ (dist x y + dist y z)

------------------------------------------------------------------------------
-- 2. WDN (World Design Network) インスタンス
------------------------------------------------------------------------------

node-order = 0
node-gen   = 1
node-str   = 2

wdn-dist : ℕ → ℕ → ℕ
wdn-dist 0 1 = 2; wdn-dist 1 0 = 2
wdn-dist 1 2 = 3; wdn-dist 2 1 = 3
wdn-dist 0 2 = 5; wdn-dist 2 0 = 5
wdn-dist m n with discreteℕ m n
... | yes _ = 0
... | no  _ = 10

postulate
 wdn-refl : ∀ x → wdn-dist x x ≡ 0
 wdn-zero : ∀ {x y} → wdn-dist x y ≡ 0 → x ≡ y
 wdn-tri  : ∀ x y z → wdn-dist x z ≤ (wdn-dist x y + wdn-dist y z)

exampleMS : MetricSpace
exampleMS = record
 { Carrier   = ℕ
 ; dist      = wdn-dist
 ; dist-refl = wdn-refl
 ; dist-zero = wdn-zero
 ; dist-tri  = wdn-tri
 }

------------------------------------------------------------------------------
-- 3. ホモロジーの構造定義
------------------------------------------------------------------------------

data Fin : ℕ → Type where
 fzero : {n : ℕ} → Fin (suc n)
 fsuc  : {n : ℕ} → Fin n → Fin (suc n)

weakenFin : {n : ℕ} → Fin n → Fin (suc n)
weakenFin fzero    = fzero
weakenFin (fsuc i) = fsuc (weakenFin i)

skip : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)
skip {zero}  fzero ()
skip {suc n} fzero i = fsuc i
skip {suc n} (fsuc i) fzero    = fzero
skip {suc n} (fsuc i) (fsuc j) = fsuc (skip i j)

sumDist : (MS : MetricSpace) → {n : ℕ} → (Fin n → MetricSpace.Carrier MS) → ℕ
sumDist MS {zero} xs = 0
sumDist MS {suc zero} xs = 0
sumDist MS {suc (suc n)} xs =
 MetricSpace.dist MS (xs fzero) (xs (fsuc fzero)) +
 sumDist MS {suc n} (λ i → xs (fsuc i))

record GenChain (MS : MetricSpace) (n : ℕ) (l : ℕ) : Type where
 constructor gen
 field
   xs       : Fin (suc n) → MetricSpace.Carrier MS
   adjDiff  : (i : Fin n) → ¬ (xs (weakenFin i) ≡ xs (fsuc i))
   totalLen : sumDist MS xs ≡ l

data Chain (MS : MetricSpace) (n : ℕ) (l : ℕ) : Type where
 zeroC : Chain MS n l
 pos   : GenChain MS n l → Chain MS n l
 neg   : GenChain MS n l → Chain MS n l
 _+C_  : Chain MS n l → Chain MS n l → Chain MS n l

------------------------------------------------------------------------------
-- 4. 境界演算子と簡略化のロジック
------------------------------------------------------------------------------

isEven : ℕ → Bool
isEven zero = true
isEven (suc n) = not (isEven n)

module BoundaryImpl (MS : MetricSpace) where
 open MetricSpace MS

 flip-sign : {n : ℕ} {l : ℕ} → Chain MS n l → Chain MS n l
 flip-sign zeroC = zeroC
 flip-sign (pos g) = neg g
 flip-sign (neg g) = pos g
 flip-sign (c1 +C c2) = flip-sign c1 +C flip-sign c2

 -- ユーザー様提案：冗長な zeroC を取り除くスマート加算
 _⊕_ : {n : ℕ} {l : ℕ} → Chain MS n l → Chain MS n l → Chain MS n l
 zeroC ⊕ c2 = c2
 c1 ⊕ zeroC = c1
 c1 ⊕ c2 = c1 +C c2

 simplify : {n : ℕ} {l : ℕ} → Chain MS n l → Chain MS n l
 simplify zeroC = zeroC
 simplify (pos g) = pos g
 simplify (neg g) = neg g
 simplify (c1 +C c2) = (simplify c1) ⊕ (simplify c2)

 face-xs : {n : ℕ} → (Fin (suc (suc n)) → Carrier) → Fin (suc (suc n)) → (Fin (suc n) → Carrier)
 face-xs xs i j = xs (skip i j)

 fromNatIdx : (n : ℕ) → (i : ℕ) → Fin (suc n)
 fromNatIdx zero _ = fzero
 fromNatIdx (suc n) zero = fzero
 fromNatIdx (suc n) (suc i) = fsuc (fromNatIdx n i)

 postulate
   prove-new-adj : {n : ℕ} {l : ℕ} (g : GenChain MS (suc n) l) (i : ℕ)
                 (p : sumDist MS (face-xs (GenChain.xs g) (fromNatIdx (suc n) i)) ≡ l)
                 → (j : Fin n) → ¬ (face-xs (GenChain.xs g) (fromNatIdx (suc n) i) (weakenFin j) ≡ face-xs (GenChain.xs g) (fromNatIdx (suc n) i) (fsuc j))

 compute-face : {n : ℕ} {l : ℕ} → GenChain MS (suc n) l → (i : ℕ) → Chain MS n l
 compute-face {n} {l} g i with discreteℕ i 0
 ... | yes _ = zeroC
 ... | no  _ with discreteℕ i (suc n)
 ... | yes _ = zeroC
 ... | no  _ with discreteℕ (sumDist MS (face-xs (GenChain.xs g) (fromNatIdx (suc n) i))) l
 ... | yes p =
     let res = pos (gen (face-xs (GenChain.xs g) (fromNatIdx (suc n) i)) (prove-new-adj g i p) p)
     in if isEven i then res else flip-sign res
 ... | no  _ = zeroC

 sum-faces : {n : ℕ} {l : ℕ} → GenChain MS (suc n) l → (count : ℕ) → Chain MS n l
 sum-faces g zero = compute-face g zero
 sum-faces g (suc count) = compute-face g (suc count) +C sum-faces g count

boundary : ∀ {MS n l} → Chain MS (suc n) l → Chain MS n l
boundary zeroC = zeroC
boundary {MS} {n} {l} (pos g) = BoundaryImpl.sum-faces MS g (suc n)
boundary {MS} {n} {l} (neg g) = BoundaryImpl.flip-sign MS (BoundaryImpl.sum-faces MS g (suc n))
boundary (c1 +C c2) = boundary c1 +C boundary c2

------------------------------------------------------------------------------
-- 5. 具体的なパスと最終検証
------------------------------------------------------------------------------

xs-example : Fin 3 → ℕ
xs-example fzero = node-order
xs-example (fsuc fzero) = node-gen
xs-example (fsuc (fsuc fzero)) = node-str

adj-example : (i : Fin 2) → ¬ (xs-example (weakenFin i) ≡ xs-example (fsuc i))
adj-example fzero p = znots p
adj-example (fsuc fzero) p = znots (cong predℕ p)

examplePath : GenChain exampleMS 2 5
examplePath = gen xs-example adj-example refl

-- 正規化 (C-c C-n) すると neg (gen ...) が得られます！
finalResult : Chain exampleMS 1 5
finalResult = BoundaryImpl.simplify exampleMS (boundary (pos examplePath))

-- ユーザー様提案の「直通ルート」： 0 (秩序) から 2 (強度) へ
directPath : GenChain exampleMS 1 5
directPath = gen xs adj refl
 where
   xs : Fin 2 → ℕ
   xs fzero = node-order
   xs (fsuc fzero) = node-str
  
   adj : (i : Fin 1) → ¬ (xs (weakenFin i) ≡ xs (fsuc i))
   -- p : 0 ≡ 2 です。これは 0 ≡ suc 1 なので、そのまま znots に渡せます。
   adj fzero p = znots p