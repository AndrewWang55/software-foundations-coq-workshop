module istinitosna_funkcionalnost where

open import Relation.Binary.Core using (_≡_; refl )


data ℕ : Set where
  zero : ℕ 
  succ : ℕ -> ℕ

data bool : Set where
  ⊤ ⊥ : bool

iskazno-slovo = ℕ

¬ᵇ : bool -> bool
¬ᵇ ⊤ = ⊥
¬ᵇ ⊥ = ⊤

_∧ᵇ_  : bool -> bool -> bool
⊤ ∧ᵇ q = q
⊥ ∧ᵇ q = ⊥

valuacija = iskazno-slovo -> bool

data formula : Set where
  p : iskazno-slovo -> formula
  ¬ : formula -> formula
  _∧_ : formula -> formula -> formula

_⟦_⟧ : valuacija -> formula -> bool
v ⟦ p x ⟧ = v x
v ⟦ ¬ f ⟧ = ¬ᵇ ( v ⟦ f ⟧ )
v ⟦ f1 ∧ f2 ⟧ = (v ⟦ f1 ⟧ ) ∧ᵇ (v ⟦ f2 ⟧)


skup-iskaznih-slova = iskazno-slovo -> Set

_∈_ : iskazno-slovo -> skup-iskaznih-slova -> Set
x ∈ P = P x

data singlton (x : iskazno-slovo) : skup-iskaznih-slova where
  singl : x ∈ (singlton x)

data _∪_ (A : skup-iskaznih-slova)  (B : skup-iskaznih-slova)
  : skup-iskaznih-slova where
  unija-sleva : { x : iskazno-slovo } -> ( x ∈ A ) ->
    (x ∈ ( A ∪ B ))
  unija-zdesna : { x : iskazno-slovo } -> ( x ∈ B ) ->
    (x ∈ ( A ∪ B ))

thm : zero ∈ ((singlton zero) ∪ (singlton (succ zero)))
thm = unija-sleva singl

-- Skup iskaznih slova koja se javljaju u formuli
π : formula -> skup-iskaznih-slova
π (p x) = singlton x
π (¬ f) = π f
π (f1 ∧ f2) = ( π f1 ) ∪  ( π f2 )


teorema-o-istinitosnoj-funkc :
  (f : formula) ->
  {v' v'' : valuacija} ->
  ({p : iskazno-slovo} -> (p ∈ ( π f )) -> (v' p) ≡ (v'' p)) ->
  ( v' ⟦ f ⟧ ≡ v'' ⟦ f ⟧ )
teorema-o-istinitosnoj-funkc (p x) h = h singl
teorema-o-istinitosnoj-funkc (¬ f) h rewrite
  ( teorema-o-istinitosnoj-funkc f h) = refl
teorema-o-istinitosnoj-funkc (f1 ∧ f2) h rewrite
  (teorema-o-istinitosnoj-funkc f1  (\i-u-f1 -> h (unija-sleva i-u-f1)))  |
  (teorema-o-istinitosnoj-funkc f2  (\i-u-f2 -> h (unija-zdesna i-u-f2))) 
  = refl
