## Total type over a contractible type

We show that a ∑-type with contractible base is equivalent to the dependent type
evaluated at the point of contraction.

```rzk
#def total-type-center-fiber-is-contr-base
  ( A : U)
  ( is-contr-A : is-contr A)
  ( C : A → U)
  : ( C (center-contraction A is-contr-A))
  → ( Σ ( x : A) , C x)
  :=
    \ v → ((center-contraction A is-contr-A) , v)

#def center-fiber-total-type-is-contr-base
  ( A : U)
  ( is-contr-A : is-contr A)
  ( C : A → U)
  : ( Σ ( x : A) , C x)
  → ( C (center-contraction A is-contr-A))
  :=
    \ (x , u) →
      transport
        ( A)
        ( C)
        ( x)
        ( center-contraction A is-contr-A)
        ( rev
          ( A)
          ( center-contraction A is-contr-A)
          ( x)
          ( homotopy-contraction A is-contr-A x))
        ( u)

#def has-retraction-center-fiber-total-type-is-contr-base
  ( A : U)
  ( is-contr-A : is-contr A)
  ( C : A → U)
  : has-retraction
    ( Σ ( x : A) , C x)
    ( C (center-contraction A is-contr-A))
    ( center-fiber-total-type-is-contr-base A is-contr-A C)
  :=
    ( ( total-type-center-fiber-is-contr-base A is-contr-A C)
    , \ (x , u) →
        ( rev
          ( Σ ( x : A) , C x)
          ( x , u)
          ( total-type-center-fiber-is-contr-base A is-contr-A C
            ( center-fiber-total-type-is-contr-base A is-contr-A C (x , u)))
          ( transport-lift A C
              ( x)
              ( center-contraction A is-contr-A)
              ( rev
                ( A)
                ( center-contraction A is-contr-A)
                ( x)
                ( homotopy-contraction A is-contr-A x))
              ( u))))

#def has-section-center-fiber-total-type-is-contr-base
  ( A : U)
  ( is-contr-A : is-contr A)
  ( C : A → U)
  : has-section
    ( Σ ( x : A) , C x)
    ( C (center-contraction A is-contr-A))
    ( center-fiber-total-type-is-contr-base A is-contr-A C)
  :=
    ( ( total-type-center-fiber-is-contr-base A is-contr-A C)
    , \ u →
        ( transport2
          ( A)
          ( C)
          ( center-contraction A is-contr-A)
          ( center-contraction A is-contr-A)
          ( rev
            ( A)
            ( center-contraction A is-contr-A)
            ( center-contraction A is-contr-A)
            ( homotopy-contraction A is-contr-A
              ( center-contraction A is-contr-A)))
          ( refl)
          ( all-paths-equal-is-contr
            ( A)
            ( is-contr-A)
            ( center-contraction A is-contr-A)
            ( center-contraction A is-contr-A)
            ( rev
              ( A)
              ( center-contraction A is-contr-A)
              ( center-contraction A is-contr-A)
              ( homotopy-contraction A is-contr-A
                ( center-contraction A is-contr-A)))
            ( refl))
          ( u)))

#def equiv-center-fiber-total-type-is-contr-base
  ( A : U)
  ( is-contr-A : is-contr A)
  ( C : A → U)
  : Equiv
    ( Σ ( x : A) , C x)
    ( C (center-contraction A is-contr-A))
  :=
    ( ( center-fiber-total-type-is-contr-base A is-contr-A C)
    , ( ( ( has-retraction-center-fiber-total-type-is-contr-base
            A is-contr-A C)
      , ( has-section-center-fiber-total-type-is-contr-base
            A is-contr-A C))))
```

Any two elements in a contractible type are equal, so we extend the equivalence
to the dependent type evaluated at any given term in the base.

```rzk
#def transport-equiv-center-fiber-total-type-is-contr-base
  ( A : U)
  ( is-contr-A : is-contr A)
  ( C : A → U)
  ( a : A)
  : Equiv
    ( Σ ( x : A) , C x)
    ( C a)
  :=
    equiv-comp
      ( Σ ( x : A) , C x)
      ( C (center-contraction A is-contr-A))
      ( C a)
      ( equiv-center-fiber-total-type-is-contr-base A is-contr-A C)
      ( equiv-transport
        ( A)
        ( C)
        ( center-contraction A is-contr-A)
        ( a)
        ( homotopy-contraction A is-contr-A a))
```

## Weak function extensionality implies function extensionality

Using the fundamental theorem of identity types, we prove the converse of
`weakfunext-funext`, so we now know that `#!rzk FunExt` is logically equivalent
to `#!rzk WeakFunExt`. We follow the proof in Rijke, section 13.1.

We first fix one of the two functions and show that `#!rzk WeakFunExt` implies a
version of function extensionality that asserts that a type of "maps together
with homotopies" is contractible.

```rzk
#def components-dhomotopy
  ( A : U)
  ( C : A → U)
  ( f : (x : A) → C x)
  : ( Σ ( g : (x : A) → C x)
      , ( dhomotopy A C f g))
  → ( ( x : A)
    → ( Σ ( c : (C x))
      , ( f x =_{C x} c)))
  :=
    \ (g , H) →
      ( \ x →
        ( g x , H x))

#def has-retraction-components-dhomotopy
  ( A : U)
  ( C : A → U)
  ( f : (x : A) → C x)
  : has-retraction
      ( Σ ( g : (x : A) → C x)
        , ( dhomotopy A C f g))
      ( ( x : A)
        → ( Σ ( c : (C x))
          , ( f x =_{C x} c)))
      ( components-dhomotopy A C f)
  :=
    ( ( \ G →
        ( \ x → first (G x) , \ x → second (G x)))
    , \ x → refl)

#def is-retract-components-dhomotopy
  ( A : U)
  ( C : A → U)
  ( f : (x : A) → C x)
  : is-retract-of
      ( Σ ( g : (x : A) → C x)
        , ( dhomotopy A C f g))
      ( ( x : A)
        → ( Σ ( c : (C x))
          , ( f x =_{C x} c)))
  :=
    ( components-dhomotopy A C f
    , has-retraction-components-dhomotopy A C f)

#def WeirdFunExt
  : U
  :=
    ( A : U) → (C : A → U)
  → ( f : (x : A) → C x)
  → is-contr
      ( Σ ( g : (x : A) → C x)
        , ( dhomotopy A C f g))

#def weirdfunext-weakfunext
  ( weakfunext : WeakFunExt)
  : WeirdFunExt
  :=
    \ A C f →
      is-contr-is-retract-of-is-contr
        ( Σ ( g : (x : A) → C x)
          , ( dhomotopy A C f g))
        ( ( x : A)
          → ( Σ ( c : (C x))
              , ( f x =_{C x} c)))
        ( is-retract-components-dhomotopy A C f)
        ( weakfunext
          ( A)
          ( \ x → Σ (c : (C x)) , (f x =_{C x} c))
          ( \ x → is-contr-based-paths (C x) (f x)))
```

We now use the fundamental theorem of identity types to go from the version for
a fixed f to the total `#!rzk FunExt` axiom.

```rzk
#def funext-weirdfunext
  ( weirdfunext : WeirdFunExt)
  : FunExt
  :=
    \ A C f g →
      are-equiv-from-paths-is-contr-total
        ( ( x : A) → C x)
        ( f)
        ( \ h → dhomotopy A C f h)
        ( \ h → htpy-eq A C f h)
        ( weirdfunext A C f)
        ( g)

#def funext-weakfunext
  ( weakfunext : WeakFunExt)
  : FunExt
  :=
    funext-weirdfunext (weirdfunext-weakfunext weakfunext)
```

The proof of `weakfunext-funext` from `06-contractible.rzk` works with a version
of function extensionality only requiring the map in the converse direction. We
can then prove a cycle of implications between `#!rzk FunExt`,
`#!rzk NaiveFunExt` and `#!rzk WeakFunExt`.

```rzk
#def NaiveFunExt
  : U
  :=
    ( A : U) → (C : A → U)
  → ( f : (x : A) → C x)
  → ( g : (x : A) → C x)
  → ( p : (x : A) → f x = g x)
  → ( f = g)

#def naivefunext-funext
  ( funext : FunExt)
  : NaiveFunExt
  :=
    \ A C f g p →
      eq-htpy funext A C f g p

#def weakfunext-naivefunext
  ( naivefunext : NaiveFunExt)
  : WeakFunExt
  :=
    \ A C is-contr-C →
      ( map-weakfunext A C is-contr-C
      , ( \ g →
          ( naivefunext
            ( A)
            ( C)
            ( map-weakfunext A C is-contr-C)
            ( g)
          ( \ a → second (is-contr-C a) (g a)))))
```

## Dependent composition

In a covariant family over a Segal type, we will define dependent composition of
arrows. We first apply the result that the total type is Segal as follows.

```rzk
#def is-contr-horn-ext-is-covariant-family-is-segal-base uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( a : (t : Λ) → A)
  ( c : (t : Λ) → C (a t))
  : is-contr
    ( Σ ( f : ((t : Δ²) → A [Λ t ↦ a t]))
      , ( ( t : Δ²) → C (f t) [Λ t ↦ c t]))
  :=
    is-contr-equiv-is-contr
      ( ( t : Δ²) → (Σ (x : A) , C x) [Λ t ↦ (a t , c t)])
      ( Σ ( f : ((t : Δ²) → A [Λ t ↦ a t]))
        , ( ( t : Δ²) → C (f t) [Λ t ↦ c t]))
      ( axiom-choice
        ( 2 × 2)
        ( Δ²)
        ( \ t → Λ t)
        ( \ t → A)
        ( \ t → \ x → C x)
        ( a)
        ( c))
      ( has-unique-inner-extensions-is-segal
        ( Σ ( x : A) , C x)
        ( is-segal-total-type-covariant-family-is-segal-base
          A C is-covariant-C is-segal-A)
        ( \ t → (a t , c t)))

#def equiv-comp-horn-ext-is-segal-base
  ( A : U)
  ( is-segal-A : is-segal A)
  ( C : A → U)
  ( a : (t : Λ) → A)
  ( c : (t : Λ) → C (a t))
  : Equiv
    ( Σ ( f : ((t : Δ²) → A [Λ t ↦ a t]))
    , ( ( t : Δ²) → C (f t) [Λ t ↦ c t]))
    ( ( t : Δ²)
      → C (witness-comp-is-segal A is-segal-A (a (0₂ , 0₂)) (a (1₂ , 0₂))
          ( a (1₂ , 1₂)) (\ s → a (s , 0₂)) (\ s → a (1₂ , s)) t) [Λ t ↦ c t])
  :=
    transport-equiv-center-fiber-total-type-is-contr-base
      ( ( t : Δ²) → A [Λ t ↦ a t])
      ( has-unique-inner-extensions-is-segal A is-segal-A a)
      ( \ f → ((t : Δ²) → C (f t) [Λ t ↦ c t]))
      ( witness-comp-is-segal A is-segal-A (a (0₂ , 0₂)) (a (1₂ , 0₂))
          ( a (1₂ , 1₂)) (\ s → a (s , 0₂)) (\ s → a (1₂ , s)))

#def is-contr-comp-horn-ext-is-covariant-family-is-segal-base uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( a : (t : Λ) → A)
  ( c : (t : Λ) → C (a t))
  : is-contr
    ( ( t : Δ²)
      → C (witness-comp-is-segal A is-segal-A (a (0₂ , 0₂)) (a (1₂ , 0₂))
          ( a (1₂ , 1₂)) (\ s → a (s , 0₂)) (\ s → a (1₂ , s)) t) [Λ t ↦ c t])
  :=
    is-contr-equiv-is-contr
      ( Σ ( f : ((t : Δ²) → A [Λ t ↦ a t]))
      , ( ( t : Δ²) → C (f t) [Λ t ↦ c t]))
      ( ( t : Δ²)
        → C (witness-comp-is-segal A is-segal-A (a (0₂ , 0₂)) (a (1₂ , 0₂))
            ( a (1₂ , 1₂)) (\ s → a (s , 0₂)) (\ s → a (1₂ , s)) t) [Λ t ↦ c t])
      ( equiv-comp-horn-ext-is-segal-base A is-segal-A C a c)
      ( is-contr-horn-ext-is-covariant-family-is-segal-base
        A is-segal-A C is-covariant-C a c)

#def dhorn
  ( A : U)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( C : A → U)
  ( u : C x)
  ( v : C y)
  ( w : C z)
  ( ff : dhom A x y f C u v)
  ( gg : dhom A y z g C v w)
  : ( ( t : Λ) → C (horn A x y z f g t))
  :=
    \ (t , s) →
      recOR
        ( s ≡ 0₂ ↦ ff t
        , t ≡ 1₂ ↦ gg s)

#def dcompositions-are-dhorn-fillings
  ( A : U)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( h : hom A x z)
  ( α : hom2 A x y z f g h)
  ( C : A → U)
  ( u : C x)
  ( v : C y)
  ( w : C z)
  ( ff : dhom A x y f C u v)
  ( gg : dhom A y z g C v w)
  : Equiv
    ( Σ ( hh : dhom A x z h C u w)
      , ( dhom2 A x y z f g h α C u v w ff gg hh))
    ( ( t : Δ²) → C (α t) [Λ t ↦ dhorn A x y z f g C u v w ff gg t])
  :=
    ( \ (hh , H) t → H t
    , ( ( \ k → (\ t → k (t , t) , \ (t , s) → k (t , s))
        , \ (hh , H) → refl)
      , ( \ k → (\ t → k (t , t) , \ (t , s) → k (t , s))
        , \ (hh , H) → refl)))
```

We now prove contractibility of a type that will be used to define dependent
composition.

```rzk title="RS17, Remark 8.11"
#def is-contr-dhom2-comp-is-covariant-family-is-segal-base uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( u : C x)
  ( v : C y)
  ( w : C z)
  ( ff : dhom A x y f C u v)
  ( gg : dhom A y z g C v w)
  : is-contr
    ( Σ ( hh : dhom A x z (comp-is-segal A is-segal-A x y z f g) C u w)
      , dhom2 A x y z f g (comp-is-segal A is-segal-A x y z f g)
        ( witness-comp-is-segal A is-segal-A x y z f g) C u v w ff gg hh)
  :=
    is-contr-equiv-is-contr'
      ( Σ ( hh : dhom A x z (comp-is-segal A is-segal-A x y z f g) C u w)
        , dhom2 A x y z f g (comp-is-segal A is-segal-A x y z f g)
          ( witness-comp-is-segal A is-segal-A x y z f g) C u v w ff gg hh)
      ( ( t : Δ²) → C ((witness-comp-is-segal A is-segal-A x y z f g) t)
                    [Λ t ↦ dhorn A x y z f g C u v w ff gg t])
      ( dcompositions-are-dhorn-fillings A x y z f g
        ( comp-is-segal A is-segal-A x y z f g)
        ( witness-comp-is-segal A is-segal-A x y z f g)
          C u v w ff gg)
      ( is-contr-comp-horn-ext-is-covariant-family-is-segal-base
        ( A)
        ( is-segal-A)
        ( C)
        ( is-covariant-C)
        ( horn A x y z f g)
        ( dhorn A x y z f g C u v w ff gg))

#def dcomp-is-covariant-family-is-segal-base uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( u : C x)
  ( v : C y)
  ( w : C z)
  ( ff : dhom A x y f C u v)
  ( gg : dhom A y z g C v w)
  : dhom A x z (comp-is-segal A is-segal-A x y z f g) C u w
  :=
    ( first
      ( first
        ( is-contr-dhom2-comp-is-covariant-family-is-segal-base
          A is-segal-A C is-covariant-C x y z f g u v w ff gg)))

#def witness-dcomp-is-covariant-family-is-segal-base uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( u : C x)
  ( v : C y)
  ( w : C z)
  ( ff : dhom A x y f C u v)
  ( gg : dhom A y z g C v w)
  : dhom2 A x y z f g (comp-is-segal A is-segal-A x y z f g)
      ( witness-comp-is-segal A is-segal-A x y z f g) C u v w ff gg
        ( dcomp-is-covariant-family-is-segal-base
          A is-segal-A C is-covariant-C x y z f g u v w ff gg)
  :=
    ( second
      ( first
        ( is-contr-dhom2-comp-is-covariant-family-is-segal-base
          A is-segal-A C is-covariant-C x y z f g u v w ff gg)))
```

Dependent composition is unique.

```rzk
#def uniqueness-dcomp-is-covariant-family-is-segal-base uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( u : C x)
  ( v : C y)
  ( w : C z)
  ( ff : dhom A x y f C u v)
  ( gg : dhom A y z g C v w)
  ( hh : dhom A x z (comp-is-segal A is-segal-A x y z f g) C u w)
  ( H : dhom2 A x y z f g (comp-is-segal A is-segal-A x y z f g)
        ( witness-comp-is-segal A is-segal-A x y z f g) C u v w ff gg hh)
  : ( dcomp-is-covariant-family-is-segal-base
      A is-segal-A C is-covariant-C x y z f g u v w ff gg) = hh
  :=
    first-path-Σ
      ( dhom A x z (comp-is-segal A is-segal-A x y z f g) C u w)
      ( \ hh →
          dhom2 A x y z f g (comp-is-segal A is-segal-A x y z f g)
          ( witness-comp-is-segal A is-segal-A x y z f g) C u v w ff gg hh)
      ( ( dcomp-is-covariant-family-is-segal-base
          A is-segal-A C is-covariant-C x y z f g u v w ff gg)
        , ( witness-dcomp-is-covariant-family-is-segal-base
            A is-segal-A C is-covariant-C x y z f g u v w ff gg))
      ( hh , H)
      ( homotopy-contraction
        ( ( Σ ( hh : dhom A x z (comp-is-segal A is-segal-A x y z f g) C u w)
        , dhom2 A x y z f g (comp-is-segal A is-segal-A x y z f g)
          ( witness-comp-is-segal A is-segal-A x y z f g) C u v w ff gg hh))
        ( is-contr-dhom2-comp-is-covariant-family-is-segal-base
          A is-segal-A C is-covariant-C x y z f g u v w ff gg)
        ( hh , H))
```

# 2-Segal spaces

Experimental formalization project on 2-Segal spaces.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#assume funext : FunExt
-- #assume weakextext : WeakExtExt
#assume extext : ExtExt
```

### The 3 dimensional 2-Segal horns

```rzk
#def Λ³₍₀₂₎
  : Δ³ → TOPE
  :=
    \ ((t1 , t2) , t3) → t3 ≡ 0₂ ∨ t1 ≡ t2 -- This could be t3==t2.

#def Λ³₍₁₃₎
  : Δ³ → TOPE
  :=
    \ ((t1 , t2) , t3) → t2 ≡ t3 ∨ t1 ≡ 1₂ -- This could be t1==t2.

#def 3-horn-restriction₍₀₂₎
  ( A : U)
  : ( Δ³ → A) → (Λ³₍₀₂₎ → A)
  := \ f t → f t

#def 3-horn-restriction₍₁₃₎
  ( A : U)
  : ( Δ³ → A) → (Λ³₍₁₃₎ → A)
  := \ f t → f t
```

### 2-Segal types

We use the conventions from the definition of `#!rzk hom3` from
`11-adjunctions.rzk`.

```rzk
#def is-2-segal₍₀₂₎
  ( A : U)
  : U
  :=
    ( w : A) → (x : A) → (y : A) → (z : A)
  → ( f : hom A w x) → (gf : hom A w y) → (hgf : hom A w z)
  → ( g : hom A x y) → (h : hom A y z)
  → ( α₃ : hom2 A w x y f g gf) → (α₁ : hom2 A w y z gf h hgf)
  → is-contr
      ( Σ ( hg : hom A x z)
      , ( Σ ( α₂ : hom2 A w x z f hg hgf)
        , ( Σ ( α₀ : hom2 A x y z g h hg)
            , hom3 A w x y z f gf hgf g hg h α₃ α₂ α₁ α₀)))

#def is-2-segal₍₁₃₎
  ( A : U)
  : U
  :=
    ( w : A) → (x : A) → (y : A) → (z : A)
  → ( f : hom A w x) → (hgf : hom A w z)
  → ( g : hom A x y) → (hg : hom A x z) → (h : hom A y z)
  → ( α₂ : hom2 A w x z f hg hgf) → (α₀ : hom2 A x y z g h hg)
  → is-contr
      ( Σ ( gf : hom A w y)
      , ( Σ ( α₃ : hom2 A w x y f g gf)
        , ( Σ ( α₁ : hom2 A w y z gf h hgf)
            , hom3 A w x y z f gf hgf g hg h α₃ α₂ α₁ α₀)))

#def is-2-segal
  ( A : U)
  : U
  :=
    product (is-2-segal₍₀₂₎ A) (is-2-segal₍₁₃₎ A)
```

```rzk
#def 3horn₍₀₂₎
  ( A : U)
  ( w x y z : A)
  ( f : hom A w x)
  ( gf : hom A w y)
  ( hgf : hom A w z)
  ( g : hom A x y)
  ( h : hom A y z)
  ( α₃ : hom2 A w x y f g gf)
  ( α₁ : hom2 A w y z gf h hgf)
  : Λ³₍₀₂₎ → A
  :=
    \ ((t₁ , t₂) , t₃) →
      recOR
        ( t₃ ≡ 0₂ ↦ α₃ (t₁ , t₂)
        , t₁ ≡ t₂ ↦ α₁ (t₁ , t₃)) -- This could be t3==t2.

#def 3horn₍₁₃₎
  ( A : U)
  ( w x y z : A)
  ( f : hom A w x)
  ( hgf : hom A w z)
  ( g : hom A x y)
  ( hg : hom A x z)
  ( h : hom A y z)
  ( α₂ : hom2 A w x z f hg hgf)
  ( α₀ : hom2 A x y z g h hg)
  : Λ³₍₁₃₎ → A
  :=
  \ ((t₁ , t₂) , t₃) →
    recOR
      ( t₂ ≡ t₃ ↦ α₂ (t₁ , t₃) -- This could be t1==t2.
      , t₁ ≡ 1₂ ↦ α₀ (t₂ , t₃))

#def associators-are-3horn-fillings₍₀₂₎
  ( A : U)
  ( w x y z : A)
  ( f : hom A w x)
  ( gf : hom A w y)
  ( hgf : hom A w z)
  ( g : hom A x y)
  ( h : hom A y z)
  ( α₃ : hom2 A w x y f g gf)
  ( α₁ : hom2 A w y z gf h hgf)
  : Equiv
      ( Σ ( hg : hom A x z)
      , ( Σ ( α₂ : hom2 A w x z f hg hgf)
        , ( Σ ( α₀ : hom2 A x y z g h hg)
            , hom3 A w x y z f gf hgf g hg h α₃ α₂ α₁ α₀)))
      ( ( t : Δ³) → A [Λ³₍₀₂₎ t ↦ 3horn₍₀₂₎ A w x y z f gf hgf g h α₃ α₁ t])
  :=
    ( \ H t → second (second (second H)) t
      , ( ( ( \ k → (\ t → k ((1₂ , t) , t)
          , ( \ (t , s) → k ((t , s) , s)
            , ( \ (t , s) → k ((1₂ , t) , s)
              , \ ((t1 , t2) , t3) → k ((t1 , t2) , t3))))
          , \ H → refl))
        , ( ( \ k → (\ t → k ((1₂ , t) , t)
            , ( \ (t , s) → k ((t , s) , s)
              , ( \ (t , s) → k ((1₂ , t) , s)
                , \ ((t1 , t2) , t3) → k ((t1 , t2) , t3))))
            , \ H → refl))))

#def associators-are-3horn-fillings₍₁₃₎
  ( A : U)
  ( w x y z : A)
  ( f : hom A w x)
  ( hgf : hom A w z)
  ( g : hom A x y)
  ( hg : hom A x z)
  ( h : hom A y z)
  ( α₂ : hom2 A w x z f hg hgf)
  ( α₀ : hom2 A x y z g h hg)
  : Equiv
      ( Σ ( gf : hom A w y)
      , ( Σ ( α₃ : hom2 A w x y f g gf)
        , ( Σ ( α₁ : hom2 A w y z gf h hgf)
            , hom3 A w x y z f gf hgf g hg h α₃ α₂ α₁ α₀)))
      ( ( t : Δ³) → A [Λ³₍₁₃₎ t ↦ 3horn₍₁₃₎ A w x y z f hgf g hg h α₂ α₀ t])
  :=
    ( \ H t → second (second (second H)) t
      , ( ( ( \ k → (\ t → k ((t , t) , 0₂)
          , ( \ (t , s) → k ((t , s) , 0₂)
            , ( \ (t , s) → k ((t , t) , s)
              , \ ((t1 , t2) , t3) → k ((t1 , t2) , t3))))
          , \ H → refl))
        , ( ( \ k → (\ t → k ((t , t) , 0₂)
            , ( \ (t , s) → k ((t , s) , 0₂)
              , ( \ (t , s) → k ((t , t) , s)
                , \ ((t1 , t2) , t3) → k ((t1 , t2) , t3))))
            , \ H → refl))))
```

```rzk
#def hom-coslice-hom2
  ( A : U)
  ( w x y : A)
  ( f : hom A w x)
  ( gf : hom A w y)
  : ( Σ ( g : hom A x y) , (hom2 A w x y f g gf))
  → hom (coslice A w) (x , f) (y , gf)
  :=
    \ (g , α₃) t →
      ( g t
      , \ s →
          recOR
            ( s ≤ t ↦ gf s
            , t ≤ s ↦ α₃ (s , t)))
```

### Characterizing 2-Segal types

A type is 2-Segal if and only if it is local with respect to both 2-Segal horn
inclusions.

```rzk
#def is-local-2-segal-horn-inclusion
  ( A : U)
  : U
  :=
    product
     ( is-local-type (2 × 2 × 2) Δ³ Λ³₍₀₂₎ A)
     ( is-local-type (2 × 2 × 2) Δ³ Λ³₍₁₃₎ A)

#def equiv-2-segal-horn-restriction₍₀₂₎
  ( A : U)
  : Equiv
    ( Δ³ → A)
    ( Σ ( k : Λ³₍₀₂₎ → A)
      , ( Σ ( hg : hom A (k ((1₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 1₂)))
          , ( Σ ( α₂ : hom2
                        ( A)
                        ( k ((0₂ , 0₂) , 0₂))
                        ( k ((1₂ , 0₂) , 0₂))
                        ( k ((1₂ , 1₂) , 1₂))
                        ( \ t → k ((t , 0₂) , 0₂))
                        ( hg)
                        ( \ t → k ((t , t) , t)))
              , ( Σ ( α₀ : hom2
                            ( A)
                            ( k ((1₂ , 0₂) , 0₂))
                            ( k ((1₂ , 1₂) , 0₂))
                            ( k ((1₂ , 1₂) , 1₂))
                            ( \ t → k ((1₂ , t) , 0₂))
                            ( \ t → k ((1₂ , 1₂) , t))
                            ( hg))
                  , ( hom3
                        ( A)
                        ( k ((0₂ , 0₂) , 0₂))
                        ( k ((1₂ , 0₂) , 0₂))
                        ( k ((1₂ , 1₂) , 0₂))
                        ( k ((1₂ , 1₂) , 1₂))
                        ( \ t → k ((t , 0₂) , 0₂))
                        ( \ t → k ((t , t) , 0₂))
                        ( \ t → k ((t , t) , t))
                        ( \ t → k ((1₂ , t) , 0₂))
                        ( hg)
                        ( \ t → k ((1₂ , 1₂) , t))
                        ( \ (t , s) → k ((t , s) , 0₂))
                        ( α₂)
                        ( \ (t , s) → k ((t , t) , s))
                        ( α₀))))))
  :=
    ( \ H →
      ( ( ( ( ( \ t → H t)
        , ( ( ( \ t → H ((1₂ , t) , t))
          , ( ( ( \ (t , s) → H ((t , s) , s))
            , ( ( \ (t , s) → H ((1₂ , t) , s)
              , ( H)))))))))))
      , ( ( \ G t → second (second (second (second (G)))) t , \ H → refl)
        , ( ( \ G t → second (second (second (second (G)))) t , \ H → refl))))

#def equiv-2-segal-horn-restriction₍₁₃₎
  ( A : U)
  : Equiv
    ( Δ³ → A)
    ( Σ ( k : Λ³₍₁₃₎ → A)
      , ( Σ ( gf : hom A (k ((0₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 0₂)))
          , ( Σ ( α₃ : hom2
                        ( A)
                        ( k ((0₂ , 0₂) , 0₂))
                        ( k ((1₂ , 0₂) , 0₂))
                        ( k ((1₂ , 1₂) , 0₂))
                        ( \ t → k ((t , 0₂) , 0₂))
                        ( \ t → k ((1₂ , t) , 0₂))
                        ( gf))
              , ( Σ ( α₁ : hom2
                            ( A)
                            ( k ((0₂ , 0₂) , 0₂))
                            ( k ((1₂ , 1₂) , 0₂))
                            ( k ((1₂ , 1₂) , 1₂))
                            ( gf)
                            ( \ t → k ((1₂ , 1₂) , t))
                            ( \ t → k ((t , t) , t)))
                  , ( hom3
                        ( A)
                        ( k ((0₂ , 0₂) , 0₂))
                        ( k ((1₂ , 0₂) , 0₂))
                        ( k ((1₂ , 1₂) , 0₂))
                        ( k ((1₂ , 1₂) , 1₂))
                        ( \ t → k ((t , 0₂) , 0₂))
                        ( gf)
                        ( \ t → k ((t , t) , t))
                        ( \ t → k ((1₂ , t) , 0₂))
                        ( \ t → k ((1₂ , t) , t))
                        ( \ t → k ((1₂ , 1₂) , t))
                        ( α₃)
                        ( \ (t , s) → k ((t , s) , s))
                        ( α₁)
                        ( \ (t , s) → k ((1₂ , t) , s)))))))
  :=
    ( \ H →
      ( ( ( ( ( \ t → H t)
        , ( ( ( \ t → H ((t , t) , 0₂))
          , ( ( ( \ (t , s) → H ((t , s) , 0₂))
            , ( ( \ (t , s) → H ((t , t) , s)
              , ( H)))))))))))
      , ( ( \ G t → second (second (second (second (G)))) t , \ H → refl)
        , ( ( \ G t → second (second (second (second (G)))) t , \ H → refl))))

#def equiv-2-segal-horn-restriction₍₀₂₎-is-2-segal₍₀₂₎
  ( A : U)
  ( is-2-segal₍₀₂₎-A : is-2-segal₍₀₂₎ A)
  : Equiv (Δ³ → A) (Λ³₍₀₂₎ → A)
  :=
    equiv-comp
      ( Δ³ → A)
      ( Σ ( k : Λ³₍₀₂₎ → A)
        , ( Σ ( hg : hom A (k ((1₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 1₂)))
          , ( Σ ( α₂ : hom2
                        ( A)
                        ( k ((0₂ , 0₂) , 0₂))
                        ( k ((1₂ , 0₂) , 0₂))
                        ( k ((1₂ , 1₂) , 1₂))
                        ( \ t → k ((t , 0₂) , 0₂))
                        ( hg)
                        ( \ t → k ((t , t) , t)))
              , ( Σ ( α₀ : hom2
                            ( A)
                            ( k ((1₂ , 0₂) , 0₂))
                            ( k ((1₂ , 1₂) , 0₂))
                            ( k ((1₂ , 1₂) , 1₂))
                            ( \ t → k ((1₂ , t) , 0₂))
                            ( \ t → k ((1₂ , 1₂) , t))
                            ( hg))
                  , ( hom3
                        ( A)
                        ( k ((0₂ , 0₂) , 0₂))
                        ( k ((1₂ , 0₂) , 0₂))
                        ( k ((1₂ , 1₂) , 0₂))
                        ( k ((1₂ , 1₂) , 1₂))
                        ( \ t → k ((t , 0₂) , 0₂))
                        ( \ t → k ((t , t) , 0₂))
                        ( \ t → k ((t , t) , t))
                        ( \ t → k ((1₂ , t) , 0₂))
                        ( hg)
                        ( \ t → k ((1₂ , 1₂) , t))
                        ( \ (t , s) → k ((t , s) , 0₂))
                        ( α₂)
                        ( \ (t , s) → k ((t , t) , s))
                        ( α₀))))))
      ( Λ³₍₀₂₎ → A)
      ( equiv-2-segal-horn-restriction₍₀₂₎ A)
      ( projection-total-type
        ( Λ³₍₀₂₎ → A)
        ( \ k →
          ( Σ ( hg : hom A (k ((1₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 1₂)))
            , ( Σ ( α₂ : hom2
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 1₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( hg)
                          ( \ t → k ((t , t) , t)))
                , ( Σ ( α₀ : hom2
                              ( A)
                              ( k ((1₂ , 0₂) , 0₂))
                              ( k ((1₂ , 1₂) , 0₂))
                              ( k ((1₂ , 1₂) , 1₂))
                              ( \ t → k ((1₂ , t) , 0₂))
                              ( \ t → k ((1₂ , 1₂) , t))
                              ( hg))
                    , ( hom3
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( k ((1₂ , 1₂) , 1₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( \ t → k ((t , t) , 0₂))
                          ( \ t → k ((t , t) , t))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( hg)
                          ( \ t → k ((1₂ , 1₂) , t))
                          ( \ (t , s) → k ((t , s) , 0₂))
                          ( α₂)
                          ( \ (t , s) → k ((t , t) , s))
                          ( α₀))))))
      , ( is-equiv-projection-contractible-fibers
          ( Λ³₍₀₂₎ → A)
          ( \ k →
            ( Σ ( hg : hom A (k ((1₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 1₂)))
              , ( Σ ( α₂ : hom2
                            ( A)
                            ( k ((0₂ , 0₂) , 0₂))
                            ( k ((1₂ , 0₂) , 0₂))
                            ( k ((1₂ , 1₂) , 1₂))
                            ( \ t → k ((t , 0₂) , 0₂))
                            ( hg)
                            ( \ t → k ((t , t) , t)))
                  , ( Σ ( α₀ : hom2
                                ( A)
                                ( k ((1₂ , 0₂) , 0₂))
                                ( k ((1₂ , 1₂) , 0₂))
                                ( k ((1₂ , 1₂) , 1₂))
                                ( \ t → k ((1₂ , t) , 0₂))
                                ( \ t → k ((1₂ , 1₂) , t))
                                ( hg))
                      , ( hom3
                            ( A)
                            ( k ((0₂ , 0₂) , 0₂))
                            ( k ((1₂ , 0₂) , 0₂))
                            ( k ((1₂ , 1₂) , 0₂))
                            ( k ((1₂ , 1₂) , 1₂))
                            ( \ t → k ((t , 0₂) , 0₂))
                            ( \ t → k ((t , t) , 0₂))
                            ( \ t → k ((t , t) , t))
                            ( \ t → k ((1₂ , t) , 0₂))
                            ( hg)
                            ( \ t → k ((1₂ , 1₂) , t))
                            ( \ (t , s) → k ((t , s) , 0₂))
                            ( α₂)
                            ( \ (t , s) → k ((t , t) , s))
                            ( α₀))))))
          ( \ k →
            is-2-segal₍₀₂₎-A
              ( k ((0₂ , 0₂) , 0₂))
              ( k ((1₂ , 0₂) , 0₂))
              ( k ((1₂ , 1₂) , 0₂))
              ( k ((1₂ , 1₂) , 1₂))
              ( \ t → k ((t , 0₂) , 0₂))
              ( \ t → k ((t , t) , 0₂))
              ( \ t → k ((t , t) , t))
              ( \ t → k ((1₂ , t) , 0₂))
              ( \ t → k ((1₂ , 1₂) , t))
              ( \ (t , s) → k ((t , s) , 0₂))
              ( \ (t , s) → k ((t , t) , s)))))

#def is-local-2-segal-horn-inclusion-is-2-segal₍₀₂₎
  ( A : U)
  ( is-2-segal₍₀₂₎-A : is-2-segal₍₀₂₎ A)
  : is-local-type (2 × 2 × 2) Δ³ Λ³₍₀₂₎ A
  :=
    second
      ( equiv-2-segal-horn-restriction₍₀₂₎-is-2-segal₍₀₂₎ A is-2-segal₍₀₂₎-A)

#def equiv-2-segal-horn-restriction₍₁₃₎-is-2-segal₍₁₃₎
  ( A : U)
  ( is-2-segal₍₁₃₎-A : is-2-segal₍₁₃₎ A)
  : Equiv (Δ³ → A) (Λ³₍₁₃₎ → A)
  :=
    equiv-comp
      ( Δ³ → A)
      ( Σ ( k : Λ³₍₁₃₎ → A)
        , ( Σ ( gf : hom A (k ((0₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 0₂)))
            , ( Σ ( α₃ : hom2
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( gf))
                , ( Σ ( α₁ : hom2
                              ( A)
                              ( k ((0₂ , 0₂) , 0₂))
                              ( k ((1₂ , 1₂) , 0₂))
                              ( k ((1₂ , 1₂) , 1₂))
                              ( gf)
                              ( \ t → k ((1₂ , 1₂) , t))
                              ( \ t → k ((t , t) , t)))
                    , ( hom3
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( k ((1₂ , 1₂) , 1₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( gf)
                          ( \ t → k ((t , t) , t))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( \ t → k ((1₂ , t) , t))
                          ( \ t → k ((1₂ , 1₂) , t))
                          ( α₃)
                          ( \ (t , s) → k ((t , s) , s))
                          ( α₁)
                          ( \ (t , s) → k ((1₂ , t) , s)))))))
      ( Λ³₍₁₃₎ → A)
      ( equiv-2-segal-horn-restriction₍₁₃₎ A)
      ( projection-total-type
        ( Λ³₍₁₃₎ → A)
        ( \ k →
          ( Σ ( gf : hom A (k ((0₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 0₂)))
            , ( Σ ( α₃ : hom2
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( gf))
                , ( Σ ( α₁ : hom2
                              ( A)
                              ( k ((0₂ , 0₂) , 0₂))
                              ( k ((1₂ , 1₂) , 0₂))
                              ( k ((1₂ , 1₂) , 1₂))
                              ( gf)
                              ( \ t → k ((1₂ , 1₂) , t))
                              ( \ t → k ((t , t) , t)))
                    , ( hom3
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( k ((1₂ , 1₂) , 1₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( gf)
                          ( \ t → k ((t , t) , t))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( \ t → k ((1₂ , t) , t))
                          ( \ t → k ((1₂ , 1₂) , t))
                          ( α₃)
                          ( \ (t , s) → k ((t , s) , s))
                          ( α₁)
                          ( \ (t , s) → k ((1₂ , t) , s)))))))
      , ( is-equiv-projection-contractible-fibers
          ( Λ³₍₁₃₎ → A)
          ( \ k →
            ( Σ ( gf : hom A (k ((0₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 0₂)))
              , ( Σ ( α₃ : hom2
                            ( A)
                            ( k ((0₂ , 0₂) , 0₂))
                            ( k ((1₂ , 0₂) , 0₂))
                            ( k ((1₂ , 1₂) , 0₂))
                            ( \ t → k ((t , 0₂) , 0₂))
                            ( \ t → k ((1₂ , t) , 0₂))
                            ( gf))
                  , ( Σ ( α₁ : hom2
                                ( A)
                                ( k ((0₂ , 0₂) , 0₂))
                                ( k ((1₂ , 1₂) , 0₂))
                                ( k ((1₂ , 1₂) , 1₂))
                                ( gf)
                                ( \ t → k ((1₂ , 1₂) , t))
                                ( \ t → k ((t , t) , t)))
                      , ( hom3
                            ( A)
                            ( k ((0₂ , 0₂) , 0₂))
                            ( k ((1₂ , 0₂) , 0₂))
                            ( k ((1₂ , 1₂) , 0₂))
                            ( k ((1₂ , 1₂) , 1₂))
                            ( \ t → k ((t , 0₂) , 0₂))
                            ( gf)
                            ( \ t → k ((t , t) , t))
                            ( \ t → k ((1₂ , t) , 0₂))
                            ( \ t → k ((1₂ , t) , t))
                            ( \ t → k ((1₂ , 1₂) , t))
                            ( α₃)
                            ( \ (t , s) → k ((t , s) , s))
                            ( α₁)
                            ( \ (t , s) → k ((1₂ , t) , s)))))))
          ( \ k →
            is-2-segal₍₁₃₎-A
              ( k ((0₂ , 0₂) , 0₂))
              ( k ((1₂ , 0₂) , 0₂))
              ( k ((1₂ , 1₂) , 0₂))
              ( k ((1₂ , 1₂) , 1₂))
              ( \ t → k ((t , 0₂) , 0₂))
              ( \ t → k ((t , t) , t))
              ( \ t → k ((1₂ , t) , 0₂))
              ( \ t → k ((1₂ , t) , t))
              ( \ t → k ((1₂ , 1₂) , t))
              ( \ (t , s) → k ((t , s) , s))
              ( \ (t , s) → k ((1₂ , t) , s)))))

#def is-local-2-segal-horn-inclusion-is-2-segal₍₁₃₎
  ( A : U)
  ( is-2-segal₍₁₃₎-A : is-2-segal₍₁₃₎ A)
  : is-local-type (2 × 2 × 2) Δ³ Λ³₍₁₃₎ A
  :=
    second
      ( equiv-2-segal-horn-restriction₍₁₃₎-is-2-segal₍₁₃₎ A is-2-segal₍₁₃₎-A)

#def is-local-2-segal-horn-inclusion-is-2-segal
  ( A : U)
  ( is-2-segal-A : is-2-segal A)
  : is-local-2-segal-horn-inclusion A
  :=
    ( is-local-2-segal-horn-inclusion-is-2-segal₍₀₂₎ A (first (is-2-segal-A))
    , is-local-2-segal-horn-inclusion-is-2-segal₍₁₃₎ A (second (is-2-segal-A)))
```

The converse direction: A type that is local with respect to the 2-Segal horn
inclusions in 2-Segal.

```rzk
#def is-2-segal-is-local-2-segal-horn-inclusion₍₀₂₎
  ( A : U)
  ( is-local-A : is-local-type (2 × 2 × 2) Δ³ Λ³₍₀₂₎ A)
  : is-2-segal₍₀₂₎ A
  :=
    \ w x y z f gf hgf g h α₃ α₁ →
      contractible-fibers-is-equiv-projection
        ( Λ³₍₀₂₎ → A)
        ( \ k →
          ( Σ ( hg : hom A (k ((1₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 1₂)))
            , ( Σ ( α₂ : hom2
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 1₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( hg)
                          ( \ t → k ((t , t) , t)))
                , ( Σ ( α₀ : hom2
                              ( A)
                              ( k ((1₂ , 0₂) , 0₂))
                              ( k ((1₂ , 1₂) , 0₂))
                              ( k ((1₂ , 1₂) , 1₂))
                              ( \ t → k ((1₂ , t) , 0₂))
                              ( \ t → k ((1₂ , 1₂) , t))
                              ( hg))
                    , ( hom3
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( k ((1₂ , 1₂) , 1₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( \ t → k ((t , t) , 0₂))
                          ( \ t → k ((t , t) , t))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( hg)
                          ( \ t → k ((1₂ , 1₂) , t))
                          ( \ (t , s) → k ((t , s) , 0₂))
                          ( α₂)
                          ( \ (t , s) → k ((t , t) , s))
                          ( α₀))))))
        ( second
          ( equiv-comp
            ( Σ ( k : Λ³₍₀₂₎ → A)
              , ( Σ ( hg : hom A (k ((1₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 1₂)))
                  , ( Σ ( α₂ : hom2
                                ( A)
                                ( k ((0₂ , 0₂) , 0₂))
                                ( k ((1₂ , 0₂) , 0₂))
                                ( k ((1₂ , 1₂) , 1₂))
                                ( \ t → k ((t , 0₂) , 0₂))
                                ( hg)
                                ( \ t → k ((t , t) , t)))
                      , ( Σ ( α₀ : hom2
                                    ( A)
                                    ( k ((1₂ , 0₂) , 0₂))
                                    ( k ((1₂ , 1₂) , 0₂))
                                    ( k ((1₂ , 1₂) , 1₂))
                                    ( \ t → k ((1₂ , t) , 0₂))
                                    ( \ t → k ((1₂ , 1₂) , t))
                                    ( hg))
                          , ( hom3
                                ( A)
                                ( k ((0₂ , 0₂) , 0₂))
                                ( k ((1₂ , 0₂) , 0₂))
                                ( k ((1₂ , 1₂) , 0₂))
                                ( k ((1₂ , 1₂) , 1₂))
                                ( \ t → k ((t , 0₂) , 0₂))
                                ( \ t → k ((t , t) , 0₂))
                                ( \ t → k ((t , t) , t))
                                ( \ t → k ((1₂ , t) , 0₂))
                                ( hg)
                                ( \ t → k ((1₂ , 1₂) , t))
                                ( \ (t , s) → k ((t , s) , 0₂))
                                ( α₂)
                                ( \ (t , s) → k ((t , t) , s))
                                ( α₀))))))
            ( Δ³ → A)
            ( Λ³₍₀₂₎ → A)
            ( inv-equiv
              ( Δ³ → A)
              ( Σ ( k : Λ³₍₀₂₎ → A)
                , ( Σ ( hg : hom A (k ((1₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 1₂)))
                    , ( Σ ( α₂ : hom2
                                  ( A)
                                  ( k ((0₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 1₂) , 1₂))
                                  ( \ t → k ((t , 0₂) , 0₂))
                                  ( hg)
                                  ( \ t → k ((t , t) , t)))
                        , ( Σ ( α₀ : hom2
                                      ( A)
                                      ( k ((1₂ , 0₂) , 0₂))
                                      ( k ((1₂ , 1₂) , 0₂))
                                      ( k ((1₂ , 1₂) , 1₂))
                                      ( \ t → k ((1₂ , t) , 0₂))
                                      ( \ t → k ((1₂ , 1₂) , t))
                                      ( hg))
                            , ( hom3
                                  ( A)
                                  ( k ((0₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 1₂) , 0₂))
                                  ( k ((1₂ , 1₂) , 1₂))
                                  ( \ t → k ((t , 0₂) , 0₂))
                                  ( \ t → k ((t , t) , 0₂))
                                  ( \ t → k ((t , t) , t))
                                  ( \ t → k ((1₂ , t) , 0₂))
                                  ( hg)
                                  ( \ t → k ((1₂ , 1₂) , t))
                                  ( \ (t , s) → k ((t , s) , 0₂))
                                  ( α₂)
                                  ( \ (t , s) → k ((t , t) , s))
                                  ( α₀))))))
              ( equiv-2-segal-horn-restriction₍₀₂₎ A))
            ( \ f t → f t , is-local-A)))
        ( 3horn₍₀₂₎ A w x y z f gf hgf g h α₃ α₁)

#def is-2-segal-is-local-2-segal-horn-inclusion₍₁₃₎
  ( A : U)
  ( is-local-A : is-local-type (2 × 2 × 2) Δ³ Λ³₍₁₃₎ A)
  : is-2-segal₍₁₃₎ A
  :=
    \ w x y z f hgf g hg h α₂ α₀ →
      contractible-fibers-is-equiv-projection
        ( Λ³₍₁₃₎ → A)
        ( \ k →
          ( Σ ( gf : hom A (k ((0₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 0₂)))
            , ( Σ ( α₃ : hom2
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( gf))
                , ( Σ ( α₁ : hom2
                              ( A)
                              ( k ((0₂ , 0₂) , 0₂))
                              ( k ((1₂ , 1₂) , 0₂))
                              ( k ((1₂ , 1₂) , 1₂))
                              ( gf)
                              ( \ t → k ((1₂ , 1₂) , t))
                              ( \ t → k ((t , t) , t)))
                    , ( hom3
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( k ((1₂ , 1₂) , 1₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( gf)
                          ( \ t → k ((t , t) , t))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( \ t → k ((1₂ , t) , t))
                          ( \ t → k ((1₂ , 1₂) , t))
                          ( α₃)
                          ( \ (t , s) → k ((t , s) , s))
                          ( α₁)
                          ( \ (t , s) → k ((1₂ , t) , s)))))))
        ( second
          ( equiv-comp
            ( Σ ( k : Λ³₍₁₃₎ → A)
              , ( Σ ( gf : hom A (k ((0₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 0₂)))
                  , ( Σ ( α₃ : hom2
                                ( A)
                                ( k ((0₂ , 0₂) , 0₂))
                                ( k ((1₂ , 0₂) , 0₂))
                                ( k ((1₂ , 1₂) , 0₂))
                                ( \ t → k ((t , 0₂) , 0₂))
                                ( \ t → k ((1₂ , t) , 0₂))
                                ( gf))
                      , ( Σ ( α₁ : hom2
                                    ( A)
                                    ( k ((0₂ , 0₂) , 0₂))
                                    ( k ((1₂ , 1₂) , 0₂))
                                    ( k ((1₂ , 1₂) , 1₂))
                                    ( gf)
                                    ( \ t → k ((1₂ , 1₂) , t))
                                    ( \ t → k ((t , t) , t)))
                          , ( hom3
                                ( A)
                                ( k ((0₂ , 0₂) , 0₂))
                                ( k ((1₂ , 0₂) , 0₂))
                                ( k ((1₂ , 1₂) , 0₂))
                                ( k ((1₂ , 1₂) , 1₂))
                                ( \ t → k ((t , 0₂) , 0₂))
                                ( gf)
                                ( \ t → k ((t , t) , t))
                                ( \ t → k ((1₂ , t) , 0₂))
                                ( \ t → k ((1₂ , t) , t))
                                ( \ t → k ((1₂ , 1₂) , t))
                                ( α₃)
                                ( \ (t , s) → k ((t , s) , s))
                                ( α₁)
                                ( \ (t , s) → k ((1₂ , t) , s)))))))
            ( Δ³ → A)
            ( Λ³₍₁₃₎ → A)
            ( inv-equiv
              ( Δ³ → A)
              ( Σ ( k : Λ³₍₁₃₎ → A)
                , ( Σ ( gf : hom A (k ((0₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 0₂)))
                    , ( Σ ( α₃ : hom2
                                  ( A)
                                  ( k ((0₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 1₂) , 0₂))
                                  ( \ t → k ((t , 0₂) , 0₂))
                                  ( \ t → k ((1₂ , t) , 0₂))
                                  ( gf))
                        , ( Σ ( α₁ : hom2
                                      ( A)
                                      ( k ((0₂ , 0₂) , 0₂))
                                      ( k ((1₂ , 1₂) , 0₂))
                                      ( k ((1₂ , 1₂) , 1₂))
                                      ( gf)
                                      ( \ t → k ((1₂ , 1₂) , t))
                                      ( \ t → k ((t , t) , t)))
                            , ( hom3
                                  ( A)
                                  ( k ((0₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 1₂) , 0₂))
                                  ( k ((1₂ , 1₂) , 1₂))
                                  ( \ t → k ((t , 0₂) , 0₂))
                                  ( gf)
                                  ( \ t → k ((t , t) , t))
                                  ( \ t → k ((1₂ , t) , 0₂))
                                  ( \ t → k ((1₂ , t) , t))
                                  ( \ t → k ((1₂ , 1₂) , t))
                                  ( α₃)
                                  ( \ (t , s) → k ((t , s) , s))
                                  ( α₁)
                                  ( \ (t , s) → k ((1₂ , t) , s)))))))
              ( equiv-2-segal-horn-restriction₍₁₃₎ A))
            ( \ f t → f t , is-local-A)))
        ( 3horn₍₁₃₎ A w x y z f hgf g hg h α₂ α₀)

#def is-2-segal-is-local-2-segal-horn-inclusion
  ( A : U)
  ( is-local-A : is-local-2-segal-horn-inclusion A)
  : is-2-segal A
  :=
    ( is-2-segal-is-local-2-segal-horn-inclusion₍₀₂₎ A (first (is-local-A))
    , is-2-segal-is-local-2-segal-horn-inclusion₍₁₃₎ A (second (is-local-A)))

#def is-2-segal-iff-is-local-2-segal-horn-inclusion
  ( A : U)
  : iff (is-2-segal A) (is-local-2-segal-horn-inclusion A)
  :=
    ( is-local-2-segal-horn-inclusion-is-2-segal A
    , is-2-segal-is-local-2-segal-horn-inclusion A)
```

The proof of `is-local-horn-inclusion-function-type` generalizes to types being
local with respect to an arbitrary subshape inclusion.

```rzk
#def subshape-restriction
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : U)
  : ( ψ → A) → (ϕ → A)
  := \ f t → f t

#def is-local-function-type-fiberwise-is-local
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : U)
  ( C : A → U)
  ( fiberwise-is-local-C : (x : A) → is-local-type I ψ ϕ (C x))
  : is-local-type I ψ ϕ ((x : A) → C x)
  :=
    is-equiv-triple-comp
      ( ψ → ((x : A) → C x))
      ( ( x : A) → ψ → C x)
      ( ( x : A) → ϕ → C x)
      ( ϕ → ((x : A) → C x))
      ( \ g x t → g t x) -- first equivalence
      ( second (flip-ext-fun
        ( I)
        ( ψ)
        ( \ t → BOT)
        ( A)
        ( \ t → C)
        ( \ t → recBOT)))
      ( \ h x t → h x t) -- second equivalence
      ( second (equiv-function-equiv-family
        ( funext)
        ( A)
        ( \ x → (ψ → C x))
        ( \ x → (ϕ → C x))
        ( \ x → (subshape-restriction I ψ ϕ (C x) , fiberwise-is-local-C x))))
      ( \ h t x → (h x) t) -- third equivalence
      ( second (flip-ext-fun-inv
        ( I)
        ( \ t → ϕ t)
        ( \ t → BOT)
        ( A)
        ( \ t → C)
        ( \ t → recBOT)))
```

Using this general form, we prove that (dependent) function types into a family
of 2-Segal types are 2-Segal.

```rzk
#def is-local-2-segal-horn-inclusion-function-type uses (funext)
  ( A : U)
  ( C : A → U)
  ( fiberwise-is-2-segal-A : (x : A) → is-local-2-segal-horn-inclusion (C x))
  : is-local-2-segal-horn-inclusion ((x : A) → C x)
  :=
    ( is-local-function-type-fiberwise-is-local
        ( 2 × 2 × 2)
        ( Δ³)
        ( Λ³₍₀₂₎)
        ( A)
        ( C)
        ( \ x → first (fiberwise-is-2-segal-A x))
    , is-local-function-type-fiberwise-is-local
        ( 2 × 2 × 2)
        ( Δ³)
        ( Λ³₍₁₃₎)
        ( A)
        ( C)
        ( \ x → second (fiberwise-is-2-segal-A x)))
```

We do the same for the proof of `is-local-horn-inclusion-extension-type`

```rzk
#def is-local-subshape-inclusion-extension-type uses (extext)
  ( I J : CUBE)
  ( χ : I → TOPE)
  ( ψ : J → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : χ → U)
  ( fiberwise-is-local-A : (s : χ) → is-local-type J ψ ϕ (A s))
  : is-local-type J ψ ϕ ((s : χ) → A s)
  :=
    is-equiv-triple-comp
      ( ψ → (s : χ) → A s)
      ( ( s : χ) → ψ → A s)
      ( ( s : χ) → ϕ → A s)
      ( ϕ → (s : χ) → A s)
      ( \ g s t → g t s)  -- first equivalence
      ( second
        ( fubini
          ( J)
          ( I)
          ( \ t → ψ t)
          ( \ t → BOT)
          ( χ)
          ( \ s → BOT)
          ( \ t s → A s)
          ( \ u → recBOT)))
      ( \ h s t → h s t) -- second equivalence
      ( second (equiv-extensions-equiv extext I χ (\ _ → BOT)
        ( \ s → ψ → A s)
        ( \ s → ϕ → A s)
        ( \ s → (subshape-restriction J ψ ϕ (A s) , fiberwise-is-local-A s))
        ( \ _ → recBOT)))
      ( \ h t s → (h s) t) -- third equivalence
      ( second
        ( fubini
          ( I)
          ( J)
          ( χ)
          ( \ s → BOT)
          ( \ t → ϕ t)
          ( \ t → BOT)
          ( \ s t → A s)
          ( \ u → recBOT)))

#def is-2-segal-extension-type uses (extext)
  ( I : CUBE)
  ( χ : I → TOPE)
  ( A : χ → U)
  ( fiberwise-is-2-segal-A : (s : χ) → is-local-2-segal-horn-inclusion (A s))
  : is-local-2-segal-horn-inclusion ((s : χ) → A s)
  :=
    ( is-local-subshape-inclusion-extension-type I
        ( 2 × 2 × 2)
        ( χ)
        ( Δ³)
        ( Λ³₍₀₂₎)
        ( A)
        ( \ x → first (fiberwise-is-2-segal-A x))
    , is-local-subshape-inclusion-extension-type I
        ( 2 × 2 × 2)
        ( χ)
        ( Δ³)
        ( Λ³₍₁₃₎)
        ( A)
        ( \ x → second (fiberwise-is-2-segal-A x)))
```
