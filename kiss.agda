module kiss where

open import string
open import list
open import bool
open import relations
open import product
open import unit

data formula : Set where
  $ : string → formula
  True : formula
  Implies : formula → formula → formula
  And : formula → formula → formula

ctxt : Set
ctxt = 𝕃 formula

data _⊢_ : ctxt → formula → Set where
  Assume : ∀{Γ f} → (f :: Γ) ⊢ f
  Weaken : ∀{Γ f f'} → Γ ⊢ f → (f' :: Γ) ⊢ f
  ImpliesI : ∀{Γ f1 f2} → (f1 :: Γ) ⊢ f2 → Γ ⊢ (Implies f1 f2)
  ImpliesE : ∀{Γ f1 f2} → Γ ⊢ (Implies f1 f2) → Γ ⊢ f1 → Γ ⊢ f2
  TrueI : ∀{Γ} → Γ ⊢ True
  AndI : ∀{Γ f1 f2} → Γ ⊢ f1 → Γ ⊢ f2 → Γ ⊢ (And f1 f2)
  AndE : ∀(b : 𝔹){Γ f1 f2} → Γ ⊢ (And f1 f2) → Γ ⊢ (if b then f1 else f2)
{-
p : formula
p = $ "p"

f1 : (p :: []) ⊢ p
f1 = assume {[]}{p}

f2 : (p :: []) ⊢ (And p p)
f2 = AndI f1 f1

f3 : [] ⊢ (Implies p (And p p))
f3 = ImpliesI f2
-}
record struct : Set1 where
  field W         : Set
        R         : W → W → Set
        preorderR : preorder R
        V         : W → string → Set
        monoV     : ∀{w w'} → R w w' → ∀{i} →
                    V w i → V w' i
  reflR : reflexive R
  reflR = fst preorderR
  transR : transitive R
  transR = snd preorderR

data world : Set where
  w0 : world
  w1 : world
  w2 : world

data rel : world → world → Set where
  r00 : rel w0 w0
  r11 : rel w1 w1
  r22 : rel w2 w2
  r01 : rel w0 w1
  r02 : rel w0 w2

rel-refl : reflexive rel
rel-refl {w0} = r00
rel-refl {w1} = r11
rel-refl {w2} = r22

rel-trans : transitive rel
rel-trans r00 r00 = r00
rel-trans r00 r01 = r01
rel-trans r00 r02 = r02
rel-trans r11 r11 = r11
rel-trans r22 r22 = r22
rel-trans r01 r11 = r01
rel-trans r02 r22 = r02

data val : world → string → Set where
  v1p : val w1 "p"
  v1q : val w1 "q"
  v2p : val w2 "p"
  v2q : val w2 "q"

mono-val : ∀{w w'} → rel w w' →
           ∀{i} → val w i → val w' i
mono-val r00 p = p
mono-val r11 p = p
mono-val r22 p = p
mono-val r01 ()
mono-val r02 ()

k : struct
k = record { W         = world ;
             R         = rel ;
             preorderR = (rel-refl , rel-trans) ;
             V         = val ;
             monoV     = mono-val }

open struct

_,_⊨_ : ∀(k : struct) → W k → formula → Set
k , w ⊨ ($ x) = V k w x
k , w ⊨ True = ⊤
k , w ⊨ Implies f1 f2 = ∀ {w' : W k} → R k w w' →
                        k , w' ⊨ f1 → k , w' ⊨ f2
k , w ⊨ And f1 f2 = k , w ⊨ f1 ∧ k , w ⊨ f2

pf-test-sem : k , w0 ⊨ Implies ($ "p") ($ "q")
pf-test-sem r00 ()
pf-test-sem r01 p = v1q
pf-test-sem r02 p = v2q

_,_⊨ctxt_ : ∀(k : struct) → W k → ctxt → Set
k , w ⊨ctxt [] = ⊤
k , w ⊨ctxt (f :: Γ) = (k , w ⊨ f) ∧ (k , w ⊨ctxt Γ)

mono⊨ : ∀{k : struct}{w1 w2 : W k}{f : formula} → 
         R k w1 w2 → 
         k , w1 ⊨ f → 
         k , w2 ⊨ f
mono⊨{k} {f = $ x} r p = monoV k r p 
mono⊨{k} {f = True} r p = triv
mono⊨{k} {f = Implies f1 f2} r p r' p' = p (transR k r r') p'
mono⊨{k} {f = And f1 f2} r (p1 , p2) = mono⊨{f = f1} r p1 , mono⊨{f = f2} r p2

mono⊨ctxt : ∀{k : struct}{Γ : ctxt}{w1 w2 : W k} → 
            R k w1 w2 → 
            k , w1 ⊨ctxt Γ → 
            k , w2 ⊨ctxt Γ
mono⊨ctxt{k}{[]} _ _ = triv
mono⊨ctxt{k}{f :: Γ} r (u , v) = mono⊨{k}{f = f} r u , mono⊨ctxt{k}{Γ} r v

_⊩_ : ctxt → formula → Set1
Γ ⊩ f = ∀{k : struct}{w : W k} → k , w ⊨ctxt Γ → k , w ⊨ f

Soundness : ∀{Γ : ctxt}{f : formula} → Γ ⊢ f → Γ ⊩ f
Soundness Assume g = fst g
Soundness (Weaken p) g = Soundness p (snd g)
Soundness (ImpliesI p) g r u' = Soundness p (u' , mono⊨ctxt r g)
Soundness (ImpliesE p p') {k} g = (Soundness p g) (reflR k) (Soundness p' g)
Soundness TrueI g = triv
Soundness (AndI p p') g = (Soundness p g , Soundness p' g)
Soundness (AndE tt p) g = fst (Soundness p g)
Soundness (AndE ff p) g = snd (Soundness p g)

data _≼_ : 𝕃 formula → 𝕃 formula → Set where
  ≼-refl : ∀{Γ} → Γ ≼ Γ
  ≼-cons : ∀{Γ Γ' f} → Γ ≼ Γ' → Γ ≼ (f :: Γ')

≼-trans : ∀ {Γ Γ' Γ''} → Γ ≼ Γ' → Γ' ≼ Γ'' → Γ ≼ Γ''
≼-trans u ≼-refl = u
≼-trans u (≼-cons u') = ≼-cons (≼-trans u u') 

Weaken≼ : ∀ {Γ Γ'}{f : formula} → Γ ≼ Γ' → Γ ⊢ f → Γ' ⊢ f
Weaken≼ ≼-refl p = p
Weaken≼ (≼-cons d) p = Weaken (Weaken≼ d p)

U : struct
U = record { W = ctxt ;
             R = _≼_ ;
             preorderR = ≼-refl , ≼-trans ;
             V = λ Γ n → Γ ⊢ $ n ;
             monoV = λ d p → Weaken≼ d p }

CompletenessU : ∀{f : formula}{Γ : W U} → U , Γ ⊨ f → Γ ⊢ f 
SoundnessU : ∀{f : formula}{Γ : W U} → Γ ⊢ f → U , Γ ⊨ f
CompletenessU {$ x} u = u
CompletenessU {True} u = TrueI
CompletenessU {And f f'} u = AndI (CompletenessU{f} (fst u)) (CompletenessU{f'} (snd u))
CompletenessU {Implies f f'}{Γ} u = 
  ImpliesI 
    (CompletenessU {f'} 
      (u (≼-cons ≼-refl) (SoundnessU {f} (Assume {Γ}))))
SoundnessU {$ x} p = p
SoundnessU {True} p = triv
SoundnessU {And f f'} p = SoundnessU{f} (AndE tt p) , SoundnessU{f'} (AndE ff p)
SoundnessU {Implies f f'} p r u = SoundnessU (ImpliesE (Weaken≼ r p) (CompletenessU {f} u))

ctxt-id : ∀{Γ : ctxt} → U , Γ ⊨ctxt Γ
ctxt-id{[]} = triv
ctxt-id{f :: Γ} = SoundnessU{f} Assume , mono⊨ctxt (≼-cons ≼-refl) (ctxt-id {Γ}) 

Completeness : ∀{Γ : ctxt}{f : formula} → Γ ⊩ f → Γ ⊢ f 
Completeness{Γ} p = CompletenessU (p{U}{Γ} (ctxt-id{Γ}))

Universality1 : ∀{Γ : ctxt}{f : formula} → Γ ⊩ f → U , Γ ⊨ f
Universality1{Γ}{f} p = SoundnessU (Completeness{Γ}{f} p)

Universality2 : ∀{Γ : ctxt}{f : formula} → U , Γ ⊨ f → Γ ⊩ f
Universality2{Γ}{f} p = Soundness (CompletenessU{f}{Γ} p)

nbe : ∀ {Γ f} → Γ ⊢ f → Γ ⊢ f
nbe {Γ} p = Completeness (Soundness p)
