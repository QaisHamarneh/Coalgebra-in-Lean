import category_theory.category
import category_theory.functor
import category_theory.concrete_category
import category_theory.types


/-
universes u v

variable Automat₁ {S α : Type u} 
    (δ : S → α → S) 
    (terminal : S → bool) : Type v

variables S α β : Type u
variable δ : S → α → S
variable terminal : S → bool

variable σ : Automat₁ δ terminal → Automat₁ δ terminal

def id_Automat (X : Automat₁ δ terminal) := X
-/



---------------------------
section Automat
    parameter α : Type          -- Alphabet

    structure Automat := mk:: {S: Type*} 
                (δ : S → α × S)        
                     -- Here δ returns a pair from (α × S)
                (terminal : S → bool)

    structure functor_A (A B :Automat) := 
        mk::
            (states : A.S → B.S)
            (delta : α × A.S → α × B.S)     -- maps a pair to a pair

    def homomorphismus
            (A B : Automat) 
            (σ : functor_A A B) : Prop := 
            ∀ a : A.S , 
                (A.terminal a = B.terminal (σ.states a) ∧
                    σ.delta (A.δ a) = B.δ (σ.states a))
                        -- comparing a pair with a pair (B.S , α)

end Automat

section Automat_1
    parameter α : Type

    structure Automat_1 := mk:: {S: Type*} 
                (δ : S → α → S) 
                    -- Here delta returns a function (α → S)
                (terminal : S → bool)

    #check Automat

    variable f : Automat_1 → Automat_1 

    structure map_1 (A B :Automat_1) := 
        mk::
            (states : A.S → B.S)
                -- Here there is no use of the morphism part

    def homomorphismus_1
            (A B : Automat_1) 
            (σ : map_1 A B) : Prop := 
            ∀ a : A.S , 
                (A.terminal a = B.terminal (σ.states a) ∧
                ∀ e : α , 
                    σ.states (A.δ a e) = B.δ (σ.states a) e)
                        -- comparing a state to a state from B.S

end Automat_1

section Automat_2
    parameter α : Type

    structure Automat_2 := mk:: {S : Type*} 
            (F : S → (α → S) × bool)

    #check Automat

    variable f : Automat_2 → Automat_2 

    structure map_2 (A B :Automat_2) := 
        mk::
            (states : A.S → B.S)


    def homomorphismus_2
            (A B : Automat_2) 
            (σ : map_2 A B) : Prop := 
            ∀ a : A.S , 
                ((A.F a).2 = (B.F (σ.states a)).2 ∧
                ∀ e : α , 
                    σ.states ((A.F a).1 e) = (B.F (σ.states a)).1 e)

end Automat_2

section Automat_3       -- Coalgebric Automat
    parameter Alphabet : Type                          -- Alphabet
    def F := λ S: Type , (Alphabet → S) × bool         -- Signature

    structure Automat_3 := 
                mk:: (S : Type) (γ : S → F S)

    /-structure map_3 (A B :Automat_3) := 
        mk::
            (states : A.S → B.S)-/

    def homomorphismus_3
            (A B : Automat_3) (σ : A.S → B.S) : Prop := 
            ∀ a : A.S , 
                ((A.γ a).2 = (B.γ (σ a)).2 ∧
                ∀ e : Alphabet , 
                    σ ((A.γ a).1 e) = (B.γ (σ a)).1 e)

end Automat_3


open category_theory

section Coalgebra 

    universes u v w

    class someStructure (α : Type u) : Type u
    
    @[reducible] def Carrier : Type (u+1) := bundled someStructure


    def is_XX_hom {α β}
        [someStructure α] 
        [someStructure β] (f : α → β) : Prop := true

    instance concrete_is_XX_hom : 
        concrete_category @is_XX_hom := sorry

    
    variable F1 : Carrier  ⥤ Type w 

    structure coalgebra := 
            (A : Carrier) (α : A → F1.obj A)



    #check coalgebra

end Coalgebra

universe u

instance Set : large_category (Type u) :=
{ hom     := λ a b, (a → b),
  id      := λ a, id,
  comp    := λ _ _ _ f g, g ∘ f }


variables (p : Prop) (h : p)

#check classical.em 


variables (X B C : Type)

variable (S : set X)

open set

def fun_to_image (f : X → B) : X → range f := 
    λ a , 
    have h : f a ∈ range f := 
        exists.intro a 
            (eq.refl (f a)),
    ⟨f a, h⟩

#check range_factorization 

#check Sort 1



variables {AA BB : Type u} (ff gg: AA → BB)
#check setoid
#check eqv_gen

def R (f g: AA → BB) 
    : BB → BB → Prop := λ b₁ b₂ , ∃ a , f a = b₁ ∧ g a = b₂ 


def Θ := @eqv_gen BB (R ff gg)
def s := eqv_gen.setoid (R ff gg)

--def proj : B → quotient (s f g) := λ b , ⟦b⟧

#check quotient (eqv_gen.setoid (R ff gg)) 

    --setoid BB := eqv_gen.setoid (R ff gg)

def set_BB : setoid BB := eqv_gen.setoid (R ff gg)

--instance quot.mk (R ff gg)

variables (b : BB) 

#check quotient (set_BB ff gg)

def bla (s : setoid BB) (b : BB) : @quot BB setoid.r :=
    quot.mk setoid.r b

variable [s : setoid BB]

#check ⟦b⟧

#check bla (eqv_gen.setoid (R ff gg)) b



example (A : Type) (S T : set A) 
    (h: ∀a : A ,a ∈ S ↔ a ∈ T)
    : S = T  := 
    begin
        have h1 : ∀s : S , s.val ∈ T :=
           λ s, (h s.val).1 s.property,
        have h2 : ∀t : T , t.val ∈ S :=
           λ t, (h t.val).2 t.property,
        simp at *, 
        ext1, 
        fsplit, 
        intros s, 
        exact h1 x s, 
        intros t, 
        exact h2 x t
    end


