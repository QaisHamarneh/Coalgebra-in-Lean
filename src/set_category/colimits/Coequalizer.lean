import tactic.tidy

import set_category.diagram_lemmas
import help_functions
import category_theory.category




namespace Coequalizer

open set 
     diagram_lemmas
     classical
     function
     help_functions
     category_theory

universe u



local notation f ` ⊚ `:80 g:80 := category_struct.comp g f

def is_coequalizer {X : Type u} [category X]
    {A B C : X}
    (f g : A ⟶ B)
    (c : B ⟶ C) : Prop :=
    c ⊚ f = c ⊚ g ∧ 
    Π (Q : X) (q : B ⟶ Q),
    q ⊚ f = q ⊚ g → 
    ∃! h : C ⟶ Q , h ⊚ c = q

-- def is_coequalizer (c : B → C) : Prop :=
--     c ∘ f = c ∘ g ∧ 
--     Π (Q : Type u) (q : B → Q),
--     q ∘ f = q ∘ g → 
--     ∃! h : C → Q , h ∘ c = q


variables {A B C : Type u}
variables (f g : A ⟶ B)

def R : B → B → Prop := 
    λ b₁ b₂ , ∃ a , f a = b₁ ∧ g a = b₂ 

def Θ : B → B → Prop := eqv_gen (R f g)

def Θ_setoid : setoid B := eqv_gen.setoid (R f g)

definition theta := quotient (Θ_setoid f g)

local notation `⟦`:max a `⟧`:0 := @quotient.mk B (Θ_setoid f g) a

definition coequalizer : B → (theta f g) := λ b, ⟦b⟧
--quot.mk (Θ f g)



open eqv_gen

lemma quot_is_surjective : surjective (coequalizer f g) :=
    by tidy



lemma coequalizer_kern : 
    Π (Q : Type u) (q : B → Q),
    q ∘ f = q ∘ g → sub_kern (coequalizer f g) q :=
    begin 
        intros Q q qfg,
        let co := (coequalizer f g),
        let ker := kern co,
        let ker_q := kern q,
        
        intros b₁ b₂ kb1b2,
        have quotb1b2 : ⟦b₁⟧ = ⟦b₂⟧  := kb1b2,
        let Θb1b2 : eqv_gen (R f g) b₁ b₂ := 
            @quotient.exact B (Θ_setoid f g)
            b₁ b₂ 
            quotb1b2,
        apply eqv_gen.rec_on Θb1b2,
        -- rel i.e. ∀ (x y : B), R f g x y → ker_q x y
        exact (λ b₁ b₂ (h: ∃ a : A , f a = b₁ ∧ g a = b₂), 
            let a : A := some h in
            have fga : f a = b₁ ∧ g a = b₂ := some_spec h,
            have qfga : (q ∘ f) a = (q ∘ g) a := by simp[qfg],
            have qb1 : q b₁ = (q ∘ f) a :=by simp [fga],
            have qb2 : q b₂ = (q ∘ g) a :=by simp [fga],
            have qb1b2 :q b₁ = q b₂ := by simp [qb1 , qb2 , qfga], 
            qb1b2),
        -- refl : ∀ (x : B), ker_q x x
        exact (λ x, rfl),
        -- symm : ∀ (x y : B), eqv_gen (R f g) x y → ker_q x y → ker_q y x
        exact (λ x y _ (h : q x = q y), eq.symm h),
        -- trans :∀ (x y z : B), 
        --    eqv_gen (R f g) x y → eqv_gen (R f g) y z → 
        --         ker_q x y → ker_q y z → ker_q x z
        exact (λ x y z _ _ (h₁ : q x = q y) (h₂ : q y = q z), eq.trans h₁ h₂),
    
    end


lemma quot_is_coequalizer 
    : is_coequalizer f g (coequalizer f g) :=
    ⟨   
        have element : ∀ a : A,
        ((coequalizer f g) ∘ f) a = ((coequalizer f g) ∘ g) a
        := assume a,
            have Rfg : R f g (f a) (g a) := exists.intro a ⟨rfl , rfl⟩,
            have Θfg : Θ f g (f a) (g a) := eqv_gen.rel (f a) (g a) Rfg,
            quot.sound Θfg,
        funext element
        , 
        begin 
            intros Q q qfg,
            
            let co := (coequalizer f g),

            have sub_ker : sub_kern co q := coequalizer_kern f g Q q qfg,
            
            exact 
                (diagram_surjective 
                    co
                    q
                    (quot_is_surjective f g)).elim_right
                sub_ker
        end
    ⟩ 


end Coequalizer