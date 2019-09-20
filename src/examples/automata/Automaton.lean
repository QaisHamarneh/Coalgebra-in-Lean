import data.set
open set

namespace Automaton


universes u₃ u₂ u₁ 

inductive word (Sigma : Type u₂)
        | ε  {}         : word
        | nonempty      : Sigma → word → word 


notation e ` • ` v := word.nonempty e v

variables {Sigma : Type u₂}  {Γ : Type u₃} 


open word

structure Automaton  (Sigma : Type u₂)  (Γ : Type u₃): 
    Type (max (u₁+1) u₂ u₃) :=         
        (State : Type u₁)                   -- Set of States
        (δ : State → Sigma → State)         -- δ: S × Σ → S
        (s₀ : State)                        -- S₀ the starting state
        (γ : State → Γ)               -- T ⊆ S
        


instance Automaton_to_Type : has_coe_to_sort (Automaton Sigma Γ) :=
⟨ Type u₁ , λ A , A.State⟩ 
/--
Given a morphism τ between two Automates A and B
determines if τ is a homomorphism
-/
def is_homomorphism  {A B : Automaton Sigma Γ}              
    (τ : A → B) : Prop :=   
        ∀ a : A.State ,                                 -- ∀ states (a) in A
            A.γ a = B.γ (τ a) ∧     -- a ∈ T_A iff τ(a) ∈ T_B
                ∀ e : Sigma ,                       -- and ∀ e ∈ Σ
                    τ (A.δ a e) = B.δ (τ a) e     -- τ(δ_A(a , e)) = δ_B(τ(a) , e)


def δ_Star {A : Automaton Sigma Γ} (s : A): 
    word Sigma     →  A 
    | ε           :=  s 
    | (e•v)       :=  A.δ (δ_Star v) e


def accepted (A : Automaton Sigma Prop) (w : word Sigma) : Prop :=
    A.γ (δ_Star A.s₀ w)

end Automaton
