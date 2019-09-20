import category_theory.category
import category_theory.functor
import category_theory.types
import help_functions

import tactic.tidy

universes v u

namespace Sum
open category_theory 
     set 
     classical
     function
     help_functions
     sum




local notation f ` ⊚ `:80 g:80 := category_struct.comp g f
/- Sum -/
/--
predicate to determine if S along with e₁ and e₂ is a Sum in category theory definition
-/
def is_sum  {X : Type v} [category X]
            {A B : X}
            (S: X) 
            (e₁ : A ⟶ S) 
            (e₂ : B ⟶ S) :Prop
            := Π (Q : X) 
                (q₁ : A ⟶ Q)
                (q₂ : B ⟶ Q),
                ∃! s : S ⟶ Q, 
                q₁ = s ⊚ e₁ ∧ q₂ = s ⊚ e₂ 

lemma jointly_epi_cat {X : Type v} [category X]
    {A B S Q : X} (e₁ : A ⟶ S) (e₂ : B ⟶ S)
    (is_sm : is_sum S e₁ e₂)
        (f g: S ⟶ Q) 
        (h1 : f ⊚ e₁ = g ⊚ e₁)
        (h2 : f ⊚ e₂ = g ⊚ e₂)
    : f = g := 
    begin
        have ex : _ := is_sm Q (f ⊚ e₁) (f ⊚ e₂),
        cases ex with s spec_s,
        have g_s : g = s := spec_s.2 g ⟨h1, h2⟩,
        rw g_s,
        exact spec_s.2 f ⟨rfl, rfl⟩
    end

lemma jointly_epi  {A B Q : Type u} 
                    (s s₁: (A ⊕ B) → Q) 
                    (h1 : s₁ ∘ inl = s ∘ inl)
                    (h2 : s₁ ∘ inr = s ∘ inr)
    : s₁ = s := 
    begin
        have all_ab : ∀ ab : (A ⊕ B) , s₁ ab = s ab :=
            begin 
                intro ab,
                induction ab,
                case inl :
                    {
                    have s0 : (s₁ ∘ inl) ab = (s ∘ inl) ab 
                        := by rw h1,
                    exact s0
                    },
                case inr :
                    begin 
                        have s0 : (s₁ ∘ inr) ab = (s ∘ inr) ab 
                            := by rw h2,
                        exact s0
                    end,
            end,
        exact funext all_ab
    end



variables   {A B C: Type u} 
/--
A proof that the disjoint union, which is defined inductively (inl : A → sum, inr : B → sum) in lean
is a sum in the category theory definition.
-/
lemma disjoint_union_is_sum :
    is_sum  (A ⊕ B) 
            inl 
            inr := 
    begin
        intros Q q₁ q₂,         -- competitor with 2 morphisms
        show ∃! s : (A ⊕ B) ⟶ Q, (q₁ = s ∘ inl ∧ q₂ = s ∘ inr)
                , from
        let s : (A ⊕ B) ⟶ Q :=      --defining the unique morphism s : sum → Q inductively
            begin
                intro ab, 
                induction ab,
                case inl :
                    begin
                        exact q₁ ab
                    end,
                case inr :
                    begin
                        exact q₂ ab
                    end,
            end in
            
        have commut_A : q₁ = s ∘ inl := rfl,
        have commut_B : q₂ = s ∘ inr := rfl,
        have unique : ∀ s₁ ,
                        (q₁ = s₁ ∘ inl ∧ q₂ = s₁ ∘ inr) → 
                        s₁ = s := 
            assume s₁ h₁,
                jointly_epi s s₁ 
                    (by rw [← h₁.1 ,commut_A ]) 
                    (by rw [← h₁.2 ,commut_B ]),
        
        exists_unique.intro s 
            ⟨commut_A , commut_B⟩ unique
    end



        









end Sum


