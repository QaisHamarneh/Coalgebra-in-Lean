import tactic.tidy

import category_theory.category
import set_category.diagram_lemmas
import help_functions




namespace Equalizer

open set 
     diagram_lemmas
     classical
     function
     help_functions
     category_theory


universes v u

local notation f ` ⊚ `:80 g:80 := category_struct.comp g f

def is_equalizer {X : Type v} [category X]
    {A B E : X} (f g : A ⟶ B)
                (e : E ⟶ A) : Prop := 
    f ⊚ e = g ⊚ e ∧ 
    Π {Q : X} (q : Q ⟶ A),
        f ⊚ q = g ⊚ q →
            ∃! h : Q ⟶ E, q = e ⊚ h


lemma equalizer_is_mono {X : Type v} [category X]
    {A B E : X} (f₁ f₂ : A ⟶ B)
    (e : E ⟶ A) (equaliz : is_equalizer f₁ f₂ e):
    mono e :=
    ⟨
        begin
            intros Q g₁ g₂ m,
            have s1 : f₁ ⊚ (e ⊚ g₁) = f₂ ⊚ (e ⊚ g₁) := by tidy,
            have compit : _ := equaliz.2 (e ⊚ g₁) s1,
            cases compit with h spec_h,
            have g₁_h : g₁ = h := spec_h.2 g₁ rfl,
            have g₂_h : g₂ = h := spec_h.2 g₂ m,
            simp [g₁_h , g₂_h]
        end
    ⟩ 

variables {A B : Type u}
variables (f g : A ⟶ B)

def equalizer_set : set A := λ a, f a = g a


lemma eqaulizer_set_is_equalizer : 
    is_equalizer f g ((equalizer_set f g) ↪ A) :=
    let E := equalizer_set f g in
    let e := E ↪ A in
    ⟨ 
        have elements : ∀ a, (f ∘ e) a = (g ∘ e) a := 
                λ a, a.property,
        funext elements
        ,
        begin
            intros Q q fq_gq,
            have s0 : ∀ b : Q , (f ⊚ q) b = (g ⊚ q) b := 
                            assume b, by rw fq_gq,
            have s1 : ∀ b : Q , q b ∈ E := 
                        assume b, s0 b,
            let h : Q → E := λ b, ⟨q b, s1 b⟩,
            have q_eh : q = e ∘ h := by tidy,
            use h,
            split,
            exact q_eh, 
            intros h₁ spec_h₁,
            tidy,
            have inj : injective e := inj_inclusion A E,
            have ey_eh: e ∘ h₁ = e ∘ h := by rw [← spec_h₁ , q_eh],
            have elements : ∀ b, (e ∘ h₁) b = (e ∘ h) b := 
                    assume a, by rw ey_eh,
            dsimp at *, 
            solve_by_elim
        end
    ⟩ 














end Equalizer