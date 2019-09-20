import tactic.tidy

import set_category.diagram_lemmas
import help_functions




namespace Product

open set 
     diagram_lemmas
     classical
     function
     help_functions
     category_theory


universes v u

local notation f ` ⊚ `:80 g:80 := category_struct.comp g f

def is_product {X : Type v} [category X]
    (A B : X)
    {P : X} (π₁ : P ⟶ A) (π₂ : P ⟶ B): Prop := 
    Π (Q : X) (q₁ : Q ⟶ A) (q₂ : Q ⟶ B),
            ∃! p : Q ⟶ P, q₁ = π₁ ⊚ p ∧ q₂ = π₂ ⊚ p


variables (A B : Type u)


lemma cartesian_product_is_product : 
    is_product A B prod.fst prod.snd :=
    begin
        intros Q q₁ q₂,
        let p : Q → (A × B) := λ k, ⟨q₁ k,q₂ k⟩,
        use p,
        tidy
    end

lemma jointly_mono
    {X : Type v} [category X]
    (A B P : X) {Q: X} (π₁ : P ⟶ A) (π₂ : P ⟶ B)
        (prod: is_product A B π₁ π₂)
        {s s₁: Q ⟶ P} 
        (h1 : π₁ ⊚ s₁ = π₁ ⊚ s)
        (h2 : π₂ ⊚ s₁ = π₂ ⊚ s):
        s₁ = s :=
    begin
        have prod_Q := prod Q (π₁ ⊚ s₁) (π₂ ⊚ s₁),
        cases prod_Q with p spec_p,
        have spec_s1 : π₁ ⊚ s = π₁ ⊚ p := 
            h1 ▸ spec_p.1.1,
        have spec_s2 : π₂ ⊚ s = π₂ ⊚ p := 
            h2 ▸ spec_p.1.2,
        rw spec_p.2 s ⟨h1, h2⟩,
        exact spec_p.2 s₁ ⟨rfl, rfl⟩,
    end

open prod

lemma jointly_mono_set
        {Q : Type u}
        {f g: Q → (A × B)} 
        (h1 : fst ∘ f = fst ∘ g)
        (h2 : snd ∘ f = snd ∘ g):
        f = g :=
        have elements : ∀ q : Q , f q = g q :=
            assume q,
            have π₁ : (f q).1 = (g q).1 := 
                 have f1 : (prod.fst ∘ f) q = (prod.fst ∘ g) q := by rw h1,
                 f1,
            have π₂ : prod.snd (f q) = prod.snd (g q) := 
                 have s1 : (prod.snd ∘ f) q = (prod.snd ∘ g) q := by rw h2,
                 s1,
            by {
                ext1,
                exact π₁, exact π₂
            },
        funext elements



end Product