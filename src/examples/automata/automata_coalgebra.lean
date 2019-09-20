import coalgebra.Coalgebra
import examples.automata.Automaton
import set_category.category_set
import category_theory.types
import help_functions
import data.fin


namespace Automata_Coalgebra

open set help_functions coalgebra Automaton


universes u₁ u₂ u₃ 

variables {Sigma : Type u₂} {Γ : Type u₃}

def F : Type u₁ ⥤ Type (max u₁ u₂ u₃) := 
    {
        obj := λ S, Γ × (Sigma → S),
        map := λ {A B} ϕ, λ ⟨d₁ , δ⟩ , ⟨d₁ , λ e, ϕ (δ e)⟩,
    } 

def α (A : Automaton Sigma Γ): A → F.obj A := 
        λ s, ⟨A.γ s,  A.δ s⟩

def Automata_Coalgebra (A : Automaton Sigma Γ): Coalgebra F := 
    ⟨A.State , α A⟩ 


lemma Automata_Coalgebra_hom {A B : Automaton Sigma Γ} (ϕ : A → B): 
    is_homomorphism ϕ ↔ 
    @is_coalgebra_homomorphism F 
        (Automata_Coalgebra A) 
        (Automata_Coalgebra B)
            ϕ := 
        let 𝔸 := Automata_Coalgebra A in
        let Β := Automata_Coalgebra B in
    begin
        
        split,
        intro h,
        dsimp at *,
        ext1 s,
        dsimp at *,
        have hs := h s,
        ext1,
        have B_fst : (Β.α (ϕ s)).fst = B.γ (ϕ s) := 
            by tidy,
        have A_fst : (F.map ϕ ((Automata_Coalgebra A).α s)).fst = B.γ (ϕ s) := 
            by tidy,
        simp [B_fst , A_fst],
        have A_snd : (Β.α (ϕ s)).snd = ((F.map ϕ) (𝔸.α s)).snd :=
            by tidy,
        exact A_snd,

        intro co_h, 
        dsimp at *,
        intro s,
        have h_s : (Β.α ∘ ϕ) s = 
                (F.map ϕ ∘ 𝔸.α) s := by rw co_h,
        split,
        tidy
    end








end Automata_Coalgebra
