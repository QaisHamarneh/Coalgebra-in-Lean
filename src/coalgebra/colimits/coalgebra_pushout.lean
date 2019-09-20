import category_theory.category
import category_theory.functor
import help_functions
import set_category.colimits.Coequalizer
import coalgebra.Coalgebra
import coalgebra.colimits.coalgebra_sum
import coalgebra.colimits.coalgebra_coequalizer
import set_category.colimits.Pushout
import set_category.colimits.Sum
import set_category.category_set


import tactic.tidy

universes u



namespace coalgebra_pushout

open category_theory 
     set 
     sum
     Sum
     classical
     function
     help_functions
     Coequalizer
     coalgebra
     coalgebra_sum
     coalgebra_coequalizer
     Pushout
     category_set
     


local notation f ` ⊚ `:80 g:80 := category_struct.comp g f

variables   {F : Type u ⥤ Type u}
            {𝔸 Β₁ Β₂: Coalgebra F} 
            (ϕ : 𝔸 ⟶ Β₁)
            (ψ : 𝔸 ⟶ Β₂)


theorem pushout_is_coalgebra :
    let S := Β₁ ⊞ Β₂  in
    let Β_Θ := @theta 𝔸 S (inl ∘ ϕ) (inr ∘ ψ) in
    let π_Θ := @coequalizer 𝔸 S (inl ∘ ϕ) (inr ∘ ψ) in
    ∃! α : Β_Θ → F.obj Β_Θ,  
    let P : Coalgebra F := ⟨Β_Θ, α⟩ in 
    @is_coalgebra_homomorphism F Β₁ P (π_Θ ∘ inl) ∧ 
    @is_coalgebra_homomorphism F Β₂ P (π_Θ ∘ inr)  := 
    begin
        assume S Β_Θ π_Θ,

        have po1 : π_Θ ∘ inl ∘ ϕ = π_Θ ∘ inr ∘ ψ
                   := (coequalizer_sum_is_pushout ϕ ψ).1,

        let p₁ : 𝔸 → S := (inl ∘ ϕ),
        let p₂ : 𝔸 → S := (inr ∘ ψ),

        have hom_p₁ : is_coalgebra_homomorphism p₁ := 
            @comp_is_hom F 𝔸 Β₁ S ϕ ⟨inl, inl_is_homomorphism Β₁ Β₂⟩,

        have hom_p₂ : is_coalgebra_homomorphism p₂ := 
            @comp_is_hom F 𝔸 Β₂ S ψ ⟨inr, inr_is_homomorphism Β₁ Β₂⟩,

        have co : _ := coequalizer_is_homomorphism 
                        ⟨p₁, hom_p₁⟩ ⟨p₂,  hom_p₂⟩,
        let α := some co,
        have hom_π : @is_coalgebra_homomorphism F S ⟨Β_Θ , α⟩ π_Θ
                := (some_spec co).1,
        let P : Coalgebra F := ⟨Β_Θ, α⟩,

        have hom_π_inl : α ∘ (π_Θ ∘ inl) = (F.map (π_Θ ∘ inl)) ∘ Β₁.α
                    := @comp_is_hom F Β₁ S P 
                        ⟨inl, inl_is_homomorphism Β₁ Β₂⟩
                        ⟨π_Θ, hom_π⟩,

        have hom_π_inr : α ∘ (π_Θ ∘ inr) = (F.map (π_Θ ∘ inr)) ∘ Β₂.α
                    := @comp_is_hom F Β₂ S P 
                        ⟨inr, inr_is_homomorphism Β₁ Β₂⟩
                        ⟨π_Θ, hom_π⟩,

        use α,
        split,
        exact ⟨hom_π_inl , hom_π_inr⟩ ,

        intros α₁ hom,

        have hom1 : α₁ ∘ (π_Θ ∘ inl) = (F.map (π_Θ ∘ inl)) ∘ Β₁.α := hom.1,

        have hom2 : α₁ ∘ (π_Θ ∘ inr) = (F.map (π_Θ ∘ inr)) ∘ Β₂.α := hom.2,

        have α_α₁_l : α₁ ∘ π_Θ ∘ inl = α ∘ π_Θ ∘ inl := 
                by simp [hom_π_inl, hom1],

        have α_α₁_r : α₁ ∘ π_Θ ∘ inr = α ∘ π_Θ ∘ inr := 
                by simp [hom_π_inr, hom2],

        have α_α₁_π : α₁ ∘ π_Θ = α ∘ π_Θ := 
            jointly_epi (α ∘ π_Θ) (α₁ ∘ π_Θ) α_α₁_l α_α₁_r,

        let mor_π : (Β₁ ⊕ Β₂) ⟶ Β_Θ := π_Θ,
        haveI ep : epi mor_π := 
            (epi_iff_surjective mor_π).2 
            (quot_is_surjective (inl ∘ ϕ) (inr ∘ ψ)),

        exact right_cancel mor_π α_α₁_π,
    end


end coalgebra_pushout